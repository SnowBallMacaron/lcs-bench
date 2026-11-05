import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.HerbrandTheorem
import LCS.Herbrand.SHGTheorem.Part1
import Attach
import LCS.Herbrand.SHGTheorem.Part2.ProofsStamp

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.HerbrandTheorem

/-- Example 7.6.2: The NNF formula A = forall x(P(a) or exists y(Q(y) and forall z(P(y, z) or exists u Q(x, u)))) or exists w Q(a, w). Variables: x = 0, y = 1, z = 2, u = 3, w = 4. -/
@[blueprint "chap7__example_7_6_2"]
def usExFormula : FormulaN usExLang :=
  FormulaN.disj
    (FormulaN.all 0
      (FormulaN.disj
        (FormulaN.predN USExPred.P1
          (usExVec1 (.const USExConst.a)))
        (FormulaN.ex 1
          (FormulaN.conj
            (FormulaN.predN USExPred.Q1
              (usExVec1 (.var 1)))
            (FormulaN.all 2
              (FormulaN.disj
                (FormulaN.predN USExPred.P2
                  (usExVec2 (.var 1) (.var 2)))
                (FormulaN.ex 3
                  (FormulaN.predN USExPred.Q2
                    (usExVec2 (.var 0) (.var 3))))))))))
    (FormulaN.ex 4
      (FormulaN.predN USExPred.Q2
        (usExVec2 (.const USExConst.a) (.var 4))))

-- ===================================================================
-- Example 7.6.2 (companion def): usExExistsYSubformula
-- ===================================================================

/-- Example 7.6.2 (companion def): The subformula exists y(Q(y) and forall z(P(y, z) or exists u Q(x, u))). Variables: x = 0, y = 1, z = 2, u = 3. Universal scope is <x>. -/
@[blueprint "chap7__example_7_6_2"]
def usExExistsYSubformula : FormulaN usExLang :=
  FormulaN.ex 1
    (FormulaN.conj
      (FormulaN.predN USExPred.Q1
        (usExVec1 (.var 1)))
      (FormulaN.all 2
        (FormulaN.disj
          (FormulaN.predN USExPred.P2
            (usExVec2 (.var 1) (.var 2)))
          (FormulaN.ex 3
            (FormulaN.predN USExPred.Q2
              (usExVec2 (.var 0) (.var 3)))))))

-- ===================================================================
-- Example 7.6.2 (companion def): usExExistsUSubformula
-- ===================================================================

/-- Example 7.6.2 (companion def): The subformula exists u Q(x, u).
Variables: x = 0, u = 3. Universal scope is <x, z>. -/
@[blueprint "chap7__example_7_6_2"]
def usExExistsUSubformula : FormulaN usExLang :=
  FormulaN.ex 3
    (FormulaN.predN USExPred.Q2
      (usExVec2 (.var 0) (.var 3)))

-- ===================================================================
-- Example 7.6.2 (companion def): usExExistsWSubformula
-- ===================================================================

/-- Example 7.6.2 (companion def): The subformula exists w Q(a, w).
Variables: w = 4. Universal scope is empty <>. -/
@[blueprint "chap7__example_7_6_2"]
def usExExistsWSubformula : FormulaN usExLang :=
  FormulaN.ex 4
    (FormulaN.predN USExPred.Q2
      (usExVec2 (.const USExConst.a) (.var 4)))

-- ===================================================================
-- Definition 7.6.2 (companion def): SkolemLanguage
-- ===================================================================

/-- Definition 7.6.2: Extend the base language by one fresh symbol per
allocation index. Zero-rank indices form new constants; positive-rank
indices form new function symbols of their prescribed ranks. The sum
injections distinguish every new symbol from the base language, and
subtype values retain the original occurrence indices. -/
@[blueprint "chap7__definition_7_6_2"]
def SkolemLanguage {L : Language}
    (n : Nat) (skolemRank : Fin n → Nat) : Language where
  funSymbols := L.funSymbols ⊕ {i : Fin n // 0 < skolemRank i}
  funArity := fun
    | .inl f => L.funArity f
    | .inr i => skolemRank i.val
  constSymbols := L.constSymbols ⊕ {i : Fin n // skolemRank i = 0}
  predSymbols := L.predSymbols
  predArity := L.predArity
  hasEquality := L.hasEquality

/-- Definition 7.6.2 (companion type): `SkolemSpec L` packages exactly
the standing assumptions on the rectified NNF sentence being
Skolemized. Its allocation data is not caller-supplied: the derived
APIs below compute the preorder list of existential occurrences,
one fresh symbol index per list position, the exact scope at that
position, and its length as the symbol rank. Consequently a value of
this structure cannot under-allocate, over-allocate, duplicate an
allocation, or reorder ranks/scopes. Structurally equal existential
syntax at two positions remains two occurrences because the computed
representation is a list, not a set. Equal ranks remain permitted:
freshness is supplied by distinct `Fin n` indices, not by injectivity
of the `Nat`-valued rank function. -/
@[blueprint "chap7__definition_7_6_2"]
structure SkolemSpec (L : Language) where
  /-- The rectified NNF sentence being Skolemized. -/
  source : FormulaN L
  /-- `source` is in negation normal form (Def 6.4.1). -/
  hNNF : source.isNNF
  /-- `source` is rectified (Def 5.3.10). -/
  hRect : LCS.FirstOrder.Semantics.Subformulae.isRectified source
  /-- `source` is closed — no free variables (Def 5.2.5). -/
  hSentence : LCS.FirstOrder.SyntaxN.Variables.FormulaN.isClosed source

/-- Definition 7.6.2 (companion def): Exact ordered existential
allocations computed from `S.source`. -/
@[blueprint "chap7__definition_7_6_2"]
def SkolemSpec.allocations {L : Language}
    (S : SkolemSpec L) : List (FormulaN L × List Nat) :=
  existentialDescriptors S.source

/-- Definition 7.6.2 (companion def): Number of Skolem symbols, exactly
the number of existential occurrences in `S.source`. -/
@[blueprint "chap7__definition_7_6_2"]
def SkolemSpec.n {L : Language} (S : SkolemSpec L) : Nat :=
  S.allocations.length

/-- Definition 7.6.2 (companion def): The existential occurrence and
scope allocated to the `i`th Skolem symbol. The `Fin S.n` index is the
occurrence identity. -/
@[blueprint "chap7__definition_7_6_2"]
def SkolemSpec.allocation {L : Language} (S : SkolemSpec L)
    (i : Fin S.n) : FormulaN L × List Nat :=
  S.allocations.get i

/-- Definition 7.6.2 (companion def): Exact ordered universal scope of
the existential occurrence allocated to `i`. -/
@[blueprint "chap7__definition_7_6_2"]
def SkolemSpec.skolemScope {L : Language} (S : SkolemSpec L)
    (i : Fin S.n) : List Nat :=
  (S.allocation i).2

/-- Definition 7.6.2 (companion def): Rank of the `i`th Skolem symbol,
computed as the length of that occurrence's exact universal scope. -/
@[blueprint "chap7__definition_7_6_2"]
def SkolemSpec.skolemRank {L : Language} (S : SkolemSpec L)
    (i : Fin S.n) : Nat :=
  (S.skolemScope i).length

/-- Definition 7.6.2: The Skolem extension of the original source language.
Empty-scope occurrences supply fresh constants; nonempty-scope occurrences
supply fresh functions whose ranks are their full ordered scope lengths. -/
@[blueprint "chap7__definition_7_6_2"]
def SkolemSpec.language {L : Language} (S : SkolemSpec L) : Language :=
  SkolemLanguage (L := L) S.n S.skolemRank

/-- The ordered list `0, ..., S.n - 1` of all allocated Skolem
symbol indices. The exact traversal consumes this list from left to
right. -/
def SkolemSpec.indices {L : Language}
    (S : SkolemSpec L) : List (Fin S.n) :=
  List.ofFn (fun i : Fin S.n => i) /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

private theorem list_ofFn_get {α : Type} (xs : List α) :
    List.ofFn (fun i : Fin xs.length => xs.get i) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.ofFn_succ]
    simp only [List.get_cons_zero]
    congr 1 /- ATTACH-BLOCKER: private declaration -/

/-- The index enumeration visits every allocation exactly once and in
list order. -/
theorem SkolemSpec.indices_allocations {L : Language}
    (S : SkolemSpec L) :
    S.indices.map S.allocation = S.allocations := by
  rw [SkolemSpec.indices, List.map_ofFn]
  change
    List.ofFn
      (fun i : Fin S.allocations.length => S.allocations.get i) =
        S.allocations
  exact list_ofFn_get S.allocations /- ATTACH-BLOCKER: private name in relocated declaration -/

/-- The index enumeration therefore carries exactly the descriptor
scope sequence, including repeated ranks and empty scopes. -/
theorem SkolemSpec.indices_scopes {L : Language}
    (S : SkolemSpec L) :
    S.indices.map S.skolemScope =
      existentialScopesAux S.source [] := by
  calc
    S.indices.map S.skolemScope =
        (S.indices.map S.allocation).map Prod.snd := by
          rw [List.map_map]
          congr 1
    _ = S.allocations.map Prod.snd := by
          rw [S.indices_allocations]
    _ = existentialScopesAux S.source [] := by
          exact existentialDescriptorsAux_scopes S.source [] /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

/-- The computed symbol count is exactly the descriptor traversal
count. -/
theorem SkolemSpec.n_eq_descriptorCount {L : Language}
    (S : SkolemSpec L) :
    S.n = skolemDescriptorCount S.source := by
  exact existentialDescriptorsAux_length S.source [] /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

/-- Definition 7.6.2 (required helper): If `spec.source` has no
existential subformulae (as recorded by `universalScopeAux`), then its
computed allocation list is empty and hence `spec.n = 0`. -/
theorem SkolemSpec.n_eq_zero_of_no_ex_source {L : Language}
    (spec : SkolemSpec L)
    (hNoEx : ∀ x C scope,
      (FormulaN.ex x C, scope) ∉ universalScopeAux spec.source []) :
    spec.n = 0 := by
  unfold SkolemSpec.n SkolemSpec.allocations existentialDescriptors
  apply List.length_eq_zero_iff.mpr
  apply List.filterMap_eq_nil_iff.mpr
  intro pair hMem
  rcases pair with ⟨D, scope⟩
  cases D with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg _ => rfl
  | conj _ _ => rfl
  | disj _ _ => rfl
  | impl _ _ => rfl
  | all _ _ => rfl
  | ex x C => exact (hNoEx x C scope hMem).elim /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

end LCS.Herbrand.SHGTheorem
end

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.HerbrandTheorem
namespace SkolemAllocationRegression

/-- Nullary predicates keep the allocation regressions focused on
quantifier occurrence, order, and scope. -/
inductive Pred : Type where
  | p
  | q /- ATTACH-BLOCKER: unsupported untagged inductive -/

def language : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := Empty
  predSymbols := Pred
  predArity := fun _ => 0 /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

def atom (P : Pred) : FormulaN language :=
  .predN P fun i => i.elim0 /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

def zeroSource : FormulaN language :=
  .all 0 (atom .p) /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

def oneSource : FormulaN language :=
  .ex 0 (atom .p) /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/



def siblingLeft : FormulaN language :=
  .ex 1 (atom .p) /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

def siblingRight : FormulaN language :=
  .ex 2 (atom .q) /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

def siblingSource : FormulaN language :=
  .all 0 (.conj siblingLeft siblingRight) /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

def nestedOuter : FormulaN language :=
  .ex 1 (.all 2 (.ex 3 (atom .p))) /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/



def nestedSource : FormulaN language :=
  .all 0 nestedOuter /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

private theorem atom_fv_empty (P : Pred) :
    formulaFVN (atom P) = (∅ : Set Nat) := by
  funext x
  apply propext
  change (∃ i : Fin 0, termFV (i.elim0) x) ↔ False
  constructor
  · rintro ⟨i, _⟩
    exact i.elim0
  · intro h
    exact h.elim /- ATTACH-BLOCKER: private declaration -/

private theorem atom_bv_empty (P : Pred) :
    formulaBVN (atom P) = (∅ : Set Nat) := by
  rfl /- ATTACH-BLOCKER: private declaration -/

private theorem atom_distinct_bindings (P : Pred) :
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings
      (atom P) := by
  trivial /- ATTACH-BLOCKER: private declaration -/

@[simp] private theorem mem_empty_iff_false (x : Nat) :
    x ∈ (∅ : Set Nat) ↔ False := by
  rfl /- ATTACH-BLOCKER: private declaration -/

@[simp] private theorem mem_union_iff (x : Nat) (s t : Set Nat) :
    x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := by
  rfl /- ATTACH-BLOCKER: private declaration -/

@[simp] private theorem mem_diff_iff (x : Nat) (s t : Set Nat) :
    x ∈ s \ t ↔ x ∈ s ∧ ¬x ∈ t := by
  rfl /- ATTACH-BLOCKER: private declaration -/

@[simp] private theorem mem_singleton_iff (x y : Nat) :
    x ∈ Set.singleton y ↔ x = y := by
  rfl /- ATTACH-BLOCKER: private declaration -/

@[simp] private theorem empty_diff (s : Set Nat) :
    (∅ : Set Nat) \ s = ∅ := by
  funext x
  apply propext
  change (False ∧ ¬s x) ↔ False
  exact ⟨fun h => h.1, False.elim⟩ /- ATTACH-BLOCKER: private declaration -/

@[simp] private theorem empty_union (s : Set Nat) :
    (∅ : Set Nat) ∪ s = s := by
  funext x
  apply propext
  change (False ∨ s x) ↔ s x
  exact ⟨fun h => h.elim False.elim id, Or.inr⟩ /- ATTACH-BLOCKER: private declaration -/

@[simp] private theorem union_empty (s : Set Nat) :
    s ∪ (∅ : Set Nat) = s := by
  funext x
  apply propext
  change (s x ∨ False) ↔ s x
  exact ⟨fun h => h.elim id False.elim, Or.inl⟩ /- ATTACH-BLOCKER: private declaration -/

private theorem zeroSource_rectified :
    LCS.FirstOrder.Semantics.Subformulae.isRectified zeroSource := by
  simp [zeroSource, atom_fv_empty, atom_bv_empty, atom_distinct_bindings,
    LCS.FirstOrder.Semantics.Subformulae.isRectified,
    LCS.FirstOrder.Semantics.Subformulae.boundVarsFresh,
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
    formulaFVN, formulaBVN] /- ATTACH-BLOCKER: private declaration -/

private theorem oneSource_rectified :
    LCS.FirstOrder.Semantics.Subformulae.isRectified oneSource := by
  simp [oneSource, atom_fv_empty, atom_bv_empty, atom_distinct_bindings,
    LCS.FirstOrder.Semantics.Subformulae.isRectified,
    LCS.FirstOrder.Semantics.Subformulae.boundVarsFresh,
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
    formulaFVN, formulaBVN] /- ATTACH-BLOCKER: private declaration -/

private theorem siblingSource_rectified :
    LCS.FirstOrder.Semantics.Subformulae.isRectified siblingSource := by
  simp [siblingSource, siblingLeft, siblingRight, atom_fv_empty,
    atom_bv_empty, atom_distinct_bindings,
    LCS.FirstOrder.Semantics.Subformulae.isRectified,
    LCS.FirstOrder.Semantics.Subformulae.boundVarsFresh,
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
    formulaFVN, formulaBVN] /- ATTACH-BLOCKER: private declaration -/

private theorem nestedSource_rectified :
    LCS.FirstOrder.Semantics.Subformulae.isRectified nestedSource := by
  simp [nestedSource, nestedOuter, atom_fv_empty, atom_bv_empty,
    atom_distinct_bindings,
    LCS.FirstOrder.Semantics.Subformulae.isRectified,
    LCS.FirstOrder.Semantics.Subformulae.boundVarsFresh,
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
    formulaFVN, formulaBVN] /- ATTACH-BLOCKER: private declaration -/

def zeroSpec : SkolemSpec language where
  source := zeroSource
  hNNF := by simp [zeroSource, atom, FormulaN.isNNF]
  hRect := zeroSource_rectified
  hSentence := by
    simp [FormulaN.isClosed, zeroSource, atom_fv_empty, formulaFVN] /- ATTACH-BLOCKER: private name in relocated declaration -/

def oneSpec : SkolemSpec language where
  source := oneSource
  hNNF := by simp [oneSource, atom, FormulaN.isNNF]
  hRect := oneSource_rectified
  hSentence := by
    simp [FormulaN.isClosed, oneSource, atom_fv_empty, formulaFVN] /- ATTACH-BLOCKER: private name in relocated declaration -/

def siblingSpec : SkolemSpec language where
  source := siblingSource
  hNNF := by
    simp [siblingSource, siblingLeft, siblingRight, atom, FormulaN.isNNF]
  hRect := siblingSource_rectified
  hSentence := by
    simp [FormulaN.isClosed, siblingSource, siblingLeft, siblingRight,
      atom_fv_empty, formulaFVN] /- ATTACH-BLOCKER: private name in relocated declaration -/

def nestedSpec : SkolemSpec language where
  source := nestedSource
  hNNF := by
    simp [nestedSource, nestedOuter, atom, FormulaN.isNNF]
  hRect := nestedSource_rectified
  hSentence := by
    simp [FormulaN.isClosed, nestedSource, nestedOuter,
      atom_fv_empty, formulaFVN] /- ATTACH-BLOCKER: private name in relocated declaration -/

def oneIndex : Fin oneSpec.n := ⟨0, by decide⟩ /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/



def nestedIndex1 : Fin nestedSpec.n := ⟨1, by decide⟩ /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

/-- Zero existentials allocate exactly zero symbols. -/
theorem zero_exact : zeroSpec.n = 0 := by rfl /- retained: used by LCS.SLD.FirstOrder.HornEncoding.Proofs -/








































end SkolemAllocationRegression
end LCS.Herbrand.SHGTheorem
end

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.HerbrandTheorem

/-- Definition 7.6.2: Look up the fresh symbol for an allocation index.
The result is a constant for rank zero and a function for positive rank. -/
@[blueprint "chap7__definition_7_6_2"]
def SkolemLanguage.symbolLookup {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat}
    (i : Nat) (hi : i < n) :
    (SkolemLanguage n skolemRank (L := L)).constSymbols ⊕
      (SkolemLanguage n skolemRank (L := L)).funSymbols :=
  if h : skolemRank ⟨i, hi⟩ = 0 then
    .inl (.inr ⟨⟨i, hi⟩, h⟩)
  else
    .inr (.inr ⟨⟨i, hi⟩, Nat.pos_of_ne_zero h⟩)

-- ===================================================================
-- Lemma 7.6.3 (companion def): liftTermSkolem
-- ===================================================================

/-- Lemma 7.6.3: Embed a base-language term into the Skolem extension.
Variables are preserved; both base constants and base functions use the
left sum injection, keeping them distinct from all fresh symbols. -/
@[blueprint "chap7__definition_7_6_2"]
def liftTermSkolem {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat} :
    Term L → Term (SkolemLanguage (L := L) n skolemRank)
  | .var x => .var x
  | .const c => .const (Sum.inl c)
  | .func f ts => .func (Sum.inl f) (fun i => liftTermSkolem (ts i))

-- ===================================================================
-- Lemma 7.6.3 (companion def): liftFormulaSkolem
-- ===================================================================

/-- Lemma 7.6.3 (companion def): Embeds a FormulaN from the base language L into the Skolem-extended language by lifting all embedded terms via liftTermSkolem. The formula structure (connectives, quantifiers, negation) is preserved; base constant and function symbols both use Sum.inl. -/
@[blueprint "chap7__definition_7_6_2"]
def liftFormulaSkolem {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat} :
    FormulaN L → FormulaN (SkolemLanguage (L := L) n skolemRank)
  | .predN P ts => .predN P (fun i => liftTermSkolem (ts i))
  | .eq_ h t1 t2 => .eq_ h (liftTermSkolem t1) (liftTermSkolem t2)
  | .neg A => .neg (liftFormulaSkolem A)
  | .conj A B => .conj (liftFormulaSkolem A) (liftFormulaSkolem B)
  | .disj A B => .disj (liftFormulaSkolem A) (liftFormulaSkolem B)
  | .impl A B => .impl (liftFormulaSkolem A) (liftFormulaSkolem B)
  | .all x A => .all x (liftFormulaSkolem A)
  | .ex x A => .ex x (liftFormulaSkolem A)

/-- Term substitution preserves the descriptor traversal count because
it changes terms only, never formula constructors. -/
theorem formulaSubstN_descriptorCount {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) :
    skolemDescriptorCount (formulaSubstN A t x) =
      skolemDescriptorCount A := by
  induction A with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg _ _ => rfl
  | conj A B ihA ihB =>
    simp [formulaSubstN, skolemDescriptorCount, ihA, ihB]
  | disj A B ihA ihB =>
    simp [formulaSubstN, skolemDescriptorCount, ihA, ihB]
  | impl _ _ _ _ => rfl
  | all y B ih =>
    simp [formulaSubstN, skolemDescriptorCount]
    split <;> simp [skolemDescriptorCount, ih]
  | ex y B ih =>
    simp [formulaSubstN, skolemDescriptorCount]
    split <;> simp [skolemDescriptorCount, ih] /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

/-- Term substitution also preserves the ordered existential-scope
traversal. -/
theorem existentialScopesAux_formulaSubstN {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) (scope : List Nat) :
    existentialScopesAux (formulaSubstN A t x) scope =
      existentialScopesAux A scope := by
  induction A generalizing scope with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg _ _ => rfl
  | conj A B ihA ihB =>
    simp [formulaSubstN, existentialScopesAux, ihA, ihB]
  | disj A B ihA ihB =>
    simp [formulaSubstN, existentialScopesAux, ihA, ihB]
  | impl _ _ _ _ => rfl
  | all y B ih =>
    simp [formulaSubstN]
    split <;> simp [existentialScopesAux, ih]
  | ex y B ih =>
    simp [formulaSubstN]
    split <;> simp [existentialScopesAux, ih] /- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.LowerConstruction, LCS.Herbrand.SHGTheorem.Main.SkolemEquisatisfiability, LCS.Herbrand.SHGTheorem.Main.SkolemSemanticsBase -/

/-- Lifting into the Skolem language preserves the descriptor count. -/
theorem liftFormulaSkolem_descriptorCount {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat} (A : FormulaN L) :
    skolemDescriptorCount
        (liftFormulaSkolem (skolemRank := skolemRank) A) =
      skolemDescriptorCount A := by
  induction A with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg _ _ => rfl
  | conj _ _ ihA ihB =>
    simp [liftFormulaSkolem, skolemDescriptorCount, ihA, ihB]
  | disj _ _ ihA ihB =>
    simp [liftFormulaSkolem, skolemDescriptorCount, ihA, ihB]
  | impl _ _ _ _ => rfl
  | all _ _ ih =>
    simp [liftFormulaSkolem, skolemDescriptorCount, ih]
  | ex _ _ ih =>
    simp [liftFormulaSkolem, skolemDescriptorCount, ih] /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

/-- Lifting also preserves the ordered existential-scope traversal. -/
theorem liftFormulaSkolem_existentialScopesAux {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat}
    (A : FormulaN L) (scope : List Nat) :
    existentialScopesAux
        (liftFormulaSkolem (skolemRank := skolemRank) A) scope =
      existentialScopesAux A scope := by
  induction A generalizing scope with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg _ _ => rfl
  | conj _ _ ihA ihB =>
    simp [liftFormulaSkolem, existentialScopesAux, ihA, ihB]
  | disj _ _ ihA ihB =>
    simp [liftFormulaSkolem, existentialScopesAux, ihA, ihB]
  | impl _ _ _ _ => rfl
  | all _ _ ih =>
    simp [liftFormulaSkolem, existentialScopesAux, ih]
  | ex _ _ ih =>
    simp [liftFormulaSkolem, existentialScopesAux, ih] /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

/-- Definition 7.6.2 (helper): Argument `k` of the Skolem symbol
allocated to descriptor index `i`. This is literally position `k` of
the descriptor's ordered universal scope. -/
def exactSkolemArgument {L : Language} (S : SkolemSpec L)
    (i : Fin S.n) (k : Fin (S.skolemRank i)) : Term S.language :=
    Term.var ((S.skolemScope i).get
      ⟨k.val, by
        simp [SkolemSpec.skolemRank] at k
        exact k.isLt⟩) /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

/-- Definition 7.6.2: The exact term for an original-root allocation.
An empty scope produces `Term.const` with that occurrence's fresh constant.
A nonempty scope produces `Term.func` with that occurrence's fresh positive-rank
function, applied to every variable in its full scope, in order. -/
@[blueprint "chap7__definition_7_6_2"]
def exactSkolemTerm {L : Language} (S : SkolemSpec L)
    (i : Fin S.n) : Term S.language :=
  if hRank : S.skolemRank i = 0 then
    Term.const (.inr ⟨i, hRank⟩)
  else
    Term.func (.inr ⟨i, Nat.pos_of_ne_zero hRank⟩)
      (exactSkolemArgument S i)

-- ===================================================================
-- Definition 7.6.2 (companion def): skolemSubst
-- ===================================================================

/-- Definition 7.6.2: Substitute the exact term allocated to occurrence
`i` of the original rectified NNF sentence `S.source`. An empty original
scope supplies its fresh constant; a positive original scope supplies its
fresh function applied to the full ordered scope. `B` may already contain
substitutions, but the allocation and scope are always read from the same
original `S`. -/
@[blueprint "chap7__definition_7_6_2"]
def skolemSubst {L : Language} (S : SkolemSpec L)
    (B : FormulaN S.language) (x : Nat) (i : Fin S.n) :
    FormulaN S.language :=
  formulaSubstN B (exactSkolemTerm S i) x

-- ===================================================================
-- Definition 7.6.2 (helper): formulaQuantCount
-- ===================================================================

/-- Definition 7.6.2 (helper): Counts the number of quantifier
constructors (both universal and existential) in a formula. Used as
the termination metric for skolemForm: each recursive call on a
subterm or skolemSubst result has strictly fewer quantifiers. Binary
connectives add 1 to ensure strict decrease. -/
def formulaQuantCount {L : Language} : FormulaN L → Nat
  | .predN _ _ => 0
  | .eq_ _ _ _ => 0
  | .neg B => formulaQuantCount B
  | .conj A B => 1 + formulaQuantCount A + formulaQuantCount B
  | .disj A B => 1 + formulaQuantCount A + formulaQuantCount B
  | .impl A B => 1 + formulaQuantCount A + formulaQuantCount B
  | .all _ B => 1 + formulaQuantCount B
  | .ex _ B => 1 + formulaQuantCount B /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

/-- Definition 7.6.2 (helper): formulaSubstN preserves formulaQuantCount
because substitution replaces variables (no quantifiers) with terms
(also no quantifiers). -/
theorem formulaSubst_quantCount {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) :
    formulaQuantCount (formulaSubstN A t x) = formulaQuantCount A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg B ih => simp [formulaSubstN, formulaQuantCount, ih]
  | conj A B ihA ihB => simp [formulaSubstN, formulaQuantCount, ihA, ihB]
  | disj A B ihA ihB => simp [formulaSubstN, formulaQuantCount, ihA, ihB]
  | impl A B ihA ihB => simp [formulaSubstN, formulaQuantCount, ihA, ihB]
  | all y B ih =>
    simp [formulaSubstN, formulaQuantCount]
    try split <;> simp [formulaQuantCount, ih]
  | ex y B ih =>
    simp [formulaSubstN, formulaQuantCount]
    try split <;> simp [formulaQuantCount, ih] /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

/-- Definition 7.6.2 (helper): skolemSubst preserves formulaQuantCount
since it is just a formulaSubstN with a specific term. -/
theorem skolemSubst_quantCount {L : Language} (S : SkolemSpec L)
    (B : FormulaN S.language) (x : Nat) (i : Fin S.n) :
    formulaQuantCount (skolemSubst S B x i) = formulaQuantCount B :=
-- BEGIN PROOF
  formulaSubst_quantCount B _ x /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

-- ===================================================================
-- Definition 7.6.2: skolemForm
-- ===================================================================

/-- Legacy arbitrary-state compatibility helper for older downstream
proofs. It threads a numeric counter and remains total even on states
that do not correspond to `S.allocations`, so it retains counter
overrun, modulo-indexing, and empty-scope branches. The proof-backed
top-level `skolemForm` does not call this helper; it uses
`skolemFormExactAux` below, whose descriptor-index input makes all of
those branches unrepresentable. -/
def skolemFormAux {L : Language} (S : SkolemSpec L) :
    FormulaN S.language → List Nat → Nat →
      FormulaN S.language × Nat
  | .predN P ts, _, i => (.predN P ts, i)
  | .eq_ h t1 t2, _, i => (.eq_ h t1 t2, i)
  | .neg A, _, i =>
    -- Def 7.6.2 (i): "If A' is either an atomic formula B or the
    -- negation ¬B of an atomic formula B, then SK(A') = A'." NNF
    -- inputs have only atomic bodies under `.neg` (Def 6.4.1), so
    -- `.neg A` is returned unchanged here. The counter is not
    -- advanced because no existential sits under a literal-level
    -- negation in a rectified NNF sentence.
    (.neg A, i)
  | .conj A B, scope, i =>
    let (A', i') := skolemFormAux S A scope i
    let (B', i'') := skolemFormAux S B scope i'
    (.conj A' B', i'')
  | .disj A B, scope, i =>
    let (A', i') := skolemFormAux S A scope i
    let (B', i'') := skolemFormAux S B scope i'
    (.disj A' B', i'')
  | .impl A B, scope, i =>
    -- NNF inputs never contain `.impl`; recurse for totality.
    let (A', i') := skolemFormAux S A scope i
    let (B', i'') := skolemFormAux S B scope i'
    (.impl A' B', i'')
  | .all x B, scope, i =>
    let (B', i') := skolemFormAux S B (scope ++ [x]) i
    (.all x B', i')
  | .ex x B, scope, i =>
    if h : i < S.n then
      let idx : Fin S.n := ⟨i, h⟩
      -- The allocation rank selects the constant or function carrier.
      -- For positive ranks this arbitrary-state helper retains its
      -- supplied-scope argument selection; the top-level exact traversal
      -- uses the original allocation's ordered scope.
      let skolemTerm : Term S.language :=
        if hRank : S.skolemRank idx = 0 then
          Term.const (.inr ⟨idx, hRank⟩)
        else
          let skolemFun : S.language.funSymbols :=
            Sum.inr ⟨idx, Nat.pos_of_ne_zero hRank⟩
          Term.func skolemFun
            (fun (k : Fin (S.language.funArity skolemFun)) =>
              match hLen : scope.length with
              | 0 => Term.var x
              | _ + 1 =>
                Term.var
                  (scope.get ⟨k.val % scope.length, by
                    rw [hLen]; exact Nat.mod_lt _ (by omega)⟩))
      let B_sub := formulaSubstN B skolemTerm x
      skolemFormAux S B_sub scope (i + 1)
    else
      -- Totality branch for a legacy arbitrary recursive state. It is
      -- absent from `skolemForm`'s exact descriptor traversal.
      let (B', i') := skolemFormAux S B scope i
      (.ex x B', i')
  termination_by A _ _ => formulaQuantCount A
  decreasing_by
    all_goals
      simp_wf
      try (rw [formulaSubst_quantCount])
      try (simp [formulaQuantCount]; done)
      try (simp [formulaQuantCount]; omega) /- ATTACH-BLOCKER: termination suffix -/

-- The empty-scope allocation is represented by a constant constructor.
example :
    exactSkolemTerm SkolemAllocationRegression.oneSpec
      SkolemAllocationRegression.oneIndex =
      Term.const (L := SkolemAllocationRegression.oneSpec.language)
        (.inr ⟨SkolemAllocationRegression.oneIndex, rfl⟩) := rfl /- ATTACH-BLOCKER: unsupported untagged example -/

-- A nested positive-scope allocation uses every scope variable in order.
example :
    exactSkolemTerm SkolemAllocationRegression.nestedSpec
      SkolemAllocationRegression.nestedIndex1 =
      Term.func (L := SkolemAllocationRegression.nestedSpec.language)
        (.inr ⟨SkolemAllocationRegression.nestedIndex1, by decide⟩)
        (fun k => Term.var ([0, 2].get k)) := rfl /- ATTACH-BLOCKER: unsupported untagged example -/

-- Base constants remain distinct from all freshly allocated constants.
example {L : Language} {n : Nat} {rank : Fin n → Nat}
    (c : L.constSymbols) (i : Fin n) (h : rank i = 0) :
    (Sum.inl c : (SkolemLanguage (L := L) n rank).constSymbols) ≠
      Sum.inr ⟨i, h⟩ := by
  intro heq
  cases heq /- ATTACH-BLOCKER: unsupported untagged example -/

/-- Definition 7.6.2 (helper): Exact allocation-consuming traversal
used by top-level `skolemForm`.

The input index list is split structurally at binary connectives and
must contain exactly one index per existential descriptor. Literals,
implications, and exhausted subtrees reject unused indices; an
existential rejects an empty list. Hence arbitrary malformed states
return `none` instead of silently preserving an existential or
inventing a term. Every successful existential step consumes the
head index and calls `skolemSubst S B x i`. The same `S` is threaded
through every recursive call, so both constant/function selection and
ordered scope come from the original allocation even after substitution.

The returned natural number is the number of consumed allocations.
Top-level success and the equality of that counter with `S.n` are
proved below before the result is extracted with `Option.get`. -/
@[blueprint "chap7__definition_7_6_2"]
def skolemFormExactAux {L : Language} (S : SkolemSpec L) :
    FormulaN S.language → List Nat → List (Fin S.n) →
      Option (FormulaN S.language × Nat)
  | .predN P ts, _, [] => some (.predN P ts, 0)
  | .predN _ _, _, _ :: _ => none
  | .eq_ h t1 t2, _, [] => some (.eq_ h t1 t2, 0)
  | .eq_ _ _ _, _, _ :: _ => none
  | .neg A, _, [] => some (.neg A, 0)
  | .neg _, _, _ :: _ => none
  | .conj A B, scope, indices =>
    let left := indices.take (skolemDescriptorCount A)
    let right := indices.drop (skolemDescriptorCount A)
    match skolemFormExactAux S A scope left,
        skolemFormExactAux S B scope right with
    | some (A', usedA), some (B', usedB) =>
        some (.conj A' B', usedA + usedB)
    | _, _ => none
  | .disj A B, scope, indices =>
    let left := indices.take (skolemDescriptorCount A)
    let right := indices.drop (skolemDescriptorCount A)
    match skolemFormExactAux S A scope left,
        skolemFormExactAux S B scope right with
    | some (A', usedA), some (B', usedB) =>
        some (.disj A' B', usedA + usedB)
    | _, _ => none
  | .impl A B, _, [] => some (.impl A B, 0)
  | .impl _ _, _, _ :: _ => none
  | .all x B, scope, indices =>
    match skolemFormExactAux S B (scope ++ [x]) indices with
    | some (B', used) => some (.all x B', used)
    | none => none
  | .ex _ _, _, [] => none
  | .ex x B, scope, i :: rest =>
    let BSub := skolemSubst S B x i
    match skolemFormExactAux S BSub scope rest with
    | some (B', used) => some (B', used + 1)
    | none => none
  termination_by A _ _ => formulaQuantCount A
  decreasing_by
    all_goals
      simp_wf
      try (rw [skolemSubst_quantCount])
      try (rw [formulaSubst_quantCount])
      try (simp [formulaQuantCount]; done)
      try (simp [formulaQuantCount]; omega) /- ATTACH-BLOCKER: termination suffix -/

/-- Exact traversal succeeds on, and consumes, precisely a descriptor-
count-sized index list. The returned counter is that exact count. -/
theorem skolemFormExactAux_result {L : Language} (S : SkolemSpec L) :
    ∀ (m : Nat) (A : FormulaN S.language) (scope : List Nat)
      (indices : List (Fin S.n)),
      formulaQuantCount A = m →
      indices.length = skolemDescriptorCount A →
      ∃ B, skolemFormExactAux S A scope indices =
        some (B, skolemDescriptorCount A) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro A scope indices hCount hLength
    match A, hCount, hLength with
    | .predN P ts, _, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      refine ⟨.predN P ts, ?_⟩
      simp [skolemFormExactAux, skolemDescriptorCount]
    | .eq_ h t₁ t₂, _, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      refine ⟨.eq_ h t₁ t₂, ?_⟩
      simp [skolemFormExactAux, skolemDescriptorCount]
    | .neg B, _, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      refine ⟨.neg B, ?_⟩
      simp [skolemFormExactAux, skolemDescriptorCount]
    | .conj A B, hCount, hLength =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qA : formulaQuantCount A < m := by omega
      have qB : formulaQuantCount B < m := by omega
      have hALe : skolemDescriptorCount A ≤ indices.length := by
        rw [hLength]
        exact Nat.le_add_right _ _
      have hLeftLength :
          (indices.take (skolemDescriptorCount A)).length =
            skolemDescriptorCount A :=
        List.length_take_of_le hALe
      have hRightLength :
          (indices.drop (skolemDescriptorCount A)).length =
            skolemDescriptorCount B := by
        rw [List.length_drop, hLength]
        simp [skolemDescriptorCount]
      obtain ⟨A', hA'⟩ :=
        ih _ qA A scope (indices.take (skolemDescriptorCount A))
          rfl hLeftLength
      obtain ⟨B', hB'⟩ :=
        ih _ qB B scope (indices.drop (skolemDescriptorCount A))
          rfl hRightLength
      refine ⟨.conj A' B', ?_⟩
      simp [skolemFormExactAux, hA', hB', skolemDescriptorCount]
    | .disj A B, hCount, hLength =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qA : formulaQuantCount A < m := by omega
      have qB : formulaQuantCount B < m := by omega
      have hALe : skolemDescriptorCount A ≤ indices.length := by
        rw [hLength]
        exact Nat.le_add_right _ _
      have hLeftLength :
          (indices.take (skolemDescriptorCount A)).length =
            skolemDescriptorCount A :=
        List.length_take_of_le hALe
      have hRightLength :
          (indices.drop (skolemDescriptorCount A)).length =
            skolemDescriptorCount B := by
        rw [List.length_drop, hLength]
        simp [skolemDescriptorCount]
      obtain ⟨A', hA'⟩ :=
        ih _ qA A scope (indices.take (skolemDescriptorCount A))
          rfl hLeftLength
      obtain ⟨B', hB'⟩ :=
        ih _ qB B scope (indices.drop (skolemDescriptorCount A))
          rfl hRightLength
      refine ⟨.disj A' B', ?_⟩
      simp [skolemFormExactAux, hA', hB', skolemDescriptorCount]
    | .impl A B, _, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      refine ⟨.impl A B, ?_⟩
      simp [skolemFormExactAux, skolemDescriptorCount]
    | .all x B, hCount, hLength =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qB : formulaQuantCount B < m := by omega
      obtain ⟨B', hB'⟩ :=
        ih _ qB B (scope ++ [x]) indices rfl
          (by simpa [skolemDescriptorCount] using hLength)
      refine ⟨.all x B', ?_⟩
      simp [skolemFormExactAux, hB', skolemDescriptorCount]
    | .ex x B, hCount, hLength =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      cases indices with
      | nil =>
        simp [skolemDescriptorCount] at hLength
        omega
      | cons i rest =>
        have hRestLength :
            rest.length = skolemDescriptorCount B := by
          simp [skolemDescriptorCount] at hLength
          omega
        have qBSub :
            formulaQuantCount
                (formulaSubstN B (exactSkolemTerm S i) x) < m := by
          rw [formulaSubst_quantCount]
          omega
        obtain ⟨B', hB'⟩ :=
          ih _ qBSub
            (formulaSubstN B (exactSkolemTerm S i) x)
            scope rest rfl
            (by
              rw [formulaSubstN_descriptorCount]
              exact hRestLength)
        refine ⟨B', ?_⟩
        simp [skolemFormExactAux, skolemSubst, hB',
          skolemDescriptorCount, formulaSubstN_descriptorCount,
          Nat.add_comm] /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

/-- A successful exact traversal has a unique formula component. -/
theorem skolemFormExactAux_formula_unique {L : Language}
    {S : SkolemSpec L} {A : FormulaN S.language}
    {scope : List Nat} {indices : List (Fin S.n)}
    {B₁ B₂ : FormulaN S.language} {used₁ used₂ : Nat}
    (h₁ : skolemFormExactAux S A scope indices = some (B₁, used₁))
    (h₂ : skolemFormExactAux S A scope indices = some (B₂, used₂)) :
    B₁ = B₂ := by
  have hPair :
      (B₁, used₁) = (B₂, used₂) :=
    Option.some.inj (h₁.symm.trans h₂)
  exact congrArg Prod.fst hPair /- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.LowerConstruction, LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds, LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.Herbrand.SHGTheorem.Main.SHG, LCS.Herbrand.SHGTheorem.Main.SkolemEquisatisfiability, LCS.Herbrand.SHGTheorem.Main.SkolemSemanticsBase -/

/-- With no descriptor to consume, the exact traversal is the identity
and returns counter zero. This is the exact-traversal compatibility
fact needed by downstream fragments whose sources contain no
existential quantifier. -/
theorem skolemFormExactAux_eq_self_of_descriptorCount_zero
    {L : Language} (S : SkolemSpec L) :
    ∀ (A : FormulaN S.language) (scope : List Nat),
      skolemDescriptorCount A = 0 →
      skolemFormExactAux S A scope [] = some (A, 0) := by
  intro A
  induction A with
  | predN P ts =>
    intro scope _
    simp [skolemFormExactAux]
  | eq_ h t₁ t₂ =>
    intro scope _
    simp [skolemFormExactAux]
  | neg B ih =>
    intro scope _
    simp [skolemFormExactAux]
  | conj A B ihA ihB =>
    intro scope hZero
    simp only [skolemDescriptorCount, Nat.add_eq_zero_iff] at hZero
    simp [skolemFormExactAux, ihA scope hZero.1, ihB scope hZero.2]
  | disj A B ihA ihB =>
    intro scope hZero
    simp only [skolemDescriptorCount, Nat.add_eq_zero_iff] at hZero
    simp [skolemFormExactAux, ihA scope hZero.1, ihB scope hZero.2]
  | impl A B ihA ihB =>
    intro scope _
    simp [skolemFormExactAux]
  | all x B ih =>
    intro scope hZero
    simp only [skolemDescriptorCount] at hZero
    simp [skolemFormExactAux, ih (scope ++ [x]) hZero]
  | ex x B ih =>
    intro scope hZero
    simp [skolemDescriptorCount] at hZero /- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.Herbrand.SHGTheorem.Main.SHG -/

/-- The full index enumeration has exactly the descriptor count of the
lifted source formula. -/
theorem SkolemSpec.indices_length_eq_lifted_descriptorCount
    {L : Language} (S : SkolemSpec L) :
    S.indices.length =
      skolemDescriptorCount
        (liftFormulaSkolem (skolemRank := S.skolemRank) S.source) := by
  unfold SkolemSpec.indices
  rw [List.length_ofFn, liftFormulaSkolem_descriptorCount,
    S.n_eq_descriptorCount] /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

/-- Top-level index scopes align position-for-position with the
lifted source traversal. -/
theorem SkolemSpec.indices_scopes_lifted {L : Language}
    (S : SkolemSpec L) :
    S.indices.map S.skolemScope =
      existentialScopesAux
        (liftFormulaSkolem (skolemRank := S.skolemRank) S.source) [] := by
  rw [liftFormulaSkolem_existentialScopesAux]
  exact S.indices_scopes /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

/-- Top-level exact traversal succeeds and returns final counter
`S.n`; hence every allocation is consumed and no extra allocation is
left unused. -/
theorem skolemFormExactAux_top_result {L : Language}
    (S : SkolemSpec L) :
    ∃ B, skolemFormExactAux S
        (liftFormulaSkolem (skolemRank := S.skolemRank) S.source)
        [] S.indices = some (B, S.n) := by
  obtain ⟨B, hB⟩ :=
    skolemFormExactAux_result S _
      (liftFormulaSkolem (skolemRank := S.skolemRank) S.source)
      [] S.indices rfl S.indices_length_eq_lifted_descriptorCount
  have hCounter :
      skolemDescriptorCount
          (liftFormulaSkolem (skolemRank := S.skolemRank) S.source) =
        S.n := by
    rw [liftFormulaSkolem_descriptorCount]
    exact S.n_eq_descriptorCount.symm
  exact ⟨B, hB.trans (congrArg (fun k => some (B, k)) hCounter)⟩ /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

/-- Boolean proof used by `Option.get` in `skolemFormTraversal`. -/
theorem skolemFormExactAux_top_isSome {L : Language}
    (S : SkolemSpec L) :
    (skolemFormExactAux S
      (liftFormulaSkolem (skolemRank := S.skolemRank) S.source)
      [] S.indices).isSome = true := by
  obtain ⟨B, hB⟩ := skolemFormExactAux_top_result S
  exact Option.isSome_iff_exists.mpr ⟨(B, S.n), hB⟩ /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

/-- The top-level traversal embeds `S.source` into the split Skolem
language and consumes `S.indices` in preorder. All recursive substitutions
keep this original `S` and the corresponding allocation indices.
`skolemFormExactAux_top_isSome` proves success before result extraction. -/
def skolemFormTraversal {L : Language} (S : SkolemSpec L) :
    FormulaN S.language × Nat :=
  (skolemFormExactAux S
    (liftFormulaSkolem (skolemRank := S.skolemRank) S.source)
    [] S.indices).get (skolemFormExactAux_top_isSome S) /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/



/-- Definition 7.6.2: Skolem form of the rectified NNF sentence `S.source`
in its extended language. Literals retain their embedded terms; conjunction
and disjunction recurse on both children; universal quantifiers remain.
Each existential is eliminated by `skolemSubst` using its original allocation
index: empty scope yields a fresh constant, and positive scope yields its
fresh function applied to the full ordered scope. Recursive substitution
retains the original `S`, so the scope of a detached body is never used to
allocate symbols. The traversal consumes all `S.n` occurrences in preorder. -/
@[blueprint "chap7__definition_7_6_2" (main := true)]
def skolemForm {L : Language} (S : SkolemSpec L) :
    FormulaN S.language :=
  (skolemFormTraversal S).1

/-- Public equation for downstream structural proofs: the exact
top-level traversal returns precisely `skolemForm S` and consumes
precisely `S.n` allocations. -/
theorem skolemFormExactAux_top_formula_result {L : Language}
    (S : SkolemSpec L) :
    skolemFormExactAux S
        (liftFormulaSkolem (skolemRank := S.skolemRank) S.source)
        [] S.indices =
      some (skolemForm S, S.n) := by
  obtain ⟨B, hB⟩ := skolemFormExactAux_top_result S
  have hGet :
      skolemFormTraversal S = (B, S.n) :=
    Option.get_of_eq_some (skolemFormExactAux_top_isSome S) hB
  simpa [skolemForm, hGet] using hB /- retained: used by LCS.Herbrand.SHGTheorem.Main.SHG, LCS.Herbrand.SHGTheorem.Main.SkolemEquisatisfiability, LCS.Herbrand.SHGTheorem.Main.SkolemSemanticsBase, LCS.Herbrand.SHGTheorem.Part3.Proofs, LCS.SLD.FirstOrder.GroundSemantics -/

/-- If the computed allocation is empty, top-level Skolemization is
exactly the pure language lift. This is the compatibility boundary for
downstream no-existential source arguments; it does not route through
the legacy numeric-counter helper. -/
theorem skolemForm_eq_liftFormulaSkolem_of_n_eq_zero {L : Language}
    (S : SkolemSpec L) (hZero : S.n = 0) :
    skolemForm S =
      liftFormulaSkolem (skolemRank := S.skolemRank) S.source := by
  have hDescriptorZero : skolemDescriptorCount S.source = 0 := by
    rw [← S.n_eq_descriptorCount]
    exact hZero
  have hLiftDescriptorZero :
      skolemDescriptorCount
          (liftFormulaSkolem (skolemRank := S.skolemRank) S.source) = 0 := by
    rw [liftFormulaSkolem_descriptorCount]
    exact hDescriptorZero
  have hIndices : S.indices = [] := by
    apply List.length_eq_zero_iff.mp
    rw [S.indices_length_eq_lifted_descriptorCount,
      hLiftDescriptorZero]
  have hSelf :=
    skolemFormExactAux_eq_self_of_descriptorCount_zero S
      (liftFormulaSkolem (skolemRank := S.skolemRank) S.source) []
      hLiftDescriptorZero
  have hTop := skolemFormExactAux_top_formula_result S
  rw [hIndices] at hTop
  have hPairs :
      (liftFormulaSkolem (skolemRank := S.skolemRank) S.source, 0) =
        (skolemForm S, S.n) :=
    Option.some.inj (hSelf.symm.trans hTop)
  exact (congrArg Prod.fst hPairs).symm /- retained: used by LCS.SLD.FirstOrder.GroundInstances -/

-- ===================================================================
-- Definition 7.6.2 (companion abbrev): SK
-- ===================================================================

/-- Definition 7.6.2: `SK S` is the Skolem form of the original rectified
NNF sentence `S.source`, in the extension containing its fresh constants and
positive-rank functions. It uses the same original occurrence allocation
throughout the traversal. -/
@[blueprint "chap7__definition_7_6_2"]
abbrev SK {L : Language} (S : SkolemSpec L) : FormulaN S.language :=
  skolemForm S

end LCS.Herbrand.SHGTheorem
end

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.HerbrandTheorem
namespace SkolemAllocationRegression





















end SkolemAllocationRegression
end LCS.Herbrand.SHGTheorem
end

