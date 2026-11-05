import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.HerbrandTheorem
import LCS.Herbrand.SHGTheorem.Part1
import LCS.Herbrand.SHGTheorem.Part2
import Attach
import LCS.Herbrand.SHGTheorem.Part3.ProofsStamp

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.HerbrandTheorem
namespace CInstance

/-- Definition 7.6.3: Extract the formula of a compound instance.
Literal and binary-connective nodes preserve their constructors. A universal
node with children `h₀, h₁, ..., hₖ` produces the right-nested conjunction
`H₀ ∧ (H₁ ∧ ... ∧ Hₖ)` in that order. A sole child produces `H₀`.
The constructor supplies `h₀` structurally, enforcing nonemptiness. -/
@[blueprint "chap7__definition_7_6_3"]
def toFormula {L : Language} : CInstance L → FormulaN L
  | .atom B _ => B
  | .negAtom B _ => .neg B
  | .connective true _ _ H K => .conj (toFormula H) (toFormula K)
  | .connective false _ _ H K => .disj (toFormula H) (toFormula K)
  | .forallInst _ _ _ h₀ _ hsRest _ _ =>
    -- Each suffix receives its first child, so no terminal formula is added.
    (hsRest.map toFormula).foldr
      (fun f rest first => .conj first (rest f)) id (toFormula h₀)

-- Universal output preserves singleton, binary, and ternary child order.
-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} (x : Nat) (C : FormulaN L) (t : Term L)
    (hg : t.isClosed) (H : CInstance L) :
    (forallInst x C t H [] [] hg (by simp)).toFormula = H.toFormula := by
  simp [toFormula]

-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} (x : Nat) (C : FormulaN L) (t : Term L)
    (hg : t.isClosed) (H K : CInstance L) :
    (forallInst x C t H [t] [K] hg (by simpa using hg)).toFormula =
      FormulaN.conj H.toFormula K.toFormula := by
  simp [toFormula]

-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} (x : Nat) (C : FormulaN L) (t : Term L)
    (hg : t.isClosed) (H K J : CInstance L) :
    (forallInst x C t H [t, t] [K, J] hg (by simpa using hg)).toFormula =
      FormulaN.conj H.toFormula (FormulaN.conj K.toFormula J.toFormula) := by
  simp [toFormula]

-- ===================================================================
-- Definition 7.6.3 (companion def): CInstance.closedTerms
-- ===================================================================

/-- Definition 7.6.3 (companion def): Extracts the closed terms used in universal quantifier instantiations within a compound instance derivation tree. -/
@[blueprint "chap7__definition_7_6_3"]
def closedTerms {L : Language} : CInstance L → List (Term L)
  | .atom _ _ => []
  | .negAtom _ _ => []
  | .connective _ _ _ H K => closedTerms H ++ closedTerms K
  | .forallInst _ _ t₀ h₀ tsRest hsRest _ _ =>
    (t₀ :: tsRest) ++ (closedTerms h₀ ++ hsRest.flatMap closedTerms)

/-- Definition 7.6.3 (companion def): Reconstructs the source Skolem form formula from which a CInstance derivation tree was built. - atom B _ => B (the atomic formula) - negAtom B _ => neg B (the negated atomic formula) - connective true C D _ _ => conj C D (recorded by the constructor) - connective false C D _ _ => disj C D (recorded by the constructor) - forallInst x C ts hs => all x C (the universal quantifier) -/
@[blueprint "chap7__definition_7_6_3"]
def source {L : Language} : CInstance L → FormulaN L
  | .atom B _ => B
  | .negAtom B _ => .neg B
  | .connective true C D _ _ => .conj C D
  | .connective false C D _ _ => .disj C D
  | .forallInst x C _ _ _ _ _ _ => .all x C

end CInstance
end LCS.Herbrand.SHGTheorem
end

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Substitution

-- ATTACH-BLOCKER: mutual
mutual
/-- Definition 7.6.3 (companion def): A CInstance derivation tree is WellFormed when every node's children have sources matching the textbook's Def 7.6.3 conditions: - `connective star C D H K`: sources of H and K match the parent's operands (Def 7.6.3(ii) requirement that H is a c-instance *of C* and K is a c-instance *of D*), and both children are recursively WellFormed. - `forallInst x C t₀ h₀ tsRest hsRest`: lengths `tsRest.length = hsRest.length` match, `h₀.source = C[t₀/x]` and each `hsRest[i]` has source `C[tsRest[i]/x]`, and every child is recursively WellFormed. (Non-emptiness k ≥ 1 is enforced structurally by the constructor splitting out `t₀, h₀`.) For atom and negAtom nodes, WellFormed holds trivially (no children). -/
@[blueprint "chap7__definition_7_6_3"]
def CInstance.WellFormed {L : Language} : CInstance L → Prop
  | .atom _ _ => True
  | .negAtom _ _ => True
  | .connective _ C D H K =>
    CInstance.source H = C ∧ CInstance.source K = D ∧
    CInstance.WellFormed H ∧ CInstance.WellFormed K
  | .forallInst x C t₀ h₀ tsRest hsRest _ _ =>
    h₀.source = formulaSubstN C t₀ x ∧
    CInstance.WellFormed h₀ ∧
    CInstance.WellFormedList x C tsRest hsRest

/-- Definition 7.6.3 (companion def): Auxiliary for WellFormed that
walks the parallel lists of terms and c-instance children, checking
each child's source matches the substitution instance. -/
@[blueprint "chap7__definition_7_6_3"]
def CInstance.WellFormedList {L : Language} (x : Nat) (C : FormulaN L)
    : List (Term L) → List (CInstance L) → Prop
  | [], [] => True
  | t :: ts, h :: hs =>
    h.source = formulaSubstN C t x ∧ CInstance.WellFormed h ∧
    CInstance.WellFormedList x C ts hs
  | _, _ => False
end

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem CInstance.WellFormedList_append {L : Language}
    (x : Nat) (C : FormulaN L)
    (ts1 : List (Term L)) (hs1 : List (CInstance L))
    (ts2 : List (Term L)) (hs2 : List (CInstance L))
    (h1 : CInstance.WellFormedList x C ts1 hs1)
    (h2 : CInstance.WellFormedList x C ts2 hs2) :
    CInstance.WellFormedList x C (ts1 ++ ts2) (hs1 ++ hs2) := by
-- BEGIN PROOF
  induction ts1 generalizing hs1 with
  | nil =>
    cases hs1 with
    | nil => exact h2
    | cons _ _ => exact absurd h1 id
  | cons t ts1 ih =>
    cases hs1 with
    | nil => exact absurd h1 id
    | cons h hs1 =>
      obtain ⟨hsrc, hwf, hrest⟩ := h1
      simp [List.cons_append]
      exact ⟨hsrc, hwf, ih hs1 hrest⟩

-- ===================================================================
-- Lemma 7.6.1 (required def): isSkolemNormalForm
-- ===================================================================

/-- Lemma 7.6.1 (required def, STRUCTURAL piece): structural shape-check ensuring a formula has no existential quantifiers and negations only apply to atomic formulae. This is the NNF+no-existential piece of the Skolem-normal-form check; rectification and closed-ness (sentence-hood) are enforced at the top level via `isSkolemNormalForm` (see below). -/
@[blueprint "chap7__definition_7_6_2"]
def isSkolemNormalFormShape {L : Language} : FormulaN L → Prop
  | .predN _ _ => True
  | .eq_ _ _ _ => True
  | .neg A => A.isAtomic
  | .conj A B =>
    isSkolemNormalFormShape A ∧ isSkolemNormalFormShape B
  | .disj A B =>
    isSkolemNormalFormShape A ∧ isSkolemNormalFormShape B
  | .all _ B => isSkolemNormalFormShape B
  | .ex _ _ => False
  | .impl _ _ => False

/-- Lemma 7.6.1 (required def): A formula is in Skolem normal form (Definition 7.6.2) iff all existential quantifiers have been eliminated AND the formula is a rectified sentence (Def 5.3.10 + Def 5.2.5). Structurally, a Skolem normal form formula: - Contains no existential quantifiers (no .ex constructors), - Has universal quantifiers only at outermost prenex positions (the body under each forall is again in Skolem-normal shape), - Propositional connectives (conj, disj) have Skolem-normal subformulae, - Literals (atomic, negated atomic) are structurally SK-normal. Plus the textbook conditions "rectified" (`isRectified`) and "sentence" (`FormulaN.isClosed`, i.e. no free variables) from Def 7.6.2's standing assumption "Given a rectified sentence A". Defined here (rather than alongside Lemma 7.6.1 in SHGTheorem/Herbrand.lean) because `isCInstanceOf` in Def 7.6.3 requires its argument B to be a Skolem form. -/
@[blueprint "chap7__definition_7_6_2"]
def isSkolemNormalForm {L : Language} (A : FormulaN L) : Prop :=
  isSkolemNormalFormShape A ∧
  LCS.FirstOrder.Semantics.Subformulae.isRectified A ∧
  LCS.FirstOrder.SyntaxN.Variables.FormulaN.isClosed A

-- ===================================================================
-- Definition 7.6.3 (companion def): isCInstanceOf
-- ===================================================================

/-- Definition 7.6.3 (companion def): Predicate that a formula H is a c-instance of the Skolem form B: there exists a CInstance derivation `ci` derived from B such that `ci.toFormula = H` and the derivation is WellFormed. The `CInstance.source` function reconstructs the source formula from the derivation tree, ensuring the derivation actually corresponds to B. The WellFormed condition ensures that `forallInst` children have sources matching the substitution instances of their parent's body. Textbook Def 7.6.3 opens with "Let A be a rectified sentence and let B be its Skolem form" — this is an EXTERNAL framing assumption on theorems that USE `isCInstanceOf` (e.g. Lem 7.6.1 `cInstance_combination`, `herbrand_half_lemma`), NOT an internal conjunct of the membership predicate. Clause (i) of the textbook ("atomic B is its own c-instance") holds WITHOUT any rectified/closed hypothesis on B, so bundling `isSkolemNormalForm B` inside would be strictly stronger than the textbook relation. -/
@[blueprint "chap7__definition_7_6_3" (main := true)]
def isCInstanceOf {L : Language}
    (H : FormulaN L) (B : FormulaN L) : Prop :=
  ∃ (ci : CInstance L), ci.source = B ∧ ci.toFormula = H ∧
    CInstance.WellFormed ci

end LCS.Herbrand.SHGTheorem
end

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Substitution
section SkExComputation
-- ATTACH-BLOCKER: global set_option
set_option backward.isDefEq.respectTransparency false

/-- Example 7.6.3: the fixed original-root environment for all four
Skolem computations. Its allocations are y, u, w, in preorder. -/
@[blueprint "chap7__example_7_6_3"]
def skExSpec : SkolemSpec usExLang where
  source := usExFormula
  hNNF := by trivial
  hRect := by
    simp [usExFormula, usExLang,
      LCS.FirstOrder.Semantics.Subformulae.isRectified,
      LCS.FirstOrder.Semantics.Subformulae.boundVarsFresh,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
      LCS.FirstOrder.SyntaxN.Variables.formulaFVN, LCS.FirstOrder.SyntaxN.Variables.formulaBVN, termFV, Membership.mem,
      Set.iUnion, Set.union, Set.diff, Set.singleton, Set.empty,
      usExVec1, usExVec2, Fin.exists_fin_succ, Fin.forall_fin_succ] <;>
      (try constructor) <;> (intros; omega)
  hSentence := by
    change LCS.FirstOrder.SyntaxN.Variables.formulaFVN usExFormula = (∅ : Set Nat)
    funext x
    apply propext
    simp [usExFormula, usExLang, LCS.FirstOrder.SyntaxN.Variables.formulaFVN, termFV, Membership.mem,
      Set.iUnion, Set.union, Set.diff, Set.singleton, Set.empty,
      usExVec1, usExVec2, Fin.exists_fin_succ, Fin.forall_fin_succ] <;> omega

/-- Example 7.6.3: the positive-rank fresh functions allocated to A.
The names g and f below identify the original y and u indices. -/
@[blueprint "chap7__example_7_6_3"]
abbrev SKExSkolemFunc : Type := skExSpec.language.funSymbols

@[blueprint "chap7__example_7_6_3"]
def SKExSkolemFunc.g : SKExSkolemFunc := .inr ⟨⟨0, by decide⟩, by decide⟩
@[blueprint "chap7__example_7_6_3"]
def SKExSkolemFunc.f : SKExSkolemFunc := .inr ⟨⟨1, by decide⟩, by decide⟩

/-- Example 7.6.3: the exact Skolem extension of the original language.
The old constant a embeds on the left; the fresh constant c is allocated
to w. The positive-rank allocations are g for y and f for u. -/
@[blueprint "chap7__example_7_6_3"]
def skExSkolemLang : Language := skExSpec.language

/-- Example 7.6.3: the genuine fresh constant allocated to the empty
universal scope of w, distinct from every embedded base constant. -/
@[blueprint "chap7__example_7_6_3"]
def skExC : skExSkolemLang.constSymbols := .inr ⟨⟨2, by decide⟩, by decide⟩

-- ===================================================================
-- Example 7.6.3 (helpers): skExVec1, skExVec2
-- ===================================================================

/-- Example 7.6.3 (companion def): Build a Fin 1 -> Term from a single
term in skExSkolemLang. -/
@[blueprint "chap7__example_7_6_3"]
def skExVec1 (t : Term skExSkolemLang) :
    Fin 1 → Term skExSkolemLang
  | ⟨0, _⟩ => t

/-- Example 7.6.3 (companion def): Build a Fin 2 -> Term from two terms
in skExSkolemLang. -/
@[blueprint "chap7__example_7_6_3"]
def skExVec2 (t1 t2 : Term skExSkolemLang) :
    Fin 2 → Term skExSkolemLang
  | ⟨0, _⟩ => t1
  | ⟨1, _⟩ => t2

-- Variables: x = 0, y = 1, z = 2, u = 3, w = 4.

-- ===================================================================
-- Example 7.6.3: skExFormula
-- ===================================================================

/-- Example 7.6.3: The formula A = forall x(P(a) or exists y(Q(y) and forall z(P(y, z) or exists u Q(x, u)))) or exists w Q(a, w), same formula as Example 7.6.2, reencoded in skExSkolemLang for demonstrating the Skolem form computation. Variables: x = 0, y = 1, z = 2, u = 3, w = 4. -/
@[blueprint "chap7__example_7_6_3"]
def skExFormula : FormulaN skExSkolemLang :=
  FormulaN.disj
    (FormulaN.all 0
      (FormulaN.disj
        (FormulaN.predN USExPred.P1
          (skExVec1 (.const (.inl USExConst.a))))
        (FormulaN.ex 1
          (FormulaN.conj
            (FormulaN.predN USExPred.Q1
              (skExVec1 (.var 1)))
            (FormulaN.all 2
              (FormulaN.disj
                (FormulaN.predN USExPred.P2
                  (skExVec2 (.var 1) (.var 2)))
                (FormulaN.ex 3
                  (FormulaN.predN USExPred.Q2
                    (skExVec2 (.var 0) (.var 3))))))))))
    (FormulaN.ex 4
      (FormulaN.predN USExPred.Q2
        (skExVec2 (.const (.inl USExConst.a)) (.var 4))))

-- ===================================================================
-- Example 7.6.3 (companion def): skExSKExistsW
-- ===================================================================

/-- Example 7.6.3 (companion def): SK(exists w Q(a, w)) = Q(a, c), where c is the Skolem constant for the empty universal scope. The existential quantifier exists w is eliminated by replacing w with the Skolem constant c (a fresh constant symbol). -/
@[blueprint "chap7__example_7_6_3"]
def skExSKExistsW : FormulaN skExSkolemLang :=
  FormulaN.predN USExPred.Q2
    (skExVec2 (.const (.inl USExConst.a))
      (Term.const skExC))

-- ===================================================================
-- Example 7.6.3 (companion def): skExSKExistsU
-- ===================================================================

/-- Example 7.6.3 (companion def): SK(exists u Q(x, u)) = Q(x, f(x, z)), where f is the binary Skolem function for the universal scope <x, z>. Variables: x = 0, z = 2. -/
@[blueprint "chap7__example_7_6_3"]
def skExSKExistsU : FormulaN skExSkolemLang :=
  FormulaN.predN USExPred.Q2
    (skExVec2 (.var 0)
      (Term.func SKExSkolemFunc.f
        (skExVec2 (.var 0) (.var 2))))

-- ===================================================================
-- Example 7.6.3 (companion def): skExSKExistsY
-- ===================================================================

/-- Example 7.6.3 (companion def): SK(exists y(Q(y) and forall z(P(y, z) or exists u Q(x, u)))) = Q(g(x)) and forall z(P(g(x), z) or Q(x, f(x, z))), where g is the unary Skolem function for the universal scope <x>. Variables: x = 0, z = 2. -/
@[blueprint "chap7__example_7_6_3"]
def skExSKExistsY : FormulaN skExSkolemLang :=
  let gx := Term.func SKExSkolemFunc.g (skExVec1 (.var 0))
  FormulaN.conj
    (FormulaN.predN USExPred.Q1 (skExVec1 gx))
    (FormulaN.all 2
      (FormulaN.disj
        (FormulaN.predN USExPred.P2 (skExVec2 gx (.var 2)))
        (FormulaN.predN USExPred.Q2
          (skExVec2 (.var 0)
            (Term.func SKExSkolemFunc.f
              (skExVec2 (.var 0) (.var 2)))))))

-- ===================================================================
-- Example 7.6.3 (companion def): skExFullSK
-- ===================================================================

/-- Example 7.6.3 (companion def): The complete Skolem form SK(A) = forall x(P(a) or (Q(g(x)) and forall z(P(g(x), z) or Q(x, f(x, z))))) or Q(a, c). Variables: x = 0, z = 2. -/
@[blueprint "chap7__example_7_6_3"]
def skExFullSK : FormulaN skExSkolemLang :=
  let gx := Term.func SKExSkolemFunc.g (skExVec1 (.var 0))
  FormulaN.disj
    (FormulaN.all 0
      (FormulaN.disj
        (FormulaN.predN USExPred.P1
          (skExVec1 (.const (.inl USExConst.a))))
        (FormulaN.conj
          (FormulaN.predN USExPred.Q1 (skExVec1 gx))
          (FormulaN.all 2
            (FormulaN.disj
              (FormulaN.predN USExPred.P2
                (skExVec2 gx (.var 2)))
              (FormulaN.predN USExPred.Q2
                (skExVec2 (.var 0)
                  (Term.func SKExSkolemFunc.f
                    (skExVec2 (.var 0) (.var 2))))))))))
    (FormulaN.predN USExPred.Q2
      (skExVec2 (.const (.inl USExConst.a))
        (Term.const skExC)))

-- ATTACH-BLOCKER: section options: helper requires front context
/-- The original-root preorder allocations retain the full scopes x and
x,z, and allocate a genuine constant to the empty scope of w. -/
theorem skExAllocations :
    skExSpec.allocations =
      [(usExExistsYSubformula, [0]), (usExExistsUSubformula, [0, 2]),
        (usExExistsWSubformula, [])] := rfl

-- ATTACH-BLOCKER: section options: helper requires front context
/-- The concrete allocation-to-name map: index 0 is g, index 1 is f,
and index 2 is c; the new constant is distinct from the old constant a. -/
theorem skExAllocationNames :
    SkolemLanguage.symbolLookup (L := usExLang)
      (skolemRank := skExSpec.skolemRank) 0 (by decide) =
        Sum.inr SKExSkolemFunc.g ∧
    SkolemLanguage.symbolLookup (L := usExLang)
      (skolemRank := skExSpec.skolemRank) 1 (by decide) =
        Sum.inr SKExSkolemFunc.f ∧
    SkolemLanguage.symbolLookup (L := usExLang)
      (skolemRank := skExSpec.skolemRank) 2 (by decide) =
        Sum.inl skExC ∧
    skExC ≠ Sum.inl USExConst.a := by
  exact ⟨rfl, rfl, rfl, by intro h; cases h⟩

-- ATTACH-BLOCKER: section options: helper requires front context
/-- The displayed input is the embedding of the same original sentence A. -/
theorem skExFormula_origin :
    liftFormulaSkolem (skolemRank := skExSpec.skolemRank) usExFormula =
      skExFormula := by
  simp [skExFormula, skExSKExistsW, skExSKExistsU, skExSKExistsY, skExFullSK,
    usExFormula, usExExistsWSubformula, usExExistsUSubformula, usExExistsYSubformula,
    skolemFormExactAux, skolemSubst, exactSkolemTerm, exactSkolemArgument,
    liftFormulaSkolem, liftTermSkolem, formulaSubstN, termSubst,
    SkolemSpec.n, SkolemSpec.allocations, SkolemSpec.allocation,
    SkolemSpec.skolemRank, SkolemSpec.skolemScope, existentialDescriptors,
    existentialDescriptorsAux, skolemDescriptorCount,
    skExSkolemLang, SkolemSpec.language, SkolemLanguage,
    SKExSkolemFunc.f, SKExSkolemFunc.g, skExC, usExLang,
    usExVec1, usExVec2, skExVec1, skExVec2,
    funext_iff, Fin.forall_fin_succ]

/-- Fixed-origin SK equation for w, using original allocation index 2. -/
@[blueprint "chap7__example_7_6_3" (main := true)]
theorem skExSKExistsW_eq :
    skolemFormExactAux skExSpec
      (liftFormulaSkolem (skolemRank := skExSpec.skolemRank) usExExistsWSubformula)
      [] [⟨2, by decide⟩] = some (skExSKExistsW, 1) 

/-- Fixed-origin SK equation for u: index 1 retains both x and z, even
though z does not occur free in the detached formula exists u Q(x,u). -/
@[blueprint "chap7__example_7_6_3" (main := true)]
theorem skExSKExistsU_eq :
    skolemFormExactAux skExSpec
      (liftFormulaSkolem (skolemRank := skExSpec.skolemRank) usExExistsUSubformula)
      [0, 2] [⟨1, by decide⟩] = some (skExSKExistsU, 1) 

/-- Fixed-origin SK equation for y and its nested u, using indices 0,1
of the original A rather than allocating symbols from the detached body. -/
@[blueprint "chap7__example_7_6_3" (main := true)]
theorem skExSKExistsY_eq :
    skolemFormExactAux skExSpec
      (liftFormulaSkolem (skolemRank := skExSpec.skolemRank) usExExistsYSubformula)
      [0] [⟨0, by decide⟩, ⟨1, by decide⟩] = some (skExSKExistsY, 2) 

/-- The complete displayed SK(A), computed using the same original-root
allocation environment as the three indexed subformula equations. -/
@[blueprint "chap7__example_7_6_3" (main := true)]
theorem skExFullSK_eq : SK skExSpec = skExFullSK  

end SkExComputation
end LCS.Herbrand.SHGTheorem
end

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Substitution

/-- Example 7.6.4 (companion type): Predicate symbols for the
compound instance example: P (unary) and Q (binary). -/
@[blueprint "chap7__example_7_6_4"]
inductive CInstExPred : Type where
  | P : CInstExPred
  | Q : CInstExPred

-- ===================================================================
-- Example 7.6.4 (companion type): CInstExConst
-- ===================================================================

/-- Example 7.6.4 (companion type): Constant symbols for the
compound instance example: a and b. -/
@[blueprint "chap7__example_7_6_4"]
inductive CInstExConst : Type where
  | a : CInstExConst
  | b : CInstExConst

-- ===================================================================
-- Example 7.6.4 (companion type): CInstExFunc
-- ===================================================================

/-- Example 7.6.4 (companion type): Function symbols for the
compound instance example: f (unary). -/
@[blueprint "chap7__example_7_6_4"]
inductive CInstExFunc : Type where
  | f : CInstExFunc

-- ===================================================================
-- Example 7.6.4 (companion def): cInstExLang
-- ===================================================================

/-- Example 7.6.4 (companion def): A language with unary predicate P,
binary predicate Q, constants a and b, and unary function symbol f. -/
@[blueprint "chap7__example_7_6_4"]
def cInstExLang : Language where
  funSymbols := CInstExFunc
  funArity := fun | .f => 1
  constSymbols := CInstExConst
  predSymbols := CInstExPred
  predArity := fun
    | .P => 1
    | .Q => 2

-- ===================================================================
-- Example 7.6.4 (helpers): cInstExVec1, cInstExVec2
-- ===================================================================

/-- Example 7.6.4 (companion def): Build a Fin 1 -> Term from a single
term in cInstExLang. -/
@[blueprint "chap7__example_7_6_4"]
def cInstExVec1 (t : Term cInstExLang) :
    Fin 1 → Term cInstExLang
  | ⟨0, _⟩ => t

/-- Example 7.6.4 (companion def): Build a Fin 2 -> Term from two terms
in cInstExLang. -/
@[blueprint "chap7__example_7_6_4"]
def cInstExVec2 (t1 t2 : Term cInstExLang) :
    Fin 2 → Term cInstExLang
  | ⟨0, _⟩ => t1
  | ⟨1, _⟩ => t2

-- Variables: x = 0, y = 1.

-- ===================================================================
-- Example 7.6.4: cInstExSkolemForm
-- ===================================================================

/-- Example 7.6.4: The Skolem form B = forall x(P(x) or forall y Q(y, f(x))) and (not P(a) and (not Q(a, f(a)) or not Q(b, f(a)))). Variables: x = 0, y = 1. -/
@[blueprint "chap7__example_7_6_4"]
def cInstExSkolemForm : FormulaN cInstExLang :=
  let fa := Term.func CInstExFunc.f
    (cInstExVec1 (.const CInstExConst.a))
  FormulaN.conj
    (FormulaN.all 0
      (FormulaN.disj
        (FormulaN.predN CInstExPred.P (cInstExVec1 (.var 0)))
        (FormulaN.all 1
          (FormulaN.predN CInstExPred.Q
            (cInstExVec2 (.var 1)
              (Term.func CInstExFunc.f
                (cInstExVec1 (.var 0))))))))
    (FormulaN.conj
      (FormulaN.neg
        (FormulaN.predN CInstExPred.P
          (cInstExVec1 (.const CInstExConst.a))))
      (FormulaN.disj
        (FormulaN.neg
          (FormulaN.predN CInstExPred.Q
            (cInstExVec2 (.const CInstExConst.a) fa)))
        (FormulaN.neg
          (FormulaN.predN CInstExPred.Q
            (cInstExVec2 (.const CInstExConst.b) fa)))))

-- ===================================================================
-- Example 7.6.4 (companion def): cInstExCInstance
-- ===================================================================

/-- Example 7.6.4 (companion def): The c-instance (P(a) or (Q(a, f(a)) and Q(b, f(a)))) and (not P(a) and (not Q(a, f(a)) or not Q(b, f(a)))). Obtained by: instantiating forall x with a, then instantiating forall y with a and b, producing Q(a, f(a)) and Q(b, f(a)). -/
@[blueprint "chap7__example_7_6_4"]
def cInstExCInstance : FormulaN cInstExLang :=
  let fa := Term.func CInstExFunc.f
    (cInstExVec1 (.const CInstExConst.a))
  FormulaN.conj
    (FormulaN.disj
      (FormulaN.predN CInstExPred.P
        (cInstExVec1 (.const CInstExConst.a)))
      (FormulaN.conj
        (FormulaN.predN CInstExPred.Q
          (cInstExVec2 (.const CInstExConst.a) fa))
        (FormulaN.predN CInstExPred.Q
          (cInstExVec2 (.const CInstExConst.b) fa))))
    (FormulaN.conj
      (FormulaN.neg
        (FormulaN.predN CInstExPred.P
          (cInstExVec1 (.const CInstExConst.a))))
      (FormulaN.disj
        (FormulaN.neg
          (FormulaN.predN CInstExPred.Q
            (cInstExVec2 (.const CInstExConst.a) fa)))
        (FormulaN.neg
          (FormulaN.predN CInstExPred.Q
            (cInstExVec2 (.const CInstExConst.b) fa)))))

-- ===================================================================
-- Example 7.6.4 (companion def): cInstExDerivation
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 7.6.4 (companion def): The derivation tree witnessing that cInstExCInstance is a c-instance of cInstExSkolemForm. Constructed using: - connective true (outer conjunction) - forallInst 0 _ [a] [outer disjunction c-instance] - connective false (disjunction: P(a) or ...) - atom P(a) - forallInst 1 _ [a, b] [atom Q(a,f(a)), atom Q(b,f(a))] - connective true (inner conjunction) - negAtom P(a) - connective false (inner disjunction) - negAtom Q(a, f(a)) - negAtom Q(b, f(a)) -/
def cInstExDerivation : CInstance cInstExLang :=
  let fa := Term.func CInstExFunc.f
    (cInstExVec1 (.const CInstExConst.a))
  -- P(a) is atomic
  let pa := FormulaN.predN CInstExPred.P
    (cInstExVec1 (.const CInstExConst.a))
  -- Q(a, f(a)) is atomic
  let qafa := FormulaN.predN CInstExPred.Q
    (cInstExVec2 (.const CInstExConst.a) fa)
  -- Q(b, f(a)) is atomic
  let qbfa := FormulaN.predN CInstExPred.Q
    (cInstExVec2 (.const CInstExConst.b) fa)
  -- Parent shape operands for the outer conjunction / inner disj / inner conj
  let pxBody := FormulaN.predN CInstExPred.P (cInstExVec1 (.var 0))
  let allyQ := FormulaN.all 1
    (FormulaN.predN CInstExPred.Q
      (cInstExVec2 (.var 1)
        (Term.func CInstExFunc.f
          (cInstExVec1 (.var 0)))))
  let outerForallBody := FormulaN.disj pxBody allyQ
  let outerForall := FormulaN.all 0 outerForallBody
  let notPa := FormulaN.neg
    (FormulaN.predN CInstExPred.P
      (cInstExVec1 (.const CInstExConst.a)))
  let notQafa := FormulaN.neg
    (FormulaN.predN CInstExPred.Q
      (cInstExVec2 (.const CInstExConst.a) fa))
  let notQbfa := FormulaN.neg
    (FormulaN.predN CInstExPred.Q
      (cInstExVec2 (.const CInstExConst.b) fa))
  let innerDisj := FormulaN.disj notQafa notQbfa
  let innerConj := FormulaN.conj notPa innerDisj
  -- Inner forall y Q(y, f(a)) instantiated with a and b (k=2: t₀=a, tsRest=[b])
  let innerForallInstBody := FormulaN.predN CInstExPred.Q
    (cInstExVec2 (.var 1)
      (Term.func CInstExFunc.f
        (cInstExVec1 (.const CInstExConst.a))))
  let innerForallInst :=
    CInstance.forallInst 1 innerForallInstBody
      (.const CInstExConst.a) (CInstance.atom qafa rfl)
      [.const CInstExConst.b]
      [CInstance.atom qbfa rfl]
      (by simp [LCS.FirstOrder.Basic.Term.isClosed,
                LCS.FirstOrder.Basic.termFV])
      (by intro t ht; simp at ht; subst ht;
          simp [LCS.FirstOrder.Basic.Term.isClosed,
                LCS.FirstOrder.Basic.termFV])
  -- P(a) or (Q(a,f(a)) and Q(b,f(a)))
  let leftDisj :=
    CInstance.connective false pa (.all 1 innerForallInstBody)
      (CInstance.atom pa rfl)
      innerForallInst
  -- forall x(P(x) or forall y Q(y, f(x))) instantiated with a (k=1: t₀=a)
  let outerForallInst :=
    CInstance.forallInst 0 outerForallBody
      (.const CInstExConst.a) leftDisj
      [] []
      (by simp [LCS.FirstOrder.Basic.Term.isClosed,
                LCS.FirstOrder.Basic.termFV])
      (by intro _ h; simp at h)
  -- not P(a) and (not Q(a,f(a)) or not Q(b,f(a)))
  let rightConj :=
    CInstance.connective true notPa innerDisj
      (CInstance.negAtom pa rfl)
      (CInstance.connective false notQafa notQbfa
        (CInstance.negAtom qafa rfl)
        (CInstance.negAtom qbfa rfl))
  -- Outer conjunction
  CInstance.connective true outerForall innerConj outerForallInst rightConj



-- ATTACH-BLOCKER: scoped helper requires manual relocation
set_option backward.isDefEq.respectTransparency false in
/-- Example 7.6.4: the witness produces exactly the displayed c-instance,
with the ordered pair Q(a,f(a)), Q(b,f(a)) as its inner conjunction. -/
theorem cInstExDerivation_toFormula :
    cInstExDerivation.toFormula = cInstExCInstance := by
  simp! [cInstExDerivation, CInstance.toFormula, cInstExCInstance]

-- ATTACH-BLOCKER: scoped helper requires manual relocation
set_option backward.isDefEq.respectTransparency false in
/-- Example 7.6.4: every stored connective operand matches its child source,
and every universal child has the complete prescribed substitution source. -/
theorem cInstExDerivation_wellFormed : CInstance.WellFormed cInstExDerivation := by
  simp! [cInstExDerivation, CInstance.WellFormed, CInstance.WellFormedList,
    CInstance.source, formulaSubstN, termSubst, cInstExLang,
    cInstExVec1, cInstExVec2, funext_iff, Fin.forall_fin_succ]

/-- Example 7.6.4: the displayed formula is a c-instance of B, witnessed
by the explicit source-matching derivation. -/
@[blueprint "chap7__example_7_6_4" (main := true)]
theorem cInstExCInstance_isCInstanceOf :
    isCInstanceOf cInstExCInstance cInstExSkolemForm 

-- ===================================================================
-- Definition 7.6.1 (companion def): universalScope
-- ===================================================================

/-- Definition 7.6.1: Label-based membership in US(A) for a rectified
NNF root. This asserts that some occurrence of B has the given scope;
uniqueness belongs to a fixed occurrence, queried by `universalScopeAt`. -/
@[blueprint "chap7__definition_7_6_1"]
def universalScope {L : Language}
    (A B : FormulaN L) (scope : List Nat)
    (_hNNF : A.isNNF)
    (_hRect : LCS.FirstOrder.Semantics.Subformulae.isRectified A) :
    Prop :=
  (B, scope) ∈ universalScopeAux A []

/-- Follow an address in the US closure, carrying the ordered scope.
`false` selects the left child of a connective or the body of a quantifier;
`true` selects the right child of a connective. An empty address selects
the current node. Invalid steps return `none`; literals have no children. -/
@[blueprint "chap7__definition_7_6_1"]
def universalScopeAtAux {L : Language} :
    FormulaN L → List Bool → List Nat → Option (FormulaN L × List Nat)
  | A, [], scope => some (A, scope)
  | .conj C _, false :: path, scope
  | .disj C _, false :: path, scope => universalScopeAtAux C path scope
  | .conj _ D, true :: path, scope
  | .disj _ D, true :: path, scope => universalScopeAtAux D path scope
  | .ex _ C, false :: path, scope => universalScopeAtAux C path scope
  | .all x C, false :: path, scope => universalScopeAtAux C path (scope ++ [x])
  | _, _ :: _, _ => none

/-- Definition 7.6.1: Query the formula and unique ordered universal scope
at an occurrence of a rectified NNF formula (SQ047). Addresses are paths
from the root: `false` means left/body and `true` means right. The scope
contains exactly the universal binders above the selected node, in outer
to inner order. Equal labels at distinct addresses are queried separately.
Negated atoms are leaves, as in the defining US closure. -/
@[blueprint "chap7__definition_7_6_1" (main := true)]
def universalScopeAt {L : Language}
    (A : FormulaN L) (path : List Bool)
    (_hNNF : A.isNNF)
    (_hRect : LCS.FirstOrder.Semantics.Subformulae.isRectified A) :
    Option (FormulaN L × List Nat) :=
  universalScopeAtAux A path []

-- Example 7.6.2: the three existential occurrences retain their scopes.
-- ATTACH-BLOCKER: unsupported untagged example
example (hNNF : usExFormula.isNNF)
    (hRect : LCS.FirstOrder.Semantics.Subformulae.isRectified usExFormula) :
    universalScopeAt usExFormula [false, false, true] hNNF hRect =
      some (usExExistsYSubformula, [0]) ∧
    universalScopeAt usExFormula
      [false, false, true, false, true, false, true] hNNF hRect =
      some (usExExistsUSubformula, [0, 2]) ∧
    universalScopeAt usExFormula [true] hNNF hRect =
      some (usExExistsWSubformula, []) := ⟨rfl, rfl, rfl⟩

-- Equal labels at distinct nodes can have different scopes.
-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} (B : FormulaN L)
    (hNNF : (FormulaN.conj (.all 0 B) B).isNNF)
    (hRect : LCS.FirstOrder.Semantics.Subformulae.isRectified
      (FormulaN.conj (.all 0 B) B)) :
    universalScopeAt (.conj (.all 0 B) B) [false, false] hNNF hRect =
      some (B, [0]) ∧
    universalScopeAt (.conj (.all 0 B) B) [true] hNNF hRect =
      some (B, []) := by
  simp [universalScopeAt, universalScopeAtAux]

-- ===================================================================
-- Example 7.6.2 (theorem): usExScopeOfExistsY
-- ===================================================================

/-- Example 7.6.2 (companion theorem): The universal scope of exists y(Q(y) and forall z(P(y, z) or exists u Q(x, u))) in the formula A is the single variable x = 0. That is, the pair (usExExistsYSubformula, [0]) belongs to universalScopeAux usExFormula []. The `hNNF` and `hRect` arguments witness Def 7.6.1's standing assumption on `usExFormula`. -/
@[blueprint "chap7__example_7_6_2" (main := true)]
theorem usExScopeOfExistsY
    (hNNF : usExFormula.isNNF)
    (hRect : LCS.FirstOrder.Semantics.Subformulae.isRectified
      usExFormula) :
    universalScope usExFormula usExExistsYSubformula [0] hNNF hRect 

-- ===================================================================
-- Example 7.6.2 (theorem): usExScopeOfExistsU
-- ===================================================================

/-- Example 7.6.2 (companion theorem): The universal scope of exists u Q(x, u) in the formula A is the variable sequence x, z (i.e., [0, 2]). That is, the pair (usExExistsUSubformula, [0, 2]) belongs to universalScopeAux usExFormula []. The `hNNF` and `hRect` arguments witness Def 7.6.1's standing assumption on `usExFormula`. -/
@[blueprint "chap7__example_7_6_2" (main := true)]
theorem usExScopeOfExistsU
    (hNNF : usExFormula.isNNF)
    (hRect : LCS.FirstOrder.Semantics.Subformulae.isRectified
      usExFormula) :
    universalScope usExFormula usExExistsUSubformula [0, 2] hNNF hRect 

-- ===================================================================
-- Example 7.6.2 (theorem): usExScopeOfExistsW
-- ===================================================================

/-- Example 7.6.2 (companion theorem): The universal scope of exists w Q(a, w) in the formula A is the empty sequence []. That is, the pair (usExExistsWSubformula, []) belongs to universalScopeAux usExFormula []. The `hNNF` and `hRect` arguments witness Def 7.6.1's standing assumption on `usExFormula`. -/
@[blueprint "chap7__example_7_6_2" (main := true)]
theorem usExScopeOfExistsW
    (hNNF : usExFormula.isNNF)
    (hRect : LCS.FirstOrder.Semantics.Subformulae.isRectified
      usExFormula) :
    universalScope usExFormula usExExistsWSubformula [] hNNF hRect 

-- ===================================================================
-- Definition 7.6.3 (theorem): CInstance.isQuantifierFree
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Helper: an atomic formula is quantifier-free. -/
theorem isAtomic_isQuantifierFree {L : Language}
    (B : FormulaN L) (h : B.isAtomic) :
    LCS.FirstOrder.SemanticsN.isQuantifierFree B := by
-- BEGIN PROOF
  cases B <;> simp_all [FormulaN.isAtomic,
    LCS.FirstOrder.SemanticsN.isQuantifierFree]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Quantifier-free formulae remain quantifier-free under the nonempty
right fold used for universal c-instance output. -/
theorem qf_foldr_conj {L : Language}
    (fs : List (FormulaN L)) (init : FormulaN L)
    (hInit : LCS.FirstOrder.SemanticsN.isQuantifierFree init)
    (hFs : ∀ f, f ∈ fs →
      LCS.FirstOrder.SemanticsN.isQuantifierFree f) :
    LCS.FirstOrder.SemanticsN.isQuantifierFree
      (fs.foldr (fun f rest first => .conj first (rest f)) id init) := by
  induction fs generalizing init with
  | nil => exact hInit
  | cons f rest ih =>
    change LCS.FirstOrder.SemanticsN.isQuantifierFree
      (.conj init (rest.foldr (fun g tail first => .conj first (tail g)) id f))
    exact ⟨hInit, ih f (hFs f (by simp))
      (fun g hg => hFs g (by simp; right; exact hg))⟩

end LCS.Herbrand.SHGTheorem
end

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Substitution
namespace CInstance

-- ATTACH-BLOCKER: termination suffix
/-- Definition 7.6.3 (companion theorem): Every compound instance is a quantifier-free formula. This is the c-instance quantifier-free property: since c-instances are built from atomic/negated atomic formulae combined with connectives and finite conjunctions of universal quantifier instantiations, the result never contains quantifiers. -/
theorem isQuantifierFree {L : Language}
    (ci : CInstance L) :
    LCS.FirstOrder.SemanticsN.isQuantifierFree ci.toFormula := by
-- BEGIN PROOF
  match ci with
  | .atom B hAtom =>
    simp only [toFormula]
    exact isAtomic_isQuantifierFree B hAtom
  | .negAtom B hAtom =>
    simp only [toFormula, LCS.FirstOrder.SemanticsN.isQuantifierFree]
    exact isAtomic_isQuantifierFree B hAtom
  | .connective true C D H K =>
    simp only [toFormula, LCS.FirstOrder.SemanticsN.isQuantifierFree]
    exact ⟨isQuantifierFree H, isQuantifierFree K⟩
  | .connective false C D H K =>
    simp only [toFormula, LCS.FirstOrder.SemanticsN.isQuantifierFree]
    exact ⟨isQuantifierFree H, isQuantifierFree K⟩
  | .forallInst x C t₀ h₀ tsRest hsRest hGround₀ hGroundRest =>
    simp only [toFormula]
    apply qf_foldr_conj
    · exact isQuantifierFree h₀
    · intro f hf
      rw [List.mem_map] at hf
      obtain ⟨h, hMem, heq⟩ := hf
      rw [← heq]
      exact isQuantifierFree h
termination_by sizeOf ci
decreasing_by
  all_goals first
    | (simp_wf; omega)
    | (simp_wf
       have := List.sizeOf_lt_of_mem hMem
       omega)

end CInstance
end LCS.Herbrand.SHGTheorem
end

