import LCS.FirstOrder.Basic
import LCS.FirstOrder.Syntax.RankedAlphabet
import LCS.FirstOrder.Syntax.FreeGeneration
import Attach
import LCS.FirstOrder.Syntax.Algebra.ProofsStamp

/-! # The two-sorted alphabet of a first-order language

The sorts and ranks of the symbols listed in the remark following
Definition 5.2.1, and algebras over a many-sorted ranked alphabet.
-/

namespace LCS.FirstOrder.Syntax.Algebra

open LCS.FirstOrder.Basic
open LCS.FirstOrder.ManySorted.CongruenceClosure

/-- Definition 5.2.1 (companion): The two sorts of a first-order alphabet. -/
@[blueprint "chap5__definition_5_2_1"]
inductive FirstOrderSort where
  | term
  | formula
  deriving DecidableEq

/-- Definition 5.2.1 (companion): The disjoint union V ⊕ CS ⊕ FS ⊕ PS ⊕ {⊥}
of symbols in the two-sorted-alphabet remark. -/
@[blueprint "chap5__definition_5_2_1"]
inductive TwoSortedSymbol (L : Language) where
  | var : Nat → TwoSortedSymbol L
  | const : L.constSymbols → TwoSortedSymbol L
  | func : L.funSymbols → TwoSortedSymbol L
  | pred : L.predSymbols → TwoSortedSymbol L
  | bot : TwoSortedSymbol L

/-- Definition 5.2.1 (companion): Variables and constants have rank (ε, term),
functions of arity n have rank (termⁿ, term), predicates of arity n have rank
(termⁿ, formula), and ⊥ has rank (ε, formula). -/
@[blueprint "chap5__definition_5_2_1"]
def twoSortedRank {L : Language} : TwoSortedSymbol L → List FirstOrderSort × FirstOrderSort
  | .var _ | .const _ => ([], .term)
  | .func f => (List.replicate (L.funArity f) .term, .term)
  | .pred P => (List.replicate (L.predArity P) .term, .formula)
  | .bot => ([], .formula)

/-- Definition 5.2.1 (companion): An algebra over a many-sorted ranked
alphabet has a nonempty carrier for each sort and an operation for each symbol.
An operation accepts exactly the argument sorts in its symbol's rank and
returns a value of the result sort; empty argument lists give constants. -/
@[blueprint "chap5__definition_5_3_1"]
structure MSAlgebra (A : MSRankedAlphabet) : Type 1 where
  carrier : A.SortType → Type
  carrierNonempty : ∀ s, Nonempty (carrier s)
  operation : (f : A.symbols) →
    ((i : Fin (A.argSorts f).length) → carrier ((A.argSorts f).get i)) →
    carrier (A.resultSort f)

end LCS.FirstOrder.Syntax.Algebra

namespace LCS.FirstOrder.Basic.Language

open LCS.FirstOrder.Syntax.Algebra
open LCS.FirstOrder.ManySorted.CongruenceClosure

/-- Definition 5.2.1 (companion): A language supplies a ranked alphabet with
sorts term and formula and symbols V ⊕ CS ⊕ FS ⊕ PS ⊕ {⊥}. -/
@[blueprint "chap5__definition_5_2_1"]
def twoSortedAlphabet (L : Language) : MSRankedAlphabet where
  SortType := FirstOrderSort
  symbols := TwoSortedSymbol L
  rank := twoSortedRank











end LCS.FirstOrder.Basic.Language

namespace LCS.FirstOrder.Syntax.Algebra

open LCS.FirstOrder.Basic
open LCS.FirstOrder.ManySorted.CongruenceClosure
open LCS.FirstOrder.Syntax.FreeGeneration

/-- Theorem 5.2.2 (companion): A homomorphism preserves every ranked operation. -/
@[blueprint "chap5__theorem_5_2_2"]
structure MSHom {S : MSRankedAlphabet} (A B : MSAlgebra S) where
  map : (s : S.SortType) → A.carrier s → B.carrier s
  preserves : ∀ f args, map (S.resultSort f) (A.operation f args) =
    B.operation f (fun i => map ((S.argSorts f).get i) (args i))

/-- Theorem 5.2.2 (companion): An algebra isomorphism is an operation-preserving
map with a two-sided inverse in each sort. -/
@[blueprint "chap5__theorem_5_2_2"]
structure MSIso {S : MSRankedAlphabet} (A B : MSAlgebra S) extends MSHom A B where
  inv : (s : S.SortType) → B.carrier s → A.carrier s
  leftInv : ∀ s x, inv s (map s x) = x
  rightInv : ∀ s y, map s (inv s y) = y

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 5.2.2 (companion): Convert homogeneous tuples to ranked arguments. -/
def rankedArgs {C : FirstOrderSort → Type} {s : FirstOrderSort} {n : Nat}
    (v : Fin n → C s) : (i : Fin (List.replicate n s).length) →
      C ((List.replicate n s).get i) := fun i => by
  simpa using v ⟨i.val, by simpa using i.isLt⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 5.2.2 (companion): Read a homogeneous tuple from ranked arguments. -/
def unrankedArgs {C : FirstOrderSort → Type} {s : FirstOrderSort} {n : Nat}
    (v : (i : Fin (List.replicate n s).length) → C ((List.replicate n s).get i)) :
    Fin n → C s := fun i => by
  simpa using v ⟨i.val, by simp⟩

-- ATTACH-BLOCKER: private declaration
private theorem unranked_ranked {C : FirstOrderSort → Type} {s : FirstOrderSort} {n : Nat}
    (v : Fin n → C s) : unrankedArgs (rankedArgs v) = v := by
  funext i
  simp [unrankedArgs, rankedArgs]

/-- Theorem 5.2.2 (companion): The signature of the term/formula algebra.
Variables are generators, while A_i and E_i are unary operation symbols. -/
@[blueprint "chap5__theorem_5_2_2"]
inductive SyntaxOperation (L : Language) where
  | const : L.constSymbols → SyntaxOperation L
  | func : L.funSymbols → SyntaxOperation L
  | pred : L.predSymbols → SyntaxOperation L
  | eq : L.hasEquality = true → SyntaxOperation L
  | bot | conj | disj | impl | equiv | neg
  | all : Nat → SyntaxOperation L
  | ex : Nat → SyntaxOperation L

/-- Theorem 5.2.2 (companion): Arity of a term/formula operation. -/
@[blueprint "chap5__theorem_5_2_2"]
abbrev SyntaxOperation.arity {L : Language} : SyntaxOperation L → Nat
  | .const _ | .bot => 0
  | .func f => L.funArity f
  | .pred P => L.predArity P
  | .eq _ | .conj | .disj | .impl | .equiv => 2
  | .neg | .all _ | .ex _ => 1

/-- Theorem 5.2.2 (companion): Input sort of a term/formula operation. -/
@[blueprint "chap5__theorem_5_2_2"]
abbrev SyntaxOperation.inputSort {L : Language} : SyntaxOperation L → FirstOrderSort
  | .const _ | .func _ | .pred _ | .eq _ => .term
  | _ => .formula

/-- Theorem 5.2.2 (companion): Result sort of a term/formula operation. -/
@[blueprint "chap5__theorem_5_2_2"]
abbrev SyntaxOperation.outputSort {L : Language} : SyntaxOperation L → FirstOrderSort
  | .const _ | .func _ => .term
  | _ => .formula

/-- Theorem 5.2.2 (companion): The ranked signature of T(L,V). -/
@[blueprint "chap5__theorem_5_2_2"]
abbrev syntaxAlphabet (L : Language) : MSRankedAlphabet where
  SortType := FirstOrderSort
  symbols := SyntaxOperation L
  rank op := (List.replicate op.arity op.inputSort, op.outputSort)

/-- Theorem 5.2.2 (companion): Apply a syntax operation to a homogeneous tuple. -/
@[blueprint "chap5__theorem_5_2_2"]
def syntaxApply {L : Language} (A : MSAlgebra (syntaxAlphabet L))
    (op : SyntaxOperation L) (v : Fin op.arity → A.carrier op.inputSort) :
    A.carrier op.outputSort := A.operation op (rankedArgs v)

/-- Theorem 5.2.2 (companion): The term and formula tree carriers. -/
@[blueprint "chap5__theorem_5_2_2"]
abbrev treeCarrier (L : Language) : FirstOrderSort → Type
  | .term => Term L
  | .formula => Formula L

/-- Theorem 5.2.2 (companion): Tree operations use the syntax constructors;
in particular A_i(A) is ∀x_i A and E_i(A) is ∃x_i A. -/
@[blueprint "chap5__theorem_5_2_2"]
def treeOperation {L : Language} (op : SyntaxOperation L) :
    (Fin op.arity → treeCarrier L op.inputSort) → treeCarrier L op.outputSort :=
  match op with
  | .const c => fun _ => .const c
  | .func f => fun v => .func f v
  | .pred P => fun v => if h : L.predArity P = 0 then .pred0 P h
      else .predN P (Nat.pos_of_ne_zero h) v
  | .eq h => fun v => .eq_ h (v 0) (v 1)
  | .bot => fun _ => .falsum
  | .conj => fun v => .conj (v 0) (v 1)
  | .disj => fun v => .disj (v 0) (v 1)
  | .impl => fun v => .impl (v 0) (v 1)
  | .equiv => fun v => .equiv_ (v 0) (v 1)
  | .neg => fun v => .neg (v 0)
  | .all i => fun v => .all i (v 0)
  | .ex i => fun v => .ex i (v 0)

/-- Theorem 5.2.2 (companion): The tree algebra T_L(V). -/
@[blueprint "chap5__theorem_5_2_2"]
abbrev treeAlgebra (L : Language) : MSAlgebra (syntaxAlphabet L) where
  carrier := treeCarrier L
  carrierNonempty := fun s => by cases s; exact ⟨Term.var 0⟩; exact ⟨Formula.falsum⟩
  operation op args := treeOperation op (unrankedArgs args)

/-- Theorem 5.2.2 (companion): The actual string carriers TERM_L and FORM_L. -/
@[blueprint "chap5__theorem_5_2_2"]
abbrev stringCarrier (L : Language) : FirstOrderSort → Type
  | .term => {s : List (TermSymbol L) // ∃ t : Term L, Term.toSymbolList t = s}
  | .formula => {s : List (FormulaSymbol L) // ∃ A : Formula L, Formula.toSymbolList A = s}

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 5.2.2 (companion): Print a syntax tree as a well-formed string. -/
def printTree {L : Language} : (s : FirstOrderSort) → treeCarrier L s → stringCarrier L s
  | .term, t => ⟨Term.toSymbolList t, t, rfl⟩
  | .formula, A => ⟨Formula.toSymbolList A, A, rfl⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 5.2.2 (companion): Parse a well-formed term or formula string. -/
noncomputable def parseString {L : Language} : (s : FirstOrderSort) → stringCarrier L s → treeCarrier L s
  | .term, t => Classical.choose t.property
  | .formula, A => Classical.choose A.property

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 5.2.2 (companion): Parsing a printed tree recovers it. -/
theorem parse_print {L : Language} (s : FirstOrderSort) (x : treeCarrier L s) :
    parseString s (printTree s x) = x := by
  cases s with
  | term => exact term_toSymbolList_injective _ _ (Classical.choose_spec (printTree .term x).property)
  | formula =>
      exact formula_constructor_range_distinguishable _ _
        (Classical.choose_spec (printTree .formula x).property)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 5.2.2 (companion): Printing the parse recovers the original string. -/
theorem print_parse {L : Language} (s : FirstOrderSort) (x : stringCarrier L s) :
    printTree s (parseString s x) = x := by
  cases s <;> apply Subtype.ext <;> exact Classical.choose_spec x.property

/-- Theorem 5.2.2 (companion): The string algebra T(L,V), with constructor
operations on the uniquely parsed strings, followed by their printing maps. -/
@[blueprint "chap5__theorem_5_2_2"]
noncomputable abbrev stringAlgebra (L : Language) : MSAlgebra (syntaxAlphabet L) where
  carrier := stringCarrier L
  carrierNonempty := fun s => by
    cases s
    · exact ⟨printTree .term (Term.var 0)⟩
    · exact ⟨printTree .formula Formula.falsum⟩
  operation op args := printTree _ ((treeAlgebra L).operation op
    (fun i => parseString _ (args i)))

/-- Theorem 5.2.2 (companion): Printing is an isomorphism from the tree
algebra T_L(V) to the string algebra T(L,V). -/
@[blueprint "chap5__theorem_5_2_2"]
noncomputable def treeStringIso (L : Language) : MSIso (treeAlgebra L) (stringAlgebra L) where
  map := printTree
  inv := parseString
  leftInv := parse_print
  rightInv := print_parse
  preserves := by
    intro op args
    change printTree _ ((treeAlgebra L).operation op args) =
      printTree _ ((treeAlgebra L).operation op (fun i => parseString _ (printTree _ (args i))))
    apply congrArg (printTree _)
    apply congrArg ((treeAlgebra L).operation op)
    funext i
    exact (parse_print _ (args i)).symm

/-- Theorem 5.2.2 (companion): Variables are generators of the term sort
in the string algebra. -/
@[blueprint "chap5__theorem_5_2_2"]
def stringVariable {L : Language} (x : Nat) : stringCarrier L .term :=
  printTree .term (.var x)

/-- Theorem 5.2.2 (companion): Freeness on V means that every assignment
of the term-sort variables extends to exactly one algebra homomorphism. -/
@[blueprint "chap5__theorem_5_2_2"]
def freeOnVariables {L : Language} (A : MSAlgebra (syntaxAlphabet L))
    (v : Nat → A.carrier .term) : Prop :=
  ∀ B : MSAlgebra (syntaxAlphabet L), ∀ ρ : Nat → B.carrier .term,
    ∃ h : MSHom A B, (∀ i, h.map .term (v i) = ρ i) ∧
      ∀ g : MSHom A B, (∀ i, g.map .term (v i) = ρ i) → g = h

-- ATTACH-BLOCKER: private declaration
private theorem cast_map {C D : FirstOrderSort → Type} (f : ∀ s, C s → D s)
    {s t : FirstOrderSort} (h : s = t) (x : C s) :
    cast (congrArg D h) (f s x) = f t (cast (congrArg C h) x) := by
  cases h
  rfl

-- ATTACH-BLOCKER: private declaration
private theorem ranked_map {C D : FirstOrderSort → Type} (f : ∀ s, C s → D s)
    {s : FirstOrderSort} {n : Nat} (v : Fin n → C s) :
    rankedArgs (fun i => f s (v i)) = (fun i => f _ (rankedArgs v i)) := by
  funext i
  simp only [rankedArgs]
  exact cast_map f (List.getElem_replicate i.isLt).symm _

-- ATTACH-BLOCKER: private declaration
def foldTerm {L : Language} (A : MSAlgebra (syntaxAlphabet L))
    (ρ : Nat → A.carrier .term) : Term L → A.carrier .term
  | .var i => ρ i
  | .const c => syntaxApply A (.const c) (fun i => i.elim0)
  | .func f ts => syntaxApply A (.func f) (fun i => foldTerm A ρ (ts i))

-- ATTACH-BLOCKER: private declaration
private def foldFormula {L : Language} (A : MSAlgebra (syntaxAlphabet L))
    (ρ : Nat → A.carrier .term) : Formula L → A.carrier .formula
  | .falsum => syntaxApply A .bot (fun i => i.elim0)
  | .pred0 P h => syntaxApply A (.pred P) (fun i => Fin.elim0 (h ▸ i))
  | .predN P _ ts => syntaxApply A (.pred P) (fun i => foldTerm A ρ (ts i))
  | .eq_ h t u => syntaxApply A (.eq h) (vec2 (foldTerm A ρ t) (foldTerm A ρ u))
  | .conj B C => syntaxApply A .conj (vec2 (foldFormula A ρ B) (foldFormula A ρ C))
  | .disj B C => syntaxApply A .disj (vec2 (foldFormula A ρ B) (foldFormula A ρ C))
  | .impl B C => syntaxApply A .impl (vec2 (foldFormula A ρ B) (foldFormula A ρ C))
  | .equiv_ B C => syntaxApply A .equiv (vec2 (foldFormula A ρ B) (foldFormula A ρ C))
  | .neg B => syntaxApply A .neg (fun _ => foldFormula A ρ B)
  | .all i B => syntaxApply A (.all i) (fun _ => foldFormula A ρ B)
  | .ex i B => syntaxApply A (.ex i) (fun _ => foldFormula A ρ B)

-- ATTACH-BLOCKER: private declaration
private def foldTree {L : Language} (A : MSAlgebra (syntaxAlphabet L))
    (ρ : Nat → A.carrier .term) : (s : FirstOrderSort) → treeCarrier L s → A.carrier s
  | .term => foldTerm A ρ
  | .formula => foldFormula A ρ

-- ATTACH-BLOCKER: private declaration
private theorem fold_operation {L : Language} (A : MSAlgebra (syntaxAlphabet L))
    (ρ : Nat → A.carrier .term) (op : SyntaxOperation L)
    (v : Fin op.arity → treeCarrier L op.inputSort) :
    foldTree A ρ _ (treeOperation op v) =
      syntaxApply A op (fun i => foldTree A ρ _ (v i)) := by
  cases op with
  | pred P =>
    by_cases h : L.predArity P = 0
    · simp only [treeOperation, dite_eq_left h, foldTree, foldFormula]
      apply congrArg (syntaxApply A (.pred P))
      funext i
      exact Fin.elim0 (h ▸ i)
    · simp [treeOperation, h, foldTree, foldFormula]
  | const c =>
    apply congrArg (syntaxApply A (.const c))
    funext i
    exact i.elim0
  | bot =>
    apply congrArg (syntaxApply A .bot)
    funext i
    exact i.elim0
  | func f => rfl
  | eq h | conj | disj | impl | equiv =>
    simp only [treeOperation, foldTree, foldFormula]
    congr 1
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | n + 2 => omega
  | neg | all _ | ex _ =>
    simp only [treeOperation, foldTree, foldFormula]
    congr 1
    funext i
    have : i = 0 := by apply Fin.ext; simp only [SyntaxOperation.arity] at *; omega
    subst i
    rfl

-- ATTACH-BLOCKER: private declaration
private theorem ranked_unranked {C : FirstOrderSort → Type} {s : FirstOrderSort} {n : Nat}
    (v : (i : Fin (List.replicate n s).length) → C ((List.replicate n s).get i)) :
    rankedArgs (unrankedArgs v) = v := by
  funext i
  simp [unrankedArgs, rankedArgs]

-- ATTACH-BLOCKER: private declaration
def foldHom {L : Language} (A : MSAlgebra (syntaxAlphabet L))
    (ρ : Nat → A.carrier .term) : MSHom (treeAlgebra L) A where
  map := foldTree A ρ
  preserves := by
    intro op args
    change foldTree A ρ _ (treeOperation op (unrankedArgs args)) = _
    rw [fold_operation]
    unfold syntaxApply
    rw [ranked_map]
    apply congrArg (A.operation op)
    funext i
    apply congrArg (foldTree A ρ _)
    exact congrFun (ranked_unranked (C := treeCarrier L) args) i


-- ATTACH-BLOCKER: private declaration
private theorem hom_uniform {L : Language} {A : MSAlgebra (syntaxAlphabet L)}
    (h : MSHom (treeAlgebra L) A) (op : SyntaxOperation L)
    (v : Fin op.arity → treeCarrier L op.inputSort) :
    h.map _ (treeOperation op v) = syntaxApply A op (fun i => h.map _ (v i)) := by
  have hh := h.preserves op (rankedArgs v)
  change h.map _ (treeOperation op (unrankedArgs (rankedArgs v))) = _ at hh
  rw [unranked_ranked] at hh
  exact hh.trans (congrArg (A.operation op)
    (ranked_map (C := treeCarrier L) (D := A.carrier) h.map v).symm)

-- ATTACH-BLOCKER: private declaration
theorem hom_ext {S : MSRankedAlphabet} {A B : MSAlgebra S}
    {h g : MSHom A B} (he : h.map = g.map) : h = g := by
  cases h; cases g; cases he; rfl

-- ATTACH-BLOCKER: private declaration
private theorem vec2_map {X Y : Type} (f : X → Y) (x y : X) :
    (fun i => f (vec2 x y i)) = vec2 (f x) (f y) := by
  funext i
  rcases i with ⟨i, hi⟩
  match i with
  | 0 => rfl
  | 1 => rfl
  | n + 2 => omega

-- ATTACH-BLOCKER: private declaration
theorem fold_unique {L : Language} (A : MSAlgebra (syntaxAlphabet L))
    (ρ : Nat → A.carrier .term) (h : MSHom (treeAlgebra L) A)
    (hv : ∀ i, h.map .term (Term.var i) = ρ i) : h = foldHom A ρ := by
  have ht (t : Term L) : h.map .term t = foldTerm A ρ t := by
    induction t with
    | var i => exact hv i
    | const c =>
      have hh := hom_uniform h (.const c) (fun i => i.elim0)
      change h.map .term (Term.const c) = syntaxApply A (.const c) _ at hh
      rw [hh]
      apply congrArg (syntaxApply A (.const c))
      funext i; exact i.elim0
    | func f ts ih =>
      have hh := hom_uniform h (.func f) ts
      simpa [treeOperation, foldTerm, ih] using hh
  apply hom_ext
  funext s x
  cases s with
  | term => exact ht x
  | formula =>
    change h.map .formula x = foldFormula A ρ x
    induction x with
    | falsum =>
      have hh := hom_uniform h .bot (fun i => i.elim0)
      change h.map .formula Formula.falsum = syntaxApply A .bot _ at hh
      rw [hh]
      apply congrArg (syntaxApply A .bot)
      funext i; exact i.elim0
    | pred0 P hz =>
      have hh := hom_uniform h (.pred P) (fun i => Fin.elim0 (hz ▸ i))
      simp only [treeOperation, dite_eq_left hz] at hh
      rw [hh]
      apply congrArg (syntaxApply A (.pred P))
      funext i; exact Fin.elim0 (hz ▸ i)
    | predN P hp ts =>
      have hz : L.predArity P ≠ 0 := Nat.ne_of_gt hp
      have hh := hom_uniform h (.pred P) ts
      simpa [treeOperation, hz, foldFormula, ht] using hh
    | eq_ he t u =>
      have hh := hom_uniform h (.eq he) (vec2 t u)
      change h.map .formula (.eq_ he t u) =
        syntaxApply A (.eq he) (fun i => h.map .term (vec2 t u i)) at hh
      rw [vec2_map, ht t, ht u] at hh
      exact hh
    | conj B C ihB ihC =>
      have hh := hom_uniform h .conj (vec2 B C)
      change h.map .formula (.conj B C) =
        syntaxApply A .conj (fun i => h.map .formula (vec2 B C i)) at hh
      rw [vec2_map, ihB, ihC] at hh
      exact hh
    | disj B C ihB ihC =>
      have hh := hom_uniform h .disj (vec2 B C)
      change h.map .formula (.disj B C) =
        syntaxApply A .disj (fun i => h.map .formula (vec2 B C i)) at hh
      rw [vec2_map, ihB, ihC] at hh
      exact hh
    | impl B C ihB ihC =>
      have hh := hom_uniform h .impl (vec2 B C)
      change h.map .formula (.impl B C) =
        syntaxApply A .impl (fun i => h.map .formula (vec2 B C i)) at hh
      rw [vec2_map, ihB, ihC] at hh
      exact hh
    | equiv_ B C ihB ihC =>
      have hh := hom_uniform h .equiv (vec2 B C)
      change h.map .formula (.equiv_ B C) =
        syntaxApply A .equiv (fun i => h.map .formula (vec2 B C i)) at hh
      rw [vec2_map, ihB, ihC] at hh
      exact hh
    | neg B ih =>
      have hh := hom_uniform h .neg (fun _ => B)
      simpa [treeOperation, foldFormula, ih] using hh
    | all i B ih =>
      have hh := hom_uniform h (.all i) (fun _ => B)
      simpa [treeOperation, foldFormula, ih] using hh
    | ex i B ih =>
      have hh := hom_uniform h (.ex i) (fun _ => B)
      simpa [treeOperation, foldFormula, ih] using hh


/-- Theorem 5.2.2 (companion): The string term/formula algebra is free on V. -/
@[blueprint "chap5__theorem_5_2_2"]
theorem stringAlgebra_free (L : Language) :
    freeOnVariables (stringAlgebra L) stringVariable

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Theorem 5.2.2 (companion): Every string operation is the corresponding
syntax constructor printed as a string, including C_f, C_P, equality,
connectives, and the indexed quantifier operations. -/
theorem stringAlgebra_apply_print {L : Language} (op : SyntaxOperation L)
    (v : Fin op.arity → treeCarrier L op.inputSort) :
    syntaxApply (stringAlgebra L) op (fun i => printTree _ (v i)) =
      printTree _ (treeOperation op v) := by
  have h := (treeStringIso L).preserves op (rankedArgs v)
  change printTree _ (treeOperation op (unrankedArgs (rankedArgs v))) =
    (stringAlgebra L).operation op (fun i => printTree _ (rankedArgs v i)) at h
  rw [unranked_ranked] at h
  exact (congrArg ((stringAlgebra L).operation op)
    (ranked_map (C := treeCarrier L) (D := stringCarrier L) printTree v)).trans h.symm





end LCS.FirstOrder.Syntax.Algebra

namespace LCS.FirstOrder.Syntax.Algebra

open LCS.FirstOrder.Basic
open LCS.FirstOrder.ManySorted.CongruenceClosure

/-- Definition 5.3.1 (companion): The nonlogical symbols interpreted by a structure. -/
@[blueprint "chap5__definition_5_3_1"]
inductive NonlogicalSymbol (L : Language) where
  | const : L.constSymbols → NonlogicalSymbol L
  | func : L.funSymbols → NonlogicalSymbol L
  | pred : L.predSymbols → NonlogicalSymbol L

/-- Definition 5.3.1 (companion): The nonlogical ranked signature Σ_L;
predicates return formula-sort values, and functions and constants return terms. -/
@[blueprint "chap5__definition_5_3_1"]
abbrev nonlogicalAlphabet (L : Language) : MSRankedAlphabet where
  SortType := FirstOrderSort
  symbols := NonlogicalSymbol L
  rank
    | .const _ => ([], .term)
    | .func f => (List.replicate (L.funArity f) .term, .term)
    | .pred P => (List.replicate (L.predArity P) .term, .formula)

/-- Definition 5.3.1 (companion): The carriers of a structure's two-sorted
algebra are its domain M and the classical truth-value type Prop. -/
@[blueprint "chap5__definition_5_3_1"]
abbrev structureCarrier {L : Language} (M : Structure L) : FirstOrderSort → Type
  | .term => M.carrier
  | .formula => Prop

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.3.1 (companion): Both carriers of a structure's algebra are nonempty. -/
theorem structureCarrier_nonempty {L : Language} (M : Structure L) (s : FirstOrderSort) :
    Nonempty (structureCarrier M s) := by
  cases s
  · exact M.carrierNonempty
  · exact ⟨False⟩

/-- Definition 5.3.1 (companion): Every L-structure is a Σ_L-algebra,
with its given interpretation of constants, functions, and predicates. -/
@[blueprint "chap5__definition_5_3_1"]
def structureAlgebra {L : Language} (M : Structure L) : MSAlgebra (nonlogicalAlphabet L) where
  carrier := structureCarrier M
  carrierNonempty := structureCarrier_nonempty M
  operation op := match op with
    | .const c => fun _ => M.interpConst c
    | .func f => fun args => M.interpFunc f (unrankedArgs args)
    | .pred P => fun args => M.interpPred P (unrankedArgs args)







-- ATTACH-BLOCKER: private name in relocated declaration
/-- Definition 5.3.1 (companion): Function interpretations are unchanged. -/
theorem structureAlgebra_func {L : Language} (M : Structure L) (f : L.funSymbols)
    (v : Fin (L.funArity f) → M.carrier) :
    (structureAlgebra M).operation (.func f) (rankedArgs v) = M.interpFunc f v := by
  change M.interpFunc f (unrankedArgs (C := structureCarrier M) (s := .term) (rankedArgs v)) = M.interpFunc f v
  rw [unranked_ranked]

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Definition 5.3.1 (companion): Predicate interpretations, including rank zero, are unchanged. -/
theorem structureAlgebra_pred {L : Language} (M : Structure L) (P : L.predSymbols)
    (v : Fin (L.predArity P) → M.carrier) :
    (structureAlgebra M).operation (.pred P) (rankedArgs v) = M.interpPred P v := by
  change M.interpPred P (unrankedArgs (C := structureCarrier M) (s := .term) (rankedArgs v)) = M.interpPred P v
  rw [unranked_ranked]

end LCS.FirstOrder.Syntax.Algebra
