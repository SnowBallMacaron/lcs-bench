import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.Semantics.Subformulae.Part1
import Attach
import LCS.FirstOrder.ManySorted.SemanticLaws.ProofsStamp

/-! # Many-sorted semantic laws

The transfer in §10.3.5 of §§5.3.7–5.3.9: tautological instances,
connective identities, logical equivalence and the Lindenbaum algebra.
Validity ranges over all structures and full assignments. Formula equality
remains literal syntax equality until the explicit logical-equivalence quotient.
-/

namespace LCS.FirstOrder.ManySorted.SemanticLaws

open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.Propositional.Semantics
open LCS.FirstOrder.Semantics.Subformulae (PropFormulaOver evalProp tautology)

/-- A formula is valid when every structure and assignment gives it value T. -/
@[blueprint "chap10__lemma_10_3_2"]
def msValid {L : MSLanguage} (A : MSFormula L) : Prop :=
  ∀ (M : MSStructure L) (v : MSAssignment M), msFormulaEval M A v = BoolVal.T

/-- The propositional letters PS₀ are exactly the nullary predicates of L. -/
@[blueprint "chap10__lemma_10_3_2"]
abbrev MSPropLetters (L : MSLanguage) :=
  {P : L.predSymbols // L.predArity P = []}

/-- Simultaneous formula substitution at propositional leaves. Replacement
formulae are inserted whole, so their binders do not capture other replacements. -/
@[blueprint "chap10__lemma_10_3_2"]
def msPropSubst {L : MSLanguage} {α : Type} (σ : α → MSFormula L) :
    PropFormulaOver α → MSFormula L
  | .fls => .falsum
  | .var p => σ p
  | .neg A => .neg (msPropSubst σ A)
  | .conj A B => .conj (msPropSubst σ A) (msPropSubst σ B)
  | .disj A B => .disj (msPropSubst σ A) (msPropSubst σ B)
  | .impl A B => .impl (msPropSubst σ A) (msPropSubst σ B)
  | .equiv_ A B => .equiv_ (msPropSubst σ A) (msPropSubst σ B)

/-- PROP_L consists of simultaneous instances of tautologies over PS₀. -/
@[blueprint "chap10__lemma_10_3_2"]
def msInPROPL {L : MSLanguage} (A : MSFormula L) : Prop :=
  ∃ (B : PropFormulaOver (MSPropLetters L)) (σ : MSPropLetters L → MSFormula L),
    tautology B ∧ msPropSubst σ B = A

/-- Substitution evaluation agrees with the induced propositional valuation. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msPropSubstEval {L : MSLanguage} {α : Type} (σ : α → MSFormula L)
    (B : PropFormulaOver α) (M : MSStructure L) (v : MSAssignment M) :
    (msFormulaEval M (msPropSubst σ B) v = BoolVal.T) ↔
      evalProp (fun p => msFormulaEval M (σ p) v = BoolVal.T) B

/-- Every member of PROP_L is valid (the transfer of Lemma 5.3.5). -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msTautologicalInstanceValid {L : MSLanguage} (A : MSFormula L) :
    msInPROPL A → msValid A

/-- Identity 1 of Lemma 5.3.6, with arbitrary many-sorted formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msValid_equivExpansion {L : MSLanguage} (A B : MSFormula L) :
    msValid (.equiv_ (.equiv_ A B) (.conj (.impl A B) (.impl B A)))

/-- Identity 2 of Lemma 5.3.6, with arbitrary many-sorted formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msValid_implAsDisj {L : MSLanguage} (A B : MSFormula L) :
    msValid (.equiv_ (.impl A B) (.disj (.neg A) B))

/-- Identity 3 of Lemma 5.3.6, with arbitrary many-sorted formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msValid_disjAsImpl {L : MSLanguage} (A B : MSFormula L) :
    msValid (.equiv_ (.disj A B) (.impl (.neg A) B))

/-- Identity 4 of Lemma 5.3.6, with arbitrary many-sorted formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msValid_disjAsNegConj {L : MSLanguage} (A B : MSFormula L) :
    msValid (.equiv_ (.disj A B) (.neg (.conj (.neg A) (.neg B))))

/-- Identity 5 of Lemma 5.3.6, with arbitrary many-sorted formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msValid_conjAsNegDisj {L : MSLanguage} (A B : MSFormula L) :
    msValid (.equiv_ (.conj A B) (.neg (.disj (.neg A) (.neg B))))

/-- Identity 6 of Lemma 5.3.6, with arbitrary many-sorted formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msValid_negAsImplFalsum {L : MSLanguage} (A : MSFormula L) :
    msValid (.equiv_ (.neg A) (.impl A .falsum))

/-- Identity 7 of Lemma 5.3.6, with arbitrary many-sorted formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msValid_falsumAsContradiction {L : MSLanguage} (A : MSFormula L) :
    msValid (.equiv_ .falsum (.conj A (.neg A)))

/-- Identity 8 of Lemma 5.3.6, with arbitrary many-sorted formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msValid_negAllAsExNeg {L : MSLanguage} (s : L.SortType) (x : Nat) (A : MSFormula L) :
    msValid (.equiv_ (.neg (.all s x A)) (.ex s x (.neg A)))

/-- Identity 9 of Lemma 5.3.6, with arbitrary many-sorted formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msValid_negExAsAllNeg {L : MSLanguage} (s : L.SortType) (x : Nat) (A : MSFormula L) :
    msValid (.equiv_ (.neg (.ex s x A)) (.all s x (.neg A)))

/-- Identity 10 of Lemma 5.3.6, with arbitrary many-sorted formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msValid_allAsNegExNeg {L : MSLanguage} (s : L.SortType) (x : Nat) (A : MSFormula L) :
    msValid (.equiv_ (.all s x A) (.neg (.ex s x (.neg A))))

/-- Identity 11 of Lemma 5.3.6, with arbitrary many-sorted formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msValid_exAsNegAllNeg {L : MSLanguage} (s : L.SortType) (x : Nat) (A : MSFormula L) :
    msValid (.equiv_ (.ex s x A) (.neg (.all s x (.neg A))))

/-- Logical equivalence A ≃ B is validity of the primitive formula A ≡ B. -/
@[blueprint "chap10__lemma_10_3_2"]
def msLogEquiv {L : MSLanguage} (A B : MSFormula L) : Prop :=
  msValid (.equiv_ A B)

/-- Logical equivalence is equality of meanings in every structure and assignment. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_iff_eval {L : MSLanguage} (A B : MSFormula L) :
    msLogEquiv A B ↔ ∀ (M : MSStructure L) (v : MSAssignment M),
      msFormulaEval M A v = msFormulaEval M B v

/-- Logical equivalence is reflexive. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_refl {L : MSLanguage} (A : MSFormula L) :
    msLogEquiv A A

/-- Logical equivalence is symmetric. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_symm {L : MSLanguage} {A B : MSFormula L} (h : msLogEquiv A B) :
    msLogEquiv B A

/-- Logical equivalence is transitive. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_trans {L : MSLanguage} {A B C : MSFormula L} (hAB : msLogEquiv A B) (hBC : msLogEquiv B C) :
    msLogEquiv A C

/-- Logical equivalence respects conj in both independent arguments. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_conj {L : MSLanguage} {A A' B B' : MSFormula L}
    (hA : msLogEquiv A A') (hB : msLogEquiv B B') :
    msLogEquiv (.conj A B) (.conj A' B')

/-- Logical equivalence respects disj in both independent arguments. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_disj {L : MSLanguage} {A A' B B' : MSFormula L}
    (hA : msLogEquiv A A') (hB : msLogEquiv B B') :
    msLogEquiv (.disj A B) (.disj A' B')

/-- Logical equivalence respects impl in both independent arguments. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_impl {L : MSLanguage} {A A' B B' : MSFormula L}
    (hA : msLogEquiv A A') (hB : msLogEquiv B B') :
    msLogEquiv (.impl A B) (.impl A' B')

/-- Logical equivalence respects equiv in both independent arguments. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_equiv {L : MSLanguage} {A A' B B' : MSFormula L}
    (hA : msLogEquiv A A') (hB : msLogEquiv B B') :
    msLogEquiv (.equiv_ A B) (.equiv_ A' B')

/-- Logical equivalence respects negation. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_neg {L : MSLanguage} {A A' : MSFormula L} (hA : msLogEquiv A A') :
    msLogEquiv (.neg A) (.neg A')

/-- Logical equivalence respects the sorted all binder. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_all {L : MSLanguage} (s : L.SortType) (x : Nat)
    {A A' : MSFormula L} (hA : msLogEquiv A A') :
    msLogEquiv (.all s x A) (.all s x A')

/-- Logical equivalence respects the sorted ex binder. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_ex {L : MSLanguage} (s : L.SortType) (x : Nat)
    {A A' : MSFormula L} (hA : msLogEquiv A A') :
    msLogEquiv (.ex s x A) (.ex s x A')

/-- Truth is represented by ¬⊥, retaining the primitive falsum. -/
@[blueprint "chap10__lemma_10_3_2"]
def msTop {L : MSLanguage} : MSFormula L := .neg .falsum

/-- Boolean identity 1 of Lemma 5.3.8 on arbitrary formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_disjAssoc {L : MSLanguage} (A B C : MSFormula L) :
    msLogEquiv (.disj (.disj A B) C) (.disj A (.disj B C))

/-- Boolean identity 2 of Lemma 5.3.8 on arbitrary formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_conjAssoc {L : MSLanguage} (A B C : MSFormula L) :
    msLogEquiv (.conj (.conj A B) C) (.conj A (.conj B C))

/-- Boolean identity 3 of Lemma 5.3.8 on arbitrary formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_disjComm {L : MSLanguage} (A B : MSFormula L) :
    msLogEquiv (.disj A B) (.disj B A)

/-- Boolean identity 4 of Lemma 5.3.8 on arbitrary formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_conjComm {L : MSLanguage} (A B : MSFormula L) :
    msLogEquiv (.conj A B) (.conj B A)

/-- Boolean identity 5 of Lemma 5.3.8 on arbitrary formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_disjConjDistrib {L : MSLanguage} (A B C : MSFormula L) :
    msLogEquiv (.disj A (.conj B C)) (.conj (.disj A B) (.disj A C))

/-- Boolean identity 6 of Lemma 5.3.8 on arbitrary formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_conjDisjDistrib {L : MSLanguage} (A B C : MSFormula L) :
    msLogEquiv (.conj A (.disj B C)) (.disj (.conj A B) (.conj A C))

/-- Boolean identity 7 of Lemma 5.3.8 on arbitrary formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_negDisj {L : MSLanguage} (A B : MSFormula L) :
    msLogEquiv (.neg (.disj A B)) (.conj (.neg A) (.neg B))

/-- Boolean identity 8 of Lemma 5.3.8 on arbitrary formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_negConj {L : MSLanguage} (A B : MSFormula L) :
    msLogEquiv (.neg (.conj A B)) (.disj (.neg A) (.neg B))

/-- Boolean identity 9 of Lemma 5.3.8 on arbitrary formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_disjIdempotent {L : MSLanguage} (A : MSFormula L) :
    msLogEquiv (.disj A A) A

/-- Boolean identity 10 of Lemma 5.3.8 on arbitrary formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_conjIdempotent {L : MSLanguage} (A : MSFormula L) :
    msLogEquiv (.conj A A) A

/-- Boolean identity 11 of Lemma 5.3.8 on arbitrary formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_negNeg {L : MSLanguage} (A : MSFormula L) :
    msLogEquiv (.neg (.neg A)) A

/-- Boolean identity 12 of Lemma 5.3.8 on arbitrary formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_disjAbsorption {L : MSLanguage} (A B : MSFormula L) :
    msLogEquiv (.disj A (.conj A B)) A

/-- Boolean identity 13 of Lemma 5.3.8 on arbitrary formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_conjAbsorption {L : MSLanguage} (A B : MSFormula L) :
    msLogEquiv (.conj A (.disj A B)) A

/-- Boolean identity 14 of Lemma 5.3.8 on arbitrary formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_disjFalsum {L : MSLanguage} (A : MSFormula L) :
    msLogEquiv (.disj A .falsum) A

/-- Boolean identity 15 of Lemma 5.3.8 on arbitrary formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_conjFalsum {L : MSLanguage} (A : MSFormula L) :
    msLogEquiv (.conj A .falsum) .falsum

/-- Boolean identity 16 of Lemma 5.3.8 on arbitrary formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_disjTop {L : MSLanguage} (A : MSFormula L) :
    msLogEquiv (.disj A msTop) msTop

/-- Boolean identity 17 of Lemma 5.3.8 on arbitrary formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_conjTop {L : MSLanguage} (A : MSFormula L) :
    msLogEquiv (.conj A msTop) A

/-- Boolean identity 18 of Lemma 5.3.8 on arbitrary formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_disjNeg {L : MSLanguage} (A : MSFormula L) :
    msLogEquiv (.disj A (.neg A)) msTop

/-- Boolean identity 19 of Lemma 5.3.8 on arbitrary formulae. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLogEquiv_conjNeg {L : MSLanguage} (A : MSFormula L) :
    msLogEquiv (.conj A (.neg A)) .falsum

/-- The setoid of logical equivalence on literal formula syntax. -/
@[blueprint "chap10__lemma_10_3_2"]
def msLogEquivSetoid (L : MSLanguage) : Setoid (MSFormula L) where
  r := msLogEquiv
  iseqv := ⟨msLogEquiv_refl, msLogEquiv_symm, msLogEquiv_trans⟩

/-- The Lindenbaum carrier B_L is FORM_L modulo logical equivalence. -/
@[blueprint "chap10__lemma_10_3_2"]
def MSLindenbaum (L : MSLanguage) : Type := Quotient (msLogEquivSetoid L)

/-- The equivalence class [A] of a formula A. -/
@[blueprint "chap10__lemma_10_3_2"]
def msFormulaClass {L : MSLanguage} (A : MSFormula L) : MSLindenbaum L :=
  Quotient.mk (msLogEquivSetoid L) A

/-- The quotient operation induced by disj is independent of both representatives. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaumAddWellDefined {L : MSLanguage} {A A' B B' : MSFormula L}
    (hA : msLogEquiv A A') (hB : msLogEquiv B B') :
    msFormulaClass (.disj A B) = msFormulaClass (.disj A' B')

/-- The quotient sum [A] + [B] = [A ∨ B]. -/
@[blueprint "chap10__lemma_10_3_2"]
def msLindenbaumAdd {L : MSLanguage} (a b : MSLindenbaum L) : MSLindenbaum L :=
  Quotient.liftOn₂ a b (fun A B => msFormulaClass (.disj A B))
    (fun _ _ _ _ hA hB => msLindenbaumAddWellDefined hA hB)

/-- The quotient operation induced by conj is independent of both representatives. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaumMulWellDefined {L : MSLanguage} {A A' B B' : MSFormula L}
    (hA : msLogEquiv A A') (hB : msLogEquiv B B') :
    msFormulaClass (.conj A B) = msFormulaClass (.conj A' B')

/-- The quotient product [A] * [B] = [A ∧ B]. -/
@[blueprint "chap10__lemma_10_3_2"]
def msLindenbaumMul {L : MSLanguage} (a b : MSLindenbaum L) : MSLindenbaum L :=
  Quotient.liftOn₂ a b (fun A B => msFormulaClass (.conj A B))
    (fun _ _ _ _ hA hB => msLindenbaumMulWellDefined hA hB)

/-- Quotient complement is independent of its representative. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaumNegWellDefined {L : MSLanguage} {A A' : MSFormula L} (hA : msLogEquiv A A') :
    msFormulaClass (.neg A) = msFormulaClass (.neg A')

/-- The quotient complement ¬[A] = [¬A]. -/
@[blueprint "chap10__lemma_10_3_2"]
def msLindenbaumNeg {L : MSLanguage} (a : MSLindenbaum L) : MSLindenbaum L :=
  Quotient.liftOn a (fun A => msFormulaClass (.neg A))
    (fun _ _ hA => msLindenbaumNegWellDefined hA)

/-- The quotient zero is [⊥]. -/
@[blueprint "chap10__lemma_10_3_2"]
def msLindenbaumZero {L : MSLanguage} : MSLindenbaum L := msFormulaClass .falsum

/-- The quotient one is [¬⊥]. -/
@[blueprint "chap10__lemma_10_3_2"]
def msLindenbaumOne {L : MSLanguage} : MSLindenbaum L := msFormulaClass msTop

/-- Classes are equal exactly when the original formulae are logically equivalent. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msFormulaClass_eq_iff {L : MSLanguage} (A B : MSFormula L) :
    msFormulaClass A = msFormulaClass B ↔ msLogEquiv A B

/-- The quotient add is induced by its formula constructor. -/
@[blueprint "chap10__lemma_10_3_2"]
theorem msFormulaClass_add {L : MSLanguage} (A B : MSFormula L) :
    msLindenbaumAdd (msFormulaClass A) (msFormulaClass B) = msFormulaClass (.disj A B)

/-- The quotient mul is induced by its formula constructor. -/
@[blueprint "chap10__lemma_10_3_2"]
theorem msFormulaClass_mul {L : MSLanguage} (A B : MSFormula L) :
    msLindenbaumMul (msFormulaClass A) (msFormulaClass B) = msFormulaClass (.conj A B)

/-- The quotient complement is induced by formula negation. -/
@[blueprint "chap10__lemma_10_3_2"]
theorem msFormulaClass_neg {L : MSLanguage} (A : MSFormula L) :
    msLindenbaumNeg (msFormulaClass A) = msFormulaClass (.neg A)

/-- The Boolean law disjAssoc descends to all Lindenbaum classes. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaum_disjAssoc {L : MSLanguage} (A B C : MSLindenbaum L) :
    (msLindenbaumAdd (msLindenbaumAdd A B) C) = (msLindenbaumAdd A (msLindenbaumAdd B C))

/-- The Boolean law conjAssoc descends to all Lindenbaum classes. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaum_conjAssoc {L : MSLanguage} (A B C : MSLindenbaum L) :
    (msLindenbaumMul (msLindenbaumMul A B) C) = (msLindenbaumMul A (msLindenbaumMul B C))

/-- The Boolean law disjComm descends to all Lindenbaum classes. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaum_disjComm {L : MSLanguage} (A B : MSLindenbaum L) :
    (msLindenbaumAdd A B) = (msLindenbaumAdd B A)

/-- The Boolean law conjComm descends to all Lindenbaum classes. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaum_conjComm {L : MSLanguage} (A B : MSLindenbaum L) :
    (msLindenbaumMul A B) = (msLindenbaumMul B A)

/-- The Boolean law disjConjDistrib descends to all Lindenbaum classes. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaum_disjConjDistrib {L : MSLanguage} (A B C : MSLindenbaum L) :
    (msLindenbaumAdd A (msLindenbaumMul B C)) = (msLindenbaumMul (msLindenbaumAdd A B) (msLindenbaumAdd A C))

/-- The Boolean law conjDisjDistrib descends to all Lindenbaum classes. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaum_conjDisjDistrib {L : MSLanguage} (A B C : MSLindenbaum L) :
    (msLindenbaumMul A (msLindenbaumAdd B C)) = (msLindenbaumAdd (msLindenbaumMul A B) (msLindenbaumMul A C))

/-- The Boolean law negDisj descends to all Lindenbaum classes. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaum_negDisj {L : MSLanguage} (A B : MSLindenbaum L) :
    (msLindenbaumNeg (msLindenbaumAdd A B)) = (msLindenbaumMul (msLindenbaumNeg A) (msLindenbaumNeg B))

/-- The Boolean law negConj descends to all Lindenbaum classes. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaum_negConj {L : MSLanguage} (A B : MSLindenbaum L) :
    (msLindenbaumNeg (msLindenbaumMul A B)) = (msLindenbaumAdd (msLindenbaumNeg A) (msLindenbaumNeg B))

/-- The Boolean law disjIdempotent descends to all Lindenbaum classes. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaum_disjIdempotent {L : MSLanguage} (A : MSLindenbaum L) :
    (msLindenbaumAdd A A) = A

/-- The Boolean law conjIdempotent descends to all Lindenbaum classes. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaum_conjIdempotent {L : MSLanguage} (A : MSLindenbaum L) :
    (msLindenbaumMul A A) = A

/-- The Boolean law negNeg descends to all Lindenbaum classes. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaum_negNeg {L : MSLanguage} (A : MSLindenbaum L) :
    (msLindenbaumNeg (msLindenbaumNeg A)) = A

/-- The Boolean law disjAbsorption descends to all Lindenbaum classes. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaum_disjAbsorption {L : MSLanguage} (A B : MSLindenbaum L) :
    (msLindenbaumAdd A (msLindenbaumMul A B)) = A

/-- The Boolean law conjAbsorption descends to all Lindenbaum classes. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaum_conjAbsorption {L : MSLanguage} (A B : MSLindenbaum L) :
    (msLindenbaumMul A (msLindenbaumAdd A B)) = A

/-- The Boolean law disjFalsum descends to all Lindenbaum classes. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaum_disjFalsum {L : MSLanguage} (A : MSLindenbaum L) :
    (msLindenbaumAdd A msLindenbaumZero) = A

/-- The Boolean law conjFalsum descends to all Lindenbaum classes. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaum_conjFalsum {L : MSLanguage} (A : MSLindenbaum L) :
    (msLindenbaumMul A msLindenbaumZero) = msLindenbaumZero

/-- The Boolean law disjTop descends to all Lindenbaum classes. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaum_disjTop {L : MSLanguage} (A : MSLindenbaum L) :
    (msLindenbaumAdd A msLindenbaumOne) = msLindenbaumOne

/-- The Boolean law conjTop descends to all Lindenbaum classes. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaum_conjTop {L : MSLanguage} (A : MSLindenbaum L) :
    (msLindenbaumMul A msLindenbaumOne) = A

/-- The Boolean law disjNeg descends to all Lindenbaum classes. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaum_disjNeg {L : MSLanguage} (A : MSLindenbaum L) :
    (msLindenbaumAdd A (msLindenbaumNeg A)) = msLindenbaumOne

/-- The Boolean law conjNeg descends to all Lindenbaum classes. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaum_conjNeg {L : MSLanguage} (A : MSLindenbaum L) :
    (msLindenbaumMul A (msLindenbaumNeg A)) = msLindenbaumZero

/-- The nineteen Boolean algebra identities for the induced Lindenbaum operations. -/
@[blueprint "chap10__lemma_10_3_2"]
def msLindenbaumBooleanLaws (L : MSLanguage) : Prop :=
  (∀ A B C : MSLindenbaum L, (msLindenbaumAdd (msLindenbaumAdd A B) C) = (msLindenbaumAdd A (msLindenbaumAdd B C))) ∧
  (∀ A B C : MSLindenbaum L, (msLindenbaumMul (msLindenbaumMul A B) C) = (msLindenbaumMul A (msLindenbaumMul B C))) ∧
  (∀ A B : MSLindenbaum L, (msLindenbaumAdd A B) = (msLindenbaumAdd B A)) ∧
  (∀ A B : MSLindenbaum L, (msLindenbaumMul A B) = (msLindenbaumMul B A)) ∧
  (∀ A B C : MSLindenbaum L, (msLindenbaumAdd A (msLindenbaumMul B C)) = (msLindenbaumMul (msLindenbaumAdd A B) (msLindenbaumAdd A C))) ∧
  (∀ A B C : MSLindenbaum L, (msLindenbaumMul A (msLindenbaumAdd B C)) = (msLindenbaumAdd (msLindenbaumMul A B) (msLindenbaumMul A C))) ∧
  (∀ A B : MSLindenbaum L, (msLindenbaumNeg (msLindenbaumAdd A B)) = (msLindenbaumMul (msLindenbaumNeg A) (msLindenbaumNeg B))) ∧
  (∀ A B : MSLindenbaum L, (msLindenbaumNeg (msLindenbaumMul A B)) = (msLindenbaumAdd (msLindenbaumNeg A) (msLindenbaumNeg B))) ∧
  (∀ A : MSLindenbaum L, (msLindenbaumAdd A A) = A) ∧
  (∀ A : MSLindenbaum L, (msLindenbaumMul A A) = A) ∧
  (∀ A : MSLindenbaum L, (msLindenbaumNeg (msLindenbaumNeg A)) = A) ∧
  (∀ A B : MSLindenbaum L, (msLindenbaumAdd A (msLindenbaumMul A B)) = A) ∧
  (∀ A B : MSLindenbaum L, (msLindenbaumMul A (msLindenbaumAdd A B)) = A) ∧
  (∀ A : MSLindenbaum L, (msLindenbaumAdd A msLindenbaumZero) = A) ∧
  (∀ A : MSLindenbaum L, (msLindenbaumMul A msLindenbaumZero) = msLindenbaumZero) ∧
  (∀ A : MSLindenbaum L, (msLindenbaumAdd A msLindenbaumOne) = msLindenbaumOne) ∧
  (∀ A : MSLindenbaum L, (msLindenbaumMul A msLindenbaumOne) = A) ∧
  (∀ A : MSLindenbaum L, (msLindenbaumAdd A (msLindenbaumNeg A)) = msLindenbaumOne) ∧
  (∀ A : MSLindenbaum L, (msLindenbaumMul A (msLindenbaumNeg A)) = msLindenbaumZero)

/-- The Lindenbaum carrier and its induced operations satisfy all Boolean algebra laws. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msLindenbaumIsBooleanAlgebra (L : MSLanguage) : msLindenbaumBooleanLaws L

/-- The primitive connectives, including falsum and both sorted quantifier kinds. -/
@[blueprint "chap10__lemma_10_3_2"]
inductive MSConnective where
  | bot | neg | conj | disj | impl | equiv | all | ex
  deriving DecidableEq

/-- The connective occurrences of a formula; predicate and equality atoms have none. -/
@[blueprint "chap10__lemma_10_3_2"]
def msFormulaConnectives {L : MSLanguage} : MSFormula L → List MSConnective
  | .falsum => [.bot]
  | .pred _ _ | .eq_ _ _ _ _ => []
  | .neg A => .neg :: msFormulaConnectives A
  | .conj A B => .conj :: (msFormulaConnectives A ++ msFormulaConnectives B)
  | .disj A B => .disj :: (msFormulaConnectives A ++ msFormulaConnectives B)
  | .impl A B => .impl :: (msFormulaConnectives A ++ msFormulaConnectives B)
  | .equiv_ A B => .equiv :: (msFormulaConnectives A ++ msFormulaConnectives B)
  | .all _ _ A => .all :: msFormulaConnectives A
  | .ex _ _ A => .ex :: msFormulaConnectives A

/-- The propositional connective occurrences of a formula over letters. -/
@[blueprint "chap10__lemma_10_3_2"]
def msPropConnectives {α : Type} : PropFormulaOver α → List MSConnective
  | .fls => [.bot]
  | .var _ => []
  | .neg A => .neg :: msPropConnectives A
  | .conj A B => .conj :: (msPropConnectives A ++ msPropConnectives B)
  | .disj A B => .disj :: (msPropConnectives A ++ msPropConnectives B)
  | .impl A B => .impl :: (msPropConnectives A ++ msPropConnectives B)
  | .equiv_ A B => .equiv :: (msPropConnectives A ++ msPropConnectives B)

/-- A propositional basis represents every truth function of positive finite arity. -/
@[blueprint "chap10__lemma_10_3_2"]
def msFunctionallyComplete (K : MSConnective → Prop) : Prop :=
  ∀ n : Nat, 0 < n → ∀ f : (Fin n → Prop) → Prop,
    ∃ B : PropFormulaOver (Fin n),
      (∀ c ∈ msPropConnectives B, K c) ∧ ∀ v, evalProp v B ↔ f v

/-- All propositional connectives belong to K; quantifiers remain permitted. -/
@[blueprint "chap10__lemma_10_3_2"]
def msUsesConnectives {L : MSLanguage} (K : MSConnective → Prop)
    (A : MSFormula L) : Prop :=
  ∀ c ∈ msFormulaConnectives A, K c ∨ c = .all ∨ c = .ex

/-- Every formula has a presentation over any functionally complete basis.
A basis without falsum needs an available atom to express constants, as in §5.3.8. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msConnectivePresentation {L : MSLanguage} {K : MSConnective → Prop}
    (hK : msFunctionallyComplete K)
    (hbase : K .bot ∨ ∃ atom : MSFormula L, msFormulaConnectives atom = [])
    (A : MSFormula L) :
    ∃ B : MSFormula L, msUsesConnectives K B ∧ msLogEquiv A B

/-- Every arbitrary formula has an equivalent presentation omitting ex quantifiers. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msExistsFreePresentation {L : MSLanguage} (A : MSFormula L) :
    ∃ B : MSFormula L, MSConnective.ex ∉ msFormulaConnectives B ∧ msLogEquiv A B

/-- Every arbitrary formula has an equivalent presentation omitting all quantifiers. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msForallFreePresentation {L : MSLanguage} (A : MSFormula L) :
    ∃ B : MSFormula L, MSConnective.all ∉ msFormulaConnectives B ∧ msLogEquiv A B

/-- Given an atom, every formula has an equivalent presentation using
conjunction, disjunction, negation, implication and the two sorted quantifiers. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msSixConnectivePresentation {L : MSLanguage} (atom : MSFormula L)
    (hatom : msFormulaConnectives atom = []) (A : MSFormula L) :
    ∃ B : MSFormula L,
      (∀ c ∈ msFormulaConnectives B,
        c = .conj ∨ c = .disj ∨ c = .neg ∨ c = .impl ∨ c = .all ∨ c = .ex) ∧
      msLogEquiv A B

end LCS.FirstOrder.ManySorted.SemanticLaws
