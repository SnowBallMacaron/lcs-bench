import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.CutElim.CompletenessBridge
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.LKe.Equivalence.AtomicCuts
import LCS.CutElim.LKe.Equivalence.GeqToLKe
import LCS.CutElim.LKe.Equivalence.SemanticBridge.TermEnumeration
import LCS.CutElim.LKe.Equivalence.SemanticBridge.SupportLanguage
import LCS.CutElim.LKe.Equivalence.SemanticBridge.Lifting

section
namespace LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality.Completeness
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.CompletenessBridge
open LCS.FirstOrder.Equality

-- ===================================================================
-- Semantic bridge infrastructure: one-formula encoding and closure
-- ===================================================================
-- retained: used by LCS.CutElim.Interpolation.Equality.Support
def validBridgeBottom {L : Language} (P : FormulaN L) : FormulaN L :=
  FormulaN.neg (FormulaN.impl P P)

-- retained: used by LCS.CutElim.Interpolation.Equality.Support
def validBridgeSuccedentFormula {L : Language} (P : FormulaN L) :
    List (FormulaN L) → FormulaN L
  | [] => validBridgeBottom P
  | B :: Δ => FormulaN.disj B (validBridgeSuccedentFormula P Δ)

-- retained: used by LCS.CutElim.Interpolation.Equality.Support
def validBridgeSequentFormula {L : Language} (P : FormulaN L)
    (Δ : List (FormulaN L)) : List (FormulaN L) → FormulaN L
  | [] => validBridgeSuccedentFormula P Δ
  | A :: Γ => FormulaN.impl A (validBridgeSequentFormula P Δ Γ)

-- retained: used by LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeBottom_eval {L : Language} (P : FormulaN L)
    (M : Structure L) (s : Assignment M) :
    ¬ formulaEvalN M (validBridgeBottom P) s := by
  simp [validBridgeBottom, formulaEvalN, LCS.FirstOrder.Basic.negM,
    LCS.FirstOrder.Basic.implM]

-- retained: used by LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeSuccedentFormula_eval {L : Language}
    (P : FormulaN L) (M : Structure L) (s : Assignment M) :
    ∀ Δ : List (FormulaN L),
      formulaEvalN M (validBridgeSuccedentFormula P Δ) s ↔
        ∃ B, B ∈ Δ ∧ formulaEvalN M B s := by
  intro Δ
  induction Δ with
  | nil =>
      simp [validBridgeSuccedentFormula, validBridgeBottom_eval]
  | cons B Δ ih =>
      simp [validBridgeSuccedentFormula, formulaEvalN,
        LCS.FirstOrder.Basic.orM, ih]

-- retained: used by LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeSequentFormula_eval {L : Language}
    (P : FormulaN L) (M : Structure L) (s : Assignment M)
    (Δ : List (FormulaN L)) :
    ∀ Γ : List (FormulaN L),
      formulaEvalN M (validBridgeSequentFormula P Δ Γ) s ↔
        ((∀ A ∈ Γ, formulaEvalN M A s) →
          ∃ B, B ∈ Δ ∧ formulaEvalN M B s) := by
  intro Γ
  induction Γ with
  | nil =>
      simpa [validBridgeSequentFormula] using
        validBridgeSuccedentFormula_eval P M s Δ
  | cons A Γ ih =>
      simp only [validBridgeSequentFormula, formulaEvalN,
        LCS.FirstOrder.Basic.implM]
      constructor
      · intro h hall
        apply ih.mp (h (hall A (List.Mem.head _)))
        intro C hC
        exact hall C (List.mem_cons_of_mem A hC)
      · intro h hA
        apply ih.mpr
        intro hall
        apply h
        intro C hC
        rcases List.mem_cons.mp hC with rfl | hC
        · exact hA
        · exact hall C hC

-- retained: used by LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeSequentFormula_valid {L : Language}
    (P : FormulaN L) (Γ Δ : List (FormulaN L))
    (hvalid : sequentValid (Sequent.mk Γ Δ)) :
    ∀ (M : Structure L) (s : Assignment M),
      formulaEvalN M (validBridgeSequentFormula P Δ Γ) s := by
  intro M s
  apply (validBridgeSequentFormula_eval P M s Δ Γ).mpr
  exact hvalid M s

-- retained: used by LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeBottom_left {L : Language} (P : FormulaN L) :
    folkCutFreeProvable
      (Sequent.mk [validBridgeBottom P] []) := by
  have hax := folkCutFree_axiom P
  have himpl := folkCutFree_implRight_head P P [] [] hax
  simpa [validBridgeBottom] using
    folkCutFree_negLeft_head (FormulaN.impl P P) [] [] himpl

-- retained: used by LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeSuccedentFormula_left {L : Language}
    (P : FormulaN L) :
    ∀ (Δ Γ : List (FormulaN L)),
      folkCutFreeProvable
        (Sequent.mk (validBridgeSuccedentFormula P Δ :: Γ) Δ) := by
  intro Δ
  induction Δ with
  | nil =>
      intro Γ
      exact folkCutFree_weakenLeftAppend Γ [validBridgeBottom P] []
        (validBridgeBottom_left P)
  | cons B Δ ih =>
      intro Γ
      have h₁ : folkCutFreeProvable
          (Sequent.mk (B :: Γ) (B :: Δ)) :=
        folkCutFree_shared_axiom _ ⟨B, List.Mem.head _, List.Mem.head _⟩
      have h₂base := ih Γ
      have h₂ : folkCutFreeProvable
          (Sequent.mk (validBridgeSuccedentFormula P Δ :: Γ)
            (B :: Δ)) := by
        simpa using folkCutFree_weakenRightPrepend [B]
          (validBridgeSuccedentFormula P Δ :: Γ) Δ h₂base
      exact folkCutFree_orLeft_head B
        (validBridgeSuccedentFormula P Δ) Γ (B :: Δ) h₁ h₂

-- retained: used by LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeSequentFormula_left {L : Language}
    (P : FormulaN L) (Δ : List (FormulaN L)) :
    ∀ Γ : List (FormulaN L),
      folkCutFreeProvable
        (Sequent.mk (validBridgeSequentFormula P Δ Γ :: Γ) Δ) := by
  intro Γ
  induction Γ with
  | nil =>
      exact validBridgeSuccedentFormula_left P Δ []
  | cons A Γ ih =>
      have hA := folkCutFree_axiom A
      simpa [validBridgeSequentFormula] using
        folkCutFree_implLeft_head A
          (validBridgeSequentFormula P Δ Γ)
          [A] [] Γ Δ hA ih

-- retained: used by LCS.CutElim.Interpolation.Equality.Axioms, LCS.CutElim.Interpolation.Equality.Reduction, LCS.CutElim.Interpolation.Equality.Support
def validBridgeAllList {L : Language} (xs : List Nat)
    (A : FormulaN L) : FormulaN L :=
  xs.foldr FormulaN.all A

-- retained: used by LCS.CutElim.Interpolation.Equality.Axioms, LCS.CutElim.Interpolation.Equality.Reduction, LCS.CutElim.Interpolation.Equality.Support
def validBridgeUniversalClose {L : Language}
    (A : FormulaN L) : FormulaN L :=
  validBridgeAllList (List.range (formulaMaxVarN A + 1)) A

-- retained: used by LCS.CutElim.Interpolation.Equality.Axioms, LCS.CutElim.Interpolation.Equality.Reduction, LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeAllList_fv {L : Language}
    (xs : List Nat) (A : FormulaN L) (x : Nat) :
    x ∈ formulaFVN (validBridgeAllList xs A) ↔
      x ∈ formulaFVN A ∧ x ∉ xs := by
  induction xs with
  | nil =>
      simp [validBridgeAllList]
  | cons y ys ih =>
      rw [show validBridgeAllList (y :: ys) A =
        FormulaN.all y (validBridgeAllList ys A) from rfl]
      simp only [formulaFVN]
      unfold Set.diff Set.singleton
      simp only [List.mem_cons, not_or]
      change
        (x ∈ formulaFVN (validBridgeAllList ys A) ∧ ¬ x = y) ↔
          x ∈ formulaFVN A ∧ ¬ x = y ∧ x ∉ ys
      rw [ih]
      constructor
      · rintro ⟨⟨hA, hys⟩, hxy⟩
        exact ⟨hA, hxy, hys⟩
      · rintro ⟨hA, hxy, hys⟩
        exact ⟨⟨hA, hys⟩, hxy⟩

-- retained: used by LCS.CutElim.Interpolation.Equality.Axioms, LCS.CutElim.Interpolation.Equality.Reduction, LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeUniversalClose_fv_empty {L : Language}
    (A : FormulaN L) :
    formulaFVN (validBridgeUniversalClose A) = ∅ := by
  funext x
  apply propext
  change x ∈ formulaFVN (validBridgeUniversalClose A) ↔ False
  rw [validBridgeUniversalClose, validBridgeAllList_fv]
  constructor
  · intro h
    have hxle := formulaFVN_le_maxVarN A x h.1
    exact h.2 (List.mem_range.mpr (Nat.lt_succ_of_le hxle))
  · intro h
    exact h.elim

-- retained: used by LCS.CutElim.Interpolation.Equality.Axioms, LCS.CutElim.Interpolation.Equality.Reduction, LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeAllList_eval_of_valid {L : Language}
    (M : Structure L) (xs : List Nat) (A : FormulaN L)
    (h : ∀ s : Assignment M, formulaEvalN M A s) :
    ∀ s : Assignment M,
      formulaEvalN M (validBridgeAllList xs A) s := by
  induction xs with
  | nil => exact h
  | cons x xs ih =>
      intro s a
      exact ih (assignUpdate s x a)

-- retained: used by LCS.CutElim.Interpolation.Equality.Axioms, LCS.CutElim.Interpolation.Equality.Reduction, LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeLift_allList {L : Language} (F : FormulaN L)
    (xs : List Nat) (A : FormulaN (ValidBridgeSupportLanguage F)) :
    validBridgeLiftFormula F (validBridgeAllList xs A) =
      validBridgeAllList xs (validBridgeLiftFormula F A) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change
        FormulaN.all x
            (validBridgeLiftFormula F (validBridgeAllList xs A)) =
          FormulaN.all x
            (validBridgeAllList xs (validBridgeLiftFormula F A))
      rw [ih]

-- retained: used by LCS.CutElim.Interpolation.Equality.Axioms, LCS.CutElim.Interpolation.Equality.Reduction, LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeVar_freeFor_self {L : Language}
    (A : FormulaN L) (x : Nat) :
    isFreeForN (Term.var x) x A := by
  induction A with
  | predN P ts => trivial
  | eq_ hL t₁ t₂ => trivial
  | neg A ih => exact ih
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      exact ⟨ihA, ihB⟩
  | all y A ih | ex y A ih =>
      by_cases hxy : x = y
      · exact Or.inl hxy
      · exact Or.inr ⟨by
          intro hy
          exact hxy hy.symm, ih⟩

-- retained: used by LCS.CutElim.Interpolation.Equality.Axioms, LCS.CutElim.Interpolation.Equality.Reduction, LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeAllList_left {L : Language}
    (xs : List Nat) (A : FormulaN L) :
    folkCutFreeProvable
      (Sequent.mk [validBridgeAllList xs A] [A]) := by
  induction xs with
  | nil =>
      simpa [validBridgeAllList] using folkCutFree_axiom A
  | cons x xs ih =>
      have hprem : folkCutFreeProvable
          (Sequent.mk
            [formulaSubstN (validBridgeAllList xs A) (Term.var x) x]
            [A]) := by
        simpa [formulaSubstN_var_self] using ih
      simpa [validBridgeAllList] using
        folkCutFree_allLeft_head (Term.var x) x
          (validBridgeAllList xs A) [] [A]
          (validBridgeVar_freeFor_self _ x) hprem

-- retained: used by LCS.CutElim.Interpolation.Craig, LCS.CutElim.Interpolation.Craig.Proofs
theorem validBridgeFormulaNoEq_of_false {L : Language}
    (hL : L.hasEquality = false) :
    ∀ A : FormulaN L, formulaNoEq A := by
  intro A
  induction A with
  | predN P ts => trivial
  | eq_ heq t₁ t₂ =>
      exact (by simp [hL] at heq)
  | neg A ih => exact ih
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      exact ⟨ihA, ihB⟩
  | all x A ih | ex x A ih => exact ih

-- ===================================================================
-- Semantic bridge: sequentValid -> lkeProvable
-- ===================================================================
-- retained: used by LCS.CutElim.Interpolation.Equality.Axioms, LCS.CutElim.Interpolation.Equality.Reduction, LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeProvable_of_valid_withPivot {L : Language}
    (P : FormulaN L) (Γ Δ : List (FormulaN L))
    (hvalid : sequentValid (Sequent.mk Γ Δ)) :
    lkeProvable (Sequent.mk Γ Δ) := by
  let F := validBridgeSequentFormula P Δ Γ
  let K := ValidBridgeSupportLanguage F
  let R : FormulaN K := validBridgeRestrictSelf F
  let xs := List.range (formulaMaxVarN R + 1)
  let C := validBridgeAllList xs R
  let q : Sequent K := Sequent.mk [] [C]
  letI : Countable (Term K) := by
    dsimp [K]
    exact
      validBridgeTermCountable (ValidBridgeSupportLanguage F)
        (validBridgeFormulaFunSymbols F).attach
        (validBridgeFormulaConstSymbols F).attach
        (List.mem_attach (validBridgeFormulaFunSymbols F))
        (List.mem_attach (validBridgeFormulaConstSymbols F))
  have hRvalid :
      ∀ (M : Structure K) (s : Assignment M),
        formulaEvalN M R s := by
    intro M s
    apply (validBridgeRestrictSelf_eval F M s).mpr
    exact validBridgeSequentFormula_valid P Γ Δ hvalid
      (validBridgeExtendStructure F M) s
  have hCvalid :
      ∀ (M : Structure K) (s : Assignment M),
        formulaEvalN M C s := by
    intro M
    exact validBridgeAllList_eval_of_valid M xs R (hRvalid M)
  have hqvalid : sequentValid q := by
    intro M s _
    exact ⟨C, by simp [q], hCvalid M s⟩
  have hCclosed : formulaFVN C = (∅ : Set Nat) := by
    simpa [C, xs, validBridgeUniversalClose] using
      validBridgeUniversalClose_fv_empty R
  have hqCross : crossNoFreeBound q := by
    intro x ⟨A, hA, hx⟩
    have hAC : A = C := by
      simpa [q] using hA
    subst A
    rw [hCclosed] at hx
    exact False.elim hx
  have hqproof : LKeProofTree q := by
    cases hEq : L.hasEquality with
    | false =>
        have hKEq : K.hasEquality = false := by
          simpa [K, ValidBridgeSupportLanguage] using hEq
        let g := Classical.choice
          (completenessG_cross hKEq q hqCross hqvalid)
        let t := Classical.choose (gProofTree_to_folkCutFree g)
        exact .lk t
    | true =>
        have hKEq : K.hasEquality = true := by
          simpa [K, ValidBridgeSupportLanguage] using hEq
        let g := Classical.choice
          (completenessGEq_cross hKEq q hqCross hqvalid)
        classical
        exact geqProof_to_lkeNoEssentialCuts g
  let D := validBridgeAllList xs F
  have hLiftC : validBridgeLiftFormula F C = D := by
    dsimp [C, D]
    rw [validBridgeLift_allList]
    dsimp [R]
    rw [validBridgeLift_restrictSelf]
  have hClosedTree : LKeProofTree (Sequent.mk [] [D]) := by
    simpa [q, validBridgeLiftSequent, hLiftC] using
      validBridgeLiftLKeProof F hqproof
  obtain ⟨tPeel, _⟩ := validBridgeAllList_left xs F
  have hFormulaTree : LKeProofTree (Sequent.mk [] [F]) := by
    simpa using
      LKeProofTree.cut D [] [] [] [F]
        hClosedTree (LKeProofTree.lk tPeel)
  obtain ⟨tDecode, _⟩ := validBridgeSequentFormula_left P Δ Γ
  exact ⟨by
    simpa [F] using
      LKeProofTree.cut F [] [] Γ Δ
        hFormulaTree (LKeProofTree.lk tDecode)⟩

-- retained: used by LCS.CutElim.Interpolation.Equality.Axioms, LCS.CutElim.Interpolation.Equality.Reduction, LCS.CutElim.Interpolation.Equality.Support
theorem lkeProvable_of_valid {L : Language}
    (s : Sequent L) (hvalid : sequentValid s) :
    lkeProvable s := by
-- BEGIN PROOF
  rcases s with ⟨Γ, Δ⟩
  cases Γ with
  | nil =>
      cases Δ with
      | nil =>
          exfalso
          let M : Structure L :=
            { carrier := Unit
              carrierNonempty := ⟨()⟩
              interpFunc := fun _ _ => ()
              interpConst := fun _ => ()
              interpPred := fun _ _ => False }
          let v : Assignment M := fun _ => ()
          obtain ⟨B, hB, _⟩ := hvalid M v (by
            intro A hA
            simp at hA)
          simpa using hB
      | cons B Δ =>
          exact validBridgeProvable_of_valid_withPivot
            B [] (B :: Δ) hvalid
  | cons A Γ =>
      exact validBridgeProvable_of_valid_withPivot
        A (A :: Γ) Δ hvalid

end LCS.CutElim.LKe.Equivalence
end
