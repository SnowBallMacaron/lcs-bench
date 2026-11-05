import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.CutElim.CompletenessBridge
import LCS.CutElim.LKe
import LCS.CutElim.Interpolation
import LCS.FirstOrder.Syntax
import LCS.FirstOrder.Semantics
import LCS.CutElim.Beth.Part1
import Attach
import LCS.CutElim.Beth.Part2.ProofsStamp

section
namespace LCS.CutElim.Beth
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Completeness
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.SyntaxN.Variables
open Classical

/-- Example 6.6.1 (companion): Function symbols for the exact language
of the example: unary successor and binary addition. -/
@[blueprint "chap6__example_6_6_1"]
inductive BethExampleFunc : Type where
  | succ : BethExampleFunc
  | plus : BethExampleFunc

/-- Example 6.6.1 (companion): The sole constant symbol 0. -/
@[blueprint "chap6__example_6_6_1"]
inductive BethExampleConst : Type where
  | zero : BethExampleConst

/-- Example 6.6.1 (companion): The sole non-equality predicate symbol <. -/
@[blueprint "chap6__example_6_6_1"]
inductive BethExamplePred : Type where
  | lt : BethExamplePred

/-- Example 6.6.1 (companion): The exact equality language with constant 0,
unary function S, binary function +, and binary predicate <. -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_arithWithOrder : Language :=
  { funSymbols := BethExampleFunc
    funArity := fun
      | .succ => 1
      | .plus => 2
    constSymbols := BethExampleConst
    predSymbols := BethExamplePred
    predArity := fun
      | .lt => 2
    hasEquality := true }

/-- Example 6.6.1 (companion): Build the term S(t). -/
@[blueprint "chap6__example_6_6_1"]
def bethExampleSucc (t : Term bethExample_arithWithOrder) :
    Term bethExample_arithWithOrder :=
  Term.func BethExampleFunc.succ (vec1 t)

/-- Example 6.6.1 (companion): Build the term t₁ + t₂. -/
@[blueprint "chap6__example_6_6_1"]
def bethExamplePlus (t1 t2 : Term bethExample_arithWithOrder) :
    Term bethExample_arithWithOrder :=
  Term.func BethExampleFunc.plus (vec2 t1 t2)

/-- Example 6.6.1 (companion): The constant term 0. -/
@[blueprint "chap6__example_6_6_1"]
def bethExampleZero : Term bethExample_arithWithOrder :=
  Term.const BethExampleConst.zero

-- ===================================================================
-- Example 6.6.1 (companion defs): axiom formulae
-- ===================================================================

/-- Example 6.6.1 (companion): First of the five axioms of Example 6.6.1:
`forall x, ¬(S(x) = 0)`. -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_succNonZeroAxiom : FormulaN bethExample_arithWithOrder :=
  FormulaN.all 0
    (FormulaN.neg
      (FormulaN.eq_ rfl (bethExampleSucc (Term.var 0)) bethExampleZero))

/-- Example 6.6.1 (companion): Second of the five axioms:
`forall x y, S(x) = S(y) → x = y`. -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_succInjectiveAxiom : FormulaN bethExample_arithWithOrder :=
  FormulaN.all 0 (FormulaN.all 1
    (FormulaN.impl
      (FormulaN.eq_ rfl
        (bethExampleSucc (Term.var 0))
        (bethExampleSucc (Term.var 1)))
      (FormulaN.eq_ rfl (Term.var 0) (Term.var 1))))

/-- Example 6.6.1 (companion): Third of the five axioms:
`forall x, x + 0 = x`. -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_addZeroAxiom : FormulaN bethExample_arithWithOrder :=
  FormulaN.all 0
    (FormulaN.eq_ rfl
      (bethExamplePlus (Term.var 0) bethExampleZero)
      (Term.var 0))

/-- Example 6.6.1 (companion): Fourth of the five axioms:
`forall x y, x + S(y) = S(x + y)`. -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_addSuccAxiom : FormulaN bethExample_arithWithOrder :=
  FormulaN.all 0 (FormulaN.all 1
    (FormulaN.eq_ rfl
      (bethExamplePlus (Term.var 0) (bethExampleSucc (Term.var 1)))
      (bethExampleSucc (bethExamplePlus (Term.var 0) (Term.var 1)))))

/-- Example 6.6.1 (companion): Fifth of the five axioms:
`forall x, 0 < S(x)`. -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_zeroLtSuccAxiom : FormulaN bethExample_arithWithOrder :=
  FormulaN.all 0
    (FormulaN.predN BethExamplePred.lt
      (vec2 bethExampleZero (bethExampleSucc (Term.var 0))))

/-- Example 6.6.1 (companion): The conjunction of the five textbook axioms
of Example 6.6.1. -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_fiveAxioms : FormulaN bethExample_arithWithOrder :=
  FormulaN.conj
    (FormulaN.conj
      (FormulaN.conj
        (FormulaN.conj
          bethExample_succNonZeroAxiom
          bethExample_succInjectiveAxiom)
        bethExample_addZeroAxiom)
      bethExample_addSuccAxiom)
    bethExample_zeroLtSuccAxiom

-- ===================================================================
-- Example 6.6.1 (companion defs): structures
-- ===================================================================

/-- Example 6.6.1 (companion): Standard arithmetic structure on ℕ, in
which < is the usual strict order. Used as structure M1 in the
non-implicit-definability witness. -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_standardOrderStructure :
    Structure bethExample_arithWithOrder where
  carrier := Nat
  carrierNonempty := ⟨0⟩
  interpFunc
    | BethExampleFunc.succ, args => Nat.succ (args ⟨0, by decide⟩)
    | BethExampleFunc.plus, args =>
        Nat.add (args ⟨0, by decide⟩) (args ⟨1, by decide⟩)
  interpConst
    | BethExampleConst.zero => 0
  interpPred
    | BethExamplePred.lt, args =>
        (args ⟨0, by decide⟩) < (args ⟨1, by decide⟩)

/-- Example 6.6.1 (companion): Nonstandard arithmetic structure on ℕ,
agreeing with the standard structure on 0, S, +, but interpreting
`x < y` exactly as `x = 0`. Used as structure M2 in the
non-implicit-definability witness. -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_nonstandardOrderStructure :
    Structure bethExample_arithWithOrder where
  carrier := Nat
  carrierNonempty := ⟨0⟩
  interpFunc
    | BethExampleFunc.succ, args => Nat.succ (args ⟨0, by decide⟩)
    | BethExampleFunc.plus, args =>
        Nat.add (args ⟨0, by decide⟩) (args ⟨1, by decide⟩)
  interpConst
    | BethExampleConst.zero => 0
  interpPred
    | BethExamplePred.lt, args =>
        args ⟨0, by decide⟩ = 0





-- ===================================================================
-- Example 6.6.1 (companion theorem): bethExample_nonImplicitDef
-- ===================================================================



-- ===================================================================
-- Example 6.6.1 (companion defs): order characterization
-- ===================================================================

/-- Example 6.6.1 (companion): The order characterization axiom
`forall x y (x < y iff exists z (y = x + S(z)))` added to the five
axioms to give a six-axiom theory in which < is explicitly definable.
Uses FormulaN.equiv (abbreviation for conj (impl A B) (impl B A)). -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_orderCharAxiom : FormulaN bethExample_arithWithOrder :=
  FormulaN.all 0 (FormulaN.all 1
    (FormulaN.equiv
      (FormulaN.predN BethExamplePred.lt
        (vec2 (Term.var 0) (Term.var 1)))
      (FormulaN.ex 2
        (FormulaN.eq_ rfl (Term.var 1)
          (bethExamplePlus (Term.var 0)
            (bethExampleSucc (Term.var 2)))))))

/-- Example 6.6.1 (companion): The textbook's explicit definition
`D = exists z (y = x + S(z))` of < in the six-axiom theory. -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_explicitDefOfOrder : FormulaN bethExample_arithWithOrder :=
  FormulaN.ex 2
    (FormulaN.eq_ rfl (Term.var 1)
      (bethExamplePlus (Term.var 0)
        (bethExampleSucc (Term.var 2))))

/-- Example 6.6.1 (companion): The extended 6-axiom theory (five
original axioms together with the order-characterization axiom). -/
@[blueprint "chap6__example_6_6_1"]
def bethExample_sixAxioms : FormulaN bethExample_arithWithOrder :=
  FormulaN.conj bethExample_fiveAxioms bethExample_orderCharAxiom

-- ===================================================================
-- Example 6.6.1: claim (a) five-axiom theory does NOT implicitly
-- define <
-- ===================================================================

/-- Example 6.6.1: (claim a) Under the five axioms, < is NOT
implicitly definable from {=, 0, S, +}: there are two structures on ℕ
that agree on 0, S, +, both satisfy the five axioms, and disagree on <. -/
@[blueprint "chap6__example_6_6_1" (main := true)]
theorem bethExample_fiveAxioms_notImplicitlyDefinesLt :
    ∃ (M1 M2 : Structure bethExample_arithWithOrder),
      M1.carrier = Nat ∧ M2.carrier = Nat ∧
      HEq M1.interpFunc M2.interpFunc ∧
      HEq M1.interpConst M2.interpConst ∧
      validInN M1 bethExample_fiveAxioms ∧
      validInN M2 bethExample_fiveAxioms ∧
      ¬ (HEq M1.interpPred M2.interpPred) 

-- ===================================================================
-- Example 6.6.1: claim (b) the six-axiom theory explicitly defines <
-- ===================================================================

/-- Example 6.6.1: (claim b) Adding the order-characterization axiom
∀x∀y (x<y ≡ ∃z (y = x + S(z))) to the five axioms yields a theory in
which < is explicitly defined by D = ∃z (y = x + S(z)). -/
@[blueprint "chap6__example_6_6_1" (main := true)]
theorem bethExample_sixAxioms_explicitlyDefinesLt :
    universallyValidN
      (FormulaN.impl bethExample_sixAxioms
        (bethUniversalPrefix 2
          (FormulaN.equiv
            (bethPredApplied BethExamplePred.lt)
            bethExample_explicitDefOfOrder))) 

/- Semantic and finite-support helpers used in the common-predicate
branch of Beth's theorem. -/

-- ATTACH-BLOCKER: private declaration
private theorem bethUniversalPrefix_at_current {L : Language}
    (M : Structure L) (n : Nat) (A : FormulaN L)
    (s : Assignment M)
    (h : formulaEvalN M (bethUniversalPrefix n A) s) :
    formulaEvalN M A s := by
  unfold bethUniversalPrefix at h
  generalize List.range n = xs at h
  induction xs generalizing s with
  | nil =>
      exact h
  | cons x xs ih =>
      have hx := h (s x)
      have hUpdate : assignUpdate s x (s x) = s := by
        funext y
        simp only [assignUpdate]
        split <;> simp_all
      rw [hUpdate] at hx
      exact ih s hx

-- ATTACH-BLOCKER: private declaration
private theorem bethUniversalPrefix_of_validIn {L : Language}
    (M : Structure L) (n : Nat) (A : FormulaN L)
    (hA : ∀ s : Assignment M, formulaEvalN M A s) :
    ∀ s : Assignment M,
      formulaEvalN M (bethUniversalPrefix n A) s := by
  intro s
  unfold bethUniversalPrefix
  generalize List.range n = xs
  induction xs generalizing s with
  | nil =>
      exact hA s
  | cons x xs ih =>
      intro a
      exact ih (assignUpdate s x a)

-- ATTACH-BLOCKER: private declaration
private theorem bethFormulaPredSymbols_interpolation_eq {L : Language}
    (A : FormulaN L) :
    LCS.CutElim.Interpolation.formulaPredSymbolsN A =
      formulaPredSymbolsN A := by
  funext P
  apply propext
  induction A with
  | predN Q ts => rfl
  | eq_ hEq t₁ t₂ => rfl
  | neg A ih => exact ih
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      exact or_congr ihA ihB
  | all x A ih | ex x A ih => exact ih

-- ATTACH-BLOCKER: private declaration
private theorem bethFormulaPredSymbols_rectifyAux {L : Language}
    (A : FormulaN L) (sigma : Nat → Nat) (ctr : Nat) :
    formulaPredSymbolsN (rectifyAux A sigma ctr).1 =
      formulaPredSymbolsN A := by
  induction A generalizing sigma ctr with
  | predN P ts => rfl
  | eq_ hEq t₁ t₂ => rfl
  | neg A ih =>
      simpa [rectifyAux, formulaPredSymbolsN] using ih sigma ctr
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      simp only [rectifyAux, formulaPredSymbolsN]
      rw [ihA, ihB]
  | all x A ih | ex x A ih =>
      simp only [rectifyAux, formulaPredSymbolsN]
      rw [ih]

-- ATTACH-BLOCKER: private declaration
private theorem bethFormulaPredSymbols_rectify {L : Language}
    (A : FormulaN L) :
    formulaPredSymbolsN (rectify A) = formulaPredSymbolsN A := by
  exact bethFormulaPredSymbols_rectifyAux A id (formulaMaxVarN A + 1)

-- ATTACH-BLOCKER: private declaration
private theorem bethFormulaPredSymbols_predSubst_of_ne {L : Language}
    (Q Qcopy P : L.predSymbols)
    (hArity : L.predArity Qcopy = L.predArity Q)
    (hPQ : P ≠ Q) (hPCopy : P ≠ Qcopy)
    (A : FormulaN L) :
    formulaPredSymbolsN (formulaPredSubstN Q Qcopy hArity A) P ↔
      formulaPredSymbolsN A P := by
  induction A with
  | predN R ts =>
      by_cases hRQ : R = Q
      · subst R
        simp [formulaPredSubstN, formulaPredSymbolsN, hPQ, hPCopy]
      · simp [formulaPredSubstN, formulaPredSymbolsN, hRQ]
  | eq_ hEq t₁ t₂ => rfl
  | neg A ih =>
      simpa [formulaPredSubstN, formulaPredSymbolsN] using ih
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      simp only [formulaPredSubstN, formulaPredSymbolsN]
      exact or_congr ihA ihB
  | all x A ih | ex x A ih =>
      simpa [formulaPredSubstN, formulaPredSymbolsN] using ih

-- ATTACH-BLOCKER: private declaration
private theorem bethValidBridgeLiftFormula_bv {L : Language}
    (F : FormulaN L)
    (A : FormulaN (ValidBridgeSupportLanguage F)) :
    formulaBVN (validBridgeLiftFormula F A) = formulaBVN A := by
  induction A with
  | predN P ts => rfl
  | eq_ hEq t₁ t₂ => rfl
  | neg A ih =>
      simpa [validBridgeLiftFormula, formulaBVN] using ih
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      simp only [validBridgeLiftFormula, formulaBVN, ihA, ihB]
  | all x A ih | ex x A ih =>
      simp only [validBridgeLiftFormula, formulaBVN, ih]

-- ATTACH-BLOCKER: private declaration
private theorem bethRestrictFormula_fv_bv {L : Language}
    (F A : FormulaN L)
    (hf : ∀ f, validBridgeFormulaFunOccurs f A →
      validBridgeFormulaFunOccurs f F)
    (hc : ∀ c, validBridgeFormulaConstOccurs c A →
      validBridgeFormulaConstOccurs c F)
    (hp : ∀ P, validBridgeFormulaPredOccurs P A →
      validBridgeFormulaPredOccurs P F) :
    formulaFVN (validBridgeRestrictFormula F A hf hc hp) =
        formulaFVN A ∧
      formulaBVN (validBridgeRestrictFormula F A hf hc hp) =
        formulaBVN A := by
  let A' := validBridgeRestrictFormula F A hf hc hp
  have hLift : validBridgeLiftFormula F A' = A :=
    validBridgeLift_restrictFormula F A hf hc hp
  constructor
  · have hFv := validBridgeLiftFormula_fv F A'
    rw [hLift] at hFv
    exact hFv.symm
  · have hBv := bethValidBridgeLiftFormula_bv F A'
    rw [hLift] at hBv
    exact hBv.symm

-- ATTACH-BLOCKER: private declaration
private def bethFOLKStep2NoCut {L : Language}
    {prem₁ prem₂ conc : Sequent L}
    (rule : FOLKStep2 prem₁ prem₂ conc) : Prop :=
  match rule with
  | .cut .. => False
  | _ => True

-- ATTACH-BLOCKER: private declaration
private theorem bethFOLKTwoPremise_isCutFree {L : Language}
    {prem₁ prem₂ conc : Sequent L}
    (rule : FOLKStep2 prem₁ prem₂ conc)
    (t₁ : FOLKProofTree prem₁) (t₂ : FOLKProofTree prem₂) :
    (FOLKProofTree.twoPremise rule t₁ t₂).isCutFree ↔
      bethFOLKStep2NoCut rule ∧ t₁.isCutFree ∧ t₂.isCutFree := by
  cases rule <;> rfl

-- ATTACH-BLOCKER: private declaration
private def bethReindexFOLKStep2 {L : Language}
    {prem₁ prem₂ conc prem₁' prem₂' conc' : Sequent L}
    (rule : FOLKStep2 prem₁ prem₂ conc)
    (hprem₁ : prem₁ = prem₁') (hprem₂ : prem₂ = prem₂')
    (hconc : conc = conc') :
    FOLKStep2 prem₁' prem₂' conc' := by
  cases hprem₁
  cases hprem₂
  cases hconc
  exact rule

-- ATTACH-BLOCKER: private declaration
private theorem bethReindexFOLKStep2_noCut {L : Language}
    {prem₁ prem₂ conc prem₁' prem₂' conc' : Sequent L}
    (rule : FOLKStep2 prem₁ prem₂ conc)
    (hprem₁ : prem₁ = prem₁') (hprem₂ : prem₂ = prem₂')
    (hconc : conc = conc') :
    bethFOLKStep2NoCut
        (bethReindexFOLKStep2 rule hprem₁ hprem₂ hconc) ↔
      bethFOLKStep2NoCut rule := by
  cases hprem₁
  cases hprem₂
  cases hconc
  exact Iff.rfl

-- ATTACH-BLOCKER: private declaration
private def bethLiftFOLKStep2 {L : Language}
    (F : FormulaN L)
    {prem₁ prem₂ conc : Sequent (ValidBridgeSupportLanguage F)}
    (rule : FOLKStep2 prem₁ prem₂ conc) :
    FOLKStep2 (validBridgeLiftSequent F prem₁)
      (validBridgeLiftSequent F prem₂)
      (validBridgeLiftSequent F conc) := by
  cases rule with
  | cut A Γ Δ Λ Θ =>
      let lifted :=
        FOLKStep2.cut (validBridgeLiftFormula F A)
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F))
          (Λ.map (validBridgeLiftFormula F))
          (Θ.map (validBridgeLiftFormula F))
      exact bethReindexFOLKStep2 lifted
        (by simp [validBridgeLiftSequent, List.map_append])
        (by simp [validBridgeLiftSequent])
        (by simp [validBridgeLiftSequent, List.map_append])
  | andRight A B Γ Δ =>
      let lifted :=
        FOLKStep2.andRight
          (validBridgeLiftFormula F A) (validBridgeLiftFormula F B)
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F))
      exact bethReindexFOLKStep2 lifted
        (by simp [validBridgeLiftSequent, List.map_append])
        (by simp [validBridgeLiftSequent, List.map_append])
        (by simp [validBridgeLiftSequent, validBridgeLiftFormula,
          List.map_append])
  | orLeft A B Γ Δ =>
      let lifted :=
        FOLKStep2.orLeft
          (validBridgeLiftFormula F A) (validBridgeLiftFormula F B)
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F))
      exact bethReindexFOLKStep2 lifted
        (by simp [validBridgeLiftSequent])
        (by simp [validBridgeLiftSequent])
        (by simp [validBridgeLiftSequent, validBridgeLiftFormula])
  | implLeft A B Γ Δ Λ Θ =>
      let lifted :=
        FOLKStep2.implLeft
          (validBridgeLiftFormula F A) (validBridgeLiftFormula F B)
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F))
          (Λ.map (validBridgeLiftFormula F))
          (Θ.map (validBridgeLiftFormula F))
      exact bethReindexFOLKStep2 lifted
        (by simp [validBridgeLiftSequent, List.map_append])
        (by simp [validBridgeLiftSequent])
        (by simp [validBridgeLiftSequent, validBridgeLiftFormula,
          List.map_append])

-- ATTACH-BLOCKER: private declaration
private theorem bethLiftFOLKStep2_noCut {L : Language}
    (F : FormulaN L)
    {prem₁ prem₂ conc : Sequent (ValidBridgeSupportLanguage F)}
    (rule : FOLKStep2 prem₁ prem₂ conc) :
    bethFOLKStep2NoCut (bethLiftFOLKStep2 F rule) ↔
      bethFOLKStep2NoCut rule := by
  cases rule <;>
    unfold bethLiftFOLKStep2 <;>
    rw [bethReindexFOLKStep2_noCut] <;>
    rfl

-- ATTACH-BLOCKER: private declaration
private def bethLiftFOLKProof {L : Language} (F : FormulaN L) :
    {s : Sequent (ValidBridgeSupportLanguage F)} →
      FOLKProofTree s →
      FOLKProofTree (validBridgeLiftSequent F s)
  | _, .axiom_ s h =>
      .axiom_ (validBridgeLiftSequent F s)
        (validBridgeLift_isFOLKAxiom F h)
  | _, .onePremise rule t =>
      .onePremise (validBridgeLiftFOLKStep1 F rule)
        (bethLiftFOLKProof F t)
  | _, .twoPremise rule t₁ t₂ =>
      .twoPremise (bethLiftFOLKStep2 F rule)
        (bethLiftFOLKProof F t₁)
        (bethLiftFOLKProof F t₂)

-- ATTACH-BLOCKER: private declaration
private theorem bethLiftFOLKProof_isCutFree {L : Language}
    (F : FormulaN L) {s : Sequent (ValidBridgeSupportLanguage F)}
    (t : FOLKProofTree s) (ht : t.isCutFree) :
    (bethLiftFOLKProof F t).isCutFree := by
  induction t with
  | axiom_ s h => trivial
  | onePremise rule t ih =>
      simp only [FOLKProofTree.isCutFree] at ht ⊢
      exact ih ht
  | twoPremise rule t₁ t₂ ih₁ ih₂ =>
      rw [bethFOLKTwoPremise_isCutFree] at ht
      simp only [bethLiftFOLKProof]
      rw [bethFOLKTwoPremise_isCutFree]
      exact ⟨(bethLiftFOLKStep2_noCut F rule).2 ht.1,
        ih₁ ht.2.1, ih₂ ht.2.2⟩

-- ATTACH-BLOCKER: private declaration
private theorem bethCutFree_of_rectified_valid {L : Language}
    (hNoEq : L.withoutEquality)
    (A B : FormulaN L)
    (hCross : crossNoFreeBound (Sequent.mk [A] [B]))
    (hValid : universallyValidN (FormulaN.impl A B)) :
    folkCutFreeProvable { antecedent := [A], succedent := [B] } := by
  let F := FormulaN.conj A B
  let K := ValidBridgeSupportLanguage F
  let A' : FormulaN K :=
    validBridgeRestrictFormula F A
      (fun _ h => Or.inl h) (fun _ h => Or.inl h)
      (fun _ h => Or.inl h)
  let B' : FormulaN K :=
    validBridgeRestrictFormula F B
      (fun _ h => Or.inr h) (fun _ h => Or.inr h)
      (fun _ h => Or.inr h)
  let q : Sequent K := { antecedent := [A'], succedent := [B'] }
  letI : Countable (Term K) := by
    dsimp [K]
    exact
      validBridgeTermCountable (ValidBridgeSupportLanguage F)
        (validBridgeFormulaFunSymbols F).attach
        (validBridgeFormulaConstSymbols F).attach
        (List.mem_attach (validBridgeFormulaFunSymbols F))
        (List.mem_attach (validBridgeFormulaConstSymbols F))
  have hAB :
      validBridgeLiftFormula F A' = A ∧
        validBridgeLiftFormula F B' = B := by
    constructor
    · exact validBridgeLift_restrictFormula F A
        (fun _ h => Or.inl h) (fun _ h => Or.inl h)
        (fun _ h => Or.inl h)
    · exact validBridgeLift_restrictFormula F B
        (fun _ h => Or.inr h) (fun _ h => Or.inr h)
        (fun _ h => Or.inr h)
  have hFvBvA :
      formulaFVN A' = formulaFVN A ∧ formulaBVN A' = formulaBVN A :=
    bethRestrictFormula_fv_bv F A
      (fun _ h => Or.inl h) (fun _ h => Or.inl h)
      (fun _ h => Or.inl h)
  have hFvBvB :
      formulaFVN B' = formulaFVN B ∧ formulaBVN B' = formulaBVN B :=
    bethRestrictFormula_fv_bv F B
      (fun _ h => Or.inr h) (fun _ h => Or.inr h)
      (fun _ h => Or.inr h)
  have hCrossQ : crossNoFreeBound q := by
    intro x hFree D hD hBound
    obtain ⟨C, hC, hx⟩ := hFree
    simp only [q, List.singleton_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hC hD
    have hFreeAB : ∃ C ∈ ([A] ++ [B]), x ∈ formulaFVN C := by
      rcases hC with rfl | rfl
      · exact ⟨A, by simp, by simpa only [hFvBvA.1] using hx⟩
      · exact ⟨B, by simp, by simpa only [hFvBvB.1] using hx⟩
    rcases hD with rfl | rfl
    · exact hCross x hFreeAB A (by simp)
        (by simpa only [hFvBvA.2] using hBound)
    · exact hCross x hFreeAB B (by simp)
        (by simpa only [hFvBvB.2] using hBound)
  have hKEq : K.withoutEquality := by
    simpa [K, ValidBridgeSupportLanguage, Language.withoutEquality] using hNoEq
  have hQValid : sequentValid q := by
    intro M s hAnte
    have hA' : formulaEvalN M A' s :=
      hAnte A' (by simp [q])
    have hA :
        formulaEvalN (validBridgeExtendStructure F M) A s :=
      (validBridgeRestrictFormula_eval F M s A
        (fun _ h => Or.inl h) (fun _ h => Or.inl h)
        (fun _ h => Or.inl h)).mp hA'
    have hB :
        formulaEvalN (validBridgeExtendStructure F M) B s :=
      hValid (validBridgeExtendStructure F M) s hA
    refine ⟨B', by simp [q], ?_⟩
    exact
      (validBridgeRestrictFormula_eval F M s B
        (fun _ h => Or.inr h) (fun _ h => Or.inr h)
        (fun _ h => Or.inr h)).mpr hB
  obtain ⟨g⟩ := LCS.CutElim.CompletenessBridge.completenessG_cross hKEq q hCrossQ hQValid
  obtain ⟨t, ht⟩ := gProofTree_to_folkCutFree g
  have hConclusion :
      validBridgeLiftSequent F q =
        { antecedent := [A], succedent := [B] } := by
    simp [q, validBridgeLiftSequent, hAB.1, hAB.2]
  rw [← hConclusion]
  exact ⟨bethLiftFOLKProof F t,
    bethLiftFOLKProof_isCutFree F t ht⟩

-- ATTACH-BLOCKER: private declaration
private theorem bethFolkSingletonImp_valid {L : Language}
    (A B : FormulaN L)
    (hProv : folkProvable { antecedent := [A], succedent := [B] }) :
    universallyValidN (FormulaN.impl A B) := by
  intro M s hA
  obtain ⟨C, hC, hEval⟩ :=
    soundness_FOLK { antecedent := [A], succedent := [B] } hProv
      M s (by
        intro C hC
        have hCA : C = A := by simpa using hC
        subst C
        exact hA)
  have hCB : C = B := by simpa using hC
  subst C
  exact hEval

-- ATTACH-BLOCKER: private declaration
/-- The left side of the Craig implication in L⁺: A(P,Q) ∧ Q(x̄). -/
private def bethCraigAntecedent {L : Language}
    (implDef : ImplicitDefinability L) :
    FormulaN (L.addPred (L.predArity implDef.predQ)) :=
  .conj (implDef.axiomFormula.liftAddPred (L.predArity implDef.predQ))
    (bethPredApplied (some implDef.predQ))

-- ATTACH-BLOCKER: private declaration
/-- The right side in L⁺: A(P,Q′) ⊃ Q′(x̄), where Q′ is the fresh predicate none. -/
private noncomputable def bethCraigConsequent {L : Language}
    (implDef : ImplicitDefinability L) :
    FormulaN (L.addPred (L.predArity implDef.predQ)) :=
  .impl
    (formulaPredSubstN (some implDef.predQ) none rfl
      (implDef.axiomFormula.liftAddPred (L.predArity implDef.predQ)))
    (bethPredApplied none)

/-- The implicit-definability condition yields the Craig implication
as an LK-provable sequent in the fresh-predicate expansion. -/
private theorem bethCraigImplication_provable {L : Language}
    (hNoEq : L.withoutEquality) (implDef : ImplicitDefinability L) :
    folkProvable
      ⟨[bethCraigAntecedent implDef], [bethCraigConsequent implDef]⟩ := by
  -- Specialize the universal prefix of validityCondition and curry the
  -- resulting implication; obtain an LK proof using validity with cuts.
  -- REPAIR(T6-57b): proof pending
  sorry

/-- If no listed predicate occurs in A, the two sides of the L⁺ Craig
implication have no common predicate: only some Q can occur on the left,
and only the fresh none can occur on the right. -/
private theorem bethCraig_no_common_pred {L : Language}
    (implDef : ImplicitDefinability L)
    (hNone : NoPredOccurs implDef.axiomFormula implDef.preds) :
    ∀ P : (L.addPred (L.predArity implDef.predQ)).predSymbols,
      ¬ (LCS.CutElim.Interpolation.formulaPredSymbolsN (bethCraigAntecedent implDef) P ∧
        LCS.CutElim.Interpolation.formulaPredSymbolsN (bethCraigConsequent implDef) P) := by
  -- REPAIR(T6-57b): proof pending
  sorry

/-- Interpret the fresh predicate as Q to lower Craig's disjunction
from L⁺ to the original language, then universally quantify Q's arguments. -/
private theorem bethCraig_dichotomy_lower {L : Language}
    (implDef : ImplicitDefinability L)
    (hCraig :
      folkProvable ⟨[bethCraigAntecedent implDef], []⟩ ∨
      folkProvable ⟨[], [bethCraigConsequent implDef]⟩) :
    UnivTrueOrFalse implDef := by
  -- The left branch says A ∧ Q is impossible; the right branch says
  -- A(P,Q′) implies Q′. Lower by interpreting the fresh copy as Q.
  -- REPAIR(T6-57b): proof pending
  sorry

private theorem beth_explicit_definer_exists
    (L : Language)
    (hNoEq : L.withoutEquality)
    (implDef : ImplicitDefinability L)
    (hOccurs : SomePredOccurs implDef.axiomFormula implDef.preds) :
    ∃ D : FormulaN L, ExplicitDefinabilityWitness implDef D := by
  -- Apply Craig interpolation in the fresh-predicate expansion, then
  -- lower the interpolant to L and adjoin a closed tautology over an
  -- occurring listed predicate to satisfy the nonempty-occurrence clause.
  -- REPAIR(T6-57a): proof pending
  sorry

-- ===================================================================
-- Theorem 6.6.1 (part a, required helper): beth_explicit_definer
-- ===================================================================

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Theorem 6.6.1 (part a, required helper): Given an implicit
definability witness for Q together with a proof that at least one
P_i occurs in the axiom formula, constructs an explicit definability
witness — the L-formula D(P_1,...,P_k) obtained from Craig's
interpolation (Theorem 6.5.1) that explicitly defines Q from
P_1,...,P_k.

STANDING ASSUMPTION #11 (§5.4): Theorem 6.6.1 is for first-order
languages WITHOUT equality; encoded by `L.withoutEquality`. -/
noncomputable def beth_explicit_definer
    (L : Language)
    (hNoEq : L.withoutEquality)
    (implDef : ImplicitDefinability L)
    (hOccurs : SomePredOccurs implDef.axiomFormula implDef.preds) :
    FormulaN L :=
-- BEGIN PROOF
  Classical.choose
    (beth_explicit_definer_exists L hNoEq implDef hOccurs)

-- ATTACH-BLOCKER: private name in relocated declaration
/-- The formula produced by `beth_explicit_definer` satisfies the
four conditions bundled in `ExplicitDefinabilityWitness`: its free
variables are among {x_0,...,x_{n-1}}, its predicate symbols are
among P_1,...,P_k, at least one P_i occurs, and the biconditional
under the axiom is universally valid. -/
theorem beth_explicit_definer_spec
    (L : Language)
    (hNoEq : L.withoutEquality)
    (implDef : ImplicitDefinability L)
    (hOccurs : SomePredOccurs implDef.axiomFormula implDef.preds) :
    ExplicitDefinabilityWitness implDef
      (beth_explicit_definer L hNoEq implDef hOccurs) :=
-- BEGIN PROOF
by
  exact Classical.choose_spec
    (beth_explicit_definer_exists L hNoEq implDef hOccurs)

-- ===================================================================
-- Theorem 6.6.1 (companion, part a): beth_without_equality_part_a
-- ===================================================================



-- ===================================================================
-- Theorem 6.6.1 (companion, part b): beth_without_equality_part_b
-- ===================================================================

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Theorem 6.6.1 (companion, part b): If no predicate symbol
occurs in the axiom formula, Q is universally true or false.

STANDING ASSUMPTION #11 (§5.4): Theorem 6.6.1 is for first-order
languages WITHOUT equality; encoded by `L.withoutEquality`. -/
theorem beth_without_equality_part_b
    (L : Language)
    (hNoEq : L.withoutEquality)
    (implDef : ImplicitDefinability L)
    (hNone : NoPredOccurs implDef.axiomFormula implDef.preds) :
    UnivTrueOrFalse implDef :=
-- BEGIN PROOF
by
  apply bethCraig_dichotomy_lower implDef
  exact LCS.CutElim.Interpolation.craig_interpolation_no_common_pred
    (bethCraigAntecedent implDef) (bethCraigConsequent implDef)
    (show (L.addPred (L.predArity implDef.predQ)).withoutEquality from hNoEq)
    (bethCraigImplication_provable hNoEq implDef)
    (bethCraig_no_common_pred implDef hNone)

-- ===================================================================
-- Theorem 6.6.1: beth_definability_without_equality
-- ===================================================================

/-- Theorem 6.6.1: (Beth's definability theorem, without equality)
(a) If some predicate symbol occurs in the axiom, implicit
definability implies explicit definability. (b) If no predicate
symbol occurs, Q is universally true or universally false.

STANDING ASSUMPTION #11 (§5.4): Theorem 6.6.1 is for first-order
languages WITHOUT equality; encoded by `L.withoutEquality`. -/
@[blueprint "chap6__theorem_6_6_1" (main := true)]
theorem beth_definability_without_equality
    (L : Language)
    (hNoEq : L.withoutEquality)
    (implDef : ImplicitDefinability L) :
    (SomePredOccurs implDef.axiomFormula implDef.preds →
      ∃ D : FormulaN L, ExplicitDefinabilityWitness implDef D) ∧
    (NoPredOccurs implDef.axiomFormula implDef.preds →
      UnivTrueOrFalse implDef) 

-- ===================================================================
-- Theorem 6.6.2 (companion, part a): beth_with_equality_part_a
-- ===================================================================

/-- Theorem 6.6.2 (companion, part a): Implicit definability of a
predicate implies explicit definability under the adopted equality-logical
reading R-BETH-EQ: D may contain equality, including when the P-list is empty.

STANDING ASSUMPTION #12 (§5.6): Theorem 6.6.2 is for first-order
languages WITH equality; encoded by `L.hasEquality = true`. -/
theorem beth_with_equality_part_a
    (L : Language)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (hEq : L.hasEquality = true)
    (implDef : ImplicitDefinabilityEq L) :
    ∃ D : FormulaN L, ExplicitDefinabilityWitnessEq implDef D :=
-- BEGIN PROOF
by
  -- REPAIR(T6-58): proof pending
  sorry

-- ===================================================================
-- Theorem 6.6.2 (companion, part b): beth_with_equality_part_b
-- ===================================================================

/-- Theorem 6.6.2 (companion, part b): Implicit definability of a
function or constant occurring in A implies explicit definability.

STANDING ASSUMPTION #12 (§5.6): Theorem 6.6.2 is for first-order
languages WITH equality; encoded by `L.hasEquality = true`. -/
theorem beth_with_equality_part_b
    (L : Language)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (hEq : L.hasEquality = true)
    (implDef : ImplicitDefinabilityFunc L) :
    ∃ D : FormulaN L, ExplicitDefinabilityFuncWitness implDef D :=
-- BEGIN PROOF
by
  -- Use equality interpolation in the selected symbol's fresh expansion
  -- and lower the defining formula to L, retaining the output variable y.
  -- REPAIR(T6-57c): proof pending
  sorry

-- ===================================================================
-- Theorem 6.6.2: beth_definability_with_equality
-- ===================================================================

/-- Theorem 6.6.2: (Beth's definability theorem, with equality)
(a) Implicit definability of a predicate implies explicit
definability under R-BETH-EQ, allowing equality in D and an empty P-list.
(b) Implicit definability of a function or constant
occurring in A implies explicit definability.

STANDING ASSUMPTION #12 (§5.6): Theorem 6.6.2 is for first-order
languages WITH equality; encoded by `L.hasEquality = true`. -/
@[blueprint "chap6__theorem_6_6_2" (main := true)]
theorem beth_definability_with_equality
    (L : Language)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (hEq : L.hasEquality = true) :
    (∀ implDef : ImplicitDefinabilityEq L,
      ∃ D : FormulaN L, ExplicitDefinabilityWitnessEq implDef D) ∧
    (∀ implDef : ImplicitDefinabilityFunc L,
      ∃ D : FormulaN L, ExplicitDefinabilityFuncWitness implDef D) 

end LCS.CutElim.Beth
end

