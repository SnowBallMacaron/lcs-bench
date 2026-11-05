import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.CutElim.CompletenessBridge
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.LKe.Equivalence.AtomicLeaves
import LCS.CutElim.LKe.Equivalence.ContextPermutation
import LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
import LCS.CutElim.LKe.Equivalence.ImplicationPermutation
import LCS.CutElim.LKe.Equivalence.Normalization
import LCS.CutElim.LKe.Equivalence.AtomicTranslation
import LCS.CutElim.LKe.Equivalence.EqualityTranslation
import Attach
import LCS.CutElim.LKe.Equivalence.Validity.ProofsStamp

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

-- retained: used by LCS.CutElim.Beth.Part2
theorem validBridgeLift_restrictTerm {L : Language} (F : FormulaN L) :
    ∀ (t : Term L)
      (hf : ∀ f, validBridgeTermFunOccurs f t →
        validBridgeFormulaFunOccurs f F)
      (hc : ∀ c, validBridgeTermConstOccurs c t →
        validBridgeFormulaConstOccurs c F),
      validBridgeLiftTerm F (validBridgeRestrictTerm F t hf hc) = t := by
  intro t
  induction t with
  | var n => intro hf hc; rfl
  | const c => intro hf hc; rfl
  | func f ts ih =>
      intro hf hc
      simp only [validBridgeRestrictTerm, validBridgeLiftTerm]
      congr 1
      funext i
      exact ih i
        (fun g hg => hf g (Or.inr ⟨i, hg⟩))
        (fun c hc' => hc c ⟨i, hc'⟩)

-- retained: used by LCS.CutElim.Beth.Part2
theorem validBridgeLift_restrictFormula {L : Language} (F : FormulaN L) :
    ∀ (A : FormulaN L)
      (hf : ∀ f, validBridgeFormulaFunOccurs f A →
        validBridgeFormulaFunOccurs f F)
      (hc : ∀ c, validBridgeFormulaConstOccurs c A →
        validBridgeFormulaConstOccurs c F)
      (hp : ∀ P, validBridgeFormulaPredOccurs P A →
        validBridgeFormulaPredOccurs P F),
      validBridgeLiftFormula F
        (validBridgeRestrictFormula F A hf hc hp) = A := by
  intro A
  induction A with
  | predN P ts =>
      intro hf hc hp
      simp only [validBridgeRestrictFormula, validBridgeLiftFormula]
      congr 1
      funext i
      exact validBridgeLift_restrictTerm F (ts i)
        (fun f h => hf f ⟨i, h⟩)
        (fun c h => hc c ⟨i, h⟩)
  | eq_ hL t₁ t₂ =>
      intro hf hc hp
      simp only [validBridgeRestrictFormula, validBridgeLiftFormula]
      rw [validBridgeLift_restrictTerm, validBridgeLift_restrictTerm]
  | neg A ih =>
      intro hf hc hp
      simp only [validBridgeRestrictFormula, validBridgeLiftFormula]
      exact congrArg FormulaN.neg (ih hf hc hp)
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      intro hf hc hp
      simp only [validBridgeRestrictFormula, validBridgeLiftFormula]
      rw [ihA, ihB]
  | all x A ih | ex x A ih =>
      intro hf hc hp
      simp only [validBridgeRestrictFormula, validBridgeLiftFormula]
      exact congrArg _ (ih hf hc hp)

-- retained: used by LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeLift_restrictSelf {L : Language} (F : FormulaN L) :
    validBridgeLiftFormula F (validBridgeRestrictSelf F) = F :=
  validBridgeLift_restrictFormula F F
    (fun _ h => h) (fun _ h => h) (fun _ h => h)

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.Interpolation.Equality.Support
noncomputable def validBridgeExtendStructure {L : Language}
    (F : FormulaN L) (M : Structure (ValidBridgeSupportLanguage F)) :
    Structure L := by
  classical
  exact
    { carrier := M.carrier
      carrierNonempty := M.carrierNonempty
      interpFunc := fun f xs =>
        if h : f ∈ validBridgeFormulaFunSymbols F then
          M.interpFunc ⟨f, h⟩ xs
        else
          Classical.choice M.carrierNonempty
      interpConst := fun c =>
        if h : c ∈ validBridgeFormulaConstSymbols F then
          M.interpConst ⟨c, h⟩
        else
          Classical.choice M.carrierNonempty
      interpPred := fun P xs =>
        if h : P ∈ validBridgeFormulaPredSymbols F then
          M.interpPred ⟨P, h⟩ xs
        else
          False }

-- retained: used by LCS.CutElim.Beth.Part2
theorem validBridgeRestrictTerm_eval {L : Language}
    (F : FormulaN L) (M : Structure (ValidBridgeSupportLanguage F))
    (s : Assignment M) :
    ∀ (t : Term L)
      (hf : ∀ f, validBridgeTermFunOccurs f t →
        validBridgeFormulaFunOccurs f F)
      (hc : ∀ c, validBridgeTermConstOccurs c t →
        validBridgeFormulaConstOccurs c F),
      termEval M s (validBridgeRestrictTerm F t hf hc) =
        termEval (validBridgeExtendStructure F M) s t := by
  intro t
  induction t with
  | var n =>
      intro hf hc
      rfl
  | const c =>
      intro hf hc
      have hmem : c ∈ validBridgeFormulaConstSymbols F :=
        validBridgeFormulaConstOccurs_mem
          (hc c (by simp [validBridgeTermConstOccurs]))
      simp [validBridgeRestrictTerm, termEval,
        validBridgeExtendStructure, hmem]
  | func f ts ih =>
      intro hf hc
      have hmem : f ∈ validBridgeFormulaFunSymbols F :=
        validBridgeFormulaFunOccurs_mem (hf f (Or.inl rfl))
      simp only [validBridgeRestrictTerm, termEval,
        validBridgeExtendStructure, dif_pos hmem]
      congr 1
      funext i
      exact ih i
        (fun g hg => hf g (Or.inr ⟨i, hg⟩))
        (fun c hc' => hc c ⟨i, hc'⟩)

-- retained: used by LCS.CutElim.Beth.Part2
theorem validBridgeRestrictFormula_eval {L : Language}
    (F : FormulaN L) (M : Structure (ValidBridgeSupportLanguage F))
    (s : Assignment M) :
    ∀ (A : FormulaN L)
      (hf : ∀ f, validBridgeFormulaFunOccurs f A →
        validBridgeFormulaFunOccurs f F)
      (hc : ∀ c, validBridgeFormulaConstOccurs c A →
        validBridgeFormulaConstOccurs c F)
      (hp : ∀ P, validBridgeFormulaPredOccurs P A →
        validBridgeFormulaPredOccurs P F),
      formulaEvalN M (validBridgeRestrictFormula F A hf hc hp) s ↔
        formulaEvalN (validBridgeExtendStructure F M) A s := by
  intro A
  induction A generalizing s with
  | predN P ts =>
      intro hf hc hp
      have hmem : P ∈ validBridgeFormulaPredSymbols F :=
        validBridgeFormulaPredOccurs_mem
          (hp P (by simp [validBridgeFormulaPredOccurs]))
      simp only [validBridgeRestrictFormula, formulaEvalN,
        validBridgeExtendStructure, dif_pos hmem]
      have hproof :
          validBridgeFormulaPredOccurs_mem
              (hp P (by simp [validBridgeFormulaPredOccurs])) =
            hmem :=
        Subsingleton.elim _ _
      cases hproof
      apply iff_of_eq
      apply congrArg (M.interpPred
        ⟨P, validBridgeFormulaPredOccurs_mem
          (hp P (by simp [validBridgeFormulaPredOccurs]))⟩)
      funext i
      exact validBridgeRestrictTerm_eval F M s (ts i)
        (fun f h => hf f ⟨i, h⟩)
        (fun c h => hc c ⟨i, h⟩)
  | eq_ hL t₁ t₂ =>
      intro hf hc hp
      simp only [validBridgeRestrictFormula, formulaEvalN]
      rw [validBridgeRestrictTerm_eval, validBridgeRestrictTerm_eval]
      exact Iff.rfl
  | neg A ih =>
      intro hf hc hp
      simp only [validBridgeRestrictFormula, formulaEvalN,
        LCS.FirstOrder.Basic.negM]
      exact not_congr (ih s hf hc hp)
  | conj A B ihA ihB =>
      intro hf hc hp
      simp only [validBridgeRestrictFormula, formulaEvalN,
        LCS.FirstOrder.Basic.andM]
      exact and_congr
        (ihA s
          (fun f h => hf f (Or.inl h))
          (fun c h => hc c (Or.inl h))
          (fun P h => hp P (Or.inl h)))
        (ihB s
          (fun f h => hf f (Or.inr h))
          (fun c h => hc c (Or.inr h))
          (fun P h => hp P (Or.inr h)))
  | disj A B ihA ihB =>
      intro hf hc hp
      simp only [validBridgeRestrictFormula, formulaEvalN,
        LCS.FirstOrder.Basic.orM]
      exact or_congr
        (ihA s
          (fun f h => hf f (Or.inl h))
          (fun c h => hc c (Or.inl h))
          (fun P h => hp P (Or.inl h)))
        (ihB s
          (fun f h => hf f (Or.inr h))
          (fun c h => hc c (Or.inr h))
          (fun P h => hp P (Or.inr h)))
  | impl A B ihA ihB =>
      intro hf hc hp
      simp only [validBridgeRestrictFormula, formulaEvalN,
        LCS.FirstOrder.Basic.implM]
      exact imp_congr
        (ihA s
          (fun f h => hf f (Or.inl h))
          (fun c h => hc c (Or.inl h))
          (fun P h => hp P (Or.inl h)))
        (ihB s
          (fun f h => hf f (Or.inr h))
          (fun c h => hc c (Or.inr h))
          (fun P h => hp P (Or.inr h)))
  | all x A ih =>
      intro hf hc hp
      simp only [validBridgeRestrictFormula, formulaEvalN]
      constructor
      · intro h a
        exact (ih (assignUpdate s x a) hf hc hp).mp (h a)
      · intro h a
        exact (ih (assignUpdate s x a) hf hc hp).mpr (h a)
  | ex x A ih =>
      intro hf hc hp
      simp only [validBridgeRestrictFormula, formulaEvalN]
      constructor
      · rintro ⟨a, ha⟩
        exact ⟨a, (ih (assignUpdate s x a) hf hc hp).mp ha⟩
      · rintro ⟨a, ha⟩
        exact ⟨a, (ih (assignUpdate s x a) hf hc hp).mpr ha⟩

-- retained: used by LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeRestrictSelf_eval {L : Language}
    (F : FormulaN L) (M : Structure (ValidBridgeSupportLanguage F))
    (s : Assignment M) :
    formulaEvalN M (validBridgeRestrictSelf F) s ↔
      formulaEvalN (validBridgeExtendStructure F M) F s :=
  validBridgeRestrictFormula_eval F M s F
    (fun _ h => h) (fun _ h => h) (fun _ h => h)

-- ===================================================================
-- Semantic bridge infrastructure: lifting finite-support proofs
-- ===================================================================

-- retained: used by LCS.CutElim.Beth.Part2
theorem validBridgeLiftTerm_termFV {L : Language} (F : FormulaN L) :
    ∀ t : Term (ValidBridgeSupportLanguage F),
      termFV (validBridgeLiftTerm F t) = termFV t := by
  intro t
  induction t with
  | var n => rfl
  | const c => rfl
  | func f ts ih =>
      ext x
      simp only [validBridgeLiftTerm, termFV]
      change (∃ i, x ∈ termFV (validBridgeLiftTerm F (ts i))) ↔
        ∃ i, x ∈ termFV (ts i)
      constructor
      · rintro ⟨i, hi⟩
        rw [ih i] at hi
        exact ⟨i, hi⟩
      · rintro ⟨i, hi⟩
        refine ⟨i, ?_⟩
        rw [ih i]
        exact hi

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeLiftTerm_subst {L : Language} (F : FormulaN L) :
    ∀ (u t : Term (ValidBridgeSupportLanguage F)) (x : Nat),
      validBridgeLiftTerm F (termSubst u t x) =
        termSubst (validBridgeLiftTerm F u)
          (validBridgeLiftTerm F t) x := by
  intro u
  induction u with
  | var n =>
      intro t x
      simp only [termSubst, validBridgeLiftTerm]
      split <;> rfl
  | const c =>
      intro t x
      rfl
  | func f ts ih =>
      intro t x
      simp only [termSubst, validBridgeLiftTerm]
      congr 1
      funext i
      exact ih i t x

-- retained: used by LCS.CutElim.Beth.Part2
theorem validBridgeLiftFormula_fv {L : Language} (F : FormulaN L) :
    ∀ A : FormulaN (ValidBridgeSupportLanguage F),
      formulaFVN (validBridgeLiftFormula F A) = formulaFVN A := by
  intro A
  induction A with
  | predN P ts =>
      ext x
      simp only [validBridgeLiftFormula, formulaFVN]
      change
        (∃ i, x ∈ termFV (validBridgeLiftTerm F (ts i))) ↔
          ∃ i, x ∈ termFV (ts i)
      constructor
      · rintro ⟨i, hi⟩
        rw [validBridgeLiftTerm_termFV F (ts i)] at hi
        exact ⟨i, hi⟩
      · rintro ⟨i, hi⟩
        refine ⟨i, ?_⟩
        rw [validBridgeLiftTerm_termFV F (ts i)]
        exact hi
  | eq_ hL t₁ t₂ =>
      simp only [validBridgeLiftFormula, formulaFVN,
        validBridgeLiftTerm_termFV]
  | neg A ih =>
      simpa [validBridgeLiftFormula, formulaFVN] using ih
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      simp only [validBridgeLiftFormula, formulaFVN, ihA, ihB]
  | all x A ih | ex x A ih =>
      simp only [validBridgeLiftFormula, formulaFVN, ih]

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeLiftFormula_subst {L : Language} (F : FormulaN L) :
    ∀ (A : FormulaN (ValidBridgeSupportLanguage F))
      (t : Term (ValidBridgeSupportLanguage F)) (x : Nat),
      validBridgeLiftFormula F (formulaSubstN A t x) =
        formulaSubstN (validBridgeLiftFormula F A)
          (validBridgeLiftTerm F t) x := by
  intro A
  induction A with
  | predN P ts =>
      intro t x
      simp only [formulaSubstN, validBridgeLiftFormula]
      congr 1
      funext i
      exact validBridgeLiftTerm_subst F (ts i) t x
  | eq_ hL t₁ t₂ =>
      intro t x
      simp only [formulaSubstN, validBridgeLiftFormula,
        validBridgeLiftTerm_subst]
  | neg A ih =>
      intro t x
      simp only [formulaSubstN, validBridgeLiftFormula, ih]
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      intro t x
      simp only [formulaSubstN, validBridgeLiftFormula, ihA, ihB]
  | all y A ih | ex y A ih =>
      intro t x
      simp only [formulaSubstN, validBridgeLiftFormula]
      split
      · simp only [validBridgeLiftFormula, ih]
      · rfl

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeLift_isFreeFor {L : Language} (F : FormulaN L) :
    ∀ (t : Term (ValidBridgeSupportLanguage F)) (x : Nat)
      (A : FormulaN (ValidBridgeSupportLanguage F)),
      isFreeForN (validBridgeLiftTerm F t) x
          (validBridgeLiftFormula F A) ↔
        isFreeForN t x A := by
  intro t x A
  induction A with
  | predN P ts => rfl
  | eq_ hL t₁ t₂ => rfl
  | neg A ih =>
      simpa [validBridgeLiftFormula, isFreeForN] using ih
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      simp only [validBridgeLiftFormula, isFreeForN, ihA, ihB]
  | all y A ih | ex y A ih =>
      simp only [validBridgeLiftFormula, isFreeForN,
        validBridgeLiftTerm_termFV, ih]

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.Interpolation.Equality.Support
def validBridgeLiftSequent {L : Language} (F : FormulaN L)
    (s : Sequent (ValidBridgeSupportLanguage F)) : Sequent L :=
  Sequent.mk
    (s.antecedent.map (validBridgeLiftFormula F))
    (s.succedent.map (validBridgeLiftFormula F))

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeLift_isFOLKAxiom {L : Language} (F : FormulaN L)
    {s : Sequent (ValidBridgeSupportLanguage F)}
    (h : isFOLKAxiom s) :
    isFOLKAxiom (validBridgeLiftSequent F s) := by
  obtain ⟨A, hA, hB⟩ := h
  refine ⟨validBridgeLiftFormula F A, ?_, ?_⟩
  · simp [validBridgeLiftSequent, hA]
  · simp [validBridgeLiftSequent, hB]

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeLiftSequent_fresh {L : Language} (F : FormulaN L)
    {s : Sequent (ValidBridgeSupportLanguage F)} {y : Nat}
    (h : ∀ A ∈ s.antecedent ++ s.succedent, y ∉ formulaFVN A) :
    ∀ B ∈ (validBridgeLiftSequent F s).antecedent ++
        (validBridgeLiftSequent F s).succedent,
      y ∉ formulaFVN B := by
  intro B hB
  change B ∈
    s.antecedent.map (validBridgeLiftFormula F) ++
      s.succedent.map (validBridgeLiftFormula F) at hB
  rw [← List.map_append] at hB
  obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
  simpa only [validBridgeLiftFormula_fv] using h A hA

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.Interpolation.Equality.Support
def validBridgeLift_allRight
    (L : Language) (F : FormulaN L) (y : Nat) (x : Nat) (A : FormulaN (ValidBridgeSupportLanguage F)) (Γ :
      List (FormulaN (ValidBridgeSupportLanguage F))) (Δ : List (FormulaN (ValidBridgeSupportLanguage F)))
      (hfresh : ∀ (F_1 : FormulaN (ValidBridgeSupportLanguage F)), F_1 ∈ (Γ) ++ (Δ ++ [FormulaN.all x A]) → ¬y
      ∈ formulaFVN F_1) (hfree : isFreeForN (Term.var y) x A)
    : FOLKStep1 (validBridgeLiftSequent F (Sequent.mk (Γ) (Δ ++ [formulaSubstN A (Term.var y) x])))
      (validBridgeLiftSequent F (Sequent.mk (Γ) (Δ ++ [FormulaN.all x A]))) := by
  have hfresh' : ∀ G ∈ (Sequent.mk (Γ.map (validBridgeLiftFormula F)) (Δ.map (validBridgeLiftFormula F) ++
              [FormulaN.all x (validBridgeLiftFormula F A)])).antecedent ++
          (Sequent.mk (Γ.map (validBridgeLiftFormula F)) (Δ.map (validBridgeLiftFormula F) ++
              [FormulaN.all x (validBridgeLiftFormula F A)])).succedent,
        y ∉ formulaFVN G := by
    intro G hG
    apply validBridgeLiftSequent_fresh F (s := Sequent.mk Γ (Δ ++ [FormulaN.all x A])) hfresh G
    simpa [validBridgeLiftSequent, validBridgeLiftFormula, List.map_append] using hG
  have hfree' : isFreeForN (Term.var y) x (validBridgeLiftFormula F A) := by
    simpa [validBridgeLiftTerm] using (validBridgeLift_isFreeFor F (Term.var y) x A).mpr hfree
  simpa [validBridgeLiftSequent, validBridgeLiftFormula, validBridgeLiftFormula_subst, validBridgeLiftTerm,
    List.map_append] using
    FOLKStep1.allRight y x (validBridgeLiftFormula F A) (Γ.map (validBridgeLiftFormula F))
      (Δ.map (validBridgeLiftFormula F)) hfresh' hfree'

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.Interpolation.Equality.Support
def validBridgeLift_exLeft
    (L : Language) (F : FormulaN L) (y : Nat) (x : Nat) (A : FormulaN (ValidBridgeSupportLanguage F)) (Γ :
      List (FormulaN (ValidBridgeSupportLanguage F))) (Δ : List (FormulaN (ValidBridgeSupportLanguage F)))
      (hfresh : ∀ (F_1 : FormulaN (ValidBridgeSupportLanguage F)), F_1 ∈ (FormulaN.ex x A :: Γ) ++ (Δ) → ¬y ∈
      formulaFVN F_1) (hfree : isFreeForN (Term.var y) x A)
    : FOLKStep1 (validBridgeLiftSequent F (Sequent.mk (formulaSubstN A (Term.var y) x :: Γ) (Δ)))
      (validBridgeLiftSequent F (Sequent.mk (FormulaN.ex x A :: Γ) (Δ))) := by
  have hfresh' : ∀ G ∈ (Sequent.mk (FormulaN.ex x (validBridgeLiftFormula F A) ::
              Γ.map (validBridgeLiftFormula F))
            (Δ.map (validBridgeLiftFormula F))).antecedent ++
          (Sequent.mk (FormulaN.ex x (validBridgeLiftFormula F A) :: Γ.map (validBridgeLiftFormula F))
            (Δ.map (validBridgeLiftFormula F))).succedent,
        y ∉ formulaFVN G := by
    intro G hG
    apply validBridgeLiftSequent_fresh F (s := Sequent.mk (FormulaN.ex x A :: Γ) Δ) hfresh G
    simpa [validBridgeLiftSequent, validBridgeLiftFormula, List.map_append] using hG
  have hfree' : isFreeForN (Term.var y) x (validBridgeLiftFormula F A) := by
    simpa [validBridgeLiftTerm] using (validBridgeLift_isFreeFor F (Term.var y) x A).mpr hfree
  simpa [validBridgeLiftSequent, validBridgeLiftFormula, validBridgeLiftFormula_subst, validBridgeLiftTerm,
    List.map_append] using
    FOLKStep1.exLeft y x (validBridgeLiftFormula F A) (Γ.map (validBridgeLiftFormula F))
      (Δ.map (validBridgeLiftFormula F)) hfresh' hfree'

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.Interpolation.Equality.Support
def validBridgeLiftFOLKStep1 {L : Language} (F : FormulaN L)
    {prem conc : Sequent (ValidBridgeSupportLanguage F)}
    (rule : FOLKStep1 prem conc) :
    FOLKStep1 (validBridgeLiftSequent F prem)
      (validBridgeLiftSequent F conc) := by
  cases rule with
  | weakenLeft A Γ Δ =>
      simpa [validBridgeLiftSequent, validBridgeLiftFormula] using
        FOLKStep1.weakenLeft (validBridgeLiftFormula F A)
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F))
  | weakenRight A Γ Δ =>
      simpa [validBridgeLiftSequent, validBridgeLiftFormula,
        List.map_append] using
        FOLKStep1.weakenRight (validBridgeLiftFormula F A)
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F))
  | contractLeft A Γ Δ =>
      simpa [validBridgeLiftSequent, validBridgeLiftFormula] using
        FOLKStep1.contractLeft (validBridgeLiftFormula F A)
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F))
  | contractRight A Γ Δ =>
      simpa [validBridgeLiftSequent, validBridgeLiftFormula,
        List.map_append] using
        FOLKStep1.contractRight (validBridgeLiftFormula F A)
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F))
  | exchangeLeft Γ A B Δ Λ =>
      simpa [validBridgeLiftSequent, validBridgeLiftFormula,
        List.map_append] using
        FOLKStep1.exchangeLeft
          (Γ.map (validBridgeLiftFormula F))
          (validBridgeLiftFormula F A) (validBridgeLiftFormula F B)
          (Δ.map (validBridgeLiftFormula F))
          (Λ.map (validBridgeLiftFormula F))
  | exchangeRight Γ Δ A B Λ =>
      simpa [validBridgeLiftSequent, validBridgeLiftFormula,
        List.map_append] using
        FOLKStep1.exchangeRight
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F))
          (validBridgeLiftFormula F A) (validBridgeLiftFormula F B)
          (Λ.map (validBridgeLiftFormula F))
  | andLeftL A B Γ Δ =>
      simpa [validBridgeLiftSequent, validBridgeLiftFormula] using
        FOLKStep1.andLeftL
          (validBridgeLiftFormula F A) (validBridgeLiftFormula F B)
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F))
  | andLeftR A B Γ Δ =>
      simpa [validBridgeLiftSequent, validBridgeLiftFormula] using
        FOLKStep1.andLeftR
          (validBridgeLiftFormula F A) (validBridgeLiftFormula F B)
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F))
  | orRightL A B Γ Δ =>
      simpa [validBridgeLiftSequent, validBridgeLiftFormula,
        List.map_append] using
        FOLKStep1.orRightL
          (validBridgeLiftFormula F A) (validBridgeLiftFormula F B)
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F))
  | orRightR A B Γ Δ =>
      simpa [validBridgeLiftSequent, validBridgeLiftFormula,
        List.map_append] using
        FOLKStep1.orRightR
          (validBridgeLiftFormula F A) (validBridgeLiftFormula F B)
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F))
  | implRight A B Γ Δ =>
      simpa [validBridgeLiftSequent, validBridgeLiftFormula,
        List.map_append] using
        FOLKStep1.implRight
          (validBridgeLiftFormula F A) (validBridgeLiftFormula F B)
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F))
  | negLeft A Γ Δ =>
      simpa [validBridgeLiftSequent, validBridgeLiftFormula,
        List.map_append] using
        FOLKStep1.negLeft (validBridgeLiftFormula F A)
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F))
  | negRight A Γ Δ =>
      simpa [validBridgeLiftSequent, validBridgeLiftFormula,
        List.map_append] using
        FOLKStep1.negRight (validBridgeLiftFormula F A)
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F))
  | allLeft t x A Γ Δ hfree =>
      have hfree' :
          isFreeForN (validBridgeLiftTerm F t) x
            (validBridgeLiftFormula F A) :=
        (validBridgeLift_isFreeFor F t x A).mpr hfree
      simpa [validBridgeLiftSequent, validBridgeLiftFormula,
        validBridgeLiftFormula_subst, List.map_append] using
        FOLKStep1.allLeft (validBridgeLiftTerm F t) x
          (validBridgeLiftFormula F A)
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F)) hfree'
  | allRight y x A Γ Δ hfresh hfree =>
      exact validBridgeLift_allRight L F y x A Γ Δ hfresh hfree
  | exLeft y x A Γ Δ hfresh hfree =>
      exact validBridgeLift_exLeft L F y x A Γ Δ hfresh hfree
  | exRight t x A Γ Δ hfree =>
      have hfree' :
          isFreeForN (validBridgeLiftTerm F t) x
            (validBridgeLiftFormula F A) :=
        (validBridgeLift_isFreeFor F t x A).mpr hfree
      simpa [validBridgeLiftSequent, validBridgeLiftFormula,
        validBridgeLiftFormula_subst, List.map_append] using
        FOLKStep1.exRight (validBridgeLiftTerm F t) x
          (validBridgeLiftFormula F A)
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F)) hfree'

-- retained: used by LCS.CutElim.Interpolation.Equality.Support
def validBridgeLiftFOLKStep2 {L : Language} (F : FormulaN L)
    {prem₁ prem₂ conc : Sequent (ValidBridgeSupportLanguage F)}
    (rule : FOLKStep2 prem₁ prem₂ conc) :
    FOLKStep2 (validBridgeLiftSequent F prem₁)
      (validBridgeLiftSequent F prem₂)
      (validBridgeLiftSequent F conc) := by
  cases rule with
  | cut A Γ Δ Λ Θ =>
      simpa [validBridgeLiftSequent, validBridgeLiftFormula,
        List.map_append] using
        FOLKStep2.cut (validBridgeLiftFormula F A)
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F))
          (Λ.map (validBridgeLiftFormula F))
          (Θ.map (validBridgeLiftFormula F))
  | andRight A B Γ Δ =>
      simpa [validBridgeLiftSequent, validBridgeLiftFormula,
        List.map_append] using
        FOLKStep2.andRight
          (validBridgeLiftFormula F A) (validBridgeLiftFormula F B)
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F))
  | orLeft A B Γ Δ =>
      simpa [validBridgeLiftSequent, validBridgeLiftFormula,
        List.map_append] using
        FOLKStep2.orLeft
          (validBridgeLiftFormula F A) (validBridgeLiftFormula F B)
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F))
  | implLeft A B Γ Δ Λ Θ =>
      simpa [validBridgeLiftSequent, validBridgeLiftFormula,
        List.map_append] using
        FOLKStep2.implLeft
          (validBridgeLiftFormula F A) (validBridgeLiftFormula F B)
          (Γ.map (validBridgeLiftFormula F))
          (Δ.map (validBridgeLiftFormula F))
          (Λ.map (validBridgeLiftFormula F))
          (Θ.map (validBridgeLiftFormula F))



-- retained: used by LCS.CutElim.Interpolation.Equality.Support
def validBridgeLiftEqualityAxiom {L : Language} (F : FormulaN L) :
    LKeEqualityAxiom (ValidBridgeSupportLanguage F) →
      LKeEqualityAxiom L
  | .refl t => .refl (validBridgeLiftTerm F t)
  | .funcCong f ss ts =>
      .funcCong f.1
        (fun i => validBridgeLiftTerm F (ss i))
        (fun i => validBridgeLiftTerm F (ts i))
  | .predCong P ss ts =>
      .predCong P.1
        (fun i => validBridgeLiftTerm F (ss i))
        (fun i => validBridgeLiftTerm F (ts i))
  | .eqCong s1 s2 t1 t2 =>
      .eqCong
        (validBridgeLiftTerm F s1)
        (validBridgeLiftTerm F s2)
        (validBridgeLiftTerm F t1)
        (validBridgeLiftTerm F t2)

-- retained: used by LCS.CutElim.Interpolation.Equality.Support
theorem validBridgeLiftEqualityAxiom_toSequent {L : Language}
    (F : FormulaN L)
    (hL : (ValidBridgeSupportLanguage F).hasEquality = true)
    (ax : LKeEqualityAxiom (ValidBridgeSupportLanguage F)) :
    validBridgeLiftSequent F (ax.toSequent hL) =
      LKeEqualityAxiom.toSequent (L := L) hL
        (validBridgeLiftEqualityAxiom F ax) := by
  cases ax with
  | refl t =>
      rfl
  | funcCong f ss ts =>
      simp [LKeEqualityAxiom.toSequent, validBridgeLiftSequent,
        validBridgeLiftEqualityAxiom, validBridgeLiftFormula,
        validBridgeLiftTerm,
        List.map_map, List.map_append, Function.comp_apply]
      change
        List.map
            (fun i : Fin (L.funArity f.1) =>
              FormulaN.eq_ (L := L) hL
                (validBridgeLiftTerm (L := L) F (ss i))
                (validBridgeLiftTerm (L := L) F (ts i)))
            (List.finRange (L.funArity f.1)) =
          List.map
            (fun i : Fin (L.funArity f.1) =>
              FormulaN.eq_ (L := L) hL
                (validBridgeLiftTerm (L := L) F (ss i))
                (validBridgeLiftTerm (L := L) F (ts i)))
            (List.finRange (L.funArity f.1))
      rfl
  | predCong P ss ts =>
      simp [LKeEqualityAxiom.toSequent, validBridgeLiftSequent,
        validBridgeLiftEqualityAxiom, validBridgeLiftFormula,
        validBridgeLiftTerm,
        List.map_map, List.map_append, Function.comp_apply]
      change
        List.map
            (fun i : Fin (L.predArity P.1) =>
              FormulaN.eq_ (L := L) hL
                (validBridgeLiftTerm (L := L) F (ss i))
                (validBridgeLiftTerm (L := L) F (ts i)))
            (List.finRange (L.predArity P.1)) =
          List.map
            (fun i : Fin (L.predArity P.1) =>
              FormulaN.eq_ (L := L) hL
                (validBridgeLiftTerm (L := L) F (ss i))
                (validBridgeLiftTerm (L := L) F (ts i)))
            (List.finRange (L.predArity P.1))
      rfl
  | eqCong s1 s2 t1 t2 =>
      rfl

-- retained: used by LCS.CutElim.Interpolation.Equality.Axioms, LCS.CutElim.Interpolation.Equality.Reduction, LCS.CutElim.Interpolation.Equality.Support
def validBridgeLiftLKeProof {L : Language} (F : FormulaN L) :
    {s : Sequent (ValidBridgeSupportLanguage F)} →
      LKeProofTree s →
      LKeProofTree (validBridgeLiftSequent F s)
  | _, .axiom_ s h =>
      .axiom_ (validBridgeLiftSequent F s)
        (validBridgeLift_isFOLKAxiom F h)
  | _, .eqAxiom hL ax => by
      rw [validBridgeLiftEqualityAxiom_toSequent F hL ax]
      exact LKeProofTree.eqAxiom (L := L) hL
        (validBridgeLiftEqualityAxiom F ax)
  | _, .onePremise rule t =>
      .onePremise (validBridgeLiftFOLKStep1 F rule)
        (validBridgeLiftLKeProof F t)
  | _, .twoPremise rule t1 t2 =>
      .twoPremise (validBridgeLiftFOLKStep2 F rule)
        (validBridgeLiftLKeProof F t1)
        (validBridgeLiftLKeProof F t2)



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

-- Helper: removing a valid formula from the antecedent preserves lkeProvable.
-- retained: used by LCS.CutElim.Interpolation.Equality.Replay
theorem lkeProvable_remove_valid_antecedent {L : Language}
    (A : FormulaN L) (Γ Δ : List (FormulaN L)) (Λ : List (FormulaN L))
    (hvalid_A : ∀ (M : Structure L) (s : Assignment M), formulaEvalN M A s)
    (h : lkeProvable (Sequent.mk (Γ ++ [A] ++ Δ) Λ)) :
    lkeProvable (Sequent.mk (Γ ++ Δ) Λ) := by
-- BEGIN PROOF
  apply lkeProvable_of_valid
  have hvalid := lkeProvable_valid _ h
  intro M s hAnte
  apply hvalid M s
  intro F hF
  simp only [List.append_assoc, List.singleton_append] at hF
  rcases List.mem_append.mp hF with hFΓ | hFA
  · exact hAnte F (List.mem_append_left _ hFΓ)
  · rcases List.mem_cons.mp hFA with rfl | hFΔ
    · exact hvalid_A M s
    · exact hAnte F (List.mem_append_right _ hFΔ)

-- Helper: removing a list of valid formulas from the antecedent prefix
-- retained: used by LCS.CutElim.Interpolation.Equality.Replay
theorem lkeProvable_remove_valid_prefix {L : Language}
    (axioms : List (FormulaN L)) (rest : List (FormulaN L))
    (Λ : List (FormulaN L))
    (hvalid : ∀ A ∈ axioms,
      ∀ (M : Structure L) (s : Assignment M), formulaEvalN M A s)
    (h : lkeProvable (Sequent.mk (axioms ++ rest) Λ)) :
    lkeProvable (Sequent.mk rest Λ) := by
-- BEGIN PROOF
  induction axioms with
  | nil => exact h
  | cons a axioms' ih =>
    have hvalid_a : ∀ (M : Structure L) (s : Assignment M),
        formulaEvalN M a s :=
      hvalid a (List.Mem.head _)
    have hvalid' : ∀ A ∈ axioms',
        ∀ (M : Structure L) (s : Assignment M), formulaEvalN M A s :=
      fun A hA => hvalid A (List.mem_cons_of_mem _ hA)
    have h' : lkeProvable
        (Sequent.mk ([] ++ [a] ++ (axioms' ++ rest)) Λ) := by
      simp at h ⊢; exact h
    have h'' := lkeProvable_remove_valid_antecedent a []
      (axioms' ++ rest) Λ hvalid_a h'
    simp at h''
    exact ih hvalid' h''

-- Helper: every equality axiom instance formula is valid
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem isEqAxiomInstance_valid {L : Language} (hL : L.hasEquality = true)
    (A : FormulaN L)
    (h : isEqAxiomInstance hL A) :
    ∀ (M : Structure L) (s : Assignment M), formulaEvalN M A s := by
  exact eqAxiomInstanceValid hL A h

-- ===================================================================
-- Theorem 6.3.1 (helper): lkeNoEssentialCuts_of_sequentValid
-- ===================================================================

theorem lkeNoEssentialCuts_of_sequentValid {L : Language}
    (s : Sequent L) (hvalid : sequentValid s) :
    lkeProvableWithoutEssentialCuts s := by
-- BEGIN PROOF
  -- DEBT(Theorem 6.3.1 proof step: a valid sequent is LKe-provable without essential cuts; proof pending)
  sorry

-- ===================================================================
-- Theorem 6.3.1 (helper): lkeNoEssentialCuts_remove_eqRefl
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Removes FormulaN.eq_ t t from the antecedent of an
lkeProvableWithoutEssentialCuts proof. -/
theorem lkeNoEssentialCuts_remove_eqRefl {L : Language} (hL : L.hasEquality = true)
    (t : Term L) (Γ Δ Λ : List (FormulaN L))
    (ih : lkeProvableWithoutEssentialCuts
      (Sequent.mk (Γ ++ [FormulaN.eq_ hL t t] ++ Δ) Λ)) :
    lkeProvableWithoutEssentialCuts (Sequent.mk (Γ ++ Δ) Λ) := by
-- BEGIN PROOF
  apply lkeNoEssentialCuts_of_sequentValid
  obtain ⟨T, _⟩ := ih
  have hvalid_orig := lkeProofTree_valid T
  intro M s hAnte
  apply hvalid_orig M s
  intro F hF
  simp only [List.append_assoc, List.singleton_append] at hF
  rcases List.mem_append.mp hF with hFΓ | hFA
  · exact hAnte F (List.mem_append_left _ hFΓ)
  · rcases List.mem_cons.mp hFA with rfl | hFΔ
    · simp [formulaEvalN]
    · exact hAnte F (List.mem_append_right _ hFΔ)

-- ===================================================================
-- Theorem 6.3.1 (helper): lkeNoEssentialCuts_remove_eqAxiomInstance
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Removes an isEqAxiomInstance formula from the antecedent of an
lkeProvableWithoutEssentialCuts proof. -/
theorem lkeNoEssentialCuts_remove_eqAxiomInstance {L : Language}
    (hL : L.hasEquality = true)
    (A : FormulaN L) (hA : isEqAxiomInstance hL A)
    (Γ Δ Λ : List (FormulaN L))
    (ih : lkeProvableWithoutEssentialCuts (Sequent.mk (Γ ++ [A] ++ Δ) Λ)) :
    lkeProvableWithoutEssentialCuts (Sequent.mk (Γ ++ Δ) Λ) := by
-- BEGIN PROOF
  apply lkeNoEssentialCuts_of_sequentValid
  obtain ⟨T, _⟩ := ih
  have hvalid_orig := lkeProofTree_valid T
  have hA_valid := isEqAxiomInstance_valid hL A hA
  intro M s hAnte
  apply hvalid_orig M s
  intro F hF
  simp only [List.append_assoc, List.singleton_append] at hF
  rcases List.mem_append.mp hF with hFΓ | hFA
  · exact hAnte F (List.mem_append_left _ hFΓ)
  · rcases List.mem_cons.mp hFA with rfl | hFΔ
    · exact hA_valid M s
    · exact hAnte F (List.mem_append_right _ hFΔ)

-- ===================================================================
-- Theorem 6.3.1 (helper): lkeNoEssentialCuts_remove_axiom_prefix
-- ===================================================================



-- ===================================================================
-- Theorem 6.3.1 (helper): sequentProvableEq_lkeNoEssentialCuts
-- ===================================================================

/-- Every G=-provable sequent is LKe-provable without essential cuts. -/
theorem sequentProvableEq_lkeNoEssentialCuts {L : Language} (hL : L.hasEquality = true)
    (s : Sequent L) (h : sequentProvableEq hL s) :
    lkeProvableWithoutEssentialCuts s := by
-- BEGIN PROOF
  obtain ⟨T⟩ := h
  -- By induction on the indexed GEqProofTree T
  suffices hsuff : lkeProvableWithoutEssentialCuts s from hsuff
  induction T with
  | base g =>
    have hgprov : sequentProvableExt _ := ⟨g⟩
    exact folkCutFree_implies_lkeNoEssentialCuts _ (gProvable_folkCutFreeProvable _ hgprov)
  | axiom_ s hAx =>
    have hgprov : sequentProvableExt s := ⟨.axiom_ s hAx⟩
    exact folkCutFree_implies_lkeNoEssentialCuts _ (gProvable_folkCutFreeProvable _ hgprov)
  | onePremise rule sub ih =>
    -- The sub-tree proves the premise; the rule gives us the conclusion.
    -- The premise is lkeProvableWithoutEssentialCuts by IH.
    -- The conclusion follows because the rule is sound.
    -- Use semantic detour: lkeNoEssentialCuts_of_sequentValid.
    apply lkeNoEssentialCuts_of_sequentValid
    -- The G-rule preserves validity: the premise is valid (from IH via soundness)
    -- and the rule conclusion is valid.
    -- DEBT(Theorem 6.3.1 proof step: one-premise G= rule simulated in LKe without essential cuts; proof pending)
    sorry
  | twoPremise rule sub1 sub2 ih1 ih2 =>
    apply lkeNoEssentialCuts_of_sequentValid
    -- DEBT(Theorem 6.3.1 proof step: two-premise G= rule simulated in LKe without essential cuts; proof pending)
    sorry
  | eqRefl t Γ Δ sub ih =>
    simpa using lkeNoEssentialCuts_remove_eqRefl hL t Γ [] Δ (by simpa using ih)
  | eqFuncCong f ss ts Γ Δ sub ih =>
    simpa using lkeNoEssentialCuts_remove_eqAxiomInstance hL
      (eqCongruenceImplFunc L hL f ss ts)
      (Or.inr (Or.inl ⟨f, ss, ts, rfl⟩)) Γ [] Δ (by simpa using ih)
  | eqPredCong P ss ts Γ Δ sub ih =>
    simpa using lkeNoEssentialCuts_remove_eqAxiomInstance hL
      (eqCongruenceImplPred L hL P ss ts)
      (Or.inr (Or.inr (Or.inl ⟨P, ss, ts, rfl⟩))) Γ [] Δ (by simpa using ih)
  | eqGeneral axioms _hne haxioms Γ Δ sub ih =>
    have removeSuffix : ∀ (as : List (FormulaN L)),
        (∀ A ∈ as, isEqAxiomInstance hL A) →
        lkeProvableWithoutEssentialCuts (Sequent.mk (Γ ++ as) Δ) →
        lkeProvableWithoutEssentialCuts (Sequent.mk Γ Δ) := by
      intro as
      induction as with
      | nil => intro _ hp; simpa using hp
      | cons A rest ihas =>
        intro has hp
        have hp' := lkeNoEssentialCuts_remove_eqAxiomInstance hL A
          (has A List.mem_cons_self) Γ rest Δ (by simpa using hp)
        exact ihas (fun B hB => has B (List.mem_cons_of_mem _ hB)) hp'
    exact removeSuffix axioms haxioms ih

-- ===================================================================
-- Theorem 6.3.1 (normalized): geq_lke_equivalence
-- ===================================================================



-- ===================================================================
-- Theorem 6.3.1: gentzenHaupsatzLKe
-- ===================================================================

/-- Theorem 6.3.1 (companion, Gentzen Hauptsatz for LKe): Over a language
with equality, an end sequent satisfying the §6.1 sequent-level free/bound
convention is LKe-provable iff it is LKe-provable without essential cuts
(E-CUTFB). -/
@[blueprint "chap6__theorem_6_3_1"]
theorem gentzenHaupsatzLKe {L : Language} (hL : L.hasEquality = true)
    [Countable (Term L)]
    (seq : Sequent L) (hCross : crossNoFreeBound seq) :
    lkeProvable seq ↔ lkeProvableWithoutEssentialCuts seq 

/-- Theorem 6.4.2 (companion, LK_e note): An LK_e-provable sequent has an
LK_e proof whose cut formulae are all equations. The end sequent satisfies
the §6.1 sequent-level free/bound convention (E-CUTFB). This is the result
cited to Takeuti (1975) in the note closing §6.4.6. -/
@[attach_debt, blueprint "chap6__theorem_6_4_2"]
theorem lke_inessential_cut_elimination {L : Language} (hL : L.hasEquality = true)
    [Countable (Term L)] (seq : Sequent L) (hCross : crossNoFreeBound seq) :
    lkeProvable seq → ∃ T : LKeProofTree seq, lkeAllCutsEquational T 

end LCS.CutElim.LKe.Equivalence
end

