import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.CutElim.CompletenessBridge
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Semantics.Subformulae

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
-- Semantic bridge infrastructure: finite-support language
-- ===================================================================
-- retained: used by LCS.CutElim.Interpolation.Equality.Support, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeTermFunOccurs {L : Language} (f : L.funSymbols) :
    Term L → Prop
  | .var _ => False
  | .const _ => False
  | .func g ts => f = g ∨ ∃ i, validBridgeTermFunOccurs f (ts i)

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity
def validBridgeTermConstOccurs {L : Language} (c : L.constSymbols) :
    Term L → Prop
  | .var _ => False
  | .const d => c = d
  | .func _ ts => ∃ i, validBridgeTermConstOccurs c (ts i)

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.Interpolation.Equality.Support, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeFormulaFunOccurs {L : Language} (f : L.funSymbols) :
    FormulaN L → Prop
  | .predN _ ts => ∃ i, validBridgeTermFunOccurs f (ts i)
  | .eq_ _ t₁ t₂ =>
      validBridgeTermFunOccurs f t₁ ∨ validBridgeTermFunOccurs f t₂
  | .neg A => validBridgeFormulaFunOccurs f A
  | .conj A B | .disj A B | .impl A B =>
      validBridgeFormulaFunOccurs f A ∨ validBridgeFormulaFunOccurs f B
  | .all _ A | .ex _ A => validBridgeFormulaFunOccurs f A

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeFormulaConstOccurs {L : Language} (c : L.constSymbols) :
    FormulaN L → Prop
  | .predN _ ts => ∃ i, validBridgeTermConstOccurs c (ts i)
  | .eq_ _ t₁ t₂ =>
      validBridgeTermConstOccurs c t₁ ∨ validBridgeTermConstOccurs c t₂
  | .neg A => validBridgeFormulaConstOccurs c A
  | .conj A B | .disj A B | .impl A B =>
      validBridgeFormulaConstOccurs c A ∨ validBridgeFormulaConstOccurs c B
  | .all _ A | .ex _ A => validBridgeFormulaConstOccurs c A

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.Interpolation.Equality.Support, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeFormulaPredOccurs {L : Language} (P : L.predSymbols) :
    FormulaN L → Prop
  | .predN Q _ => P = Q
  | .eq_ _ _ _ => False
  | .neg A => validBridgeFormulaPredOccurs P A
  | .conj A B | .disj A B | .impl A B =>
      validBridgeFormulaPredOccurs P A ∨ validBridgeFormulaPredOccurs P B
  | .all _ A | .ex _ A => validBridgeFormulaPredOccurs P A

-- retained: used by LCS.CutElim.Interpolation.Equality.Support
def validBridgeTermFunSymbols {L : Language} : Term L → List L.funSymbols
  | .var _ => []
  | .const _ => []
  | .func f ts =>
      f :: (List.ofFn (fun i => validBridgeTermFunSymbols (ts i))).flatten

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeTermConstSymbols {L : Language} :
    Term L → List L.constSymbols
  | .var _ => []
  | .const c => [c]
  | .func _ ts =>
      (List.ofFn (fun i => validBridgeTermConstSymbols (ts i))).flatten

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.Interpolation.Equality.Support, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeFormulaFunSymbols {L : Language} :
    FormulaN L → List L.funSymbols
  | .predN _ ts =>
      (List.ofFn (fun i => validBridgeTermFunSymbols (ts i))).flatten
  | .eq_ _ t₁ t₂ =>
      validBridgeTermFunSymbols t₁ ++ validBridgeTermFunSymbols t₂
  | .neg A => validBridgeFormulaFunSymbols A
  | .conj A B | .disj A B | .impl A B =>
      validBridgeFormulaFunSymbols A ++ validBridgeFormulaFunSymbols B
  | .all _ A | .ex _ A => validBridgeFormulaFunSymbols A

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeFormulaConstSymbols {L : Language} :
    FormulaN L → List L.constSymbols
  | .predN _ ts =>
      (List.ofFn (fun i => validBridgeTermConstSymbols (ts i))).flatten
  | .eq_ _ t₁ t₂ =>
      validBridgeTermConstSymbols t₁ ++ validBridgeTermConstSymbols t₂
  | .neg A => validBridgeFormulaConstSymbols A
  | .conj A B | .disj A B | .impl A B =>
      validBridgeFormulaConstSymbols A ++ validBridgeFormulaConstSymbols B
  | .all _ A | .ex _ A => validBridgeFormulaConstSymbols A

-- retained: used by LCS.CutElim.Interpolation.Equality.Support, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeFormulaPredSymbols {L : Language} :
    FormulaN L → List L.predSymbols
  | .predN P _ => [P]
  | .eq_ _ _ _ => []
  | .neg A => validBridgeFormulaPredSymbols A
  | .conj A B | .disj A B | .impl A B =>
      validBridgeFormulaPredSymbols A ++ validBridgeFormulaPredSymbols B
  | .all _ A | .ex _ A => validBridgeFormulaPredSymbols A

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity
theorem validBridge_mem_flatten_ofFn {α : Type} {n : Nat}
    (xs : Fin n → List α) (i : Fin n) {a : α} (ha : a ∈ xs i) :
    a ∈ (List.ofFn xs).flatten := by
  apply List.mem_flatten.mpr
  exact ⟨xs i, by simp, ha⟩

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity
theorem validBridgeTermFunOccurs_mem {L : Language}
    {f : L.funSymbols} {t : Term L}
    (h : validBridgeTermFunOccurs f t) :
    f ∈ validBridgeTermFunSymbols t := by
  induction t with
  | var _ => exact h.elim
  | const _ => exact h.elim
  | func g ts ih =>
      simp only [validBridgeTermFunOccurs] at h
      simp only [validBridgeTermFunSymbols, List.mem_cons]
      rcases h with rfl | ⟨i, hi⟩
      · exact Or.inl rfl
      · exact Or.inr (validBridge_mem_flatten_ofFn
          (fun j => validBridgeTermFunSymbols (ts j)) i (ih i hi))

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity
theorem validBridgeTermConstOccurs_mem {L : Language}
    {c : L.constSymbols} {t : Term L}
    (h : validBridgeTermConstOccurs c t) :
    c ∈ validBridgeTermConstSymbols t := by
  induction t with
  | var _ => exact h.elim
  | const d =>
      simpa [validBridgeTermConstOccurs, validBridgeTermConstSymbols] using h
  | func f ts ih =>
      simp only [validBridgeTermConstOccurs] at h
      obtain ⟨i, hi⟩ := h
      exact validBridge_mem_flatten_ofFn
        (fun j => validBridgeTermConstSymbols (ts j)) i (ih i hi)

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity
theorem validBridgeFormulaFunOccurs_mem {L : Language}
    {f : L.funSymbols} {A : FormulaN L}
    (h : validBridgeFormulaFunOccurs f A) :
    f ∈ validBridgeFormulaFunSymbols A := by
  induction A with
  | predN P ts =>
      obtain ⟨i, hi⟩ := h
      exact validBridge_mem_flatten_ofFn
        (fun j => validBridgeTermFunSymbols (ts j)) i
        (validBridgeTermFunOccurs_mem hi)
  | eq_ hL t₁ t₂ =>
      rcases h with h | h
      · exact List.mem_append_left _ (validBridgeTermFunOccurs_mem h)
      · exact List.mem_append_right _ (validBridgeTermFunOccurs_mem h)
  | neg A ih => exact ih h
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      rcases h with h | h
      · exact List.mem_append_left _ (ihA h)
      · exact List.mem_append_right _ (ihB h)
  | all x A ih | ex x A ih => exact ih h

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity
theorem validBridgeFormulaConstOccurs_mem {L : Language}
    {c : L.constSymbols} {A : FormulaN L}
    (h : validBridgeFormulaConstOccurs c A) :
    c ∈ validBridgeFormulaConstSymbols A := by
  induction A with
  | predN P ts =>
      obtain ⟨i, hi⟩ := h
      exact validBridge_mem_flatten_ofFn
        (fun j => validBridgeTermConstSymbols (ts j)) i
        (validBridgeTermConstOccurs_mem hi)
  | eq_ hL t₁ t₂ =>
      rcases h with h | h
      · exact List.mem_append_left _ (validBridgeTermConstOccurs_mem h)
      · exact List.mem_append_right _ (validBridgeTermConstOccurs_mem h)
  | neg A ih => exact ih h
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      rcases h with h | h
      · exact List.mem_append_left _ (ihA h)
      · exact List.mem_append_right _ (ihB h)
  | all x A ih | ex x A ih => exact ih h

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity
theorem validBridgeFormulaPredOccurs_mem {L : Language}
    {P : L.predSymbols} {A : FormulaN L}
    (h : validBridgeFormulaPredOccurs P A) :
    P ∈ validBridgeFormulaPredSymbols A := by
  induction A with
  | predN Q ts =>
      simpa [validBridgeFormulaPredOccurs, validBridgeFormulaPredSymbols] using h
  | eq_ hL t₁ t₂ => exact h.elim
  | neg A ih => exact ih h
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      rcases h with h | h
      · exact List.mem_append_left _ (ihA h)
      · exact List.mem_append_right _ (ihB h)
  | all x A ih | ex x A ih => exact ih h

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.Interpolation.Equality.Support, LCS.CutElim.LKe.Equivalence.Validity
/-- The sublanguage consisting exactly of the symbols occurring in a
single formula. -/
def ValidBridgeSupportLanguage {L : Language} (F : FormulaN L) :
    Language where
  funSymbols := {f // f ∈ validBridgeFormulaFunSymbols F}
  funArity := fun f => L.funArity f.1
  constSymbols := {c // c ∈ validBridgeFormulaConstSymbols F}
  predSymbols := {P // P ∈ validBridgeFormulaPredSymbols F}
  predArity := fun P => L.predArity P.1
  hasEquality := L.hasEquality

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity
def validBridgeRestrictTerm {L : Language} (F : FormulaN L) :
    (t : Term L) →
    (∀ f, validBridgeTermFunOccurs f t →
      validBridgeFormulaFunOccurs f F) →
    (∀ c, validBridgeTermConstOccurs c t →
      validBridgeFormulaConstOccurs c F) →
    Term (ValidBridgeSupportLanguage F)
  | .var n, _, _ => .var n
  | .const c, _, hc =>
      .const ⟨c, validBridgeFormulaConstOccurs_mem
        (hc c (by simp [validBridgeTermConstOccurs]))⟩
  | .func f ts, hf, hc =>
      .func
        ⟨f, validBridgeFormulaFunOccurs_mem
          (hf f (Or.inl rfl))⟩
        (fun i => validBridgeRestrictTerm F (ts i)
          (fun g hg => hf g (Or.inr ⟨i, hg⟩))
          (fun c hc' => hc c ⟨i, hc'⟩))

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeRestrictFormula {L : Language} (F : FormulaN L) :
    (A : FormulaN L) →
    (∀ f, validBridgeFormulaFunOccurs f A →
      validBridgeFormulaFunOccurs f F) →
    (∀ c, validBridgeFormulaConstOccurs c A →
      validBridgeFormulaConstOccurs c F) →
    (∀ P, validBridgeFormulaPredOccurs P A →
      validBridgeFormulaPredOccurs P F) →
    FormulaN (ValidBridgeSupportLanguage F)
  | .predN P ts, hf, hc, hp =>
      .predN
        ⟨P, validBridgeFormulaPredOccurs_mem
          (hp P (by simp [validBridgeFormulaPredOccurs]))⟩
        (fun i => validBridgeRestrictTerm F (ts i)
          (fun f h => hf f ⟨i, h⟩)
          (fun c h => hc c ⟨i, h⟩))
  | .eq_ hL t₁ t₂, hf, hc, _ =>
      .eq_ hL
        (validBridgeRestrictTerm F t₁
          (fun f h => hf f (Or.inl h))
          (fun c h => hc c (Or.inl h)))
        (validBridgeRestrictTerm F t₂
          (fun f h => hf f (Or.inr h))
          (fun c h => hc c (Or.inr h)))
  | .neg A, hf, hc, hp =>
      .neg (validBridgeRestrictFormula F A hf hc hp)
  | .conj A B, hf, hc, hp =>
      .conj
        (validBridgeRestrictFormula F A
          (fun f h => hf f (Or.inl h))
          (fun c h => hc c (Or.inl h))
          (fun P h => hp P (Or.inl h)))
        (validBridgeRestrictFormula F B
          (fun f h => hf f (Or.inr h))
          (fun c h => hc c (Or.inr h))
          (fun P h => hp P (Or.inr h)))
  | .disj A B, hf, hc, hp =>
      .disj
        (validBridgeRestrictFormula F A
          (fun f h => hf f (Or.inl h))
          (fun c h => hc c (Or.inl h))
          (fun P h => hp P (Or.inl h)))
        (validBridgeRestrictFormula F B
          (fun f h => hf f (Or.inr h))
          (fun c h => hc c (Or.inr h))
          (fun P h => hp P (Or.inr h)))
  | .impl A B, hf, hc, hp =>
      .impl
        (validBridgeRestrictFormula F A
          (fun f h => hf f (Or.inl h))
          (fun c h => hc c (Or.inl h))
          (fun P h => hp P (Or.inl h)))
        (validBridgeRestrictFormula F B
          (fun f h => hf f (Or.inr h))
          (fun c h => hc c (Or.inr h))
          (fun P h => hp P (Or.inr h)))
  | .all x A, hf, hc, hp =>
      .all x (validBridgeRestrictFormula F A hf hc hp)
  | .ex x A, hf, hc, hp =>
      .ex x (validBridgeRestrictFormula F A hf hc hp)

-- retained: used by LCS.CutElim.Interpolation.Equality.Support, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeRestrictSelf {L : Language} (F : FormulaN L) :
    FormulaN (ValidBridgeSupportLanguage F) :=
  validBridgeRestrictFormula F F
    (fun _ h => h) (fun _ h => h) (fun _ h => h)

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity
def validBridgeLiftTerm {L : Language} (F : FormulaN L) :
    Term (ValidBridgeSupportLanguage F) → Term L
  | .var n => .var n
  | .const c => .const c.1
  | .func f ts => .func f.1 (fun i => validBridgeLiftTerm F (ts i))

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.Interpolation.Equality.Support, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeLiftFormula {L : Language} (F : FormulaN L) :
    FormulaN (ValidBridgeSupportLanguage F) → FormulaN L
  | .predN P ts =>
      .predN P.1 (fun i => validBridgeLiftTerm F (ts i))
  | .eq_ hL t₁ t₂ =>
      .eq_ hL (validBridgeLiftTerm F t₁) (validBridgeLiftTerm F t₂)
  | .neg A => .neg (validBridgeLiftFormula F A)
  | .conj A B =>
      .conj (validBridgeLiftFormula F A) (validBridgeLiftFormula F B)
  | .disj A B =>
      .disj (validBridgeLiftFormula F A) (validBridgeLiftFormula F B)
  | .impl A B =>
      .impl (validBridgeLiftFormula F A) (validBridgeLiftFormula F B)
  | .all x A => .all x (validBridgeLiftFormula F A)
  | .ex x A => .ex x (validBridgeLiftFormula F A)

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

end LCS.CutElim.LKe.Equivalence
end
