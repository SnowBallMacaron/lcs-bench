import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.CutElim.CompletenessBridge
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.LKe.Equivalence.SemanticBridge.SupportLanguage

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

end LCS.CutElim.LKe.Equivalence
end
