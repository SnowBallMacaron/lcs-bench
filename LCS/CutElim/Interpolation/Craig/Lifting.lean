import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.Craig.FreshBottom

section
namespace LCS.CutElim.Interpolation
open Classical
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen.Hintikka
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
namespace CraigFreshBot

-- ===================================================================
-- Internal Craig helper: lifting indexed LK derivations
-- ===================================================================

/-- Lifting preserves the exact axiom sequent, rather than merely producing
an extension-language axiom with an unrelated conclusion. -/
theorem freshLift_isFOLKAxiom {L : Language} (s : Sequent L)
    (h : isFOLKAxiom s) :
    isFOLKAxiom (freshLiftSequent s) := by
  rcases h with ⟨A, hΓ, hΔ⟩
  refine ⟨freshLiftFormula A, ?_, ?_⟩
  · simp only [freshLiftSequent, hΓ, freshLiftList,
      List.map_cons, List.map_nil]
  · simp only [freshLiftSequent, hΔ, freshLiftList,
      List.map_cons, List.map_nil]

section
variable (L : Language)

def freshLift_allRight
    (y : Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfresh : ∀ (F :
      FormulaN L), F ∈ (Γ) ++ (Δ ++ [FormulaN.all x A]) → ¬y ∈ formulaFVN F) (hfreeFor : isFreeForN (Term.var
      y) x A)
    : FOLKStep1 (freshLiftSequent (Sequent.mk (Γ) (Δ ++ [formulaSubstN A (Term.var y) x]))) (freshLiftSequent
      (Sequent.mk (Γ) (Δ ++ [FormulaN.all x A]))) := by
  have hfresh' : ∀ F ∈ (Sequent.mk (freshLiftList Γ) (freshLiftList Δ ++
              [FormulaN.all x (freshLiftFormula A)])).antecedent ++
          (Sequent.mk (freshLiftList Γ) (freshLiftList Δ ++ [FormulaN.all x (freshLiftFormula A)])).succedent,
        y ∉ formulaFVN F := by
    intro F hF
    have hF' : F ∈ freshLiftList ((Sequent.mk Γ (Δ ++ [FormulaN.all x A])).antecedent ++ (Sequent.mk Γ
            (Δ ++ [FormulaN.all x A])).succedent) := by
      simpa only [freshLiftList, freshLiftFormula, List.map_append, List.map_cons, List.map_nil] using hF
    simp only [freshLiftList] at hF'
    rcases List.mem_map.mp hF' with ⟨G, hG, rfl⟩
    simpa only [freshLiftFormula_fv] using hfresh G hG
  have hfreeFor' : isFreeForN (Term.var y : Term (FreshBotLanguage L)) x (freshLiftFormula A) := by
    simpa only [freshLiftTerm] using (freshLiftFormula_isFreeFor (Term.var y) x A).mpr hfreeFor
  simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
    freshLiftFormula_subst, List.map_append, List.map_cons,
    List.map_nil, freshLiftTerm] using
    (FOLKStep1.allRight y x (freshLiftFormula A) (freshLiftList Γ) (freshLiftList Δ) hfresh' hfreeFor')

def freshLift_exLeft
    (y : Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfresh : ∀ (F :
      FormulaN L), F ∈ (FormulaN.ex x A :: Γ) ++ (Δ) → ¬y ∈ formulaFVN F) (hfreeFor : isFreeForN (Term.var y)
      x A)
    : FOLKStep1 (freshLiftSequent (Sequent.mk (formulaSubstN A (Term.var y) x :: Γ) (Δ))) (freshLiftSequent
      (Sequent.mk (FormulaN.ex x A :: Γ) (Δ))) := by
  have hfresh' : ∀ F ∈ (Sequent.mk (FormulaN.ex x (freshLiftFormula A) :: freshLiftList Γ)
            (freshLiftList Δ)).antecedent ++
          (Sequent.mk (FormulaN.ex x (freshLiftFormula A) :: freshLiftList Γ) (freshLiftList Δ)).succedent,
        y ∉ formulaFVN F := by
    intro F hF
    have hF' : F ∈ freshLiftList ((Sequent.mk (FormulaN.ex x A :: Γ) Δ).antecedent ++
           (Sequent.mk (FormulaN.ex x A :: Γ) Δ).succedent) := by
      simpa only [freshLiftList, freshLiftFormula, List.map_append, List.map_cons] using hF
    simp only [freshLiftList] at hF'
    rcases List.mem_map.mp hF' with ⟨G, hG, rfl⟩
    simpa only [freshLiftFormula_fv] using hfresh G hG
  have hfreeFor' : isFreeForN (Term.var y : Term (FreshBotLanguage L)) x (freshLiftFormula A) := by
    simpa only [freshLiftTerm] using (freshLiftFormula_isFreeFor (Term.var y) x A).mpr hfreeFor
  simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
    freshLiftFormula_subst, List.map_cons, freshLiftTerm] using
    (FOLKStep1.exLeft y x (freshLiftFormula A) (freshLiftList Γ) (freshLiftList Δ) hfresh' hfreeFor')

end

/-- Lift every indexed one-premise LK rule to the fresh-bottom language.
The premise and conclusion indices are exactly the pointwise lifts of the
source indices. -/
def freshLift_folkStep1 {L : Language} {prem conc : Sequent L}
    (rule : FOLKStep1 prem conc) :
    FOLKStep1 (freshLiftSequent prem) (freshLiftSequent conc) := by
  cases rule with
  | weakenLeft A Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList,
      List.map_cons] using
      (FOLKStep1.weakenLeft (freshLiftFormula A)
        (freshLiftList Γ) (freshLiftList Δ))
  | weakenRight A Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList, List.map_append,
      List.map_cons, List.map_nil] using
      (FOLKStep1.weakenRight (freshLiftFormula A)
        (freshLiftList Γ) (freshLiftList Δ))
  | contractLeft A Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList,
      List.map_cons] using
      (FOLKStep1.contractLeft (freshLiftFormula A)
        (freshLiftList Γ) (freshLiftList Δ))
  | contractRight A Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList, List.map_append,
      List.map_cons, List.map_nil] using
      (FOLKStep1.contractRight (freshLiftFormula A)
        (freshLiftList Γ) (freshLiftList Δ))
  | exchangeLeft Γ A B Δ Λ =>
    simpa only [freshLiftSequent, freshLiftList, List.map_append,
      List.map_cons, List.map_nil] using
      (FOLKStep1.exchangeLeft (freshLiftList Γ)
        (freshLiftFormula A) (freshLiftFormula B)
        (freshLiftList Δ) (freshLiftList Λ))
  | exchangeRight Γ Δ A B Λ =>
    simpa only [freshLiftSequent, freshLiftList, List.map_append,
      List.map_cons, List.map_nil] using
      (FOLKStep1.exchangeRight (freshLiftList Γ) (freshLiftList Δ)
        (freshLiftFormula A) (freshLiftFormula B) (freshLiftList Λ))
  | andLeftL A B Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
      List.map_cons] using
      (FOLKStep1.andLeftL (freshLiftFormula A) (freshLiftFormula B)
        (freshLiftList Γ) (freshLiftList Δ))
  | andLeftR A B Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
      List.map_cons] using
      (FOLKStep1.andLeftR (freshLiftFormula A) (freshLiftFormula B)
        (freshLiftList Γ) (freshLiftList Δ))
  | orRightL A B Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
      List.map_append, List.map_cons, List.map_nil] using
      (FOLKStep1.orRightL (freshLiftFormula A) (freshLiftFormula B)
        (freshLiftList Γ) (freshLiftList Δ))
  | orRightR A B Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
      List.map_append, List.map_cons, List.map_nil] using
      (FOLKStep1.orRightR (freshLiftFormula A) (freshLiftFormula B)
        (freshLiftList Γ) (freshLiftList Δ))
  | implRight A B Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
      List.map_append, List.map_cons, List.map_nil] using
      (FOLKStep1.implRight (freshLiftFormula A) (freshLiftFormula B)
        (freshLiftList Γ) (freshLiftList Δ))
  | negLeft A Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
      List.map_append, List.map_cons, List.map_nil] using
      (FOLKStep1.negLeft (freshLiftFormula A)
        (freshLiftList Γ) (freshLiftList Δ))
  | negRight A Γ Δ =>
    simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
      List.map_append, List.map_cons, List.map_nil] using
      (FOLKStep1.negRight (freshLiftFormula A)
        (freshLiftList Γ) (freshLiftList Δ))
  | allLeft t x A Γ Δ hfree =>
    have hfree' :
        isFreeForN (freshLiftTerm t) x (freshLiftFormula A) :=
      (freshLiftFormula_isFreeFor t x A).mpr hfree
    simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
      freshLiftFormula_subst, List.map_cons] using
      (FOLKStep1.allLeft (freshLiftTerm t) x (freshLiftFormula A)
        (freshLiftList Γ) (freshLiftList Δ) hfree')
  | allRight y x A Γ Δ hfresh hfreeFor =>
    exact freshLift_allRight L y x A Γ Δ hfresh hfreeFor
  | exLeft y x A Γ Δ hfresh hfreeFor =>
    exact freshLift_exLeft L y x A Γ Δ hfresh hfreeFor
  | exRight t x A Γ Δ hfree =>
    have hfree' :
        isFreeForN (freshLiftTerm t) x (freshLiftFormula A) :=
      (freshLiftFormula_isFreeFor t x A).mpr hfree
    simpa only [freshLiftSequent, freshLiftList, freshLiftFormula,
      freshLiftFormula_subst, List.map_append, List.map_cons,
      List.map_nil] using
      (FOLKStep1.exRight (freshLiftTerm t) x (freshLiftFormula A)
        (freshLiftList Γ) (freshLiftList Δ) hfree')

def reindexFOLKStep2 {L : Language}
    {prem₁ prem₂ conc prem₁' prem₂' conc' : Sequent L}
    (rule : FOLKStep2 prem₁ prem₂ conc)
    (hprem₁ : prem₁ = prem₁') (hprem₂ : prem₂ = prem₂')
    (hconc : conc = conc') :
    FOLKStep2 prem₁' prem₂' conc' := by
  cases hprem₁
  cases hprem₂
  cases hconc
  exact rule

/-- Lift every indexed two-premise LK rule to the fresh-bottom language,
including cut. All three sequent indices are translated exactly. -/
def freshLift_folkStep2 {L : Language}
    {prem₁ prem₂ conc : Sequent L}
    (rule : FOLKStep2 prem₁ prem₂ conc) :
    FOLKStep2 (freshLiftSequent prem₁) (freshLiftSequent prem₂)
      (freshLiftSequent conc) := by
  cases rule with
  | cut A Γ Δ Λ Θ =>
    let lifted := FOLKStep2.cut (freshLiftFormula A)
      (freshLiftList Γ) (freshLiftList Δ)
      (freshLiftList Λ) (freshLiftList Θ)
    exact reindexFOLKStep2 lifted
      (by simp only [freshLiftSequent, freshLiftList, List.map_append,
        List.map_cons, List.map_nil])
      (by simp only [freshLiftSequent, freshLiftList, List.map_cons])
      (by simp only [freshLiftSequent, freshLiftList, List.map_append])
  | andRight A B Γ Δ =>
    let lifted := FOLKStep2.andRight
      (freshLiftFormula A) (freshLiftFormula B)
      (freshLiftList Γ) (freshLiftList Δ)
    exact reindexFOLKStep2 lifted
      (by simp only [freshLiftSequent, freshLiftList, List.map_append,
        List.map_cons, List.map_nil])
      (by simp only [freshLiftSequent, freshLiftList, List.map_append,
        List.map_cons, List.map_nil])
      (by simp only [freshLiftSequent, freshLiftList, freshLiftFormula,
        List.map_append, List.map_cons, List.map_nil])
  | orLeft A B Γ Δ =>
    let lifted := FOLKStep2.orLeft
      (freshLiftFormula A) (freshLiftFormula B)
      (freshLiftList Γ) (freshLiftList Δ)
    exact reindexFOLKStep2 lifted
      (by simp only [freshLiftSequent, freshLiftList, List.map_cons])
      (by simp only [freshLiftSequent, freshLiftList, List.map_cons])
      (by simp only [freshLiftSequent, freshLiftList, freshLiftFormula,
        List.map_cons])
  | implLeft A B Γ Δ Λ Θ =>
    let lifted := FOLKStep2.implLeft
      (freshLiftFormula A) (freshLiftFormula B)
      (freshLiftList Γ) (freshLiftList Δ)
      (freshLiftList Λ) (freshLiftList Θ)
    exact reindexFOLKStep2 lifted
      (by simp only [freshLiftSequent, freshLiftList, List.map_append,
        List.map_cons, List.map_nil])
      (by simp only [freshLiftSequent, freshLiftList, List.map_cons])
      (by simp only [freshLiftSequent, freshLiftList, freshLiftFormula,
        List.map_append, List.map_cons])

/-- Structural lifting of indexed LK proof trees. Every recursive constructor
uses the correspondingly lifted indexed rule, so the result has exactly the
lifted source conclusion. -/
def freshLift_folkProofTree {L : Language} :
    {s : Sequent L} → FOLKProofTree s →
      FOLKProofTree (freshLiftSequent s)
  | _, .axiom_ s h =>
      .axiom_ (freshLiftSequent s) (freshLift_isFOLKAxiom s h)
  | _, .onePremise rule t =>
      .onePremise (freshLift_folkStep1 rule)
        (freshLift_folkProofTree t)
  | _, .twoPremise rule t₁ t₂ =>
      .twoPremise (freshLift_folkStep2 rule)
        (freshLift_folkProofTree t₁) (freshLift_folkProofTree t₂)

end CraigFreshBot
end LCS.CutElim.Interpolation
end
