import LCS.FirstOrder.Equality.Soundness

section

namespace LCS.FirstOrder.Equality

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SemanticsN.Substitution (formulaSubstEvalDirectN)

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.SignedFormulae

open LCS.FirstOrder.Gentzen.Hintikka

open LCS.FirstOrder.Completeness

helper /-- Helper: if a formula is valid (true in all structures under all
assignments), then adding it to the antecedent of a sequent does not
change validity. The forward direction holds because the extra formula
is true anyway; the backward direction holds because removing a true
antecedent only weakens the hypothesis. -/
theorem addValidToAntecedent_iff {L : Language}
    (Γ Δ : List (FormulaN L)) (Λ : List (FormulaN L)) (A : FormulaN L)
    (hvalid : ∀ (M : Structure L) (s : Assignment M), formulaEvalN M A s) :
    sequentValid (Sequent.mk (Γ ++ Δ) Λ) ↔
    sequentValid (Sequent.mk (Γ ++ [A] ++ Δ) Λ) := by
-- BEGIN PROOF
  constructor
  · -- Forward: valid without A → valid with A (weakening)
    intro h M s hant
    exact h M s (fun F hF => by
      rcases memcat_cases hF with hΓ | hΔ
      · exact hant F (mem1_left hΓ)
      · exact hant F (mem1_right hΔ))
  · -- Backward: valid with A → valid without A
    intro h M s hant
    exact h M s (fun F hF => by
      rcases mem1_cases hF with h1 | rfl | h3
      · exact hant F (memcat_left h1)
      · exact hvalid M s
      · exact hant F (memcat_right h3))

helper /-- Helper: adding multiple valid formulas (appended) to the
antecedent does not change validity. -/
theorem addValidListToAntecedent_iff {L : Language}
    (axioms : List (FormulaN L)) (ant succ : List (FormulaN L))
    (hvalid : ∀ A ∈ axioms, ∀ (M : Structure L) (s : Assignment M),
      formulaEvalN M A s) :
    sequentValid (Sequent.mk ant succ) ↔
    sequentValid (Sequent.mk (ant ++ axioms) succ) := by
-- BEGIN PROOF
  constructor
  · intro h M s hant
    exact h M s (fun F hF => hant F (List.mem_append_left _ hF))
  · intro h M s hant
    exact h M s (fun F hF => by
      rcases List.mem_append.mp hF with horiginal | hax
      · exact hant F horiginal
      · exact hvalid F hax M s)

helper /-- Helper: adding a valid formula to the antecedent does not change
falsifiability in a specific model. -/
theorem addValidToAntecedent_falsifiableIn_iff {L : Language}
    (M : Structure L)
    (Γ Δ : List (FormulaN L)) (Λ : List (FormulaN L)) (A : FormulaN L)
    (hvalid : ∀ (s : Assignment M), formulaEvalN M A s) :
    sequentFalsifiableIn M (Sequent.mk (Γ ++ Δ) Λ) ↔
    sequentFalsifiableIn M (Sequent.mk (Γ ++ [A] ++ Δ) Λ) := by
-- BEGIN PROOF
  constructor
  · intro ⟨s, hant, hsucc⟩
    exact ⟨s, fun F hF => by
      rcases mem1_cases hF with h1 | rfl | h3
      · exact hant F (memcat_left h1)
      · exact hvalid s
      · exact hant F (memcat_right h3),
    hsucc⟩
  · intro ⟨s, hant, hsucc⟩
    exact ⟨s, fun F hF => by
      rcases memcat_cases hF with hΓ | hΔ
      · exact hant F (mem1_left hΓ)
      · exact hant F (mem1_right hΔ),
    hsucc⟩

helper /-- Helper: adding multiple valid formulas (appended) to the
antecedent does not change falsifiability in a specific model. -/
theorem addValidListToAntecedent_falsifiableIn_iff {L : Language}
    (M : Structure L)
    (axioms : List (FormulaN L)) (ant succ : List (FormulaN L))
    (hvalid : ∀ A ∈ axioms, ∀ (s : Assignment M),
      formulaEvalN M A s) :
    sequentFalsifiableIn M (Sequent.mk ant succ) ↔
    sequentFalsifiableIn M (Sequent.mk (ant ++ axioms) succ) := by
-- BEGIN PROOF
  constructor
  · intro ⟨s, hant, hsucc⟩
    exact ⟨s, fun F hF => by
      rcases List.mem_append.mp hF with horiginal | hax
      · exact hant F horiginal
      · exact hvalid F hax s,
    hsucc⟩
  · intro ⟨s, hant, hsucc⟩
    exact ⟨s, fun F hF => hant F (List.mem_append_left _ hF), hsucc⟩

proof_of eqRuleFalsificationIff := by
  have hsingle (A : FormulaN L)
      (hvalid : ∀ (M : Structure L) (s : Assignment M), formulaEvalN M A s) :
      sequentFalsifiable (Sequent.mk (Γ ++ [A]) Δ) ↔
        sequentFalsifiable (Sequent.mk Γ Δ) := by
    change (∃ M, sequentFalsifiableIn M (Sequent.mk (Γ ++ [A]) Δ)) ↔
      (∃ M, sequentFalsifiableIn M (Sequent.mk Γ Δ))
    apply exists_congr
    intro M
    simpa only [List.append_nil] using
      (addValidToAntecedent_falsifiableIn_iff M Γ [] Δ A (hvalid M)).symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact hsingle _ (eqReflValid hL t)
  · intro f ss ts
    exact hsingle _ (eqFuncCongValid hL f ss ts)
  · intro P ss ts
    exact hsingle _ (eqPredCongValid hL P ss ts)
  · intro s1 s2 t1 t2
    exact hsingle _ (eqEqCongValid hL s1 s2 t1 t2)
  · intro axioms _hne haxioms
    change (∃ M, sequentFalsifiableIn M (Sequent.mk (Γ ++ axioms) Δ)) ↔
      (∃ M, sequentFalsifiableIn M (Sequent.mk Γ Δ))
    apply exists_congr
    intro M
    exact (addValidListToAntecedent_falsifiableIn_iff M axioms Γ Δ
      (fun A hA s => eqAxiomInstanceValid hL A (haxioms A hA) M s)).symm

proof_of soundnessGEq := 
  -- BEGIN PROOF
  let rec
    /-- Helper: every GEq proof tree has a valid conclusion. -/
    eqTreeValid : ∀ (s : Sequent L), GEqProofTree hL s →
        sequentValid s
      | _, .base g => soundnessG_Ext _ ⟨g⟩
      | _, .axiom_ s hAx => by
          intro M as hant
          obtain ⟨A, hA_ant, hA_suc⟩ := hAx
          exact ⟨A, hA_suc, hant A hA_ant⟩
      | _, .onePremise rule sub =>
          (ruleValidityIff1Ext rule).mpr (eqTreeValid _ sub)
      | _, .twoPremise rule sub1 sub2 =>
          (ruleValidityIff2Ext rule).mpr
            ⟨eqTreeValid _ sub1, eqTreeValid _ sub2⟩
      | _, .eqRefl t Γ Δ sub =>
          by
            have he := addValidToAntecedent_iff Γ [] Δ _ (eqReflValid hL t)
            simp only [List.append_nil] at he
            exact he.mpr (eqTreeValid _ sub)
      | _, .eqFuncCong f ss ts Γ Δ sub =>
          by
            have he := addValidToAntecedent_iff Γ [] Δ _ (eqFuncCongValid hL f ss ts)
            simp only [List.append_nil] at he
            exact he.mpr (eqTreeValid _ sub)
      | _, .eqPredCong P ss ts Γ Δ sub =>
          by
            have he := addValidToAntecedent_iff Γ [] Δ _ (eqPredCongValid hL P ss ts)
            simp only [List.append_nil] at he
            exact he.mpr (eqTreeValid _ sub)
      | _, .eqGeneral axioms hne haxioms Γ Δ sub =>
          (addValidListToAntecedent_iff _ _ _
            (fun A hA M s => eqAxiomInstanceValid hL A (haxioms A hA) M s)).mpr
            (eqTreeValid _ sub)
  by
    obtain ⟨tree⟩ := h
    exact eqTreeValid seq tree

end LCS.FirstOrder.Equality

end
