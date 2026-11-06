import LCS.Herbrand.PrenexForm.Example

namespace LCS.Herbrand.PrenexForm
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Equivalence
open LCS.FirstOrder.Semantics.Subformulae

proof_of exPrenex_equiv_7_2_1 := by
  -- BEGIN PROOF
    intro M s
    change
      (formulaEvalN M exampleFormula_7_2_1 s →
        formulaEvalN M exPrenexFinal_7_2_1 s) ∧
      (formulaEvalN M exPrenexFinal_7_2_1 s →
        formulaEvalN M exampleFormula_7_2_1 s)
    have evalVec2 (t : Assignment M) (i j : Nat) :
        (fun k =>
          termEval M t (vec2 (Term.var i) (Term.var j) k)) =
          vec2 (t i) (t j) := by
      funext ⟨k, hk⟩
      match k, hk with
      | 0, _ => rfl
      | 1, _ => rfl
    let p : M.carrier → Prop := fun a =>
      M.interpPred ExPred_7_2_1.P (fun _ => a)
    let q : M.carrier → Prop := fun a =>
      M.interpPred ExPred_7_2_1.Q (fun _ => a)
    let r : M.carrier → M.carrier → Prop := fun a b =>
      M.interpPred ExPred_7_2_1.R (vec2 a b)
    have evalR (t : Assignment M) (i j : Nat) :
        M.interpPred ExPred_7_2_1.R
            (fun k =>
              termEval M t (vec2 (Term.var i) (Term.var j) k)) ↔
          r (t i) (t j) := by
      dsimp only [r]
      exact evalVec2 t i j ▸ Iff.rfl
    have evalOriginal :
        formulaEvalN M exampleFormula_7_2_1 s ↔
          (∀ a, p a ∨ ¬ ∃ b, q b ∧ r a b) ∨
            ¬ (p (s 1) ∧ ¬ ∀ c, p c) := by
      simp only [exampleFormula_7_2_1, formulaEvalN]
      simp only [evalR]
      simp [p, q, r, termEval, assignUpdate]
    have evalFinal :
        formulaEvalN M exPrenexFinal_7_2_1 s ↔
          ∀ a b c,
            (p a ∨ ¬ (q b ∧ r a b)) ∨
              ¬ (p (s 1) ∧ ¬ p c) := by
      simp only [exPrenexFinal_7_2_1, formulaEvalN]
      simp only [evalR]
      simp [p, q, r, termEval, assignUpdate]
    constructor
    · intro hOriginal
      apply evalFinal.mpr
      rcases evalOriginal.mp hOriginal with hLeft | hRight
      · intro a b c
        left
        rcases hLeft a with hPa | hNoWitness
        · exact Or.inl hPa
        · exact Or.inr (fun hQandR => hNoWitness ⟨b, hQandR⟩)
      · intro a b c
        right
        intro hPyNotPc
        apply hRight
        exact ⟨hPyNotPc.1, fun hAllP => hPyNotPc.2 (hAllP c)⟩
    · intro hFinal
      apply evalOriginal.mpr
      have hFinal' := evalFinal.mp hFinal
      by_cases hRight : ¬ (p (s 1) ∧ ¬ ∀ c, p c)
      · exact Or.inr hRight
      · left
        have hPyNotAll : p (s 1) ∧ ¬ ∀ c, p c :=
          Classical.byContradiction hRight
        obtain ⟨c, hNotPc⟩ := Classical.not_forall.mp hPyNotAll.2
        intro a
        by_cases hPa : p a
        · exact Or.inl hPa
        · exact Or.inr (fun hWitness => by
            obtain ⟨b, hQandR⟩ := hWitness
            rcases hFinal' a b c with hLeft | hRight'
            · rcases hLeft with hPa' | hNotQandR
              · exact hPa hPa'
              · exact hNotQandR hQandR
            · exact hRight' ⟨hPyNotAll.1, hNotPc⟩)

end LCS.Herbrand.PrenexForm

namespace LCS.Herbrand.PrenexForm
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Equivalence
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN.Substitution

proof_of exPrenexStep1_equiv_7_2_1 := by
  -- BEGIN PROOF
    exact prenex_equiv_c_neg_ex 1 _

proof_of exPrenexStep2_equiv_7_2_1 := by
  -- BEGIN PROOF
    apply foLogEquivN_all 0
    refine foLogEquivN_trans (foLogEquivN_disj (foLogEquivN_refl _)
      exPrenexStep1_equiv_7_2_1) ?_
    refine foLogEquivN_trans (foLogEquivN_disj_comm _ _) ?_
    refine foLogEquivN_trans (prenex_equiv_d_univ_disj 1 _ _ ?_) ?_
    · change ¬ (∃ i : Fin 1, (1 : Nat) = 0)
      simp
    · exact foLogEquivN_all 1 (foLogEquivN_disj_comm _ _)

proof_of exPrenexStep3_equiv_7_2_1 := by
  -- BEGIN PROOF
    exact prenex_equiv_c_neg_all 0 _

proof_of exPrenexStep4_equiv_7_2_1 := by
  -- BEGIN PROOF
    refine foLogEquivN_trans (foLogEquivN_conj (foLogEquivN_refl _)
      exPrenexStep3_equiv_7_2_1) ?_
    refine foLogEquivN_trans (foLogEquivN_conj_comm _ _) ?_
    refine foLogEquivN_trans (prenex_equiv_d_ex_conj 0 _ _ ?_) ?_
    · change ¬ (∃ i : Fin 1, (0 : Nat) = 1)
      simp
    · exact foLogEquivN_ex 0 (foLogEquivN_conj_comm _ _)

proof_of exPrenexStep5_equiv_7_2_1 := by
  -- BEGIN PROOF
    exact foLogEquivN_trans (foLogEquivN_neg exPrenexStep4_equiv_7_2_1)
      (prenex_equiv_c_neg_ex 0 _)

end LCS.Herbrand.PrenexForm
