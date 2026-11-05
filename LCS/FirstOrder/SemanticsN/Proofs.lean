import LCS.FirstOrder.SemanticsN

namespace LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SyntaxN.Variables



proof_of coincidenceLemmaN := by
  -- BEGIN PROOF
    induction A generalizing s1 s2 with
    | predN P ts =>
      simp only [formulaEvalN]
      have : (fun i => termEval M s1 (ts i)) = (fun i => termEval M s2 (ts i)) := by
        funext j; exact termCoincidence M (ts j) s1 s2 (fun y hy => h y ⟨j, hy⟩)
      rw [this]
    | eq_ _ t1 t2 =>
      simp only [formulaEvalN]
      rw [termCoincidence M t1 s1 s2 (fun y hy => h y (Or.inl hy)),
          termCoincidence M t2 s1 s2 (fun y hy => h y (Or.inr hy))]
    | neg A ih =>
      simp only [formulaEvalN]; exact not_congr (ih s1 s2 h)
    | conj A B ihA ihB =>
      simp only [formulaEvalN]
      exact and_congr (ihA s1 s2 fun y hy => h y (Or.inl hy))
                      (ihB s1 s2 fun y hy => h y (Or.inr hy))
    | disj A B ihA ihB =>
      simp only [formulaEvalN]
      exact or_congr (ihA s1 s2 fun y hy => h y (Or.inl hy))
                     (ihB s1 s2 fun y hy => h y (Or.inr hy))
    | impl A B ihA ihB =>
      simp only [formulaEvalN]
      exact imp_congr (ihA s1 s2 fun y hy => h y (Or.inl hy))
                      (ihB s1 s2 fun y hy => h y (Or.inr hy))
    | all i A ih =>
      simp only [formulaEvalN]
      constructor <;> intro hall a
      · exact (ih _ _ (fun y hy => by
          simp only [assignUpdate]; split
          · rfl
          · rename_i hyi; exact h y ⟨hy, hyi⟩)).mp (hall a)
      · exact (ih _ _ (fun y hy => by
          simp only [assignUpdate]; split
          · rfl
          · rename_i hyi; exact (h y ⟨hy, hyi⟩).symm)).mp (hall a)
    | ex i A ih =>
      simp only [formulaEvalN]
      constructor <;> intro ⟨a, ha⟩
      · exact ⟨a, (ih _ _ (fun y hy => by
          simp only [assignUpdate]; split
          · rfl
          · rename_i hyi; exact h y ⟨hy, hyi⟩)).mp ha⟩
      · exact ⟨a, (ih _ _ (fun y hy => by
          simp only [assignUpdate]; split
          · rfl
          · rename_i hyi; exact (h y ⟨hy, hyi⟩).symm)).mp ha⟩




end LCS.FirstOrder.SemanticsN
