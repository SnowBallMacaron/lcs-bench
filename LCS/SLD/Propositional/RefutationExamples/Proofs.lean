import LCS.SLD.Propositional.RefutationExamples

section
namespace LCS.SLD.Propositional
open LCS.Resolution.GCNF
open LCS.SLD.SLDForm

proof_of exMultiGoalRefutation1_clauses_subset := by
  -- BEGIN PROOF
    change ∀ C, exMultiGoalRefutation1.definiteClauses C → C ∈ exMultiGoalClauseSet
    simp [exMultiGoalRefutation1, exMultiGoalClauseSet]

proof_of exSLDRefutation_isRefutation := by
  -- BEGIN PROOF
    unfold isSLDRefutation exSLDRefutation exLinearizationResult
    simp [List.getLast]

proof_of exMultiGoalRefutation1_isRefutation := by
  -- BEGIN PROOF
    unfold isSLDRefutation exMultiGoalRefutation1
    simp [List.getLast]

proof_of exMultiGoalRefutation2_isRefutation := by
  -- BEGIN PROOF
    unfold isSLDRefutation exMultiGoalRefutation2
    simp [List.getLast]

end LCS.SLD.Propositional
end
