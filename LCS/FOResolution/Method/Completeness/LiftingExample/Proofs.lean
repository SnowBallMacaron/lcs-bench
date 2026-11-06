import LCS.FOResolution.Method.Completeness.LiftingExample

section
namespace LCS.FOResolution.Method.Completeness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.GroundResolution
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.HerbrandBridge
open LCS.CutElim.LK
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open Classical

proof_of exLiftHom_preserves_premises := by
  revert v
  decide

proof_of exLiftHom_node_labels := by
  -- REPAIR(T8-84): proof pending
  sorry

proof_of exLiftedDAG_inferences_legal := by
  -- REPAIR(T8-84): proof pending
  sorry

proof_of exLiftGroundDAG_inferences_legal := by
  -- REPAIR(T8-84): proof pending
  sorry

proof_of exLiftingExample_refutations := by
  constructor
  · refine ⟨?_, exLiftedDAG_inferences_legal, rfl⟩
    intro ⟨n, hn⟩ h
    have hCases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨
        n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
    rcases hCases with hN | hN | hN | hN | hN | hN | hN | hN <;>
      subst n <;> simp [exLiftingExample, exLiftedDAG] at h ⊢
  · refine ⟨?_, exLiftGroundDAG_inferences_legal, rfl⟩
    intro ⟨n, hn⟩ h
    have hCases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨
        n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
    rcases hCases with hN | hN | hN | hN | hN | hN | hN | hN <;>
      subst n <;> simp [exLiftingExample, exLiftGroundDAG] at h ⊢

end LCS.FOResolution.Method.Completeness
end
