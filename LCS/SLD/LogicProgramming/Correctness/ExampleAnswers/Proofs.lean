import LCS.SLD.LogicProgramming.Correctness.ExampleAnswers

section
namespace LCS.SLD.LogicProgramming.Correctness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.SLD.FirstOrder
open LCS.SLD.LogicProgramming

proof_of exIndefiniteAnswerValidity := by
  classical
  intro M hSat s
  change ¬ M.interpPred .rocksinger (fun _ => s 22) ∨ M.interpPred .rich (fun _ => s 22)
  by_cases hRock : M.interpPred .rocksinger (fun _ => s 22)
  · right
    have hRule := hSat (fun _ => s 22) ex954_C4
      (by
        change ex954_C4 ∈ [ex954_C1, ex954_C2, ex954_C3, ex954_C4, exCorrectnessGoalClause1]
        simp)
    change (∀ a ∈ [mkCorrAtom .rocksinger (.var 0)],
      formulaEvalN M a.toFormula (fun _ => s 22)) →
      M.interpPred .rich (fun _ => s 22) at hRule
    apply hRule
    intro a ha
    simp only [List.mem_singleton] at ha
    subst a
    exact hRock
  · exact Or.inl hRock

proof_of exDisplayedRefutation_answerClasses := by
  -- REPAIR(T9-55): proof pending — four distinct displayed output patterns and two traces per goal
  sorry

proof_of exAnswer_groundCoordinateCases := by
  -- REPAIR(T9-55): proof pending — validity of all three independent free-coordinate families over P
  sorry

proof_of exAnswer_diagonalCase := by
  -- REPAIR(T9-55): proof pending — common finite grounding of both shared-variable coordinates over P
  sorry

end LCS.SLD.LogicProgramming.Correctness
end
