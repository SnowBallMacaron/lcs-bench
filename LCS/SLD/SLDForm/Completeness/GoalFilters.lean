import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm.Occurrence
import LCS.SLD.SLDForm.Completeness.OccurrenceNormalization
import LCS.SLD.SLDForm.Completeness.RootPartition
import Attach
import LCS.SLD.SLDForm.Completeness.GoalFilters.ProofsStamp

section
namespace LCS.SLD.SLDForm.Completeness
open LCS.Resolution.GCNF
open LCS.SLD.SLDForm
open LCS.SLD.SLDForm.Occurrence

























-- ========= Helpers for goal_reduction rule case =========









-- ========= Lemma 9.2.5: Goal reduction =========

/-- Lemma 9.2.5: If a Horn set S (J, goals N_1,...,N_k, definite C_1,...,C_m) is
    GCNF'-provable, then some J ∪ {C_1,...,C_m} ∪ {N_i} is GCNF'-provable. -/
@[blueprint "chap9__lemma_9_2_5" (main := true)]
theorem goal_reduction
    (J : ClauseSequent)
    (goals : List Clause)
    (defs : List Clause)
    (hJ : ∀ C ∈ J, ∃ P : Nat, C = Clause.single (Literal.pos P))
    (hGoals : ∀ C ∈ goals, isGoalClause C)
    (hGoalsNe : goals ≠ [])
    (hDefs : ∀ C ∈ defs, isDefiniteClause C ∧ (∃ l₁ l₂, l₁ ∈ C ∧ l₂ ∈ C ∧ l₁ ≠ l₂))
    (S : ClauseSequent)
    (hS : S = Finset.union (Finset.union J (ClauseSequent.ofList defs)) (ClauseSequent.ofList goals))
    (hProv : GCNFProvable S) :
    -- Part (a): some single-goal subset is provable
    (∃ (i : Fin goals.length),
      GCNFProvable (Finset.union (Finset.union J (ClauseSequent.ofList defs))
        (ClauseSequent.single (goals.get i)))) ∧
    -- Part (b): for any specific proof, some single-goal subset has bounded depth
    (∀ T : GCNFProofTree S,
      IsStrictIWW T → T.axiomsAllSingleLiteral →
      ∃ (i : Fin goals.length),
        ∃ T' : GCNFProofTree (Finset.union (Finset.union J (ClauseSequent.ofList defs))
          (ClauseSequent.single (goals.get i))),
          proofDepth T' ≤ proofDepth T) 

end LCS.SLD.SLDForm.Completeness
end

