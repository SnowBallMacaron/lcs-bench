import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm.Occurrence
import LCS.SLD.SLDForm.Completeness.OccurrenceNormalization
import LCS.SLD.SLDForm.Completeness.RootPartition
import LCS.SLD.SLDForm.Completeness.GoalFilters
import Attach
import LCS.SLD.SLDForm.Completeness.GoalReduction.ProofsStamp

section
namespace LCS.SLD.SLDForm.Completeness
open LCS.Resolution.GCNF
open LCS.SLD.SLDForm
open LCS.SLD.SLDForm.Occurrence





/-- Lemma 9.2.2 (companion, ∨:left invertibility for GCNF'): If S is
    GCNF'-provable and contains a clause of the form `clauseWithLiteral B'' Q`
    (i.e., B'' ∨ Q), then both sub-sequents obtained by replacing that clause
    with B'' (the left premise) or with {Q} (the right premise) are
    GCNF'-provable. Requires the non-emptiness side conditions needed for
    completeness: B'' is non-empty, and every clause in
    S.erase(clauseWithLiteral B'' Q) is non-empty. -/
@[blueprint "chap9__lemma_9_2_2"]
theorem gcnf_provable_clause_split
    (S : ClauseSequent)
    (B'' : Clause) (Q : Literal)
    (hCwlMem : clauseWithLiteral B'' Q ∈ S)
    (hB''ne : B'' ≠ Clause.empty)
    (hGammaNe : ∀ C ∈ Finset.erase S (clauseWithLiteral B'' Q), C ≠ Clause.empty)
    (hProv : GCNFProvable S) :
    GCNFProvable
      (Finset.union (Finset.erase S (clauseWithLiteral B'' Q))
        (ClauseSequent.single B'')) ∧
    GCNFProvable
      (Finset.union (Finset.erase S (clauseWithLiteral B'' Q))
        (ClauseSequent.single (Clause.single Q))) 

-- ========= Helpers for the outer goal-split right-subtree witness =========

























-- ========= Theorem 9.2.1: Completeness of proofs in SLD-form =========

/-- Theorem 9.2.1: (Completeness of proofs in SLD-form) If a set S of definite
    clauses with a single goal B = {neg P_1, ..., neg P_n} (with n ≥ 1) is
    GCNF'-provable, it has a GCNF'-proof in SLD-form. The hypothesis
    `hBne : B ≠ Clause.empty` encodes the textbook's implicit assumption that
    the goal is a nonempty set of negative literals (the n ≥ 1 side condition
    in Def 9.2.1's goal-clause shape {neg P_1, ..., neg P_n}). -/
@[blueprint "chap9__theorem_9_2_1" (main := true)]
theorem sld_form_completeness (S : ClauseSequent)
    (hDef : ∀ C ∈ S, isDefiniteClause C ∨ isGoalClause C)
    (B : Clause)
    (hB : B ∈ S)
    (hGoalB : isGoalClause B)
    (hBne : B ≠ Clause.empty)
    (hUnique : ∀ C ∈ S, isGoalClause C → C = B)
    (hProv : GCNFProvable S) :
    ∃ T : GCNFProofTree S, isSLDForm T 

-- ========= Theorem 9.2.2: SLD-form completeness for multiple goals =========

/-- Theorem 9.2.2: If a set S of Horn clauses (with J, goals N_1,...,N_k, definite
    C_1,...,C_m) is GCNF'-provable, some single-goal subset has a GCNF'-proof in
    SLD-form. Each goal N_j is required to be nonempty (textbook's implicit n ≥ 1
    in Def 9.2.1's goal-clause shape), propagated to Thm 9.2.1. -/
@[blueprint "chap9__theorem_9_2_2" (main := true)]
theorem sld_form_completeness_multiple_goals
    (J : ClauseSequent)
    (goals : List Clause)
    (defs : List Clause)
    (hJ : ∀ C ∈ J, ∃ P : Nat, C = Clause.single (Literal.pos P))
    (hGoals : ∀ C ∈ goals, isGoalClause C)
    (hGoalsNonempty : ∀ C ∈ goals, C ≠ Clause.empty)
    (hGoalsNe : goals ≠ [])
    (hDefs : ∀ C ∈ defs, isDefiniteClause C ∧ (∃ l₁ l₂, l₁ ∈ C ∧ l₂ ∈ C ∧ l₁ ≠ l₂))
    (S : ClauseSequent)
    (hS : S = Finset.union (Finset.union J (ClauseSequent.ofList defs)) (ClauseSequent.ofList goals))
    (hProv : GCNFProvable S) :
    ∃ (i : Fin goals.length),
      ∃ T : GCNFProofTree (Finset.union (Finset.union J (ClauseSequent.ofList defs)) (ClauseSequent.single (goals.get i))),
        isSLDForm T 

end LCS.SLD.SLDForm.Completeness
end

