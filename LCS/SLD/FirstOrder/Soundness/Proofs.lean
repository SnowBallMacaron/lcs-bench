import LCS.SLD.FirstOrder.Soundness

section
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.Completeness

proof_of foSLDResolution_sound := by
  -- BEGIN PROOF
    -- Unfold unsatisfiability: show no structure satisfies all clause translations
    simp only [FOHornClauseSet.isUnsatisfiable, FOClauseSet.isUnsatisfiable]
    intro ⟨M, hSat⟩
    -- By sld_goal_invariant: clauseToFormula of current goal holds for all s
    have hInv := (sld_goal_invariant (hNoEq := by all_goals exact hNoEq)) Afalsum D goals d hGoalType M
      (fun C hC fvs _ => FOClause.universalClosure_of_validIn hNoEq M C (hSat C hC) Afalsum fvs)
    -- isRefutation: currentGoalVal = ∅
    have hEmpty : currentGoalVal = (∅ : LCS.Finset (FOAtom L hNoEq)) := hRef
    rw [hEmpty] at hInv
    -- `∅ : LCS.Finset _` has empty toList (via perm with []) so the mapped list is empty.
    have hToListEmpty : (∅ : LCS.Finset (FOAtom L hNoEq)).toList = [] := by
      have hEq := LCS.Finset.toList_ofList_eq (∅ : LCS.Finset (FOAtom L hNoEq))
      have hPerm : (∅ : LCS.Finset (FOAtom L hNoEq)).toList.Perm [] :=
        Quotient.exact hEq
      exact List.Perm.eq_nil hPerm
    rw [hToListEmpty] at hInv
    simp only [List.map] at hInv
    -- clauseToFormula [] is falsum Afalsum = Afalsum ∧ ¬Afalsum, a contradiction
    have hFalse := hInv (fun _ => Classical.choice M.carrierNonempty)
    simp only [clauseToFormula, FormulaN.falsum, formulaEvalN] at hFalse
    exact hFalse.2 hFalse.1

end LCS.SLD.FirstOrder
end
