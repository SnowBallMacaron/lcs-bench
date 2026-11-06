import LCS.SLD.FirstOrder.AdditionExample

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

proof_of exAddSigma1_isAtomMGU := by
  refine ⟨exAddPairs1, ?_, exAddSigma1_isPairwiseMGU⟩
  classical
  have hRenamed :
      (mkAdd (Term.var 0) (mkSucc (Term.var 1))
        (mkSucc (Term.var 2))).subst (hNoEq := by all_goals rfl) exAddRho1 =
      mkAdd (Term.var 4) (mkSucc (Term.var 5))
        (mkSucc (Term.var 6)) := by
    simp [formulaSubstAll_mkAdd, termSubstAll, exAddRho1,
      termSubstAll_mkSucc]
  rw [hRenamed]
  exact (atomUnifPairs?_predN_same (hNoEq := by all_goals rfl)) _ _ _

proof_of exAddSigma2_isAtomMGU := by
  refine ⟨exAddPairs2, ?_, exAddSigma2_isPairwiseMGU⟩
  classical
  have hRenamed :
      (mkAdd (Term.var 0) zeroTm (Term.var 0)).subst (hNoEq := by all_goals rfl) exAddRho2 =
      mkAdd (Term.var 7) zeroTm (Term.var 7) := by
    simp [formulaSubstAll_mkAdd, termSubstAll,
      termSubstAll_zeroTm, exAddRho2]
  rw [hRenamed]
  exact (atomUnifPairs?_predN_same (hNoEq := by all_goals rfl)) _ _ _

proof_of exAddRefutation_isRefutation := by
  -- BEGIN PROOF
    show (∅ : LCS.Finset (FOAtom exAddLang rfl)) =
         (∅ : LCS.Finset (FOAtom exAddLang rfl))
    rfl

end LCS.SLD.FirstOrder
end
namespace LCS.SLD.FirstOrder

proof_of exAddQuery_goalConsistent_iff := by
  -- REPAIR(T9-51): proof pending — closed negative-goal equivalences and the full map observed at V
  sorry

proof_of exAddAnswer_arithmeticDifference := by
  -- REPAIR(T9-52): proof pending — interpret the computed V as the numeral for 2 − 1
  sorry

end LCS.SLD.FirstOrder
