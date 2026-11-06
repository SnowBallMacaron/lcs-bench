import LCS.CutElim.Hauptsatz.CutElimination.SubstitutionPreservation

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

proof_of g1nnf_term_subst_preservation := by
  constructor
  · intro z hz
    refine ⟨T.forgetProofTree.substituteVar_isProof z y hNotBound hz
      T.forgetProofTree_isProof, ?_⟩
    -- REPAIR(T6-28): proof pending
    sorry
  · intro t hf he ht
    refine ⟨T.forgetProofTree.substTerm_isProof t y hNotBound hf he ht
      T.forgetProofTree_isProof, ?_⟩
    -- REPAIR(T6-28): proof pending
    sorry

end LCS.CutElim.Hauptsatz
end
