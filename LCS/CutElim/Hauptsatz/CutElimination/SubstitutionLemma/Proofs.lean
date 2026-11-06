import LCS.CutElim.Hauptsatz.CutElimination.SubstitutionLemma

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

proof_of g1nnf_substitution_lemma := by
  let R := G1nnfProofTree.prepareSubstitution T t y hNotBound hFree
  obtain ⟨T', hd, hc, he⟩ :=
    g1nnf_substitution_of_treeSubstOk R.tree y t R.treeSubstOk
  exact ⟨T', hd.trans R.depth_eq, hc.trans R.cutRank_eq, he⟩

end LCS.CutElim.Hauptsatz
end
