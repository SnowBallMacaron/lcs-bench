import LCS.Herbrand.NNFHauptsatz.Soundness

namespace LCS.Herbrand.NNFHauptsatz.Soundness

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SyntaxN.Variables

open LCS.Herbrand.NNFHauptsatz

open LCS.CutElim.Hauptsatz

open LCS.Herbrand.PrenexForm

open LCS.FirstOrder.SemanticsN.Substitution

proof_of g2nnf_provable_implies_valid := by
  -- BEGIN PROOF
    intro hProv M s hG
    obtain ⟨T⟩ := hProv
    exact Classical.byContradiction fun hNotDelta => by
      have hDelta : ∀ B, Membership.mem Delta B → ¬ formulaEvalN M B s :=
        fun B hB hEval => hNotDelta ⟨B, hB, hEval⟩
      exact g2nnf_tree_soundness hL M T ⟨s, hG, hDelta⟩


end LCS.Herbrand.NNFHauptsatz.Soundness
