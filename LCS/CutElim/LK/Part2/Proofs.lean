import LCS.CutElim.LK.Part2

section

namespace LCS.CutElim.LK

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SemanticsN.Substitution

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Completeness

open LCS.FirstOrder.Gentzen.Hintikka

open LCS.CutElim.CompletenessBridge

proof_of gentzenHaupsatzLK := by
  -- BEGIN PROOF
    constructor
    · intro hfolk
      have hvalid : sequentValid seq := soundness_FOLK seq hfolk
      have hgprov : sequentProvableExt seq :=
        completenessG_cross hL seq hCross hvalid
      exact gProvable_folkCutFreeProvable seq hgprov
    · intro ⟨t, _hcf⟩
      exact ⟨t⟩


helper /-- Theorem 6.2.1 (LK → G): Convert an LK proof over a language without
equality to a G proof of the same sequent, assuming the §6.1 sequent-level
free/bound convention. This direction selects its tree by classical choice.
The converse effective procedure is `convert_g_to_folkCutFree`. -/
noncomputable def theorem_6_2_1 {L : Language} [Countable (Term L)]
    (hL : L.withoutEquality) :
    ∀ (seq : Sequent L), crossNoFreeBound seq →
      FOLKProofTree seq → GProofTreeExt seq :=
  fun _ hCross t => convert_folk_to_g hL hCross t

proof_of theorem_6_2_1_spec := fun _ t =>
  convert_g_to_folkCutFree_isCutFree t


end LCS.CutElim.LK

end
