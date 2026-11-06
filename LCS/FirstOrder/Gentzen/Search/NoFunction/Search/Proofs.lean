import LCS.FirstOrder.Gentzen.Search.NoFunction.Search

section

namespace LCS.FirstOrder.Gentzen.Search.NoFunction
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka

proof_of search_halts_with_proof_or_falsifying_model := by
  -- BEGIN PROOF

    refine ⟨?_, ?_⟩
    · -- Part (i): valid ⇒ ∃ k, search halts with closed proof tree.
      intro _hValid
      -- REPAIR(T88): proof pending
      sorry
    · -- Part (ii): ¬ valid ⇒ finite CE ∨ infinite tree + model.
      -- Classical case split on whether search ever produces a finished tree.
      intro hNotValid
      by_cases hFin : ∃ k : Nat,
          isFinishedTree hNoEq
            (search hNoEq hNoFunc seq hCNFB initial k).1
            (search hNoEq hNoFunc seq hCNFB initial k).2
      · -- Case A: ∃ k, search produces a finished tree.
        left
        obtain ⟨k, hFinK⟩ := hFin
        refine ⟨k, hFinK, ?_, ?_⟩
        · -- ¬ isClosed at stage k. If the tree at stage k were closed, it
          -- would witness sequentProvableExt seq via toProofTree, hence
          -- sequentValid seq by soundness — contradicting hNotValid.
          intro hClosed
          have hProof :
              (search hNoEq hNoFunc seq hCNFB initial k).1.toDeductionTree.isProof :=
            ((search hNoEq hNoFunc seq hCNFB initial k).1.toDeductionTree.isProof_iff_isClosed).mpr hClosed
          have hProvable : sequentProvableExt seq :=
            ⟨(search hNoEq hNoFunc seq hCNFB initial k).1.toDeductionTree.toProofTree hProof⟩
          exact hNotValid (soundnessG_Ext seq hProvable)
        · -- Extract a finite falsifying model from a non-axiom finished leaf.
          -- REPAIR(T88): proof pending
          sorry
      · -- Case B: ∀ k, search does NOT produce a finished tree.
        right
        have hFin' : ∀ k : Nat,
            ¬ isFinishedTree hNoEq
                (search hNoEq hNoFunc seq hCNFB initial k).1
                (search hNoEq hNoFunc seq hCNFB initial k).2 := by
          intro k hk
          exact hFin ⟨k, hk⟩
        refine ⟨hFin', ?_⟩
        -- Extract a countably infinite falsifying model from an infinite path.
        -- REPAIR(T88): proof pending
        sorry

end LCS.FirstOrder.Gentzen.Search.NoFunction

end
