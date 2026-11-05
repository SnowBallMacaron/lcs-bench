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

helper /-- Expanding the original leaves preserves every existing inference node. -/
theorem expandTree_extends {L : Language} {supply : TermStream L}
    (hNoEq : L.hasEquality = false) (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat} (hCNFB : crossNoFreeBound seq)
    {s : Sequent L} (t : SearchTree s) (st : SearchState L supply)
    (hInv : SearchState.Inv seq bound st)
    (hTLI : TreeLeafInv supply t seq st.availNext) :
    t.Extends (expandTree hNoEq hNoFunc hCNFB t st hInv hTLI).tree := by
  induction t generalizing st with
  | leaf s records => exact .leaf records _
  | onePremise rule t ih =>
      exact .onePremise rule (ih _ _ _)
  | twoPremise rule t1 t2 ih1 ih2 =>
      exact .twoPremise rule (ih1 _ _ _) (ih2 _ _ _)

helper /-- A complete round extends its input tree, including the record commit. -/
theorem searchRound_extends {L : Language} {supply : TermStream L}
    (hNoEq : L.hasEquality = false) (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat} (hCNFB : crossNoFreeBound seq)
    {s : Sequent L} (t : SearchTree s) (st : SearchState L supply)
    (hInv : SearchState.Inv seq bound st)
    (hTLI : TreeLeafInv supply t seq st.availNext) :
    t.Extends (searchRound hNoEq hNoFunc hCNFB t st hInv hTLI).tree :=
  (expandTree_extends hNoEq hNoFunc hCNFB t st hInv hTLI).commitRound _

helper /-- Each additional round extends the preceding finite approximant. -/
theorem searchAux_mono {L : Language} {supply : TermStream L}
    (hNoEq : L.hasEquality = false) (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat} (hCNFB : crossNoFreeBound seq)
    (k : Nat) {s : Sequent L} (t : SearchTree s) (st : SearchState L supply)
    (hInv : SearchState.Inv seq bound st)
    (hTLI : TreeLeafInv supply t seq st.availNext) :
    (searchAux hNoEq hNoFunc hCNFB k t st hInv hTLI).tree.Extends
      (searchAux hNoEq hNoFunc hCNFB (k + 1) t st hInv hTLI).tree := by
  induction k generalizing s st with
  | zero => exact searchRound_extends hNoEq hNoFunc hCNFB t st hInv hTLI
  | succ k ih =>
      let out := searchRound hNoEq hNoFunc hCNFB t st hInv hTLI
      exact ih out.tree out.state out.state_inv out.tree_leaf_inv

helper /-- Definition 5.4.9 (companion): For a fixed admissible initialization,
    round `k + 1` extends round `k` by replacing leaves with subtrees. -/
theorem search_mono {L : Language} (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False) (seq : Sequent L)
    (hCNFB : crossNoFreeBound seq) (initial : Init seq) (k : Nat) :
    (search hNoEq hNoFunc seq hCNFB initial k).1.Extends
      (search hNoEq hNoFunc seq hCNFB initial (k + 1)).1 :=
  searchAux_mono hNoEq hNoFunc hCNFB k _ _ _ _

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


proof_of search_goedel_corollary := by
  -- BEGIN PROOF
    let initial := Init.default seq
    obtain ⟨hPart1, _⟩ :=
      search_halts_with_proof_or_falsifying_model hNoEq hNoFunc seq hCNFB initial
    obtain ⟨k, hProof⟩ := hPart1 hValid
    exact ⟨(search hNoEq hNoFunc seq hCNFB initial k).1.toDeductionTree.toProofTree hProof⟩


end LCS.FirstOrder.Gentzen.Search.NoFunction

end
