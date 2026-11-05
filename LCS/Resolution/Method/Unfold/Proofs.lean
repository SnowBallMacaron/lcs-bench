import LCS.Resolution.Method.Unfold

namespace LCS.Resolution.Method.FiniteGraph

open LCS.Resolution.GCNF

helper /-- Every copied inference is valid and carries the original vertex label. -/
theorem unfoldAt_correct (g : FiniteGraph) (hg : g.WellFormed)
    (i : Nat) (hi : i < g.table.length) (hreach : i ∈ g.vertexIds) :
    (g.unfoldAt hg.2.1 i hi).IsWellFormed ∧
      g.label i = some (g.unfoldAt hg.2.1 i hi).label := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    let n := g.table[i]
    have hn : g.node i = some n := node_get g i hi
    cases hr : n.inference with
    | none =>
      rw [unfoldAt_leaf g hg.2.1 i hi n hn hr]
      exact ⟨True.intro, by simp [label, hn, ResolutionTree.label]⟩
    | some r =>
      obtain ⟨a, b, ha, hb, hp, hq, hlabel⟩ := hg.2.2 i hreach n hn r hr
      have hlt := hg.2.1 i n hn r hr
      have hlreach := LCS.Resolution.Method.FiniteGraph.next_mem_vertexIds hg hreach (show g.next i 0 = some r.left by simp [next, hn, hr])
      have hrreach := LCS.Resolution.Method.FiniteGraph.next_mem_vertexIds hg hreach (show g.next i 1 = some r.right by simp [next, hn, hr])
      have hleft := ih r.left hlt.1 (Nat.lt_trans hlt.1 hi) hlreach
      have hright := ih r.right hlt.2 (Nat.lt_trans hlt.2 hi) hrreach
      have hal : a.clause = (g.unfoldAt hg.2.1 r.left (Nat.lt_trans hlt.1 hi)).label :=
        by
          have hx : g.label r.left = some a.clause := by simp [label, ha]
          exact Option.some.inj (hx.symm.trans hleft.2)
      have hbl : b.clause = (g.unfoldAt hg.2.1 r.right (Nat.lt_trans hlt.2 hi)).label :=
        by
          have hx : g.label r.right = some b.clause := by simp [label, hb]
          exact Option.some.inj (hx.symm.trans hright.2)
      rw [unfoldAt_step g hg.2.1 i hi n hn r hr]
      refine ⟨⟨hleft.1, hright.1, hal ▸ hp, hbl ▸ hq⟩, ?_⟩
      simp [label, hn, ResolutionTree.label, ← hal, ← hbl, hlabel]

proof_of unfold_isWellFormed := (unfoldAt_correct g hg g.root hg.1 (LCS.Resolution.Method.FiniteGraph.root_mem_vertexIds g hg)).1


proof_of unfold_rootLabel := (unfoldAt_correct g hg g.root hg.1 (LCS.Resolution.Method.FiniteGraph.root_mem_vertexIds g hg)).2


proof_of unfold_inputs_subset := (LCS.Resolution.Method.Erase.Proofs.leavesFrom_iff_inputs_subset _ S).symm.trans
    (unfold_leavesFrom g hg S)


end LCS.Resolution.Method.FiniteGraph
