import LCS.Resolution.Method.Unfold

/-! # Unfolding counts for resolution trees

A graph with a unique root path to each vertex has no copied occurrences in its
unfolding. Its executable reachable-vertex count is therefore exactly the full
binary tree's node count.
-/

namespace LCS.Resolution.Method.FiniteGraph

/-- Unique paths make the traversal list duplicate-free before erasing IDs. -/
theorem reachableFrom_nodup_of_unique_paths (g : FiniteGraph) (depth i : Nat)
    (hunique : ∀ a b j, g.followFrom i a = some j →
      g.followFrom i b = some j → a = b) :
    (g.reachableFrom depth i).Nodup := by
  induction depth generalizing i with
  | zero => simp [reachableFrom]
  | succ depth ih =>
    have hchild (p j : Nat) (hn : g.next i p = some j) :
        ∀ a b k, g.followFrom j a = some k →
          g.followFrom j b = some k → a = b := by
      intro a b k ha hb
      have he := hunique (p :: a) (p :: b) k
        (by simp [followFrom, hn, ha]) (by simp [followFrom, hn, hb])
      exact List.cons.inj he |>.2
    have hnot (p j : Nat) (hn : g.next i p = some j) :
        i ∉ g.reachableFrom depth j := by
      intro hm
      obtain ⟨a, ha, _⟩ := (mem_reachableFrom_iff g depth j i).mp hm
      have he := hunique [] (p :: a) i rfl (by simp [followFrom, hn, ha])
      cases he
    cases hleft : g.next i 0 with
    | none =>
      cases hright : g.next i 1 with
      | none => simp [reachableFrom, hleft, hright]
      | some r =>
        simp only [reachableFrom, hleft, hright, List.nil_append]
        exact List.nodup_cons.mpr ⟨hnot 1 r hright, ih r (hchild 1 r hright)⟩
    | some l =>
      cases hright : g.next i 1 with
      | none =>
        simp only [reachableFrom, hleft, hright, List.append_nil]
        exact List.nodup_cons.mpr ⟨hnot 0 l hleft, ih l (hchild 0 l hleft)⟩
      | some r =>
        simp only [reachableFrom, hleft, hright]
        apply List.nodup_cons.mpr
        refine ⟨?_, List.nodup_append.mpr ⟨ih l (hchild 0 l hleft),
          ih r (hchild 1 r hright), ?_⟩⟩
        · intro hm
          rcases List.mem_append.mp hm with hl | hr
          · exact hnot 0 l hleft hl
          · exact hnot 1 r hright hr
        · intro a ha b hb hab
          subst b
          obtain ⟨u, hu, _⟩ := (mem_reachableFrom_iff g depth l a).mp ha
          obtain ⟨v, hv, _⟩ := (mem_reachableFrom_iff g depth r a).mp hb
          have he := hunique (0 :: u) (1 :: v) a
            (by simp [followFrom, hleft, hu]) (by simp [followFrom, hright, hv])
          cases he

/-- The traversal visits every occurrence of the finite binary unfolding. -/
theorem reachableFrom_length_eq_unfoldAt (g : FiniteGraph) (ht : g.Topological)
    (i : Nat) (hi : i < g.table.length) (depth : Nat) (hdepth : i < depth) :
    (g.reachableFrom depth i).length =
      2 * (g.unfoldAt ht i hi).treeStepCount + 1 := by
  induction depth generalizing i with
  | zero => omega
  | succ depth ih =>
    let n := g.table[i]
    have hn : g.node i = some n := by simp [node, n, hi]
    cases hr : n.inference with
    | none =>
      rw [LCS.Resolution.Method.FiniteGraph.unfoldAt_leaf g ht i hi n hn hr]
      simp [reachableFrom, next, hn, hr, ResolutionTree.treeStepCount]
    | some r =>
      have hlt := ht i n hn r hr
      have hl := ih r.left (Nat.lt_trans hlt.1 hi) (by omega)
      have hr' := ih r.right (Nat.lt_trans hlt.2 hi) (by omega)
      rw [LCS.Resolution.Method.FiniteGraph.unfoldAt_step g ht i hi n hn r hr]
      have hnextl : g.next i 0 = some r.left := by simp [next, hn, hr]
      have hnextr : g.next i 1 = some r.right := by simp [next, hn, hr]
      simp only [reachableFrom, hnextl, hnextr, List.length_cons,
        List.length_append, ResolutionTree.treeStepCount]
      omega

/-- Without sharing, actual graph vertices coincide with unfolded occurrences. -/
theorem nodeCount_eq_two_unfold_steps_add_one (g : FiniteGraph) (hg : g.WellFormed)
    (htree : (g.toResolutionDAG hg).isTreeShaped) :
    g.nodeCount = 2 * (g.unfold hg).treeStepCount + 1 := by
  have hnd := reachableFrom_nodup_of_unique_paths g g.table.length g.root
    ((LCS.Resolution.Method.FiniteGraph.toResolutionDAG_isTreeShaped_iff g hg).mp htree)
  have he := reachableFrom_length_eq_unfoldAt g hg.2.1 g.root hg.1
    g.table.length hg.1
  have hp := LCS.list_perm_of_nodup_of_mem_iff (LCS.Resolution.Method.FiniteGraph.vertexIds_nodup g) hnd
    (by intro j; simp [vertexIds])
  exact hp.length_eq.trans he

/-- The number of unfolded steps is bounded by the actual graph vertex count. -/
theorem unfold_steps_add_one_le_nodeCount (g : FiniteGraph) (hg : g.WellFormed)
    (htree : (g.toResolutionDAG hg).isTreeShaped) :
    (g.unfold hg).treeStepCount + 1 ≤ g.nodeCount := by
  rw [nodeCount_eq_two_unfold_steps_add_one g hg htree]
  omega

end LCS.Resolution.Method.FiniteGraph
