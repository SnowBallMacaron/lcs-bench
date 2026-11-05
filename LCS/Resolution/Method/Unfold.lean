import LCS.Resolution.Method.FiniteGraph
import LCS.Resolution.Method.Erase
import Attach
import LCS.Resolution.Method.Unfold.ProofsStamp

/-! # Executable unfolding of a finite resolution graph

Unfolding follows the stored premise identifiers. Every occurrence of a shared
vertex is copied into the tree; the graph's identifiers and graph counts remain
available separately. Topological order supplies a termination proof, so no
fuel exhaustion or arbitrary default tree is used.
-/

namespace LCS.Resolution.Method.FiniteGraph

open LCS.Resolution.GCNF



-- ATTACH-BLOCKER: used by LCS.Resolution.Method.Unfold (unfoldAt_leaf)
theorem node_get (g : FiniteGraph) (i : Nat) (hi : i < g.table.length) :
    g.node i = some g.table[i] := by simp [node, hi]

/-- Unfold a stored vertex by following its ordered premise identifiers. -/
@[blueprint "chap4__theorem_4_3_3"]
def unfoldAt (g : FiniteGraph) (ht : g.Topological)
    (i : Nat) (hi : i < g.table.length) : ResolutionTree :=
  let n := g.table[i]
  match hr : n.inference with
  | none => .axiom_ n.clause
  | some r =>
      .resolve
        (g.unfoldAt ht r.left (Nat.lt_trans (ht i n (List.getElem?_eq_getElem hi) r hr).1 hi))
        (g.unfoldAt ht r.right (Nat.lt_trans (ht i n (List.getElem?_eq_getElem hi) r hr).2 hi))
        r.pivot
termination_by i
decreasing_by
  · exact (ht i n (List.getElem?_eq_getElem hi) r hr).1
  · exact (ht i n (List.getElem?_eq_getElem hi) r hr).2

/-- The actual tree obtained by duplicating shared subderivations. -/
@[blueprint "chap4__theorem_4_3_3"]
def unfold (g : FiniteGraph) (hg : g.WellFormed) : ResolutionTree :=
  g.unfoldAt hg.2.1 g.root hg.1







-- ATTACH-BLOCKER: used by LCS.Resolution.Method.ReverseGrowth, LCS.Resolution.Method.UnfoldBounds
theorem unfoldAt_leaf (g : FiniteGraph) (ht : g.Topological)
    (i : Nat) (hi : i < g.table.length) (n : Node)
    (hn : g.node i = some n) (hr : n.inference = none) :
    g.unfoldAt ht i hi = .axiom_ n.clause := by
  have he : g.table[i] = n := Option.some.inj ((node_get g i hi).symm.trans hn)
  have hr' : g.table[i].inference = none := he ▸ hr
  rw [unfoldAt]
  split
  · simp [he]
  · rename_i r h
    have : (none : Option Inference) = some r := hr'.symm.trans h
    contradiction

-- ATTACH-BLOCKER: used by LCS.Resolution.Method.ReverseGrowth, LCS.Resolution.Method.UnfoldBounds
theorem unfoldAt_step (g : FiniteGraph) (ht : g.Topological)
    (i : Nat) (hi : i < g.table.length) (n : Node)
    (hn : g.node i = some n) (r : Inference) (hr : n.inference = some r) :
    g.unfoldAt ht i hi = .resolve
      (g.unfoldAt ht r.left (Nat.lt_trans (ht i n hn r hr).1 hi))
      (g.unfoldAt ht r.right (Nat.lt_trans (ht i n hn r hr).2 hi)) r.pivot := by
  have he : g.table[i] = n := Option.some.inj ((node_get g i hi).symm.trans hn)
  have hr' : g.table[i].inference = some r := he ▸ hr
  rw [unfoldAt]
  split
  · rename_i h
    have : (some r : Option Inference) = none := hr'.symm.trans h
    contradiction
  · rename_i r' h
    have : r = r' := Option.some.inj (hr'.symm.trans h)
    subst r'
    rfl

@[blueprint "chap4__theorem_4_3_3"]
theorem unfold_isWellFormed (g : FiniteGraph) (hg : g.WellFormed) :
    (g.unfold hg).IsWellFormed 

@[blueprint "chap4__theorem_4_3_3"]
theorem unfold_rootLabel (g : FiniteGraph) (hg : g.WellFormed) :
    g.rootLabel = some (g.unfold hg).label 






-- ATTACH-BLOCKER: used by LCS.Resolution.Method.Unfold (unfold_leavesFrom)
/-- The leaf condition of the unfolded tree is exactly the path-based leaf
condition of its source vertex. Repeated visits to a shared leaf do not change
which input clauses are permitted. -/
theorem unfoldAt_leavesFrom (g : FiniteGraph) (ht : g.Topological)
    (i : Nat) (hi : i < g.table.length) (S : ClauseSequent) :
    (g.unfoldAt ht i hi).leavesFrom S ↔
      ∀ a j n, g.followFrom i a = some j → g.node j = some n →
        n.inference = none → n.clause ∈ S := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    let n := g.table[i]
    have hn : g.node i = some n := node_get g i hi
    cases hr : n.inference with
    | none =>
      rw [unfoldAt_leaf g ht i hi n hn hr]
      constructor
      · intro h a j m hpath hm hmleaf
        cases a with
        | nil =>
          have he : i = j := Option.some.inj hpath
          subst j
          have he : n = m := Option.some.inj (hn.symm.trans hm)
          subst m
          exact h
        | cons p rest => simp [followFrom, next, hn, hr] at hpath
      · intro h
        exact h [] i n rfl hn hr
    | some r =>
      have hlt := ht i n hn r hr
      rw [unfoldAt_step g ht i hi n hn r hr]
      change (_ ∧ _) ↔ _
      rw [ih r.left hlt.1 (Nat.lt_trans hlt.1 hi),
        ih r.right hlt.2 (Nat.lt_trans hlt.2 hi)]
      constructor
      · rintro ⟨hleft, hright⟩ a j m hpath hm hmleaf
        cases a with
        | nil =>
          have he : i = j := Option.some.inj hpath
          subst j
          have he : n = m := Option.some.inj (hn.symm.trans hm)
          subst m
          rw [hr] at hmleaf
          contradiction
        | cons p rest =>
          cases p with
          | zero =>
            apply hleft rest j m _ hm hmleaf
            simpa [followFrom, next, hn, hr] using hpath
          | succ p =>
            cases p with
            | zero =>
              apply hright rest j m _ hm hmleaf
              simpa [followFrom, next, hn, hr] using hpath
            | succ p => simp [followFrom, next, hn] at hpath
      · intro h
        constructor
        · intro a j m hpath hm hmleaf
          apply h (0 :: a) j m _ hm hmleaf
          simpa [followFrom, next, hn, hr] using hpath
        · intro a j m hpath hm hmleaf
          apply h (1 :: a) j m _ hm hmleaf
          simpa [followFrom, next, hn, hr] using hpath

-- ATTACH-BLOCKER: used by LCS.FOResolution.GroundResolution
/-- Unfolding preserves exactly the allowable input clauses. -/
theorem unfold_leavesFrom (g : FiniteGraph) (hg : g.WellFormed)
    (S : ClauseSequent) : (g.unfold hg).leavesFrom S ↔ g.LeavesFrom S := by
  rw [unfold, unfoldAt_leavesFrom]
  constructor
  · intro h i hi
    obtain ⟨hvertex, hleaf⟩ := List.mem_filter.mp hi
    obtain ⟨a, ha, _⟩ := (mem_vertexIds_iff g i).mp hvertex
    have hib := LCS.Resolution.Method.FiniteGraph.vertexIds_index_lt hg hvertex
    let n := g.table[i]
    have hn : g.node i = some n := node_get g i hib
    have hr : n.inference = none := by
      cases hr : n.inference with
      | none => rfl
      | some r => simp [isInternal, hn, hr] at hleaf
    exact ⟨n.clause, by simp [label, hn], h a i n ha hn hr⟩
  · intro h a i n ha hn hr
    have hvertex := LCS.Resolution.Method.FiniteGraph.follow_mem_vertexIds hg ha
    have hleaf : i ∈ g.leafIds := List.mem_filter.mpr
      ⟨hvertex, by simp [isInternal, hn, hr]⟩
    obtain ⟨C, hC, hmem⟩ := h i hleaf
    have he : n.clause = C := by
      have hx : g.label i = some n.clause := by simp [label, hn]
      exact Option.some.inj (hx.symm.trans hC)
    exact he ▸ hmem

@[blueprint "chap4__theorem_4_3_3"]
theorem unfold_inputs_subset (g : FiniteGraph) (hg : g.WellFormed)
    (S : ClauseSequent) :
    LCS.Finset.Subset (g.unfold hg).inputs S ↔ g.LeavesFrom S 

end LCS.Resolution.Method.FiniteGraph
