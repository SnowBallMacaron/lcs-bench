import LCS.Resolution.Method.Soundness
open LCS.Resolution.Method.Resolvents.Proofs

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Propositional.Syntax LCS.Propositional.Semantics

proof_of resolution_soundness := by
  -- BEGIN PROOF
    -- Unfold isResolutionRefutation to get leaves from S and root = empty
    obtain ⟨hLeaves, hRoot⟩ := hRef
    -- Assume for contradiction that S is satisfiable
    intro ⟨v, hSat⟩
    -- Key claim: every node in the DAG is satisfied by v.
    -- We prove this by showing the set of unsatisfied nodes is empty.
    suffices h_all_sat : ∀ u, (hu : u ∈ D.dag.tree.domain.dom) →
        Clause.satisfies v (D.dag.tree.label u hu) by
      -- Apply to root: root is satisfied
      have hRootSat := h_all_sat [] D.dag.tree.domain.root_mem
      -- But root = empty clause, which has no literals
      rw [show D.dag.tree.label [] D.dag.tree.domain.root_mem = D.rootLabel from rfl] at hRootSat
      rw [hRoot] at hRootSat
      -- Clause.satisfies v Clause.empty = ∃ L ∈ Clause.empty, ... which is False
      obtain ⟨L, hL, _⟩ := hRootSat
      rw [GCNF.Clause.empty] at hL
      exact (LCS.Finset.mem_empty L).mp hL
    -- Derive a depth bound from dom_finite.
    obtain ⟨l, hl⟩ := D.dom_finite
    -- Helper: foldl max result is >= the initial accumulator
    have foldl_ge_init : ∀ (xs : List TreeAddr) (init : Nat),
        init ≤ List.foldl (fun acc (x : TreeAddr) => max acc x.length) init xs := by
      intro xs; induction xs with
      | nil => intro init; exact Nat.le_refl _
      | cons x xs ih =>
        intro init
        simp only [List.foldl_cons]
        exact Nat.le_trans (Nat.le_max_left init x.length) (ih _)
    -- Helper: foldl max is monotone in the initial accumulator
    have foldl_mono : ∀ (xs : List TreeAddr) (a b : Nat), a ≤ b →
        List.foldl (fun acc (x : TreeAddr) => max acc x.length) a xs ≤
        List.foldl (fun acc (x : TreeAddr) => max acc x.length) b xs := by
      intro xs; induction xs with
      | nil => intro a b h; exact h
      | cons x xs ih =>
        intro a b hab
        simp only [List.foldl_cons]
        exact ih _ _ (Nat.max_le.mpr ⟨Nat.le_trans hab (Nat.le_max_left b x.length),
          Nat.le_max_right b x.length⟩)
    -- Helper: every element in the list has length ≤ foldl result
    have foldl_bound : ∀ (xs : List TreeAddr) (init : Nat) (u : TreeAddr),
        u ∈ xs → u.length ≤ List.foldl (fun acc (x : TreeAddr) => max acc x.length) init xs := by
      intro xs; induction xs with
      | nil => intro _ u hu; exact absurd hu List.not_mem_nil
      | cons hd tl ih =>
        intro init u hu
        simp only [List.foldl_cons]
        rcases List.mem_cons.mp hu with rfl | htl
        · exact Nat.le_trans (Nat.le_max_right init u.length) (foldl_ge_init tl _)
        · exact ih _ u htl
    let N := l.foldl (fun acc (a : TreeAddr) => max acc a.length) 0
    have hBound : ∀ u, u ∈ D.dag.tree.domain.dom → u.length ≤ N := by
      intro u hu
      exact foldl_bound l 0 u ((hl u).mp hu)
    -- Use strong induction on (N - u.length): deeper nodes (larger u.length)
    -- are handled first.
    intro u hu
    have hle : u.length ≤ N := hBound u hu
    revert u hu
    suffices ∀ d, ∀ u, u.length ≤ N → N - u.length = d →
        (hu : u ∈ D.dag.tree.domain.dom) → Clause.satisfies v (D.dag.tree.label u hu) by
      intro u hu hle
      exact this (N - u.length) u hle rfl hu
    intro d
    induction d using Nat.strongRecOn with
    | _ d ih =>
    intro u hle hd hu
    -- Case: u is a leaf (no child [0])
    by_cases h_leaf : (u ++ [0]) ∈ D.dag.tree.domain.dom
    · -- u is internal, has children
      have h_child1_dom := D.binary_branching u hu h_leaf
      have h0_le : (u ++ [0]).length ≤ N := hBound _ h_leaf
      have h1_le : (u ++ [1]).length ≤ N := hBound _ h_child1_dom
      have h0_len : (u ++ [0]).length = u.length + 1 := by simp
      have h1_len : (u ++ [1]).length = u.length + 1 := by simp
      have hd_pos : d ≥ 1 := by omega
      have h0_d : N - (u ++ [0]).length < d := by omega
      have h1_d : N - (u ++ [1]).length < d := by omega
      -- Apply IH to both children
      have h_sat0 := ih _ h0_d (u ++ [0]) h0_le (by omega) h_leaf
      have h_sat1 := ih _ h1_d (u ++ [1]) h1_le (by omega) h_child1_dom
      -- By resolvent_at_internal, label(u) = union(remove(C0, L), remove(C1, conj L))
      obtain ⟨L, _, _, hResolvent⟩ := D.resolvent_at_internal u hu h_leaf
      rw [hResolvent]
      exact resolvent_sat _ _ _ v h_sat0 h_sat1
    · -- u is a leaf
      have hFromS := hLeaves u hu h_leaf
      exact hSat (D.dag.tree.label u hu) hFromS

end LCS.Resolution.Method
end
