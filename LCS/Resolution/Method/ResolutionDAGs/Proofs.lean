import LCS.Resolution.Method.ResolutionDAGs

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionDAG

proof_of mk_axiom_prefix_closed := by
  -- BEGIN PROOF
    intro u v h
    have : u ++ v = [] := h
    exact (List.append_eq_nil_iff.mp this).1

proof_of mk_axiom_left_sibling_closed := by
  -- BEGIN PROOF
    intro u i (h : u ++ [i + 1] = [])
    -- u ++ [i+1] = [] is impossible
    cases u with
    | nil => simp at h
    | cons hd tl => simp at h

proof_of mk_axiom_addr_independence := by
  -- BEGIN PROOF
    intro u v huv hne; exact absurd huv hne

proof_of mk_axiom_child_preservation := by
  -- BEGIN PROOF
    intro u v huv i; subst huv; exact Iff.rfl

proof_of mk_axiom_child_equivalence := by
  -- BEGIN PROOF
    intro u v huv i _; subst huv; rfl

proof_of mk_axiom_label_agreement := by
  -- BEGIN PROOF
    intro u v huv; subst huv; rfl

proof_of mk_axiom_binary_branching := by
  -- BEGIN PROOF
    intro u hu h0
    -- u ∈ dom means u = [], so u ++ [0] = [0] must be in dom,
    -- but [0] ≠ [], contradiction
    have hu' : u = [] := (hdom u).mp hu
    subst hu'
    exact absurd ((hdom _).mp h0) (by show ¬([0] = []); simp)

proof_of mk_axiom_resolvent_at_internal := by
  -- BEGIN PROOF
    intro u hu h0
    have hu' : u = [] := (hdom u).mp hu
    subst hu'
    exact absurd ((hdom _).mp h0) (by show ¬([0] = []); simp)

proof_of mk_resolve_prefix_closed := by
  -- BEGIN PROOF
    intro u v h
    rcases h with heq | ⟨t, ht_eq, ht_mem⟩ | ⟨t, ht_eq, ht_mem⟩
    · exact Or.inl (List.append_eq_nil_iff.mp heq).1
    · -- u ++ v = 0 :: t, t ∈ D1
      cases u with
      | nil => exact Or.inl rfl
      | cons hd tl =>
        simp at ht_eq
        obtain ⟨rfl, rfl⟩ := ht_eq
        exact Or.inr (Or.inl ⟨tl, rfl, D1.dag.tree.domain.prefix_closed tl v ht_mem⟩)
    · cases u with
      | nil => exact Or.inl rfl
      | cons hd tl =>
        simp at ht_eq
        obtain ⟨rfl, rfl⟩ := ht_eq
        exact Or.inr (Or.inr ⟨tl, rfl, D2.dag.tree.domain.prefix_closed tl v ht_mem⟩)

proof_of mk_resolve_left_sibling_closed := by
  -- BEGIN PROOF
    intro u i h
    rcases h with heq | ⟨t, ht_eq, ht_mem⟩ | ⟨t, ht_eq, ht_mem⟩
    · -- u ++ [i + 1] = [] is impossible
      exact absurd heq (by simp)
    · -- u ++ [i + 1] = 0 :: t, t ∈ D1
      cases u with
      | nil =>
        -- [i + 1] = 0 :: t, so i + 1 = 0 — impossible
        simp at ht_eq
      | cons hd tl =>
        simp at ht_eq
        obtain ⟨rfl, rfl⟩ := ht_eq
        exact Or.inr (Or.inl ⟨tl ++ [i], by simp, D1.dag.tree.domain.left_sibling_closed tl i ht_mem⟩)
    · cases u with
      | nil =>
        -- [i + 1] = 1 :: t
        simp at ht_eq
        obtain ⟨rfl, rfl⟩ := ht_eq
        -- i = 0, so we need [0] in domain
        exact Or.inr (Or.inl ⟨[], by simp, D1.dag.tree.domain.root_mem⟩)
      | cons hd tl =>
        simp at ht_eq
        obtain ⟨rfl, rfl⟩ := ht_eq
        exact Or.inr (Or.inr ⟨tl ++ [i], by simp, D2.dag.tree.domain.left_sibling_closed tl i ht_mem⟩)

proof_of mk_resolve_addr_independence := by
  -- BEGIN PROOF
    intro u v huv hne; exact absurd huv hne

proof_of mk_resolve_child_preservation := by
  -- BEGIN PROOF
    intro u v huv i; subst huv; exact Iff.rfl

proof_of mk_resolve_child_equivalence := by
  -- BEGIN PROOF
    intro u v huv i _; subst huv; rfl

proof_of mk_resolve_label_agreement := by
  -- BEGIN PROOF
    intro u v huv; subst huv; rfl

proof_of mk_resolve_binary_branching := by
  -- BEGIN PROOF
    intro u hu h0
    rcases hu with rfl | ⟨t, rfl, ht_mem⟩ | ⟨t, rfl, ht_mem⟩
    · -- u = [], child [0] present → [1] present (D2 root)
      exact Or.inr (Or.inr ⟨[], rfl, D2.dag.tree.domain.root_mem⟩)
    · -- u = 0 :: t, child (0 :: t) ++ [0] present → (0 :: t) ++ [1]
      simp only [List.cons_append] at h0 ⊢
      have h0' : (t ++ [0]) ∈ D1.dag.tree.domain.dom := by
        rcases h0 with h | ⟨t', ht_eq, ht_mem'⟩ | ⟨t', ht_eq, _⟩
        · exact absurd h (List.cons_ne_nil _ _)
        · exact (List.cons.inj ht_eq).2 ▸ ht_mem'
        · exact absurd (List.cons.inj ht_eq).1 (by omega)
      exact Or.inr (Or.inl ⟨t ++ [1], rfl, D1.binary_branching t ht_mem h0'⟩)
    · -- u = 1 :: t, child (1 :: t) ++ [0] → (1 :: t) ++ [1]
      simp only [List.cons_append] at h0 ⊢
      have h0' : (t ++ [0]) ∈ D2.dag.tree.domain.dom := by
        rcases h0 with h | ⟨t', ht_eq, _⟩ | ⟨t', ht_eq, ht_mem'⟩
        · exact absurd h (List.cons_ne_nil _ _)
        · exact absurd (List.cons.inj ht_eq).1 (by omega)
        · exact (List.cons.inj ht_eq).2 ▸ ht_mem'
      exact Or.inr (Or.inr ⟨t ++ [1], rfl, D2.binary_branching t ht_mem h0'⟩)

proof_of mk_resolve_children_binary := by
  intro u hu i hi
  rcases hu with rfl | ⟨t, rfl, ht⟩ | ⟨t, rfl, ht⟩
  · rcases hi with h | ⟨t, h, ht⟩ | ⟨t, h, ht⟩
    · simp at h
    · have := (List.cons.inj h).1; omega
    · have := (List.cons.inj h).1; omega
  · rcases hi with h | ⟨t', h, ht'⟩ | ⟨t', h, ht'⟩
    · simp at h
    · have heq : t ++ [i] = t' := (List.cons.inj h).2
      subst t'
      exact D1.children_binary t ht i ht'
    · have := (List.cons.inj h).1; omega
  · rcases hi with h | ⟨t', h, ht'⟩ | ⟨t', h, ht'⟩
    · simp at h
    · have := (List.cons.inj h).1; omega
    · have heq : t ++ [i] = t' := (List.cons.inj h).2
      subst t'
      exact D2.children_binary t ht i ht'

proof_of mk_resolve_resolvent_at_internal := by
  -- BEGIN PROOF
    intro u hu h0
    rcases hu with rfl | ⟨t, rfl, ht_mem⟩ | ⟨t, rfl, ht_mem⟩
    · -- u = [], root: label = union (remove D1.root L) (remove D2.root (conj L))
      refine ⟨L, ?_, ?_, ?_⟩
      · simpa [mk_resolve_dag, mk_resolve_tree, mk_resolve_label, rootLabel] using hL
      · simpa [mk_resolve_dag, mk_resolve_tree, mk_resolve_label, rootLabel] using hLc
      show (mk_resolve_dag D1 D2 L).tree.label [] _ = _
      unfold mk_resolve_dag mk_resolve_tree mk_resolve_label
      simp
      unfold ResolutionDAG.rootLabel
      rfl
    · -- u = 0 :: t, label at 0::t = D1.label at t
      simp only [List.cons_append] at h0 ⊢
      have h0' : (t ++ [0]) ∈ D1.dag.tree.domain.dom := by
        rcases h0 with h | ⟨t', ht_eq, ht_mem'⟩ | ⟨t', ht_eq, _⟩
        · exact absurd h (List.cons_ne_nil _ _)
        · exact (List.cons.inj ht_eq).2 ▸ ht_mem'
        · exact absurd (List.cons.inj ht_eq).1 (by omega)
      obtain ⟨L', hMem, hMemc, hL'⟩ := D1.resolvent_at_internal t ht_mem h0'
      refine ⟨L', ?_, ?_, ?_⟩
      · simpa [mk_resolve_dag, mk_resolve_tree, mk_resolve_label] using hMem
      · simpa [mk_resolve_dag, mk_resolve_tree, mk_resolve_label] using hMemc
      show (mk_resolve_dag D1 D2 L).tree.label _ _ = _
      unfold mk_resolve_dag mk_resolve_tree mk_resolve_label
      simp [show (0 :: t ≠ []) from List.cons_ne_nil _ _]
      exact hL'
    · -- u = 1 :: t, label at 1::t = D2.label at t
      simp only [List.cons_append] at h0 ⊢
      have h0' : (t ++ [0]) ∈ D2.dag.tree.domain.dom := by
        rcases h0 with h | ⟨t', ht_eq, _⟩ | ⟨t', ht_eq, ht_mem'⟩
        · exact absurd h (List.cons_ne_nil _ _)
        · exact absurd (List.cons.inj ht_eq).1 (by omega)
        · exact (List.cons.inj ht_eq).2 ▸ ht_mem'
      obtain ⟨L', hMem, hMemc, hL'⟩ := D2.resolvent_at_internal t ht_mem h0'
      refine ⟨L', ?_, ?_, ?_⟩
      · simpa [mk_resolve_dag, mk_resolve_tree, mk_resolve_label] using hMem
      · simpa [mk_resolve_dag, mk_resolve_tree, mk_resolve_label] using hMemc
      show (mk_resolve_dag D1 D2 L).tree.label _ _ = _
      unfold mk_resolve_dag mk_resolve_tree mk_resolve_label
      simp [show (1 :: t ≠ []) from List.cons_ne_nil _ _]
      exact hL'

proof_of mk_resolve_dom_finite := by
  -- BEGIN PROOF
    obtain ⟨l1, hl1⟩ := D1.dom_finite
    obtain ⟨l2, hl2⟩ := D2.dom_finite
    refine ⟨[] :: (l1.map (0 :: ·)) ++ (l2.map (1 :: ·)), fun a => ?_⟩
    constructor
    · intro ha
      rcases ha with rfl | ⟨t, rfl, ht_mem⟩ | ⟨t, rfl, ht_mem⟩
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl
          (List.mem_map.mpr ⟨t, (hl1 t).mp ht_mem, rfl⟩))))
      · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr
          (List.mem_map.mpr ⟨t, (hl2 t).mp ht_mem, rfl⟩))))
    · intro ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inl rfl
      · rcases List.mem_append.mp ha with h1 | h2
        · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h1
          exact Or.inr (Or.inl ⟨t, rfl, (hl1 t).mpr ht⟩)
        · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h2
          exact Or.inr (Or.inr ⟨t, rfl, (hl2 t).mpr ht⟩)

helper /-- The root label of mk_axiom C is C. -/
theorem rootLabel_axiom (C : Clause) : (mk_axiom C).rootLabel = C := by
-- BEGIN PROOF
  unfold rootLabel mk_axiom
  rfl

end ResolutionDAG
end LCS.Resolution.Method
end
