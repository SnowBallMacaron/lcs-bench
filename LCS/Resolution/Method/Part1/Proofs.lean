import LCS.Resolution.Method.Part1

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF

proof_of labelAtOpt_of_mem := by
  -- BEGIN PROOF
    unfold labelAtOpt; simp [h]

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace DAG

helper theorem suffixCongruence (d : DAG Delta) {u v : TreeAddr}
    (hu : u ∈ d.tree.domain.dom) (hv : v ∈ d.tree.domain.dom) (h : d.rel u v)
    (w : TreeAddr) :
    (u ++ w ∈ d.tree.domain.dom ↔ v ++ w ∈ d.tree.domain.dom) ∧
    (u ++ w ∈ d.tree.domain.dom → d.rel (u ++ w) (v ++ w)) := by
  induction w generalizing u v with
  | nil => simpa using And.intro (show (u ∈ d.tree.domain.dom ↔ v ∈ d.tree.domain.dom) from ⟨fun _ => hv, fun _ => hu⟩) (fun _ => h)
  | cons i w ih =>
    have cp := d.child_preservation u v h i
    have forward : u ++ i :: w ∈ d.tree.domain.dom →
        v ++ i :: w ∈ d.tree.domain.dom ∧ d.rel (u ++ i :: w) (v ++ i :: w) := by
      intro huw
      have hui : u ++ [i] ∈ d.tree.domain.dom :=
        d.tree.domain.prefix_closed (u ++ [i]) w (by simpa [List.append_assoc] using huw)
      have hvi := cp.mp hui
      have hs := ih hui hvi (d.child_equivalence u v h i hui)
      have hw : (u ++ [i]) ++ w ∈ d.tree.domain.dom := by simpa [List.append_assoc] using huw
      simpa [List.append_assoc] using And.intro (hs.1.mp hw) (hs.2 hw)
    constructor
    · constructor
      · exact fun huw => (forward huw).1
      · intro hvw
        have hvi : v ++ [i] ∈ d.tree.domain.dom :=
          d.tree.domain.prefix_closed (v ++ [i]) w (by simpa [List.append_assoc] using hvw)
        have hui := cp.mpr hvi
        have hs := ih hui hvi (d.child_equivalence u v h i hui)
        have hw : (v ++ [i]) ++ w ∈ d.tree.domain.dom := by simpa [List.append_assoc] using hvw
        simpa [List.append_assoc] using hs.1.mpr hw
    · exact fun huw => (forward huw).2

end DAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace DAG

helper theorem equivalentSubtrees (d : DAG Delta) {u v : TreeAddr}
    (hu : u ∈ d.tree.domain.dom) (hv : v ∈ d.tree.domain.dom) (h : d.rel u v) :
    ∀ w, (u ++ w ∈ d.tree.domain.dom ↔ v ++ w ∈ d.tree.domain.dom) ∧
      labelAtOpt d.tree (u ++ w) = labelAtOpt d.tree (v ++ w) := by
  intro w
  have hc := suffixCongruence d hu hv h w
  refine ⟨hc.1, ?_⟩
  by_cases huw : u ++ w ∈ d.tree.domain.dom
  · exact d.label_agreement _ _ (hc.2 huw)
  · have hvw : ¬ v ++ w ∈ d.tree.domain.dom := fun hvw => huw (hc.1.mpr hvw)
    simp [labelAtOpt, huw, hvw]

end DAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace DAG

helper theorem directedPathLift (d : DAG Delta) {S T : Set TreeAddr} {n : Nat}
    (hp : DirectedPath d S T n) {u : TreeAddr}
    (hu : u ∈ d.tree.domain.dom) (hS : S = d.eqClass u) :
    ∃ w, w.length = n ∧ u ++ w ∈ d.tree.domain.dom ∧ T = d.eqClass (u ++ w) := by
  induction hp generalizing u with
  | nil _ => exact ⟨[], rfl, by simpa using hu, by simpa using hS⟩
  | @cons S V T n he hp ih =>
    obtain ⟨v, i, hv, hvi, hSv, hV⟩ := he
    have huv : d.rel u v := rel_of_eqClass_eq d (hS.symm.trans hSv)
    have hui : u ++ [i] ∈ d.tree.domain.dom :=
      (d.child_preservation u v huv i).mpr hvi
    have hrel := d.child_equivalence u v huv i hui
    have hVu : V = d.eqClass (u ++ [i]) := hV.trans (eqClass_eq_of_rel d hrel).symm
    obtain ⟨w, hw, huw, hT⟩ := ih hui hVu
    refine ⟨i :: w, by simp [hw], ?_, ?_⟩
    · simpa [List.append_assoc] using huw
    · simpa [List.append_assoc] using hT

end DAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace DAG

helper theorem noDirectedCycle (d : DAG Delta) {S : Set TreeAddr} {n : Nat}
    (hp : DirectedPath d S S n) : n = 0 := by
  have hnode : S ∈ d.nodes := by
    cases hp with
    | nil h => exact h
    | cons h _ =>
      obtain ⟨u, i, hu, _, hS, _⟩ := h
      exact ⟨u, hu, hS⟩
  obtain ⟨u, hu, hS⟩ := hnode
  obtain ⟨w, hw, huw, hSw⟩ := directedPathLift d hp hu hS
  have hur : d.rel u (u ++ w) := rel_of_eqClass_eq d (hS.symm.trans hSw)
  have heq : u = u ++ w := by
    apply Classical.byContradiction
    intro hne
    have hi := (d.addr_independence u (u ++ w) hur hne).1
    exact hi (by simp)
  have hl := congrArg List.length heq
  simp only [List.length_append] at hl
  omega

end DAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace DAG

helper theorem directedPathEndpoints (d : DAG Delta) {S T : Set TreeAddr} {n : Nat}
    (hp : DirectedPath d S T n) : S ∈ d.nodes ∧ T ∈ d.nodes := by
  induction hp with
  | nil h => exact ⟨h, h⟩
  | cons he _ ih =>
    obtain ⟨u, i, hu, _, hS, _⟩ := he
    exact ⟨⟨u, hu, hS⟩, ih.2⟩

end DAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace DAG

helper theorem directedPathOfSuffix (d : DAG Delta) (u w : TreeAddr)
    (huw : u ++ w ∈ d.tree.domain.dom) :
    DirectedPath d (d.eqClass u) (d.eqClass (u ++ w)) w.length := by
  induction w generalizing u with
  | nil =>
    simpa using DirectedPath.nil (d := d) (S := d.eqClass u) ⟨u, by simpa using huw, rfl⟩
  | cons i w ih =>
    have hu : u ∈ d.tree.domain.dom := d.tree.domain.prefix_closed u (i :: w) huw
    have hui : u ++ [i] ∈ d.tree.domain.dom :=
      d.tree.domain.prefix_closed (u ++ [i]) w (by simpa [List.append_assoc] using huw)
    have hp := ih (u ++ [i]) (by simpa [List.append_assoc] using huw)
    have he : (d.eqClass u, d.eqClass (u ++ [i])) ∈ d.edges :=
      ⟨u, i, hu, hui, rfl, rfl⟩
    simpa [List.append_assoc] using DirectedPath.cons he hp

end DAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace DAG

helper theorem pathBetween_iff_descendant (d : DAG Delta) (S T : Set TreeAddr) :
    pathBetween d S T ↔ isDescendant d T S := by
  constructor
  · intro ⟨n, hp⟩
    obtain ⟨u, hu, hS⟩ := (directedPathEndpoints d hp).1
    obtain ⟨w, _, huw, hT⟩ := directedPathLift d hp hu hS
    exact ⟨u ++ w, u, huw, hu, hT, hS, by simp⟩
  · intro ⟨u, v, hu, hv, hT, hS, hpref⟩
    obtain ⟨w, hw⟩ := List.isPrefixOf_iff_prefix.mp hpref
    refine ⟨w.length, ?_⟩
    rw [hT, hS, ← hw]
    exact directedPathOfSuffix d v w (by simpa [hw] using hu)

end DAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace DAG

helper theorem rootReachesEveryNode (d : DAG Delta) {S : Set TreeAddr}
    (hS : S ∈ d.nodes) : pathBetween d d.root S := by
  obtain ⟨u, hu, rfl⟩ := hS
  exact ⟨u.length, by simpa [LCS.Resolution.Method.DAG.root] using
    directedPathOfSuffix d [] u (by simpa using hu)⟩

end DAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace DAG

proof_of InfinitePath.successiveEdges := by
  refine ⟨p.address n, p.successor n, p.inDomain n, ?_, rfl, ?_⟩
  · rw [← p.next n]
    exact p.inDomain (n + 1)
  · change d.eqClass (p.address (n + 1)) = _
    rw [p.next n]

end DAG
end LCS.Resolution.Method
end

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

end ResolutionDAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionDAG

proof_of mk_axiom_left_sibling_closed := by
  -- BEGIN PROOF
    intro u i (h : u ++ [i + 1] = [])
    -- u ++ [i+1] = [] is impossible
    cases u with
    | nil => simp at h
    | cons hd tl => simp at h

end ResolutionDAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionDAG

proof_of mk_axiom_addr_independence := by
  -- BEGIN PROOF
    intro u v huv hne; exact absurd huv hne

end ResolutionDAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionDAG

proof_of mk_axiom_child_preservation := by
  -- BEGIN PROOF
    intro u v huv i; subst huv; exact Iff.rfl

end ResolutionDAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionDAG

proof_of mk_axiom_child_equivalence := by
  -- BEGIN PROOF
    intro u v huv i _; subst huv; rfl

end ResolutionDAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionDAG

proof_of mk_axiom_label_agreement := by
  -- BEGIN PROOF
    intro u v huv; subst huv; rfl

end ResolutionDAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionDAG

proof_of mk_axiom_binary_branching := by
  -- BEGIN PROOF
    intro u hu h0
    -- u ∈ dom means u = [], so u ++ [0] = [0] must be in dom,
    -- but [0] ≠ [], contradiction
    have hu' : u = [] := (hdom u).mp hu
    subst hu'
    exact absurd ((hdom _).mp h0) (by show ¬([0] = []); simp)

end ResolutionDAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionDAG

proof_of mk_axiom_resolvent_at_internal := by
  -- BEGIN PROOF
    intro u hu h0
    have hu' : u = [] := (hdom u).mp hu
    subst hu'
    exact absurd ((hdom _).mp h0) (by show ¬([0] = []); simp)

end ResolutionDAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionDAG

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

end ResolutionDAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionDAG

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

end ResolutionDAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionDAG

proof_of mk_resolve_addr_independence := by
  -- BEGIN PROOF
    intro u v huv hne; exact absurd huv hne

end ResolutionDAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionDAG

proof_of mk_resolve_child_preservation := by
  -- BEGIN PROOF
    intro u v huv i; subst huv; exact Iff.rfl

end ResolutionDAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionDAG

proof_of mk_resolve_child_equivalence := by
  -- BEGIN PROOF
    intro u v huv i _; subst huv; rfl

end ResolutionDAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionDAG

proof_of mk_resolve_label_agreement := by
  -- BEGIN PROOF
    intro u v huv; subst huv; rfl

end ResolutionDAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionDAG

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

end ResolutionDAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionDAG

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

end ResolutionDAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionDAG

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

end ResolutionDAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionDAG

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

end ResolutionDAG
end LCS.Resolution.Method
end
