import LCS.Resolution.Method.RefutationExample

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

helper @[simp] theorem mem_exResolutionRefutation_dom (a : TreeAddr) :
    a ∈ exResolutionRefutation_dom ↔
      a = [] ∨ a = [0] ∨ a = [0, 0] ∨ a = [0, 1] ∨ a = [1] ∨
      a = [1, 0] ∨ a = [1, 0, 0] ∨ a = [1, 0, 1] ∨ a = [1, 1] := Iff.rfl

proof_of exResolutionRefutation_prefix_closed := by
  -- BEGIN PROOF
    intro u v huv
    -- huv : u ++ v ∈ dom, i.e. u ++ v is one of the 9 addresses
    show u = [] ∨ u = [0] ∨ u = [0, 0] ∨ u = [0, 1] ∨
         u = [1] ∨ u = [1, 0] ∨ u = [1, 0, 0] ∨ u = [1, 0, 1] ∨ u = [1, 1]
    rcases huv with h | h | h | h | h | h | h | h | h <;> (
      rcases u with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _⟩⟩⟩⟩ <;>
      simp_all [List.cons_append, List.nil_append]
    )

proof_of exResolutionRefutation_left_sibling_closed := by
  -- BEGIN PROOF
    intro u i huv
    show u ++ [i] = [] ∨ u ++ [i] = [0] ∨ u ++ [i] = [0, 0] ∨ u ++ [i] = [0, 1] ∨
         u ++ [i] = [1] ∨ u ++ [i] = [1, 0] ∨ u ++ [i] = [1, 0, 0] ∨
         u ++ [i] = [1, 0, 1] ∨ u ++ [i] = [1, 1]
    rcases huv with h | h | h | h | h | h | h | h | h <;> (
      rcases u with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _⟩⟩⟩⟩ <;>
      simp_all [List.cons_append, List.nil_append]
    )

proof_of exResolutionRefutation_rel_equiv := ⟨fun _ => Or.inl rfl,
  -- BEGIN PROOF
     fun h => h.elim (fun heq => Or.inl heq.symm)
       (fun h => h.elim (fun ⟨hu, hv⟩ => Or.inr (Or.inr ⟨hv, hu⟩))
         (fun ⟨hu, hv⟩ => Or.inr (Or.inl ⟨hv, hu⟩))),
     fun {x y z} h1 h2 => by
       rcases h1 with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
       · exact h2
       · -- x = [0,0], y = [1,0,0]
         rcases h2 with rfl | ⟨h2a, h2b⟩ | ⟨_, rfl⟩
         · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
         · exact absurd h2a (by decide)
         · exact Or.inl rfl
       · -- x = [1,0,0], y = [0,0]
         rcases h2 with rfl | ⟨_, rfl⟩ | ⟨h2a, _⟩
         · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
         · exact Or.inl rfl
         · exact absurd h2a (by decide)⟩

proof_of exResolutionRefutation_addr_independence := by
  -- BEGIN PROOF
    intro u v huv hne
    rcases huv with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩

proof_of exResolutionRefutation_child_preservation := by
  -- BEGIN PROOF
    intro u v huv i
    rcases huv with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Iff.rfl
    · -- u = [0,0], v = [1,0,0]. Show [0,0,i] ∈ dom ↔ [1,0,0,i] ∈ dom
      constructor
      · intro h
        rcases h with h | h | h | h | h | h | h | h | h <;> simp_all
      · intro h
        rcases h with h | h | h | h | h | h | h | h | h <;> simp_all
    · -- u = [1,0,0], v = [0,0]. Symmetric
      constructor
      · intro h
        rcases h with h | h | h | h | h | h | h | h | h <;> simp_all
      · intro h
        rcases h with h | h | h | h | h | h | h | h | h <;> simp_all

proof_of exResolutionRefutation_child_equivalence := by
  -- BEGIN PROOF
    intro u v huv i hmem
    rcases huv with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · -- u = [0,0], [0,0,i] ∈ dom — impossible
      rcases hmem with h | h | h | h | h | h | h | h | h <;> simp_all
    · -- u = [1,0,0], [1,0,0,i] ∈ dom — impossible
      rcases hmem with h | h | h | h | h | h | h | h | h <;> simp_all

proof_of exResolutionRefutation_label_agreement := by
  -- BEGIN PROOF
    intro u v huv
    rcases huv with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · -- u = [0,0], v = [1,0,0]. Both in domain, same label.
      have h1 : ([0, 0] : TreeAddr) ∈ (exResolutionRefutation_tree P Q).domain.dom :=
        show ([0, 0] : TreeAddr) ∈ exResolutionRefutation_dom from
          Or.inr (Or.inr (Or.inl rfl))
      have h2 : ([1, 0, 0] : TreeAddr) ∈ (exResolutionRefutation_tree P Q).domain.dom :=
        show ([1, 0, 0] : TreeAddr) ∈ exResolutionRefutation_dom from
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      rw [labelAtOpt_of_mem _ _ h1, labelAtOpt_of_mem _ _ h2]
      rfl
    · -- Symmetric case
      have h1 : ([1, 0, 0] : TreeAddr) ∈ (exResolutionRefutation_tree P Q).domain.dom :=
        show ([1, 0, 0] : TreeAddr) ∈ exResolutionRefutation_dom from
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      have h2 : ([0, 0] : TreeAddr) ∈ (exResolutionRefutation_tree P Q).domain.dom :=
        show ([0, 0] : TreeAddr) ∈ exResolutionRefutation_dom from
          Or.inr (Or.inr (Or.inl rfl))
      rw [labelAtOpt_of_mem _ _ h1, labelAtOpt_of_mem _ _ h2]
      rfl

proof_of exResolutionRefutation_binary_branching := by
  -- BEGIN PROOF
    intro u hu h0
    -- u ∈ dom and u ++ [0] ∈ dom. Show u ++ [1] ∈ dom.
    -- Internal nodes: [], [0], [1], [1,0] — their ++ [1] is in domain.
    -- Leaves: [0,0], [0,1], [1,0,0], [1,0,1], [1,1] — h0 is impossible.
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    -- u = []: [] ++ [1] = [1] ∈ dom
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    -- u = [0]: [0] ++ [1] = [0,1] ∈ dom
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    -- u = [0,0] — leaf, h0 : [0,0,0] ∈ dom is impossible
    · exact absurd h0 (by intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp_all)
    -- u = [0,1] — leaf
    · exact absurd h0 (by intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp_all)
    -- u = [1]: [1] ++ [1] = [1,1] ∈ dom
    · change [1, 1] ∈ _; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
    -- u = [1,0]: [1,0] ++ [1] = [1,0,1] ∈ dom
    · change [1, 0, 1] ∈ _; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    -- u = [1,0,0] — leaf
    · exact absurd h0 (by intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp_all)
    -- u = [1,0,1] — leaf
    · exact absurd h0 (by intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp_all)
    -- u = [1,1] — leaf
    · exact absurd h0 (by intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp_all)

proof_of exResolutionRefutation_resolvent_at_internal := by
  intro u hu h0
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨Literal.pos P, ?_, ?_, ?_⟩
    · simp [exResolutionRefutation_dag, exResolutionRefutation_tree,
        exResolutionRefutation_label, GCNF.Clause.ofList]
    · simp [exResolutionRefutation_dag, exResolutionRefutation_tree,
        exResolutionRefutation_label, GCNF.Clause.ofList, Literal.conjugate]
    · apply LCS.Finset.ext
      intro x
      change x ∈ (∅ : Clause) ↔ _
      rw [LCS.Finset.mem_empty]
      cases x <;> simp [exResolutionRefutation_dag, exResolutionRefutation_tree,
        exResolutionRefutation_label, GCNF.Clause.ofList, GCNF.Clause.union,
        GCNF.Clause.remove, LCS.Finset.mem_union_exp, LCS.Finset.mem_erase,
        Literal.conjugate]
  · refine ⟨Literal.pos Q, ?_, ?_, ?_⟩
    all_goals try { simp [exResolutionRefutation_dag, exResolutionRefutation_tree,
    exResolutionRefutation_label, GCNF.Clause.ofList, Literal.conjugate] }
    all_goals
      apply LCS.Finset.ext
      intro x
      cases x <;> simp [exResolutionRefutation_dag, exResolutionRefutation_tree,
      exResolutionRefutation_label, GCNF.Clause.ofList,
      GCNF.Clause.union, GCNF.Clause.remove, LCS.Finset.mem_union_exp,
      LCS.Finset.mem_erase, Literal.conjugate] <;> grind

  · exact absurd h0 (by intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp_all)
  · exact absurd h0 (by intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp_all)
  · refine ⟨Literal.pos Q, ?_, ?_, ?_⟩
    all_goals try { simp [exResolutionRefutation_dag, exResolutionRefutation_tree,
    exResolutionRefutation_label, GCNF.Clause.ofList, Literal.conjugate] }
    all_goals
      apply LCS.Finset.ext
      intro x
      cases x <;> simp [exResolutionRefutation_dag, exResolutionRefutation_tree,
      exResolutionRefutation_label, GCNF.Clause.ofList,
      GCNF.Clause.union, GCNF.Clause.remove, LCS.Finset.mem_union_exp,
      LCS.Finset.mem_erase, Literal.conjugate] <;> grind

  · refine ⟨Literal.pos P, ?_, ?_, ?_⟩
    all_goals try { simp [exResolutionRefutation_dag, exResolutionRefutation_tree,
    exResolutionRefutation_label, GCNF.Clause.ofList, Literal.conjugate] }
    all_goals
      apply LCS.Finset.ext
      intro x
      cases x <;> simp [exResolutionRefutation_dag, exResolutionRefutation_tree,
      exResolutionRefutation_label, GCNF.Clause.ofList,
      GCNF.Clause.union, GCNF.Clause.remove, LCS.Finset.mem_union_exp,
      LCS.Finset.mem_erase, Literal.conjugate] <;> grind

  · exact absurd h0 (by intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp_all)
  · exact absurd h0 (by intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp_all)
  · exact absurd h0 (by intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp_all)

proof_of exResolutionRefutation_correct := by
  refine ⟨?_, rfl⟩
  intro u hu hLeaf
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [exResolutionRefutation, exResolutionRefutation_dag,
      exResolutionRefutation_tree, exResolutionRefutation_domain,
      mem_exResolutionRefutation_dom, exResolutionRefutation_label,
      exResolutionRefutationInput, GCNF.ClauseSequent.ofList] <;>
    first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr (Or.inl rfl))
    | exact Or.inr (Or.inr (Or.inr rfl))

end LCS.Resolution.Method
end
