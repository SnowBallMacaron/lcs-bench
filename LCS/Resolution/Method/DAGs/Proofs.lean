import LCS.Resolution.Method.DAGs

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF

proof_of labelAtOpt_of_mem := by
  -- BEGIN PROOF
    unfold labelAtOpt; simp [h]

proof_of exDAGTreeDomain_root_mem := by
  -- BEGIN PROOF
    show ([] : TreeAddr) ∈ ([[], [0], [1], [1,0], [1,1], [1,0,0], [1,0,1], [1,1,0], [1,1,1]] : List TreeAddr)
    simp

proof_of exDAGTreeDomain_prefix_closed := by
  -- BEGIN PROOF
    intro u v h
    unfold exDAGTreeAddrs at h ⊢
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢
    rcases h with h | h | h | h | h | h | h | h | h
    · left; exact (List.append_eq_nil_iff.mp h).1
    all_goals (
      rcases u with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _⟩⟩⟩⟩ <;>
        simp_all (config := { decide := false }) <;>
        dsimp only [Membership.mem] <;>
        simp)

proof_of exDAGTreeDomain_left_sibling_closed := by
  -- BEGIN PROOF
    intro u i h
    unfold exDAGTreeAddrs at h ⊢
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢
    rcases h with h | h | h | h | h | h | h | h | h
    all_goals (
      rcases u with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _⟩⟩⟩⟩ <;>
        simp_all (config := { decide := false }) <;>
        first
        | omega
        | (dsimp only [Membership.mem]; simp_all (config := { decide := false }); try omega))

proof_of exDAG_mem_dom_iff := Iff.rfl

proof_of exDAG_mem_10 := by
  -- BEGIN PROOF
    rw [exDAG_mem_dom_iff]; simp [exDAGAddrs]

proof_of exDAG_mem_11 := by
  -- BEGIN PROOF
    rw [exDAG_mem_dom_iff]; simp [exDAGAddrs]

proof_of exCollapsedDAG_rel_equiv := by
  -- BEGIN PROOF
    constructor
    · -- refl
      intro x; left; rfl
    · -- symm
      intro x y hxy
      rcases hxy with rfl | hxy | hxy
      · left; rfl
      · right; left
        rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact Or.inr ⟨hy, hx⟩
        · exact Or.inl ⟨hy, hx⟩
      · right; right
        exact ⟨hxy.2, hxy.1⟩
    · -- trans
      intro x y z hxy hyz
      rcases hxy with rfl | hxy | hxy
      · exact hyz
      · rcases hyz with rfl | hyz | hyz
        · right; left; exact hxy
        · -- x ~ y via [1,0]/[1,1], y ~ z via [1,0]/[1,1]
          rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;>
          rcases hyz with ⟨hy2, hz⟩ | ⟨hy2, hz⟩ <;>
          subst_eqs <;>
          first | (left; rfl) | (exact absurd hy2 (by decide))
        · -- x ~ y via [1,0]/[1,1], y ~ z via leaf set
          rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> simp_all
      · rcases hyz with rfl | hyz | hyz
        · right; right; exact hxy
        · -- x ~ y via leaf set, y ~ z via [1,0]/[1,1]
          rcases hyz with ⟨hy2, hz⟩ | ⟨hy2, hz⟩ <;> simp_all
        · right; right; exact ⟨hxy.1, hyz.2⟩

proof_of exCollapsedDAG_addr_independence := by
  -- BEGIN PROOF
    intro u v hrel hne
    rcases hrel with rfl | hrel | hrel
    · exact absurd rfl hne
    · rcases hrel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [List.isPrefixOf]
    · obtain ⟨hu, hv⟩ := hrel
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu hv
      rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl hne | simp [List.isPrefixOf]

proof_of exCollapsedDAG_child_preservation := by
  -- BEGIN PROOF
    intro u v hrel i
    rcases hrel with rfl | hrel | hrel
    · exact Iff.rfl
    · rcases hrel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [List.cons_append, List.nil_append] <;> (
        rw [exDAG_mem_dom_iff, exDAG_mem_dom_iff]
        simp only [exDAGAddrs, List.mem_cons, List.mem_nil_iff, or_false]
        constructor
        · intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp_all
        · intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp_all)
    · obtain ⟨hu, hv⟩ := hrel
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu hv
      constructor
      · intro h
        rw [exDAG_mem_dom_iff] at h ⊢
        simp only [exDAGAddrs, List.mem_cons, List.mem_nil_iff, or_false] at h ⊢
        rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;>
          (rcases h with h | h | h | h | h | h | h | h | h <;> simp_all)
      · intro h
        rw [exDAG_mem_dom_iff] at h ⊢
        simp only [exDAGAddrs, List.mem_cons, List.mem_nil_iff, or_false] at h ⊢
        rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;>
          (rcases h with h | h | h | h | h | h | h | h | h <;> simp_all)

proof_of exCollapsedDAG_child_equivalence := by
  -- BEGIN PROOF
    intro u v hrel i hmem
    rcases hrel with rfl | hrel | hrel
    · left; rfl
    · rcases hrel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [List.cons_append, List.nil_append]
      all_goals (
        rw [exDAG_mem_dom_iff] at hmem
        simp only [exDAGAddrs, List.mem_cons, List.mem_nil_iff, or_false] at hmem
        rcases hmem with h | h | h | h | h | h | h | h | h <;> simp_all
        all_goals (right; right; exact ⟨by simp, by simp⟩))
    · -- leaf set: no children, vacuously true
      obtain ⟨hu, _⟩ := hrel
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
      rw [exDAG_mem_dom_iff] at hmem
      simp only [exDAGAddrs, List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hu with rfl | rfl | rfl | rfl <;>
        (rcases hmem with h | h | h | h | h | h | h | h | h <;> simp_all)

proof_of exCollapsedDAG_label_agreement := by
  -- BEGIN PROOF
    intro u v hrel
    rcases hrel with rfl | hrel | hrel
    · rfl
    · -- [1,0] ~ [1,1]: both labeled 'f'
      rcases hrel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> (
        simp only [labelAtOpt_of_mem _ _ exDAG_mem_10, labelAtOpt_of_mem _ _ exDAG_mem_11]
        rfl)
    · -- leaf set: all labeled 'b'
      obtain ⟨hu, hv⟩ := hrel
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu hv
      rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;> (
        first
        | rfl
        | (rw [labelAtOpt_of_mem _ _ (by rw [exDAG_mem_dom_iff]; simp [exDAGAddrs]),
               labelAtOpt_of_mem _ _ (by rw [exDAG_mem_dom_iff]; simp [exDAGAddrs])]; rfl))

end LCS.Resolution.Method
end
