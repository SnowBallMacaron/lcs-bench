import LCS.Resolution.Method.Part2

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionDAG

helper /-- The root label of mk_axiom C is C. -/
theorem rootLabel_axiom (C : Clause) : (mk_axiom C).rootLabel = C := by
-- BEGIN PROOF
  unfold rootLabel mk_axiom
  rfl

end ResolutionDAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionDAG

helper theorem nodeCount_eq_of_representatives (D : ResolutionDAG) (reps : List TreeAddr)
    (hrep : ∀ u ∈ reps, u ∈ D.dag.tree.domain.dom)
    (hnodup : (reps.map (Quotient.mk ⟨D.dag.rel, D.dag.rel_equiv⟩)).Nodup)
    (hcover : ∀ u, u ∈ D.dag.tree.domain.dom → ∃ v ∈ reps, D.dag.rel u v) :
    D.nodeCount = reps.length := by
  classical
  unfold LCS.Resolution.Method.ResolutionDAG.nodeCount
  dsimp only
  apply @quotientCount_eq_of_representatives TreeAddr ⟨D.dag.rel, D.dag.rel_equiv⟩
    (fun _ _ => Classical.propDecidable _)
  · intro v hv
    exact (D.dom_finite.choose_spec v).mp (hrep v hv)
  · exact hnodup
  · intro u hu
    exact hcover u ((D.dom_finite.choose_spec u).mpr hu)

end ResolutionDAG
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionForest

proof_of refutation_iff := by
  constructor
  · rintro ⟨F, D, hF, hRoot⟩
    exact ⟨D, F.leavesFrom D (by rw [hF]; rfl), hRoot⟩
  · rintro ⟨D, hLeaves, hRoot⟩
    exact ⟨singleton D hLeaves, D, rfl, hRoot⟩

end ResolutionForest
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionForest

proof_of emptyClauseRefutation := ⟨(ResolutionDAG.leavesFrom_axiom _ S).mpr h, rfl⟩

end ResolutionForest
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionForest

proof_of emptyClauseRefutation_zeroSteps := by
  apply ResolutionDAG.stepCount_eq_of_representatives _ []
  · intro u hu; cases hu
  · exact List.nodup_nil
  · intro u hu hChild
    have hu' : u = [] := hu
    subst u
    have : ([0] : TreeAddr) = [] := hChild
    contradiction

end ResolutionForest
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionTree
open LCS.Resolution.GCNF

helper theorem toResolutionDAG_rootLabel (T : ResolutionTree) (h : T.IsWellFormed) :
    (T.toResolutionDAG h).rootLabel = T.label :=
  (T.toResolutionDAGWithLabel h).property

end ResolutionTree
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionTree
open LCS.Resolution.GCNF

helper theorem toResolutionDAG_leavesFrom (T : ResolutionTree) (h : T.IsWellFormed)
    (S : ClauseSequent) : T.leavesFrom S → (T.toResolutionDAG h).leavesFrom S := by
  induction T with
  | axiom_ C => exact (ResolutionDAG.leavesFrom_axiom C S).mpr
  | resolve T1 T2 L ih1 ih2 =>
    intro ⟨h1, h2⟩
    apply (ResolutionDAG.leavesFrom_resolve _ _ _
      ((toResolutionDAG_rootLabel T1 h.1).symm ▸ h.2.2.1)
      ((toResolutionDAG_rootLabel T2 h.2.1).symm ▸ h.2.2.2) S).mpr
    exact ⟨ih1 h.1 h1, ih2 h.2.1 h2⟩

end ResolutionTree
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF

proof_of exDAGTreeDomain_root_mem := by
  -- BEGIN PROOF
    show ([] : TreeAddr) ∈ ([[], [0], [1], [1,0], [1,1], [1,0,0], [1,0,1], [1,1,0], [1,1,1]] : List TreeAddr)
    simp

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF

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

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF

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

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF

proof_of exDAG_mem_dom_iff := Iff.rfl

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF

proof_of exDAG_mem_10 := by
  -- BEGIN PROOF
    rw [exDAG_mem_dom_iff]; simp [exDAGAddrs]

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF

proof_of exDAG_mem_11 := by
  -- BEGIN PROOF
    rw [exDAG_mem_dom_iff]; simp [exDAGAddrs]

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF

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

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF

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

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF

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

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF

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

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF

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

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

helper theorem removePairFirst (L M : Literal) (h : L ≠ M) :
    GCNF.Clause.remove (GCNF.Clause.ofList [L, M]) L = GCNF.Clause.single M := by
  apply LCS.Finset.ext
  intro x
  simp only [GCNF.Clause.remove, LCS.Finset.mem_erase, GCNF.Clause.ofList,
    LCS.Finset.mem_ofList, List.mem_cons, List.not_mem_nil, or_false,
    GCNF.Clause.single, LCS.Finset.mem_singleton]
  constructor
  · intro ⟨hx, hne⟩
    exact hx.elim (fun he => False.elim (hne he)) id
  · intro hx
    subst x
    exact ⟨Or.inr rfl, Ne.symm h⟩

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

helper theorem removePairSecond (L M : Literal) (h : L ≠ M) :
    GCNF.Clause.remove (GCNF.Clause.ofList [L, M]) M = GCNF.Clause.single L := by
  apply LCS.Finset.ext
  intro x
  simp only [GCNF.Clause.remove, LCS.Finset.mem_erase, GCNF.Clause.ofList,
    LCS.Finset.mem_ofList, List.mem_cons, List.not_mem_nil, or_false,
    GCNF.Clause.single, LCS.Finset.mem_singleton]
  constructor
  · intro ⟨hx, hne⟩
    exact hx.elim id (fun he => False.elim (hne he))
  · intro hx
    subst x
    exact ⟨Or.inl rfl, h⟩

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

helper theorem unionSingles (L M : Literal) :
    GCNF.Clause.union (GCNF.Clause.single L) (GCNF.Clause.single M) =
      GCNF.Clause.ofList [L, M] := by
  apply LCS.Finset.ext
  intro x
  simp [GCNF.Clause.union, GCNF.Clause.single, GCNF.Clause.ofList,
    LCS.Finset.mem_union_exp, LCS.Finset.mem_singleton]

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

proof_of exampleTwoResolvents := by
  have hPos : Literal.pos A ≠ Literal.pos B := fun h => hAB (Literal.pos.inj h)
  have hNeg : Literal.neg A ≠ Literal.neg B := fun h => hAB (Literal.neg.inj h)
  constructor
  · rintro ⟨L, hL, _, hC⟩
    simp only [GCNF.Clause.ofList, LCS.Finset.mem_ofList, List.mem_cons,
      List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl
    · right
      simpa only [Clause.remove, Literal.conjugate, removePairFirst _ _ hPos,
        removePairFirst _ _ hNeg, unionSingles] using hC
    · left
      simpa only [Clause.remove, Literal.conjugate, removePairSecond _ _ hPos,
        removePairSecond _ _ hNeg, unionSingles] using hC
  · rintro (rfl | rfl)
    · refine ⟨.pos B, ?_, ?_, ?_⟩
      · simp [GCNF.Clause.ofList]
      · simp [GCNF.Clause.ofList, Literal.conjugate]
      · simp only [Clause.remove, Literal.conjugate, removePairSecond _ _ hPos,
          removePairSecond _ _ hNeg, unionSingles]
    · refine ⟨.pos A, ?_, ?_, ?_⟩
      · simp [GCNF.Clause.ofList]
      · simp [GCNF.Clause.ofList, Literal.conjugate]
      · simp only [Clause.remove, Literal.conjugate, removePairFirst _ _ hPos,
          removePairFirst _ _ hNeg, unionSingles]

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

proof_of exampleTwoResolventsDistinct := by
  intro he
  have hmem : Literal.pos A ∈ GCNF.Clause.ofList [.pos B, .neg B] := by
    rw [← he]
    simp [GCNF.Clause.ofList]
  simp only [GCNF.Clause.ofList, LCS.Finset.mem_ofList, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with heq | heq
  · exact hAB (Literal.pos.inj heq)
  · cases heq

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

proof_of exampleCoincidentResolvent := by
  have hResult : GCNF.Clause.union
      (GCNF.Clause.remove (GCNF.Clause.ofList [.pos A, .pos A]) (.pos A))
      (GCNF.Clause.remove (GCNF.Clause.ofList [.neg A, .neg A]) (.neg A)) =
      GCNF.Clause.empty := by
    apply LCS.Finset.ext
    intro x
    simp only [GCNF.Clause.union, LCS.Finset.mem_union_exp,
      GCNF.Clause.remove, LCS.Finset.mem_erase, GCNF.Clause.ofList,
      LCS.Finset.mem_ofList, List.mem_cons, List.not_mem_nil, or_false,
      or_self, and_not_self, or_self]
    exact (LCS.Finset.mem_empty x).symm
  constructor
  · rintro ⟨L, hL, _, hC⟩
    have hL' : L = .pos A := by simpa [GCNF.Clause.ofList] using hL
    subst L
    exact hC.trans hResult
  · rintro rfl
    refine ⟨.pos A, ?_, ?_, hResult.symm⟩
    · simp [GCNF.Clause.ofList]
    · simp [GCNF.Clause.ofList, Literal.conjugate]

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

helper @[simp] theorem mem_exResolutionRefutation_dom (a : TreeAddr) :
    a ∈ exResolutionRefutation_dom ↔
      a = [] ∨ a = [0] ∨ a = [0, 0] ∨ a = [0, 1] ∨ a = [1] ∨
      a = [1, 0] ∨ a = [1, 0, 0] ∨ a = [1, 0, 1] ∨ a = [1, 1] := Iff.rfl

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

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

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

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

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

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

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

proof_of exResolutionRefutation_addr_independence := by
  -- BEGIN PROOF
    intro u v huv hne
    rcases huv with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

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

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

proof_of exResolutionRefutation_child_equivalence := by
  -- BEGIN PROOF
    intro u v huv i hmem
    rcases huv with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · -- u = [0,0], [0,0,i] ∈ dom — impossible
      rcases hmem with h | h | h | h | h | h | h | h | h <;> simp_all
    · -- u = [1,0,0], [1,0,0,i] ∈ dom — impossible
      rcases hmem with h | h | h | h | h | h | h | h | h <;> simp_all

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

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

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

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

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

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

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

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

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

proof_of exResolutionRefutation_sharedLeaf := DAG.eqClass_eq_of_rel _ (Or.inr (Or.inl ⟨rfl, rfl⟩))

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

proof_of exResolutionRefutation_eightVertices := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [exResolutionRefutationNodeClasses, List.nodup_cons,
      DAG.eqClass_eq_iff_rel, exResolutionRefutation_dag, exResolutionRefutation_rel]
  · intro V
    constructor
    · rintro ⟨u, hu, rfl⟩
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [exResolutionRefutationNodeClasses, DAG.eqClass_eq_iff_rel,
          exResolutionRefutation_dag, exResolutionRefutation_rel]
    · intro h
      simp only [exResolutionRefutationNodeClasses, List.mem_map] at h
      obtain ⟨u, hu, rfl⟩ := h
      refine ⟨u, ?_, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [exResolutionRefutation_dag, exResolutionRefutation_tree,
          exResolutionRefutation_domain, mem_exResolutionRefutation_dom]

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

proof_of exResolutionRefutation_coincidentFailure := by
  intro ⟨L, hL, _, hResult⟩
  have hPivot : L = .pos P := by simpa [GCNF.Clause.ofList] using hL
  subst L
  have hMem : Literal.neg P ∈ GCNF.Clause.ofList [.neg P] := by
    simp [GCNF.Clause.ofList]
  rw [hResult] at hMem
  simp [GCNF.Clause.union, Clause.remove, GCNF.Clause.remove, GCNF.Clause.ofList,
    LCS.Finset.mem_union_exp, LCS.Finset.mem_erase, Literal.conjugate] at hMem

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

helper /-- A literal and its conjugate cannot both be satisfied by the same
    valuation. -/
theorem literal_conjugate_not_both_sat (L : Literal) (v : Nat → Bool) :
    Literal.satisfiedBy L v → Literal.satisfiedBy (Literal.conjugate L) v → False := by
-- BEGIN PROOF
  cases L with
  | pos n => simp [Literal.satisfiedBy, Literal.conjugate]
  | neg n => simp [Literal.satisfiedBy, Literal.conjugate]

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

proof_of resolution_tautology := by
  -- BEGIN PROOF
    intro v
    constructor
    · -- Forward: (A∨P) ∧ (B∨¬P) → (A∨P) ∧ (B∨¬P) ∧ (A∨B)
      intro ⟨hAP, hBnP⟩
      refine ⟨hAP, hBnP, ?_⟩
      obtain ⟨L1, hL1mem, hL1sat⟩ := hAP
      obtain ⟨L2, hL2mem, hL2sat⟩ := hBnP
      rw [GCNF.Clause.union, LCS.Finset.mem_union_exp, GCNF.Clause.single, LCS.Finset.mem_singleton] at hL1mem
      rw [GCNF.Clause.union, LCS.Finset.mem_union_exp, GCNF.Clause.single, LCS.Finset.mem_singleton] at hL2mem
      rcases hL1mem with hL1A | hL1P
      · exact ⟨L1, (LCS.Finset.mem_union_exp L1 A B).mpr (Or.inl hL1A), hL1sat⟩
      · rcases hL2mem with hL2B | hL2nP
        · exact ⟨L2, (LCS.Finset.mem_union_exp L2 A B).mpr (Or.inr hL2B), hL2sat⟩
        · -- L1 = P and L2 = conjugate P, both satisfied — contradiction
          rw [hL1P] at hL1sat; rw [hL2nP] at hL2sat
          exact absurd hL2sat (literal_conjugate_not_both_sat P v hL1sat)
    · -- Backward: trivial (conjunction implies each conjunct)
      intro ⟨h1, h2, _⟩
      exact ⟨h1, h2⟩

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

helper /-- If a valuation satisfies both C1 and C2, then it satisfies
    union (remove C1 L) (remove C2 (conjugate L)), for any L. -/
theorem resolvent_sat (C1 C2 : Clause) (L : Literal) (v : Nat → Bool)
    (h1 : Clause.satisfies v C1) (h2 : Clause.satisfies v C2) :
    Clause.satisfies v (GCNF.Clause.union (GCNF.Clause.remove C1 L) (GCNF.Clause.remove C2 (Literal.conjugate L))) := by
-- BEGIN PROOF
  obtain ⟨M, hMmem, hMsat⟩ := h1
  obtain ⟨N, hNmem, hNsat⟩ := h2
  by_cases hML : M = L
  · -- M = L, so v ⊨ L
    by_cases hNcL : N = Literal.conjugate L
    · -- N = conjugate L, so v ⊨ conjugate L — contradiction with v ⊨ L
      rw [hML] at hMsat; rw [hNcL] at hNsat
      exact absurd hNsat (literal_conjugate_not_both_sat L v hMsat)
    · -- N ≠ conjugate L, so N ∈ remove C2 (conjugate L)
      refine ⟨N, ?_, hNsat⟩
      rw [GCNF.Clause.union, LCS.Finset.mem_union_exp]
      exact Or.inr (by rw [GCNF.Clause.remove, LCS.Finset.mem_erase]; exact ⟨hNmem, hNcL⟩)
  · -- M ≠ L, so M ∈ remove C1 L
    refine ⟨M, ?_, hMsat⟩
    rw [GCNF.Clause.union, LCS.Finset.mem_union_exp]
    exact Or.inl (by rw [GCNF.Clause.remove, LCS.Finset.mem_erase]; exact ⟨hMmem, hML⟩)

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Propositional.Syntax LCS.Propositional.Semantics

helper /-- The printed singleton {⊥} and the literal empty clause both have
    false disjunction semantics. They are different sorts of sets, not equal sets. -/
theorem displayedFalseSingletonSemantics (v : Valuation) :
    (∃ A ∈ (LCS.Finset.singleton PropFormula.fls), evalExt v A = .T) ↔
      Clause.satisfies (fun n => v n == .T) GCNF.Clause.empty := by
  constructor
  · intro ⟨A, hA, h⟩
    have : A = PropFormula.fls := by simpa using hA
    subst A
    cases h
  · intro ⟨L, hL, _⟩
    exact False.elim ((LCS.Finset.mem_empty L).mp hL)

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Propositional.Syntax LCS.Propositional.Semantics

proof_of resolutionFormulaTautology := by
  intro v
  simp only [evalExt]
  cases evalExt v A <;> cases evalExt v B <;> cases v P <;> rfl

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Propositional.Syntax LCS.Propositional.Semantics

proof_of emptyDisjunctionReductions := by
  simp only [evalExt]
  cases evalExt v A <;> cases v P <;> decide

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Propositional.Syntax LCS.Propositional.Semantics

helper /-- Removing the pivot from a residual disjunction extended by that pivot
    recovers precisely the residual, provided the pivot was absent. -/
theorem removeUnionSingle (A : Clause) (L : Literal) (hL : L ∉ A) :
    GCNF.Clause.remove (GCNF.Clause.union A (GCNF.Clause.single L)) L = A := by
  apply LCS.Finset.ext
  intro x
  simp only [GCNF.Clause.remove, LCS.Finset.mem_erase, GCNF.Clause.union,
    LCS.Finset.mem_union_exp, GCNF.Clause.single, LCS.Finset.mem_singleton]
  constructor
  · intro ⟨hx, hne⟩
    exact hx.elim id (fun he => False.elim (hne he))
  · intro hx
    exact ⟨Or.inl hx, fun he => hL (he ▸ hx)⟩

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Propositional.Syntax LCS.Propositional.Semantics

proof_of residualUnionIsResolvent := by
  refine ⟨L, ?_, ?_, ?_⟩
  · exact (LCS.Finset.mem_union_exp _ _ _).mpr
      (Or.inr ((LCS.Finset.mem_singleton _ _).mpr rfl))
  · exact (LCS.Finset.mem_union_exp _ _ _).mpr
      (Or.inr ((LCS.Finset.mem_singleton _ _).mpr rfl))
  · simp only [Clause.remove, removeUnionSingle A L hA,
      removeUnionSingle B (Literal.conjugate L) hB]

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Propositional.Syntax LCS.Propositional.Semantics

proof_of complementaryUnitsResolve := by
  refine ⟨L, (LCS.Finset.mem_singleton _ _).mpr rfl,
    (LCS.Finset.mem_singleton _ _).mpr rfl, ?_⟩
  apply LCS.Finset.ext
  intro x
  simp [GCNF.Clause.empty, GCNF.Clause.union, Clause.remove,
    GCNF.Clause.remove, GCNF.Clause.single, LCS.Finset.mem_union_exp,
    LCS.Finset.mem_singleton, LCS.Finset.mem_erase]
  exact LCS.Finset.not_mem_empty

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Propositional.Syntax LCS.Propositional.Semantics

proof_of resolventInsertionPreservesModels := by
  constructor
  · intro h D hD
    exact h D (LCS.Finset.mem_insert.mpr (Or.inr hD))
  · intro h D hD
    rcases LCS.Finset.mem_insert.mp hD with rfl | hD
    · obtain ⟨L, _, _, rfl⟩ := hC
      exact resolvent_sat C₁ C₂ L v (h C₁ h₁) (h C₂ h₂)
    · exact h D hD

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Propositional.Syntax LCS.Propositional.Semantics

proof_of resolventInsertionPreservesUnsatisfiability := by
  unfold ClauseSet.isUnsatisfiable
  simp only [resolventInsertionPreservesModels S C C₁ C₂ h₁ h₂ hC]

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Propositional.Syntax LCS.Propositional.Semantics

proof_of residualInsertionPreservesModels := by
  dsimp
  constructor
  · intro h C hC
    exact h C (LCS.Finset.mem_insert.mpr (Or.inr hC))
  · intro h C hC
    rcases LCS.Finset.mem_insert.mp hC with rfl | hC
    · exact ((resolution_tautology A B L v).mp
        ⟨h _ (LCS.Finset.mem_insert.mpr (Or.inl rfl)),
         h _ (LCS.Finset.mem_insert.mpr (Or.inr
           (LCS.Finset.mem_insert.mpr (Or.inl rfl))))⟩).2.2
    · exact h C hC

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Propositional.Syntax LCS.Propositional.Semantics

proof_of resolutionStepPreservesModels := by
  obtain ⟨C₁, h₁, C₂, h₂, C, hC, rfl⟩ := h
  exact resolventInsertionPreservesModels S C C₁ C₂ h₁ h₂ hC v

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Propositional.Syntax LCS.Propositional.Semantics

proof_of ResolutionProcess.preservesModels := by
  obtain ⟨n, hn⟩ := i
  induction n with
  | zero => rw [R.initial]
  | succ n ih =>
    have hlt : n < R.length := by omega
    exact (resolutionStepPreservesModels (R.successive ⟨n, hlt⟩) v).trans
      (ih (by omega))

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Propositional.Syntax LCS.Propositional.Semantics

proof_of containsEmptyIsUnsatisfiable := by
  rintro ⟨v, hv⟩
  obtain ⟨L, hL, _⟩ := hv _ h
  exact (LCS.Finset.mem_empty L).mp hL

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Propositional.Syntax LCS.Propositional.Semantics

proof_of ResolutionProcess.successfulSound := by
  rintro ⟨v, hv⟩
  exact containsEmptyIsUnsatisfiable _ h
    ⟨v, (R.preservesModels v _).mpr hv⟩

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Propositional.Syntax LCS.Propositional.Semantics

proof_of residualInsertionPreservesUnsatisfiability := by
  dsimp
  unfold ClauseSet.isUnsatisfiable
  simp only [residualInsertionPreservesModels S A B L]

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Propositional.Syntax LCS.Propositional.Semantics

proof_of parentDeletionResolvent := by
  refine ⟨.pos Q, ?_, (LCS.Finset.mem_singleton _ _).mpr rfl, ?_⟩
  · simp [GCNF.Clause.ofList]
  · apply LCS.Finset.ext
    intro L
    simp only [GCNF.Clause.single, LCS.Finset.mem_singleton,
      GCNF.Clause.union, LCS.Finset.mem_union_exp, Clause.remove,
      GCNF.Clause.remove, LCS.Finset.mem_erase, GCNF.Clause.ofList,
      LCS.Finset.mem_ofList, List.mem_cons, List.not_mem_nil, or_false,
      Literal.conjugate, and_not_self, or_false]
    constructor
    · intro h
      subst L
      exact ⟨Or.inl rfl, fun he => hPQ (Literal.pos.inj he)⟩
    · intro ⟨h, hne⟩
      exact h.elim id (fun he => False.elim (hne he))

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Propositional.Syntax LCS.Propositional.Semantics

proof_of parentDeletionResult := by
  have hFirst : GCNF.Clause.single (.pos P) ≠ GCNF.Clause.ofList [.pos P, .pos Q] := by
    intro he
    have hmem : Literal.pos Q ∈ GCNF.Clause.single (.pos P) := by
      rw [he]
      simp [GCNF.Clause.ofList]
    have hQP := Literal.pos.inj ((LCS.Finset.mem_singleton _ _).mp hmem)
    exact hPQ hQP.symm
  have hSecond : GCNF.Clause.single (.pos P) ≠ GCNF.Clause.single (.neg Q) := by
    intro he
    have hmem : Literal.pos P ∈ GCNF.Clause.single (.neg Q) := by
      rw [← he]
      exact (LCS.Finset.mem_singleton _ _).mpr rfl
    have heq := (LCS.Finset.mem_singleton _ _).mp hmem
    cases heq
  apply LCS.Finset.ext
  intro C
  simp only [LCS.Finset.mem_erase, LCS.Finset.mem_insert,
    parentDeletionInput, ClauseSequent.ofList, LCS.Finset.mem_ofList,
    List.mem_cons, List.not_mem_nil, or_false,
    ClauseSequent.single, LCS.Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h, h₁⟩, h₂⟩
    rcases h with h | h | h
    · exact h
    · exact False.elim (h₁ h)
    · exact False.elim (h₂ h)
  · intro h
    subst C
    exact ⟨⟨Or.inl rfl, hFirst⟩, hSecond⟩

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Propositional.Syntax LCS.Propositional.Semantics

proof_of parentDeletionCountervaluation := by
  constructor
  · intro C hC
    have hC' := (LCS.Finset.mem_singleton _ _).mp hC
    subst C
    exact ⟨.pos P, (LCS.Finset.mem_singleton _ _).mpr rfl, hP⟩
  · intro h
    have hNeg : Clause.satisfies v (GCNF.Clause.single (.neg Q)) :=
      h _ (by simp [parentDeletionInput, ClauseSequent.ofList])
    obtain ⟨L, hL, hSat⟩ := hNeg
    have hL' := (LCS.Finset.mem_singleton _ _).mp hL
    subst L
    change v Q = false at hSat
    rw [hQ] at hSat
    cases hSat

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Propositional.Syntax LCS.Propositional.Semantics

proof_of parentDeletionNotEquivalent := by
  intro h
  exact (parentDeletionCountervaluation P Q (fun _ => true) rfl rfl).2
    ((h (fun _ => true)).mpr (parentDeletionCountervaluation P Q (fun _ => true) rfl rfl).1)

end LCS.Resolution.Method
end

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
