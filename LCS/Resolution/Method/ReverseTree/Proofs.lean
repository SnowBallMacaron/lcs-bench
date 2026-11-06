import LCS.Resolution.Method.ReverseTree

namespace LCS.Resolution.Method

open LCS.Resolution.GCNF

proof_of weakenTo_leafCount := by
  simp [weakenTo, LCS.Resolution.GCNF.Proofs.GCNFProofTree.weaken_leafCount]


namespace ResolutionTree

helper theorem ResolutionTree.remove_eq_empty_imp_single (C : GCNF.Clause) (L : Literal)
    (hL : L ∈ C) (h : GCNF.Clause.remove C L = GCNF.Clause.empty) :
    C = GCNF.Clause.single L := by
  apply LCS.Finset.ext
  intro K
  rw [GCNF.Clause.single, LCS.Finset.mem_singleton]
  constructor
  · intro hK
    by_cases hEq : K = L
    · exact hEq
    · have he : K ∈ GCNF.Clause.remove C L :=
        (LCS.Finset.mem_erase L K C).mpr ⟨hK, hEq⟩
      exact (LCS.Finset.not_mem_empty (h ▸ he)).elim
  · rintro rfl
    exact hL

proof_of units_of_empty := open LCS.Resolution.Method.ReverseTree.Proofs.ResolutionTree in
  by
    have hremA : GCNF.Clause.remove A.label L = GCNF.Clause.empty := by
      apply LCS.Finset.ext
      intro K
      constructor
      · intro hK
        have hr : K ∈ (resolve A B L).label :=
          LCS.Finset.mem_union.mpr (Or.inl hK)
        exact (LCS.Finset.not_mem_empty (hEmpty ▸ hr)).elim
      · exact fun h => (LCS.Finset.not_mem_empty h).elim
    have hremB : GCNF.Clause.remove B.label L.conjugate = GCNF.Clause.empty := by
      apply LCS.Finset.ext
      intro K
      constructor
      · intro hK
        have hr : K ∈ (resolve A B L).label :=
          LCS.Finset.mem_union.mpr (Or.inr hK)
        exact (LCS.Finset.not_mem_empty (hEmpty ▸ hr)).elim
      · exact fun h => (LCS.Finset.not_mem_empty h).elim
    exact ⟨remove_eq_empty_imp_single _ _ hWF.2.2.1 hremA,
      remove_eq_empty_imp_single _ _ hWF.2.2.2 hremB⟩


proof_of unit_refutation_label := open LCS.Resolution.Method.ReverseTree.Proofs.ResolutionTree in
  by
    apply LCS.Finset.ext
    intro K
    constructor
    · intro hK
      simp [label, hA, hB, GCNF.Clause.union, GCNF.Clause.remove,
        GCNF.Clause.single, LCS.Finset.mem_erase, LCS.Finset.mem_singleton] at hK
    · exact fun hK => (LCS.Finset.not_mem_empty hK).elim


proof_of inputs_partition := open LCS.Resolution.Method.ReverseTree.Proofs.ResolutionTree in
  by
    apply LCS.Finset.ext
    intro C
    by_cases h : C ∈ S <;>
      simp [oldInputs, newInputs, h]


proof_of subset_of_newInputs_empty := open LCS.Resolution.Method.ReverseTree.Proofs.ResolutionTree in
  by
    intro C hC
    by_cases hs : C ∈ S
    · exact hs
    · have hn : C ∈ newInputs U S := by
        exact LCS.Finset.mem_filter.mpr ⟨hC, by simp [hs]⟩
      exact (LCS.Finset.not_mem_empty (h ▸ hn)).elim

end ResolutionTree

end LCS.Resolution.Method
