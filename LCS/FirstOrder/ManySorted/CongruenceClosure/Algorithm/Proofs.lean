import LCS.FirstOrder.ManySorted.CongruenceClosure.Algorithm

namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Algorithm

open LCS.FirstOrder.ManySorted

proof_of msUnion_spec := by
  -- REPAIR(T10-39): proof pending — prove ordinary two-block UNION equivalence, leastness, and preservation of other blocks
  sorry

proof_of msMerge_sound := by
  -- REPAIR(T10-40): proof pending — show ordinary R₁ contains R and the selected pair, then use sorted closure
  sorry

proof_of msMerge_minimal := by
  -- REPAIR(T10-40): proof pending — use equivalence leastness for R₁ and compatibility for R₂
  sorry

proof_of msMerge_correct := by
  -- REPAIR(T10-20): proof pending — identify the sorted guarded specification with closure of the enlarged seed
  sorry

proof_of msClosureProgram_correct := by
  -- REPAIR(T10-20): proof pending — apply the sorted fold invariant and absorb the saturated identity seed
  sorry

proof_of msMerge_computes_congruenceClosure :=
  ⟨msMerge_sound G R hR p, msMerge_minimal G R p⟩

proof_of msPredecessorSnapshots := by
  -- REPAIR(T10-75): proof pending — verify the four finite predecessor sets and the compatible but unjoined parent pair
  sorry

proof_of msMerge_terminates := by
  have hcontains : ∀ a b, R a b → msUnion G R u v a b :=
    fun _ _ hab => Or.inl hab
  refine ⟨?_, ?_⟩
  · rintro ⟨a, b⟩ hp hR
    exact hp (hcontains a b hR)
  · refine ⟨(u, v), h, ?_⟩
    intro hcon
    exact hcon (Or.inr (Or.inl ⟨hR.refl u, hR.refl v⟩))

end LCS.FirstOrder.ManySorted.CongruenceClosure.Algorithm
