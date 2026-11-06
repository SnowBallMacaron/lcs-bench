import LCS.FirstOrder.ManySorted.CongruenceClosure.Algorithm

namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Algorithm

open LCS.FirstOrder.ManySorted

proof_of msMerge_sound := by
  -- REPAIR(T10-40): proof pending — show ordinary R₁ contains R and the selected pair, then use sorted closure
  sorry

proof_of msMerge_minimal := by
  -- REPAIR(T10-40): proof pending — use equivalence leastness for R₁ and compatibility for R₂
  sorry

proof_of msMerge_computes_congruenceClosure :=
  ⟨msMerge_sound G R hR p, msMerge_minimal G R p⟩

end LCS.FirstOrder.ManySorted.CongruenceClosure.Algorithm
