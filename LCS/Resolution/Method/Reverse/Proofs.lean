import LCS.Resolution.Method.Reverse

namespace LCS.Resolution.Method

open LCS.Resolution.GCNF

namespace FiniteGraph

proof_of toGCNF_nodeCount_bound := by
  have hOutput := LCS.Resolution.GCNF.Proofs.GCNFProofTree.nodeCount_eq_two_leafCount_sub_one
    (g.toGCNF S hRef hOrdinary)
  have hLeaves := g.toGCNF_leafCount_le_unfold S hRef hOrdinary
  have hInput := g.unfold_steps_add_one_le_nodeCount hRef.1 hTree
  omega

end FiniteGraph

end LCS.Resolution.Method
