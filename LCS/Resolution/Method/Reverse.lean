import LCS.Resolution.Method.UnfoldBounds
import LCS.Resolution.Method.ReverseTree
import Attach
import LCS.Resolution.Method.Reverse.ProofsStamp

/-! # From resolution refutations to GCNF′ proofs

The ordinary-input interpretation of §4.3.5 is explicit.  The literal extension
of resolution to an input empty clause has a zero-step refutation, while §4.2's
GCNF′ proof trees have ordinary clauses at their roots.  The source's literal
path-deletion operation is recorded separately from its corrected replay:
deleting a literal can remove a pivot of a redundant resolution inference.
-/

namespace LCS.Resolution.Method

open LCS.Resolution.GCNF

namespace FiniteGraph

/-- Theorem 4.3.3, ordinary-input reading: execute the recursive conversion
on the unfolding of the finite graph, then restore the full input clause set.
The result is the actual proof tree. Shared graph vertices retain their IDs in
`g`; their repeated occurrences are used only to execute the recursion. -/
@[blueprint "chap4__theorem_4_3_3" (main := true)]
def toGCNF (g : FiniteGraph) (S : ClauseSequent)
    (hRef : g.IsRefutationFor S) (hOrdinary : S.isOrdinary) : GCNFProofTree S :=
  let t := g.unfold hRef.1
  let hSub := (g.unfold_inputs_subset hRef.1 S).mpr hRef.2.1
  let hEmpty : t.label = GCNF.Clause.empty :=
    Option.some.inj ((g.unfold_rootLabel hRef.1).symm.trans hRef.2.2)
  let converted := t.toGCNF (g.unfold_isWellFormed hRef.1) hEmpty
    (ClauseSequent.ordinary_subset hOrdinary hSub)
  weakenTo converted.val S hOrdinary hSub

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The actual output is bounded by the number of resolution occurrences in
the unfolding. No equality with the graph's shared-vertex count is assumed. -/
theorem toGCNF_leafCount_le_unfold (g : FiniteGraph) (S : ClauseSequent)
    (hRef : g.IsRefutationFor S) (hOrdinary : S.isOrdinary) :
    (g.toGCNF S hRef hOrdinary).leafCount ≤ (g.unfold hRef.1).treeStepCount := by
  unfold toGCNF
  rw [weakenTo_leafCount]
  exact LCS.Resolution.Method.ResolutionTree.toGCNF_leafCount_le _ _ _ _

/-- Proof of Lemma 4.3.4: count the constructed proof and the actual graph
vertices. The source inequality is stated in ordinary, subtraction-free
arithmetic, so the zero-step empty-input boundary remains visible. -/
@[blueprint "chap4__lemma_4_3_4" (main := true)]
theorem toGCNF_nodeCount_bound (g : FiniteGraph) (S : ClauseSequent)
    (hRef : g.IsRefutationFor S) (hOrdinary : S.isOrdinary)
    (hTree : (g.toResolutionDAG hRef.1).isTreeShaped) :
    (g.toGCNF S hRef hOrdinary).nodeCount + 3 ≤ 2 * g.nodeCount 

end FiniteGraph
end LCS.Resolution.Method
