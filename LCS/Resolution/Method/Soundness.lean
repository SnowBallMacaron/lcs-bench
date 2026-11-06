import LCS.Item
import LCS.Util
import LCS.Resolution.GCNF
import Attach
import LCS.Resolution.Method.ResolutionDAGs
import LCS.Resolution.Method.Soundness.ProofsStamp

/-! # Soundness of the resolution method (Section 4.3.3, Lemma 4.3.2)
-/
section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Propositional.Syntax LCS.Propositional.Semantics

-- ========= Lemma 4.3.2: Soundness of Resolution =========

/-- Lemma 4.3.2: If a set S of clauses has a resolution refutation, then S
    is unsatisfiable. -/
@[blueprint "chap4__lemma_4_3_2" (main := true)]
theorem resolution_soundness (S : ClauseSequent) (D : ResolutionDAG)
    (hRef : ResolutionDAG.isResolutionRefutation D S) :
    ClauseSet.isUnsatisfiable S 

end LCS.Resolution.Method
end
