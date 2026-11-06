import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm
import LCS.SLD.SLDForm.Completeness
import LCS.Resolution.Method.FiniteGraph
import LCS.SLD.Propositional.Linearization
import Attach
import LCS.SLD.Propositional.LinearizationExample.ProofsStamp

/-! # Example 9.3.1

Section 9.3.1: the linearization of the SLD-form proof of Example 9.2.1, subtree by subtree. -/

section
namespace LCS.SLD.Propositional
open LCS.Resolution.GCNF
open LCS.SLD.SLDForm

-- ========= Example 9.3.1: Linearization example =========

/-- Example 9.3.1 (companion): The sequence corresponding to the left
    subtree: <{neg P_1}, {neg P_3, neg P_4}, {neg P_4}, square>. -/
@[blueprint "chap9__example_9_3_1"]
def exLeftSubtreeLinearization : List Clause :=
  [Clause.ofList [Literal.neg 1],
   Clause.ofList [Literal.neg 3, Literal.neg 4],
   Clause.ofList [Literal.neg 4],
   Clause.empty]

/-- Example 9.3.1 (companion): The sequence corresponding to the right
    subtree: <{neg P_2}, {neg P_3}, square>. -/
@[blueprint "chap9__example_9_3_1"]
def exRightSubtreeLinearization : List Clause :=
  [Clause.ofList [Literal.neg 2],
   Clause.ofList [Literal.neg 3],
   Clause.empty]

/-- Example 9.3.1: The linearization of the SLD-form proof from Example 9.2.1:
    <{neg P_1, neg P_2}, {neg P_3, neg P_4, neg P_2}, {neg P_4, neg P_2}, {neg P_2}, {neg P_3}, square>. -/
@[blueprint "chap9__example_9_3_1" (main := true)]
def exLinearizationResult : List Clause :=
  [Clause.ofList [Literal.neg 1, Literal.neg 2],
   Clause.ofList [Literal.neg 3, Literal.neg 4, Literal.neg 2],
   Clause.ofList [Literal.neg 4, Literal.neg 2],
   Clause.ofList [Literal.neg 2],
   Clause.ofList [Literal.neg 3],
   Clause.empty]

/-- Linearize the actual subtree at a kernel path: false chooses the left
premise, true the right. An absent descendant has no output. -/
@[blueprint "chap9__example_9_3_1"]
noncomputable def linearizeAt : {S : ClauseSequent} → GCNFProofTree S →
    List Bool → Option (List Clause)
  | _, T, [] => some (linearize T)
  | _, .axiom_ _ _ _, _ :: _ => none
  | _, .rule _ _ _ _ _ _ _ _ left right _ _ _ _, b :: path =>
      if b then linearizeAt right path else linearizeAt left path

/-- The displayed left subtree of the exact Example 9.2.1 tree has the
four-entry output of Example 9.3.1; its root is unswapped (SQ18). -/
@[attach_debt, blueprint "chap9__example_9_3_1"]
theorem exLeftSubtree_linearize_eq :
    linearizeAt exSLDFormProof.kernel [false] = some exLeftSubtreeLinearization

/-- The displayed right subtree of the same tree has the three-entry output. -/
@[attach_debt, blueprint "chap9__example_9_3_1"]
theorem exRightSubtree_linearize_eq :
    linearizeAt exSLDFormProof.kernel [true] = some exRightSubtreeLinearization

/-- The exact worked tree produces the six-entry sequence. This finite
instance does not assert the unrestricted SQ18 linearization specification. -/
@[attach_debt, blueprint "chap9__example_9_3_1"]
theorem exSLDFormProof_linearize_eq :
    linearize exSLDFormProof.kernel = exLinearizationResult

end LCS.SLD.Propositional
end
