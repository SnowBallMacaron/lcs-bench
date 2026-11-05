import LCS.Resolution.Method
import Attach
import LCS.Resolution.Method.Erase.ProofsStamp

/-! # Literal deletion in resolution trees

Deletion follows paths whose labels contain the selected literal. A replayed
inference whose pivot disappears contracts to the premise lacking that pivot.
This is the corrected deletion operation needed in §4.3.5.
-/

namespace LCS.Resolution.Method.ResolutionTree

open LCS.Resolution.GCNF

/-- The finite set of actual input clauses of a resolution tree. -/
@[blueprint "chap4__theorem_4_3_3"]
def inputs : ResolutionTree → ClauseSequent
  | .axiom_ C => ClauseSequent.single C
  | .resolve A B _ => LCS.Finset.union A.inputs B.inputs









/-- Replay one inference, contracting to a premise when its pivot disappeared. -/
@[blueprint "chap4__theorem_4_3_3"]
def replayResolve (A B : ResolutionTree) (P : Literal) : ResolutionTree :=
  if P ∈ A.label then
    if P.conjugate ∈ B.label then .resolve A B P else B
  else A

/-- Erase a literal along its persistent paths and replay the remaining steps. -/
@[blueprint "chap4__theorem_4_3_3"]
def eraseLiteral (T : ResolutionTree) (L : Literal) : ResolutionTree :=
  if L ∈ T.label then
    match T with
    | .axiom_ C => .axiom_ (GCNF.Clause.remove C L)
    | .resolve A B P => replayResolve (A.eraseLiteral L) (B.eraseLiteral L) P
  else T





@[blueprint "chap4__theorem_4_3_3"]
theorem eraseLiteral_isWellFormed (T : ResolutionTree) (L : Literal)
    (h : T.IsWellFormed) : (T.eraseLiteral L).IsWellFormed 





@[blueprint "chap4__theorem_4_3_3"]
theorem eraseLiteral_unit_label (T : ResolutionTree) (L : Literal)
    (h : T.label = GCNF.Clause.single L) :
    (T.eraseLiteral L).label = GCNF.Clause.empty 

@[blueprint "chap4__theorem_4_3_3"]
theorem eraseLiteral_treeStepCount_le (T : ResolutionTree) (L : Literal) :
    (T.eraseLiteral L).treeStepCount ≤ T.treeStepCount 











/-- An input introduced by deletion recovers an original input upon restoring L. -/
@[blueprint "chap4__theorem_4_3_3"]
theorem eraseLiteral_novel_input_restore (T : ResolutionTree) (L : Literal)
    (C : Clause) (hC : C ∈ (T.eraseLiteral L).inputs) (hNovel : C ∉ T.inputs) :
    clauseWithLiteral C L ∈ T.inputs 

/-- Deleting L preserves ordinary inputs if the unit clause L was not an input. -/
@[blueprint "chap4__theorem_4_3_3"]
theorem eraseLiteral_inputs_ordinary (T : ResolutionTree) (L : Literal)
    (hOrd : T.inputs.isOrdinary) (hUnit : GCNF.Clause.single L ∉ T.inputs) :
    (T.eraseLiteral L).inputs.isOrdinary 

end LCS.Resolution.Method.ResolutionTree
