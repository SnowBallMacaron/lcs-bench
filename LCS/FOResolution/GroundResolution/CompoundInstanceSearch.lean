import LCS.Item
import LCS.Util
import LCS.FOResolution.ClauseForm
import LCS.Resolution.Method.Completeness
import LCS.Resolution.Method.Unfold
import LCS.FOResolution.Unification.Substitutions
import LCS.FOResolution.Graph
import LCS.Herbrand.PrimRecursive
import LCS.FirstOrder.Equality.Search.Procedure
import LCS.CutElim.LKe.Equivalence
import LCS.FOResolution.GroundResolution.PropositionalTranslation
import LCS.FOResolution.GroundResolution.ThreeStepProcedure
import Attach
import LCS.FOResolution.GroundResolution.CompoundInstanceSearch.ProofsStamp

section
namespace LCS.FOResolution.GroundResolution
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FOResolution.ClauseForm
open LCS.FirstOrder.SemanticsN
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.Method.Completeness
open LCS.FirstOrder.SemanticsN
open Classical
open LCS.FirstOrder.Gentzen
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FOResolution.Unification

/-- Structural clause presentation: literal leaves and disjunction append.
    This is a relation on the actual formula, not an arbitrary equisatisfiable set. -/
@[blueprint "chap8__definition_8_2_1"]
inductive QFClausePresentation {L : Language} (hNoEq : L.withoutEquality) :
    FormulaN L → FOClause L hNoEq → Prop where
  | positive (P : L.predSymbols) (ts : Fin (L.predArity P) → Term L) :
      QFClausePresentation hNoEq (.predN P ts) [.pos (.predN P ts)]
  | negative (P : L.predSymbols) (ts : Fin (L.predArity P) → Term L) :
      QFClausePresentation hNoEq (.neg (.predN P ts)) [.neg (.predN P ts)]
  | disjunction {A B C D} : QFClausePresentation hNoEq A C →
      QFClausePresentation hNoEq B D → QFClausePresentation hNoEq (.disj A B) (C ++ D)

/-- Structural finite CNF presentation of the actual compound instance. -/
@[blueprint "chap8__definition_8_2_1"]
inductive QFCNFPresentation {L : Language} (hNoEq : L.withoutEquality) :
    FormulaN L → List (FOClause L hNoEq) → Prop where
  | clause {A C} : QFClausePresentation hNoEq A C → QFCNFPresentation hNoEq A [C]
  | conjunction {A B S T} : QFCNFPresentation hNoEq A S →
      QFCNFPresentation hNoEq B T → QFCNFPresentation hNoEq (.conj A B) (S ++ T)

end LCS.FOResolution.GroundResolution
end
