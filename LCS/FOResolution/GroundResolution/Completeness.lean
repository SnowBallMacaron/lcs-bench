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
import LCS.FOResolution.GroundResolution.GroundClauses
import LCS.FOResolution.GroundResolution.ResolutionTrees
import LCS.FOResolution.GroundResolution.PropositionalTranslation
import Attach
import LCS.FOResolution.GroundResolution.Completeness.ProofsStamp

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

/-- Lemma 8.3.1: (Completeness of ground resolution) The ground
    resolution method is complete for ground clauses. -/
@[blueprint "chap8__lemma_8_3_1" (main := true)]
theorem ground_resolution_completeness
    {L : Language} (hNoEq : L.withoutEquality)
    (hL : L.withoutEquality)
    (S : List (FOClause L hNoEq))
    (hGround : ∀ c ∈ S, FOClause.isGround hNoEq c)
    (hUnsat : GroundClauseSet.isUnsatisfiable (hNoEq := hNoEq) S) :
    ∃ T : FOResolutionTree L hNoEq,
      T.isRefutation (hNoEq := hNoEq) (fun c => c ∈ S)

-- ===================================================================
-- Translation functions (parametric in an encoding)
-- ===================================================================

/-! The equality caveat concerns the ordinary propositional resolution route.
    Equality atoms can be encoded for that route using the general atom carrier;
    the public equality-free ground-resolution calculus remains unchanged. -/

open LCS.FirstOrder.Gentzen
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence

end LCS.FOResolution.GroundResolution
end
