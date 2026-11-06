import LCS.Item
import LCS.Util
import LCS.FOResolution.Method
import LCS.FirstOrder.SemanticsN.Substitution
import LCS.FOResolution.Method.Soundness.ClauseSemantics
import LCS.FOResolution.Method.Soundness.SubstitutionLemma
import LCS.FOResolution.Method.Soundness.ResolventValidity
import Attach
import LCS.FOResolution.Method.Soundness.ResolutionSoundness.ProofsStamp

section
namespace LCS.FOResolution.Method.Soundness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method

-- ===================================================================
-- Helper: well-formed tree label validity (induction on tree)
-- ===================================================================

-- ATTACH-BLOCKER: size baseline: retain helper in front
/-- Every label of a well-formed resolution tree is satisfied whenever
    all source clauses are satisfied, using direct clause semantics. -/
theorem tree_label_valid {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    (S : FOClause L hNoEq → Prop) (M : Structure L)
    (hSat : ∀ C, S C → FOClause.validIn hNoEq M C)
    (T : FOResolutionTree L hNoEq)
    (hLeaves : T.leavesFrom hNoEq S) (hWF : T.isWellFormed hNoEq) :
    FOClause.validIn hNoEq M (T.label hNoEq) := by
  induction T with
  | axiom_ C => exact hSat C hLeaves
  | resolve T1 T2 A' B' rho rho' sigma ih1 ih2 =>
    obtain ⟨hWF1, hWF2, hVia⟩ := hWF
    exact resolvent_validity_pw hNoEq _ _ _
      ⟨A', B', rho, rho', sigma, hVia⟩ M
      (ih1 hLeaves.1 hWF1) (ih2 hLeaves.2 hWF2)

-- ===================================================================
-- Lemma 8.5.2: Soundness of first-order resolution
-- ===================================================================

/-- Lemma 8.5.2: A finite resolution refutation of S in a language
    without equality makes S unsatisfiable under direct clause semantics.
    The singleton refutation consisting of an empty source clause is
    included, even when the language has no atomic formula. -/
@[blueprint "chap8__lemma_8_5_2" (main := true)]
theorem resolution_soundness_fo {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FOLiteral L hNoEq)]
    (S : FOClause L hNoEq → Prop)
    (D : FOResolutionDAG L hNoEq)
    (hRef : (FOResolutionDAG.isResolutionRefutation (hNoEq := by all_goals exact hNoEq)) D S) :
    (FOClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) S

end LCS.FOResolution.Method.Soundness
end
