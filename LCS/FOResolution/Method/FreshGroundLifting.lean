import LCS.Item
import LCS.Util
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import LCS.FOResolution.Method.SeparatingPairs
import LCS.FOResolution.Method.Resolvents
import LCS.FOResolution.Method.ResolutionDAGs
import LCS.FOResolution.Method.FreshGroundLanguage
import Attach
import LCS.FOResolution.Method.FreshGroundLifting.ProofsStamp

section
namespace LCS.FOResolution.Method
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification

namespace FOResolutionTree
open FreshGroundLanguage

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Structural invariant certifying that every clause and substitution stored
    in a fresh-extension resolution tree uses only original symbols. -/
def AllOriginal {L : Language} (hNoEq : L.withoutEquality) :
    FOResolutionTree (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq) → Prop
  | .axiom_ C =>
      IsOriginalClause (hNoEq := by first | exact hNoEq | done) C
  | .resolve T₁ T₂ resolvedA resolvedB rho rho' sigma =>
      AllOriginal (hNoEq := by first | exact hNoEq | done) T₁ ∧
      AllOriginal (hNoEq := by first | exact hNoEq | done) T₂ ∧
      IsOriginalClause (hNoEq := by first | exact hNoEq | done) resolvedA ∧
      IsOriginalClause (hNoEq := by first | exact hNoEq | done) resolvedB ∧
      IsOriginalSubst rho ∧
      IsOriginalSubst rho' ∧
      IsOriginalSubst sigma

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Certified structural descent of a fresh-extension resolution tree. -/
def lower {L : Language} (hNoEq : L.withoutEquality) :
    (T : FOResolutionTree (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)) →
      AllOriginal (hNoEq := by first | exact hNoEq | done) T → FOResolutionTree L hNoEq
  | .axiom_ C, hC =>
      .axiom_ (lowerClause (hNoEq := by first | exact hNoEq | done) C hC)
  | .resolve T₁ T₂ resolvedA resolvedB rho rho' sigma,
      ⟨h₁, h₂, hA, hB, hRho, hRho', hSigma⟩ =>
      .resolve
        (lower (hNoEq := by first | exact hNoEq | done) T₁ h₁)
        (lower (hNoEq := by first | exact hNoEq | done) T₂ h₂)
        (lowerClause (hNoEq := by first | exact hNoEq | done) resolvedA hA)
        (lowerClause (hNoEq := by first | exact hNoEq | done) resolvedB hB)
        (lowerSubst rho hRho)
        (lowerSubst rho' hRho')
        (lowerSubst sigma hSigma)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The label of a certified lowered tree lifts back to the source label. -/
theorem liftClause_lower_label {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    [DecidableEq (FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))]
    (T : FOResolutionTree (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))
    (hT : AllOriginal (hNoEq := by first | exact hNoEq | done) T) :
    liftClause (hNoEq := by first | exact hNoEq | done) (label (hNoEq := by first | exact hNoEq | done) (lower (hNoEq := by first | exact hNoEq | done) T hT)) = label (hNoEq := by first | exact hNoEq | done) T := by
  induction T with
  | axiom_ C =>
      exact liftClause_lowerClause (hNoEq := by first | exact hNoEq | done) hT
  | resolve T₁ T₂ resolvedA resolvedB rho rho' sigma ih₁ ih₂ =>
      obtain ⟨h₁, h₂, hA, hB, hRho, hRho', hSigma⟩ := hT
      simp only [lower, label]
      rw [liftClause_substLits (hNoEq := by first | exact hNoEq | done), liftSubst_lowerSubst,
        liftClause_append (hNoEq := by first | exact hNoEq | done), liftClause_substLits (hNoEq := by first | exact hNoEq | done),
        liftSubst_lowerSubst, liftClause_listDiff (hNoEq := by first | exact hNoEq | done),
        ih₁ h₁, liftClause_lowerClause (hNoEq := by first | exact hNoEq | done),
        liftClause_substLits (hNoEq := by first | exact hNoEq | done), liftSubst_lowerSubst,
        liftClause_listDiff (hNoEq := by first | exact hNoEq | done), ih₂ h₂, liftClause_lowerClause (hNoEq := by first | exact hNoEq | done)]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Every label of an all-original tree is an original-symbol clause. -/
theorem AllOriginal.label {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    [DecidableEq (FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))]
    {T : FOResolutionTree (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hT : AllOriginal (hNoEq := by first | exact hNoEq | done) T) :
    IsOriginalClause (hNoEq := by first | exact hNoEq | done) (label (hNoEq := by first | exact hNoEq | done) T) := by
  rw [← liftClause_lower_label (hNoEq := by first | exact hNoEq | done) T hT]
  exact liftClause_isOriginal (hNoEq := by first | exact hNoEq | done) _

end FOResolutionTree
end LCS.FOResolution.Method
end
