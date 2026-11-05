import LCS.FOResolution.Method.GroundExtension

section

namespace LCS.FOResolution.Method

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FOResolution.ClauseForm

open LCS.FOResolution.Unification

namespace FreshGroundLanguage

helper /-- Certified clause descent preserves the clause free-variable set. -/
theorem FreshGroundLanguage.clauseFV_lowerClause {L : Language} (hNoEq : L.withoutEquality)
    {C : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hC : IsOriginalClause (hNoEq := by first | exact hNoEq | done) C) :
    clauseFV (hNoEq := by first | exact hNoEq | done) (lowerClause (hNoEq := by first | exact hNoEq | done) C hC) = clauseFV (hNoEq := by first | exact hNoEq | done) C := by
  rw [← clauseFV_liftClause (hNoEq := by first | exact hNoEq | done) (lowerClause (hNoEq := by first | exact hNoEq | done) C hC),
    liftClause_lowerClause (hNoEq := by first | exact hNoEq | done) hC]

helper /-- Certified descent distributes over clause append. -/
theorem FreshGroundLanguage.lowerClause_append {L : Language} (hNoEq : L.withoutEquality)
    {left right : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hLeft : IsOriginalClause (hNoEq := by first | exact hNoEq | done) left)
    (hRight : IsOriginalClause (hNoEq := by first | exact hNoEq | done) right) :
    lowerClause (hNoEq := by first | exact hNoEq | done) (left ++ right) (hLeft.append (hNoEq := by first | exact hNoEq | done) hRight) =
      lowerClause (hNoEq := by first | exact hNoEq | done) left hLeft ++ lowerClause (hNoEq := by first | exact hNoEq | done) right hRight := by
  apply liftClause_injective (hNoEq := by first | exact hNoEq | done)
  rw [liftClause_lowerClause (hNoEq := by first | exact hNoEq | done), liftClause_append (hNoEq := by first | exact hNoEq | done),
    liftClause_lowerClause (hNoEq := by first | exact hNoEq | done), liftClause_lowerClause (hNoEq := by first | exact hNoEq | done)]

helper /-- Certified descent commutes with literal-set conjugation. -/
theorem FreshGroundLanguage.lowerClause_conjugate {L : Language} (hNoEq : L.withoutEquality)
    {lits : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hLits : IsOriginalClause (hNoEq := by first | exact hNoEq | done) lits) :
    lowerClause (hNoEq := by first | exact hNoEq | done) (LitSetConjugate (hNoEq := by first | exact hNoEq | done) lits) hLits.conjugate =
      LitSetConjugate (hNoEq := by first | exact hNoEq | done) (lowerClause (hNoEq := by first | exact hNoEq | done) lits hLits) := by
  apply liftClause_injective (hNoEq := by first | exact hNoEq | done)
  rw [liftClause_lowerClause (hNoEq := by first | exact hNoEq | done), liftClause_conjugate (hNoEq := by first | exact hNoEq | done),
    liftClause_lowerClause (hNoEq := by first | exact hNoEq | done)]

helper /-- Certified descent commutes with the total literal-set absolute value. -/
theorem FreshGroundLanguage.lowerClause_abs {L : Language} (hNoEq : L.withoutEquality)
    {lits : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hLits : IsOriginalClause (hNoEq := by first | exact hNoEq | done) lits) :
    lowerClause (hNoEq := by first | exact hNoEq | done) (LitSetAbs (hNoEq := by first | exact hNoEq | done) lits) hLits.abs =
      LitSetAbs (hNoEq := by first | exact hNoEq | done) (lowerClause (hNoEq := by first | exact hNoEq | done) lits hLits) := by
  apply liftClause_injective (hNoEq := by first | exact hNoEq | done)
  rw [liftClause_lowerClause (hNoEq := by first | exact hNoEq | done), liftClause_abs (hNoEq := by first | exact hNoEq | done),
    liftClause_lowerClause (hNoEq := by first | exact hNoEq | done)]

helper /-- Certified clause and substitution descent commute with substitution. -/
theorem FreshGroundLanguage.lowerClause_subst {L : Language} (hNoEq : L.withoutEquality)
    {C : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hC : IsOriginalClause (hNoEq := by first | exact hNoEq | done) C)
    (sigma : Nat → Term (FreshGroundLanguage L))
    (hSigma : IsOriginalSubst sigma) :
    lowerClause (hNoEq := by first | exact hNoEq | done) (substLits (hNoEq := by first | exact hNoEq | done) sigma C) (hC.subst (hNoEq := by first | exact hNoEq | done) sigma hSigma) =
      substLits (hNoEq := by first | exact hNoEq | done) (lowerSubst sigma hSigma) (lowerClause (hNoEq := by first | exact hNoEq | done) C hC) := by
  apply liftClause_injective (hNoEq := by first | exact hNoEq | done)
  rw [liftClause_lowerClause (hNoEq := by first | exact hNoEq | done), liftClause_substLits (hNoEq := by first | exact hNoEq | done),
    liftSubst_lowerSubst, liftClause_lowerClause (hNoEq := by first | exact hNoEq | done)]

helper /-- Certified descent commutes with list difference on original clauses. -/
theorem FreshGroundLanguage.lowerClause_listDiff {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    [DecidableEq (FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))]
    {C : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hC : IsOriginalClause (hNoEq := by first | exact hNoEq | done) C)
    {removed : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hRemoved : IsOriginalClause (hNoEq := by first | exact hNoEq | done) removed) :
    lowerClause (hNoEq := by first | exact hNoEq | done) (Method.listDiff C removed) (hC.listDiff (hNoEq := by first | exact hNoEq | done) removed) =
      Method.listDiff (lowerClause (hNoEq := by first | exact hNoEq | done) C hC)
        (lowerClause (hNoEq := by first | exact hNoEq | done) removed hRemoved) := by
  apply liftClause_injective (hNoEq := by first | exact hNoEq | done)
  rw [liftClause_lowerClause (hNoEq := by first | exact hNoEq | done), liftClause_listDiff (hNoEq := by first | exact hNoEq | done),
    liftClause_lowerClause (hNoEq := by first | exact hNoEq | done), liftClause_lowerClause (hNoEq := by first | exact hNoEq | done)]



helper /-- The fresh seed is closed. -/
theorem FreshGroundLanguage.seed_isClosed {L : Language} :
    (@seed L).isClosed :=
  rfl









end FreshGroundLanguage

end LCS.FOResolution.Method

end

section

namespace LCS.FOResolution.Method

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FOResolution.ClauseForm

open LCS.FOResolution.Unification

namespace FOResolutionTree

open FreshGroundLanguage







helper /-- Bundled certified lowering: the returned base-language tree is
    exactly the structural lowering, is well-formed, and its root label lifts
    exactly to the source root label. -/
def FOResolutionTree.lowerCertified {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    [DecidableEq (FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))]
    (T : FOResolutionTree (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))
    (hOriginal : AllOriginal (hNoEq := by first | exact hNoEq | done) T)
    (hWF : isWellFormed (hNoEq := by first | exact hNoEq | done) T) :
    {U : FOResolutionTree L hNoEq //
      U = lower (hNoEq := by first | exact hNoEq | done) T hOriginal ∧
      isWellFormed (hNoEq := by first | exact hNoEq | done) U ∧
      liftClause (hNoEq := by first | exact hNoEq | done) (label (hNoEq := by first | exact hNoEq | done) U) = label (hNoEq := by first | exact hNoEq | done) T} :=
  ⟨lower (hNoEq := by first | exact hNoEq | done) T hOriginal,
    rfl,
    lower_isWellFormed (hNoEq := by first | exact hNoEq | done) T hOriginal hWF,
    liftClause_lower_label (hNoEq := by first | exact hNoEq | done) T hOriginal⟩

end FOResolutionTree

end LCS.FOResolution.Method

end
