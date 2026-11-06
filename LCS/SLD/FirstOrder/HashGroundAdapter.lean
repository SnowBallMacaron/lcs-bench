import LCS.Item
import LCS.Util
import LCS.SLD.Propositional
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import LCS.FOResolution.Method
import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.Method.Completeness
import LCS.Herbrand.SHGTheorem.Main
import LCS.SLD.FirstOrder.HornClauses
import LCS.SLD.FirstOrder.SLDRefutations
import LCS.SLD.FirstOrder.Lifting
import LCS.SLD.FirstOrder.HashLanguage
import LCS.SLD.FirstOrder.HornEncoding
import Attach
import LCS.SLD.FirstOrder.HashGroundAdapter.ProofsStamp

/-! # Adapting hash-ground SLD steps to the base language

Section 9.4.2 (proof of Theorem 9.4.1): the direct adaptation of a ground SLD transcript in the hash language to an SLD-refutation over the base language. -/

noncomputable section
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.Completeness

/-- Structural lowering of a hash-language atom. -/
def hashLowerAtom {L : Language} (hNoEq : L.withoutEquality) (k : Nat) :
    FOAtom (HashLanguage L) hNoEq → FOAtom L hNoEq
  | .predN P args =>
      .predN P (fun i => hashLowerTerm k (args i))
  | .eq_ hL lhs rhs =>
      .eq_ hL (hashLowerTerm k lhs) (hashLowerTerm k rhs)

/-- Atom finite-set lowering is the exact image of structural lowering. -/
noncomputable def hashLowerAtomFinset {L : Language} (hNoEq : L.withoutEquality)  (k : Nat)
    (S : LCS.Finset (FOAtom (HashLanguage L) hNoEq)) :
    LCS.Finset (FOAtom L hNoEq) :=
  LCS.Finset.image ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k) S

/-- The goal index computed by one ground transcript step. -/
noncomputable abbrev GroundSLDStep.nextGoal {L : Language} (hNoEq : L.withoutEquality)
    {D : List (FOHornClause L hNoEq)}
    {prevGoal : LCS.Finset (FOAtom L hNoEq)}
    (step : (GroundSLDStep (hNoEq := by all_goals exact hNoEq)) D prevGoal) :
    LCS.Finset (FOAtom L hNoEq) :=
  LCS.Finset.image ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var))
    ((prevGoal.erase step.Ak).union
      (LCS.Finset.ofList
        (step.clause.bodyFOAtoms.map
          ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var)))))

/-- A one-step direct adaptation result.  Its derivation is indexed by the
    exact lowering of the hash transcript's next goal, and it records the
    exact base source clause recovered from mapped-program membership. -/
structure HashAdaptedGroundStep {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq))
    {Dg : List (FOHornClause (HashLanguage L) (by all_goals exact hNoEq))}
    {prevHash : LCS.Finset (FOAtom (HashLanguage L) hNoEq)}
    (step : (GroundSLDStep (hNoEq := by all_goals exact hNoEq)) Dg prevHash)
    (sourceHash : FOHornClause (HashLanguage L) (by all_goals exact hNoEq))
    (prev : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals
      ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) prevHash)) where
  sourceClause : FOHornClause L hNoEq
  sourceMem : sourceClause ∈ D
  sourceLift : (hashLiftHornClause (hNoEq := by all_goals exact hNoEq)) sourceClause = sourceHash
  derivation : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals
    ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) step.nextGoal)
  firstSelected :
    (derivation.firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) =
      firstSelectedAppend (prev.firstSelectedAtom (hNoEq := by all_goals exact hNoEq))
        (some ((hashLowerAtom (hNoEq := by all_goals exact hNoEq))
          ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) step.Ak))

/-- Direct adaptation of a whole ground transcript.  The result remains
    indexed by the exact lowering of the transcript's terminal goal and
    records the chronological first selected atom. -/
structure HashAdaptedGroundTranscript {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq))
    {Dg : List (FOHornClause (HashLanguage L) (by all_goals exact hNoEq))}
    {prevHash : LCS.Finset (FOAtom (HashLanguage L) hNoEq)}
    (t : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) Dg prevHash)
    (prev : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals
      ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) prevHash)) where
  derivation : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals
    ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) t.finalGoal)
  firstSelected :
    (derivation.firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) =
      firstSelectedAppend (prev.firstSelectedAtom (hNoEq := by all_goals exact hNoEq))
        (t.firstSelectedAtom.map
          ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals)))

/-- An initialized direct hash-ground run.  The initial hash substitution
    is lowered rigidly at the single globally fresh even variable, and the
    resulting derivation never leaves the base language. -/
structure HashAdaptedGroundRun {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq))
    (initGoal : FOHornClause L hNoEq)
    (σHash : Nat → Term (HashLanguage L))
    {Dg : List (FOHornClause (HashLanguage L) (by all_goals exact hNoEq))}
    {bodyHash : LCS.Finset (FOAtom (HashLanguage L) hNoEq)}
    (t : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) Dg bodyHash) where
  initialGoalMem : initGoal ∈ goals
  initialHashIndex :
    bodyHash =
      LCS.Finset.ofList
        (((hashLiftHornClause (hNoEq := by all_goals exact hNoEq)) initGoal).bodyFOAtoms.map
          ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq)) σHash))
  freshEven :
    ∃ q, (hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals = 2 * q
  lowerSubstitution : Nat → Term L
  lowerSubstitution_eq :
    lowerSubstitution =
      hashLowerSubst ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) σHash
  initialIndex :
    (hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) bodyHash =
      LCS.Finset.ofList
        (initGoal.bodyFOAtoms.map
          ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq)) lowerSubstitution))
  initialDerivation : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals
    ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) bodyHash)
  derivation : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals
    ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) t.finalGoal)
  firstSelected :
    (derivation.firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) =
      t.firstSelectedAtom.map
        ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals))

/-- A direct adapter result specialized to an actual empty-goal
    refutation in the base language. -/
structure HashAdaptedGroundRefutation {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq))
    {Dg : List (FOHornClause (HashLanguage L) (by all_goals exact hNoEq))}
    {bodyHash : LCS.Finset (FOAtom (HashLanguage L) hNoEq)}
    (t : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) Dg bodyHash) where
  derivation :
    (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals (∅ : LCS.Finset (FOAtom L hNoEq))
  isRefutation : (derivation.isRefutation (hNoEq := by all_goals exact hNoEq))
  firstSelected :
    (derivation.firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) =
      t.firstSelectedAtom.map
        ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals))

end LCS.SLD.FirstOrder
end
