import LCS.Item
import LCS.Util
import LCS.SLD.Propositional
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import LCS.FOResolution.Method
import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.Method.Completeness
import LCS.Herbrand.SHGTheorem.Main
import LCS.SLD.FirstOrder.SLDDerivations
import LCS.SLD.FirstOrder.HornClauses
import Attach
import LCS.SLD.FirstOrder.SLDRefutations.ProofsStamp

/-! # SLD-derivations and SLD-refutations (Definition 9.4.2)

Section 9.4.1: most general unifiers of atoms, first-order SLD-derivations with their selected atoms, input clauses and result substitutions, and the linear input-resolution tree of a derivation. -/

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

-- ===================================================================
-- Definition 9.4.2: First-order SLD-derivation
-- ===================================================================

/-- The exact per-position MGU certificate for two predicate atoms.
    `atomUnifPairs?` rejects predicate mismatches and equality atoms
    visibly; on success, `IsPairwiseMGU` supplies the unifier,
    finite-support, and universal factorization conditions of §8.4. -/
@[blueprint "chap9__definition_9_4_2"]
def IsAtomMGU {L : Language} (hNoEq : L.withoutEquality)  (reference atom : FOAtom L hNoEq)
    (sigma : Nat → Term L) : Prop :=
  ∃ pairs : List (Term L × Term L),
    (atomUnifPairs? (hNoEq := by all_goals exact hNoEq)) reference atom = some pairs ∧
      IsPairwiseMGU sigma pairs

/-- Definition 9.4.2: An SLD-derivation for S = D ∪ {G_1,...,G_q} is a
    sequence <N_0,...,N_p> with N_0 a goal clause from S and each
    N_{i+1} an MGU-resolvent with a definite clause in D. This indexed
    inductive bakes the textbook side conditions into the constructor
    fields:
    (1) init: goal ∈ goals, and the index (currentGoal) is precisely
        the extracted body atoms of the chosen goal clause;
    (2) step: clause ∈ D, clause.isDefinite, the selected atom A_k
        is in prev's current goal, clause's head is some headA,
        sigma is an MGU of A_k and rho(headA), (Id, rho) is a separating
        pair for the current goal and the locally renamed input clause
        (SQ22/SQ23). The index of the resulting derivation is
        the current goal clause obtained by taking the union of
        prev's goal minus A_k with the rho-renamed body atoms of the
        definite clause and applying sigma (as a Finset, per Gallier
        §4.2.1 Def 4.2.1: clauses are SETS of literals). -/
@[blueprint "chap9__definition_9_4_2" (main := true)]
abbrev FOSLDDerivation {L : Language} (hNoEq : L.withoutEquality)
    (D : Set (FOHornClause L hNoEq)) (goals : List (FOHornClause L hNoEq)) :=
  FOSLDDerivationCore D goals

namespace FOSLDDerivation

export FOSLDDerivationCore (init step)

/-- Definition 9.4.2 (companion): The number of resolution steps in
    the derivation. init has length 0; step increments by 1. -/
@[blueprint "chap9__definition_9_4_2"]
def length {L : Language} (hNoEq : L.withoutEquality) {D : Set (FOHornClause L hNoEq)} {goals : List (FOHornClause L hNoEq)}
    {currentGoal : LCS.Finset (FOAtom L hNoEq)} :
    (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) D goals currentGoal → Nat
  | .init _ _ => 0
  | .step prev _ _ _ _ _ _ _ _ _ _ _ => (length (hNoEq := by all_goals exact hNoEq) prev) + 1

/-- Definition 9.4.2 (companion): An SLD-derivation is an
    SLD-refutation iff its current goal (the type index) is the empty
    Finset (N_p = square). -/
@[blueprint "chap9__definition_9_4_2"]
def isRefutation {L : Language} (hNoEq : L.withoutEquality)  {D : Set (FOHornClause L hNoEq)} {goals : List (FOHornClause L hNoEq)}
    {currentGoal : LCS.Finset (FOAtom L hNoEq)}
    (_ : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) D goals currentGoal) : Prop :=
  currentGoal = (∅ : LCS.Finset (FOAtom L hNoEq))

/-- Definition 9.4.2 (companion): The composition of all substitutions
    accumulated through the derivation. For init, returns the identity.
    For step, composes the current (rho, sigma) pair with the
    accumulated substitution from prev. -/
@[blueprint "chap9__definition_9_4_2"]
def resultSubstitution {L : Language} (hNoEq : L.withoutEquality) {D : Set (FOHornClause L hNoEq)} {goals : List (FOHornClause L hNoEq)}
    {currentGoal : LCS.Finset (FOAtom L hNoEq)} :
    (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) D goals currentGoal → (Nat → Term L)
  | .init _ _ => Term.var
  | .step prev _ _ _ _ _ _ _ rho sigma _ _ =>
    SubstitutionCore.substCompose (SubstitutionCore.substCompose sigma rho) ((resultSubstitution (hNoEq := by all_goals exact hNoEq)) prev)

/-- Definition 9.4.2 (companion): The selected atom of the first
    resolution step in the derivation (the innermost step wrapping
    init). For init (no steps), returns none. For a single step,
    returns the selected atom at that step. For nested steps,
    recurses into the previous derivation. -/
@[blueprint "chap9__definition_9_4_2"]
def firstSelectedAtom {L : Language} (hNoEq : L.withoutEquality) {D : Set (FOHornClause L hNoEq)} {goals : List (FOHornClause L hNoEq)}
    {currentGoal : LCS.Finset (FOAtom L hNoEq)} :
    (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) D goals currentGoal → Option (FOAtom L hNoEq)
  | .init _ _ => none
  | .step prev _ _ _ Ak _ _ _ _ _ _ _ =>
    match prev with
    | .init _ _ => some Ak
    | .step .. => (firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) prev

end FOSLDDerivation
end LCS.SLD.FirstOrder
end
