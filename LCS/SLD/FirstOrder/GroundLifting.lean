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
import LCS.SLD.FirstOrder.HashLanguage
import LCS.SLD.FirstOrder.HornEncoding
import LCS.SLD.FirstOrder.Soundness
import Attach
import LCS.SLD.FirstOrder.GroundLifting.ProofsStamp

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









-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Structural lowering of a hash-language atom. -/
def hashLowerAtom {L : Language} (hNoEq : L.withoutEquality) (k : Nat) :
    FOAtom (HashLanguage L) hNoEq → FOAtom L hNoEq
  | .predN P args =>
      .predN P (fun i => hashLowerTerm k (args i))
  | .eq_ hL lhs rhs =>
      .eq_ hL (hashLowerTerm k lhs) (hashLowerTerm k rhs)

















-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Atom finite-set lowering is the exact image of structural lowering. -/
noncomputable def hashLowerAtomFinset {L : Language} (hNoEq : L.withoutEquality)  (k : Nat)
    (S : LCS.Finset (FOAtom (HashLanguage L) hNoEq)) :
    LCS.Finset (FOAtom L hNoEq) :=
  LCS.Finset.image ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k) S

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem mem_hashLowerAtomFinset {L : Language} (hNoEq : L.withoutEquality)  (k : Nat)
    (B : FOAtom L hNoEq)
    (S : LCS.Finset (FOAtom (HashLanguage L) hNoEq)) :
    B ∈ (hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k S ↔
      ∃ A ∈ S, (hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k A = B := by
  unfold hashLowerAtomFinset
  exact LCS.Finset.mem_image

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem hashLowerAtomFinset_empty {L : Language} (hNoEq : L.withoutEquality)  (k : Nat) :
    (hashLowerAtomFinset (L := L) (hNoEq := by all_goals exact hNoEq)) k
      (∅ : LCS.Finset (FOAtom (HashLanguage L) hNoEq)) =
        (∅ : LCS.Finset (FOAtom L hNoEq)) := by
  apply LCS.Finset.ext
  intro B
  constructor
  · intro h
    obtain ⟨A, hA, _⟩ :=
      ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k B
        (∅ : LCS.Finset (FOAtom (HashLanguage L) hNoEq))).mp h
    exact (LCS.Finset.mem_empty A).mp hA |>.elim
  · intro h
    exact (LCS.Finset.mem_empty B).mp h |>.elim



























-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- A definite Horn clause carries a head atom.  This accessor is
    structurally total because its goal-clause branch receives an
    impossible definiteness proof. -/
def FOHornClause.headOfDefinite {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) (hDef : (c.isDefinite (hNoEq := by all_goals exact hNoEq))) : FOAtom L hNoEq :=
  match c with
  | FOHornClauseCore.rule head _ => head
  | FOHornClauseCore.fact head => head
  | FOHornClauseCore.goal _ => False.elim hDef

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The structurally extracted head is exactly the clause's optional head. -/
theorem FOHornClause.headAtom_headOfDefinite {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) (hDef : (c.isDefinite (hNoEq := by all_goals exact hNoEq))) :
    (c.headFOAtom (hNoEq := by all_goals exact hNoEq)) = some (c.headOfDefinite (hNoEq := hNoEq) hDef) := by
  cases c with
  | rule head body => rfl
  | fact head => rfl
  | goal body => exact False.elim hDef

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Every structural body atom embeds as an atomic formula. -/
theorem FOHornClause.bodyAtoms_atomic_of_allAtomsAtomic {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) :
    ∀ A ∈ (c.bodyFOAtoms (hNoEq := by all_goals exact hNoEq)),
      FormulaN.isAtomic A.toFormula = true := by
  intro A _
  exact FOAtomCore.toFormula_isAtomic A

-- ATTACH-BLOCKER: unsupported untagged abbrev
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

-- ATTACH-BLOCKER: unsupported untagged structure
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

/-- Adapt one correspondence node directly to a base-language SLD step.
    The source clause is recovered from mapped-program membership; no
    hash-language derivation is ever constructed and no arbitrary term is
    demoted. -/
noncomputable def hashAdaptGroundStep {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq))
    {Dg : List (FOHornClause (HashLanguage L) (by all_goals exact hNoEq))}
    {prevHash : LCS.Finset (FOAtom (HashLanguage L) hNoEq)}
    (step : (GroundSLDStep (hNoEq := by all_goals exact hNoEq)) Dg prevHash)
    (sourceHash : FOHornClause (HashLanguage L) (by all_goals exact hNoEq))
    (hSourceMem : sourceHash ∈ D.map (hashLiftHornClause (hNoEq := by all_goals exact hNoEq)))
    (σHash : Nat → Term (HashLanguage L))
    (hInst :
      step.clause = (substAllInHornClause (hNoEq := by all_goals exact hNoEq)) sourceHash σHash)
    (prev : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals
      ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) prevHash)) :
    (HashAdaptedGroundStep (hNoEq := by all_goals exact hNoEq)) D goals step sourceHash prev := by
  -- REPAIR(CH9-ROOT): proof pending
  -- DEBT(pre-existing: bespoke substitution shown to unify only; MGU upgrade needs the residual-instance invariant)
  sorry

-- ATTACH-BLOCKER: unsupported untagged structure
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

-- ATTACH-KEEP: helper is used from a reopened nested proof namespace
-- ATTACH-BLOCKER: helper is used from a reopened nested proof namespace
/-- Recursively adapt a mapped-program correspondence without ever
    constructing an arbitrary derivation in `HashLanguage L`. -/
noncomputable def hashAdaptGroundCorrespondence {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq)) :
    {Dg : List (FOHornClause (HashLanguage L) (by all_goals exact hNoEq))} →
    {prevHash : LCS.Finset (FOAtom (HashLanguage L) hNoEq)} →
    (prev : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals
      ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) prevHash)) →
    {t : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) Dg prevHash} →
    (GroundSLDCorrespondence (hNoEq := by all_goals exact hNoEq)) (D.map (hashLiftHornClause (hNoEq := by all_goals exact hNoEq))) Dg t →
    (HashAdaptedGroundTranscript (hNoEq := by all_goals exact hNoEq)) D goals t prev := by
  intro Dg prevHash prev t corr
  induction corr with
  | nil =>
      exact {
        derivation := prev
        firstSelected := by
          change (prev.firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) =
            firstSelectedAppend (prev.firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) none
          cases (prev.firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) <;> rfl }
  | @cons prevHash step rest sourceHash hSourceMem σHash hInst restCorr ih =>
    let one :=
      (hashAdaptGroundStep (hNoEq := by all_goals exact hNoEq)) D goals step sourceHash
        hSourceMem σHash hInst prev
    let tail :=
      ih one.derivation
    let tailDerivation :
        (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals
          ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals)
            (GroundSLDTranscript.cons step rest).finalGoal) :=
      tail.derivation
    exact {
      derivation := tailDerivation
      firstSelected := by
        have hTailFirst :
            (tail.derivation.firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) =
              firstSelectedAppend (one.derivation.firstSelectedAtom (hNoEq := by all_goals exact hNoEq))
                (rest.firstSelectedAtom.map
                  ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals))) :=
          tail.firstSelected
        calc
          (tailDerivation.firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) =
              (tail.derivation.firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) := rfl
          _ =
              firstSelectedAppend (one.derivation.firstSelectedAtom (hNoEq := by all_goals exact hNoEq))
                (rest.firstSelectedAtom.map
                  ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals))) :=
            hTailFirst
          _ = firstSelectedAppend
                (firstSelectedAppend (prev.firstSelectedAtom (hNoEq := by all_goals exact hNoEq))
                  (some ((hashLowerAtom (hNoEq := by all_goals exact hNoEq))
                    ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) step.Ak)))
                (rest.firstSelectedAtom.map
                  ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals))) := by
            rw [one.firstSelected]
          _ = firstSelectedAppend (prev.firstSelectedAtom (hNoEq := by all_goals exact hNoEq))
                (some ((hashLowerAtom (hNoEq := by all_goals exact hNoEq))
                  ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) step.Ak)) := by
            cases hPrev : (prev.firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) <;> rfl
          _ = firstSelectedAppend (prev.firstSelectedAtom (hNoEq := by all_goals exact hNoEq))
                ((GroundSLDTranscript.cons step rest).firstSelectedAtom.map
                  ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals))) := rfl }


-- ATTACH-BLOCKER: unsupported untagged structure
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

/-- Initialize and run the direct adapter from a hash-ground instance of
    one base goal clause. -/
noncomputable def hashAdaptGroundCorrespondenceFromInit {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq))
    (initGoal : FOHornClause L hNoEq)
    (hInitMem : initGoal ∈ goals)
    (σHash : Nat → Term (HashLanguage L))
    {Dg : List (FOHornClause (HashLanguage L) (by all_goals exact hNoEq))}
    {bodyHash : LCS.Finset (FOAtom (HashLanguage L) hNoEq)}
    (hBodyHash :
      bodyHash =
        LCS.Finset.ofList
          (((hashLiftHornClause (hNoEq := by all_goals exact hNoEq)) initGoal).bodyFOAtoms.map
            ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq)) σHash)))
    (t : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) Dg bodyHash)
    (corr :
      (GroundSLDCorrespondence (hNoEq := by all_goals exact hNoEq)) (D.map (hashLiftHornClause (hNoEq := by all_goals exact hNoEq))) Dg t) :
    (HashAdaptedGroundRun (hNoEq := by all_goals exact hNoEq)) D goals initGoal σHash t := by
  -- REPAIR(CH9-ROOT): proof pending — statement truth open, see repairs/ch9/proof-debt.md
  -- DEBT(pre-existing: bespoke substitution shown to unify only; MGU upgrade needs the residual-instance invariant)
  sorry

-- ATTACH-BLOCKER: unsupported untagged structure
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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Transport an exact-index initialized run across an empty terminal
    hash goal.  The final index cast leaves first selection unchanged. -/
noncomputable def HashAdaptedGroundRun.toRefutation {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)}
    {initGoal : FOHornClause L hNoEq}
    {σHash : Nat → Term (HashLanguage L)}
    {Dg : List (FOHornClause (HashLanguage L) (by all_goals exact hNoEq))}
    {bodyHash : LCS.Finset (FOAtom (HashLanguage L) hNoEq)}
    {t : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) Dg bodyHash}
    (run : (HashAdaptedGroundRun (hNoEq := by all_goals exact hNoEq)) D goals initGoal σHash t)
    (hFinalEmpty :
      t.finalGoal =
        (∅ : LCS.Finset (FOAtom (HashLanguage L) hNoEq))) :
    (HashAdaptedGroundRefutation (hNoEq := by all_goals exact hNoEq)) D goals t := by
  let k := (hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals
  have hLowerEmpty :
      (hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k t.finalGoal =
        (∅ : LCS.Finset (FOAtom L hNoEq)) := by
    rw [hFinalEmpty, (hashLowerAtomFinset_empty (hNoEq := by all_goals exact hNoEq))]
  let dEmpty :
      (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals
        (∅ : LCS.Finset (FOAtom L hNoEq)) :=
    hLowerEmpty ▸ run.derivation
  refine
    { derivation := dEmpty
      isRefutation := rfl
      firstSelected := ?_ }
  calc
    (dEmpty.firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) = (run.derivation.firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) := by
      exact (FOSLDDerivation.firstSelectedAtom_cast (hNoEq := by all_goals exact hNoEq))
        hLowerEmpty run.derivation
    _ = t.firstSelectedAtom.map
        ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals)) :=
      run.firstSelected

end LCS.SLD.FirstOrder
end

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
namespace HashGroundAdapterRegression









end HashGroundAdapterRegression
end LCS.SLD.FirstOrder
end

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

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 9.4.1 (required helper): Attempt to demote a term from the
    Skolem-extended language back to the base language `L`.

    Returns `some t` when the term contains only base-language function
    symbols (i.e. only `Sum.inl` wrappers on `.func` nodes); returns
    `none` as soon as a Skolem-introduced `Sum.inr` is encountered.

    In the Horn setting `spec.n = 0`, `Sum.inr : Fin 0 → ...` is
    uninhabited, so every closed `Term spec.language` built from a
    `WellFormed CInstance` trivially avoids the `none` branch: all its
    function symbols are `Sum.inl f_L` and recursive demotion succeeds.
    This makes `demoteTerm` a TOTAL extraction in that setting, not a
    partial one — the `Option` type is a structural convenience to keep
    the recursion total for arbitrary (potentially non-Horn) inputs. -/
def demoteTermOpt {L : Language} {n : Nat} {skolemRank : Fin n → Nat} :
    Term (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank) →
      Option (Term L)
  | .var x => some (.var x)
  | .const (.inl c) => some (.const c)
  | .const (.inr _) => none
  | .func (Sum.inl f) args =>
    -- Recurse on each argument; combine.
    let recArgs : Fin (L.funArity f) → Option (Term L) :=
      fun i => demoteTermOpt (args i)
    -- Combine: succeeds iff all args demote
    if h : ∀ i, (recArgs i).isSome then
      some (.func f (fun i => (recArgs i).get (h i)))
    else
      none
  | .func (Sum.inr _) _ => none

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 9.4.1 (required helper): Total demotion of a term from the
    Skolem-extended language. Uses `demoteTermOpt` when possible;
    otherwise falls back to a variable placeholder (used only on
    ill-formed inputs — unreachable on closed `Term spec.language`
    built from a `WellFormed CInstance` in the Horn setting `spec.n = 0`). -/
def demoteTerm {L : Language} {n : Nat} {skolemRank : Fin n → Nat}
    (t : Term (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank)) :
    Term L :=
  match demoteTermOpt t with
  | some t' => t'
  | none => .var 0

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 9.4.1 (required helper): Build a `Nat → Term L` substitution
    from a list of `(Nat × Term spec.language)` pairs: each pair `(x, t)`
    binds variable `x` to `demoteTerm t`. Unlisted variables map to the
    identity `.var`.

    This is the `σ_c` of Thm 9.4.1's proof for clause `c`: a
    per-variable substitution derived from ci's forallInst witness chain
    traversed for clause `c`, turning each free variable `x ∈ FV(c)` into
    the specific witness `t_x` carried by ci's corresponding forallInst
    node. Variables outside the chain (or not in FV(c)) remain as `.var`,
    which has no effect on ground output when applied to c with all of
    c's free variables covered by the chain. -/
def substFromList {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat}
    (entries : List (Nat × Term
      (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank))) :
      Nat → Term L :=
  fun x =>
    match entries.find? (fun p => p.1 = x) with
    | some (_, t) => demoteTerm t
    | none => .var x

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 9.4.1 (required helper): Navigate ci's top-level conjunction
    tree to the `k`-th clause's c-instance subtree (0-indexed).

    STRUCTURE. `hornClauses_to_formulaN Afalsum (c₁ :: c₂ :: ... :: cₘ)`
    left-associates as `.conj (univClos c₁) (hornClauses... (c₂::...))`,
    and `SK spec` preserves this shape because `skolemFormAux` handles
    `.conj A B` by recursing on both children and rebuilding the same
    `.conj` node (Horn has no existentials so `spec.n = 0` and no
    Skolem substitution is triggered). A WellFormed `CInstance` of
    `SK spec` thus has top-level `connective true _ _ H K` nodes exactly
    paralleling this tree (H = c-instance of `univClos cₖ`,
    K = c-instance of the tail).

    CASES. When `totalClauses = 0`, there is no k-th clause so return
    `none`. When `totalClauses = 1`, the entire ci IS the sole clause's
    c-instance subtree (no outer `.conj` wraps it). When
    `totalClauses > 1` and `k = 0`, descend into the LEFT branch of ci's
    top `connective true`. When `k > 0`, descend into the RIGHT branch
    and recurse.

    If ci's shape doesn't match (ill-formed or Ill-typed input), return
    `none`; `WellFormed ci` + `ci.source = SK spec` with correctly-typed
    `spec` rules this out for Horn callers. -/
def ciProjectAtClauseIndex {L : Language} {n : Nat} {skolemRank : Fin n → Nat}
    (ci : LCS.Herbrand.SHGTheorem.CInstance
      (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank))
    (k : Nat) (totalClauses : Nat) :
    Option (LCS.Herbrand.SHGTheorem.CInstance
      (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank)) :=
  match totalClauses with
  | 0 => none
  | 1 =>
    -- Single clause: ci itself is the sole clause's subtree.
    if k = 0 then some ci else none
  | Nat.succ (Nat.succ _) =>
    -- Multiple clauses: ci's top must be `connective true _ _ H K`.
    match ci with
    | .connective true _ _ H K =>
      if k = 0 then some H
      else ciProjectAtClauseIndex K (k - 1) (totalClauses - 1)
    | _ => none

-- retained: used by LCS.SLD.FirstOrder.GroundInstances
/-- Theorem 9.4.1 (required helper): Walk ci's `forallInst` chain on a
    clause-subtree, collecting `(xᵢ, tᵢ)` pairs encoding the per-variable
    witness substitution.

    For a clause `c` whose universal closure is `∀ x₁ ∀ x₂ ... ∀ xₚ (body)`,
    a WellFormed ci for that clause has the shape:
      `forallInst x₁ _ t₁ h₁ _ _ _ _`
      where h₁ is a c-instance of `(body[t₁/x₁])` with its outermost
      `.all x₂` already stripped — so h₁ itself is
      `forallInst x₂ _ t₂ h₂ _ _ _ _`, and so on, until we reach a
      non-forallInst node (atomic / negAtom / connective for the body).

    This function returns `[(x₁, t₁), (x₂, t₂), ..., (xₚ, tₚ)]` by
    recursing on `h₀` (the FIRST witness child). Textbook Def 7.6.3(iii)
    allows k ≥ 1 parallel witnesses (tsRest, hsRest) per `∀x` node; for
    the substitution extraction we take the FIRST witness t₀ — one
    complete witness chain is enough to derive a ground instance of the
    clause. The remaining tsRest/hsRest branches would give additional
    ground instances, but a single one suffices for Thm 9.4.1's argument. -/
def ciExtractSubstFromForallChain {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat} :
    LCS.Herbrand.SHGTheorem.CInstance
      (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank) →
    List (Nat × Term
      (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank))
  | .forallInst x _ t₀ h₀ _ _ _ _ =>
    (x, t₀) :: ciExtractSubstFromForallChain h₀
  | _ => []

-- Theorem 9.4.1 (required helper): mutual helpers for multi-witness
-- extraction. `ciExtractAllSubstPaths` walks ci's forallInst chain
-- collecting ALL witness paths (not just the first); the companion
-- `ciExtractAllSubstPathsList` walks a list of parallel children.
-- Non-forallInst nodes (atom/negAtom/connective) contribute a singleton
-- `[[]]` (base of recursion). Total path count = product of witness
-- counts along every forallInst chain.
-- Needed by `extractGroundClausesFromCInstance_core` (multi-witness D_g)
-- to cover all atomic ground leaves of `ci.toFormula` (Def 7.6.3).
-- ATTACH-BLOCKER: mutual
mutual
def ciExtractAllSubstPaths {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat} :
    LCS.Herbrand.SHGTheorem.CInstance
      (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank) →
    List (List (Nat × Term
      (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank)))
  | .forallInst x _ t₀ h₀ tsRest hsRest _ _ =>
    -- First branch: prepend (x, t₀) to each path through h₀.
    let headPaths := ciExtractAllSubstPaths h₀
    let headPrepended := headPaths.map (fun path => (x, t₀) :: path)
    -- Tail branches: one per (tᵢ, hᵢ) pair in tsRest/hsRest.
    let restPaths := ciExtractAllSubstPathsList x tsRest hsRest
    headPrepended ++ restPaths
  | _ => [[]]

def ciExtractAllSubstPathsList {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat}
    (x : Nat) :
    List (Term (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank)) →
    List (LCS.Herbrand.SHGTheorem.CInstance
      (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank)) →
    List (List (Nat × Term
      (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank)))
  | [], _ => []
  | _ :: _, [] => []
  | t :: tsRest, h :: hsRest =>
    (ciExtractAllSubstPaths h).map (fun path => (x, t) :: path) ++
      ciExtractAllSubstPathsList x tsRest hsRest
end

/-- Theorem 9.4.1 (required helper): The explicit core construction
    producing the ground Horn-clause set `D_g` from a `CInstance` of
    `SK spec`, built via `ciProjectAtClauseIndex` + `ciExtractAllSubstPaths`
    + `substFromList`.

    For each clause `c : FOHornClause L` in `D` (at position `i` within
    `D ++ goals`), we:
    - Locate the c-instance subtree `ciClause_i` at `D`-index i via
      `ciProjectAtClauseIndex ci i (D ++ goals).length`.
    - Extract EVERY witness-path's substitution list via
      `ciExtractAllSubstPaths` — one path per `(tⱼ, hⱼ)` pair at each
      forallInst node, giving a LIST of paths (product of branching
      factors).
    - For each path, build `σ_{i,path} : Nat → Term L` via `substFromList`.
    - Output ALL `substAllInHornClause c σ_{i,path}` entries, flattened.

    MULTI-WITNESS RATIONALE. The previous first-witness-only extraction
    was reviewed UNFAITHFUL by `reviews/d45933d9.md`: a concrete counter-
    example showed `ci.toFormula`'s atomic ground leaves can include
    substitution instances from PARALLEL witness branches (Def 7.6.3(iii)
    with k > 1 witnesses), which were NOT captured by first-witness D_g.
    This multi-path extraction closes that gap: every atomic ground leaf
    of `ci.toFormula` derived from some D-clause appears as a D_g entry.

    This is the textbook's "ground instances of clauses in D" construction
    per Thm 9.4.1 proof's first step (SHG-cascade). -/
@[blueprint "chap9__theorem_9_4_1"]
def extractGroundClausesFromCInstance_core {L : Language} (hNoEq : L.withoutEquality)
    (_Afalsum : FormulaN L)
    (D goals : List (FOHornClause L hNoEq))
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (ci : LCS.Herbrand.SHGTheorem.CInstance spec.language) :
    List (FOHornClause L hNoEq) :=
  let total := ((D ++ goals).length)
  (D.mapIdx (fun i c =>
    let ciClauseOpt := ciProjectAtClauseIndex
      (n := spec.n) (skolemRank := spec.skolemRank) ci i total
    match ciClauseOpt with
    | some ciClause =>
      -- Collect all witness paths through this clause's subtree.
      let paths := ciExtractAllSubstPaths
        (n := spec.n) (skolemRank := spec.skolemRank) ciClause
      -- Build one ground instance per path.
      paths.map (fun entries =>
        let σ : Nat → Term L :=
          substFromList (n := spec.n) (skolemRank := spec.skolemRank) entries
        (substAllInHornClause (hNoEq := by all_goals exact hNoEq)) c σ)
    | none =>
      -- Ill-formed ci for the expected spec: return [c] unchanged
      -- (preserves type, even though c is not necessarily ground).
      -- Unreachable under WellFormed ci + matching hCiSrc/hSpec.
      [c])).flatten

-- retained: used by LCS.SLD.FirstOrder.GroundSemantics
/-- Theorem 9.4.1 (body-only helper): The explicit core construction
    producing the ground Horn-clause set `goals_g` from a `CInstance` of
    `SK spec`, by walking ci's top-level conjunction tree to the goals-side
    subtree. Parallels `extractGroundClausesFromCInstance_core` but indexes
    into goals-side positions `D.length .. (D ++ goals).length - 1`.

    For each goal `g : FOHornClause L` in `goals` (at position `i` within
    `goals`, i.e., absolute position `D.length + i` within `D ++ goals`),
    we:
    - Locate the c-instance subtree `ciClause_{D.length + i}` at goals-index
      i via `ciProjectAtClauseIndex ci (D.length + i) (D ++ goals).length`.
    - Extract EVERY witness-path's substitution list via
      `ciExtractAllSubstPaths` — one path per `(tⱼ, hⱼ)` pair at each
      forallInst node, giving a LIST of paths (product of branching factors).
    - For each path, build `σ_{i,path} : Nat → Term L` via `substFromList`.
    - Output ALL `substAllInHornClause g σ_{i,path}` entries, flattened.

    Together with `extractGroundClausesFromCInstance_core`, this completes
    the textbook's `S_g = D_g ∪ goals_g` ground Horn-clause set per
    Gallier §7.6 SHG (cf. Thm 9.4.1 proof's first step). -/
@[blueprint "chap9__theorem_9_4_1"]
def extractGroundGoalsFromCInstance_core {L : Language} (hNoEq : L.withoutEquality)
    (_Afalsum : FormulaN L)
    (D goals : List (FOHornClause L hNoEq))
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (ci : LCS.Herbrand.SHGTheorem.CInstance spec.language) :
    List (FOHornClause L hNoEq) :=
  (goals.mapIdx (fun i g =>
    let ciClauseOpt := ciProjectAtClauseIndex
      (n := spec.n) (skolemRank := spec.skolemRank) ci (D.length + i)
      ((D ++ goals).length)
    match ciClauseOpt with
    | some ciClause =>
      -- Collect all witness paths through this clause's subtree.
      let paths := ciExtractAllSubstPaths
        (n := spec.n) (skolemRank := spec.skolemRank) ciClause
      -- Build one ground instance per path.
      paths.map (fun entries =>
        let σ : Nat → Term L :=
          substFromList (n := spec.n) (skolemRank := spec.skolemRank) entries
        (substAllInHornClause (hNoEq := by all_goals exact hNoEq)) g σ)
    | none =>
      -- Ill-formed ci for the expected spec: return [g] unchanged
      -- (preserves type, even though g is not necessarily ground).
      -- Unreachable under WellFormed ci + matching hCiSrc/hSpec.
      [g])).flatten

-- retained: used by LCS.SLD.FirstOrder.GroundInstances, LCS.SLD.FirstOrder.GroundSemantics
/-- Theorem 9.4.1 (required helper): Lifts `termVars (σ x) = ∅` for every
    `x ∈ FV(t)` to `termVars (termSubstAll t σ) = ∅`. Under `σ` ground on
    `FV(t)`, the homomorphic substitution produces a ground term because
    `termSubstAll` replaces free variables of `t` by `σ x`-images (all
    ground), and `const`/`func` cases propagate groundness through the
    argument tuple. -/
theorem termSubstAll_ground_of_subst_ground_on_fv {L : Language}
    (t : Term L) (σ : Nat → Term L)
    (hσGround : ∀ x, termVars (L := L) t x → ∀ y, ¬ termVars (σ x) y) :
    ∀ y, ¬ termVars (termSubstAll t σ) y := by
-- BEGIN PROOF
  intro y hFV
  induction t with
  | var x =>
    simp only [termSubstAll] at hFV
    have hself : termVars (L := L) (Term.var x) x := rfl
    exact hσGround x hself y hFV
  | const c => simp only [termSubstAll, termVars] at hFV
  | func f args ih =>
    simp only [termSubstAll, termVars] at hFV
    obtain ⟨i, hi⟩ := hFV
    refine ih i ?_ hi
    intros x hFV2 y' hFV3
    exact hσGround x ⟨i, hFV2⟩ y' hFV3

-- retained: used by LCS.SLD.FirstOrder.GroundInstances, LCS.SLD.FirstOrder.GroundSemantics
/-- Theorem 9.4.1 (required helper): Lifts the term-level groundness
    lemma to formulae: `σ` ground on `FV(A)` implies `formulaSubstAll A σ`
    is ground. Structural recursion on `A`: each atomic / eq case delegates
    to `termSubstAll_ground_of_subst_ground_on_fv`; binary connectives
    split the free-variable witness; quantifier cases forward the
    hypothesis unchanged. -/
theorem formulaSubstAll_ground_of_subst_ground_on_fv {L : Language}
    (A : FormulaN L) (σ : Nat → Term L)
    (hσGround : ∀ x, formulaVars A x → ∀ y, ¬ termVars (σ x) y) :
    ∀ y, ¬ formulaVars (formulaSubstAll A σ) y := by
-- BEGIN PROOF
  intro y hFV
  induction A with
  | predN P ts =>
    simp only [formulaSubstAll, formulaVars] at hFV
    obtain ⟨i, hi⟩ := hFV
    refine termSubstAll_ground_of_subst_ground_on_fv (ts i) σ ?_ y hi
    intro x hFV2 y' hFV3
    exact hσGround x ⟨i, hFV2⟩ y' hFV3
  | eq_ hL t1 t2 =>
    simp only [formulaSubstAll, formulaVars] at hFV
    rcases hFV with h1 | h2
    · refine termSubstAll_ground_of_subst_ground_on_fv t1 σ ?_ y h1
      intro x hFV2; exact hσGround x (Or.inl hFV2)
    · refine termSubstAll_ground_of_subst_ground_on_fv t2 σ ?_ y h2
      intro x hFV2; exact hσGround x (Or.inr hFV2)
  | conj A B ihA ihB =>
    simp only [formulaSubstAll, formulaVars] at hFV
    rcases hFV with h1 | h2
    · refine ihA ?_ h1; intro x hFV2; exact hσGround x (Or.inl hFV2)
    · refine ihB ?_ h2; intro x hFV2; exact hσGround x (Or.inr hFV2)
  | disj A B ihA ihB =>
    simp only [formulaSubstAll, formulaVars] at hFV
    rcases hFV with h1 | h2
    · refine ihA ?_ h1; intro x hFV2; exact hσGround x (Or.inl hFV2)
    · refine ihB ?_ h2; intro x hFV2; exact hσGround x (Or.inr hFV2)
  | impl A B ihA ihB =>
    simp only [formulaSubstAll, formulaVars] at hFV
    rcases hFV with h1 | h2
    · refine ihA ?_ h1; intro x hFV2; exact hσGround x (Or.inl hFV2)
    · refine ihB ?_ h2; intro x hFV2; exact hσGround x (Or.inr hFV2)
  | neg A ih => simp only [formulaSubstAll, formulaVars] at hFV; exact ih hσGround hFV
  | all x A ih => simp only [formulaSubstAll, formulaVars] at hFV; exact ih hσGround hFV
  | ex x A ih => simp only [formulaSubstAll, formulaVars] at hFV; exact ih hσGround hFV

-- retained: used by LCS.SLD.FirstOrder.GroundInstances, LCS.SLD.FirstOrder.GroundSemantics
/-- Structural atom form of
    `formulaSubstAll_ground_of_subst_ground_on_fv`. -/
theorem atomSubst_ground_of_subst_ground_on_fv {L : Language} (hNoEq : L.withoutEquality)
    (A : FOAtom L hNoEq) (σ : Nat → Term L)
    (hσGround : ∀ x, A.vars x → ∀ y, ¬ termVars (σ x) y) :
    ∀ y, ¬ ((A.subst (hNoEq := by all_goals exact hNoEq)) σ).vars y := by
  intro y hy
  have hy' :
      formulaVars (formulaSubstAll A.toFormula σ) y := by
    rw [← (atomSubst_toFormula_formulaSubstAll (hNoEq := by all_goals exact hNoEq)),
      ← FOAtomCore.vars_eq_formulaVars]
    exact hy
  exact formulaSubstAll_ground_of_subst_ground_on_fv
    A.toFormula σ
    (by
      intro x hx
      apply hσGround x
      simpa only [FOAtomCore.vars_eq_formulaVars] using hx)
    y hy'

-- retained: used by LCS.SLD.FirstOrder.GroundInstances, LCS.SLD.FirstOrder.GroundSemantics
/-- Theorem 9.4.1 (required helper): Lifts the formula-level groundness
    lemma to `substAllInHornClause c σ`: `σ` ground on `clauseFV c.toFOClause`
    implies every literal in `(substAllInHornClause c σ).toFOClause` has no
    free variable. Case analysis on `c`: each case (rule/fact/goal) maps
    through `formulaSubstAll_ground_of_subst_ground_on_fv` on every
    body/head formula, with membership-in-list bookkeeping to translate
    each literal's free variable back into the original clause's. -/
theorem substAllInHornClause_ground_of_subst_ground_on_fv {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) (σ : Nat → Term L)
    (hσGround : ∀ x, (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) x → ∀ y, ¬ termVars (σ x) y) :
    ∀ y, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (((substAllInHornClause (hNoEq := by all_goals exact hNoEq)) c σ).toFOClause (hNoEq := by all_goals exact hNoEq)) y := by
  -- REPAIR(T9-77a): proof pending — migration to extensional bodies / renamed-head steps
  sorry

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 9.4.1 (required helper): Structural predicate asserting that a
    term in the Skolem-extended language `SkolemLanguage L n skolemRank` uses
    no `Sum.inr _` function symbol — equivalently, its function heads are all
    base-language symbols `Sum.inl f_L`.

    Under `n = 0`, `Sum.inr : Fin 0 → _` is uninhabited, so every term in the
    extended language is vacuously `termNoSumInr`. More generally, terms
    produced by `liftTermSkolem` from base-language terms are always
    `termNoSumInr` because `liftTermSkolem` only emits `Sum.inl`-headed
    function applications.

    This is the semantic content required for `demoteTermOpt` to succeed. -/
def termNoSumInr {L : Language} {n : Nat} {skolemRank : Fin n → Nat} :
    Term (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank) → Prop
  | .var _ => True
  | .const _ => True
  | .func (Sum.inl _) args => ∀ i, termNoSumInr (args i)
  | .func (Sum.inr _) _ => False



/-- Theorem 9.4.1 (required helper): For a closed, `Sum.inr`-free term in the
    Skolem-extended language, `demoteTermOpt` always succeeds and the demoted
    base-language term has no free variables.

    CONTENT. Structural recursion on `t`: `.var` case excluded by closedness;
    `.const` case trivial; `.func (Sum.inl f) args` case recurses on each
    argument (closedness + `Sum.inr`-freeness propagate to arguments), then
    bundles the demoted arguments; `.func (Sum.inr _) _` case excluded by
    the `termNoSumInr` hypothesis.

    This is the Horn-setting "demotion is total on closed ci-witnesses" fact
    needed by `substFromList_ground_on_clauseFV_of_ci_projection`. -/
theorem demoteTermOpt_some_ground_of_noSumInr_closed
    {L : Language} {n : Nat} {skolemRank : Fin n → Nat} :
    ∀ (t : Term (LCS.Herbrand.SHGTheorem.SkolemLanguage
          (L := L) n skolemRank)),
      termNoSumInr t → LCS.FirstOrder.Basic.Term.isClosed t →
      ∃ t' : Term L, demoteTermOpt t = some t' ∧ ∀ y, ¬ termVars t' y := by
  -- DEBT(FIX435): fresh Skolem constants are accepted by termNoSumInr.
  -- REPAIR(FIX435): proof pending
  sorry

end LCS.SLD.FirstOrder
end
