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
import LCS.SLD.FirstOrder.Soundness
import Attach
import LCS.SLD.FirstOrder.Lifting.ProofsStamp

/-! # Ground SLD transcripts and the lifting lemma

Section 9.4.2 (proof of Theorem 9.4.1): ground SLD steps and transcripts, their correspondence with a source program, separating renamings, and lifting a ground SLD-refutation to an SLD-refutation of the source clauses. -/

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
-- Theorem 9.4.1 (helpers): Ground propositional SLD → FO SLD lifter
-- ===================================================================

/-- Theorem 9.4.1 (companion type): A ground SLD step transcript. Carries the
    per-step data needed to build one `FOSLDDerivation.step` onto an existing
    derivation indexed at `prevGoal` using identity (ground) substitutions.
    Fields correspond one-to-one to the `.step` constructor's arguments. -/
@[blueprint "chap9__theorem_9_4_1"]
structure GroundSLDStep {L : Language} (hNoEq : L.withoutEquality)
    (D : List (FOHornClause L hNoEq))
    (prevGoal : LCS.Finset (FOAtom L hNoEq)) where
  /-- The definite Horn clause used in this resolution step. -/
  clause : FOHornClause L hNoEq
  /-- Witness: the clause is in the program `D`. -/
  hClause : clause ∈ D
  /-- Witness: the clause is a definite clause (rule or fact). -/
  hDef : (clause.isDefinite (hNoEq := by all_goals exact hNoEq))
  /-- The selected atom. -/
  Ak : FOAtom L hNoEq
  /-- The head atom of the definite clause. -/
  headA : FOAtom L hNoEq
  /-- Witness that `Ak ∈ prevGoal`. -/
  hAk : Ak ∈ prevGoal
  /-- Witness that the clause's structural head equals `some headA`. -/
  hHead : (clause.headFOAtom (hNoEq := by all_goals exact hNoEq)) = some headA
  /-- Ground unification: `Ak = headA`. With identity substitution,
      the textbook `hUnif` equation reduces to `Ak = headA`. -/
  hUnifGround : Ak = headA
  /-- Ground condition: atoms in `prevGoal` have no free variables
      (the sequence N_i atoms are all ground). -/
  hGroundPrev : ∀ a ∈ prevGoal, ∀ x, ¬ a.vars x
  /-- Ground condition: `clause.toFOClause` has no free variables
      (the definite clause is a ground instance). -/
  hGroundClause : ∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (clause.toFOClause (hNoEq := by all_goals exact hNoEq)) x

/-- The equality-free MGU certificate supplies the general derivation kernel. -/
theorem isAtomMGU_toCore {L : Language} (hNoEq : L.withoutEquality)
    {a b : FOAtom L hNoEq} {σ : Nat → Term L} (h : IsAtomMGU hNoEq a b σ) :
    IsAtomMGUCore a b σ := by
  cases a <;> cases b <;>
    simpa [IsAtomMGU, IsAtomMGUCore, atomUnifPairs?, atomUnifPairsCore] using h

/-- Theorem 9.4.1 (required helper): A ground SLD transcript is a list of
    ground step-data values, each one producing one `.step` on the running
    derivation. The indices at each step are implicit — they are computed by
    `foSLDStepGround` from `prevGoal`. This encodes the per-step transcript
    of a propositional SLD-derivation lifted to the FO level with all
    substitutions being identity (ground). -/
@[blueprint "chap9__theorem_9_4_1"]
inductive GroundSLDTranscript {L : Language} (hNoEq : L.withoutEquality)
    (D : List (FOHornClause L hNoEq)) :
    (prevGoal : LCS.Finset (FOAtom L hNoEq)) → Type where
  /-- Empty transcript: no steps, prevGoal unchanged. -/
  | nil {prevGoal : LCS.Finset (FOAtom L hNoEq)} : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D prevGoal
  /-- Cons: one step onto the transcript, producing a new prevGoal. -/
  | cons {prevGoal : LCS.Finset (FOAtom L hNoEq)}
      (step : (GroundSLDStep (hNoEq := by all_goals exact hNoEq)) D prevGoal)
      (rest : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D
        (LCS.Finset.image ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var))
          ((prevGoal.erase step.Ak).union
            (LCS.Finset.ofList
              (step.clause.bodyFOAtoms.map ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var))))))) :
      (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D prevGoal

/-- Theorem 9.4.1 (required helper): The final (terminal) goal after folding
    a ground SLD transcript onto a starting prevGoal. For `.nil` the final
    goal is `prevGoal`; for `.cons step rest` it is the final goal obtained
    by recursing on `rest` from the resolved subsequent goal. -/
@[blueprint "chap9__theorem_9_4_1"]
noncomputable def GroundSLDTranscript.finalGoal {L : Language} (hNoEq : L.withoutEquality)
    {D : List (FOHornClause L hNoEq)} :
    {prevGoal : LCS.Finset (FOAtom L hNoEq)} → (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D prevGoal →
      LCS.Finset (FOAtom L hNoEq)
  | prevGoal, .nil => prevGoal
  | _, .cons _ rest => rest.finalGoal

-- ===================================================================
-- Theorem 9.4.1 (helpers): Non-ground lifting from ground transcript
-- ===================================================================

/-- Theorem 9.4.1 (companion): Apply a simultaneous substitution to every
    atom in a Horn clause. Rule/fact/goal constructors are handled
    homomorphically via `formulaSubstAll`. -/
@[blueprint "chap9__theorem_9_4_1"]
def substAllInHornClause {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) (σ : Nat → Term L) : FOHornClause L hNoEq :=
  FOHornClauseCore.subst σ c

/-- Theorem 9.4.1 (companion type): Per-step correspondence between a ground
    SLD transcript over a ground-instance program `D_g` and a non-ground
    source program `D_orig`. Each step in the transcript is witnessed to
    arise from applying some substitution `σ_i` to a source clause
    `C_i ∈ D_orig`. This structure mirrors the per-leaf correspondence in
    `lifting_lemma_refutation_wf` (Ch8) but at the SLD-step level. -/
@[blueprint "chap9__theorem_9_4_1"]
inductive GroundSLDCorrespondence {L : Language} (hNoEq : L.withoutEquality)
    (D_orig : List (FOHornClause L hNoEq))
    (D_g : List (FOHornClause L hNoEq)) :
    {prevGoal : LCS.Finset (FOAtom L hNoEq)} →
      (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D_g prevGoal → Type where
  /-- Empty correspondence for an empty transcript. -/
  | nil {prevGoal : LCS.Finset (FOAtom L hNoEq)} :
      (GroundSLDCorrespondence (hNoEq := by all_goals exact hNoEq)) D_orig D_g
        (prevGoal := prevGoal) GroundSLDTranscript.nil
  /-- Cons: one step's correspondence witnesses, plus the rest. -/
  | cons {prevGoal : LCS.Finset (FOAtom L hNoEq)}
      (step : (GroundSLDStep (hNoEq := by all_goals exact hNoEq)) D_g prevGoal)
      (rest : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D_g
        (LCS.Finset.image ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var))
          ((prevGoal.erase step.Ak).union
            (LCS.Finset.ofList
              (step.clause.bodyFOAtoms.map ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var)))))))
      (sourceC : FOHornClause L hNoEq)
      (hSourceMem : sourceC ∈ D_orig)
      (sigma : Nat → Term L)
      (hInst : step.clause = (substAllInHornClause (hNoEq := by all_goals exact hNoEq)) sourceC sigma)
      (restCorr : (GroundSLDCorrespondence (hNoEq := by all_goals exact hNoEq)) D_orig D_g rest) :
      (GroundSLDCorrespondence (hNoEq := by all_goals exact hNoEq)) D_orig D_g
        (prevGoal := prevGoal) (GroundSLDTranscript.cons step rest)

-- ===================================================================
-- Direct hash-ground transcript adapter
-- ===================================================================

/-- The first selected atom recorded by a ground transcript.  A transcript
    stores its chronological first step at the outermost `cons`, unlike
    `FOSLDDerivation`, whose chronological first step is the innermost
    `step` above `init`. -/
def GroundSLDTranscript.firstSelectedAtom {L : Language} (hNoEq : L.withoutEquality)
    {D : List (FOHornClause L hNoEq)}
    {prevGoal : LCS.Finset (FOAtom L hNoEq)} :
    (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) D prevGoal → Option (FOAtom L hNoEq)
  | .nil => none
  | .cons step _ => some step.Ak

/-- Left-biased selection composition.  It states the accumulator
    orientation used when a transcript is appended to an existing
    derivation: an earlier selection already present in the accumulator
    remains first. -/
def firstSelectedAppend {α : Type} (earlier later : Option α) : Option α :=
  match earlier with
  | some a => some a
  | none => later

end LCS.SLD.FirstOrder
end
