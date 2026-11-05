import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm
import LCS.SLD.SLDForm.Completeness
import LCS.Resolution.Method.FiniteGraph
import LCS.SLD.Propositional.Part1
import Attach
import LCS.SLD.Propositional.Part2.ProofsStamp

section
namespace LCS.SLD.Propositional
open LCS.Resolution.GCNF
open LCS.SLD.SLDForm







-- ========= Helper lemmas for stepValid in linearize_yields_sld_refutation =========



































-- ========= Lemma 9.3.1: Correctness of linearization =========

/-- Lemma 9.3.1's total linearization claim, retained as an unproved proposition.
    The SQ18 residual-call defect prevents asserting it on all SLD-form proofs. -/
@[blueprint "chap9__lemma_9_3_1" (main := true)]
def linearize_yields_sld_refutation
    (S : ClauseSequent)
    (T : GCNFProofTree S)
    (hSLD : LCS.SLD.SLDForm.isSLDForm T)
    (hDef : ∀ C ∈ S, LCS.SLD.SLDForm.isDefiniteClause C ∨
                      LCS.SLD.SLDForm.isGoalClause C)
    (goal : Clause)
    (hGoal : goal ∈ S)
    (hGoalPred : LCS.SLD.SLDForm.isGoalClause goal)
    (hUnique : ∀ C ∈ S, LCS.SLD.SLDForm.isGoalClause C → C = goal) : Prop :=
    ∃ d : SLDDerivation,
      (∀ C ∈ d.definiteClauses,
        LCS.SLD.SLDForm.isDefiniteClause C) ∧
      goal ∈ d.goals ∧
      d.sequence = linearize T ∧
      isSLDRefutation d ∧
      (∀ C ∈ d.definiteClauses, C ∈ S)

-- REPAIR(T9-73e): statement false under OD-9-1/SQ18 on the unrestricted input;
-- retained as an unproved specification, not a proof of a total linearizer.

-- ========= Helper: relabel an SLDDerivation's definiteClauses and goals =========

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Enlarge a derivation's original program and replace its goal family,
with validity certificates for the new inputs and the same ordered trace. -/
theorem SLDDerivation.relabel (d : SLDDerivation) (D' : Set Clause) (goals' : List Clause)
    (hSub : ∀ C ∈ d.definiteClauses, C ∈ D')
    (hDef : ∀ C ∈ D', isDefiniteClause C)
    (hGoals : ∀ C ∈ goals', allNegative C)
    (hHead : d.sequence.head d.seqNonempty ∈ goals') :
    ∃ d' : SLDDerivation,
      d'.definiteClauses = D' ∧ d'.goals = goals' ∧ d'.sequence = d.sequence ∧
      (isSLDRefutation d → isSLDRefutation d') := by
  exact ⟨{
    definiteClauses := D'
    definiteValid := hDef
    goals := goals'
    goalsNegative := hGoals
    sequence := d.sequence
    sequenceNegative := d.sequenceNegative
    seqNonempty := d.seqNonempty
    initialIsGoal := hHead
    steps := d.steps
    stepValid := fun i => ⟨hSub _ (d.stepValid i).1, (d.stepValid i).2⟩
  }, rfl, rfl, rfl, id⟩

-- ========= Helper: definite clause provenance from linearize =========











-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The requested atom is stored at the actual first transition.
The positive step bound rules out a zero-step trace. -/
@[blueprint "chap9__theorem_9_3_1"]
def SLDDerivation.selectsFirst (d : SLDDerivation) (P : Nat) : Prop :=
  ∃ h : 0 < d.sequence.length - 1, (d.steps ⟨0, h⟩).selectedAtom = P

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- An empty original goal gives a concrete one-entry refutation, independently
of the size of the definite program. It has no selected transition. -/
def SLDDerivation.emptyGoal (D : Set Clause)
    (hD : ∀ C ∈ D, isDefiniteClause C)
    (goals : List Clause) (hGoals : ∀ C ∈ goals, allNegative C)
    (hEmpty : Clause.empty ∈ goals) : SLDDerivation where
  definiteClauses := D
  definiteValid := hD
  goals := goals
  goalsNegative := hGoals
  sequence := [Clause.empty]
  sequenceNegative := by
    intro C hC l hl
    have h := List.mem_singleton.mp hC
    subst C
    exact False.elim (Finset.not_mem_empty hl)
  seqNonempty := by simp
  initialIsGoal := hEmpty
  steps := fun i => False.elim (by have := i.isLt; simp at this)
  stepValid := fun i => False.elim (by have := i.isLt; simp at this)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem SLDDerivation.emptyGoal_isRefutation (D : Set Clause)
    (hD : ∀ C ∈ D, isDefiniteClause C)
    (goals : List Clause) (hGoals : ∀ C ∈ goals, allNegative C)
    (hEmpty : Clause.empty ∈ goals) :
    isSLDRefutation (SLDDerivation.emptyGoal D hD goals hGoals hEmpty) := rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem SLDDerivation.emptyGoal_no_first (D : Set Clause)
    (hD : ∀ C ∈ D, isDefiniteClause C)
    (goals : List Clause) (hGoals : ∀ C ∈ goals, allNegative C)
    (hEmpty : Clause.empty ∈ goals) (P : Nat) :
    ¬ (SLDDerivation.emptyGoal D hD goals hGoals hEmpty).selectsFirst P := by
  rintro ⟨h, _⟩
  have : 0 < 0 := h
  omega

/-- Reorder a successful refutation to select a requested atom from its
initial goal in the actual first transition, preserving both original input
families and that same initial goal. -/
theorem sld_form_swap_first_atom
    (d : SLDDerivation) (hRef : isSLDRefutation d)
    (P : Nat) (hP : Literal.neg P ∈ d.sequence.head d.seqNonempty) :
    ∃ d' : SLDDerivation,
      d'.definiteClauses = d.definiteClauses ∧ d'.goals = d.goals ∧
      d'.sequence.head d'.seqNonempty = d.sequence.head d.seqNonempty ∧
      isSLDRefutation d' ∧ d'.selectsFirst P := by
  classical
  by_cases hFirst : d.selectsFirst P
  · exact ⟨d, rfl, rfl, rfl, hRef, hFirst⟩
  · -- REPAIR(T9-10): proof pending
    -- Reorder the finite successful trace and its original side-input uses.
    sorry

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Selection is conditional on the supplied successful refutation, with its
initial goal fixed; it does not choose an unrelated successful input goal. -/
theorem sld_form_first_selected_atom
    (D : Set Clause) (goals : List Clause)
    (d : SLDDerivation) (hD : d.definiteClauses = D) (hGoals : d.goals = goals)
    (hRef : isSLDRefutation d)
    (P : Nat) (hP : Literal.neg P ∈ d.sequence.head d.seqNonempty) :
    ∃ d' : SLDDerivation,
      d'.definiteClauses = D ∧ d'.goals = goals ∧
      d'.sequence.head d'.seqNonempty = d.sequence.head d.seqNonempty ∧
      isSLDRefutation d' ∧ d'.selectsFirst P := by
  obtain ⟨d', hD', hGoals', hHead, hRef', hFirst⟩ :=
    sld_form_swap_first_atom d hRef P hP
  exact ⟨d', hD'.trans hD, hGoals'.trans hGoals, hHead, hRef', hFirst⟩

-- ========= Theorem 9.3.1: Completeness of SLD-resolution =========

/-- Theorem 9.3.1: An unsatisfiable arbitrary definite program with finitely
many negative input goals admits an SLD-refutation. For each supplied successful
refutation, every atom in its initial goal can be selected in the actual first
transition of another refutation with the same inputs and initial goal.
An empty original goal admits a zero-step refutation and requests no atom. -/
@[attach_debt, blueprint "chap9__theorem_9_3_1" (main := true)]
theorem sld_resolution_completeness
    (D : Set Clause) (goals : List Clause)
    (hD : ∀ C ∈ D, isDefiniteClause C)
    (hGoals : ∀ C ∈ goals, allNegative C)
    (hUnsat : ¬ ∃ v : Nat → Bool,
      (∀ C ∈ D, Clause.satisfiedBy C v) ∧
      (∀ G ∈ goals, Clause.satisfiedBy G v)) :
    sldResolutionMethod D goals ∧
    (∀ d : SLDDerivation,
      d.definiteClauses = D → d.goals = goals → isSLDRefutation d →
      ∀ P : Nat, Literal.neg P ∈ d.sequence.head d.seqNonempty →
        ∃ d' : SLDDerivation,
          d'.definiteClauses = D ∧ d'.goals = goals ∧
          d'.sequence.head d'.seqNonempty = d.sequence.head d.seqNonempty ∧
          isSLDRefutation d' ∧ d'.selectsFirst P) 
end LCS.SLD.Propositional
end

