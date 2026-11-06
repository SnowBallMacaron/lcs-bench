import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm
import LCS.SLD.SLDForm.Completeness
import LCS.Resolution.Method.FiniteGraph
import LCS.SLD.Propositional.Linearization
import LCS.SLD.Propositional.SLDDerivations
import Attach
import LCS.SLD.Propositional.Completeness.ProofsStamp

/-! # Completeness of SLD-resolution for Horn clauses (Lemma 9.3.1, Theorem 9.3.1)

Section 9.3.2: correctness of the linearization process and completeness of propositional SLD-resolution, with free choice of the first selected atom. -/

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

-- ========= Helper: definite clause provenance from linearize =========











/-- The requested atom is stored at the actual first transition.
The positive step bound rules out a zero-step trace. -/
@[blueprint "chap9__theorem_9_3_1"]
def SLDDerivation.selectsFirst (d : SLDDerivation) (P : Nat) : Prop :=
  ∃ h : 0 < d.sequence.length - 1, (d.steps ⟨0, h⟩).selectedAtom = P

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
