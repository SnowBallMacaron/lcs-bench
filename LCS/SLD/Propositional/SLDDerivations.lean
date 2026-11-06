import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm
import LCS.SLD.SLDForm.Completeness
import LCS.Resolution.Method.FiniteGraph
import Attach
import LCS.SLD.Propositional.SLDDerivations.ProofsStamp

/-! # SLD-derivations and SLD-refutations (Definition 9.3.2)

Section 9.3.1: SLD-derivations and SLD-refutations for a set of propositional Horn clauses, the SLD-resolution method, its soundness, and the free choice of the selected atom in a successful continuation. -/

section
namespace LCS.SLD.Propositional
open LCS.Resolution.GCNF
open LCS.SLD.SLDForm

/-- Definition 9.3.2 (companion): Given a negative clause N_i and a
    definite clause C, checks that some negative literal neg A_k in N_i
    has a matching positive literal pos A_k in C.
    I.e., ∃ A, Literal.neg A ∈ N_i ∧ Literal.pos A ∈ C. -/
@[blueprint "chap9__definition_9_3_2"]
def selectedAtomMatches (Ni : Clause) (A : Nat) (C : Clause)
    : Prop :=
  Literal.neg A ∈ Ni ∧ Literal.pos A ∈ C

-- ========= Definition 9.3.2 (companion): resolveStep =========

/-- Definition 9.3.2 (companion): Given a negative clause
    N_i = {neg A_1,...,neg A_n}, a selected atom A_k, and a definite
    clause C = {neg B_1,...,neg B_m, pos A_k}, produce the next clause
    N_{i+1} = (N_i \ {neg A_k}) ∪ {neg B_j | neg B_j ∈ C}.
    This removes neg A_k from N_i and adds all negative literals from C. -/
@[blueprint "chap9__definition_9_3_2"]
def resolveStep (Ni : Clause) (A : Nat) (C : Clause)
    : Clause :=
  let niWithout := Clause.remove Ni (Literal.neg A)
  let cNeg : Clause := Finset.filter (fun l => match l with
    | Literal.neg _ => true
    | Literal.pos _ => false) C
  Clause.union niWithout cNeg

-- ========= Definition 9.3.2: SLDDerivation =========

/-- The ordered choice made at one resolution transition. Equal side clauses
may be used at several different indices; each use retains its selected atom. -/
@[blueprint "chap9__definition_9_3_2"]
structure SLDStepWitness where
  selectedAtom : Nat
  sideClause : Clause

/-- Definition 9.3.2: A finite nonempty trace of negative clauses over an
arbitrary definite program and a finite family of negative input goals.
Every transition validates its stored selected atom and original side input.
Negative clauses may be empty, including the initial and final goal. -/
@[blueprint "chap9__definition_9_3_2" (main := true)]
structure SLDDerivation where
  definiteClauses : Set Clause
  definiteValid : ∀ C ∈ definiteClauses, isDefiniteClause C
  goals : List Clause
  goalsNegative : ∀ C ∈ goals, allNegative C
  sequence : List Clause
  sequenceNegative : ∀ C ∈ sequence, allNegative C
  seqNonempty : sequence ≠ []
  initialIsGoal : sequence.head seqNonempty ∈ goals
  steps : Fin (sequence.length - 1) → SLDStepWitness
  stepValid : ∀ i : Fin (sequence.length - 1),
    (steps i).sideClause ∈ definiteClauses ∧
    selectedAtomMatches (sequence.get ⟨i.val, by omega⟩)
      (steps i).selectedAtom (steps i).sideClause ∧
    sequence.get ⟨i.val + 1, by omega⟩ =
      resolveStep (sequence.get ⟨i.val, by omega⟩)
        (steps i).selectedAtom (steps i).sideClause

-- ========= Definition 9.3.2 (companion): isSLDRefutation =========

/-- Definition 9.3.2 (companion): An SLD-derivation is an SLD-refutation
    iff the last clause in the sequence is the empty clause. -/
@[blueprint "chap9__definition_9_3_2"]
def isSLDRefutation (d : SLDDerivation) : Prop :=
  d.sequence.getLast d.seqNonempty = Clause.empty

-- ========= Definition 9.3.2 (companion): sldResolutionMethod =========

/-- Definition 9.3.2 (companion): The SLD-resolution method succeeds when
    the same arbitrary program and finite goal family admit a validated refutation. -/
@[blueprint "chap9__definition_9_3_2"]
def sldResolutionMethod (D : Set Clause) (goals : List Clause) : Prop :=
  ∃ d : SLDDerivation,
    d.definiteClauses = D ∧ d.goals = goals ∧ isSLDRefutation d

end LCS.SLD.Propositional
end

attribute [blueprint "chap9__definition_9_3_2"] LCS.SLD.Propositional.SLDDerivation.seqNonempty
