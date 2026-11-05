import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.Syntax
import LCS.FirstOrder.Syntax.Substitution
import Attach
import LCS.FirstOrder.Semantics.ProofsStamp

/-! # FirstOrder.Semantics
    Formalization of Chapter 5, Sections 5.3.1-5.3.3.
    First-order structures, semantics of formulae, satisfaction, validity, and models.
-/

open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax

namespace LCS.FirstOrder.Semantics

-- ===================================================================
-- Definition 5.3.6: Formula evaluation
-- ===================================================================

/-- Definition 5.3.6: The function A_M : [V → M] → Prop defined by
recursion on formulae. The atomic clauses define A_M pointwise on
assignments; the non-atomic clauses lift the connectives per Def 5.3.4
(andM, orM, implM, equivM, negM), and the quantifier clauses quantify
over domain elements via assignUpdate. -/
@[blueprint "chap5__definition_5_3_6" (main := true)]
def formulaEval {L : Language} (M : Structure L) :
    Formula L → Assignment M → Prop
  | Formula.falsum => fun _ => False
  | Formula.pred0 P h => fun _ => M.interpPred P (h ▸ Fin.elim0)
  | Formula.predN P _ ts => fun s => M.interpPred P (fun i => termEval M s (ts i))
  | Formula.eq_ _ t1 t2 => fun s => termEval M s t1 = termEval M s t2
  | Formula.conj A B => andM (formulaEval M A) (formulaEval M B)
  | Formula.disj A B => orM (formulaEval M A) (formulaEval M B)
  | Formula.impl A B => implM (formulaEval M A) (formulaEval M B)
  | Formula.equiv_ A B => equivM (formulaEval M A) (formulaEval M B)
  | Formula.neg A => negM (formulaEval M A)
  | Formula.all i A =>
      fun s => ∀ a : M.carrier, formulaEval M A (assignUpdate s i a)
  | Formula.ex i A =>
      fun s => ∃ a : M.carrier, formulaEval M A (assignUpdate s i a)

-- ===================================================================
-- Definition 5.3.7: Satisfaction, satisfiability, validity, models,
--                    semantic consequence
-- ===================================================================

/-- Definition 5.3.7: A formula A is satisfiable in M iff there
is some assignment s such that A_M[s] = T. -/
@[blueprint "chap5__definition_5_3_7" (main := true)]
def satisfiableIn {L : Language} (M : Structure L)
    (A : Formula L) : Prop :=
  ∃ s : Assignment M, formulaEval M A s

/-- Definition 5.3.7: A formula A is satisfiable iff there is some
structure M in which A is satisfiable. -/
@[blueprint "chap5__definition_5_3_7" (main := true)]
def satisfiable {L : Language} (A : Formula L) : Prop :=
  ∃ (M : Structure L), satisfiableIn M A

/-- Definition 5.3.7: A formula A is valid in M (true in M) iff
A_M[s] = T for every assignment s. Denoted M |= A. -/
@[blueprint "chap5__definition_5_3_7" (main := true)]
def validIn {L : Language} (M : Structure L)
    (A : Formula L) : Prop :=
  ∀ s : Assignment M, formulaEval M A s

/-- Definition 5.3.7: A formula A is universally valid iff it is
valid in every structure M. Denoted |= A. -/
@[blueprint "chap5__definition_5_3_7" (main := true)]
def universallyValid {L : Language} (A : Formula L) : Prop :=
  ∀ (M : Structure L), validIn M A

/-- Definition 5.3.7: A set Gamma of formulae is satisfiable iff there
exists a structure M and assignment s such that M |= A[s] for every formula A in Gamma. -/
@[blueprint "chap5__definition_5_3_7" (main := true)]
def satisfiableSet {L : Language} (Gamma : Set (Formula L)) : Prop :=
  ∃ (M : Structure L) (s : Assignment M),
    ∀ A, A ∈ Gamma → formulaEval M A s

/-- Definition 5.3.7: M is a model of Gamma iff M is a model of every
formula in Gamma. Denoted M |= Gamma. -/
@[blueprint "chap5__definition_5_3_7" (main := true)]
def isModelSet {L : Language} (M : Structure L)
    (Gamma : Set (Formula L)) : Prop :=
  ∀ A, A ∈ Gamma → validIn M A

/-- Definition 5.3.7: The set Gamma is valid iff M |= Gamma for every
structure M. Denoted |= Gamma. -/
@[blueprint "chap5__definition_5_3_7" (main := true)]
def validSet {L : Language} (Gamma : Set (Formula L)) : Prop :=
  ∀ (M : Structure L), isModelSet M Gamma

/-- Definition 5.3.7: B is a semantic consequence of Gamma, denoted Gamma
|= B, iff for every L-structure M, for every assignment s, if M |= A[s] for every A in Gamma then M |= B[s]. -/
@[blueprint "chap5__definition_5_3_7" (main := true)]
def semanticConsequence {L : Language}
    (Gamma : Set (Formula L)) (B : Formula L) : Prop :=
  ∀ (M : Structure L) (s : Assignment M),
    (∀ A, A ∈ Gamma → formulaEval M A s) → formulaEval M B s

-- ===================================================================
-- Example 5.3.1: Natural number structure
-- ===================================================================

/-- Example 5.3.1: The structure 𝒩 for the predicate-free arithmetic language
with domain Nat. The constant 0 is interpreted as zero, S as Nat.succ,
+ as Nat.add, and * as Nat.mul. -/
@[blueprint "chap5__example_5_3_1" (main := true)]
def peanoNatStructure : Structure peanoLanguage where
  carrier := Nat
  carrierNonempty := ⟨0⟩
  interpFunc
    | ArithFunc.succ, args => Nat.succ (args ⟨0, by decide⟩)
    | ArithFunc.plus, args =>
        Nat.add (args ⟨0, by decide⟩) (args ⟨1, by decide⟩)
    | ArithFunc.times, args =>
        Nat.mul (args ⟨0, by decide⟩) (args ⟨1, by decide⟩)
  interpConst
    | ArithConst.zero => 0
  interpPred := fun p => Empty.elim p

-- ===================================================================
-- Example 5.2.5: Semantic effect of variable capture
-- ===================================================================

/-- Example 5.2.5 (companion): The ordered natural-number structure with
zero, successor, addition, multiplication, and the usual strict order. -/
@[blueprint "chap5__example_5_2_5"]
def natStructure : Structure arithLanguage where
  carrier := Nat
  carrierNonempty := ⟨0⟩
  interpFunc
    | ArithFunc.succ, args => Nat.succ (args ⟨0, by decide⟩)
    | ArithFunc.plus, args =>
        Nat.add (args ⟨0, by decide⟩) (args ⟨1, by decide⟩)
    | ArithFunc.times, args =>
        Nat.mul (args ⟨0, by decide⟩) (args ⟨1, by decide⟩)
  interpConst
    | ArithConst.zero => 0
  interpPred
    | ArithPred.lt, args =>
        (args ⟨0, by decide⟩) < (args ⟨1, by decide⟩)

/-- Example 5.2.5: No assignment satisfies the captured sentence ∃x(x < x)
when < is irreflexive, as it is in every strict order. -/
@[blueprint "chap5__example_5_2_5" (main := true)]
theorem captureExample_5_2_5_not_satisfied (M : Structure arithLanguage)
    (hIrrefl : ∀ a : M.carrier, ¬ M.interpPred ArithPred.lt (fun _ => a))
    (s : Assignment M) :
    ¬ formulaEval M Syntax.Substitution.captureExample_5_2_5_after s 

/-- Example 5.2.5: The ordered natural-number structure satisfies the
uncaptured formula ∃x(x < y) under the constant-one assignment, with x = 0. -/
@[blueprint "chap5__example_5_2_5" (main := true)]
theorem captureExample_5_2_5_satisfiable :
    formulaEval natStructure Syntax.Substitution.captureExample_5_2_5_before
      (fun _ => (1 : Nat)) 

-- ===================================================================
-- Example 5.3.2: Peano axioms as formulae in the arithmetic language
-- ===================================================================

/-- Example 5.3.2 (companion): build a term for a unary function applied
to a single argument term. -/
@[blueprint "chap5__example_5_3_1"]
def mkSucc (t : Term peanoLanguage) : Term peanoLanguage :=
  Term.func ArithFunc.succ (vec1 t)

/-- Example 5.3.2 (companion): build a term for addition of two argument
terms. -/
@[blueprint "chap5__example_5_3_1"]
def mkPlus (t1 t2 : Term peanoLanguage) : Term peanoLanguage :=
  Term.func ArithFunc.plus (vec2 t1 t2)

/-- Example 5.3.2 (companion): build a term for multiplication of two
argument terms. -/
@[blueprint "chap5__example_5_3_1"]
def mkTimes (t1 t2 : Term peanoLanguage) : Term peanoLanguage :=
  Term.func ArithFunc.times (vec2 t1 t2)

/-- Example 5.3.2 (companion): the constant zero term. -/
@[blueprint "chap5__example_5_3_1"]
def zeroTerm : Term peanoLanguage :=
  Term.const ArithConst.zero

/-- Example 5.3.2: The Peano axiom forall x, neg(S(x) =. 0).
Successor of any number is not zero. -/
@[blueprint "chap5__example_5_3_2"]
def peanoSuccNonZero : Formula peanoLanguage :=
  Formula.all 0
    (Formula.neg
      (Formula.eq_ rfl (mkSucc (Term.var 0)) zeroTerm))

/-- Example 5.3.2: The Peano axiom forall x forall y(S(x) =. S(y)
supset x =. y). Successor is injective. -/
@[blueprint "chap5__example_5_3_2"]
def peanoSuccInj : Formula peanoLanguage :=
  Formula.all 0 (Formula.all 1
    (Formula.impl
      (Formula.eq_ rfl (mkSucc (Term.var 0)) (mkSucc (Term.var 1)))
      (Formula.eq_ rfl (Term.var 0) (Term.var 1))))

/-- Example 5.3.2: The Peano axiom forall x(x + 0 =. x).
Adding zero is identity. -/
@[blueprint "chap5__example_5_3_2"]
def peanoAddBase : Formula peanoLanguage :=
  Formula.all 0
    (Formula.eq_ rfl (mkPlus (Term.var 0) zeroTerm) (Term.var 0))

/-- Example 5.3.2: The Peano axiom forall x forall y(x + S(y) =.
S(x + y)). Addition distributes over successor. -/
@[blueprint "chap5__example_5_3_2"]
def peanoAddSucc : Formula peanoLanguage :=
  Formula.all 0 (Formula.all 1
    (Formula.eq_ rfl
      (mkPlus (Term.var 0) (mkSucc (Term.var 1)))
      (mkSucc (mkPlus (Term.var 0) (Term.var 1)))))

/-- Example 5.3.2: The Peano axiom forall x(x * 0 =. 0).
Multiplying by zero gives zero. -/
@[blueprint "chap5__example_5_3_2"]
def peanoMulBase : Formula peanoLanguage :=
  Formula.all 0
    (Formula.eq_ rfl (mkTimes (Term.var 0) zeroTerm) zeroTerm)

/-- Example 5.3.2: The Peano axiom forall x forall y(x * S(y) =.
x * y + x). Multiplication distributes over successor. -/
@[blueprint "chap5__example_5_3_2"]
def peanoMulSucc : Formula peanoLanguage :=
  Formula.all 0 (Formula.all 1
    (Formula.eq_ rfl
      (mkTimes (Term.var 0) (mkSucc (Term.var 1)))
      (mkPlus (mkTimes (Term.var 0) (Term.var 1)) (Term.var 0))))

/-- Example 5.3.2 (companion): The list of 6 Peano axioms (excluding
the induction scheme). -/
@[blueprint "chap5__example_5_3_2"]
def peanoAxioms : List (Formula peanoLanguage) :=
  [ peanoSuccNonZero
  , peanoSuccInj
  , peanoAddBase
  , peanoAddSucc
  , peanoMulBase
  , peanoMulSucc
  ]

/-- Example 5.3.2: The set A_P of Peano arithmetic axioms in the predicate-free
language: the six displayed axioms and every induction instance
(A(0) ∧ ∀x(A(x) ⊃ A(S(x)))) ⊃ ∀y A(y), where FV(A) = {x} and y is free
for x in A. Here A(t) denotes substitution of t for x in A. -/
@[blueprint "chap5__example_5_3_2" (main := true)]
def peanoAP : Set (Formula peanoLanguage) := fun F =>
  F ∈ peanoAxioms ∨
    ∃ (A : Formula peanoLanguage) (x y : Nat),
      Syntax.Variables.formulaFV A = Set.singleton x ∧
      Syntax.Substitution.isFreeFor (Term.var y) x A ∧
      F = Formula.impl
        (Formula.conj
          (Syntax.Substitution.formulaSubst A zeroTerm x)
          (Formula.all x (Formula.impl A
            (Syntax.Substitution.formulaSubst A (mkSucc (Term.var x)) x))))
        (Formula.all y (Syntax.Substitution.formulaSubst A (Term.var y) x))

/-- Example 5.3.2: Every Peano arithmetic axiom is valid in the
natural-number structure 𝒩. -/
theorem peanoAP_validIn (A : Formula peanoLanguage) (hA : A ∈ peanoAP) :
    validIn peanoNatStructure A := by
  rcases hA with hA | ⟨B, x, y, hFV, hFree, rfl⟩
  · simp only [peanoAxioms, List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [validIn, peanoSuccNonZero, peanoSuccInj, peanoAddBase,
        peanoAddSucc, peanoMulBase, peanoMulSucc, formulaEval, termEval,
        mkSucc, mkPlus, mkTimes, zeroTerm, peanoNatStructure, vec1, vec2,
        assignUpdate, Nat.add_assoc, Nat.mul_succ]
  · -- REPAIR(T126): proof pending
    sorry

/-- Example 5.3.2: The natural-number structure 𝒩 is a model of A_P. -/
@[blueprint "chap5__example_5_3_2" (main := true)]
theorem peanoNatStructure_isModel : isModelSet peanoNatStructure peanoAP 

/-- Example 5.3.2: In every structure with a one-element carrier, the first
Peano axiom, ∀x ¬(S(x) ≐ 0), is not valid. -/
@[blueprint "chap5__example_5_3_2" (main := true)]
theorem peanoSuccNonZero_not_validIn_subsingleton (M : Structure peanoLanguage)
    [Subsingleton M.carrier] : ¬ validIn M peanoSuccNonZero 

/-- Example 5.3.2: The set A_P is not valid in all structures. -/
@[blueprint "chap5__example_5_3_2"]
theorem peanoAP_not_validSet : ¬ validSet peanoAP 

end LCS.FirstOrder.Semantics
