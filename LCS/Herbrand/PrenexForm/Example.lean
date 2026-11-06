import LCS.Item
import LCS.Util
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Semantics.Equivalence
import LCS.FirstOrder.SemanticsN.Substitution
import LCS.Herbrand.PrenexForm.PrenexFormulas
import LCS.Herbrand.PrenexForm.Equivalences
import Attach
import LCS.Herbrand.PrenexForm.Example.ProofsStamp

/-! # Herbrand.PrenexForm.Example
    Chapter 7, Section 2.1: Example 7.2.1, the step-by-step conversion of a
    formula into prenex form with the equivalence of each displayed step.

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.PrenexForm
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Equivalence
open LCS.FirstOrder.Semantics.Subformulae

-- ===================================================================
-- Example 7.2.1 (companion type): ExPred_7_2_1
-- ===================================================================

/-- Example 7.2.1 (companion type): Predicate symbols for Example 7.2.1: unary P, unary Q, and binary R. These are the nonlogical predicate symbols used in the example formula A = forall x(P(x) or not exists y(Q(y) and R(x,y))) or not(P(y) and not forall x P(x)). -/
@[blueprint "chap7__example_7_2_1"]
inductive ExPred_7_2_1 : Type where
  /-- Unary predicate P -/
  | P : ExPred_7_2_1
  /-- Unary predicate Q -/
  | Q : ExPred_7_2_1
  /-- Binary predicate R -/
  | R : ExPred_7_2_1

-- ===================================================================
-- Example 7.2.1: Language and formula definitions
-- ===================================================================

/-- Example 7.2.1 (companion def): The arity function for ExPred_7_2_1:
    P has arity 1, Q has arity 1, R has arity 2. -/
@[blueprint "chap7__example_7_2_1"]
def exPredArity_7_2_1 : ExPred_7_2_1 → Nat
  | .P => 1
  | .Q => 1
  | .R => 2

/-- Example 7.2.1 (companion def): Language with predicates P (arity 1),
    Q (arity 1), R (arity 2), no function or constant symbols. -/
@[blueprint "chap7__example_7_2_1"]
def exLang_7_2_1 : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := Empty
  predSymbols := ExPred_7_2_1
  predArity := exPredArity_7_2_1

-- Variable assignments for Example 7.2.1: x = 0, y = 1, v = 2, z = 3

/-- Example 7.2.1: The original formula A (x = 0, y = 1):
    A = forall x(P(x) or not exists y(Q(y) and R(x, y))) or not(P(y) and not forall x P(x)). -/
@[blueprint "chap7__example_7_2_1"]
def exampleFormula_7_2_1 : FormulaN exLang_7_2_1 :=
  FormulaN.disj
    (FormulaN.all 0
      (FormulaN.disj
        (FormulaN.predN ExPred_7_2_1.P (fun _ => Term.var 0))
        (FormulaN.neg
          (FormulaN.ex 1
            (FormulaN.conj
              (FormulaN.predN ExPred_7_2_1.Q (fun _ => Term.var 1))
              (FormulaN.predN ExPred_7_2_1.R
                (vec2 (Term.var 0) (Term.var 1))))))))
    (FormulaN.neg
      (FormulaN.conj
        (FormulaN.predN ExPred_7_2_1.P (fun _ => Term.var 1))
        (FormulaN.neg
          (FormulaN.all 0
            (FormulaN.predN ExPred_7_2_1.P
              (fun _ => Term.var 0))))))

/-- Example 7.2.1: Prenex form of not exists y(Q(y) and R(x, y)):
    forall y not(Q(y) and R(x, y)). -/
@[blueprint "chap7__example_7_2_1"]
def exPrenexStep1_7_2_1 : FormulaN exLang_7_2_1 :=
  FormulaN.all 1
    (FormulaN.neg
      (FormulaN.conj
        (FormulaN.predN ExPred_7_2_1.Q (fun _ => Term.var 1))
        (FormulaN.predN ExPred_7_2_1.R
          (vec2 (Term.var 0) (Term.var 1)))))

/-- Example 7.2.1: Prenex form of forall x(P(x) or not exists y(Q(y) and R(x, y))):
    forall x forall y(P(x) or not(Q(y) and R(x, y))). -/
@[blueprint "chap7__example_7_2_1"]
def exPrenexStep2_7_2_1 : FormulaN exLang_7_2_1 :=
  FormulaN.all 0
    (FormulaN.all 1
      (FormulaN.disj
        (FormulaN.predN ExPred_7_2_1.P (fun _ => Term.var 0))
        (FormulaN.neg
          (FormulaN.conj
            (FormulaN.predN ExPred_7_2_1.Q (fun _ => Term.var 1))
            (FormulaN.predN ExPred_7_2_1.R
              (vec2 (Term.var 0) (Term.var 1)))))))

/-- Example 7.2.1: Prenex form of not forall x P(x):
    exists x not P(x). -/
@[blueprint "chap7__example_7_2_1"]
def exPrenexStep3_7_2_1 : FormulaN exLang_7_2_1 :=
  FormulaN.ex 0
    (FormulaN.neg
      (FormulaN.predN ExPred_7_2_1.P (fun _ => Term.var 0)))

/-- Example 7.2.1: Prenex form of (P(y) and not forall x P(x)):
    exists x(P(y) and not P(x)). -/
@[blueprint "chap7__example_7_2_1"]
def exPrenexStep4_7_2_1 : FormulaN exLang_7_2_1 :=
  FormulaN.ex 0
    (FormulaN.conj
      (FormulaN.predN ExPred_7_2_1.P (fun _ => Term.var 1))
      (FormulaN.neg
        (FormulaN.predN ExPred_7_2_1.P (fun _ => Term.var 0))))

/-- Example 7.2.1: Prenex form of not(P(y) and not forall x P(x)):
    forall x not(P(y) and not P(x)). -/
@[blueprint "chap7__example_7_2_1"]
def exPrenexStep5_7_2_1 : FormulaN exLang_7_2_1 :=
  FormulaN.all 0
    (FormulaN.neg
      (FormulaN.conj
        (FormulaN.predN ExPred_7_2_1.P (fun _ => Term.var 1))
        (FormulaN.neg
          (FormulaN.predN ExPred_7_2_1.P (fun _ => Term.var 0)))))

/-- Example 7.2.1: Final prenex form of A (y -> v = 2, x -> z = 3; y = 1 remains free):
    forall x forall v forall z((P(x) or not(Q(v) and R(x, v))) or not(P(y) and not P(z))). -/
@[blueprint "chap7__example_7_2_1"]
def exPrenexFinal_7_2_1 : FormulaN exLang_7_2_1 :=
  FormulaN.all 0
    (FormulaN.all 2
      (FormulaN.all 3
        (FormulaN.disj
          (FormulaN.disj
            (FormulaN.predN ExPred_7_2_1.P (fun _ => Term.var 0))
            (FormulaN.neg
              (FormulaN.conj
                (FormulaN.predN ExPred_7_2_1.Q
                  (fun _ => Term.var 2))
                (FormulaN.predN ExPred_7_2_1.R
                  (vec2 (Term.var 0) (Term.var 2))))))
          (FormulaN.neg
            (FormulaN.conj
              (FormulaN.predN ExPred_7_2_1.P
                (fun _ => Term.var 1))
              (FormulaN.neg
                (FormulaN.predN ExPred_7_2_1.P
                  (fun _ => Term.var 3))))))))

/-- Example 7.2.1: The prenex form of exampleFormula_7_2_1 is exPrenexFinal_7_2_1. -/
@[blueprint "chap7__example_7_2_1" (main := true)]
theorem exPrenex_equiv_7_2_1 :
    foLogEquivN exampleFormula_7_2_1 exPrenexFinal_7_2_1

end LCS.Herbrand.PrenexForm

namespace LCS.Herbrand.PrenexForm
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Equivalence
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN.Substitution

-- ===================================================================
-- Example 7.2.1: The five displayed intermediate equivalences
-- ===================================================================

/-- Example 7.2.1 (companion): ¬∃y(Q(y)∧R(x,y)) is equivalent to the
stored ∀y¬(Q(y)∧R(x,y)); x=0 remains free and y=1 remains bound. -/
@[blueprint "chap7__example_7_2_1" (main := true)]
theorem exPrenexStep1_equiv_7_2_1 :
    foLogEquivN
      (.neg (.ex 1 (.conj
        (.predN ExPred_7_2_1.Q (fun _ => .var 1))
        (.predN ExPred_7_2_1.R (vec2 (.var 0) (.var 1))))))
      exPrenexStep1_7_2_1

/-- Example 7.2.1 (companion): The complete displayed left subformula
∀x(P(x)∨¬∃y(Q(y)∧R(x,y))) is equivalent to stored step 2, with prefix ∀x∀y. -/
@[blueprint "chap7__example_7_2_1" (main := true)]
theorem exPrenexStep2_equiv_7_2_1 :
    foLogEquivN
      (.all 0 (.disj (.predN ExPred_7_2_1.P (fun _ => .var 0))
        (.neg (.ex 1 (.conj
          (.predN ExPred_7_2_1.Q (fun _ => .var 1))
          (.predN ExPred_7_2_1.R (vec2 (.var 0) (.var 1))))))))
      exPrenexStep2_7_2_1

/-- Example 7.2.1 (companion): ¬∀xP(x) is equivalent to the stored ∃x¬P(x),
retaining the printed binder x=0. -/
@[blueprint "chap7__example_7_2_1" (main := true)]
theorem exPrenexStep3_equiv_7_2_1 :
    foLogEquivN
      (.neg (.all 0 (.predN ExPred_7_2_1.P (fun _ => .var 0))))
      exPrenexStep3_7_2_1

/-- Example 7.2.1 (companion): P(y)∧¬∀xP(x) is equivalent to the stored
∃x(P(y)∧¬P(x)); y=1 stays free outside the x=0 binder. -/
@[blueprint "chap7__example_7_2_1" (main := true)]
theorem exPrenexStep4_equiv_7_2_1 :
    foLogEquivN
      (.conj (.predN ExPred_7_2_1.P (fun _ => .var 1))
        (.neg (.all 0 (.predN ExPred_7_2_1.P (fun _ => .var 0)))))
      exPrenexStep4_7_2_1

/-- Example 7.2.1 (companion): ¬(P(y)∧¬∀xP(x)) is equivalent to the stored
∀x¬(P(y)∧¬P(x)), retaining its free y and printed x scope. -/
@[blueprint "chap7__example_7_2_1" (main := true)]
theorem exPrenexStep5_equiv_7_2_1 :
    foLogEquivN
      (.neg (.conj (.predN ExPred_7_2_1.P (fun _ => .var 1))
        (.neg (.all 0 (.predN ExPred_7_2_1.P (fun _ => .var 0))))))
      exPrenexStep5_7_2_1

end LCS.Herbrand.PrenexForm
