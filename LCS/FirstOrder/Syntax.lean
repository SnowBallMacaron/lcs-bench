import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import Attach
import LCS.FirstOrder.Syntax.ProofsStamp

/-! # FirstOrder.Syntax
    Formalization of Chapter 5, Section 5.2.1.
    Core definitions: alphabets, terms, and formulae for first-order languages.
    Source: Logic for Computer Science, Gallier 2015
-/

open LCS.FirstOrder.Basic

namespace LCS.FirstOrder.Syntax

-- ===================================================================
-- Definition 5.2.3: Formulae
-- ===================================================================

/-- Definition 5.2.3: Given a first-order language L, the set FORM_L of
L-formulae is built from atomic formulae (falsum, zero-rank predicates, n-ary predicate applications, equality) closed under connectives (conjunction, disjunction, implication, equivalence, negation) and quantifiers (universal, existential). -/
@[blueprint "chap5__definition_5_2_3" (main := true)]
inductive Formula (L : Language) : Type where
  /-- Falsum (bottom, falsity constant) is an atomic formula -/
  | falsum : Formula L
  /-- A zero-rank predicate P (with proof predArity P = 0) is an
      atomic formula (propositional symbol) -/
  | pred0 : (P : L.predSymbols) → L.predArity P = 0 → Formula L
  /-- For predicate symbol P of rank n > 0, P(t_1,...,t_n) is an atomic
      formula -/
  | predN : (P : L.predSymbols) → 0 < L.predArity P →
      (Fin (L.predArity P) → Term L) → Formula L
  /-- Equality: if t_1, t_2 are terms then t_1 =. t_2 is an atomic
      formula. Only available when `L.hasEquality = true`; the proof
      argument makes the constructor uninhabited for without-equality
      languages, faithfully realizing Def 5.2.1's "languages obtained
      by omitting the equality symbol". -/
  | eq_ : L.hasEquality = true → Term L → Term L → Formula L
  /-- Conjunction: (A /\ B) -/
  | conj : Formula L → Formula L → Formula L
  /-- Disjunction: (A \/ B) -/
  | disj : Formula L → Formula L → Formula L
  /-- Implication: (A => B) -/
  | impl : Formula L → Formula L → Formula L
  /-- Equivalence: (A <=> B) -/
  | equiv_ : Formula L → Formula L → Formula L
  /-- Negation: not A -/
  | neg : Formula L → Formula L
  /-- Universal quantification: forall x_i, A -/
  | all : Nat → Formula L → Formula L
  /-- Existential quantification: exists x_i, A -/
  | ex : Nat → Formula L → Formula L

-- ===================================================================
-- Definition 5.2.3 (companion): Formula.isAtomic
-- ===================================================================

namespace Formula

/-- Definition 5.2.3 (companion): A formula is atomic if it is falsum,
a zero-rank predicate, an n-ary predicate application, or an equality. -/
@[blueprint "chap5__definition_5_2_3" (main := true)]
def isAtomic {L : Language} : Formula L → Prop
  | .falsum      => True
  | .pred0 _ _   => True
  | .predN _ _ _   => True
  | .eq_ _ _ _   => True
  | .conj _ _    => False
  | .disj _ _    => False
  | .impl _ _    => False
  | .equiv_ _ _  => False
  | .neg _       => False
  | .all _ _     => False
  | .ex _ _      => False

end Formula

-- ===================================================================
-- Example 5.2.1: Arithmetic language
-- ===================================================================

/-- Example 5.2.1 (companion): Function symbols for the arithmetic language —
successor S (rank 1), addition + (rank 2), multiplication * (rank 2). -/
@[blueprint "chap5__example_5_2_1"]
inductive ArithFunc : Type where
  | succ  : ArithFunc
  | plus  : ArithFunc
  | times : ArithFunc

/-- Example 5.2.1 (companion): Constant symbols for the arithmetic language —
zero (rank 0). -/
@[blueprint "chap5__example_5_2_1"]
inductive ArithConst : Type where
  | zero : ArithConst

/-- Example 5.2.1 (companion): Predicate symbols for the arithmetic language —
less-than < (rank 2). -/
@[blueprint "chap5__example_5_2_1"]
inductive ArithPred : Type where
  | lt : ArithPred

/-- Example 5.2.1: The first-order language for arithmetic with
CS = {0}, FS = {S, +, *}, PS = {<}. S has rank 1; +, *, < have rank 2. -/
@[blueprint "chap5__example_5_2_1"]
def arithLanguage : Language where
  funSymbols := ArithFunc
  funArity := fun
    | .succ  => 1
    | .plus  => 2
    | .times => 2
  constSymbols := ArithConst
  predSymbols := ArithPred
  predArity := fun
    | .lt => 2

/-- Example 5.3.1: The arithmetic language with equality, CS = {0},
FS = {S, +, *}, and PS = ∅. S has rank 1; + and * have rank 2. -/
@[blueprint "chap5__example_5_3_1"]
def peanoLanguage : Language where
  funSymbols := ArithFunc
  funArity := fun
    | .succ  => 1
    | .plus  => 2
    | .times => 2
  constSymbols := ArithConst
  predSymbols := Empty
  predArity := Empty.elim
  hasEquality := true

/-- Example 5.2.1: The term S(0) in the arithmetic language — the successor
of zero, one of the sample terms demonstrated in the textbook. -/
@[blueprint "chap5__example_5_2_1" (main := true)]
def arithTerm_S0 : Term arithLanguage :=
  Term.func ArithFunc.succ (fun _ => Term.const ArithConst.zero)

/-- Example 5.2.1 (companion): The prefix term +S0SS0,
that is, S(0) + S(S(0)). -/
@[blueprint "chap5__example_5_2_1" (main := true)]
def arithTerm_plusS0SS0 : Term arithLanguage :=
  Term.func ArithFunc.plus
    (vec2 (Term.func ArithFunc.succ (vec1 (Term.const ArithConst.zero)))
      (Term.func ArithFunc.succ
        (vec1 (Term.func ArithFunc.succ (vec1 (Term.const ArithConst.zero))))))

/-- Example 5.2.1 (companion): The prefix term *x₁S+Sx₁x₂,
that is, x₁ × S(S(x₁) + x₂). -/
@[blueprint "chap5__example_5_2_1" (main := true)]
def arithTerm_timesx1Splus : Term arithLanguage :=
  Term.func ArithFunc.times
    (vec2 (Term.var 1)
      (Term.func ArithFunc.succ
        (vec1 (Term.func ArithFunc.plus
          (vec2 (Term.func ArithFunc.succ (vec1 (Term.var 1))) (Term.var 2))))))

-- ===================================================================
-- Example 5.2.2: Atomic formulae and formulae in the arithmetic language
-- ===================================================================

/-- Example 5.2.2: The atomic formula <(0, S(0)), i.e., 0 is less than S0. -/
@[blueprint "chap5__example_5_2_2" (main := true)]
def arithAtomicFormula_lt0S0 : Formula arithLanguage :=
  Formula.predN ArithPred.lt (by decide)
    (vec2 (Term.const ArithConst.zero) arithTerm_S0)

/-- Example 5.2.2: The atomic formula y =. S(x), equality of variable y
and successor of variable x. Variables: x = 0, y = 1. -/
@[blueprint "chap5__example_5_2_2" (main := true)]
def arithAtomicFormula_eq_y_Sx : Formula arithLanguage :=
  Formula.eq_ rfl (Term.var 1) (Term.func ArithFunc.succ (vec1 (Term.var 0)))

/-- Example 5.2.2: The formula ∀x∀y(x < y ⊃ ∃z(y =. +(x, z))), stating for
all x, y, if x < y then there exists z such that y = x + z. Variables: x = 0, y = 1, z = 2. -/
@[blueprint "chap5__example_5_2_2" (main := true)]
def arithFormula_subtraction_exists : Formula arithLanguage :=
  Formula.all 0 (Formula.all 1
    (Formula.impl
      (Formula.predN ArithPred.lt (by decide) (vec2 (Term.var 0) (Term.var 1)))
      (Formula.ex 2
        (Formula.eq_ rfl (Term.var 1)
          (Term.func ArithFunc.plus (vec2 (Term.var 0) (Term.var 2)))))))

/-- Example 5.2.2: The formula ∀x∀y((x < y ∨ y < x) ∨ x =. y),
the trichotomy property. Variables: x = 0, y = 1. -/
@[blueprint "chap5__example_5_2_2" (main := true)]
def arithFormula_trichotomy : Formula arithLanguage :=
  Formula.all 0 (Formula.all 1
    (Formula.disj
      (Formula.disj
        (Formula.predN ArithPred.lt (by decide) (vec2 (Term.var 0) (Term.var 1)))
        (Formula.predN ArithPred.lt (by decide) (vec2 (Term.var 1) (Term.var 0))))
      (Formula.eq_ rfl (Term.var 0) (Term.var 1))))

end LCS.FirstOrder.Syntax
