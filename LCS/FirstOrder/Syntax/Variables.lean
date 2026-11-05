import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.Syntax
import Attach
import LCS.FirstOrder.Syntax.Variables.ProofsStamp

/-! # FirstOrder.Syntax.Variables
    Formalization of Chapter 5, Section 5.2.4.
    Free and bound variables.
-/

open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax

namespace LCS.FirstOrder.Syntax.Variables

-- ===================================================================
-- Definition 5.2.4: Free variables of terms and formulae
-- ===================================================================

/-- Definition 5.2.4: The set FV(A) of free variables of a formula A,
defined by recursion on the structure of A. -/
@[blueprint "chap5__definition_5_2_4" (main := true)]
def formulaFV {L : Language} : Formula L → Set Nat
  | .falsum => ∅
  | .pred0 _ _ => ∅
  | .predN P _ ts =>
    Set.iUnion (fun (j : Fin (L.predArity P)) => termFV (ts j))
  | .eq_ _ t1 t2 => termFV t1 ∪ termFV t2
  | .neg A => formulaFV A
  | .conj A B => formulaFV A ∪ formulaFV B
  | .disj A B => formulaFV A ∪ formulaFV B
  | .impl A B => formulaFV A ∪ formulaFV B
  | .equiv_ A B => formulaFV A ∪ formulaFV B
  | .all i A => formulaFV A \ Set.singleton i
  | .ex i A => formulaFV A \ Set.singleton i

namespace Formula

/-- Definition 5.2.4 (companion): A formula A is closed if FV(A) = empty,
i.e., it contains no free variables. -/
@[blueprint "chap5__definition_5_2_4" (main := true)]
def isClosed {L : Language} (A : Formula L) : Prop :=
  formulaFV A = ∅

/-- Definition 5.2.4 (companion): A sentence is a closed formula. -/
@[blueprint "chap5__definition_5_2_4"]
abbrev isSentence {L : Language} (A : Formula L) : Prop :=
  Formula.isClosed A

/-- Definition 5.2.4 (companion): A formula is open if it contains no quantifiers.
Defined by recursion: True for non-quantifier constructors (with
recursive check on subformulae), False for all/ex. -/
@[blueprint "chap5__definition_5_2_4" (main := true)]
def isOpen {L : Language} : Formula L → Prop
  | .falsum => True
  | .pred0 _ _ => True
  | .predN _ _ _ => True
  | .eq_ _ _ _ => True
  | .neg A => isOpen A
  | .conj A B => isOpen A ∧ isOpen B
  | .disj A B => isOpen A ∧ isOpen B
  | .impl A B => isOpen A ∧ isOpen B
  | .equiv_ A B => isOpen A ∧ isOpen B
  | .all _ _ => False
  | .ex _ _ => False

end Formula

-- ===================================================================
-- Definition 5.2.5: Bound variables of formulae
-- ===================================================================

/-- Definition 5.2.5: The set BV(A) of bound variables of a formula A,
defined by recursion on the structure of A. In forall x_i A or exists x_i A, the variable x_i is bound by the quantifier. -/
@[blueprint "chap5__definition_5_2_5" (main := true)]
def formulaBV {L : Language} : Formula L → Set Nat
  | .falsum => ∅
  | .pred0 _ _ => ∅
  | .predN _ _ _ => ∅
  | .eq_ _ _ _ => ∅
  | .neg A => formulaBV A
  | .conj A B => formulaBV A ∪ formulaBV B
  | .disj A B => formulaBV A ∪ formulaBV B
  | .impl A B => formulaBV A ∪ formulaBV B
  | .equiv_ A B => formulaBV A ∪ formulaBV B
  | .all i A => formulaBV A ∪ Set.singleton i
  | .ex i A => formulaBV A ∪ Set.singleton i

/-- Definition 5.2.5 (companion): Free and bound variable sets can overlap
when the language has equality or a predicate of positive arity. -/
@[blueprint "chap5__definition_5_2_5"]
theorem fv_bv_overlap_possible {L : Language}
    (h : L.hasEquality = true ∨ ∃ P, 0 < L.predArity P) :
    ∃ (A : Formula L) (x : Nat), x ∈ formulaFV A ∧ x ∈ formulaBV A 

-- ===================================================================
-- Example 5.2.3: Formula A with overlapping FV and BV
-- ===================================================================

/-- Example 5.2.3 (companion): Predicate symbols for the example language —
R (binary) and P (unary). -/
@[blueprint "chap5__example_5_2_3"]
inductive ExPred_5_2_3 : Type where
  | R : ExPred_5_2_3
  | P : ExPred_5_2_3

/-- Example 5.2.3 (companion): The language with predicates R (arity 2)
and P (arity 1), no function symbols or constants. -/
@[blueprint "chap5__example_5_2_3"]
def exampleLang_5_2_3 : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := Empty
  predSymbols := ExPred_5_2_3
  predArity := fun
    | .R => 2
    | .P => 1

/-- Example 5.2.3: The subformula B = forall x(Rxy impl Px),
where x = 0, y = 1. FV(B) = {y}, BV(B) = {x}. -/
@[blueprint "chap5__example_5_2_3"]
def exampleFormulaB_5_2_3 : Formula exampleLang_5_2_3 :=
  Formula.all 0
    (Formula.impl
      (Formula.predN ExPred_5_2_3.R (by decide)
        (vec2 (Term.var 0) (Term.var 1)))
      (Formula.predN ExPred_5_2_3.P (by decide)
        (fun _ => Term.var 0)))

/-- Example 5.2.3: The subformula C = forall y(not Rxy and
forall x Px), where x = 0, y = 1. FV(C) = {x}, BV(C) = {x, y}. -/
@[blueprint "chap5__example_5_2_3"]
def exampleFormulaC_5_2_3 : Formula exampleLang_5_2_3 :=
  Formula.all 1
    (Formula.conj
      (Formula.neg
        (Formula.predN ExPred_5_2_3.R (by decide)
          (vec2 (Term.var 0) (Term.var 1))))
      (Formula.all 0
        (Formula.predN ExPred_5_2_3.P (by decide)
          (fun _ => Term.var 0))))

/-- Example 5.2.3: The formula A = (forall x(Rxy impl Px) and forall y(not
Rxy and forall x Px)), where x = 0, y = 1. FV(A) = {x, y}, BV(A) = {x, y}. Demonstrates that a variable can be both free and bound in the same formula. -/
@[blueprint "chap5__example_5_2_3"]
def exampleFormulaA_5_2_3 : Formula exampleLang_5_2_3 :=
  Formula.conj exampleFormulaB_5_2_3 exampleFormulaC_5_2_3

/-- Example 5.2.3: FV(A) = {x, y}, with x = 0 and y = 1. -/
@[blueprint "chap5__example_5_2_3" (main := true)]
theorem exampleFormulaA_5_2_3_fv :
    formulaFV exampleFormulaA_5_2_3 = Set.singleton 0 ∪ Set.singleton 1 



/-- Example 5.2.3: FV(B) = {y}, with x = 0 and y = 1. -/
@[blueprint "chap5__example_5_2_3" (main := true)]
theorem exampleFormulaB_5_2_3_fv :
    formulaFV exampleFormulaB_5_2_3 = Set.singleton 1 



/-- Example 5.2.3: FV(C) = {x}, with x = 0 and y = 1. -/
@[blueprint "chap5__example_5_2_3" (main := true)]
theorem exampleFormulaC_5_2_3_fv :
    formulaFV exampleFormulaC_5_2_3 = Set.singleton 0 



end LCS.FirstOrder.Syntax.Variables
