import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.Syntax.Substitution
import LCS.FirstOrder.Syntax.Variables
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.SemanticsN
import LCS.FirstOrder.Semantics.Substitution
import LCS.Propositional.Syntax
import LCS.Propositional.Semantics
import Attach
import LCS.FirstOrder.Semantics.Subformulae.RectifiedFormulae.ProofsStamp

section
namespace LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax
open LCS.FirstOrder.Syntax.Substitution
open LCS.FirstOrder.Syntax.Variables
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics
open LCS.FirstOrder.Semantics.Substitution (coincidenceLemma)

/-- Definition 5.3.9: Subformulae of full first-order formulae. Every
formula is a subformula of itself, including falsum and atomic formulae.
Binary connectives include primitive equivalence. Under a quantifier,
subformulae come from a substitution instance B[t/x] for some term t
free for x in B. -/
@[blueprint "chap5__definition_5_3_9" (main := true)]
inductive IsSubformulaF {L : Language} : Formula L → Formula L → Prop where
  /-- Every formula is a subformula of itself. -/
  | refl : (A : Formula L) → IsSubformulaF A A
  | conjLeft : IsSubformulaF X B → IsSubformulaF X (Formula.conj B C)
  | conjRight : IsSubformulaF X C → IsSubformulaF X (Formula.conj B C)
  | disjLeft : IsSubformulaF X B → IsSubformulaF X (Formula.disj B C)
  | disjRight : IsSubformulaF X C → IsSubformulaF X (Formula.disj B C)
  | implLeft : IsSubformulaF X B → IsSubformulaF X (Formula.impl B C)
  | implRight : IsSubformulaF X C → IsSubformulaF X (Formula.impl B C)
  | equivLeft : IsSubformulaF X B → IsSubformulaF X (Formula.equiv_ B C)
  | equivRight : IsSubformulaF X C → IsSubformulaF X (Formula.equiv_ B C)
  | negSub : IsSubformulaF X B → IsSubformulaF X (Formula.neg B)
  /-- Subformulae of a free-for instance of the universally quantified body. -/
  | allSub : (t : Term L) → isFreeFor t i B →
      IsSubformulaF X (formulaSubst B t i) → IsSubformulaF X (Formula.all i B)
  /-- Subformulae of a free-for instance of the existentially quantified body. -/
  | exSub : (t : Term L) → isFreeFor t i B →
      IsSubformulaF X (formulaSubst B t i) → IsSubformulaF X (Formula.ex i B)

/-- Definition 5.3.9 (companion on normalized formulae): Given a formula A, a formula X is a subformula of A
if either: (i) X = A (reflexivity — covers all base cases: predicate application, equality), (iv) A = (B * C) for * in {and, or, supset} and X is a subformula of B or C, (v) A = neg B and X is a subformula of B, (vi) A = forall x B and X is a subformula of B[t/x] for some term t free for x in B, (vii) A = exists x B and X is a subformula of B[t/x] for some term t free for x in B. The inductive relation IsSubformula X A holds iff X is a subformula of A according to Definition 5.3.9. The base cases (atomic formulae) are uniformly captured by the refl constructor: any formula is a subformula of itself. The quantifier cases quantify existentially over witness terms t. -/
@[blueprint "chap5__definition_5_3_9"]
inductive IsSubformula {L : Language} :
    FormulaN L → FormulaN L → Prop where
  /-- Reflexivity: every formula is a subformula of itself.
      Covers cases (i)-(ii): predicate application and equality
      as base cases. -/
  | refl : (A : FormulaN L) → IsSubformula A A
  /-- Case (iv) left: X is a subformula of B implies X is a
      subformula of (B and C). -/
  | conjLeft : IsSubformula X B →
      IsSubformula X (FormulaN.conj B C)
  /-- Case (iv) right: X is a subformula of C implies X is a
      subformula of (B and C). -/
  | conjRight : IsSubformula X C →
      IsSubformula X (FormulaN.conj B C)
  /-- Case (iv) left: X is a subformula of B implies X is a
      subformula of (B or C). -/
  | disjLeft : IsSubformula X B →
      IsSubformula X (FormulaN.disj B C)
  /-- Case (iv) right: X is a subformula of C implies X is a
      subformula of (B or C). -/
  | disjRight : IsSubformula X C →
      IsSubformula X (FormulaN.disj B C)
  /-- Case (iv) left: X is a subformula of B implies X is a
      subformula of (B supset C). -/
  | implLeft : IsSubformula X B →
      IsSubformula X (FormulaN.impl B C)
  /-- Case (iv) right: X is a subformula of C implies X is a
      subformula of (B supset C). -/
  | implRight : IsSubformula X C →
      IsSubformula X (FormulaN.impl B C)
  /-- Case (v): X is a subformula of B implies X is a subformula
      of (neg B). -/
  | negSub : IsSubformula X B →
      IsSubformula X (FormulaN.neg B)
  /-- Case (vi): For A = forall x_i B, X is a subformula of A if
      there exists a term t free for x_i in B such that X is a
      subformula of B[t/x_i]. -/
  | allSub : (t : Term L) → isFreeForN t i B →
      IsSubformula X (formulaSubstN B t i) →
      IsSubformula X (FormulaN.all i B)
  /-- Case (vii): For A = exists x_i B, X is a subformula of A if
      there exists a term t free for x_i in B such that X is a
      subformula of B[t/x_i]. -/
  | exSub : (t : Term L) → isFreeForN t i B →
      IsSubformula X (formulaSubstN B t i) →
      IsSubformula X (FormulaN.ex i B)

-- ===================================================================
-- Definition 5.3.10: Rectified formulae
-- ===================================================================

/-- Definition 5.3.10 (companion): A formula occurrence address. The root
is [], binary children are 0 and 1, and a unary or quantifier body is child 0. -/
@[blueprint "chap5__definition_5_3_10"]
abbrev FormulaPosition := List Nat

namespace Formula

/-- Definition 5.3.10 (companion): The formula at a syntactic occurrence
address, or none if the address does not select a subformula. -/
@[blueprint "chap5__definition_5_3_10"]
def subformulaAt {L : Language} : Formula L → FormulaPosition → Option (Formula L)
  | A, [] => some A
  | .conj B _, 0 :: pos | .disj B _, 0 :: pos
  | .impl B _, 0 :: pos | .equiv_ B _, 0 :: pos => subformulaAt B pos
  | .conj _ C, 1 :: pos | .disj _ C, 1 :: pos
  | .impl _ C, 1 :: pos | .equiv_ _ C, 1 :: pos => subformulaAt C pos
  | .neg B, 0 :: pos | .all _ B, 0 :: pos | .ex _ B, 0 :: pos => subformulaAt B pos
  | _, _ => none

end Formula

/-- Definition 5.3.10 (companion): An address of a variable occurrence,
either the binder variable at a quantifier's formula position or a variable
inside an atomic term. Atomic arguments are zero-based (0 and 1 for equality),
and term paths follow function arguments. Binder positions include the
quantifier's own variable even when its body is vacuous. -/
@[blueprint "chap5__definition_5_3_10"]
inductive VariableOccurrence where
  | atom (formulaPos : FormulaPosition) (argument : Nat) (termPos : List Nat)
  | binder (formulaPos : FormulaPosition)

/-- Definition 5.3.10 (companion): The formula position containing an
atomic-term or binder variable occurrence. -/
@[blueprint "chap5__definition_5_3_10"]
def VariableOccurrence.formulaPos : VariableOccurrence → FormulaPosition
  | .atom p _ _ => p
  | .binder p => p

namespace Term

/-- Definition 5.3.10 (companion): Look up a variable at a term address.
Function arguments use their zero-based indices; only a variable at the
end of the path succeeds. -/
@[blueprint "chap5__definition_5_3_10"]
def variableAt {L : Language} : Term L → List Nat → Option Nat
  | .var x, [] => some x
  | .func f ts, k :: pos =>
    if h : k < L.funArity f then variableAt (ts ⟨k, h⟩) pos else none
  | _, _ => none

end Term

namespace Formula

/-- Definition 5.3.10 (companion): Look up the variable index at an
atomic-term occurrence or at the binder position of ∀x B or ∃x B.
A binder position returns x, including for a vacuous quantifier. Invalid
formula paths, atomic arguments, term paths, or binder positions return none. -/
@[blueprint "chap5__definition_5_3_10"]
def variableAt {L : Language} (A : Formula L) (occ : VariableOccurrence) : Option Nat :=
  match occ with
  | .binder p =>
    match subformulaAt A p with
    | some (.all x _) | some (.ex x _) => some x
    | _ => none
  | .atom p argument termPos =>
    match subformulaAt A p with
    | some (.predN P _ ts) =>
      if h : argument < L.predArity P then
        Term.variableAt (ts ⟨argument, h⟩) termPos
      else none
    | some (.eq_ _ s t) =>
      match argument with
      | 0 => Term.variableAt s termPos
      | 1 => Term.variableAt t termPos
      | _ => none
    | _ => none

end Formula

/-- Definition 5.3.10 (companion): A quantifier occurrence binds every
occurrence of its variable in the whole subformula it heads, including its
own binder position and matching inner binder positions. There is no freeness
condition: an inner quantifier may also bind the same occurrence. The variable's
formula position must extend the quantifier's address, excluding occurrences
outside that headed subformula. -/
@[blueprint "chap5__definition_5_3_10"]
def quantifierBindsAt {L : Language} (A : Formula L)
    (qpos : FormulaPosition) (occ : VariableOccurrence) : Prop :=
  match Formula.subformulaAt A qpos with
  | some (.all x _) | some (.ex x _) =>
    Formula.variableAt A occ = some x ∧
    ∃ rest : FormulaPosition, occ.formulaPos = qpos ++ rest
  | _ => False

/-- Definition 5.3.10 (companion): The free and bound variable sets of a
full first-order formula are disjoint. -/
@[blueprint "chap5__definition_5_3_10"]
def boundVarsFreshF {L : Language} (A : Formula L) : Prop :=
  ∀ x : Nat, ¬ (x ∈ formulaFV A ∧ x ∈ formulaBV A)

/-- Definition 5.3.10 (companion): Distinct quantifier occurrences in a
full first-order formula bind distinct variable indices. Vacuous quantifiers
count as occurrences; binary branches must have disjoint bound-variable sets. -/
@[blueprint "chap5__definition_5_3_10"]
def distinctQuantifierBindingsF {L : Language} : Formula L → Prop
  | .falsum => True
  | .pred0 _ _ => True
  | .predN _ _ _ => True
  | .eq_ _ _ _ => True
  | .neg A => distinctQuantifierBindingsF A
  | .conj A B =>
    distinctQuantifierBindingsF A ∧
    distinctQuantifierBindingsF B ∧
    (∀ x : Nat, ¬ (x ∈ formulaBV A ∧ x ∈ formulaBV B))
  | .disj A B =>
    distinctQuantifierBindingsF A ∧
    distinctQuantifierBindingsF B ∧
    (∀ x : Nat, ¬ (x ∈ formulaBV A ∧ x ∈ formulaBV B))
  | .impl A B =>
    distinctQuantifierBindingsF A ∧
    distinctQuantifierBindingsF B ∧
    (∀ x : Nat, ¬ (x ∈ formulaBV A ∧ x ∈ formulaBV B))
  | .equiv_ A B =>
    distinctQuantifierBindingsF A ∧
    distinctQuantifierBindingsF B ∧
    (∀ x : Nat, ¬ (x ∈ formulaBV A ∧ x ∈ formulaBV B))
  | .all i A =>
    distinctQuantifierBindingsF A ∧ ¬ (i ∈ formulaBV A)
  | .ex i A =>
    distinctQuantifierBindingsF A ∧ ¬ (i ∈ formulaBV A)

/-- Definition 5.3.10: A full first-order formula is rectified when its
free and bound variable sets are disjoint and distinct quantifier occurrences
bind distinct variable indices, including vacuous quantifiers. -/
@[blueprint "chap5__definition_5_3_10" (main := true)]
def isRectifiedF {L : Language} (A : Formula L) : Prop :=
  boundVarsFreshF A ∧ distinctQuantifierBindingsF A

/-- Definition 5.3.10 (companion): boundVarsFresh A holds iff FV(A) and
BV(A) are disjoint, i.e., there is no variable index in both sets.
This is condition (i) of rectified formula. -/
@[blueprint "chap5__definition_5_3_10"]
def boundVarsFresh {L : Language} (A : FormulaN L) : Prop :=
  ∀ x : Nat, ¬ (x ∈ formulaFVN A ∧ x ∈ formulaBVN A)

/-- Definition 5.3.10 (companion): distinctQuantifierBindings A holds iff
every pair of distinct quantifier occurrences in A binds distinct
variables. Defined recursively: no variable index is bound by two
different quantifier occurrences in the formula tree. -/
@[blueprint "chap5__definition_5_3_10"]
def distinctQuantifierBindings {L : Language} :
    FormulaN L → Prop
  | .predN _ _ => True
  | .eq_ _ _ _ => True
  | .neg A => distinctQuantifierBindings A
  | .conj A B =>
    distinctQuantifierBindings A ∧
    distinctQuantifierBindings B ∧
    (∀ x : Nat, ¬ (x ∈ formulaBVN A ∧ x ∈ formulaBVN B))
  | .disj A B =>
    distinctQuantifierBindings A ∧
    distinctQuantifierBindings B ∧
    (∀ x : Nat, ¬ (x ∈ formulaBVN A ∧ x ∈ formulaBVN B))
  | .impl A B =>
    distinctQuantifierBindings A ∧
    distinctQuantifierBindings B ∧
    (∀ x : Nat, ¬ (x ∈ formulaBVN A ∧ x ∈ formulaBVN B))
  | .all i A =>
    distinctQuantifierBindings A ∧
    ¬ (i ∈ formulaBVN A)
  | .ex i A =>
    distinctQuantifierBindings A ∧
    ¬ (i ∈ formulaBVN A)

/-- Definition 5.3.10 (companion on normalized formulae): A formula A is rectified if (i) FV(A) and BV(A) are
disjoint (boundVarsFresh) and (ii) distinct quantifiers in A bind occurrences of distinct variables (distinctQuantifierBindings). -/
@[blueprint "chap5__definition_5_3_10"]
def isRectified {L : Language} (A : FormulaN L) : Prop :=
  boundVarsFresh A ∧ distinctQuantifierBindings A

end LCS.FirstOrder.Semantics.Subformulae
end
