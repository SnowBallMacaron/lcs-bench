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
import LCS.FirstOrder.Semantics.Subformulae.Part1.ProofsStamp

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

end LCS.FirstOrder.Semantics.Subformulae
end

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
end LCS.FirstOrder.Semantics.Subformulae
end

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

end LCS.FirstOrder.Semantics.Subformulae
end

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
end LCS.FirstOrder.Semantics.Subformulae
end

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
end LCS.FirstOrder.Semantics.Subformulae
end

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

-- ===================================================================
-- Example 5.3.3: Non-rectified and rectified formulae
-- ===================================================================

/-- Example 5.3.3 (companion): Predicate symbols for the example language. -/
@[blueprint "chap5__example_5_3_3"]
inductive ExPred_5_3_3 : Type where
  | R : ExPred_5_3_3
  | P : ExPred_5_3_3

/-- Example 5.3.3 (companion): The example language with binary R and unary P. -/
@[blueprint "chap5__example_5_3_3"]
def exampleLang_5_3_3 : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := Empty
  predSymbols := ExPred_5_3_3
  predArity := fun
    | .R => 2
    | .P => 1

/-- Example 5.3.3: The non-rectified formula A = (forall x(R x y supset P
x) and forall y(neg R x y and forall x P x)), using the language with binary R and unary P, where x=0, y=1. A is not rectified because x and y each appear both free and bound, and x is bound by two distinct quantifiers. -/
@[blueprint "chap5__example_5_3_3"]
def exampleNonRectified_5_3_3 : FormulaN exampleLang_5_3_3 :=
  FormulaN.conj
    (FormulaN.all 0
      (FormulaN.impl
        (FormulaN.predN ExPred_5_3_3.R
          (vec2 (Term.var 0) (Term.var 1)))
        (FormulaN.predN ExPred_5_3_3.P
          (fun _ => Term.var 0))))
    (FormulaN.all 1
      (FormulaN.conj
        (FormulaN.neg
          (FormulaN.predN ExPred_5_3_3.R
            (vec2 (Term.var 0) (Term.var 1))))
        (FormulaN.all 0
          (FormulaN.predN ExPred_5_3_3.P
            (fun _ => Term.var 0)))))

/-- Example 5.3.3: The rectified formula B = (forall u(R u y supset P u)
and forall v(neg R x v and forall z P z)), where u=2, v=3, z=4 as fresh variable indices. B is rectified: each quantifier binds a unique variable not free elsewhere. -/
@[blueprint "chap5__example_5_3_3"]
def exampleRectified_5_3_3 : FormulaN exampleLang_5_3_3 :=
  FormulaN.conj
    (FormulaN.all 2
      (FormulaN.impl
        (FormulaN.predN ExPred_5_3_3.R
          (vec2 (Term.var 2) (Term.var 1)))
        (FormulaN.predN ExPred_5_3_3.P
          (fun _ => Term.var 2))))
    (FormulaN.all 3
      (FormulaN.conj
        (FormulaN.neg
          (FormulaN.predN ExPred_5_3_3.R
            (vec2 (Term.var 0) (Term.var 3))))
        (FormulaN.all 4
          (FormulaN.predN ExPred_5_3_3.P
            (fun _ => Term.var 4)))))



/-- Example 5.3.3: The displayed formula A is logically equivalent to
its rectified counterpart B under every structure and assignment. -/
@[blueprint "chap5__example_5_3_3" (main := true)]
theorem exampleRectified_5_3_3_equiv :
    universallyValidN (FormulaN.equiv exampleNonRectified_5_3_3
      exampleRectified_5_3_3) 



end LCS.FirstOrder.Semantics.Subformulae
end

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
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics

/-- Definition 5.3.11 (companion): Propositional formulae over an arbitrary
letter type, with primitive falsum and equivalence as in Definitions 3.2.1–3.2.2. -/
@[blueprint "chap5__definition_5_3_11"]
inductive PropFormulaOver (α : Type) : Type where
  | fls : PropFormulaOver α
  | var : α → PropFormulaOver α
  | neg : PropFormulaOver α → PropFormulaOver α
  | conj : PropFormulaOver α → PropFormulaOver α → PropFormulaOver α
  | disj : PropFormulaOver α → PropFormulaOver α → PropFormulaOver α
  | impl : PropFormulaOver α → PropFormulaOver α → PropFormulaOver α
  | equiv_ : PropFormulaOver α → PropFormulaOver α → PropFormulaOver α

/-- Definition 5.3.11 (companion): Prop-valued evaluation under an
assignment of truth values to the propositional letters. -/
@[blueprint "chap5__definition_5_3_11"]
def evalProp {α : Type} (v : α → Prop) : PropFormulaOver α → Prop
  | .fls => False
  | .var p => v p
  | .neg B => ¬ evalProp v B
  | .conj B C => evalProp v B ∧ evalProp v C
  | .disj B C => evalProp v B ∨ evalProp v C
  | .impl B C => evalProp v B → evalProp v C
  | .equiv_ B C => evalProp v B ↔ evalProp v C

/-- Definition 5.3.11 (companion): A propositional formula is a tautology
when it holds under every valuation of its letters. -/
@[blueprint "chap5__definition_5_3_11"]
def tautology {α : Type} (B : PropFormulaOver α) : Prop :=
  ∀ v : α → Prop, evalProp v B

/-- Definition 5.3.11 (companion): The propositional letters of L are
precisely its predicate symbols of rank zero. -/
@[blueprint "chap5__definition_5_3_11"]
abbrev PS0 (L : Language) := {P : L.predSymbols // L.predArity P = 0}

/-- Definition 5.3.11 (companion): Extend a substitution from L's
propositional letters to full first-order formulae homomorphically.
Falsum and equivalence are preserved as primitive constructors. -/
@[blueprint "chap5__definition_5_3_11"]
def propSubst {L : Language} (sigma : PS0 L → Formula L) :
    PropFormulaOver (PS0 L) → Formula L
  | .fls => Formula.falsum
  | .var p => sigma p
  | .neg B => Formula.neg (propSubst sigma B)
  | .conj B C => Formula.conj (propSubst sigma B) (propSubst sigma C)
  | .disj B C => Formula.disj (propSubst sigma B) (propSubst sigma C)
  | .impl B C => Formula.impl (propSubst sigma B) (propSubst sigma C)
  | .equiv_ B C => Formula.equiv_ (propSubst sigma B) (propSubst sigma C)

/-- Definition 5.3.11: PROP_L consists of substitutions into tautologies
whose letters are the rank-zero predicates of L. -/
@[blueprint "chap5__definition_5_3_11" (main := true)]
def inPROPL {L : Language} (A : Formula L) : Prop :=
  ∃ (B : PropFormulaOver (PS0 L)) (sigma : PS0 L → Formula L),
    tautology B ∧ propSubst sigma B = A

/-- Example 5.3.4: The proposition (P ≡ Q) ≡ ((P ⊃ Q) ∧ (Q ⊃ P)). -/
@[blueprint "chap5__example_5_3_4"]
def examplePropFormula_5_3_4 {α : Type} (P Q : α) : PropFormulaOver α :=
  .equiv_ (.equiv_ (.var P) (.var Q))
    (.conj (.impl (.var P) (.var Q)) (.impl (.var Q) (.var P)))



/-- Example 5.3.4: The displayed first-order instance A uses ∀x C
and ∃y(C ∧ D) in place of the propositional letters. -/
@[blueprint "chap5__example_5_3_4"]
def exampleInstance_5_3_4 {L : Language} (C D : Formula L) (x y : Nat) : Formula L :=
  .equiv_ (.equiv_ (.all x C) (.ex y (.conj C D)))
    (.conj (.impl (.all x C) (.ex y (.conj C D)))
      (.impl (.ex y (.conj C D)) (.all x C)))



/-- Example 5.3.4: The displayed A belongs to PROP_L under the specified
substitution for P and Q. -/
@[blueprint "chap5__example_5_3_4" (main := true)]
theorem exampleInstance_5_3_4_inPROPL {L : Language} (P Q : PS0 L)
    (C D : Formula L) (x y : Nat) (sigma : PS0 L → Formula L)
    (hP : sigma P = Formula.all x C)
    (hQ : sigma Q = Formula.ex y (Formula.conj C D)) :
    inPROPL (exampleInstance_5_3_4 C D x y) 

-- retained: used by LCS.FirstOrder.Semantics.Equivalence
/-- Definition 5.3.11 (companion): Propositional evaluation of a first-order
formula's outer connectives, treating every atomic or quantified formula as
false. Quantifier bodies are opaque in this propositional evaluation. -/
def propositionalSkeletonEval {L : Language} : Formula L → Prop
  | .falsum | .pred0 _ _ | .predN _ _ _ | .eq_ _ _ _ | .all _ _ | .ex _ _ => False
  | .neg A => ¬ propositionalSkeletonEval A
  | .conj A B => propositionalSkeletonEval A ∧ propositionalSkeletonEval B
  | .disj A B => propositionalSkeletonEval A ∨ propositionalSkeletonEval B
  | .impl A B => propositionalSkeletonEval A → propositionalSkeletonEval B
  | .equiv_ A B => propositionalSkeletonEval A ↔ propositionalSkeletonEval B

-- retained: used by LCS.FirstOrder.Semantics.Equivalence
/-- Definition 5.3.11 (companion): The propositional evaluation commutes
with substitution when each letter receives the value of its image. -/
theorem propositionalSkeletonEval_propSubst {L : Language}
    (sigma : PS0 L → Formula L) (B : PropFormulaOver (PS0 L)) :
    evalProp (fun p => propositionalSkeletonEval (sigma p)) B ↔
      propositionalSkeletonEval (propSubst sigma B) := by
  induction B with
  | fls => exact Iff.rfl
  | var p => exact Iff.rfl
  | neg B ih => exact not_congr ih
  | conj B C ihB ihC => exact and_congr ihB ihC
  | disj B C ihB ihC => exact or_congr ihB ihC
  | impl B C ihB ihC => exact imp_congr ihB ihC
  | equiv_ B C ihB ihC => exact iff_congr ihB ihC

-- retained: used by LCS.FirstOrder.Semantics.Equivalence
/-- Definition 5.3.11 (companion): Every PROP_L instance is true under
the propositional evaluation with false atomic and quantified formulae. -/
theorem inPROPL_propositionalSkeletonEval {L : Language} {A : Formula L}
    (h : inPROPL A) : propositionalSkeletonEval A := by
  obtain ⟨B, sigma, hB, rfl⟩ := h
  exact (propositionalSkeletonEval_propSubst sigma B).mp
    (hB (fun p => propositionalSkeletonEval (sigma p)))

/-- Definition 5.3.11 (consequence): No formula ∀x C belongs to PROP_L. -/
@[blueprint "chap5__definition_5_3_11"]
theorem forall_not_inPROPL {L : Language} (C : Formula L) (x : Nat) :
    ¬ inPROPL (Formula.all x C) 

/-- Definition 5.3.11 (consequence): No formula ∃y(C ∧ D) belongs to PROP_L. -/
@[blueprint "chap5__definition_5_3_11"]
theorem exists_conj_not_inPROPL {L : Language} (C D : Formula L) (y : Nat) :
    ¬ inPROPL (Formula.ex y (Formula.conj C D)) 

-- retained: used by LCS.FirstOrder.Semantics.Equivalence
/-- Definition 5.3.11 (consequence): The quantifier duality
¬∀x A ≡ ∃x¬A is not a propositional tautology instance. -/
theorem quantifierDuality_not_inPROPL {L : Language} (A : Formula L) (x : Nat) :
    ¬ inPROPL (Formula.equiv_ (Formula.neg (Formula.all x A))
      (Formula.ex x (Formula.neg A))) := by
  intro h
  exact (inPROPL_propositionalSkeletonEval h).mp (fun hFalse => hFalse)

-- retained: used by LCS.FirstOrder.Semantics.Subformulae.Part2
/-- Validity of normalized propositional formulae under every valuation. -/
def isValidNorm (A : PropFormulaNormalized) : Prop :=
  ∀ v : Valuation, evalExtN v A = BoolVal.T

-- retained: used by LCS.FirstOrder.Semantics.Subformulae.Part2
/-- Homomorphic substitution from normalized
propositional formulae with Nat-indexed letters into FormulaN. -/
def propSubstN {L : Language}
    (sigma : Nat → FormulaN L)
    : PropFormulaNormalized → FormulaN L
  | .var n => sigma n
  | .neg A => FormulaN.neg (propSubstN sigma A)
  | .conj A B => FormulaN.conj (propSubstN sigma A) (propSubstN sigma B)
  | .disj A B => FormulaN.disj (propSubstN sigma A) (propSubstN sigma B)
  | .impl A B => FormulaN.impl (propSubstN sigma A) (propSubstN sigma B)

-- retained: used by LCS.FirstOrder.Semantics.Subformulae.Part2
/-- A FormulaN is an instance of a
normalized propositional tautology over Nat-indexed letters. -/
def isPropInstanceN {L : Language} (A : FormulaN L) : Prop :=
  ∃ (B : PropFormulaNormalized) (sigma : Nat → FormulaN L),
    isValidNorm B ∧ A = propSubstN sigma B

-- ===================================================================
-- Helper: Term coincidence lemma (local)
-- ===================================================================

-- termCoincidence and coincidenceLemmaN imported from SemanticsN

-- ===================================================================
-- Helper: Variable substitution evaluation with isFreeForN
-- ===================================================================

-- retained: used by LCS.FirstOrder.Semantics.Subformulae.Part2
theorem termVarSubstEval {L : Language} (M : Structure L)
    (s : Assignment M) (t : Term L) (i j : Nat) :
    termEval M s (termSubst t (Term.var j) i) =
    termEval M (assignUpdate s i (s j)) t := by
-- BEGIN PROOF
  induction t with
  | var x =>
    unfold termSubst termEval
    by_cases hxi : x = i
    · subst hxi; simp [assignUpdate]
    · simp [assignUpdate, hxi]
  | const c => simp [termSubst, termEval]
  | func f ts ih =>
    simp only [termSubst, termEval]
    congr 1; funext k; exact ih k



-- retained: used by LCS.FirstOrder.Semantics.Subformulae.Part2
theorem formulaVarSubstEvalN {L : Language} (M : Structure L)
    (s : Assignment M) (A : FormulaN L) (i j : Nat)
    (hFree : isFreeForN (Term.var j) i A) :
    formulaEvalN M (formulaSubstN A (Term.var j) i) s ↔
    formulaEvalN M A (assignUpdate s i (s j)) := by
-- BEGIN PROOF
  induction A generalizing s with
  | predN P ts =>
    simp only [formulaSubstN, formulaEvalN]
    have : (fun k => termEval M s (termSubst (ts k) (Term.var j) i)) =
           (fun k => termEval M (assignUpdate s i (s j)) (ts k)) :=
      funext fun k => termVarSubstEval M s (ts k) i j
    rw [this]
  | eq_ _ t1 t2 =>
    simp only [formulaSubstN, formulaEvalN]
    rw [termVarSubstEval M s t1 i j, termVarSubstEval M s t2 i j]
  | conj A B ihA ihB =>
    simp only [isFreeForN] at hFree
    simp only [formulaSubstN, formulaEvalN]
    exact and_congr (ihA s hFree.1) (ihB s hFree.2)
  | disj A B ihA ihB =>
    simp only [isFreeForN] at hFree
    simp only [formulaSubstN, formulaEvalN]
    exact or_congr (ihA s hFree.1) (ihB s hFree.2)
  | impl A B ihA ihB =>
    simp only [isFreeForN] at hFree
    simp only [formulaSubstN, formulaEvalN]
    exact imp_congr (ihA s hFree.1) (ihB s hFree.2)
  | neg A ih =>
    simp only [isFreeForN] at hFree
    simp only [formulaSubstN, formulaEvalN]
    exact not_congr (ih s hFree)
  | all k A ih =>
    simp only [isFreeForN] at hFree
    simp only [formulaSubstN, formulaEvalN]
    by_cases hik : i = k
    · subst hik; simp; constructor <;> intro h a
      · have heq : assignUpdate (assignUpdate s i (s j)) i a = assignUpdate s i a :=
          funext fun x => by unfold assignUpdate; split <;> simp_all
        rw [heq]; exact h a
      · have heq : assignUpdate (assignUpdate s i (s j)) i a = assignUpdate s i a :=
          funext fun x => by unfold assignUpdate; split <;> simp_all
        rw [← heq]; exact h a
    · have hFreeA : isFreeForN (Term.var j) i A := by
        rcases hFree with rfl | ⟨_, h⟩
        · exact absurd rfl hik
        · exact h
      have hjk : k ≠ j := by
        intro heq
        rcases hFree with rfl | ⟨hne, _⟩
        · exact hik rfl
        · subst heq
          exact hne rfl
      simp [hik]; constructor <;> intro h a
      · have swap : assignUpdate (assignUpdate s i (s j)) k a =
            assignUpdate (assignUpdate s k a) i (s j) := by
          funext x; unfold assignUpdate
          by_cases hxk : x = k
          · subst hxk; simp [Ne.symm hik]
          · by_cases hxi : x = i
            · subst hxi; simp [hxk]
            · simp [hxk, hxi]
        rw [swap]
        have hjks : (assignUpdate s k a) j = s j := by
          unfold assignUpdate; simp [Ne.symm hjk]
        rw [← hjks]
        exact (ih (assignUpdate s k a) hFreeA).mp (h a)
      · have swap : assignUpdate (assignUpdate s i (s j)) k a =
            assignUpdate (assignUpdate s k a) i (s j) := by
          funext x; unfold assignUpdate
          by_cases hxk : x = k
          · subst hxk; simp [Ne.symm hik]
          · by_cases hxi : x = i
            · subst hxi; simp [hxk]
            · simp [hxk, hxi]
        have hjks : (assignUpdate s k a) j = s j := by
          unfold assignUpdate; simp [Ne.symm hjk]
        have ha := h a
        have combined : assignUpdate (assignUpdate s i (s j)) k a =
            assignUpdate (assignUpdate s k a) i ((assignUpdate s k a) j) := by
          rw [swap]; congr 1; exact hjks.symm
        rw [combined] at ha
        exact (ih (assignUpdate s k a) hFreeA).mpr ha
  | ex k A ih =>
    simp only [isFreeForN] at hFree
    simp only [formulaSubstN, formulaEvalN]
    by_cases hik : i = k
    · subst hik; simp; constructor <;> intro ⟨a, ha⟩ <;> refine ⟨a, ?_⟩
      · have heq : assignUpdate (assignUpdate s i (s j)) i a = assignUpdate s i a :=
          funext fun x => by unfold assignUpdate; split <;> simp_all
        rw [heq]; exact ha
      · have heq : assignUpdate (assignUpdate s i (s j)) i a = assignUpdate s i a :=
          funext fun x => by unfold assignUpdate; split <;> simp_all
        rw [← heq]; exact ha
    · have hFreeA : isFreeForN (Term.var j) i A := by
        rcases hFree with rfl | ⟨_, h⟩
        · exact absurd rfl hik
        · exact h
      have hjk : k ≠ j := by
        intro heq
        rcases hFree with rfl | ⟨hne, _⟩
        · exact hik rfl
        · subst heq
          exact hne rfl
      simp [hik]; constructor <;> intro ⟨a, ha⟩ <;> refine ⟨a, ?_⟩
      · have swap : assignUpdate (assignUpdate s i (s j)) k a =
            assignUpdate (assignUpdate s k a) i (s j) := by
          funext x; unfold assignUpdate
          by_cases hxk : x = k
          · subst hxk; simp [Ne.symm hik]
          · by_cases hxi : x = i
            · subst hxi; simp [hxk]
            · simp [hxk, hxi]
        have hjks : (assignUpdate s k a) j = s j := by
          unfold assignUpdate; simp [Ne.symm hjk]
        rw [swap, ← hjks]
        exact (ih (assignUpdate s k a) hFreeA).mp ha
      · have swap : assignUpdate (assignUpdate s i (s j)) k a =
            assignUpdate (assignUpdate s k a) i (s j) := by
          funext x; unfold assignUpdate
          by_cases hxk : x = k
          · subst hxk; simp [Ne.symm hik]
          · by_cases hxi : x = i
            · subst hxi; simp [hxk]
            · simp [hxk, hxi]
        have hjks : (assignUpdate s k a) j = s j := by
          unfold assignUpdate; simp [Ne.symm hjk]
        have combined : assignUpdate (assignUpdate s i (s j)) k a =
            assignUpdate (assignUpdate s k a) i ((assignUpdate s k a) j) := by
          rw [swap]; congr 1; exact hjks.symm
        rw [combined] at ha
        exact (ih (assignUpdate s k a) hFreeA).mpr ha

-- ===================================================================
-- Lemma 5.3.4: Alpha-equivalence and rectification
-- ===================================================================

/-- Lemma 5.3.4(i), universal: Renaming bound variable i to j
preserves the formula's meaning when j is free for i in A and
j does not occur free in A except possibly as i. -/
@[blueprint "chap5__lemma_5_3_4" (main := true)]
theorem alphaEquivUnivF {L : Language} (A : Formula L) (i j : Nat)
    (hFree : isFreeFor (Term.var j) i A)
    (hFresh : ¬ (j ∈ (formulaFV A \ Set.singleton i))) :
    universallyValid
      (Formula.equiv_ (Formula.all i A)
        (Formula.all j (formulaSubst A (Term.var j) i))) 

/-- Lemma 5.3.4(i), existential: Renaming bound variable i to j
preserves the formula's meaning when j is free for i in A and
j does not occur free in A except possibly as i. -/
@[blueprint "chap5__lemma_5_3_4" (main := true)]
theorem alphaEquivExF {L : Language} (A : Formula L) (i j : Nat)
    (hFree : isFreeFor (Term.var j) i A)
    (hFresh : ¬ (j ∈ (formulaFV A \ Set.singleton i))) :
    universallyValid
      (Formula.equiv_ (Formula.ex i A)
        (Formula.ex j (formulaSubst A (Term.var j) i))) 

end LCS.FirstOrder.Semantics.Subformulae
end

