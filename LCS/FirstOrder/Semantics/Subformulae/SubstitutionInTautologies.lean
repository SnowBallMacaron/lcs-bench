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
import LCS.FirstOrder.Semantics.Subformulae.SubstitutionInTautologies.ProofsStamp

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

-- ===================================================================
-- Lemma 5.3.5: Validity of tautology instances
-- ===================================================================

/-- Lemma 5.3.5: Every full first-order formula obtained by substitution
into a tautology over L's rank-zero predicates is universally valid. -/
@[blueprint "chap5__lemma_5_3_5" (main := true)]
theorem propInstanceValid {L : Language} (A : Formula L) :
    inPROPL A → universallyValid A 

end LCS.FirstOrder.Semantics.Subformulae
end
