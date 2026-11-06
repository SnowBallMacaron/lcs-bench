import LCS.Item
import LCS.Util
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Semantics.Equivalence
import LCS.FirstOrder.SemanticsN.Substitution
import Attach
import LCS.Herbrand.PrenexForm.PrenexFormulas.ProofsStamp

/-! # Herbrand.PrenexForm.PrenexFormulas
    Chapter 7, Section 2.1: Definition 7.2.1 (prenex form). A formula is
    prenex iff it is quantifier-free or of the form Q1 x1 ... Qn xn B with B
    quantifier-free; its quantifier prefix and its matrix.

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.PrenexForm
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Equivalence
open LCS.FirstOrder.Semantics.Subformulae

/-- Definition 7.2.1 (companion type): An enumeration of the two quantifier kinds: universal (forall) and existential (exists). Each Q_i in the quantifier prefix of a prenex formula belongs to {forall, exists}. -/
@[blueprint "chap7__definition_7_2_1"]
inductive QuantifierKind : Type where
  /-- Universal quantifier (forall) -/
  | universal : QuantifierKind
  /-- Existential quantifier (exists) -/
  | existential : QuantifierKind

-- ===================================================================
-- Definition 7.2.1 (companion): isPrenex
-- ===================================================================

/-- Definition 7.2.1: A formula is a prenex formula (or in prenex form) iff either it contains no quantifiers, or it is of the form Q_1 x_1 ... Q_n x_n B where B is quantifier-free. Defined recursively: isPrenex A holds if FirstOrder.SemanticsN.isQuantifierFree A, or A = all x B with isPrenex B, or A = ex x B with isPrenex B. -/
@[blueprint "chap7__definition_7_2_1" (main := true)]
def isPrenex {L : Language} : FormulaN L → Prop
  | .all _ A => isPrenex A
  | .ex _ A => isPrenex A
  | A => FirstOrder.SemanticsN.isQuantifierFree A

-- ===================================================================
-- Definition 7.2.1 (companion): prenexMatrix
-- ===================================================================

/-- Definition 7.2.1 (companion def): Extracts the quantifier-free matrix B from a formula by stripping all leading quantifiers. For a prenex formula Q_1 x_1 ... Q_n x_n B, this returns B. -/

@[blueprint "chap7__definition_7_2_1"]
def prenexMatrix {L : Language} : FormulaN L → FormulaN L
  | .all _ A => prenexMatrix A
  | .ex _ A => prenexMatrix A
  | A => A

-- ===================================================================
-- Definition 7.2.1 (companion): prenexPrefix
-- ===================================================================

/-- Definition 7.2.1 (companion def): Extracts the quantifier prefix as a list of (quantifier kind, variable) pairs. For a prenex formula Q_1 x_1 ... Q_n x_n B, this returns [(Q_1, x_1), ..., (Q_n, x_n)]. -/
@[blueprint "chap7__definition_7_2_1"]
def prenexPrefix {L : Language} :
    FormulaN L → List (QuantifierKind × Nat)
  | .all x A => (QuantifierKind.universal, x) :: prenexPrefix A
  | .ex x A => (QuantifierKind.existential, x) :: prenexPrefix A
  | _ => []

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

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
/-- A quantifier-free formula is prenex. The isPrenex predicate reduces
    to FirstOrder.SemanticsN.isQuantifierFree for non-quantifier formulas. -/
theorem qf_isPrenex {L : Language} (A : FormulaN L)
    (h : FirstOrder.SemanticsN.isQuantifierFree A) : isPrenex A := by
-- BEGIN PROOF
  cases A <;> first | exact h | exact h.elim

end LCS.Herbrand.PrenexForm
