import LCS.Item
import LCS.Util
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Semantics.Equivalence
import LCS.FirstOrder.SemanticsN.Substitution
import LCS.Herbrand.PrenexForm.Part1
import LCS.Herbrand.PrenexForm.Part2

/-! # Herbrand.PrenexForm
    Formalization of Chapter 7, Section 2: Prenex Normal Form.

    Covers Definition 7.2.1 (prenex form), Lemma 7.2.1 (quantifier
    equivalences), Theorem 7.2.1 (prenex normal form existence),
    Example 7.2.1 (step-by-step prenex conversion),
    and Lemma 7.2.2 (disjunctive normal form for quantifier-free formulae).

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.PrenexForm

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Equivalence
open LCS.FirstOrder.Semantics.Subformulae

-- ===================================================================
-- Definition 7.2.1 (companion type): QuantifierKind
-- ===================================================================


-- ===================================================================
-- Theorem 7.2.1 (companion def): QuantifierKind.dual
-- ===================================================================

namespace QuantifierKind


end QuantifierKind

-- ===================================================================
-- Theorem 7.2.1 (companion def): toPrenexHelper
-- ===================================================================


-- ===================================================================
-- Lemma 7.2.1: Prenex equivalences
-- ===================================================================

open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN.Substitution

-- ===================================================================
-- Helper lemmas for Lemma 7.2.1
-- ===================================================================



end LCS.Herbrand.PrenexForm
