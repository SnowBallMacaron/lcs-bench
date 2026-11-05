import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Semantics.Substitution
import LCS.Propositional.Semantics
import LCS.FirstOrder.ManySorted.Gentzen.Calculus
import LCS.FirstOrder.ManySorted.Gentzen.Completeness

/-! # FirstOrder.ManySorted.Gentzen
    Formalization of Chapter 10, Section 10.4 (Gentzen System G for
    Many-Sorted Languages Without Equality).

    The sequent calculus G with its connective and quantifier rules,
    eigenvariable conditions, and axioms (Def 10.4.1); deduction/proof
    trees (§10.4.2); soundness (Lemma 10.4.1); and Gödel's extended
    completeness theorem for G (Theorem 10.4.1).

    Builds on §10.2 syntax (LCS.FirstOrder.ManySorted) and §10.3
    semantics (LCS.FirstOrder.ManySorted.Semantics). The truth domain is
    `BoolVal` (Ch3 Def 3.3.1), so validity is phrased over
    `msFormulaEval M A v : BoolVal` via `= BoolVal.T` / `= BoolVal.F`,
    NOT over Prop — the key difference from the one-sorted Gentzen
    system, whose `formulaEvalN` is Prop-valued.

    Source: Logic for Computer Science, Gallier 2015.
-/

namespace LCS.FirstOrder.ManySorted.Gentzen

open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.Propositional.Semantics

-- ===================================================================
-- Definition 10.4.1: Many-sorted sequent
-- ===================================================================



-- ===================================================================
-- Lemma 10.4.1: Soundness of G (many-sorted)
-- ===================================================================


end LCS.FirstOrder.ManySorted.Gentzen
