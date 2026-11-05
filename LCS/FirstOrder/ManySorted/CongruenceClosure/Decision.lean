import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Equality
import LCS.FirstOrder.ManySorted.CongruenceClosure
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.HerbrandSatisfaction
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.SemanticEquality
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.QuotientModel

/-! # FirstOrder.ManySorted.CongruenceClosure.Decision
    Formalization of Chapter 10, Subsections 10.6.1 and 10.6.3
    (Decision Procedure for Quantifier-free Formulae Without Predicate
    Symbols; The Graph Associated With a Conjunction).

    Reduction of validity to unsatisfiability of conjunctions of literals
    via disjunctive normal form (Lemma 10.6.1), the graph G(C) and term
    set TERM(C) induced by a conjunction of equations and disequations
    (Def 10.6.3), the unsatisfiability criterion via the congruence
    closure of E (Lemma 10.6.2), and a worked example (Example 10.6.2).

    Because §10.3 folded validity/satisfiability into the script-M
    algebra, the semantic predicates `msSatisfiable`/`msValid`/
    `msUnsatisfiable`/`msEntails`/`msModels` are introduced HERE, grounded
    on `msFormulaEval … = BoolVal.T` (the formula meaning A_M of §10.3).

    Builds on §10.6 graph/congruence machinery
    (LCS.FirstOrder.ManySorted.CongruenceClosure).

    Source: Logic for Computer Science, Gallier 2015.
-/

namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Decision

open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.FirstOrder.ManySorted.Equality
open LCS.FirstOrder.ManySorted.CongruenceClosure
open LCS.Propositional.Semantics

-- ===================================================================
-- §10.3-grounded semantic predicates (introduced here, used by 10.6.1/2)
-- ===================================================================


-- ===================================================================
-- Lemma 10.6.1 (companion defs): literal / DNF / conjunction syntax
-- ===================================================================

namespace MSFormula


end MSFormula


-- ===================================================================
-- Lemma 10.6.1: msValid_reduces_to_conjunction_unsat
-- ===================================================================


-- ===================================================================
-- Lemma 10.6.2: the term algebra C and its three-case operation f_C
-- ===================================================================


end LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
