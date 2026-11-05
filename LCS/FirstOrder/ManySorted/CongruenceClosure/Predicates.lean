import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Equality
import LCS.FirstOrder.ManySorted.CongruenceClosure
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
import LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.Encoding
import LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.CongruenceModel
import LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.Decision
import LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.Example

/-! # FirstOrder.ManySorted.CongruenceClosure.Predicates
    Formalization of Chapter 10, Subsection 10.6.5 (Decision Procedure
    for Quantifier-free Formulae, with predicate symbols).

    Extending the congruence-closure decision procedure to atomic
    formulae by treating `P t₁…t_k` as the equation `(P t₁…t_k ≡ ⊤)` and
    each predicate as a function symbol of output sort bool: the
    generalized unsatisfiability criterion (Lemma 10.6.4) and a worked
    example (Example 10.6.3).

    The key device is a REAL language transformation
    `boolExtendedLanguage L` (Pattern 3): a new bool sort `none` is added
    to `SortType` (`Option L.SortType`), the logical constant `⊤` is a
    constant of that sort, every predicate symbol `P` of arity `u₁…u_k`
    is reinterpreted as a function symbol of rank `(u₁…u_k, bool)`, and an
    atom `P t₁…t_k` is replaced by the bool-equation `(P t₁…t_k ≐_bool ⊤)`
    via the genuine recursive encoder `msEncodeConjunction` (never the
    identity).

    Builds on §10.6.3 decision procedure
    (LCS.FirstOrder.ManySorted.CongruenceClosure.Decision).

    Source: Logic for Computer Science, Gallier 2015.
-/

namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates

open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.FirstOrder.ManySorted.Equality
open LCS.FirstOrder.ManySorted.CongruenceClosure
open LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
open LCS.Propositional.Semantics

-- ===================================================================
-- Lemma 10.6.4: the bool-extended language L'
-- ===================================================================



-- ===================================================================
-- Lemma 10.6.4 (DECODE transfer): from a model M' of C' over L' build a
-- model `decodeModel L M'` of C over L (the converse of `encodeModel`).
-- ===================================================================


-- ===================================================================
-- Example 10.6.3: the one-sorted f/P decision
-- C = f³(a) ≐ a ∧ f⁵(a) ≐ a ∧ P(a) ∧ ¬P(f(a))
-- ===================================================================


end LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates
