import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Equality
import LCS.FirstOrder.ManySorted.CongruenceClosure
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.Satisfiability
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.DisjunctiveNormalForm
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.ValidityReduction
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.GraphOfConjunction
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.SemanticEquality
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.QuotientModel
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.Examples

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

    Content modules, in book order:
    - `Decision.Satisfiability` — the semantic notions used in Section 10.6: satisfiable, valid, unsatisfiable, entailment and models (Definition 10.3.6)
    - `Decision.DisjunctiveNormalForm` — Section 10.6.1, Lemma 10.6.1 (literals, conjunctions of literals, disjunctive normal form and its correctness)
    - `Decision.ValidityReduction` — Section 10.6.1, validity reduces to unsatisfiability of conjunctions of literals; the case without equality
    - `Decision.GraphOfConjunction` — Section 10.6.3, Definition 10.6.3 (TERM(C), the ranked alphabet and the graph G(C) of a conjunction)
    - `Decision.SemanticEquality` — Section 10.6.3, proof of Lemma 10.6.2: a model's semantic equality is a congruence containing E (collision implies unsatisfiable)
    - `Decision.QuotientModel` — Section 10.6.3, proof of Lemma 10.6.2: the quotient model of TERM(C) (no collision implies satisfiable) and Lemma 10.6.2
    - `Decision.Examples` — Examples 10.6.1-10.6.2 (the graph of a conjunction and its congruence closure)
-/

namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Decision

end LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
