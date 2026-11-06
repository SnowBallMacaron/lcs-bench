import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Semantics.Substitution
import LCS.Propositional.Semantics
import LCS.FirstOrder.ManySorted.Gentzen.SystemG
import LCS.FirstOrder.ManySorted.Gentzen.DeductionTrees
import LCS.FirstOrder.ManySorted.Gentzen.Soundness
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

    Content modules, in book order:
    - `Gentzen.SystemG` — Section 10.4.1, Definition 10.4.1 (the Gentzen system G for many-sorted languages without equality: sequents, axioms, rules)
    - `Gentzen.DeductionTrees` — Section 10.4.2 (deduction trees and proof trees, provability of finite and infinite sequents)
    - `Gentzen.Soundness` — Section 10.4.3, Lemma 10.4.1 (soundness of G, many-sorted case)
    - `Gentzen.Completeness` — Section 10.4.4, Theorem 10.4.1 (many-sorted Hintikka sets and Gödel's extended completeness theorem for G)
-/

namespace LCS.FirstOrder.ManySorted.Gentzen

end LCS.FirstOrder.ManySorted.Gentzen
