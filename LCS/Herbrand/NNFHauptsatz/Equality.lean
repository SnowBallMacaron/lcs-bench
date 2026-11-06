import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.CutElim.Hauptsatz.Equality
import LCS.Herbrand.NNFHauptsatz.Equality.RuleClasses
import LCS.Herbrand.NNFHauptsatz.Equality.RootToNodePaths
import LCS.Herbrand.NNFHauptsatz.Equality.PureVariable
import LCS.Herbrand.NNFHauptsatz.Equality.Permutability
import LCS.Herbrand.NNFHauptsatz.Equality.SharpenedHauptsatz
import LCS.Herbrand.NNFHauptsatz.Equality.Soundness

/-! # Herbrand.NNFHauptsatz.Equality
    Formalization of Chapter 7, Section 7.4.4: The system G2nnf=
    and its sharpened Hauptsatz.

    Covers Definition 7.4.4 (G2nnf=), Lemma 7.4.3 (permutability
    in G2nnf=), and Theorem 7.4.2 (sharpened Hauptsatz for G2nnf=).

    INDEXED PORT: `G2nnfEqProofTree` is indexed by its conclusion
    `LCS.Finset`-based sequent `(Γ, Δ)`, defined in
    `LCS/Herbrand/NNFHauptsatz.lean` (Layer 0). Layer 0's
    `G2nnfEqRule` has two constructors:
    - `.base (r : G2nnfRuleCore L)` — wraps a base G2nnf rule (which
      already includes weakening rules, propositional rules,
      quantifier-for-subformulae rules, and cut).
    - `.eqAxiom (ax : G1nnfEqAxiom L)` — wraps an equality axiom
      schema from G1nnf_=.

    Each quantifier-for-subformulae rule carries its exact maximal occurrence
    and quantifier shape. Its remaining free-for and eigenvariable freshness
    conditions and the standing rectification invariant live on
    `G2nnfEqRule.SideConditions`. The equality-axiom branch delegates to
    `G1nnfEqAxiom.WellFormed`, including recursive negation-closure
    admissibility. These conditions are carried as tree-constructor fields;
    no separate tree-level `WellFormed` predicate is needed.

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.NNFHauptsatz.Equality
end LCS.Herbrand.NNFHauptsatz.Equality
