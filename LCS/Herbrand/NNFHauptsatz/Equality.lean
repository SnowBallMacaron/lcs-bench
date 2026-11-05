import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.CutElim.Hauptsatz.Equality
import LCS.Herbrand.NNFHauptsatz.Equality.Part1
import LCS.Herbrand.NNFHauptsatz.Equality.Part2

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

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality

-- ===================================================================
-- Definition 7.4.4 (companion def): G2nnfEqRule.isQuantifierRule
-- ===================================================================

namespace LCS.Herbrand.NNFHauptsatz.G2nnfEqRule


end LCS.Herbrand.NNFHauptsatz.G2nnfEqRule

-- ===================================================================
-- Theorem 7.4.2 (helper): G2nnfEqProofTree.isSubtree
-- ===================================================================

namespace LCS.Herbrand.NNFHauptsatz.G2nnfEqProofTree


end LCS.Herbrand.NNFHauptsatz.G2nnfEqProofTree

namespace LCS.Herbrand.NNFHauptsatz.Equality

open LCS.Herbrand.NNFHauptsatz.G2nnfEqRule
open LCS.Herbrand.NNFHauptsatz.G2nnfEqProofTree

-- ===================================================================
-- Lemma 7.4.3 (companion def): g2nnfEqProofTreeContainsFormula
-- ===================================================================



namespace G2nnfEqSelectedPremiseOccurrence


end G2nnfEqSelectedPremiseOccurrence


end LCS.Herbrand.NNFHauptsatz.Equality
