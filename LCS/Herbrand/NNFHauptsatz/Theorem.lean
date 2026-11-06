import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.NNFHauptsatz.Renaming
import LCS.Herbrand.NNFHauptsatz.Soundness
import LCS.Herbrand.SharpenedHauptsatz
import LCS.Herbrand.SharpenedHauptsatz.Permutability
import LCS.Herbrand.SharpenedHauptsatz.Theorem
import LCS.Herbrand.PrenexForm
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination
import LCS.Herbrand.NNFHauptsatz.Theorem.RuleClasses
import LCS.Herbrand.NNFHauptsatz.Theorem.VariableSupport
import LCS.Herbrand.NNFHauptsatz.Theorem.CutFree
import LCS.Herbrand.NNFHauptsatz.Theorem.RootToNodePaths
import LCS.Herbrand.NNFHauptsatz.Theorem.FreshAlphaCopies
import LCS.Herbrand.NNFHauptsatz.Theorem.PureVariable
import LCS.Herbrand.NNFHauptsatz.Theorem.AtomicAxioms
import LCS.Herbrand.NNFHauptsatz.Theorem.QuantifierRules
import LCS.Herbrand.NNFHauptsatz.Theorem.PermutationLowerRules
import LCS.Herbrand.NNFHauptsatz.Theorem.RuleApplications
import LCS.Herbrand.NNFHauptsatz.Theorem.PermutableOccurrences
import LCS.Herbrand.NNFHauptsatz.Theorem.ExchangeBodies
import LCS.Herbrand.NNFHauptsatz.Theorem.ExchangeKernel
import LCS.Herbrand.NNFHauptsatz.Theorem.Permutability
import LCS.Herbrand.NNFHauptsatz.Theorem.Midsequents
import LCS.Herbrand.NNFHauptsatz.Theorem.SharpenedHauptsatz
import LCS.Herbrand.NNFHauptsatz.Theorem.Example

/-! # Herbrand.NNFHauptsatz.Theorem
    Formalization of Chapter 7, Section 4.3: A Gentzen-like Sharpened
    Hauptsatz for G2nnf.

    Covers Lemma 7.4.2 (permutability in G2nnf), Theorem 7.4.1
    (the sharpened Hauptsatz for G1nnf and G2nnf), and Example 7.4.4.

    Source: Logic for Computer Science, Gallier 2015

    INDEXED PORT: `G2nnfProofTree` is indexed by its conclusion
    `LCS.Finset`-based sequent `(Γ, Δ)`, defined in
    `LCS/Herbrand/NNFHauptsatz.lean`. Each quantifier-for-subformulae
    rule carries an exact maximal occurrence and its quantifier-shape
    equation; its remaining free-for and eigenvariable freshness
    conditions, together with the standing rectification invariant,
    live on `G2nnfRule.SideConditions`. These conditions are carried as
    tree-constructor fields. WellFormed is built into the indexed type
    and is not carried as a separate predicate.
-/

namespace LCS.Herbrand.NNFHauptsatz.Theorem
end LCS.Herbrand.NNFHauptsatz.Theorem
