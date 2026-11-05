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
import LCS.Herbrand.NNFHauptsatz.Theorem.VariableSupport
import LCS.Herbrand.NNFHauptsatz.Theorem.Paths
import LCS.Herbrand.NNFHauptsatz.Theorem.Purity
import LCS.Herbrand.NNFHauptsatz.Theorem.RuleOccurrences
import LCS.Herbrand.NNFHauptsatz.Theorem.ExchangeBodies
import LCS.Herbrand.NNFHauptsatz.Theorem.Midsequents
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

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Soundness
open LCS.Herbrand.SharpenedHauptsatz
open LCS.Herbrand.SharpenedHauptsatz.Permutability
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.Herbrand.PrenexForm
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS.CutElim.LK

-- ===================================================================
-- Lemma 7.4.2 (helper): G2nnfRule.cutFormula
-- ===================================================================

namespace LCS.Herbrand.NNFHauptsatz.G2nnfRuleCore


end LCS.Herbrand.NNFHauptsatz.G2nnfRuleCore

namespace LCS.Herbrand.NNFHauptsatz.G2nnfRule


end LCS.Herbrand.NNFHauptsatz.G2nnfRule

namespace LCS.Herbrand.NNFHauptsatz

/-! ## Finite support for G2nnf annotations

The Chapter 6 finite formula/term supports are exact structural supports.
The lemmas below connect them to the Chapter 7 all-variable predicates and
show that they commute with the uniform renaming API.
-/


namespace MaxQuantifierOccurrence


end MaxQuantifierOccurrence

namespace G2nnfRuleCore


end G2nnfRuleCore

end LCS.Herbrand.NNFHauptsatz

namespace LCS.Herbrand.NNFHauptsatz.G2nnfProofTree

-- ===================================================================
-- Lemma 7.4.2 (required def): G2nnfProofTree.isCutFree
-- ===================================================================



end LCS.Herbrand.NNFHauptsatz.G2nnfProofTree

namespace LCS.Herbrand.NNFHauptsatz.Theorem

open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule

-- ===================================================================
-- Lemma 7.4.2 (companion def): g2nnfProofTreeContainsFormula
-- ===================================================================



namespace G2nnfQuantifierRuleView


end G2nnfQuantifierRuleView


namespace G2nnfPermutationLowerRuleView


end G2nnfPermutationLowerRuleView


namespace G2nnfOnePremiseApplication


end G2nnfOnePremiseApplication


namespace G2nnfOnePremiseFrontier


end G2nnfOnePremiseFrontier


namespace G2nnfOtherPremiseFrontier


end G2nnfOtherPremiseFrontier


namespace G2nnfSelectedPremiseOccurrence



end G2nnfSelectedPremiseOccurrence


namespace G2nnfQuantifierRuleView


end G2nnfQuantifierRuleView


namespace G2nnfPrincipalOccurrenceRole


end G2nnfPrincipalOccurrenceRole

namespace G2nnfPermutableOccurrence


end G2nnfPermutableOccurrence

-- ===================================================================
-- Lemma 7.4.2 (untagged infrastructure): bounded local exchange
-- ===================================================================


namespace G2nnfExchangePrincipalCorrespondence


end G2nnfExchangePrincipalCorrespondence


namespace G2nnfPrincipalOccurrenceRole


end G2nnfPrincipalOccurrenceRole

namespace G2nnfPermutableOccurrence


end G2nnfPermutableOccurrence



namespace G2nnfExchangeBodyQuantifierPosition


end G2nnfExchangeBodyQuantifierPosition


namespace G2nnfExchangeBodyLowerPosition


end G2nnfExchangeBodyLowerPosition

namespace G2nnfExchangeBodyContractionPosition


end G2nnfExchangeBodyContractionPosition

namespace G2nnfExchangeCasePosition


end G2nnfExchangeCasePosition

namespace G2nnfExchangeBodyLowerPosition


end G2nnfExchangeBodyLowerPosition

namespace G2nnfExchangeBodyContractionPosition


end G2nnfExchangeBodyContractionPosition

namespace G2nnfExchangeCasePosition


end G2nnfExchangeCasePosition

namespace G2nnfExchangeBody


end G2nnfExchangeBody


namespace G2nnfQuantifierPrincipalCase


end G2nnfQuantifierPrincipalCase

namespace G2nnfPrincipalCaseKind


end G2nnfPrincipalCaseKind


namespace G2nnfExchangeKernel



end G2nnfExchangeKernel

namespace G2nnfPermutableOccurrence


end G2nnfPermutableOccurrence


namespace G2nnfLocalExchangeOrderCertificate


end G2nnfLocalExchangeOrderCertificate

namespace G2nnfLocalExchangeAt


end G2nnfLocalExchangeAt

-- ===================================================================
-- Lemma 7.4.2 (helper): RuleAppearsInTree
-- ===================================================================


noncomputable section



end

-- ===================================================================
-- Lemma 7.4.2 (propositional part): g2nnf_permutability_with_propositional
-- ===================================================================


end LCS.Herbrand.NNFHauptsatz.Theorem
