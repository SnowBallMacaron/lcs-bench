import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Equality
import LCS.Herbrand.NNFHauptsatz.Part1
import LCS.Herbrand.NNFHauptsatz.Part2

/-! # Herbrand.NNFHauptsatz
    Formalization of Chapter 7, Section 4.1: The System G2nnf.

    Covers Definitions 7.4.1-7.4.3 (maximal quantified subformulae,
    subformula substitution, and the G2nnf Gentzen system),
    and Examples 7.4.1-7.4.3.

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.NNFHauptsatz

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality


namespace AllRectified


end AllRectified


namespace MaxQuantifierOccurrence


end MaxQuantifierOccurrence

-- ===================================================================
-- Shared NNF rule and tree carriers
-- ===================================================================


namespace G2nnfRuleCore


end G2nnfRuleCore


section QuantifierPolarity

set_option backward.isDefEq.respectTransparency false


end QuantifierPolarity

-- ===================================================================
-- Definition 7.4.1: maxQuantSubformulae — QF(A)
-- ===================================================================


namespace MaxQuantifierOccurrence


end MaxQuantifierOccurrence

-- ===================================================================
-- Example 7.4.2 (companion type): QFExConst
-- ===================================================================


-- ===================================================================
-- Definition 7.4.3 (companion def): G2nnfRule.conclusion
-- ===================================================================

namespace G2nnfRule


namespace SideConditions


end SideConditions
end G2nnfRule


namespace G2nnfProofTree


end G2nnfProofTree


namespace G2nnfDeductionTree


end G2nnfDeductionTree


-- ===================================================================
-- Definition 7.4.4 (companion def): G2nnfEqRule.cutFormula
-- ===================================================================

namespace G2nnfEqRule


end G2nnfEqRule

-- ===================================================================
-- Definition 7.4.4 (required type): G2nnfEqProofTree (indexed)
-- ===================================================================


namespace G2nnfEqDeductionTree


end G2nnfEqDeductionTree

-- ===================================================================
-- G2nnf= proof-tree side-condition regressions
-- ===================================================================


namespace G2nnfEqProofTree


end G2nnfEqProofTree

-- ===================================================================
-- Theorem 7.4.2 (required def): isInessentialCut
-- ===================================================================


-- ===================================================================
-- Theorem 7.4.2 (required def): G2nnfEqProofTree.hasNoEssentialCuts
-- ===================================================================

namespace G2nnfEqProofTree


end G2nnfEqProofTree

-- ===================================================================
-- Definition 7.4.4 (companion): g2nnfEqProvable
-- ===================================================================


end LCS.Herbrand.NNFHauptsatz
