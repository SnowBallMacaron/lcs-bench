import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.CutElimination
import LCS.FirstOrder.Semantics
import LCS.CutElim.Hauptsatz.Equality.SystemG1nnfEq
import LCS.CutElim.Hauptsatz.Equality.CutElimination

/-! # CutElim.Hauptsatz.Equality
    Formalization of Chapter 6, Sections 4.5-4.6.
    The system G1nnf= and its cut elimination theorem.
    Source: Logic for Computer Science, Gallier 2015
-/

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SyntaxN.Substitution LCS.FirstOrder.SyntaxN.Variables
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS

-- ===================================================================
-- Definition 6.4.6: G1nnfEqAxiom — Equality axiom schemas
-- ===================================================================

namespace LCS.CutElim.Hauptsatz.Equality


-- ===================================================================
-- Definition 6.4.6 (companion def): G1nnfEqAxiom.toSequent
-- ===================================================================

namespace G1nnfEqAxiom


end G1nnfEqAxiom


-- ===================================================================
-- Definition 6.4.6 (companion def): G1nnfEqRule.conclusion/premises
-- ===================================================================

namespace G1nnfEqRule


end G1nnfEqRule

-- ===================================================================
-- Lemma 6.4.8 (required type): G1nnfEqProofTree (indexed by Finset)
-- ===================================================================


namespace G1nnfEqProofTree


end G1nnfEqProofTree


-- ===================================================================
-- Definition 6.4.6 (companion def): G1nnfEqAxiom.isNegClosure
-- ===================================================================

namespace G1nnfEqAxiom


end G1nnfEqAxiom

-- ===================================================================
-- Definition 6.4.6 (companion def): g1nnfEqAxiomExample
-- ===================================================================


-- ===================================================================
-- Lemma 6.4.8 (required def): G1nnfEqProofTree helpers
-- ===================================================================

namespace G1nnfEqProofTree


end G1nnfEqProofTree

-- ===================================================================
-- Lemma 6.4.9 (required def): isInessentialCut
-- ===================================================================


-- ===================================================================
-- Lemma 6.4.9 (required def): G1nnfEqProofTree.essentialCutRank
-- ===================================================================

namespace G1nnfEqProofTree


end G1nnfEqProofTree

namespace G1nnfEqRule


end G1nnfEqRule

namespace G1nnfEqProofTree


end G1nnfEqProofTree

-- ===================================================================
-- Theorem 6.4.2 (required def): G1nnfEqProofTree.hasNoEssentialCuts
-- ===================================================================

namespace G1nnfEqProofTree


end G1nnfEqProofTree

-- ===================================================================
-- Lemma 6.4.8: Completeness of G1nnf_equal
-- ===================================================================


end LCS.CutElim.Hauptsatz.Equality
