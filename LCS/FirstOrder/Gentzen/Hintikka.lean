import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.FirstOrder.Gentzen.Hintikka.Model
import LCS.FirstOrder.Gentzen.Hintikka.SearchClosure
import LCS.FirstOrder.Gentzen.Hintikka.PathModel
import LCS.FirstOrder.Gentzen.Hintikka.Construction
import LCS.FirstOrder.Gentzen.Hintikka.Examples

/-! # FirstOrder.Gentzen.Hintikka
    Formalization of Chapter 5, Sections 5.4.6-5.4.7.
    Hintikka sets (languages without equality) and completeness
    for the special case without function symbols.
    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.FirstOrder.Gentzen.Hintikka

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.SyntaxN.Variables

-- ===================================================================
-- Lemma 5.4.5 (companion): termInH - terms with free vars in H are in H
-- ===================================================================


-- ===================================================================
-- SearchState: Normalized search state using Sequent
-- ===================================================================


-- ===================================================================
-- Theorem 5.5.1 (companion, UNFAITHFUL): SearchState.termSet
-- ===================================================================

namespace SearchState


end SearchState

-- ===================================================================
-- Theorem 5.5.1 (companion, UNFAITHFUL): SearchState.init
-- ===================================================================

namespace SearchState


end SearchState

-- ===================================================================
-- Normalized decomposition: decomposeAntFormula
-- ===================================================================


-- ===================================================================
-- Infrastructure for searchTree_path_freeFor (H5)
-- ===================================================================


-- ===================================================================
-- seqNoEq preservation through decomposition and branchStep
-- ===================================================================



-- ===================================================================
-- Example 5.4.3 (companion def): exSearchFormula_5_4_3
-- ===================================================================


end LCS.FirstOrder.Gentzen.Hintikka
