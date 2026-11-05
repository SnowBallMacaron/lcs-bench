import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Equality.Part1
import LCS.FirstOrder.Equality.Part2

/-! # FirstOrder.Equality
    Formalization of Chapter 5, Sections 5.6.1-5.6.3.
    Hintikka sets for languages with equality, the Gentzen system G_=,
    and soundness.
    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.FirstOrder.Equality

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution (formulaSubstEvalDirectN)
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Completeness

-- ===================================================================
-- Definition 5.6.1 (companion def): conjoinFormulae
-- ===================================================================


namespace GEqDeductionTree


end GEqDeductionTree


-- ===================================================================
-- Example 5.6.1 (companion type): ExPredEq1
-- ===================================================================


-- ===================================================================
-- Definition 5.6.2 (companion def): GEqProofTree.conclusion (shim)
-- ===================================================================

namespace GEqProofTree


end GEqProofTree

-- ===================================================================
-- Definition 5.6.2 (companion): Well-formedness of GEqProofTree (shim)
-- ===================================================================

-- ===================================================================
-- Definition 5.6.2 (companion def): sequentProvableEq
-- ===================================================================


-- ===================================================================
-- Lemma 5.6.1 (companion theorem): eqCongruence_func
-- ===================================================================



end LCS.FirstOrder.Equality
