import LCS.Item
import LCS.Util
import LCS.CutElim.Interpolation
import LCS.CutElim.LKe
import LCS.FirstOrder.Equality.Completeness
import LCS.CutElim.Interpolation.Equality.Axioms
import LCS.CutElim.Interpolation.Equality.Support
import LCS.CutElim.Interpolation.Equality.Replay
import LCS.CutElim.Interpolation.Equality.Reduction

/-! # CutElim.Interpolation.Equality
    Formalization of Chapter 6, Section 6.5.3.
    Craig's interpolation theorem with equality.
    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.CutElim.Interpolation.Equality

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.CutElim.Interpolation
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Equality.Completeness
open LCS.FirstOrder.Gentzen.Hintikka

-- ===================================================================
-- Definition 6.5.1 (companion def): closedReflAxiom
-- ===================================================================


-- ===================================================================
-- Helper: root-support normalization for LKe equality leaves
-- ===================================================================


namespace RootSupportedLKeProof


end RootSupportedLKeProof



-- ===================================================================
-- Lemma 6.5.4 (companion theorem): se_formulae_closed
-- ===================================================================


end LCS.CutElim.Interpolation.Equality
