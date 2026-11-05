import LCS.Item
import LCS.Util
import LCS.FOResolution.Method
import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.Method.HerbrandBridge
import LCS.Herbrand.SHGTheorem.Main
import LCS.FOResolution.GroundResolution
import LCS.CutElim.LK
import LCS.FOResolution.Method.Completeness.Substitutions
import LCS.FOResolution.Method.Completeness.Lifting
import LCS.FOResolution.Method.Completeness.Completeness

/-! # FOResolution.Method.Completeness
    Formalization of Chapter 8, Section 8.5.3.
    Lifting lemma and completeness of the resolution method
    for first-order logic without equality.
    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.FOResolution.Method.Completeness

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.GroundResolution
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.HerbrandBridge
open LCS.CutElim.LK
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open Classical

-- ===================================================================
-- Lemma 8.5.4 (companion type): FOResolutionTreeHom
-- ===================================================================




-- ===================================================================
-- Theorem 8.5.2 (required defs): isPrenex, matrixIsCNF, isLKProvable,
-- FOClauseForm.ofFormula
-- ===================================================================

namespace Formula


end Formula

namespace Formula


end Formula


namespace FOClauseForm


end FOClauseForm

-- ===================================================================
-- Theorem 8.5.2: Herbrand-like theorem for resolution
-- ===================================================================


end LCS.FOResolution.Method.Completeness
