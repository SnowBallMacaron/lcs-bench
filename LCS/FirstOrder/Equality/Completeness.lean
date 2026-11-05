import LCS.Item
import LCS.Util
import LCS.FirstOrder.Equality
import LCS.FirstOrder.Equality.Search
import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Completeness.InfiniteSearch
import LCS.FirstOrder.Gentzen.Search.NoFunction
import LCS.FirstOrder.Equality.Completeness.Part1
import LCS.FirstOrder.Equality.Completeness.Part2

/-! # FirstOrder.Equality.Completeness
    Formalization of Chapter 5, Sections 5.6.4-5.6.5.
    Search procedure and completeness for languages with equality.
    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.FirstOrder.Equality.Completeness

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Completeness


-- ===================================================================
-- Equality-aware growing closure (Section 5.6.4-5.6.5)
-- ===================================================================
-- The equality-aware signed limit set extends signedLimitSet (from
-- InfiniteSearch) with the equality axiom instances (H6 conditions).
-- This avoids the contradiction in the old eqSearchClosureSet approach
-- because signedLimitSet Gamma (with equality-free Gamma) never
-- produces falseF(eq_ ...), so injecting trueF(eq_ ...) is safe.

open LCS.FirstOrder.Completeness.InfiniteSearch

-- ===================================================================
-- Definition: signedLimitSetEq
-- ===================================================================


-- ===================================================================
-- FormulaN-native theorems (Rounds 5+6)
-- ===================================================================

open LCS.FirstOrder.Completeness

-- ===================================================================
-- Lemma 5.6.3 (normalized): soundnessGEq
-- ===================================================================

-- soundnessGEq: The fully-proved version from LCS.FirstOrder.Equality
-- (imported and opened) is used.

-- ===================================================================
-- Definition 5.6.3 (normalized, companion def): eqReflFormulae
-- ===================================================================


-- ===================================================================
-- Definition 5.6.3 (normalized, companion def): eqListForIndex
-- ===================================================================

namespace SearchStateEq


end SearchStateEq

-- ===================================================================
-- Definition 5.6.3 (normalized): injectEqFormulae
-- ===================================================================


end LCS.FirstOrder.Equality.Completeness
