import LCS.Item
import LCS.Util
import LCS.FOResolution.Method
import LCS.FirstOrder.SemanticsN.Substitution
import LCS.FOResolution.Method.Soundness.SubstitutionSemantics
import LCS.FOResolution.Method.Soundness.ResolventValidity

/-! # FOResolution.Method.Soundness
    Formalization of Chapter 8, Section 8.5.2.
    Soundness of the resolution method for first-order logic
    without equality.
    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.FOResolution.Method.Soundness

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method

-- ===================================================================
-- Lemma 8.5.1 (companion def): FOClause.freeVars
-- ===================================================================

namespace FOClause


end FOClause

-- ===================================================================
-- Lemma 8.5.1 (companion def): FOClause.universalClosure
-- ===================================================================


namespace FOClause


end FOClause

-- ===================================================================
-- Lemma 8.5.1 (companion def): composedSubst
-- ===================================================================


-- ===================================================================
-- Lemma 8.5.2 (companion def): FOClauseSet.isUnsatisfiable
-- ===================================================================

namespace FOClauseSet


end FOClauseSet

-- ===================================================================
-- Helper: universal closure of the empty clause is unsatisfiable
-- ===================================================================


-- ===================================================================
-- Helper: substLit unfolding for predN
-- ===================================================================


end LCS.FOResolution.Method.Soundness
