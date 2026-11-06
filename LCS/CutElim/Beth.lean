import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.CutElim.CompletenessBridge
import LCS.CutElim.LKe
import LCS.CutElim.Interpolation
import LCS.FirstOrder.Syntax
import LCS.FirstOrder.Semantics
import LCS.CutElim.Beth.Definability
import LCS.CutElim.Beth.ArithmeticExample
import LCS.CutElim.Beth.ExplicitImpliesImplicit
import LCS.CutElim.Beth.WithoutEquality
import LCS.CutElim.Beth.WithEquality

/-! # CutElim.Beth
    Formalization of Chapter 6, Section 6.6.
    Beth's definability theorem (implicit and explicit definability).
    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.CutElim.Beth

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Completeness
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.SyntaxN.Variables
open Classical

-- ===================================================================
-- Local definitions (will be provided by Interpolation.lean once restored)
-- ===================================================================


-- ===================================================================
-- Example 6.6.1: bethExample_arithWithOrder
-- ===================================================================


end LCS.CutElim.Beth
