import LCS.Item
import LCS.Util
import LCS.Herbrand.HerbrandTheorem
import LCS.Herbrand.HerbrandTheorem.Main.Part1
import LCS.Herbrand.HerbrandTheorem.Main.Part2

/-! # Herbrand.HerbrandTheorem.Main
    Formalization of Chapter 7, Section 5.4: Herbrand's Theorem
    for prenex formulae.

    Covers Theorem 7.5.1 (Herbrand's theorem) and Example 7.5.3
    (proof reconstruction from Herbrand disjunction).

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.HerbrandTheorem.Main

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.HerbrandTheorem
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.CutElim.LK
open LCS.CutElim.LKe.Equivalence

-- ===================================================================
-- Theorem 7.5.1 (companion def): IsQuantifierFreeSubstInstance
-- ===================================================================



end LCS.Herbrand.HerbrandTheorem.Main
