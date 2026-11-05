import LCS.Item
import LCS.Util
import LCS.Herbrand.SharpenedHauptsatz
import LCS.Herbrand.SharpenedHauptsatz.Permutability
import LCS.Herbrand.PrenexForm
import LCS.Herbrand.SharpenedHauptsatz.Theorem.Part1
import LCS.Herbrand.SharpenedHauptsatz.Theorem.Part2

/-! # Herbrand.SharpenedHauptsatz.Theorem
    Formalization of Chapter 7, Section 3.3: Gentzen's Sharpened Hauptsatz
    for prenex formulae.

    Covers Theorem 7.3.1 (the sharpened Hauptsatz with midsequent)
    and Examples 7.3.3-7.3.4.

    Source: Logic for Computer Science, Gallier 2015

    INDEXED PORT: `FOLKProofTree` is indexed by its conclusion sequent
    (`FOLKProofTree : Sequent L → Type`). Classifier predicates
    (`isStructural`, `isLogical`, `isQuantifier`, …) live on the
    indexed `FOLKStep1` / `FOLKStep2` rule families defined in
    `LCS/Herbrand/SharpenedHauptsatz/Permutability.lean`. No unified
    `FOLKRule` shim is used; each pattern-match destructures directly
    via `.axiom_`, `.onePremise rule t`, `.twoPremise rule t1 t2`.
    WellFormed is built into the indexed type and is not carried as
    a separate conjunct.
-/

namespace LCS.Herbrand.SharpenedHauptsatz.Theorem

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.Herbrand.SharpenedHauptsatz
open LCS.Herbrand.SharpenedHauptsatz.Permutability
open LCS.Herbrand.PrenexForm

-- ===================================================================
-- Example 7.3.3 (companion type): PermExPred
-- ===================================================================



-- ===================================================================
-- Example 7.3.4: midsequentExampleTree
-- ===================================================================

open LCS.FirstOrder.SyntaxN.Variables


end LCS.Herbrand.SharpenedHauptsatz.Theorem
