import LCS.Item
import LCS.CutElim.Hauptsatz
import LCS.Util
import LCS.FirstOrder.Semantics.Subformulae
import LCS.Herbrand.PrenexForm
import LCS.Herbrand.SharpenedHauptsatz.Theorem
import LCS.CutElim.Interpolation.Equality
import LCS.Herbrand.HerbrandTheorem.Part1
import LCS.Herbrand.HerbrandTheorem.Part2

/-! # Herbrand.HerbrandTheorem
    Formalization of Chapter 7, Sections 5.1-5.3: Preliminaries,
    Skolem functions, and substitutions for Herbrand's theorem.

    Covers Lemma 7.5.1 (universally closing provable sequents),
    Definitions 7.5.1-7.5.4 (Skolem functions, functional form,
    substitutions, sigma-matrix), and Examples 7.5.1-7.5.2.

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.HerbrandTheorem

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.CutElim.LK
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen
open LCS.CutElim.Interpolation.Equality


namespace LKAlteredDiagram


end LKAlteredDiagram


-- ===================================================================
-- Definition 7.5.3 (companion def): Substitution.applyTerm
-- ===================================================================

namespace Substitution


end Substitution


section ValidityDuality

open LCS.FirstOrder.SemanticsN


end ValidityDuality

-- ===================================================================
-- Theorem 7.5.1 (required helper): sigmaMatrix_eq_original
-- ===================================================================


end LCS.Herbrand.HerbrandTheorem
