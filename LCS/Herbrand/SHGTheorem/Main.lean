import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.SHGTheorem.Herbrand
import LCS.Herbrand.SHGTheorem.Main.SkolemSemanticsBase
import LCS.Herbrand.SHGTheorem.Main.SkolemEquisatisfiability
import LCS.Herbrand.SHGTheorem.Main.SHG
import LCS.Herbrand.SHGTheorem.Main.GroundMatrix

/-! # Herbrand.SHGTheorem.Main
    Formalization of Chapter 7, §7.6.5: The Skolem-Herbrand-Godel
    Theorem for sentences in NNF.

    Covers Lemma 7.6.3 (satisfiability preservation under Skolemization),
    Theorem 7.6.1 (the Skolem-Herbrand-Godel theorem), and
    Corollary 7.6.1 (prenex case).
-/

namespace LCS.Herbrand.SHGTheorem.Main

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.SHGTheorem.Herbrand
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.CutElim.Hauptsatz
open LCS.FirstOrder.SemanticsN.Substitution

-- ===================================================================
-- Helper: formulaSubstN preserves isNNF (FormulaN version)
-- ===================================================================



-- ===================================================================
-- Theorem 7.6.1 (helper): foldl-conjunction evaluates as conjunction
-- ===================================================================


namespace GroundMatrixInstance


end GroundMatrixInstance

-- ===================================================================
-- Corollary 7.6.1 (companion relation): ConjunctionFlattening
-- ===================================================================


namespace ConjunctionFlattening


end ConjunctionFlattening

-- ===================================================================
-- Corollary 7.6.1 (companion def): isFiniteGroundConjunctionOfMatrix
-- ===================================================================



-- ===================================================================
-- Corollary 7.6.1 ground-conjunction carrier regressions
-- ===================================================================

namespace GroundMatrixCarrierRegression


end GroundMatrixCarrierRegression

open LCS.Herbrand.PrenexForm
open LCS.Herbrand.NNFHauptsatz.Theorem


end LCS.Herbrand.SHGTheorem.Main
