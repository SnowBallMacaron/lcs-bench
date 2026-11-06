import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.NNFHauptsatz.Renaming
import LCS.Herbrand.NNFHauptsatz.Soundness
import LCS.Herbrand.SharpenedHauptsatz
import LCS.Herbrand.SharpenedHauptsatz.Permutability
import LCS.Herbrand.SharpenedHauptsatz.Theorem
import LCS.Herbrand.PrenexForm
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination
import LCS.Herbrand.NNFHauptsatz.Theorem.RuleClasses
import LCS.Herbrand.NNFHauptsatz.Theorem.CutFree
import LCS.Herbrand.NNFHauptsatz.Theorem.FreshAlphaCopies
import LCS.Herbrand.NNFHauptsatz.Theorem.PureVariable
import LCS.Herbrand.NNFHauptsatz.Theorem.Midsequents
import Attach
import LCS.Herbrand.NNFHauptsatz.Theorem.SharpenedHauptsatz.ProofsStamp

/-! # Herbrand.NNFHauptsatz.Theorem.SharpenedHauptsatz

Theorem 7.4.1: the sharpened Hauptsatz for G1nnf and G2nnf (G1nnf is a subsystem of
G2nnf; the a/b string argument of the proof).
-/

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Soundness
open LCS.Herbrand.SharpenedHauptsatz
open LCS.Herbrand.SharpenedHauptsatz.Permutability
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.Herbrand.PrenexForm
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS.CutElim.LK
namespace LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule

-- ===================================================================
-- Theorem 7.4.1 (companion def): allSequentFormulaeAreNNF
-- ===================================================================

/-- Theorem 7.4.1 (companion def): Predicate asserting that every formula in both the antecedent and succedent of an `LCS.Finset`-based sequent is in NNF (FormulaN.isNNF holds for each formula). This is the hypothesis that all formulae in Gamma -> Delta are in negation normal form. -/
@[blueprint "chap7__theorem_7_4_1"]
def allSequentFormulaeAreNNF {L : Language}
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) : Prop :=
  (∀ A, Membership.mem seq.1 A → FormulaN.isNNF A) ∧
  (∀ A, Membership.mem seq.2 A → FormulaN.isNNF A)

-- ===================================================================
-- Theorem 7.4.1 (companion def): G1nnfProvableSet
-- ===================================================================

/-- Theorem 7.4.1 (companion def): Over a language without equality,
a set-based sequent is G1nnf-provable when it has an indexed proof tree,
`Nonempty (G1nnfProofTree hL Γ Δ)`. -/
@[blueprint "chap7__theorem_7_4_1"]
def G1nnfProvableSet {L : Language} [DecidableEq (FormulaN L)]
    (hL : L.withoutEquality)
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) : Prop :=
  Nonempty (G1nnfProofTree hL seq.1 seq.2)

-- ===================================================================
-- Theorem 7.4.1 (companion def): premiseOfHighestQuantifier
-- ===================================================================

-- ===================================================================
-- Theorem 7.4.1 (companion def): removeWeakeningQuantifiedFormulae
-- ===================================================================

-- ===================================================================
-- Theorem 7.4.1: sharpenedHauptsatz_G2nnf
-- ===================================================================

/-- Theorem 7.4.1: Over a language without equality, a G1nnf-provable
rectified NNF sequent satisfying the §6.1 sequent-level free/bound-variable
convention has a cut-free, pure-variable G2nnf proof with a midsequent.
Every formula of the midsequent is quantifier-free; above it the rules are
propositional or weakening, and below it they are quantifier-for-subformulae
rules. Rectification remains a standing assumption of §7.4 and is enforced
at every proof node by the G2nnf side conditions. -/
@[attach_debt, blueprint "chap7__theorem_7_4_1" (main := true)]
theorem sharpenedHauptsatz_G2nnf {L : Language}
    [DecidableEq (FormulaN L)]
    (hL : L.withoutEquality)
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L))
    (hAllNNF : allSequentFormulaeAreNNF seq)
    (hRect : AllRectified seq)
    (hCross : finsetCrossNoFreeBound seq.1 seq.2)
    (hProv : G1nnfProvableSet hL seq) :
    ∃ (T : G2nnfProofTree hL seq.1 seq.2)
      (mid : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)),
      T.isCutFree ∧
      IsPureVariableProofG2nnf T ∧
      IsMidsequentG2nnf T mid 
end LCS.Herbrand.NNFHauptsatz.Theorem
end
