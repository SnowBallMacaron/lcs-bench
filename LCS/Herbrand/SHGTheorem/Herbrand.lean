import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.SyntaxAllocation
import LCS.Herbrand.SHGTheorem.Herbrand.OccurrenceLineage
import LCS.Herbrand.SHGTheorem.Herbrand.CanonicalMapRegression
import LCS.Herbrand.SHGTheorem.Herbrand.NestedMapRegression
import LCS.Herbrand.SHGTheorem.Herbrand.Alteration
import LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination
import LCS.Herbrand.SHGTheorem.Herbrand.ClosedSubstitution
import LCS.Herbrand.SHGTheorem.Herbrand.ScopeAndPurity
import LCS.Herbrand.SHGTheorem.Herbrand.Provenance
import LCS.Herbrand.SHGTheorem.Herbrand.LowerTrace
import LCS.Herbrand.SHGTheorem.Herbrand.LowerConstruction
import LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds

/-! # Herbrand.SHGTheorem.Herbrand
    Formalization of Chapter 7, Section 6.4: Half of a Herbrand-like
    Theorem for sentences in NNF.

    Covers Lemma 7.6.1 (c-instances closed under conjunction) and
    Lemma 7.6.2 (constructive half of Herbrand's theorem for NNF).

    INDEXED PORT: `G2nnfProofTree` and `G2nnfEqProofTree` are indexed
    by their conclusion (`LCS.Finset (FormulaN L)` antecedent and
    succedent). Statements of the form
    `∃ T, T.conclusion = (X, Y) ∧ T.WellFormed` translate to
    `Nonempty (G2nnfProofTree X Y)` (and similarly for Eq).
    Sequent components are `LCS.Finset (FormulaN L)` throughout, with
    `{A}` for singletons and `∅` for empty.
-/

namespace LCS.Herbrand.SHGTheorem.Herbrand

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.Equality
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.Herbrand.PrenexForm
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae


namespace EigenvarSubstitution


end EigenvarSubstitution


namespace FormulaOccurrenceLineage


end FormulaOccurrenceLineage


-- ===================================================================
-- Lemma 7.6.2 exact canonical-link regressions
-- ===================================================================

namespace CanonicalEigenvarMapRegression

noncomputable section


end

end CanonicalEigenvarMapRegression

namespace OrderedEigenvarCompositionRegression

open CanonicalEigenvarMapRegression

noncomputable section



end

end OrderedEigenvarCompositionRegression

/- Permanent two-level regression for ordered canonical-map composition.
The inner raw Skolem range depends on the strict outer `∃:left`
eigenvariable; only its ancestor-normalized range is canonical. -/
namespace NestedCanonicalMapRegression

open CanonicalEigenvarMapRegression

noncomputable section


end

end NestedCanonicalMapRegression



namespace EigenvariableToSkolemSubstInterfaceRegression


end EigenvariableToSkolemSubstInterfaceRegression

-- ===================================================================
-- Lemma 7.6.2 (companion def): midsequentCInstances
-- ===================================================================









section
set_option autoImplicit false

namespace SkolemAllocationRegression


end SkolemAllocationRegression
end

-- ===================================================================
-- Lemma 7.6.2 (companion theorem): herbrand_half_lemma_G1nnf
-- ===================================================================


end LCS.Herbrand.SHGTheorem.Herbrand
