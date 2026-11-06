import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.SequentEncodings
import LCS.Herbrand.SHGTheorem.Herbrand.ConnectiveCombination
import LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination
import LCS.Herbrand.SHGTheorem.Herbrand.SkolemFormShape
import LCS.Herbrand.SHGTheorem.Herbrand.SkolemNormalForm
import LCS.Herbrand.SHGTheorem.Herbrand.EigenvarSubstitution
import LCS.Herbrand.SHGTheorem.Herbrand.ExistentialOccurrences
import LCS.Herbrand.SHGTheorem.Herbrand.OccurrenceLineage
import LCS.Herbrand.SHGTheorem.Herbrand.CanonicalEigenvarMap
import LCS.Herbrand.SHGTheorem.Herbrand.CanonicalMapRegression
import LCS.Herbrand.SHGTheorem.Herbrand.OrderedCompositionRegression
import LCS.Herbrand.SHGTheorem.Herbrand.Alteration
import LCS.Herbrand.SHGTheorem.Herbrand.ClosedSubstitution
import LCS.Herbrand.SHGTheorem.Herbrand.EigenvariablePurity
import LCS.Herbrand.SHGTheorem.Herbrand.FormulaProvenance
import LCS.Herbrand.SHGTheorem.Herbrand.ClosedBindings
import LCS.Herbrand.SHGTheorem.Herbrand.LowerConstruction
import LCS.Herbrand.SHGTheorem.Herbrand.LowerConstructionEq
import LCS.Herbrand.SHGTheorem.Herbrand.HalfHerbrand
import LCS.Herbrand.SHGTheorem.Herbrand.UniversalPrenexMidsequent

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

end LCS.Herbrand.SHGTheorem.Herbrand
