import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.OccurrenceLineage

section
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

-- ===================================================================
-- Lemma 7.6.2: chronological closed lower-path state
-- ===================================================================

/-- Every variable in the supplied chronological list still has a
free occurrence in the current antecedent.  This is the live invariant
used to turn occurrence-sensitive purity into pairwise freshness. -/
def AntecedentVariablesLive
    {L : Language} (variables : List Nat)
    (Gamma : LCS.Finset (FormulaN L)) : Prop :=
  ∀ y, y ∈ variables →
    ∃ A, A ∈ Gamma ∧ y ∈ formulaFVN A

end LCS.Herbrand.SHGTheorem.Herbrand
end
