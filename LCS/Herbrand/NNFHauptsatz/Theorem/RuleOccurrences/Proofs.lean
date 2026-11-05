import LCS.Herbrand.NNFHauptsatz.Theorem.RuleOccurrences

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

namespace G2nnfSelectedPremiseOccurrence



end G2nnfSelectedPremiseOccurrence

end LCS.Herbrand.NNFHauptsatz.Theorem

end

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

namespace G2nnfPermutableOccurrence

helper /-- Structural regression: the selected occurrence accessor cannot change the
selected premise tree stored in the carrier. -/
theorem G2nnfPermutableOccurrence.selectedOccurrence_node {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂) :
    redex.selectedOccurrence.node = redex.selectedPremise :=
  rfl

helper /-- Structural regression: the ambient quantifier path factors through the
exact selected premise path, so an unrelated equal-valued `R₁` occurrence
cannot be substituted. -/
theorem G2nnfPermutableOccurrence.quantifierOccurrence_path {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂) :
    redex.quantifierOccurrence.path =
      redex.selectedOccurrence.path.trans redex.pathFromSelectedPremise :=
  rfl

end G2nnfPermutableOccurrence

end LCS.Herbrand.NNFHauptsatz.Theorem

end
