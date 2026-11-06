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
import LCS.Herbrand.NNFHauptsatz.Theorem.QuantifierRules
import LCS.Herbrand.NNFHauptsatz.Theorem.PermutationLowerRules
import LCS.Herbrand.NNFHauptsatz.Theorem.RuleApplications
import LCS.Herbrand.NNFHauptsatz.Theorem.PermutableOccurrences
import LCS.Herbrand.NNFHauptsatz.Theorem.ExchangeBodies

/-! # Herbrand.NNFHauptsatz.Theorem.ExchangeKernel

Lemma 7.4.2: the bounded local exchange kernel, its case simulation and the
propositional/weakening branch lengths (a string ba becomes ab, abb or abbb).
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
namespace G2nnfExchangeCasePosition

/-- Exact multiplicity of the reused non-selected source frontier.  A direct
exchange retains one copy for each source other premise.  The contraction
simulation contains two lower applications, so it retains two copies.  The
case is eliminated from the structural simulation witness itself; no caller
can supply an unrelated multiplier or count. -/
def expectedOtherFrontierCount {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {tree : G2nnfProofTree hL Γ Δ}
    {body : G2nnfExchangeBody redex tree}
    {role : G2nnfPrincipalOccurrenceRole
      redex.quantifierRule.side redex.quantifierRule.principal
      redex.lowerApplication.rawGamma redex.lowerApplication.rawDelta
      (redex.lowerRule.selectedFocus redex.lowerApplication.choice)}
    {principalCase : G2nnfQuantifierPrincipalCase
      redex.quantifierRule.side redex.quantifierRule.principal
      redex.quantifierApplication.rawGamma
      redex.quantifierApplication.rawDelta
      redex.lowerApplication.rawGamma redex.lowerApplication.rawDelta}
    (position :
      G2nnfExchangeCasePosition redex body role principalCase) : Nat :=
  match position with
  | .directContext _ _ _ _ _ =>
    redex.lowerApplication.otherPremiseCount
  | .directFocused _ _ _ _ _ _ =>
    redex.lowerApplication.otherPremiseCount
  | .withContraction _ _ _ _ _ =>
    2 * redex.lowerApplication.otherPremiseCount

end G2nnfExchangeCasePosition
namespace G2nnfExchangeBody

/-- Number of exact source quantifier-premise frontier occurrences. -/
def quantifierFrontierCount {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {tree : G2nnfProofTree hL Γ Δ} :
    G2nnfExchangeBody redex tree → Nat
  | .quantifierFrontier _ => 1
  | .otherFrontier _ => 0
  | .lowerOne _ _ _ _ _ body => body.quantifierFrontierCount
  | .lowerTwo _ _ _ _ _ _ body1 body2 =>
    body1.quantifierFrontierCount + body2.quantifierFrontierCount
  | .weakening _ _ _ _ _ body => body.quantifierFrontierCount

/-- Number of exact non-selected lower-premise frontier occurrences. -/
def otherFrontierCount {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {tree : G2nnfProofTree hL Γ Δ} :
    G2nnfExchangeBody redex tree → Nat
  | .quantifierFrontier _ => 0
  | .otherFrontier _ => 1
  | .lowerOne _ _ _ _ _ body => body.otherFrontierCount
  | .lowerTwo _ _ _ _ _ _ body1 body2 =>
    body1.otherFrontierCount + body2.otherFrontierCount
  | .weakening _ _ _ _ _ body => body.otherFrontierCount

/-- For every branch ending at the source quantifier premise, count the
propositional/weakening (`b`) nodes below the moved quantifier. -/
def quantifierBranchLengths {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {tree : G2nnfProofTree hL Γ Δ} :
    G2nnfExchangeBody redex tree → List Nat
  | .quantifierFrontier _ => [0]
  | .otherFrontier _ => []
  | .lowerOne _ _ _ _ _ body =>
    body.quantifierBranchLengths.map Nat.succ
  | .lowerTwo _ _ _ _ _ _ body1 body2 =>
    (body1.quantifierBranchLengths ++
      body2.quantifierBranchLengths).map Nat.succ
  | .weakening _ _ _ _ _ body =>
    body.quantifierBranchLengths.map Nat.succ

/-- Count admitted `b` nodes on every branch ending at either exact source
frontier.  This prevents an unbounded auxiliary branch from hiding beside the
selected quantifier branch. -/
def allBranchLengths {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {tree : G2nnfProofTree hL Γ Δ} :
    G2nnfExchangeBody redex tree → List Nat
  | .quantifierFrontier _ => [0]
  | .otherFrontier _ => [0]
  | .lowerOne _ _ _ _ _ body =>
    body.allBranchLengths.map Nat.succ
  | .lowerTwo _ _ _ _ _ _ body1 body2 =>
    (body1.allBranchLengths ++ body2.allBranchLengths).map Nat.succ
  | .weakening _ _ _ _ _ body =>
    body.allBranchLengths.map Nat.succ

end G2nnfExchangeBody

/-- The exact textbook principal subcase retained by a redex. -/
inductive G2nnfPrincipalCaseKind where
  | direct
  | withContraction
deriving DecidableEq

namespace G2nnfQuantifierPrincipalCase

/-- Forget proof fields while retaining the direct/contraction distinction. -/
def kind {L : Language}
    {side : G2nnfSequentSide} {A : FormulaN L}
    {quantGamma quantDelta lowerGamma lowerDelta :
      LCS.Finset (FormulaN L)} :
    G2nnfQuantifierPrincipalCase side A
      quantGamma quantDelta lowerGamma lowerDelta →
      G2nnfPrincipalCaseKind
  | .direct _ => .direct
  | .withContraction _ _ => .withContraction

end G2nnfQuantifierPrincipalCase
namespace G2nnfPrincipalCaseKind

/-- A direct exchange has at least one residual `b` node; the simulated
contraction case has at least two.  Both retain the global upper bound three. -/
def minimumBranchLength : G2nnfPrincipalCaseKind → Nat
  | .direct => 1
  | .withContraction => 2

end G2nnfPrincipalCaseKind

/-- A bounded, exact local replacement for one adjacent occurrence.

The target is an exact reprincipalized quantifier application whose premise
is generated by `G2nnfExchangeBody`.  Frontier counts enforce exact source
reuse with case-indexed contraction multiplicity, and the branch bound records
precisely the textbook
`ba ↦ ab | abb | abbb` effect.  The located lower descendant supplies the
exact target occurrence used by the order certificate. -/
structure G2nnfExchangeKernel {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂)
    (replacement : G2nnfProofTree hL Γ Δ) where
  targetPrincipal : FormulaN L
  principalCorrespondence :
    G2nnfExchangePrincipalCorrespondence
      redex.quantifierRule redex.lowerRule
      redex.lowerApplication.choice redex.principalOccurrence
      targetPrincipal
  Γbody : LCS.Finset (FormulaN L)
  Δbody : LCS.Finset (FormulaN L)
  body : G2nnfProofTree hL Γbody Δbody
  quantifierGamma : LCS.Finset (FormulaN L)
  quantifierDelta : LCS.Finset (FormulaN L)
  quantifierApplication :
    G2nnfOnePremiseApplication
      (principalCorrespondence.reprincipalizedRule quantifierGamma quantifierDelta) replacement
  quantifierPremise :
    G2nnfOnePremiseFrontier quantifierApplication body
  bodyShape : G2nnfExchangeBody redex body
  simulationPosition :
    G2nnfExchangeCasePosition redex bodyShape
      redex.principalOccurrence redex.principalCase
  quantifierFrontierLinear :
    bodyShape.quantifierFrontierCount = 1
  otherFrontierMultiplicity :
    bodyShape.otherFrontierCount =
      simulationPosition.expectedOtherFrontierCount
  quantifierBranchBound :
    ∀ n : Nat, n ∈ bodyShape.quantifierBranchLengths →
      redex.principalCase.kind.minimumBranchLength ≤ n
  allBranchBound :
    ∀ n : Nat, n ∈ bodyShape.allBranchLengths → n ≤ 3

namespace G2nnfExchangeKernel

/-- Case-indexed expected multiplicity exported from the exact simulation
position retained by the kernel. -/
def expectedOtherFrontierCount {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    {replacement : G2nnfProofTree hL Γ Δ}
    (kernel : G2nnfExchangeKernel redex replacement) : Nat :=
  kernel.simulationPosition.expectedOtherFrontierCount

end G2nnfExchangeKernel
end LCS.Herbrand.NNFHauptsatz.Theorem
end
