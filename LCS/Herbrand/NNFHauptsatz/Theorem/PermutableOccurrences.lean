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
import LCS.Herbrand.NNFHauptsatz.Theorem.RootToNodePaths
import LCS.Herbrand.NNFHauptsatz.Theorem.QuantifierRules
import LCS.Herbrand.NNFHauptsatz.Theorem.PermutationLowerRules
import LCS.Herbrand.NNFHauptsatz.Theorem.RuleApplications
import Attach
import LCS.Herbrand.NNFHauptsatz.Theorem.PermutableOccurrences.ProofsStamp

/-! # Herbrand.NNFHauptsatz.Theorem.PermutableOccurrences

Lemma 7.4.2: exact occurrences of a quantifier rule R1 that can be permuted with a
lower rule R2 (Definition 7.3.2 redexes), their principal cases and lineages.
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

/-- Why the quantifier principal formula occurs in the selected premise of
`R₂`: it is either inherited from the exact raw context on that side, or is
the exact focused formula contributed by the selected propositional premise.
The latter constructor also records absence from the raw context, preventing
the two roles from being conflated. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfPrincipalOccurrenceRole {L : Language}
    (side : G2nnfSequentSide) (A : FormulaN L)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (focus : Option (G2nnfSequentSide × FormulaN L)) : Type where
  | context
      (hMem : Membership.mem (side.context Gamma Delta) A) :
      G2nnfPrincipalOccurrenceRole side A Gamma Delta focus
  | focused
      (hNotMem : ¬ Membership.mem (side.context Gamma Delta) A)
      (hFocus : focus = some (side, A)) :
      G2nnfPrincipalOccurrenceRole side A Gamma Delta focus

/-- Internal two-rule case split used in the local permutation proof.
This is not the presentation terminology for one quantifier inference.
`direct` covers `A` already present in the lower raw context or no retained
copy of `A` in the quantifier's top raw context.  `withContraction` records the
complementary case: `A` is absent from the lower context but retained in the
quantifier raw context, which is exactly the set-based simulated-contraction
subcase. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfQuantifierPrincipalCase {L : Language}
    (side : G2nnfSequentSide) (A : FormulaN L)
    (quantGamma quantDelta lowerGamma lowerDelta :
      LCS.Finset (FormulaN L)) : Type where
  | direct
      (hDirect :
        Membership.mem (side.context lowerGamma lowerDelta) A ∨
        ¬ Membership.mem (side.context quantGamma quantDelta) A) :
      G2nnfQuantifierPrincipalCase side A
        quantGamma quantDelta lowerGamma lowerDelta
  | withContraction
      (hLower :
        ¬ Membership.mem (side.context lowerGamma lowerDelta) A)
      (hTop :
        Membership.mem (side.context quantGamma quantDelta) A) :
      G2nnfQuantifierPrincipalCase side A
        quantGamma quantDelta lowerGamma lowerDelta

/-- Occurrence-sensitive input carrier for one local Lemma 7.4.2 exchange.

The carrier links, in one dependent value:
* the exact `R₂` application and one selected premise occurrence in `T`;
* the exact one-premise `R₁` application above that premise;
* a path on which every strict intermediate rule is a weakening;
* constructor views proving that `R₁` is quantifier and `R₂` is
  propositional/weakening; and
* the raw-context and principal-role evidence needed for both textbook
  subcases.

No field identifies applications by rule-value equality alone. -/
@[blueprint "chap7__lemma_7_4_2"]
structure G2nnfPermutableOccurrence {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Γroot Δroot)
    (R₁ R₂ : G2nnfRuleCore L) where
  lowerRule : G2nnfPermutationLowerRuleView R₂
  lowerScope : R₂.isPropositionalRule ∨ R₂.isWeakening
  Γprem : LCS.Finset (FormulaN L)
  Δprem : LCS.Finset (FormulaN L)
  selectedPremise : G2nnfProofTree hL Γprem Δprem
  lowerApplication :
    G2nnfSelectedPremiseOccurrence T R₂ selectedPremise
  Γquant : LCS.Finset (FormulaN L)
  Δquant : LCS.Finset (FormulaN L)
  quantifierNode : G2nnfProofTree hL Γquant Δquant
  quantifierRule : G2nnfQuantifierRuleView R₁
  quantifierApplication :
    G2nnfOnePremiseApplication R₁ quantifierNode
  pathFromSelectedPremise :
    RootToNodePath selectedPremise quantifierNode
  weakeningIntermediates :
    G2nnfWeakeningOnlyPath pathFromSelectedPremise
  principalOccurrence :
    G2nnfPrincipalOccurrenceRole quantifierRule.side
      quantifierRule.principal
      lowerApplication.rawGamma lowerApplication.rawDelta
      (lowerRule.selectedFocus lowerApplication.choice)
  principalCase :
    G2nnfQuantifierPrincipalCase quantifierRule.side
      quantifierRule.principal
      quantifierApplication.rawGamma quantifierApplication.rawDelta
      lowerApplication.rawGamma lowerApplication.rawDelta

/-- Proof-relevant evidence that an exact root-to-node path is empty.  A
single textbook `ba ↦ ab | abb | abbb` exchange is adjacent; a nonempty
weakening section must be handled later by iterating this local relation. -/
inductive G2nnfRootPath {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)] :
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)} →
    {root : G2nnfProofTree hL Γroot Δroot} →
    {node : G2nnfProofTree hL Γnode Δnode} →
    RootToNodePath root node → Type where
  | root {Γ Δ : LCS.Finset (FormulaN L)}
      (T : G2nnfProofTree hL Γ Δ) :
      G2nnfRootPath (.root T)

/-- Constructor-schema correspondence for the quantifier principal after an
exchange.  A context occurrence retains the old principal.  A focused
occurrence is reprincipalized at the exact logical principal of the lower
rule. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfExchangePrincipalCorrespondence {L : Language}
    {R₁ R₂ : G2nnfRuleCore L}
    (quantifier : G2nnfQuantifierRuleView R₁)
    (lower : G2nnfPermutationLowerRuleView R₂)
    (choice : G2nnfPremiseChoice)
    {lowerGamma lowerDelta : LCS.Finset (FormulaN L)} :
    G2nnfPrincipalOccurrenceRole
        quantifier.side quantifier.principal lowerGamma lowerDelta
        (lower.selectedFocus choice) →
      FormulaN L → Type where
  | context
      (hMem : Membership.mem
        (quantifier.side.context lowerGamma lowerDelta)
        quantifier.principal) :
      G2nnfExchangePrincipalCorrespondence quantifier lower choice
        (G2nnfPrincipalOccurrenceRole.context hMem)
        quantifier.principal
  | focused
      (hNotMem : ¬ Membership.mem
        (quantifier.side.context lowerGamma lowerDelta)
        quantifier.principal)
      (hFocus : lower.selectedFocus choice =
        some (quantifier.side, quantifier.principal))
      (targetPrincipal : FormulaN L)
      (hPrincipal : lower.principal =
        some (quantifier.side, targetPrincipal))
      (lifted : G2nnfPermutationLowerRuleView.G2nnfFocusedOccurrenceLift
        targetPrincipal quantifier.occurrence.selected)
      (hLift : lower.liftFocusedOccurrence choice hFocus hPrincipal
        quantifier.occurrence = some lifted) :
      G2nnfExchangePrincipalCorrespondence quantifier lower choice
        (G2nnfPrincipalOccurrenceRole.focused hNotMem hFocus)
        targetPrincipal

  | quantifierFocused
      (lowerQuantifier : G2nnfQuantifierRuleView R₂)
      (hNotMem : ¬ Membership.mem
        (quantifier.side.context lowerGamma lowerDelta) quantifier.principal)
      (hFocus : lower.selectedFocus choice =
        some (quantifier.side, quantifier.principal))
      (targetPrincipal : FormulaN L)
      (hPrincipal : lower.principal = some (quantifier.side, targetPrincipal))
      (lifted : G2nnfPermutationLowerRuleView.G2nnfFocusedOccurrenceLift
        targetPrincipal quantifier.occurrence.selected)
      (hAddress : lifted.occurrence.address = quantifier.occurrence.address) :
      G2nnfExchangePrincipalCorrespondence quantifier lower choice
        (G2nnfPrincipalOccurrenceRole.focused hNotMem hFocus) targetPrincipal

namespace G2nnfExchangePrincipalCorrespondence

/-- Exact target occurrence determined by a context/focused principal
correspondence. The propositional focused case lifts through the selected
connective branch; a quantifier focused case supplies a maximal occurrence in
the exact lower principal with the same selected quantified formula and branch
address. -/
def liftedOccurrence {L : Language} {R₁ R₂ : G2nnfRuleCore L}
    {quantifier : G2nnfQuantifierRuleView R₁}
    {lower : G2nnfPermutationLowerRuleView R₂}
    {choice : G2nnfPremiseChoice}
    {lowerGamma lowerDelta : LCS.Finset (FormulaN L)}
    {role : G2nnfPrincipalOccurrenceRole
      quantifier.side quantifier.principal lowerGamma lowerDelta
      (lower.selectedFocus choice)}
    {target : FormulaN L}
    (correspondence :
      G2nnfExchangePrincipalCorrespondence
        quantifier lower choice role target) :
    G2nnfPermutationLowerRuleView.G2nnfFocusedOccurrenceLift
      target quantifier.occurrence.selected :=
  match correspondence with
  | .context _ => ⟨quantifier.occurrence, rfl⟩
  | .focused _ _ _ _ lifted _ => lifted
  | .quantifierFocused _ _ _ _ _ lifted _ => lifted

/-- The occurrence-indexed quantifier rule at the target principal and
supplied output contexts. -/
@[blueprint "chap7__lemma_7_4_2"]
def reprincipalizedRule {L : Language} {R₁ R₂ : G2nnfRuleCore L}
    {quantifier : G2nnfQuantifierRuleView R₁}
    {lower : G2nnfPermutationLowerRuleView R₂}
    {choice : G2nnfPremiseChoice}
    {lowerGamma lowerDelta : LCS.Finset (FormulaN L)}
    {role : G2nnfPrincipalOccurrenceRole
      quantifier.side quantifier.principal lowerGamma lowerDelta
      (lower.selectedFocus choice)}
    {target : FormulaN L}
    (correspondence :
      G2nnfExchangePrincipalCorrespondence
        quantifier lower choice role target)
    (targetGamma targetDelta : LCS.Finset (FormulaN L)) :
    G2nnfRuleCore L :=
  quantifier.reprincipalAt correspondence.liftedOccurrence.occurrence
    correspondence.liftedOccurrence.selected_eq targetGamma targetDelta

end G2nnfExchangePrincipalCorrespondence

/-- A lower-rule application admitted in the exchanged fragment is either the
original constructor schema or the result of instantiating only its selected
premise occurrence, each at explicit output contexts. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfLowerRuleDescendant {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂) :
    G2nnfRuleCore L → Type where
  | original (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfLowerRuleDescendant redex (redex.lowerRule.withContexts Gamma Delta)
  | instantiated (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfLowerRuleDescendant redex
        (redex.lowerRule.instantiateSelectedOfPropositional redex.lowerScope redex.quantifierRule
          redex.lowerApplication.choice Gamma Delta)

/-- Definition 7.3.2 as imported by §7.4.3: an upper quantifier application,
any lower rule with a selected premise, and the intervening weakening section.
No propositional side-formula classification is required to form this redex. -/
@[blueprint "chap7__definition_7_3_2"]
structure G2nnfPermutationRedex {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Γroot Δroot)
    (R₁ R₂ : G2nnfRuleCore L) where
  lowerRule : G2nnfPermutationLowerRuleView R₂
  Γprem : LCS.Finset (FormulaN L)
  Δprem : LCS.Finset (FormulaN L)
  selectedPremise : G2nnfProofTree hL Γprem Δprem
  lowerApplication : G2nnfSelectedPremiseOccurrence T R₂ selectedPremise
  Γquant : LCS.Finset (FormulaN L)
  Δquant : LCS.Finset (FormulaN L)
  quantifierNode : G2nnfProofTree hL Γquant Δquant
  quantifierRule : G2nnfQuantifierRuleView R₁
  quantifierApplication : G2nnfOnePremiseApplication R₁ quantifierNode
  pathFromSelectedPremise : RootToNodePath selectedPremise quantifierNode
  weakeningIntermediates : G2nnfWeakeningOnlyPath pathFromSelectedPremise

/-- The exact lower application whose conclusion is the boundary of Q. -/
def G2nnfPermutationRedex.lowerOccurrence {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutationRedex T R₁ R₂) :
    G2nnfLocatedRuleApplication T R₂ :=
  redex.lowerApplication.applicationOccurrence

/-- Instances of the lower inference in Q. Contexts may change; propositional
side formulae may be instantiated at the selected premise. A quantifier lower
rule transports its exact selected quantified formula, binder and term to an
explicit maximal occurrence at the same branch address. A cut retains its formula, or cuts the instance
of the upper principal when that principal was the selected cut formula.
All generated instances still require the ordinary G2nnf side conditions. -/
@[blueprint "chap7__definition_7_3_2"]
inductive G2nnfPermutationLowerInstance {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutationRedex T R₁ R₂) : G2nnfRuleCore L → Type where
  | original (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerInstance redex
        (redex.lowerRule.withContexts Gamma Delta)
  | focused
      (hProp : R₂.isPropositionalRule)
      (hFocus : redex.lowerRule.selectedFocus redex.lowerApplication.choice =
        some (redex.quantifierRule.side, redex.quantifierRule.principal))
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerInstance redex
        (redex.lowerRule.instantiateSelectedOfPropositional (Or.inl hProp) redex.quantifierRule
          redex.lowerApplication.choice Gamma Delta)
  | quantifier (lower : G2nnfQuantifierRuleView R₂)
      {A : FormulaN L} (occurrence : MaxQuantifierOccurrence A)
      (hSelected : occurrence.selected = lower.occurrence.selected)
      (hAddress : occurrence.address = lower.occurrence.address)
      (hFocus : redex.lowerRule.selectedFocus redex.lowerApplication.choice =
        some (redex.quantifierRule.side, redex.quantifierRule.principal))
      (hPremise : occurrence.replace lower.replacement =
        redex.quantifierRule.premisePrincipal)
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerInstance redex
        (lower.reprincipalAt occurrence hSelected Gamma Delta)
  | cut (A : FormulaN L) (Lambda Theta Gamma Delta : LCS.Finset (FormulaN L))
      (hSource : ∃ Lambda₀ Theta₀ Gamma₀ Delta₀,
        R₂ = .cut A Lambda₀ Theta₀ Gamma₀ Delta₀) :
      G2nnfPermutationLowerInstance redex (.cut A Lambda Theta Gamma Delta)
  | cutInstance (Lambda Theta Gamma Delta : LCS.Finset (FormulaN L))
      (hSource : ∃ Lambda₀ Theta₀ Gamma₀ Delta₀,
        R₂ = .cut redex.quantifierRule.principal Lambda₀ Theta₀ Gamma₀ Delta₀)
      (hFocus : redex.lowerRule.selectedFocus redex.lowerApplication.choice =
        some (redex.quantifierRule.side, redex.quantifierRule.principal)) :
      G2nnfPermutationLowerInstance redex
        (.cut redex.quantifierRule.premisePrincipal Lambda Theta Gamma Delta)
end LCS.Herbrand.NNFHauptsatz.Theorem
end
