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
import LCS.Herbrand.NNFHauptsatz.Theorem.VariableSupport
import LCS.Herbrand.NNFHauptsatz.Theorem.Paths
import LCS.Herbrand.NNFHauptsatz.Theorem.Purity
import Attach
import LCS.Herbrand.NNFHauptsatz.Theorem.RuleOccurrences.ProofsStamp

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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The exact selected premise as a node occurrence of the ambient proof. -/
def premiseOccurrence {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γprem Δprem : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot} {R₂ : G2nnfRuleCore L}
    {premise : G2nnfProofTree hL Γprem Δprem}
    (selected : G2nnfSelectedPremiseOccurrence root R₂ premise) :
    NodeOccurrence root Γprem Δprem :=
  ⟨premise, selected.premisePath⟩

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Midsequents
/-- The exact lower-rule application occurrence containing the selected
premise. -/
def applicationOccurrence {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γprem Δprem : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot} {R₂ : G2nnfRuleCore L}
    {premise : G2nnfProofTree hL Γprem Δprem}
    (selected : G2nnfSelectedPremiseOccurrence root R₂ premise) :
    G2nnfLocatedRuleApplication root R₂ :=
  match selected with
  | .one hAdmit hPrem hSC sub path =>
    ⟨_, _,
      .onePremise R₂ hAdmit hPrem hSC sub,
      path, .one hAdmit hPrem hSC sub⟩
  | .left hAdmit hPrem hSC sub1 sub2 path =>
    ⟨_, _,
      .twoPremise R₂ hAdmit hPrem hSC sub1 sub2,
      path, .two hAdmit hPrem hSC sub1 sub2⟩
  | .right hAdmit hPrem hSC sub1 sub2 path =>
    ⟨_, _,
      .twoPremise R₂ hAdmit hPrem hSC sub1 sub2,
      path, .two hAdmit hPrem hSC sub1 sub2⟩

/-- A one-premise lower application has no other frontier; a binary lower
application has exactly one. -/
@[blueprint "chap7__lemma_7_4_2"]
def otherPremiseCount {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γprem Δprem : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot} {R₂ : G2nnfRuleCore L}
    {premise : G2nnfProofTree hL Γprem Δprem}
    (selected : G2nnfSelectedPremiseOccurrence root R₂ premise) : Nat :=
  match selected with
  | .one .. => 0
  | .left .. => 1
  | .right .. => 1

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
namespace G2nnfQuantifierRuleView

/-- The stored context on the side of this single quantifier inference. -/
@[blueprint "chap7__definition_7_4_3"]
def rawContext {L : Language} {rule : G2nnfRuleCore L}
    (view : G2nnfQuantifierRuleView rule) : LCS.Finset (FormulaN L) :=
  view.side.context (g2nnfRuleSideContexts rule).1 (g2nnfRuleSideContexts rule).2

/-- The isolated-A upper and lower displays using the supplied remainder Λ.
The opposite side is unchanged; the upper display retains both A and the
replacement at the inference's exact maximal quantifier occurrence. -/
@[blueprint "chap7__definition_7_4_3"]
def contractionDisplay {L : Language} [DecidableEq (FormulaN L)]
    {rule : G2nnfRuleCore L} (view : G2nnfQuantifierRuleView rule)
    (Λ : LCS.Finset (FormulaN L)) :
    (LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) ×
    (LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) :=
  match view.side with
  | .left =>
    ((LCS.Finset.insert view.principal (LCS.Finset.insert view.premisePrincipal Λ),
      (g2nnfRuleSideContexts rule).2),
     (LCS.Finset.insert view.principal Λ, (g2nnfRuleSideContexts rule).2))
  | .right =>
    (((g2nnfRuleSideContexts rule).1,
      LCS.Finset.insert view.principal (LCS.Finset.insert view.premisePrincipal Λ)),
     ((g2nnfRuleSideContexts rule).1, LCS.Finset.insert view.principal Λ))

end G2nnfQuantifierRuleView
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

/-- Definition 7.4.3 (presentation convention, §7.4.3): a legal single
quantifier inference displayed with contraction. A belongs to its stored
context; Λ is exactly that context minus A, and A is isolated in both the
upper and lower displays. This applies to all four quantifier kinds, on the
appropriate side. It does not classify a pair of permuted inferences. -/
@[blueprint "chap7__definition_7_4_3"]
structure G2nnfQuantifierWithContraction {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] (rule : G2nnfRule L hL)
    (view : G2nnfQuantifierRuleView rule.val)
    (Λ : LCS.Finset (FormulaN L)) : Prop where
  legal : rule.SideConditions
  principalInContext : Membership.mem view.rawContext view.principal
  remainder : Λ = view.rawContext.erase view.principal
  principalAbsent : ¬ Membership.mem Λ view.principal
  upperDisplay : rule.premises = [(view.contractionDisplay Λ).1]
  lowerDisplay : rule.conclusion = (view.contractionDisplay Λ).2

/-- Definition 7.4.3 (presentation convention, §7.4.3): the original display
of one legal quantifier inference is without contraction when A belongs to
its stored context, or A is absent from the whole upper sequent (both sides).
This is the PDF's test, for all four quantifier kinds. The first alternative
can also admit an isolated-A with-contraction display; the two presentations
are not complementary predicates. -/
@[blueprint "chap7__definition_7_4_3"]
def G2nnfQuantifierWithoutContraction {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] (rule : G2nnfRule L hL)
    (view : G2nnfQuantifierRuleView rule.val) : Prop :=
  rule.SideConditions ∧
    (Membership.mem view.rawContext view.principal ∨
      ∀ upper ∈ rule.premises,
        ¬ Membership.mem upper.1 view.principal ∧
        ¬ Membership.mem upper.2 view.principal)

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
namespace G2nnfPrincipalOccurrenceRole

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Required lower schema at supplied output contexts, determined by the
exact context/focused role. -/
def requiredLowerRule {L : Language} [DecidableEq (FormulaN L)]
    {R₁ R₂ : G2nnfRuleCore L}
    (quantifier : G2nnfQuantifierRuleView R₁)
    (lower : G2nnfPermutationLowerRuleView R₂)
    (hLower : R₂.isPropositionalRule ∨ R₂.isWeakening)
    (choice : G2nnfPremiseChoice)
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (role : G2nnfPrincipalOccurrenceRole quantifier.side
      quantifier.principal Gamma Delta (lower.selectedFocus choice))
    (targetGamma targetDelta : LCS.Finset (FormulaN L)) :
    G2nnfRuleCore L :=
  match role with
  | .context _ => lower.withContexts targetGamma targetDelta
  | .focused _ _ =>
    lower.instantiateSelectedOfPropositional hLower quantifier choice targetGamma targetDelta

end G2nnfPrincipalOccurrenceRole
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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The exact selected premise occurrence packaged by a redex carrier. -/
def selectedOccurrence {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂) :
    NodeOccurrence T redex.Γprem redex.Δprem :=
  redex.lowerApplication.premiseOccurrence

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The exact quantifier occurrence, obtained only by composing the selected
premise occurrence with the stored weakening-only relative path. -/
def quantifierOccurrence {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂) :
    NodeOccurrence T redex.Γquant redex.Δquant :=
  ⟨redex.quantifierNode,
    redex.selectedOccurrence.path.trans redex.pathFromSelectedPremise⟩





end G2nnfPermutableOccurrence
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

-- ATTACH-BLOCKER: unsupported untagged inductive
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
namespace G2nnfExchangePrincipalCorrespondence

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
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
namespace G2nnfPrincipalOccurrenceRole

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Required lower lineage determined by the exact context/focused role. -/
def requiredLowerLineage {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂)
    (role : G2nnfPrincipalOccurrenceRole redex.quantifierRule.side
      redex.quantifierRule.principal
      redex.lowerApplication.rawGamma redex.lowerApplication.rawDelta
      (redex.lowerRule.selectedFocus redex.lowerApplication.choice))
    (targetGamma targetDelta : LCS.Finset (FormulaN L)) :
    G2nnfLowerRuleDescendant redex
      (role.requiredLowerRule redex.quantifierRule redex.lowerRule redex.lowerScope
        redex.lowerApplication.choice targetGamma targetDelta) :=
  match role with
  | .context _ => .original targetGamma targetDelta
  | .focused _ _ => .instantiated targetGamma targetDelta

end G2nnfPrincipalOccurrenceRole
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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The lower-schema descendant which must occur on the exchanged
quantifier branch.  An inherited context occurrence retains the original
lower schema, while a focused occurrence requires its exact quantifier image.
Both are instantiated at the supplied output contexts. -/
def requiredLowerRule {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂)
    (targetGamma targetDelta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L :=
  redex.principalOccurrence.requiredLowerRule
    redex.quantifierRule redex.lowerRule redex.lowerScope redex.lowerApplication.choice targetGamma targetDelta

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Constructor-exact lineage of `requiredLowerRule`.  This couples the
context/focused principal role to the original/instantiated lower descendant
instead of allowing those two certificates to vary independently. -/
def requiredLowerLineage {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂)
    (targetGamma targetDelta : LCS.Finset (FormulaN L)) :
    G2nnfLowerRuleDescendant redex (redex.requiredLowerRule targetGamma targetDelta) :=
  redex.principalOccurrence.requiredLowerLineage redex targetGamma targetDelta

end G2nnfPermutableOccurrence
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

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- Fixed weakening schemas which may occur in the bounded simulation.  The
weakened formula is computed from a source principal or its exact quantifier
image; no arbitrary formula can be injected into the exchanged fragment. -/
inductive G2nnfExchangeWeakening {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂) :
    G2nnfRuleCore L → Type where
  | quantifierPrincipal (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfExchangeWeakening redex
        (redex.quantifierRule.side.weakeningRule
          redex.quantifierRule.principal Gamma Delta)
  | quantifierPremise (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfExchangeWeakening redex
        (redex.quantifierRule.side.weakeningRule
          redex.quantifierRule.premisePrincipal Gamma Delta)
  | lowerPrincipal (side : G2nnfSequentSide) (F : FormulaN L)
      (hPrincipal : redex.lowerRule.principal = some (side, F))
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfExchangeWeakening redex (side.weakeningRule F Gamma Delta)
  | instantiatedLowerPrincipal
      (side : G2nnfSequentSide) (F : FormulaN L)
      (hPrincipal :
        redex.lowerRule.instantiatedPrincipal
          redex.quantifierRule redex.lowerApplication.choice =
            some (side, F))
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfExchangeWeakening redex
        (side.weakeningRule F Gamma Delta)

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- Exact-shape grammar for the part of the exchanged fragment above the
moved quantifier.  Leaves are only the original quantifier premise and the
original non-selected lower premise.  Internal nodes are only lower-schema
descendants or one of the fixed weakening simulations above.  In particular,
there is no cut constructor and no constructor accepting the old selected
premise, quantifier node, or an arbitrary proof tree. -/
inductive G2nnfExchangeBody {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → Type where
  | quantifierFrontier
      {Γ Δ : LCS.Finset (FormulaN L)}
      {tree : G2nnfProofTree hL Γ Δ}
      (frontier : G2nnfOnePremiseFrontier
        redex.quantifierApplication tree) :
      G2nnfExchangeBody redex tree
  | otherFrontier
      {Γ Δ : LCS.Finset (FormulaN L)}
      {tree : G2nnfProofTree hL Γ Δ}
      (frontier : G2nnfOtherPremiseFrontier
        redex.lowerApplication tree) :
      G2nnfExchangeBody redex tree
  | lowerOne {targetRule : G2nnfRuleCore L}
      (lineage : G2nnfLowerRuleDescendant redex targetRule)
      (hAdmit : targetRule.BareAtomicAxiom)
      (hPrem : (targetRule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions targetRule)
      (sub : G2nnfProofTree hL
        ((targetRule.premises)[0]'(by omega)).1
        ((targetRule.premises)[0]'(by omega)).2)
      (body : G2nnfExchangeBody redex sub) :
      G2nnfExchangeBody redex
        (.onePremise targetRule hAdmit hPrem hSC sub)
  | lowerTwo {targetRule : G2nnfRuleCore L}
      (lineage : G2nnfLowerRuleDescendant redex targetRule)
      (hAdmit : targetRule.BareAtomicAxiom)
      (hPrem : (targetRule.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions targetRule)
      (sub1 : G2nnfProofTree hL
        ((targetRule.premises)[0]'(by omega)).1
        ((targetRule.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((targetRule.premises)[1]'(by omega)).1
        ((targetRule.premises)[1]'(by omega)).2)
      (body1 : G2nnfExchangeBody redex sub1)
      (body2 : G2nnfExchangeBody redex sub2) :
      G2nnfExchangeBody redex
        (.twoPremise targetRule hAdmit hPrem hSC sub1 sub2)
  | weakening {targetRule : G2nnfRuleCore L}
      (allowed : G2nnfExchangeWeakening redex targetRule)
      (hAdmit : targetRule.BareAtomicAxiom)
      (hPrem : (targetRule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions targetRule)
      (sub : G2nnfProofTree hL
        ((targetRule.premises)[0]'(by omega)).1
        ((targetRule.premises)[0]'(by omega)).2)
      (body : G2nnfExchangeBody redex sub) :
      G2nnfExchangeBody redex
        (.onePremise targetRule hAdmit hPrem hSC sub)

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- A grammar-derived path to the exact source quantifier-premise frontier.
It may cross only nodes generated by `G2nnfExchangeBody`; the sole stopping
constructor is the exact quantifier frontier itself. -/
inductive G2nnfExchangeBodyQuantifierPosition {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    {tree : G2nnfProofTree hL Γ Δ} →
    G2nnfExchangeBody redex tree → Type where
  | here
      {Γ Δ : LCS.Finset (FormulaN L)}
      {tree : G2nnfProofTree hL Γ Δ}
      (frontier : G2nnfOnePremiseFrontier
        redex.quantifierApplication tree) :
      G2nnfExchangeBodyQuantifierPosition redex
        (.quantifierFrontier frontier)
  | underLowerOne {targetRule : G2nnfRuleCore L}
      (lineage : G2nnfLowerRuleDescendant redex targetRule)
      (hAdmit : targetRule.BareAtomicAxiom)
      (hPrem : (targetRule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions targetRule)
      (sub : G2nnfProofTree hL
        ((targetRule.premises)[0]'(by omega)).1
        ((targetRule.premises)[0]'(by omega)).2)
      (body : G2nnfExchangeBody redex sub)
      (position : G2nnfExchangeBodyQuantifierPosition redex body) :
      G2nnfExchangeBodyQuantifierPosition redex
        (.lowerOne lineage hAdmit hPrem hSC sub body)
  | underLowerTwoLeft {targetRule : G2nnfRuleCore L}
      (lineage : G2nnfLowerRuleDescendant redex targetRule)
      (hAdmit : targetRule.BareAtomicAxiom)
      (hPrem : (targetRule.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions targetRule)
      (sub1 : G2nnfProofTree hL
        ((targetRule.premises)[0]'(by omega)).1
        ((targetRule.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((targetRule.premises)[1]'(by omega)).1
        ((targetRule.premises)[1]'(by omega)).2)
      (body1 : G2nnfExchangeBody redex sub1)
      (body2 : G2nnfExchangeBody redex sub2)
      (position : G2nnfExchangeBodyQuantifierPosition redex body1) :
      G2nnfExchangeBodyQuantifierPosition redex
        (.lowerTwo lineage hAdmit hPrem hSC
          sub1 sub2 body1 body2)
  | underLowerTwoRight {targetRule : G2nnfRuleCore L}
      (lineage : G2nnfLowerRuleDescendant redex targetRule)
      (hAdmit : targetRule.BareAtomicAxiom)
      (hPrem : (targetRule.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions targetRule)
      (sub1 : G2nnfProofTree hL
        ((targetRule.premises)[0]'(by omega)).1
        ((targetRule.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((targetRule.premises)[1]'(by omega)).1
        ((targetRule.premises)[1]'(by omega)).2)
      (body1 : G2nnfExchangeBody redex sub1)
      (body2 : G2nnfExchangeBody redex sub2)
      (position : G2nnfExchangeBodyQuantifierPosition redex body2) :
      G2nnfExchangeBodyQuantifierPosition redex
        (.lowerTwo lineage hAdmit hPrem hSC
          sub1 sub2 body1 body2)
  | underWeakening {targetRule : G2nnfRuleCore L}
      (allowed : G2nnfExchangeWeakening redex targetRule)
      (hAdmit : targetRule.BareAtomicAxiom)
      (hPrem : (targetRule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions targetRule)
      (sub : G2nnfProofTree hL
        ((targetRule.premises)[0]'(by omega)).1
        ((targetRule.premises)[0]'(by omega)).2)
      (body : G2nnfExchangeBody redex sub)
      (position : G2nnfExchangeBodyQuantifierPosition redex body) :
      G2nnfExchangeBodyQuantifierPosition redex
        (.weakening allowed hAdmit hPrem hSC sub body)

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- A position of a lower-schema node generated by `G2nnfExchangeBody`
itself.  The `here` constructors stop only at `.lowerOne` or `.lowerTwo`;
recursive constructors cross only generated lower/weakening nodes.  There is
intentionally no constructor which descends through either frontier, so a
stale application inside a reused source subtree cannot be selected. -/
inductive G2nnfExchangeBodyLowerPosition {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfPermutableOccurrence T R₁ R₂) :
    (targetRule : G2nnfRuleCore L) →
    G2nnfLowerRuleDescendant redex targetRule →
    {Γ Δ : LCS.Finset (FormulaN L)} →
    {tree : G2nnfProofTree hL Γ Δ} →
    G2nnfExchangeBody redex tree → Type where
  | hereOne {targetRule : G2nnfRuleCore L}
      (lineage : G2nnfLowerRuleDescendant redex targetRule)
      (hAdmit : targetRule.BareAtomicAxiom)
      (hPrem : (targetRule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions targetRule)
      (sub : G2nnfProofTree hL
        ((targetRule.premises)[0]'(by omega)).1
        ((targetRule.premises)[0]'(by omega)).2)
      (body : G2nnfExchangeBody redex sub)
      (quantifierPosition :
        G2nnfExchangeBodyQuantifierPosition redex body) :
      G2nnfExchangeBodyLowerPosition redex targetRule lineage
        (.lowerOne lineage hAdmit hPrem hSC sub body)
  | hereTwoLeft {targetRule : G2nnfRuleCore L}
      (lineage : G2nnfLowerRuleDescendant redex targetRule)
      (hAdmit : targetRule.BareAtomicAxiom)
      (hPrem : (targetRule.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions targetRule)
      (sub1 : G2nnfProofTree hL
        ((targetRule.premises)[0]'(by omega)).1
        ((targetRule.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((targetRule.premises)[1]'(by omega)).1
        ((targetRule.premises)[1]'(by omega)).2)
      (body1 : G2nnfExchangeBody redex sub1)
      (body2 : G2nnfExchangeBody redex sub2)
      (quantifierPosition :
        G2nnfExchangeBodyQuantifierPosition redex body1) :
      G2nnfExchangeBodyLowerPosition redex targetRule lineage
        (.lowerTwo lineage hAdmit hPrem hSC
          sub1 sub2 body1 body2)
  | hereTwoRight {targetRule : G2nnfRuleCore L}
      (lineage : G2nnfLowerRuleDescendant redex targetRule)
      (hAdmit : targetRule.BareAtomicAxiom)
      (hPrem : (targetRule.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions targetRule)
      (sub1 : G2nnfProofTree hL
        ((targetRule.premises)[0]'(by omega)).1
        ((targetRule.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((targetRule.premises)[1]'(by omega)).1
        ((targetRule.premises)[1]'(by omega)).2)
      (body1 : G2nnfExchangeBody redex sub1)
      (body2 : G2nnfExchangeBody redex sub2)
      (quantifierPosition :
        G2nnfExchangeBodyQuantifierPosition redex body2) :
      G2nnfExchangeBodyLowerPosition redex targetRule lineage
        (.lowerTwo lineage hAdmit hPrem hSC
          sub1 sub2 body1 body2)
  | underLowerOne {targetRule outerRule : G2nnfRuleCore L}
      {lineage : G2nnfLowerRuleDescendant redex targetRule}
      (outerLineage : G2nnfLowerRuleDescendant redex outerRule)
      (hAdmit : outerRule.BareAtomicAxiom)
      (hPrem : (outerRule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions outerRule)
      (sub : G2nnfProofTree hL
        ((outerRule.premises)[0]'(by omega)).1
        ((outerRule.premises)[0]'(by omega)).2)
      (body : G2nnfExchangeBody redex sub)
      (position :
        G2nnfExchangeBodyLowerPosition redex targetRule lineage body) :
      G2nnfExchangeBodyLowerPosition redex targetRule lineage
        (.lowerOne outerLineage hAdmit hPrem hSC sub body)
  | underLowerTwoLeft {targetRule outerRule : G2nnfRuleCore L}
      {lineage : G2nnfLowerRuleDescendant redex targetRule}
      (outerLineage : G2nnfLowerRuleDescendant redex outerRule)
      (hAdmit : outerRule.BareAtomicAxiom)
      (hPrem : (outerRule.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions outerRule)
      (sub1 : G2nnfProofTree hL
        ((outerRule.premises)[0]'(by omega)).1
        ((outerRule.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((outerRule.premises)[1]'(by omega)).1
        ((outerRule.premises)[1]'(by omega)).2)
      (body1 : G2nnfExchangeBody redex sub1)
      (body2 : G2nnfExchangeBody redex sub2)
      (position :
        G2nnfExchangeBodyLowerPosition redex targetRule lineage body1) :
      G2nnfExchangeBodyLowerPosition redex targetRule lineage
        (.lowerTwo outerLineage hAdmit hPrem hSC
          sub1 sub2 body1 body2)
  | underLowerTwoRight {targetRule outerRule : G2nnfRuleCore L}
      {lineage : G2nnfLowerRuleDescendant redex targetRule}
      (outerLineage : G2nnfLowerRuleDescendant redex outerRule)
      (hAdmit : outerRule.BareAtomicAxiom)
      (hPrem : (outerRule.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions outerRule)
      (sub1 : G2nnfProofTree hL
        ((outerRule.premises)[0]'(by omega)).1
        ((outerRule.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((outerRule.premises)[1]'(by omega)).1
        ((outerRule.premises)[1]'(by omega)).2)
      (body1 : G2nnfExchangeBody redex sub1)
      (body2 : G2nnfExchangeBody redex sub2)
      (position :
        G2nnfExchangeBodyLowerPosition redex targetRule lineage body2) :
      G2nnfExchangeBodyLowerPosition redex targetRule lineage
        (.lowerTwo outerLineage hAdmit hPrem hSC
          sub1 sub2 body1 body2)
  | underWeakening {targetRule weakeningRule : G2nnfRuleCore L}
      {lineage : G2nnfLowerRuleDescendant redex targetRule}
      (allowed : G2nnfExchangeWeakening redex weakeningRule)
      (hAdmit : weakeningRule.BareAtomicAxiom)
      (hPrem : (weakeningRule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions weakeningRule)
      (sub : G2nnfProofTree hL
        ((weakeningRule.premises)[0]'(by omega)).1
        ((weakeningRule.premises)[0]'(by omega)).2)
      (body : G2nnfExchangeBody redex sub)
      (position :
        G2nnfExchangeBodyLowerPosition redex targetRule lineage body) :
      G2nnfExchangeBodyLowerPosition redex targetRule lineage
        (.weakening allowed hAdmit hPrem hSC sub body)

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

