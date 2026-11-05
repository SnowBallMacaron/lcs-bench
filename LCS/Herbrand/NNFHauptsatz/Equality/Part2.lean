import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.CutElim.Hauptsatz.Equality
import LCS.Herbrand.NNFHauptsatz.Equality.Part1
import Attach
import LCS.Herbrand.NNFHauptsatz.Equality.Part2.ProofsStamp

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality
namespace LCS.Herbrand.NNFHauptsatz.Equality
open LCS.Herbrand.NNFHauptsatz.G2nnfEqRule
open LCS.Herbrand.NNFHauptsatz.G2nnfEqProofTree

/-- Equality lower rules include only the existing propositional/weakening
schemas or a cut on an equation literal, with independent contexts. -/
@[blueprint "chap7__lemma_7_4_3"]
inductive G2nnfEqPermutationLowerView {L : Language} {hL : L.hasEquality = true} :
    G2nnfRuleCore L → Type where
  | ordinary {r : G2nnfRuleCore L} (view : G2nnfPermutationLowerRuleView r)
      (hScope : r.isPropositionalRule ∨ r.isWeakening) :
      G2nnfEqPermutationLowerView (hL := hL) r
  | cut (A : FormulaN L) (Λ Θ Γ Δ : LCS.Finset (FormulaN L))
      (literal : (G2nnfEqRule.base (.cut A Λ Θ Γ Δ) : G2nnfEqRule L hL).isInessentialCut) :
      G2nnfEqPermutationLowerView (.cut A Λ Θ Γ Δ)

/-- Raw contexts of the selected cut premise, or the common contexts of an
ordinary lower rule. No cut branch is identified with its sibling. -/
@[blueprint "chap7__lemma_7_4_3"]
def g2nnfEqSelectedContexts {L : Language} (r : G2nnfRuleCore L)
    (choice : G2nnfPremiseChoice) : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) :=
  match r, choice with
  | .cut _ _ _ Γ Δ, .left => (Γ, Δ)
  | .cut _ Λ Θ _ _, .right => (Λ, Θ)
  | _, _ => g2nnfRuleSideContexts r

/-- One exact eligible equality-calculus occurrence pair, with only
weakening inferences between the selected premise and quantifier node. -/
@[blueprint "chap7__lemma_7_4_3"]
structure G2nnfEqPermutableOccurrence {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfEqProofTree hL Γ Δ) (R₁ R₂ : G2nnfRuleCore L) where
  lowerView : G2nnfEqPermutationLowerView (hL := hL) R₂
  Γprem : LCS.Finset (FormulaN L)
  Δprem : LCS.Finset (FormulaN L)
  selectedPremise : G2nnfEqProofTree hL Γprem Δprem
  lowerApplication : G2nnfEqSelectedPremiseOccurrence T R₂ selectedPremise
  Γquant : LCS.Finset (FormulaN L)
  Δquant : LCS.Finset (FormulaN L)
  quantifierNode : G2nnfEqProofTree hL Γquant Δquant
  quantifierView : G2nnfQuantifierRuleView R₁
  quantifierApplication : G2nnfEqOnePremiseApplication R₁ quantifierNode
  pathFromSelectedPremise : G2nnfEqProofTree.RootToNodePath selectedPremise quantifierNode
  weakeningIntermediates : G2nnfEqWeakeningOnlyPath pathFromSelectedPremise

/-- Generated lower inferences retain the selected ordinary schema, its
focused instance, or exactly the selected equation-literal cut formula. -/
@[blueprint "chap7__lemma_7_4_3"]
def G2nnfEqLowerDescendant {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] {Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfEqProofTree hL Γ Δ} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfEqPermutableOccurrence T R₁ R₂) (target : G2nnfRuleCore L) : Prop :=
  match redex.lowerView with
  | .ordinary view hScope => ∃ Γ Δ,
      target = view.withContexts Γ Δ ∨
      target = view.instantiateSelectedOfPropositional hScope redex.quantifierView redex.lowerApplication.choice Γ Δ
  | .cut A _ _ _ _ _ => ∃ Λ Θ Γ Δ, target = .cut A Λ Θ Γ Δ

/-- A moved quantifier retains its exact occurrence in a context formula,
or lifts it through the selected propositional side formula. -/
@[blueprint "chap7__lemma_7_4_3"]
inductive G2nnfEqQuantifierDescendant {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] {Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfEqProofTree hL Γ Δ} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfEqPermutableOccurrence T R₁ R₂) : G2nnfRuleCore L → Type where
  | context
      (hMem : Membership.mem
        (redex.quantifierView.side.context
          (g2nnfEqSelectedContexts R₂ redex.lowerApplication.choice).1
          (g2nnfEqSelectedContexts R₂ redex.lowerApplication.choice).2)
        redex.quantifierView.principal)
      (Γ Δ : LCS.Finset (FormulaN L)) :
      G2nnfEqQuantifierDescendant redex
        (redex.quantifierView.reprincipalAt redex.quantifierView.occurrence rfl Γ Δ)
  | focused (lower : G2nnfPermutationLowerRuleView R₂)
      (hFocus : lower.selectedFocus redex.lowerApplication.choice =
        some (redex.quantifierView.side, redex.quantifierView.principal))
      (A : FormulaN L)
      (hPrincipal : lower.principal = some (redex.quantifierView.side, A))
      (lifted : G2nnfPermutationLowerRuleView.G2nnfFocusedOccurrenceLift
        A redex.quantifierView.occurrence.selected)
      (hLift : lower.liftFocusedOccurrence redex.lowerApplication.choice hFocus hPrincipal
        redex.quantifierView.occurrence = some lifted)
      (Γ Δ : LCS.Finset (FormulaN L)) :
      G2nnfEqQuantifierDescendant redex
        (redex.quantifierView.reprincipalAt lifted.occurrence lifted.selected_eq Γ Δ)

/-- Local equality fragment body; only exact source frontiers, lower descendants and weakenings. -/
@[blueprint "chap7__lemma_7_4_3"]
inductive G2nnfEqPermutationBody {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfEqProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfEqPermutableOccurrence T R₁ R₂) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfEqProofTree hL Γ Δ → Nat → Nat → Nat → Type where
  | quantifierFrontier {Γ Δ} {tree : G2nnfEqProofTree hL Γ Δ}
      (frontier : G2nnfEqOnePremiseFrontier redex.quantifierApplication tree) :
      G2nnfEqPermutationBody redex tree 1 0 0
  | otherFrontier {Γ Δ} {tree : G2nnfEqProofTree hL Γ Δ}
      (frontier : G2nnfEqOtherPremiseFrontier redex.lowerApplication tree) :
      G2nnfEqPermutationBody redex tree 0 1 0
  | lowerOne {rule : G2nnfRuleCore L} {q o b : Nat}
      (lineage : G2nnfEqLowerDescendant redex rule)
      (hAdmit : True) (hPrem : rule.premises.length = 1)
      (hSC : rule.SideConditions)
      (sub : G2nnfEqProofTree hL
        (rule.premises[0]'(by omega)).1 (rule.premises[0]'(by omega)).2)
      (body : G2nnfEqPermutationBody redex sub q o b) :
      G2nnfEqPermutationBody redex (.onePremise rule hAdmit hPrem hSC sub)
        q o (b + q)
  | lowerTwo {rule : G2nnfRuleCore L} {q₁ q₂ o₁ o₂ b₁ b₂ : Nat}
      (lineage : G2nnfEqLowerDescendant redex rule)
      (hAdmit : True) (hPrem : rule.premises.length = 2)
      (hSC : rule.SideConditions)
      (sub₁ : G2nnfEqProofTree hL
        (rule.premises[0]'(by omega)).1 (rule.premises[0]'(by omega)).2)
      (sub₂ : G2nnfEqProofTree hL
        (rule.premises[1]'(by omega)).1 (rule.premises[1]'(by omega)).2)
      (body₁ : G2nnfEqPermutationBody redex sub₁ q₁ o₁ b₁)
      (body₂ : G2nnfEqPermutationBody redex sub₂ q₂ o₂ b₂) :
      G2nnfEqPermutationBody redex (.twoPremise rule hAdmit hPrem hSC sub₁ sub₂)
        (q₁ + q₂) (o₁ + o₂) (b₁ + b₂ + q₁ + q₂)
  | weakening {rule : G2nnfRuleCore L} {q o b : Nat}
      (hWeak : rule.isWeakening)
      (hAdmit : True) (hPrem : rule.premises.length = 1)
      (hSC : rule.SideConditions)
      (sub : G2nnfEqProofTree hL
        (rule.premises[0]'(by omega)).1 (rule.premises[0]'(by omega)).2)
      (body : G2nnfEqPermutationBody redex sub q o b) :
      G2nnfEqPermutationBody redex (.onePremise rule hAdmit hPrem hSC sub) q o b

/-- A local Q with the source frontiers fixed. Exactly one moved quantifier
lies below all generated lower-schema copies, with only weakenings below it.
At least one lower descendant lies on the path to the source quantifier
premise. The other premise is retained, with duplication permitted. Unlike
an adjacent bounded exchange, Q admits an arbitrary weakening section. -/
@[blueprint "chap7__lemma_7_4_3"]
inductive G2nnfEqPermutationFragment {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T : G2nnfEqProofTree hL Γroot Δroot} {R₁ R₂ : G2nnfRuleCore L}
    (redex : G2nnfEqPermutableOccurrence T R₁ R₂) :
    {Γ Δ : LCS.Finset (FormulaN L)} → G2nnfEqProofTree hL Γ Δ → Type where
  | quantifier {Γ Δ Γbody Δbody : LCS.Finset (FormulaN L)}
      {tree : G2nnfEqProofTree hL Γ Δ}
      (targetRule : G2nnfRuleCore L)
      (correspondence : G2nnfEqQuantifierDescendant redex targetRule)
      (application : G2nnfEqOnePremiseApplication targetRule tree)
      (body : G2nnfEqProofTree hL Γbody Δbody)
      (premise : G2nnfEqOnePremiseFrontier application body)
      (otherCount lowerCount : Nat)
      (shape : G2nnfEqPermutationBody redex body 1 otherCount lowerCount)
      (usesOther : redex.lowerApplication.otherPremiseCount ≤ otherCount)
      (reversesOrder : 0 < lowerCount) :
      G2nnfEqPermutationFragment redex tree
  | weakening {rule : G2nnfRuleCore L}
      (hWeak : rule.isWeakening)
      (hAdmit : True) (hPrem : rule.premises.length = 1)
      (hSC : rule.SideConditions)
      (sub : G2nnfEqProofTree hL
        (rule.premises[0]'(by omega)).1 (rule.premises[0]'(by omega)).2)
      (fragment : G2nnfEqPermutationFragment redex sub) :
      G2nnfEqPermutationFragment redex (.onePremise rule hAdmit hPrem hSC sub)

-- ===================================================================
-- Lemma 7.4.3 (required def): CanPermuteWith_G2nnfEq
-- ===================================================================

/-- Lemma 7.4.3 (required def): Every eligible exact inference pair admits
its own local Q, retaining the selected quantifier premise, the other lower
premise when present, and the lower conclusion. Only Q's generated nodes are
restricted to the moved quantifier, lower-schema copies and weakenings.
Reused frontier proofs and the outside continuation are unrestricted. -/
@[blueprint "chap7__lemma_7_4_3"]
def CanPermuteWith_G2nnfEq {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (R₁ R₂ : G2nnfEqRule L hL)
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfEqProofTree hL Γ Δ) : Prop :=
  match R₁, R₂ with
  | .base r₁, .base r₂ =>
    ∀ redex : G2nnfEqPermutableOccurrence T r₁ r₂,
      ∃ Q : G2nnfEqProofTree hL r₂.conclusion.1 r₂.conclusion.2,
        Nonempty (G2nnfEqPermutationFragment redex Q)
  | _, _ => True

-- ===================================================================
-- Theorem 7.4.2 (helper): occurrence-indexed lower paths
-- ===================================================================

/-- Theorem 7.4.2 (companion def): Every inference strictly below the
target occurrence selected by `path` is a G2nnf= quantifier-for-subformulae
inference.  The target node's own inference belongs to the upper subtree. -/
@[blueprint "chap7__theorem_7_4_2"]
def AllRulesQuantifierOnPath_G2nnfEq {L : Language}
    {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL Γroot Δroot}
    {node : G2nnfEqProofTree hL Γnode Δnode}
    (path : G2nnfEqProofTree.RootToNodePath root node) : Prop :=
  match path with
  | .root _ => True
  | .onePremise rule _ _ _ _ subpath =>
    rule.isQuantifierRule ∧ AllRulesQuantifierOnPath_G2nnfEq subpath
  | .leftPremise rule _ _ _ _ _ subpath =>
    rule.isQuantifierRule ∧ AllRulesQuantifierOnPath_G2nnfEq subpath
  | .rightPremise rule _ _ _ _ _ subpath =>
    rule.isQuantifierRule ∧ AllRulesQuantifierOnPath_G2nnfEq subpath



-- ===================================================================
-- Theorem 7.4.2 (companion structure): IsMidsequent_G2nnfEq
-- ===================================================================

/-- Theorem 7.4.2 (companion structure): A sequent `mid` is the midsequent
of `T` when it is quantifier-free and one occurrence-identified node supplies
both the upper subtree (propositional, weakening, or inessential-cut rules)
and the lower quantifier-only root-to-node path.  Bundling the exact path with
the node prevents equal sequents at different occurrences from being spliced.
-/
@[blueprint "chap7__theorem_7_4_2"]
structure IsMidsequent_G2nnfEq {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfEqProofTree hL Γ Δ)
    (mid : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) :
    Prop where
  /-- Every formula in the midsequent antecedent and succedent is
      quantifier-free -/
  midIsQuantifierFree :
    (∀ A, Membership.mem mid.1 A →
      FirstOrder.SemanticsN.isQuantifierFree A) ∧
    (∀ A, Membership.mem mid.2 A →
      FirstOrder.SemanticsN.isQuantifierFree A)
  /-- One occurrence supplies the target subtree, its exact position in `T`,
      the upper-rule condition, and the lower-path condition together. -/
  midOccurrence :
    ∃ occurrence : G2nnfEqProofTree.NodeOccurrence T mid.1 mid.2,
      allRulesSatisfy (fun rule =>
        rule.isPropositionalOnly ∨ rule.isWeakening ∨
        rule.isInessentialCut) occurrence.node ∧
      AllRulesQuantifierOnPath_G2nnfEq occurrence.path





-- ===================================================================
-- Theorem 7.4.2 (companion def): allFormulaeNNF
-- ===================================================================

/-- Theorem 7.4.2 (companion def): Predicate asserting that every formula in both the antecedent and succedent of an `LCS.Finset`-based sequent is in NNF (FormulaN.isNNF holds for each formula). This is the hypothesis that all formulae in Gamma -> Delta are in negation normal form. -/
@[blueprint "chap7__theorem_7_4_2"]
def allFormulaeNNF {L : Language}
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) :
    Prop :=
  (∀ A, Membership.mem seq.1 A → FormulaN.isNNF A) ∧
  (∀ A, Membership.mem seq.2 A → FormulaN.isNNF A)

-- ===================================================================
-- Theorem 7.4.2 (companion def): G1nnfEqProvable_Set
-- ===================================================================

/-- Theorem 7.4.2 (companion def): Predicate asserting existence of an indexed G1nnf= proof tree concluding with the given `LCS.Finset`-based sequent. Under the indexed API, G1nnf= provability is `Nonempty (G1nnfEqProofTree Γ Δ)`. Mirrors `G1nnfProvableSet` from Layer 3a for the equality system. -/
@[blueprint "chap7__theorem_7_4_2"]
def G1nnfEqProvable_Set {L : Language} (hL : L.hasEquality = true)
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) :
    Prop :=
  Nonempty (G1nnfEqProofTree hL seq.1 seq.2)

-- ===================================================================
-- Theorem 7.4.2 (companion def): proofMeasureM_G2nnfEq
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 7.4.2 (companion def): The sum of m(R) over all quantifier inferences R in the G2nnf= proof tree T, where m(R) counts the number of propositional inferences and inessential cuts on the path from R to the root. This is one component of the lexicographic measure (proofMeasureM, proofMeasureN) used for the induction in Theorem 7.4.2. When proofMeasureM > 0, there exists a quantifier rule above a propositional rule or inessential cut that can be permuted. -/
def proofMeasureM_G2nnfEq {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfEqProofTree hL Γ Δ → Nat
  | _, _, .leaf _ _ hOpen _ _ => hOpen.elim
  | _, _, .extraAxiom _ _ _ _ _ => 0
  | _, _, .axiom_ _ _ _ _ => 0
  | _, _, .onePremise rule _ _ _ sub =>
    if rule.isQuantifierRuleBool then
      proofMeasureM_G2nnfEq sub
    else
      proofMeasureM_G2nnfEq sub +
        countQuantifierRulesBelow sub
  | _, _, .twoPremise rule _ _ _ sub1 sub2 =>
    if rule.isQuantifierRuleBool then
      proofMeasureM_G2nnfEq sub1 +
      proofMeasureM_G2nnfEq sub2
    else
      proofMeasureM_G2nnfEq sub1 +
      proofMeasureM_G2nnfEq sub2 +
        (countQuantifierRulesBelow sub1 +
         countQuantifierRulesBelow sub2)
where
  /-- Helper: count the number of quantifier rule nodes in a
      G2nnfEq proof tree. -/
  countQuantifierRulesBelow {L : Language} {hL : L.hasEquality = true}
      [DecidableEq (FormulaN L)] :
      {Γ Δ : LCS.Finset (FormulaN L)} →
      G2nnfEqProofTree hL Γ Δ → Nat
    | _, _, .leaf _ _ hOpen _ _ => hOpen.elim
    | _, _, .extraAxiom _ _ _ _ _ => 0
    | _, _, .axiom_ _ _ _ _ => 0
    | _, _, .onePremise rule _ _ _ sub =>
      (if rule.isQuantifierRuleBool then 1 else 0) +
      countQuantifierRulesBelow sub
    | _, _, .twoPremise rule _ _ _ sub1 sub2 =>
      (if rule.isQuantifierRuleBool then 1 else 0) +
      countQuantifierRulesBelow sub1 +
      countQuantifierRulesBelow sub2

-- ===================================================================
-- Theorem 7.4.2 (companion def): proofMeasureN_G2nnfEq
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 7.4.2 (companion def): The sum of n(R) over all quantifier inferences R in the G2nnf= proof tree T, where n(R) counts the number of weakening inferences on the path from R to the root. This is the second component of the lexicographic measure. When proofMeasureM = 0 and proofMeasureN > 0, there exists a quantifier rule above a weakening that can be permuted. -/
def proofMeasureN_G2nnfEq {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfEqProofTree hL Γ Δ → Nat
  | _, _, .leaf _ _ hOpen _ _ => hOpen.elim
  | _, _, .extraAxiom _ _ _ _ _ => 0
  | _, _, .axiom_ _ _ _ _ => 0
  | _, _, .onePremise rule _ _ _ sub =>
    if rule.isQuantifierRuleBool then
      proofMeasureN_G2nnfEq sub
    else
      proofMeasureN_G2nnfEq sub +
        (match rule with
         | .weakLeft _ _ _ => countQuantifierRulesBelow sub
         | .weakRight _ _ _ => countQuantifierRulesBelow sub
         | _ => 0)
  | _, _, .twoPremise _ _ _ _ sub1 sub2 =>
    proofMeasureN_G2nnfEq sub1 +
    proofMeasureN_G2nnfEq sub2
where
  /-- Helper: count the number of quantifier rule nodes in a
      G2nnfEq proof tree. -/
  countQuantifierRulesBelow {L : Language} {hL : L.hasEquality = true}
      [DecidableEq (FormulaN L)] :
      {Γ Δ : LCS.Finset (FormulaN L)} →
      G2nnfEqProofTree hL Γ Δ → Nat
    | _, _, .leaf _ _ hOpen _ _ => hOpen.elim
    | _, _, .extraAxiom _ _ _ _ _ => 0
    | _, _, .axiom_ _ _ _ _ => 0
    | _, _, .onePremise rule _ _ _ sub =>
      (if rule.isQuantifierRuleBool then 1 else 0) +
      countQuantifierRulesBelow sub
    | _, _, .twoPremise rule _ _ _ sub1 sub2 =>
      (if rule.isQuantifierRuleBool then 1 else 0) +
      countQuantifierRulesBelow sub1 +
      countQuantifierRulesBelow sub2

-- ===================================================================
-- Lemma 7.4.3 (propositional part): g2nnfEq_permutability_with_propositional
-- ===================================================================

/-- Lemma 7.4.3 (companion propositional part): Every quantifier rule R_1 of G2nnf= can be permuted with a propositional rule R_2 in a pure-variable proof without essential cuts. This covers the cases where R_2 is a conjunction or disjunction rule from G2nnf (propositional rules shared with G2nnf). The argument parallels the propositional case of Lemma 7.4.2 for the equality-free system, since propositional rules in G2nnf= are identical to those in G2nnf. -/
theorem g2nnfEq_permutability_with_propositional
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfEqProofTree hL Γ Δ)
    (R₁ R₂ : G2nnfEqRule L hL)
    (hPure : IsPureVariableProof_G2nnfEq T)
    (hNEC : T.hasNoEssentialCuts)
    (hQuant : R₁.isQuantifierRule)
    (hPropIC : R₂.isPropositionalOrInessentialCut)
    (hProp : R₂.isPropositionalOnly) :
    CanPermuteWith_G2nnfEq R₁ R₂ T := by
-- BEGIN PROOF
  -- REPAIR(T7-49): proof pending
  sorry

-- ===================================================================
-- Lemma 7.4.3 (inessential cut part): g2nnfEq_permutability_with_inessential_cut
-- ===================================================================

/-- Lemma 7.4.3 (companion inessential cut part): Every quantifier rule R_1 of G2nnf= can be permuted with an inessential cut R_2 in a pure-variable proof without essential cuts. This is the new case not present in Lemma 7.4.2 (the equality-free case): an inessential cut is a cut on an atomic or equality formula (embedded via the `.base (.cut A)` form). The permutation follows the same argument as the cut case in Lemma 7.3.3: the quantifier rule R_1 is moved below the inessential cut using weakenings and exchanges on both branches of the cut, preserving the pure-variable and no-essential-cuts properties. -/
theorem g2nnfEq_permutability_with_inessential_cut
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfEqProofTree hL Γ Δ)
    (R₁ R₂ : G2nnfEqRule L hL)
    (hPure : IsPureVariableProof_G2nnfEq T)
    (hNEC : T.hasNoEssentialCuts)
    (hQuant : R₁.isQuantifierRule)
    (hIC : R₂.isInessentialCut) :
    CanPermuteWith_G2nnfEq R₁ R₂ T := by
-- BEGIN PROOF
  -- REPAIR(T7-49): proof pending
  sorry

-- ===================================================================
-- Lemma 7.4.3 (weakening part): g2nnfEq_permutability_with_weakening
-- ===================================================================

/-- Lemma 7.4.3 (companion weakening part): Every quantifier rule R_1 of G2nnf= can be permuted with a weakening rule R_2 in a pure-variable proof without essential cuts. The proof constructs the permuted tree T' by applying the weakening rule first, then the quantifier rule, with adjustments to the context sets. This case follows from the parallel argument in Lemma 7.4.2. -/
theorem g2nnfEq_permutability_with_weakening
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfEqProofTree hL Γ Δ)
    (R₁ R₂ : G2nnfEqRule L hL)
    (hPure : IsPureVariableProof_G2nnfEq T)
    (hNEC : T.hasNoEssentialCuts)
    (hQuant : R₁.isQuantifierRule)
    (hWeak : R₂.isWeakening) :
    CanPermuteWith_G2nnfEq R₁ R₂ T := by
-- BEGIN PROOF
  -- REPAIR(T7-49): proof pending
  sorry

-- ===================================================================
-- Lemma 7.4.3: g2nnfEq_permutability
-- ===================================================================

/-- Lemma 7.4.3: For every pure-variable proof T in G2nnf= without essential cuts, every quantifier rule R_1 of G2nnf= can be permuted with a propositional rule R_2, an inessential cut R_2, or a weakening R_2. This extends Lemma 7.4.2 (the equality-free case) by adding the case of permuting a quantifier rule with an inessential cut, which follows the argument of Lemma 7.3.3. The propositional rule case and weakening case follow directly from the parallel arguments in Lemma 7.4.2, since the propositional and weakening rules of G2nnf= are identical to those of G2nnf. The proof proceeds by case analysis on the type of R_2: - If R_2 is propositional: use g2nnfEq_permutability_with_propositional - If R_2 is an inessential cut: use g2nnfEq_permutability_with_inessential_cut - If R_2 is a weakening: use g2nnfEq_permutability_with_weakening -/
@[attach_debt, blueprint "chap7__lemma_7_4_3" (main := true)]
theorem g2nnfEq_permutability
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfEqProofTree hL Γ Δ)
    (R₁ R₂ : G2nnfEqRule L hL)
    (hPure : IsPureVariableProof_G2nnfEq T)
    (hNEC : T.hasNoEssentialCuts)
    (hQuant : R₁.isQuantifierRule)
    (hR₂ : R₂.isPropositionalOrInessentialCut ∨
            R₂.isWeakening) :
    CanPermuteWith_G2nnfEq R₁ R₂ T 

-- ===================================================================
-- Theorem 7.4.2: sharpenedHauptsatz_G2nnfEq
-- ===================================================================

/-- Theorem 7.4.2: Given a rectified `LCS.Finset`-based sequent (Gamma, Delta) containing only formulae in NNF, if it is G1nnf=-provable, then there is a pure-variable proof in G2nnf= without essential cuts that contains a midsequent Gamma' -> Delta' satisfying three properties: (1) Every formula in Gamma' -> Delta' is quantifier-free. (2) Every inference rule above Gamma' -> Delta' is either a weakening, a propositional rule, or an inessential cut (but not a quantifier rule). (3) Every inference rule below Gamma' -> Delta' is a quantifier rule. Rectification is the standing assumption at the start of §7.4 and is enforced at every G2nnf= proof node. The free/bound naming convention is required on the end/input sequent only, through finsetCrossNoFreeBound. Under the indexed `G2nnfEqProofTree Γ Δ` API, the conclusion is baked into the type, so no `T.conclusion = seq` or `T.WellFormed` conjunct is needed. The proof is essentially identical to the proof of Theorem 7.4.1 (sharpenedHauptsatz_G2nnf), but uses Lemma 7.4.3 (g2nnfEq_permutability) instead of Lemma 7.4.2. Lexicographic induction on (proofMeasureM_G2nnfEq T, proofMeasureN_G2nnfEq T). Base case: when m=0 and n=0, all propositional/weakening/ inessential-cut inferences are above all quantifier inferences; the midsequent is extracted from the premise of the highest quantifier inference. Inductive case 1 (m>0): find a quantifier rule above a propositional rule or inessential cut and permute them using Lemma 7.4.3. Inductive case 2 (m=0, n>0): find a quantifier rule above a weakening and permute them using Lemma 7.4.3. -/
@[attach_debt, blueprint "chap7__theorem_7_4_2" (main := true)]
theorem sharpenedHauptsatz_G2nnfEq {L : Language} (hL : L.hasEquality = true)
    [DecidableEq (FormulaN L)]
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L))
    (hAllNNF : allFormulaeNNF seq)
    (hRect : AllRectified seq)
    (hCross : finsetCrossNoFreeBound seq.1 seq.2)
    (hProv : G1nnfEqProvable_Set hL seq) :
    ∃ (T : G2nnfEqProofTree hL seq.1 seq.2)
      (mid : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)),
      IsPureVariableProof_G2nnfEq T ∧
      T.hasNoEssentialCuts ∧
      IsMidsequent_G2nnfEq T mid 



/-- Definition 7.4.4 (soundness, provability form): existence of a legal
G2nnf= proof implies validity in identity semantics. -/
@[blueprint "chap7__definition_7_4_4" (main := true)]
theorem g2nnfEq_provable_implies_valid {L : Language} (hL : L.hasEquality = true)
    [DecidableEq (FormulaN L)] (Γ Δ : LCS.Finset (FormulaN L)) :
    g2nnfEqProvable hL Γ Δ → Soundness.setSequentValid Γ Δ 

end LCS.Herbrand.NNFHauptsatz.Equality
end

