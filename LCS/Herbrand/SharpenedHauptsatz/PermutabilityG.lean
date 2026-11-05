import LCS.Herbrand.SharpenedHauptsatz.Permutability
import LCS.Herbrand.SharpenedHauptsatz.PermutabilityG.ProofsStamp

/-! # Permutability of inferences in G and G=

Definition 7.3.2 for the G and G= proof trees of Definition 7.3.1.
The two diagram cases preserve the ordered premise trees and outside continuation.
Neither calculus has structural inference rules, so intermediate and additional
structural inferences are absent.
-/

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Equality
open LCS.Herbrand.SharpenedHauptsatz

namespace LCS.Herbrand.SharpenedHauptsatz.Permutability

/-- Definition 7.3.2: An indexed one- or two-premise G inference. -/
@[blueprint "chap7__definition_7_3_2"]
inductive AnyGStep (L : Language) : Type where
  | one {prem conc : Sequent L} (rule : GentzenStep1Ext prem conc) : AnyGStep L
  | two {prem1 prem2 conc : Sequent L}
      (rule : GentzenStep2Ext prem1 prem2 conc) : AnyGStep L

/-- Definition 7.3.2: The ordered premises of a G inference. -/
@[blueprint "chap7__definition_7_3_2"]
def AnyGStep.premises {L : Language} : AnyGStep L → List (Sequent L)
  | .one (prem := p) _ => [p]
  | .two (prem1 := p) (prem2 := q) _ => [p, q]

/-- Definition 7.3.2: G has no structural inference rules. -/
@[blueprint "chap7__definition_7_3_2"]
def AnyGStep.isStructural {L : Language} (_ : AnyGStep L) : Prop := False

/-- Definition 7.3.2: The G inference schema, independent of side contexts. -/
@[blueprint "chap7__definition_7_3_2"]
def AnyGStep.schemaKind {L : Language} : AnyGStep L → Nat
  | .one r => (gStep1ReplacementData r).1
  | .two r => (gStep2ReplacementData r).1

/-- Definition 7.3.2: Active formulae, instantiating terms and variable annotations
retained when an inference is permuted. Side contexts may change. -/
@[blueprint "chap7__definition_7_3_2"]
def AnyGStep.permutationPayload {L : Language} :
    AnyGStep L → List (FormulaN L) × List (Term L) × List Nat
  | .one rule => match rule with
    | .conjLeft _ _ _ A B => ([A, B], [], [])
    | .disjRight _ _ _ A B => ([A, B], [], [])
    | .implRight _ _ _ A B => ([A, B], [], [])
    | .negLeft _ _ _ A => ([A], [], [])
    | .negRight _ _ _ A => ([A], [], [])
    | .allLeft ts _ _ _ x A _ _ => ([A], ts, [x])
    | .exRight ts _ _ _ x A _ _ => ([A], ts, [x])
    | .allRight y _ _ _ x A _ _ => ([A], [], [y, x])
    | .exLeft y _ _ _ x A _ _ => ([A], [], [y, x])
  | .two rule => match rule with
    | .conjRight _ _ _ A B => ([A, B], [], [])
    | .disjLeft _ _ _ A B => ([A, B], [], [])
    | .implLeft _ _ _ A B => ([A, B], [], [])

/-- Definition 7.3.2 (companion): The actual subtree at an address in the fixed proof. Unary and left premises use edge 0; right premises use edge 1. Invalid addresses return none. -/
@[blueprint "chap7__definition_7_3_2"]
def gSubtreeAt {L : Language} :
    {s : Sequent L} → GProofTreeExt s → List Nat → Option (Σ c : Sequent L, GProofTreeExt c)
  | s, t, [] => some ⟨s, t⟩
  | _, .onePremise _ t, 0 :: p => gSubtreeAt t p
  | _, .twoPremise _ t _, 0 :: p => gSubtreeAt t p
  | _, .twoPremise _ _ t, 1 :: p => gSubtreeAt t p
  | _, _, _ => none

/-- Definition 7.3.2 (companion): The indexed inference applied at an actual node. Axiom leaves, have no one- or two-premise inference. -/
@[blueprint "chap7__definition_7_3_2"]
def gInferenceAt {L : Language} {s : Sequent L}
    (T : GProofTreeExt s) (address : List Nat) : Option (AnyGStep L) :=
  match gSubtreeAt T address with
  | none => none
  | some ⟨_, t⟩ => match t with
    | .axiom_ _ _ => none
    | .onePremise rule _ => some (.one rule)
    | .twoPremise rule _ _ => some (.two rule)

/-- Definition 7.3.2 (companion): An inference occurrence in a fixed proof, identified by its address. The lookup certificate ties its indexed rule to that node; identical rules at different addresses are distinct occurrences. -/
@[blueprint "chap7__definition_7_3_2"]
structure GInferenceOccurrence {L : Language} {s : Sequent L} (T : GProofTreeExt s) where
  address : List Nat
  rule : AnyGStep L
  atAddress : gInferenceAt T address = some rule

/-- Definition 7.3.2 (companion): One-premise boundary at the selected inference: the actual premise proof, its sequent, and the conclusion sequent are tied to the ambient proof by address lookup. -/
@[blueprint "chap7__definition_7_3_2"]
structure GOnePremiseBoundary {L : Language} {s : Sequent L}
    {T : GProofTreeExt s} (o : GInferenceOccurrence T) where
  premise : Sequent L
  conclusion : Sequent L
  rule : GentzenStep1Ext premise conclusion
  tree : GProofTreeExt premise
  atAddress : gSubtreeAt T o.address = some ⟨conclusion, .onePremise rule tree⟩

/-- Definition 7.3.2 (companion): Two-premise boundary at the selected inference, retaining both actual premise proofs in their left/right order and their indexed sequents. -/
@[blueprint "chap7__definition_7_3_2"]
structure GTwoPremiseBoundary {L : Language} {s : Sequent L}
    {T : GProofTreeExt s} (o : GInferenceOccurrence T) where
  leftSequent : Sequent L
  rightSequent : Sequent L
  conclusion : Sequent L
  rule : GentzenStep2Ext leftSequent rightSequent conclusion
  leftTree : GProofTreeExt leftSequent
  rightTree : GProofTreeExt rightSequent
  atAddress : gSubtreeAt T o.address =
    some ⟨conclusion, .twoPremise rule leftTree rightTree⟩

/-- Definition 7.3.2 (companion): Ancestry of the two specified inference occurrences in the fixed proof. This tests addresses alone, independently of intermediate rule kinds. -/
@[blueprint "chap7__definition_7_3_2"]
def isDescendantOfPremiseG {L : Language} {s : Sequent L} {T : GProofTreeExt s}
    (R₁ R₂ : GInferenceOccurrence T) : Prop :=
  premiseAddressDescendant R₁.address R₂.address

/-- Definition 7.3.2 (companion): The selected upper occurrence is not in any premise subtree of the selected lower occurrence. A nonstructural intermediate does not erase ancestry. -/
@[blueprint "chap7__definition_7_3_2"]
def notDescendantOfPremiseG {L : Language} {s : Sequent L} {T : GProofTreeExt s}
    (R₁ R₂ : GInferenceOccurrence T) : Prop :=
  ¬ isDescendantOfPremiseG R₁ R₂

/-- Definition 7.3.2 (companion): The selected upper inference lies above the selected lower inference, with only structural rules strictly between their addresses. Off-path branches are unrestricted. -/
@[blueprint "chap7__definition_7_3_2"]
def descendsWithStructuralIntermediatesG {L : Language} {s : Sequent L} {T : GProofTreeExt s}
    (R₁ R₂ : GInferenceOccurrence T) : Prop :=
  isDescendantOfPremiseG R₁ R₂ ∧
  ∀ middle : GInferenceOccurrence T,
    premiseAddressDescendant middle.address R₂.address →
    premiseAddressDescendant R₁.address middle.address → middle.rule.isStructural

/-- Definition 7.3.2 (companion): Source boundaries of the selected local segment. The upper inference has one premise; the lower has one or two ordered premises. All boundary trees are actual subtrees of the same ambient proof. The chosen edge and tail identify the branch containing the upper inference. -/
@[blueprint "chap7__definition_7_3_2"]
structure GPermutationBoundary {L : Language} {s : Sequent L}
    {T : GProofTreeExt s} (upper lower : GInferenceOccurrence T) where
  upperBoundary : GOnePremiseBoundary upper
  lowerBoundary : Sum (GOnePremiseBoundary lower) (GTwoPremiseBoundary lower)
  branch : Nat
  branchInRange : branch < lower.rule.premises.length
  tail : List Nat
  upperAt : upper.address = lower.address ++ branch :: tail
  structuralPath : descendsWithStructuralIntermediatesG upper lower

/-- Definition 7.3.2 (companion): The unchanged outside continuation T₀, with one sequent-indexed hole. Every rule on its spine and every off-spine proof is retained as data. -/
@[blueprint "chap7__definition_7_3_2"]
inductive GProofContext {L : Language} (hole : Sequent L) : Sequent L → Type where
  | hole : GProofContext hole hole
  | one {p c} (rule : GentzenStep1Ext p c) (rest : GProofContext hole p) : GProofContext hole c
  | left {p q c} (rule : GentzenStep2Ext p q c) (rest : GProofContext hole p)
      (sibling : GProofTreeExt q) : GProofContext hole c
  | right {p q c} (rule : GentzenStep2Ext p q c) (sibling : GProofTreeExt p)
      (rest : GProofContext hole q) : GProofContext hole c

/-- Definition 7.3.2 (companion): Reinsert a proof of S₀ into the unchanged outside continuation. -/
@[blueprint "chap7__definition_7_3_2"]
def GProofContext.plug {L : Language} {hole : Sequent L} :
    {s : Sequent L} → GProofContext hole s → GProofTreeExt hole → GProofTreeExt s
  | _, .hole, t => t
  | _, .one rule rest, t => .onePremise rule (rest.plug t)
  | _, .left rule rest sibling, t => .twoPremise rule (rest.plug t) sibling
  | _, .right rule sibling rest, t => .twoPremise rule sibling (rest.plug t)

/-- Definition 7.3.2 (companion): The address of the selected local segment in its outside continuation. -/
@[blueprint "chap7__definition_7_3_2"]
def GProofContext.address {L : Language} {hole : Sequent L} :
    {s : Sequent L} → GProofContext hole s → List Nat
  | _, .hole => []
  | _, .one _ rest => 0 :: rest.address
  | _, .left _ rest _ => 0 :: rest.address
  | _, .right _ _ rest => 1 :: rest.address

/-- Definition 7.3.2 (companion): The local Q as a sequent-indexed open fragment. Its only leaves reference the supplied premise proof trees; it has no axiom constructor. -/
@[blueprint "chap7__definition_7_3_2"]
inductive GLocalFragment {L : Language}
    (inputs : List (Σ c : Sequent L, GProofTreeExt c)) : Sequent L → Type where
  | input (i : Fin inputs.length) : GLocalFragment inputs (inputs.get i).1
  | one {p c} (rule : GentzenStep1Ext p c) (sub : GLocalFragment inputs p) : GLocalFragment inputs c
  | two {p q c} (rule : GentzenStep2Ext p q c)
      (left : GLocalFragment inputs p) (right : GLocalFragment inputs q) : GLocalFragment inputs c

/-- Definition 7.3.2 (companion): Plug the original premise proofs into Q, preserving their proof data exactly. -/
@[blueprint "chap7__definition_7_3_2"]
def GLocalFragment.plug {L : Language} {inputs : List (Σ c : Sequent L, GProofTreeExt c)} :
    {s : Sequent L} → GLocalFragment inputs s → GProofTreeExt s
  | _, .input i => (inputs.get i).2
  | _, .one rule sub => .onePremise rule sub.plug
  | _, .two rule left right => .twoPremise rule left.plug right.plug

/-- Definition 7.3.2 (companion): The ordered input occurrences in Q. Equality with the full index range requires every supplied premise tree exactly once, in source order. -/
@[blueprint "chap7__definition_7_3_2"]
def GLocalFragment.inputOrder {L : Language} {inputs : List (Σ c : Sequent L, GProofTreeExt c)} :
    {s : Sequent L} → GLocalFragment inputs s → List Nat
  | _, .input i => [i.val]
  | _, .one _ sub => sub.inputOrder
  | _, .two _ left right => left.inputOrder ++ right.inputOrder

/-- Definition 7.3.2 (companion): Inference lookup inside Q alone. Input proof trees are boundary leaves, so their internal rules cannot witness either permuted inference or violate the local structural-only condition. -/
@[blueprint "chap7__definition_7_3_2"]
def GLocalFragment.inferenceAt {L : Language} {inputs : List (Σ c : Sequent L, GProofTreeExt c)} :
    {s : Sequent L} → GLocalFragment inputs s → List Nat → Option (AnyGStep L)
  | _, .one rule _, [] => some (.one rule)
  | _, .two rule _ _, [] => some (.two rule)
  | _, .one _ sub, 0 :: p => sub.inferenceAt p
  | _, .two _ left _, 0 :: p => left.inferenceAt p
  | _, .two _ _ right, 1 :: p => right.inferenceAt p
  | _, _, _ => none

/-- Definition 7.3.2 (companion): A local replacement certificate: the source segment reconstructs T through the same T₀; Q has the same S₀, uses precisely the original ordered premise trees, retains both named inferences, reverses their ancestry, and has only structural additional inferences. -/
@[blueprint "chap7__definition_7_3_2"]
structure GLocalReplacement {L : Language} {s c : Sequent L}
    (T : GProofTreeExt s) (rootAddress : List Nat) (source : GProofTreeExt c)
    (inputs : List (Σ p : Sequent L, GProofTreeExt p)) (R₁ R₂ : AnyGStep L) where
  continuation : GProofContext c s
  atAddress : continuation.address = rootAddress
  sourceFixed : continuation.plug source = T
  replacement : GLocalFragment inputs c
  inputOrder : replacement.inputOrder = List.range inputs.length
  firstAddress : List Nat
  secondAddress : List Nat
  firstRule : AnyGStep L
  secondRule : AnyGStep L
  firstAt : replacement.inferenceAt firstAddress = some firstRule
  secondAt : replacement.inferenceAt secondAddress = some secondRule
  firstSchema : firstRule.schemaKind = R₁.schemaKind
  secondSchema : secondRule.schemaKind = R₂.schemaKind
  firstPayload : firstRule.permutationPayload = R₁.permutationPayload
  secondPayload : secondRule.permutationPayload = R₂.permutationPayload
  distinct : firstAddress ≠ secondAddress
  reversed : ¬ premiseAddressDescendant firstAddress secondAddress
  otherStructural : ∀ p rule, replacement.inferenceAt p = some rule →
    p ≠ firstAddress → p ≠ secondAddress → rule.isStructural

/-- Definition 7.3.2 (companion): The resulting proof is computed by plugging Q through exactly the recorded outside continuation. -/
@[blueprint "chap7__definition_7_3_2"]
def GLocalReplacement.result {L : Language} {s c : Sequent L}
    {T : GProofTreeExt s} {rootAddress : List Nat} {source : GProofTreeExt c}
    {inputs : List (Σ p : Sequent L, GProofTreeExt p)} {R₁ R₂ : AnyGStep L}
    (h : GLocalReplacement T rootAddress source inputs R₁ R₂) : GProofTreeExt s :=
  h.continuation.plug h.replacement.plug

/-- Definition 7.3.2 (companion): The one-premise case fixes T₁, S₀ and the selected lower inference before specifying Q and the unchanged outside continuation. -/
@[blueprint "chap7__definition_7_3_2"]
def GOnePremiseLocalReplacement {L : Language} {s : Sequent L} {T : GProofTreeExt s}
    {upper lower : GInferenceOccurrence T} (ub : GOnePremiseBoundary upper) (lb : GOnePremiseBoundary lower) : Type :=
  GLocalReplacement T lower.address (.onePremise lb.rule lb.tree)
    [⟨ub.premise, ub.tree⟩] upper.rule lower.rule

/-- Definition 7.3.2 (companion): The two-premise case preserves the original
left-to-right frontier. On the selected branch its input is the upper rule's
premise tree; the other branch retains the lower rule's entire premise tree. -/
@[blueprint "chap7__definition_7_3_2"]
def GTwoPremiseLocalReplacement {L : Language} {s : Sequent L} {T : GProofTreeExt s}
    {upper lower : GInferenceOccurrence T}
    (ub : GOnePremiseBoundary upper) (lb : GTwoPremiseBoundary lower)
    (rightBranch : Bool) : Type :=
  GLocalReplacement T lower.address (.twoPremise lb.rule lb.leftTree lb.rightTree)
    (if rightBranch then [⟨lb.leftSequent, lb.leftTree⟩, ⟨ub.premise, ub.tree⟩]
     else [⟨ub.premise, ub.tree⟩, ⟨lb.rightSequent, lb.rightTree⟩]) upper.rule lower.rule

/-- Definition 7.3.2: Every selected source boundary admits a local Q with
the same ordered premise proof trees and conclusion S₀, plugged into the exact
same outside continuation T₀. Q retains the two named inference schemas and
their non-context parameters, removes the forbidden ancestry, and contains only
structural additional inferences. The principal/side-formula proviso is a
separate condition in the permutability lemma. -/
@[blueprint "chap7__definition_7_3_2" (main := true)]
def CanPermuteWithG {L : Language} {s : Sequent L} {T : GProofTreeExt s}
    (R₁ R₂ : GInferenceOccurrence T) : Prop :=
  ∀ boundary : GPermutationBoundary R₁ R₂,
    match boundary.lowerBoundary with
    | .inl lb => Nonempty (GOnePremiseLocalReplacement boundary.upperBoundary lb)
    | .inr lb => match boundary.branch with
      | 0 => Nonempty (GTwoPremiseLocalReplacement boundary.upperBoundary lb false)
      | 1 => Nonempty (GTwoPremiseLocalReplacement boundary.upperBoundary lb true)
      | _ => False


/-- Definition 7.3.2: One-premise G= inferences, including all four equality
constructors of GEqProofTree with their original side conditions. -/
@[blueprint "chap7__definition_7_3_2"]
inductive GEqStep1 {L : Language} (hL : L.hasEquality = true) :
    Sequent L → Sequent L → Type where
  | ordinary {p c} (rule : GentzenStep1Ext p c) : GEqStep1 hL p c
  | eqRefl (t : Term L) (Γ Δ : List (FormulaN L)) :
      GEqStep1 hL (Sequent.mk (Γ ++ [FormulaN.eq_ hL t t]) Δ) (Sequent.mk Γ Δ)
  | eqFuncCong (f : L.funSymbols) (ss ts : Fin (L.funArity f) → Term L)
      (Γ Δ : List (FormulaN L)) :
      GEqStep1 hL (Sequent.mk (Γ ++ [eqCongruenceImplFunc L hL f ss ts]) Δ)
        (Sequent.mk Γ Δ)
  | eqPredCong (P : L.predSymbols)
      (ss ts : Fin (L.predArity P) → Term L) (Γ Δ : List (FormulaN L)) :
      GEqStep1 hL (Sequent.mk (Γ ++ [eqCongruenceImplPred L hL P ss ts]) Δ)
        (Sequent.mk Γ Δ)
  | eqGeneral (axioms : List (FormulaN L)) (hne : axioms ≠ [])
      (haxioms : ∀ A ∈ axioms, isEqAxiomInstance hL A) (Γ Δ : List (FormulaN L)) :
      GEqStep1 hL (Sequent.mk (Γ ++ axioms) Δ) (Sequent.mk Γ Δ)

/-- Definition 7.3.2: Apply the recorded one-premise G= inference. -/
@[blueprint "chap7__definition_7_3_2"]
def GEqStep1.apply {L : Language} {hL : L.hasEquality = true} :
    {p c : Sequent L} → GEqStep1 hL p c → GEqProofTree hL p → GEqProofTree hL c
  | _, _, .ordinary r, t => .onePremise r t
  | _, _, .eqRefl t Γ Δ, sub => .eqRefl t Γ Δ sub
  | _, _, .eqFuncCong f ss ts Γ Δ, sub => .eqFuncCong f ss ts Γ Δ sub
  | _, _, .eqPredCong P ss ts Γ Δ, sub => .eqPredCong P ss ts Γ Δ sub
  | _, _, .eqGeneral axs hn ha Γ Δ, sub => .eqGeneral axs hn ha Γ Δ sub

/-- Definition 7.3.2: An indexed G= inference occurrence's rule. -/
@[blueprint "chap7__definition_7_3_2"]
inductive AnyGEqStep {L : Language} (hL : L.hasEquality = true) : Type where
  | one {prem conc : Sequent L} (rule : GEqStep1 hL prem conc) : AnyGEqStep hL
  | two {prem1 prem2 conc : Sequent L}
      (rule : GentzenStep2Ext prem1 prem2 conc) : AnyGEqStep hL

/-- Definition 7.3.2: The ordered premises of a G= inference. -/
@[blueprint "chap7__definition_7_3_2"]
def AnyGEqStep.premises {L : Language} {hL : L.hasEquality = true} :
    AnyGEqStep hL → List (Sequent L)
  | .one (prem := p) _ => [p]
  | .two (prem1 := p) (prem2 := q) _ => [p, q]

/-- Definition 7.3.2: G= has no structural inference rules; equality rules
are not structural rules. -/
@[blueprint "chap7__definition_7_3_2"]
def AnyGEqStep.isStructural {L : Language} {hL : L.hasEquality = true}
    (_ : AnyGEqStep hL) : Prop := False

/-- Definition 7.3.2: G= inference schemas distinguish ordinary and equality rules. -/
@[blueprint "chap7__definition_7_3_2"]
def AnyGEqStep.schemaKind {L : Language} {hL : L.hasEquality = true} :
    AnyGEqStep hL → Nat
  | .one (.ordinary r) => (AnyGStep.one r).schemaKind
  | .one (.eqRefl ..) => 80
  | .one (.eqFuncCong ..) => 81
  | .one (.eqPredCong ..) => 82
  | .one (.eqGeneral ..) => 83
  | .two r => (AnyGStep.two r).schemaKind

/-- Definition 7.3.2: The parameters of a G= inference, excluding side contexts.
Congruence formulae retain the symbol and its two ordered argument families. -/
@[blueprint "chap7__definition_7_3_2"]
def AnyGEqStep.permutationPayload {L : Language} {hL : L.hasEquality = true} :
    AnyGEqStep hL → List (FormulaN L) × List (Term L) × List Nat
  | .one (.ordinary r) => (AnyGStep.one r).permutationPayload
  | .one (.eqRefl t _ _) => ([], [t], [])
  | .one (.eqFuncCong f ss ts _ _) => ([eqCongruenceImplFunc L hL f ss ts], [], [])
  | .one (.eqPredCong P ss ts _ _) => ([eqCongruenceImplPred L hL P ss ts], [], [])
  | .one (.eqGeneral axioms _ _ _ _) => (axioms, [], [])
  | .two r => (AnyGStep.two r).permutationPayload

/-- Definition 7.3.2: Subtree lookup in G=, with an embedded G tree at the
same address as its embedding. The original representation is retained. -/
@[blueprint "chap7__definition_7_3_2"]
def gEqSubtreeAt {L : Language} {hL : L.hasEquality = true} :
    {s : Sequent L} → GEqProofTree hL s → List Nat →
      Option (Σ c : Sequent L, GEqProofTree hL c)
  | s, t, [] => some ⟨s, t⟩
  | _, .base g, p => (gSubtreeAt g p).map (fun ⟨c, t⟩ => ⟨c, .base t⟩)
  | _, .onePremise _ t, 0 :: p => gEqSubtreeAt t p
  | _, .twoPremise _ t _, 0 :: p => gEqSubtreeAt t p
  | _, .twoPremise _ _ t, 1 :: p => gEqSubtreeAt t p
  | _, .eqRefl _ _ _ t, 0 :: p => gEqSubtreeAt t p
  | _, .eqFuncCong _ _ _ _ _ t, 0 :: p => gEqSubtreeAt t p
  | _, .eqPredCong _ _ _ _ _ t, 0 :: p => gEqSubtreeAt t p
  | _, .eqGeneral _ _ _ _ _ t, 0 :: p => gEqSubtreeAt t p
  | _, _, _ => none

/-- Definition 7.3.2: Expose just the root inference of an embedded G proof.
Its children stay embedded, preserving the original premise proof data. -/
@[blueprint "chap7__definition_7_3_2"]
def gEqExposeRoot {L : Language} {hL : L.hasEquality = true} {s : Sequent L} :
    GEqProofTree hL s → GEqProofTree hL s
  | .base (.onePremise r t) => .onePremise r (.base t)
  | .base (.twoPremise r t u) => .twoPremise r (.base t) (.base u)
  | t => t

/-- Definition 7.3.2: Inference lookup covers ordinary and equality nodes;
axioms have no inference, and base embeddings add no inference. -/
@[blueprint "chap7__definition_7_3_2"]
def gEqInferenceAt {L : Language} {hL : L.hasEquality = true} {s : Sequent L}
    (T : GEqProofTree hL s) (address : List Nat) : Option (AnyGEqStep hL) :=
  match gEqSubtreeAt T address with
  | none => none
  | some ⟨_, t⟩ => match gEqExposeRoot t with
    | .onePremise r _ => some (.one (.ordinary r))
    | .twoPremise r _ _ => some (.two r)
    | .eqRefl t Γ Δ _ => some (.one (.eqRefl t Γ Δ))
    | .eqFuncCong f ss ts Γ Δ _ => some (.one (.eqFuncCong f ss ts Γ Δ))
    | .eqPredCong P ss ts Γ Δ _ => some (.one (.eqPredCong P ss ts Γ Δ))
    | .eqGeneral axs hn ha Γ Δ _ => some (.one (.eqGeneral axs hn ha Γ Δ))
    | _ => none

/-- Definition 7.3.2: An actual inference at a fixed address in a G= proof. -/
@[blueprint "chap7__definition_7_3_2"]
structure GEqInferenceOccurrence {L : Language} {hL : L.hasEquality = true}
    {s : Sequent L} (T : GEqProofTree hL s) where
  address : List Nat
  rule : AnyGEqStep hL
  atAddress : gEqInferenceAt T address = some rule

/-- Definition 7.3.2: The actual source and premise at a one-premise G= node.
Exposing an embedded G root does not change its address or its premise tree. -/
@[blueprint "chap7__definition_7_3_2"]
structure GEqOnePremiseBoundary {L : Language} {hL : L.hasEquality = true}
    {s : Sequent L} {T : GEqProofTree hL s} (o : GEqInferenceOccurrence T) where
  premise : Sequent L
  conclusion : Sequent L
  rule : GEqStep1 hL premise conclusion
  tree : GEqProofTree hL premise
  source : GEqProofTree hL conclusion
  atAddress : gEqSubtreeAt T o.address = some ⟨conclusion, source⟩
  sourceRule : gEqExposeRoot source = rule.apply tree

/-- Definition 7.3.2: The actual source and ordered premise trees at a
 two-premise G= node, including nodes inside embedded G proofs. -/
@[blueprint "chap7__definition_7_3_2"]
structure GEqTwoPremiseBoundary {L : Language} {hL : L.hasEquality = true}
    {s : Sequent L} {T : GEqProofTree hL s} (o : GEqInferenceOccurrence T) where
  leftSequent : Sequent L
  rightSequent : Sequent L
  conclusion : Sequent L
  rule : GentzenStep2Ext leftSequent rightSequent conclusion
  leftTree : GEqProofTree hL leftSequent
  rightTree : GEqProofTree hL rightSequent
  source : GEqProofTree hL conclusion
  atAddress : gEqSubtreeAt T o.address = some ⟨conclusion, source⟩
  sourceRule : gEqExposeRoot source = .twoPremise rule leftTree rightTree

/-- Definition 7.3.2: Replay a G continuation around a G= replacement.
Every G rule and off-spine proof is retained. -/
@[blueprint "chap7__definition_7_3_2"]
def GProofContext.plugGEq {L : Language} {hL : L.hasEquality = true} {hole : Sequent L} :
    {s : Sequent L} → GProofContext hole s → GEqProofTree hL hole → GEqProofTree hL s
  | _, .hole, t => t
  | _, .one r rest, t => .onePremise r (rest.plugGEq t)
  | _, .left r rest sibling, t => .twoPremise r (rest.plugGEq t) (.base sibling)
  | _, .right r sibling rest, t => .twoPremise r (.base sibling) (rest.plugGEq t)

/-- Definition 7.3.2 (companion): Ancestry of the two specified inference occurrences in the fixed proof. This tests addresses alone, independently of intermediate rule kinds. -/
@[blueprint "chap7__definition_7_3_2"]
def isDescendantOfPremiseGEq {L : Language} {hL : L.hasEquality = true} {s : Sequent L} {T : GEqProofTree hL s}
    (R₁ R₂ : GEqInferenceOccurrence T) : Prop :=
  premiseAddressDescendant R₁.address R₂.address

/-- Definition 7.3.2 (companion): The selected upper occurrence is not in any premise subtree of the selected lower occurrence. A nonstructural intermediate does not erase ancestry. -/
@[blueprint "chap7__definition_7_3_2"]
def notDescendantOfPremiseGEq {L : Language} {hL : L.hasEquality = true} {s : Sequent L} {T : GEqProofTree hL s}
    (R₁ R₂ : GEqInferenceOccurrence T) : Prop :=
  ¬ isDescendantOfPremiseGEq R₁ R₂

/-- Definition 7.3.2 (companion): The selected upper inference lies above the selected lower inference, with only structural rules strictly between their addresses. Off-path branches are unrestricted. -/
@[blueprint "chap7__definition_7_3_2"]
def descendsWithStructuralIntermediatesGEq {L : Language} {hL : L.hasEquality = true} {s : Sequent L} {T : GEqProofTree hL s}
    (R₁ R₂ : GEqInferenceOccurrence T) : Prop :=
  isDescendantOfPremiseGEq R₁ R₂ ∧
  ∀ middle : GEqInferenceOccurrence T,
    premiseAddressDescendant middle.address R₂.address →
    premiseAddressDescendant R₁.address middle.address → middle.rule.isStructural

/-- Definition 7.3.2 (companion): Source boundaries of the selected local segment. The upper inference has one premise; the lower has one or two ordered premises. All boundary trees are actual subtrees of the same ambient proof. The chosen edge and tail identify the branch containing the upper inference. -/
@[blueprint "chap7__definition_7_3_2"]
structure GEqPermutationBoundary {L : Language} {hL : L.hasEquality = true} {s : Sequent L}
    {T : GEqProofTree hL s} (upper lower : GEqInferenceOccurrence T) where
  upperBoundary : GEqOnePremiseBoundary upper
  lowerBoundary : Sum (GEqOnePremiseBoundary lower) (GEqTwoPremiseBoundary lower)
  branch : Nat
  branchInRange : branch < lower.rule.premises.length
  tail : List Nat
  upperAt : upper.address = lower.address ++ branch :: tail
  structuralPath : descendsWithStructuralIntermediatesGEq upper lower

/-- Definition 7.3.2 (companion): The unchanged outside continuation T₀, with one sequent-indexed hole. Every rule on its spine and every off-spine proof is retained as data. -/
@[blueprint "chap7__definition_7_3_2"]
inductive GEqProofContext {L : Language} {hL : L.hasEquality = true} (hole : Sequent L) : Sequent L → Type where
  | hole : GEqProofContext (hL := hL) hole hole
  | base {s} (rest : GProofContext hole s) : GEqProofContext (hL := hL) hole s
  | one {p c} (rule : GEqStep1 hL p c) (rest : GEqProofContext (hL := hL) hole p) : GEqProofContext (hL := hL) hole c
  | left {p q c} (rule : GentzenStep2Ext p q c) (rest : GEqProofContext (hL := hL) hole p)
      (sibling : GEqProofTree hL q) : GEqProofContext (hL := hL) hole c
  | right {p q c} (rule : GentzenStep2Ext p q c) (sibling : GEqProofTree hL p)
      (rest : GEqProofContext (hL := hL) hole q) : GEqProofContext (hL := hL) hole c

/-- Definition 7.3.2 (companion): Reinsert a proof of S₀ into the unchanged outside continuation. -/
@[blueprint "chap7__definition_7_3_2"]
def GEqProofContext.plug {L : Language} {hL : L.hasEquality = true} {hole : Sequent L} :
    {s : Sequent L} → GEqProofContext (hL := hL) hole s → GEqProofTree hL hole → GEqProofTree hL s
  | _, .hole, t => t
  | _, .base rest, .base g => .base (rest.plug g)
  | _, .base rest, t => rest.plugGEq t
  | _, .one rule rest, t => rule.apply (rest.plug t)
  | _, .left rule rest sibling, t => .twoPremise rule (rest.plug t) sibling
  | _, .right rule sibling rest, t => .twoPremise rule sibling (rest.plug t)

/-- Definition 7.3.2 (companion): The address of the selected local segment in its outside continuation. -/
@[blueprint "chap7__definition_7_3_2"]
def GEqProofContext.address {L : Language} {hL : L.hasEquality = true} {hole : Sequent L} :
    {s : Sequent L} → GEqProofContext (hL := hL) hole s → List Nat
  | _, .hole => []
  | _, .base rest => rest.address
  | _, .one _ rest => 0 :: rest.address
  | _, .left _ rest _ => 0 :: rest.address
  | _, .right _ _ rest => 1 :: rest.address

/-- Definition 7.3.2 (companion): The local Q as a sequent-indexed open fragment. Its only leaves reference the supplied premise proof trees; it has no axiom constructor. -/
@[blueprint "chap7__definition_7_3_2"]
inductive GEqLocalFragment {L : Language} {hL : L.hasEquality = true}
    (inputs : List (Σ c : Sequent L, GEqProofTree hL c)) : Sequent L → Type where
  | input (i : Fin inputs.length) : GEqLocalFragment inputs (inputs.get i).1
  | one {p c} (rule : GEqStep1 hL p c) (sub : GEqLocalFragment inputs p) : GEqLocalFragment inputs c
  | two {p q c} (rule : GentzenStep2Ext p q c)
      (left : GEqLocalFragment inputs p) (right : GEqLocalFragment inputs q) : GEqLocalFragment inputs c

/-- Definition 7.3.2 (companion): Plug the original premise proofs into Q, preserving their proof data exactly. -/
@[blueprint "chap7__definition_7_3_2"]
def GEqLocalFragment.plug {L : Language} {hL : L.hasEquality = true} {inputs : List (Σ c : Sequent L, GEqProofTree hL c)} :
    {s : Sequent L} → GEqLocalFragment inputs s → GEqProofTree hL s
  | _, .input i => (inputs.get i).2
  | _, .one rule sub => rule.apply sub.plug
  | _, .two rule left right => .twoPremise rule left.plug right.plug

/-- Definition 7.3.2 (companion): The ordered input occurrences in Q. Equality with the full index range requires every supplied premise tree exactly once, in source order. -/
@[blueprint "chap7__definition_7_3_2"]
def GEqLocalFragment.inputOrder {L : Language} {hL : L.hasEquality = true} {inputs : List (Σ c : Sequent L, GEqProofTree hL c)} :
    {s : Sequent L} → GEqLocalFragment inputs s → List Nat
  | _, .input i => [i.val]
  | _, .one _ sub => sub.inputOrder
  | _, .two _ left right => left.inputOrder ++ right.inputOrder

/-- Definition 7.3.2 (companion): Inference lookup inside Q alone. Input proof trees are boundary leaves, so their internal rules cannot witness either permuted inference or violate the local structural-only condition. -/
@[blueprint "chap7__definition_7_3_2"]
def GEqLocalFragment.inferenceAt {L : Language} {hL : L.hasEquality = true} {inputs : List (Σ c : Sequent L, GEqProofTree hL c)} :
    {s : Sequent L} → GEqLocalFragment inputs s → List Nat → Option (AnyGEqStep hL)
  | _, .one rule _, [] => some (.one rule)
  | _, .two rule _ _, [] => some (.two rule)
  | _, .one _ sub, 0 :: p => sub.inferenceAt p
  | _, .two _ left _, 0 :: p => left.inferenceAt p
  | _, .two _ _ right, 1 :: p => right.inferenceAt p
  | _, _, _ => none

/-- Definition 7.3.2 (companion): A local replacement certificate: the source segment reconstructs T through the same T₀; Q has the same S₀, uses precisely the original ordered premise trees, retains both named inferences, reverses their ancestry, and has only structural additional inferences. -/
@[blueprint "chap7__definition_7_3_2"]
structure GEqLocalReplacement {L : Language} {hL : L.hasEquality = true} {s c : Sequent L}
    (T : GEqProofTree hL s) (rootAddress : List Nat) (source : GEqProofTree hL c)
    (inputs : List (Σ p : Sequent L, GEqProofTree hL p)) (R₁ R₂ : AnyGEqStep hL) where
  continuation : GEqProofContext (hL := hL) c s
  atAddress : continuation.address = rootAddress
  sourceFixed : continuation.plug source = T
  replacement : GEqLocalFragment inputs c
  inputOrder : replacement.inputOrder = List.range inputs.length
  firstAddress : List Nat
  secondAddress : List Nat
  firstRule : AnyGEqStep hL
  secondRule : AnyGEqStep hL
  firstAt : replacement.inferenceAt firstAddress = some firstRule
  secondAt : replacement.inferenceAt secondAddress = some secondRule
  firstSchema : firstRule.schemaKind = R₁.schemaKind
  secondSchema : secondRule.schemaKind = R₂.schemaKind
  firstPayload : firstRule.permutationPayload = R₁.permutationPayload
  secondPayload : secondRule.permutationPayload = R₂.permutationPayload
  distinct : firstAddress ≠ secondAddress
  reversed : ¬ premiseAddressDescendant firstAddress secondAddress
  otherStructural : ∀ p rule, replacement.inferenceAt p = some rule →
    p ≠ firstAddress → p ≠ secondAddress → rule.isStructural

/-- Definition 7.3.2 (companion): The resulting proof is computed by plugging Q through exactly the recorded outside continuation. -/
@[blueprint "chap7__definition_7_3_2"]
def GEqLocalReplacement.result {L : Language} {hL : L.hasEquality = true} {s c : Sequent L}
    {T : GEqProofTree hL s} {rootAddress : List Nat} {source : GEqProofTree hL c}
    {inputs : List (Σ p : Sequent L, GEqProofTree hL p)} {R₁ R₂ : AnyGEqStep hL}
    (h : GEqLocalReplacement T rootAddress source inputs R₁ R₂) : GEqProofTree hL s :=
  h.continuation.plug h.replacement.plug

/-- Definition 7.3.2 (companion): The one-premise case fixes T₁, S₀ and the selected lower inference before specifying Q and the unchanged outside continuation. -/
@[blueprint "chap7__definition_7_3_2"]
def GEqOnePremiseLocalReplacement {L : Language} {hL : L.hasEquality = true} {s : Sequent L} {T : GEqProofTree hL s}
    {upper lower : GEqInferenceOccurrence T} (ub : GEqOnePremiseBoundary upper) (lb : GEqOnePremiseBoundary lower) : Type :=
  GEqLocalReplacement T lower.address lb.source
    [⟨ub.premise, ub.tree⟩] upper.rule lower.rule

/-- Definition 7.3.2 (companion): The two-premise case preserves the original
left-to-right frontier. On the selected branch its input is the upper rule's
premise tree; the other branch retains the lower rule's entire premise tree. -/
@[blueprint "chap7__definition_7_3_2"]
def GEqTwoPremiseLocalReplacement {L : Language} {hL : L.hasEquality = true} {s : Sequent L} {T : GEqProofTree hL s}
    {upper lower : GEqInferenceOccurrence T}
    (ub : GEqOnePremiseBoundary upper) (lb : GEqTwoPremiseBoundary lower)
    (rightBranch : Bool) : Type :=
  GEqLocalReplacement T lower.address lb.source
    (if rightBranch then [⟨lb.leftSequent, lb.leftTree⟩, ⟨ub.premise, ub.tree⟩]
     else [⟨ub.premise, ub.tree⟩, ⟨lb.rightSequent, lb.rightTree⟩]) upper.rule lower.rule

/-- Definition 7.3.2: Every selected source boundary admits a local Q with
the same ordered premise proof trees and conclusion S₀, plugged into the exact
same outside continuation T₀. Q retains the two named inference schemas and
their non-context parameters, removes the forbidden ancestry, and contains only
structural additional inferences. The principal/side-formula proviso is a
separate condition in the permutability lemma. -/
@[blueprint "chap7__definition_7_3_2" (main := true)]
def CanPermuteWithGEq {L : Language} {hL : L.hasEquality = true} {s : Sequent L} {T : GEqProofTree hL s}
    (R₁ R₂ : GEqInferenceOccurrence T) : Prop :=
  ∀ boundary : GEqPermutationBoundary R₁ R₂,
    match boundary.lowerBoundary with
    | .inl lb => Nonempty (GEqOnePremiseLocalReplacement boundary.upperBoundary lb)
    | .inr lb => match boundary.branch with
      | 0 => Nonempty (GEqTwoPremiseLocalReplacement boundary.upperBoundary lb false)
      | 1 => Nonempty (GEqTwoPremiseLocalReplacement boundary.upperBoundary lb true)
      | _ => False


end LCS.Herbrand.SharpenedHauptsatz.Permutability
