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
import LCS.Herbrand.NNFHauptsatz.Theorem.QuantifierRules
import Attach
import LCS.Herbrand.NNFHauptsatz.Theorem.PermutationLowerRules.ProofsStamp

/-! # Herbrand.NNFHauptsatz.Theorem.PermutationLowerRules

Definition 7.3.2 extended to G2nnf: the lower inference R2 below a quantifier
rule R1, its selected premise and its instances after the exchange.
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

/-- Definition 7.3.2, as extended in §7.4.3: the lower rule may be any
G2nnf rule with a premise, including a quantifier rule or cut. The extension
restricts the intervening structural section to weakenings only. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfPermutationLowerRuleView {L : Language} :
    G2nnfRuleCore L → Type where
  | weakLeft (A : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.weakLeft A Gamma Delta)
  | weakRight (A : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.weakRight A Gamma Delta)
  | conjLeft1 (A B : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.conjLeft1 A B Gamma Delta)
  | conjLeft2 (A B : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.conjLeft2 A B Gamma Delta)
  | conjRight (A B : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.conjRight A B Gamma Delta)
  | disjLeft (A B : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.disjLeft A B Gamma Delta)
  | disjRight1 (A B : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.disjRight1 A B Gamma Delta)
  | disjRight2 (A B : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.disjRight2 A B Gamma Delta)

  | cut (A : FormulaN L) (Lambda Theta : LCS.Finset (FormulaN L))
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.cut A Lambda Theta Gamma Delta)
  /-- Forall-subformula left: replace exactly the selected maximal occurrence
      of `forall x B` by `B[t/x]`.  The occurrence and its selected-formula
      equation are constructor data, so duplicate equal formulae remain
      distinct and QF-membership is enforced structurally. -/
  | allSubLeft (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A) (x : Nat)
      (B : FormulaN L) (t : Term L)
      (hSelected : occurrence.selected = FormulaN.all x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.allSubLeft A occurrence x B t hSelected Gamma Delta)
  /-- Forall-subformula right: replace exactly the selected maximal occurrence
      of `forall x B` by `B[y/x]`; `y` is fresh for the lower sequent. -/
  | allSubRight (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A) (x : Nat)
      (B : FormulaN L) (y : Nat)
      (hSelected : occurrence.selected = FormulaN.all x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.allSubRight A occurrence x B y hSelected Gamma Delta)
  /-- Exists-subformula left: replace exactly the selected maximal occurrence
      of `exists x B` by `B[y/x]`; `y` is fresh for the lower sequent. -/
  | exSubLeft (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A) (x : Nat)
      (B : FormulaN L) (y : Nat)
      (hSelected : occurrence.selected = FormulaN.ex x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.exSubLeft A occurrence x B y hSelected Gamma Delta)
  /-- Exists-subformula right: replace exactly the selected maximal occurrence
      of `exists x B` by `B[t/x]`. -/
  | exSubRight (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A) (x : Nat)
      (B : FormulaN L) (t : Term L)
      (hSelected : occurrence.selected = FormulaN.ex x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.exSubRight A occurrence x B t hSelected Gamma Delta)

/-- Which exact premise occurrence of the lower rule contains the upper
quantifier occurrence. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfPremiseChoice where
  | only
  | left
  | right
deriving DecidableEq

namespace G2nnfPermutationLowerRuleView

/-- The formula occurrence contributed by the selected premise of the lower
rule. Quantifier premises contribute the formula with the selected subformula
instantiated; cut contributes its cut formula on the selected premise side.
Weakening premises contribute no focused formula;
the quantifier principal must then be inherited from the raw context.  Invalid
arity/choice combinations return `none`, but cannot arise in
`G2nnfSelectedPremiseOccurrence` because its tree constructors carry the exact
premise-length equation. -/
@[blueprint "chap7__lemma_7_4_3", blueprint "chap7__lemma_7_4_2"]
def selectedFocus {L : Language} {rule : G2nnfRuleCore L}
    (view : G2nnfPermutationLowerRuleView rule)
    (choice : G2nnfPremiseChoice) :
    Option (G2nnfSequentSide × FormulaN L) :=
  match view, choice with
  | .weakLeft _ _ _, _ => none
  | .weakRight _ _ _, _ => none
  | .conjLeft1 A _ _ _, .only => some (.left, A)
  | .conjLeft2 _ B _ _, .only => some (.left, B)
  | .conjRight A _ _ _, .left => some (.right, A)
  | .conjRight _ B _ _, .right => some (.right, B)
  | .disjLeft A _ _ _, .left => some (.left, A)
  | .disjLeft _ B _ _, .right => some (.left, B)
  | .disjRight1 A _ _ _, .only => some (.right, A)
  | .disjRight2 _ B _ _, .only => some (.right, B)
  | .allSubLeft _ occurrence x B t _ _ _, .only =>
      some (.left, occurrence.replace (formulaSubstN B t x))
  | .allSubRight _ occurrence x B y _ _ _, .only =>
      some (.right, occurrence.replace (formulaSubstN B (.var y) x))
  | .exSubLeft _ occurrence x B y _ _ _, .only =>
      some (.left, occurrence.replace (formulaSubstN B (.var y) x))
  | .exSubRight _ occurrence x B t _ _ _, .only =>
      some (.right, occurrence.replace (formulaSubstN B t x))
  | .cut A _ _ _ _, .left => some (.right, A)
  | .cut A _ _ _ _, .right => some (.left, A)
  | _, _ => none

/-- The principal formula in the lower conclusion. Quantifier rules return
the ambient formula containing their selected quantified subformula. Weakening
and cut have no logical principal formula in the conclusion; the cut formula
is exposed by `selectedFocus` on either selected premise. -/
@[blueprint "chap7__lemma_7_4_3", blueprint "chap7__lemma_7_4_2"]
def principal {L : Language} {rule : G2nnfRuleCore L}
    (view : G2nnfPermutationLowerRuleView rule) :
    Option (G2nnfSequentSide × FormulaN L) :=
  match view with
  | .weakLeft _ _ _ => none
  | .weakRight _ _ _ => none
  | .conjLeft1 A B _ _ => some (.left, .conj A B)
  | .conjLeft2 A B _ _ => some (.left, .conj A B)
  | .conjRight A B _ _ => some (.right, .conj A B)
  | .disjLeft A B _ _ => some (.left, .disj A B)
  | .disjRight1 A B _ _ => some (.right, .disj A B)
  | .disjRight2 A B _ _ => some (.right, .disj A B)
  | .allSubLeft A _ _ _ _ _ _ _ => some (.left, A)
  | .allSubRight A _ _ _ _ _ _ _ => some (.right, A)
  | .exSubLeft A _ _ _ _ _ _ _ => some (.left, A)
  | .exSubRight A _ _ _ _ _ _ _ => some (.right, A)
  | .cut _ _ _ _ _ => none

/-- Retain all rule operands and dependent quantifier occurrences while
replacing the first pair of side contexts. Cut retains its independent second
pair; the general permutation relation supplies both pairs for cut. -/
@[blueprint "chap7__definition_7_3_2"]
def withContexts {L : Language} {rule : G2nnfRuleCore L}
    (view : G2nnfPermutationLowerRuleView rule)
    (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L :=
  match view with
  | .weakLeft A _ _ => .weakLeft A Gamma Delta
  | .weakRight A _ _ => .weakRight A Gamma Delta
  | .conjLeft1 A B _ _ => .conjLeft1 A B Gamma Delta
  | .conjLeft2 A B _ _ => .conjLeft2 A B Gamma Delta
  | .conjRight A B _ _ => .conjRight A B Gamma Delta
  | .disjLeft A B _ _ => .disjLeft A B Gamma Delta
  | .disjRight1 A B _ _ => .disjRight1 A B Gamma Delta
  | .disjRight2 A B _ _ => .disjRight2 A B Gamma Delta
  | .allSubLeft A occurrence x B t hSelected _ _ =>
      .allSubLeft A occurrence x B t hSelected Gamma Delta
  | .allSubRight A occurrence x B y hSelected _ _ =>
      .allSubRight A occurrence x B y hSelected Gamma Delta
  | .exSubLeft A occurrence x B y hSelected _ _ =>
      .exSubLeft A occurrence x B y hSelected Gamma Delta
  | .exSubRight A occurrence x B t hSelected _ _ =>
      .exSubRight A occurrence x B t hSelected Gamma Delta
  | .cut A Lambda Theta _ _ => .cut A Lambda Theta Gamma Delta

/-- Total selected-premise instantiation on Lemma 7.4.2's propositional or
weakening domain. The scope evidence excludes quantifier rules and cut. -/
@[blueprint "chap7__lemma_7_4_2"]
def instantiateSelectedOfPropositional {L : Language} {R₁ R₂ : G2nnfRuleCore L}
    (lower : G2nnfPermutationLowerRuleView R₂)
    (hLower : R₂.isPropositionalRule ∨ R₂.isWeakening)
    (quantifier : G2nnfQuantifierRuleView R₁)
    (choice : G2nnfPremiseChoice)
    (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L :=
  match lower, choice with
  | .weakLeft A _ _, _ => .weakLeft A Gamma Delta
  | .weakRight A _ _, _ => .weakRight A Gamma Delta
  | .conjLeft1 A B _ _, .only =>
      .conjLeft1 quantifier.premisePrincipal B Gamma Delta
  | .conjLeft1 A B _ _, _ => .conjLeft1 A B Gamma Delta
  | .conjLeft2 A B _ _, .only =>
      .conjLeft2 A quantifier.premisePrincipal Gamma Delta
  | .conjLeft2 A B _ _, _ => .conjLeft2 A B Gamma Delta
  | .conjRight A B _ _, .left =>
      .conjRight quantifier.premisePrincipal B Gamma Delta
  | .conjRight A B _ _, .right =>
      .conjRight A quantifier.premisePrincipal Gamma Delta
  | .conjRight A B _ _, .only => .conjRight A B Gamma Delta
  | .disjLeft A B _ _, .left =>
      .disjLeft quantifier.premisePrincipal B Gamma Delta
  | .disjLeft A B _ _, .right =>
      .disjLeft A quantifier.premisePrincipal Gamma Delta
  | .disjLeft A B _ _, .only => .disjLeft A B Gamma Delta
  | .disjRight1 A B _ _, .only =>
      .disjRight1 quantifier.premisePrincipal B Gamma Delta
  | .disjRight1 A B _ _, _ => .disjRight1 A B Gamma Delta
  | .disjRight2 A B _ _, .only =>
      .disjRight2 A quantifier.premisePrincipal Gamma Delta
  | .disjRight2 A B _ _, _ => .disjRight2 A B Gamma Delta
  | .allSubLeft .., _ | .allSubRight .., _
  | .exSubLeft .., _ | .exSubRight .., _ | .cut .., _ => by
      simp [G2nnfRuleCore.isPropositionalRule, G2nnfRuleCore.isWeakening] at hLower

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.RuleOccurrences
/-- Logical principal of the occurrence-focused propositional lower-rule image.
This Lemma 7.4.2 helper returns `none` for quantifier and cut lower rules, whose
permutation requires separate occurrence transport. -/
def instantiatedPrincipal {L : Language} {R₁ R₂ : G2nnfRuleCore L}
    (lower : G2nnfPermutationLowerRuleView R₂)
    (quantifier : G2nnfQuantifierRuleView R₁)
    (choice : G2nnfPremiseChoice) :
    Option (G2nnfSequentSide × FormulaN L) :=
  match lower, choice with
  | .weakLeft _ _ _, _ => none
  | .weakRight _ _ _, _ => none
  | .conjLeft1 _ B _ _, .only =>
      some (.left, .conj quantifier.premisePrincipal B)
  | .conjLeft1 A B _ _, _ => some (.left, .conj A B)
  | .conjLeft2 A _ _ _, .only =>
      some (.left, .conj A quantifier.premisePrincipal)
  | .conjLeft2 A B _ _, _ => some (.left, .conj A B)
  | .conjRight _ B _ _, .left =>
      some (.right, .conj quantifier.premisePrincipal B)
  | .conjRight A _ _ _, .right =>
      some (.right, .conj A quantifier.premisePrincipal)
  | .conjRight A B _ _, .only => some (.right, .conj A B)
  | .disjLeft _ B _ _, .left =>
      some (.left, .disj quantifier.premisePrincipal B)
  | .disjLeft A _ _ _, .right =>
      some (.left, .disj A quantifier.premisePrincipal)
  | .disjLeft A B _ _, .only => some (.left, .disj A B)
  | .disjRight1 _ B _ _, .only =>
      some (.right, .disj quantifier.premisePrincipal B)
  | .disjRight1 A B _ _, _ => some (.right, .disj A B)
  | .disjRight2 A _ _ _, .only =>
      some (.right, .disj A quantifier.premisePrincipal)
  | .disjRight2 A B _ _, _ => some (.right, .disj A B)
  | .allSubLeft .., _ | .allSubRight .., _
  | .exSubLeft .., _ | .exSubRight .., _ | .cut .., _ => none

/-- An exact lift of one selected occurrence into a surrounding connective,
including the invariant that the selected quantified formula is unchanged. -/
@[blueprint "chap7__lemma_7_4_3"]
structure G2nnfFocusedOccurrenceLift {L : Language}
    (target selected : FormulaN L) where
  occurrence : MaxQuantifierOccurrence target
  selected_eq : occurrence.selected = selected

attribute [blueprint "chap7__lemma_7_4_3"] _root_.LCS.Herbrand.NNFHauptsatz.Theorem.G2nnfPermutationLowerRuleView.G2nnfFocusedOccurrenceLift.occurrence

attribute [blueprint "chap7__lemma_7_4_3"] _root_.LCS.Herbrand.NNFHauptsatz.Theorem.G2nnfPermutationLowerRuleView.G2nnfFocusedOccurrenceLift.selected_eq

/-- Lift a selected maximal occurrence through the exact connective branch
identified by a focused lower premise. This Lemma 7.4.2 connective helper
returns `none` for quantifier rules and cut: maximal occurrences do not in
general lift through a quantifier, and a cut removes its cut formula. -/
@[blueprint "chap7__lemma_7_4_3"]
def liftFocusedOccurrence {L : Language} {R₂ : G2nnfRuleCore L}
    (lower : G2nnfPermutationLowerRuleView R₂)
    (choice : G2nnfPremiseChoice)
    {side : G2nnfSequentSide} {selected target : FormulaN L}
    (hFocus : lower.selectedFocus choice = some (side, selected))
    (hPrincipal : lower.principal = some (side, target))
    (occurrence : MaxQuantifierOccurrence selected) :
    Option (G2nnfFocusedOccurrenceLift target occurrence.selected) :=
  match lower, choice with
  | .weakLeft _ _ _, _ => by simp [selectedFocus] at hFocus
  | .weakRight _ _ _, _ => by simp [selectedFocus] at hFocus
  | .conjLeft1 A B _ _, .only => by
      simp only [selectedFocus, Option.some.injEq, Prod.mk.injEq] at hFocus
      simp only [principal, Option.some.injEq, Prod.mk.injEq] at hPrincipal
      rcases hFocus with ⟨rfl, rfl⟩
      rcases hPrincipal with ⟨_, rfl⟩
      exact some ⟨.conjLeft occurrence B, rfl⟩
  | .conjLeft1 _ _ _ _, .left => by simp [selectedFocus] at hFocus
  | .conjLeft1 _ _ _ _, .right => by simp [selectedFocus] at hFocus
  | .conjLeft2 A B _ _, .only => by
      simp only [selectedFocus, Option.some.injEq, Prod.mk.injEq] at hFocus
      simp only [principal, Option.some.injEq, Prod.mk.injEq] at hPrincipal
      rcases hFocus with ⟨rfl, rfl⟩
      rcases hPrincipal with ⟨_, rfl⟩
      exact some ⟨.conjRight A occurrence, rfl⟩
  | .conjLeft2 _ _ _ _, .left => by simp [selectedFocus] at hFocus
  | .conjLeft2 _ _ _ _, .right => by simp [selectedFocus] at hFocus
  | .conjRight A B _ _, .left => by
      simp only [selectedFocus, Option.some.injEq, Prod.mk.injEq] at hFocus
      simp only [principal, Option.some.injEq, Prod.mk.injEq] at hPrincipal
      rcases hFocus with ⟨rfl, rfl⟩
      rcases hPrincipal with ⟨_, rfl⟩
      exact some ⟨.conjLeft occurrence B, rfl⟩
  | .conjRight A B _ _, .right => by
      simp only [selectedFocus, Option.some.injEq, Prod.mk.injEq] at hFocus
      simp only [principal, Option.some.injEq, Prod.mk.injEq] at hPrincipal
      rcases hFocus with ⟨rfl, rfl⟩
      rcases hPrincipal with ⟨_, rfl⟩
      exact some ⟨.conjRight A occurrence, rfl⟩
  | .conjRight _ _ _ _, .only => by simp [selectedFocus] at hFocus
  | .disjLeft A B _ _, .left => by
      simp only [selectedFocus, Option.some.injEq, Prod.mk.injEq] at hFocus
      simp only [principal, Option.some.injEq, Prod.mk.injEq] at hPrincipal
      rcases hFocus with ⟨rfl, rfl⟩
      rcases hPrincipal with ⟨_, rfl⟩
      exact some ⟨.disjLeft occurrence B, rfl⟩
  | .disjLeft A B _ _, .right => by
      simp only [selectedFocus, Option.some.injEq, Prod.mk.injEq] at hFocus
      simp only [principal, Option.some.injEq, Prod.mk.injEq] at hPrincipal
      rcases hFocus with ⟨rfl, rfl⟩
      rcases hPrincipal with ⟨_, rfl⟩
      exact some ⟨.disjRight A occurrence, rfl⟩
  | .disjLeft _ _ _ _, .only => by simp [selectedFocus] at hFocus
  | .disjRight1 A B _ _, .only => by
      simp only [selectedFocus, Option.some.injEq, Prod.mk.injEq] at hFocus
      simp only [principal, Option.some.injEq, Prod.mk.injEq] at hPrincipal
      rcases hFocus with ⟨rfl, rfl⟩
      rcases hPrincipal with ⟨_, rfl⟩
      exact some ⟨.disjLeft occurrence B, rfl⟩
  | .disjRight1 _ _ _ _, .left => by simp [selectedFocus] at hFocus
  | .disjRight1 _ _ _ _, .right => by simp [selectedFocus] at hFocus
  | .disjRight2 A B _ _, .only => by
      simp only [selectedFocus, Option.some.injEq, Prod.mk.injEq] at hFocus
      simp only [principal, Option.some.injEq, Prod.mk.injEq] at hPrincipal
      rcases hFocus with ⟨rfl, rfl⟩
      rcases hPrincipal with ⟨_, rfl⟩
      exact some ⟨.disjRight A occurrence, rfl⟩
  | .disjRight2 _ _ _ _, .left => by simp [selectedFocus] at hFocus
  | .disjRight2 _ _ _ _, .right => by simp [selectedFocus] at hFocus
  | .allSubLeft .., _ | .allSubRight .., _
  | .exSubLeft .., _ | .exSubRight .., _ | .cut .., _ => none
end G2nnfPermutationLowerRuleView
end LCS.Herbrand.NNFHauptsatz.Theorem
end
