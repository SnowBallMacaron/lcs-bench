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
import Attach
import LCS.Herbrand.NNFHauptsatz.Theorem.QuantifierRules.ProofsStamp

/-! # Herbrand.NNFHauptsatz.Theorem.QuantifierRules

Section 7.4.3: the quantifier rules of G2nnf viewed by principal formula, side and
exact occurrence, and the rules with and without contraction.
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

-- ===================================================================
-- Lemma 7.4.2 (untagged infrastructure): exact permutation occurrences
-- ===================================================================

/-- The side of a sequent on which a quantifier rule's principal formula
occurs.  This is deliberately untagged proof infrastructure for the local
permutation relation. -/
@[blueprint "chap7__lemma_7_4_3", blueprint "chap7__definition_7_4_3", blueprint "chap7__lemma_7_4_2"]
inductive G2nnfSequentSide where
  | left
  | right
deriving DecidableEq

/-- Select the raw context on the side of a quantifier principal formula. -/
@[blueprint "chap7__lemma_7_4_3", blueprint "chap7__lemma_7_4_2"]
def G2nnfSequentSide.context {L : Language}
    (side : G2nnfSequentSide)
    (Gamma Delta : LCS.Finset (FormulaN L)) :
    LCS.Finset (FormulaN L) :=
  match side with
  | .left => Gamma
  | .right => Delta

/-- The weakening rule which adds a formula on the selected sequent side. -/
def G2nnfSequentSide.weakeningRule {L : Language}
    (side : G2nnfSequentSide) (A : FormulaN L)
    (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L :=
  match side with
  | .left => .weakLeft A Gamma Delta
  | .right => .weakRight A Gamma Delta

/-- Constructor-exact evidence that a rule is one of the four G2nnf
quantifier rules.  Unlike `isQuantifierRule`, this view exposes the principal
formula and its sequent side without recovering them from rule-value
equalities. -/
@[blueprint "chap7__definition_7_4_3"]
inductive G2nnfQuantifierRuleView {L : Language} :
    G2nnfRuleCore L → Type where
  | allSubLeft (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A)
      (x : Nat) (B : FormulaN L) (t : Term L)
      (hSelected : occurrence.selected = FormulaN.all x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfQuantifierRuleView
        (.allSubLeft A occurrence x B t hSelected Gamma Delta)
  | allSubRight (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A)
      (x : Nat) (B : FormulaN L) (y : Nat)
      (hSelected : occurrence.selected = FormulaN.all x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfQuantifierRuleView
        (.allSubRight A occurrence x B y hSelected Gamma Delta)
  | exSubLeft (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A)
      (x : Nat) (B : FormulaN L) (y : Nat)
      (hSelected : occurrence.selected = FormulaN.ex x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfQuantifierRuleView
        (.exSubLeft A occurrence x B y hSelected Gamma Delta)
  | exSubRight (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A)
      (x : Nat) (B : FormulaN L) (t : Term L)
      (hSelected : occurrence.selected = FormulaN.ex x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfQuantifierRuleView
        (.exSubRight A occurrence x B t hSelected Gamma Delta)

namespace G2nnfQuantifierRuleView

/-- The exact principal formula carried by a quantifier-rule view. -/
@[blueprint "chap7__definition_7_4_3"]
def principal {L : Language} {rule : G2nnfRuleCore L} :
    G2nnfQuantifierRuleView rule → FormulaN L
  | .allSubLeft A _ _ _ _ _ _ _ => A
  | .allSubRight A _ _ _ _ _ _ _ => A
  | .exSubLeft A _ _ _ _ _ _ _ => A
  | .exSubRight A _ _ _ _ _ _ _ => A

/-- The side on which the viewed quantifier rule acts. -/
@[blueprint "chap7__definition_7_4_3"]
def side {L : Language} {rule : G2nnfRuleCore L} :
    G2nnfQuantifierRuleView rule → G2nnfSequentSide
  | .allSubLeft _ _ _ _ _ _ _ _ => .left
  | .allSubRight _ _ _ _ _ _ _ _ => .right
  | .exSubLeft _ _ _ _ _ _ _ _ => .left
  | .exSubRight _ _ _ _ _ _ _ _ => .right

/-- The exact maximal occurrence carried by the viewed rule. -/
@[blueprint "chap7__lemma_7_4_3"]
def occurrence {L : Language} {rule : G2nnfRuleCore L}
    (view : G2nnfQuantifierRuleView rule) :
    MaxQuantifierOccurrence view.principal :=
  match view with
  | .allSubLeft _ occurrence _ _ _ _ _ _ => occurrence
  | .allSubRight _ occurrence _ _ _ _ _ _ => occurrence
  | .exSubLeft _ occurrence _ _ _ _ _ _ => occurrence
  | .exSubRight _ occurrence _ _ _ _ _ _ => occurrence

/-- The substitution result inserted at the exact selected occurrence. -/
@[blueprint "chap7__lemma_7_4_2"]
def replacement {L : Language} {rule : G2nnfRuleCore L}
    (view : G2nnfQuantifierRuleView rule) : FormulaN L :=
  match view with
  | .allSubLeft _ _ x B t _ _ _ => formulaSubstN B t x
  | .allSubRight _ _ x B y _ _ _ => formulaSubstN B (.var y) x
  | .exSubLeft _ _ x B y _ _ _ => formulaSubstN B (.var y) x
  | .exSubRight _ _ x B t _ _ _ => formulaSubstN B t x

/-- The principal formula in the premise of the viewed quantifier rule. -/
@[blueprint "chap7__lemma_7_4_2"]
def premisePrincipal {L : Language}
    {rule : G2nnfRuleCore L}
    (view : G2nnfQuantifierRuleView rule) : FormulaN L :=
  view.occurrence.replace view.replacement

/-- Rebuild the same quantifier schema at a new principal only when the
caller supplies the exact transported occurrence.  The selected formula must
be the same one selected by the source rule. The caller supplies the output
side contexts of the rebuilt instance. -/
@[blueprint "chap7__lemma_7_4_3"]
def reprincipalAt {L : Language} {rule : G2nnfRuleCore L}
    (view : G2nnfQuantifierRuleView rule) {A' : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A')
    (hSameSelected : occurrence.selected = view.occurrence.selected)
    (Gamma Delta : LCS.Finset (FormulaN L)) :
    G2nnfRuleCore L :=
  match view with
  | .allSubLeft _ _ x B t hSelected _ _ =>
      .allSubLeft A' occurrence x B t
        (hSameSelected.trans hSelected) Gamma Delta
  | .allSubRight _ _ x B y hSelected _ _ =>
      .allSubRight A' occurrence x B y
        (hSameSelected.trans hSelected) Gamma Delta
  | .exSubLeft _ _ x B y hSelected _ _ =>
      .exSubLeft A' occurrence x B y
        (hSameSelected.trans hSelected) Gamma Delta
  | .exSubRight _ _ x B t hSelected _ _ =>
      .exSubRight A' occurrence x B t
        (hSameSelected.trans hSelected) Gamma Delta

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

end LCS.Herbrand.NNFHauptsatz.Theorem
end
