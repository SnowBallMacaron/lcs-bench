import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Equality
import LCS.Herbrand.NNFHauptsatz.Rectification
import LCS.Herbrand.NNFHauptsatz.MaxQuantSubformulae
import LCS.Herbrand.NNFHauptsatz.SubformulaSubstitution
import Attach
import LCS.Herbrand.NNFHauptsatz.RuleCore.ProofsStamp

/-! # Herbrand.NNFHauptsatz.RuleCore

Definitions 7.4.3 and 7.4.4: the rule instances and indexed proof trees shared by
the systems G2nnf and G2nnf=, with their NNF and side conditions.
-/

section
namespace LCS.Herbrand.NNFHauptsatz
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality

/-- Every formula on either side of a finite sequent is in NNF. -/
@[blueprint "chap7__definition_7_4_3"]
def AllNNF {L : Language}
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) : Prop :=
  (∀ A, A ∈ seq.1 → A.isNNF) ∧ (∀ A, A ∈ seq.2 → A.isNNF)

/-- General rule instances shared by the ordinary and equality systems.
Contexts are data of the instance; cut carries two independent context pairs.
Ordinary axioms are contextual here. `BareAtomicAxiom` selects the bare
instances for the equality-free public calculus. NNF and logical side
conditions are checked at every tree node. -/
@[blueprint "chap7__definition_7_4_4"]
inductive G2nnfRuleCore (L : Language) : Type where
  /-- Contextual positive identity: Gamma, A -> Delta, A for atomic A -/
  | axiomPosId (A : FormulaN L) (hAtom : A.isAtomic)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Contextual negative identity: Gamma, not A -> Delta, not A for atomic A -/
  | axiomNegId (A : FormulaN L) (hAtom : A.isAtomic)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Contextual complementary right: Gamma -> Delta, A, not A for atomic A -/
  | axiomCompRight (A : FormulaN L) (hAtom : A.isAtomic)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Contextual complementary left: Gamma, A, not A -> Delta for atomic A -/
  | axiomCompLeft (A : FormulaN L) (hAtom : A.isAtomic)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Weakening left: from Gamma -> Delta infer A, Gamma -> Delta -/
  | weakLeft (A : FormulaN L)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Weakening right: from Gamma -> Delta infer Gamma -> Delta, A -/
  | weakRight (A : FormulaN L)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Conjunction left (variant 1): from A, Gamma -> Delta infer
      A and B, Gamma -> Delta -/
  | conjLeft1 (A B : FormulaN L)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Conjunction left (variant 2): from B, Gamma -> Delta infer
      A and B, Gamma -> Delta -/
  | conjLeft2 (A B : FormulaN L)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Conjunction right: from Gamma -> Delta, A and Gamma -> Delta, B
      infer Gamma -> Delta, A and B -/
  | conjRight (A B : FormulaN L)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Disjunction left: from A, Gamma -> Delta and B, Gamma -> Delta
      infer A or B, Gamma -> Delta -/
  | disjLeft (A B : FormulaN L)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Disjunction right (variant 1): from Gamma -> Delta, A infer
      Gamma -> Delta, A or B -/
  | disjRight1 (A B : FormulaN L)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Disjunction right (variant 2): from Gamma -> Delta, B infer
      Gamma -> Delta, A or B -/
  | disjRight2 (A B : FormulaN L)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Cut rule: from Gamma -> Delta, A and A, Lambda -> Theta infer
      Gamma, Lambda -> Delta, Theta -/
  | cut (A : FormulaN L) (Lambda Theta : LCS.Finset (FormulaN L))
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Forall-subformula left: replace exactly the selected maximal occurrence
      of `forall x B` by `B[t/x]`.  The occurrence and its selected-formula
      equation are constructor data, so duplicate equal formulae remain
      distinct and QF-membership is enforced structurally. -/
  | allSubLeft (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A) (x : Nat)
      (B : FormulaN L) (t : Term L)
      (hSelected : occurrence.selected = FormulaN.all x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Forall-subformula right: replace exactly the selected maximal occurrence
      of `forall x B` by `B[y/x]`; `y` is fresh for the lower sequent. -/
  | allSubRight (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A) (x : Nat)
      (B : FormulaN L) (y : Nat)
      (hSelected : occurrence.selected = FormulaN.all x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Exists-subformula left: replace exactly the selected maximal occurrence
      of `exists x B` by `B[y/x]`; `y` is fresh for the lower sequent. -/
  | exSubLeft (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A) (x : Nat)
      (B : FormulaN L) (y : Nat)
      (hSelected : occurrence.selected = FormulaN.ex x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Exists-subformula right: replace exactly the selected maximal occurrence
      of `exists x B` by `B[t/x]`. -/
  | exSubRight (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A) (x : Nat)
      (B : FormulaN L) (t : Term L)
      (hSelected : occurrence.selected = FormulaN.ex x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L

namespace G2nnfRuleCore

/-- The actual conclusion, including the union of independent cut contexts. -/
@[blueprint "chap7__definition_7_4_4"]
def conclusion {L : Language} [DecidableEq (FormulaN L)] :
    G2nnfRuleCore L →
    LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)
  | .axiomPosId A _ Gamma Delta =>
    (LCS.Finset.insert A Gamma, LCS.Finset.insert A Delta)
  | .axiomNegId A _ Gamma Delta =>
    (LCS.Finset.insert (.neg A) Gamma, LCS.Finset.insert (.neg A) Delta)
  | .axiomCompRight A _ Gamma Delta =>
    (Gamma, LCS.Finset.insert A (LCS.Finset.insert (.neg A) Delta))
  | .axiomCompLeft A _ Gamma Delta =>
    (LCS.Finset.insert A (LCS.Finset.insert (.neg A) Gamma), Delta)
  | .weakLeft A Gamma Delta =>
    (LCS.Finset.insert A Gamma, Delta)
  | .weakRight A Gamma Delta =>
    (Gamma, LCS.Finset.insert A Delta)
  | .conjLeft1 A B Gamma Delta =>
    (LCS.Finset.insert (.conj A B) Gamma, Delta)
  | .conjLeft2 A B Gamma Delta =>
    (LCS.Finset.insert (.conj A B) Gamma, Delta)
  | .conjRight A B Gamma Delta =>
    (Gamma, LCS.Finset.insert (.conj A B) Delta)
  | .disjLeft A B Gamma Delta =>
    (LCS.Finset.insert (.disj A B) Gamma, Delta)
  | .disjRight1 A B Gamma Delta =>
    (Gamma, LCS.Finset.insert (.disj A B) Delta)
  | .disjRight2 A B Gamma Delta =>
    (Gamma, LCS.Finset.insert (.disj A B) Delta)
  | .cut _ Lambda Theta Gamma Delta =>
    (LCS.Finset.union Gamma Lambda, LCS.Finset.union Delta Theta)
  | .allSubLeft A _ _ _ _ _ Gamma Delta =>
    (LCS.Finset.insert A Gamma, Delta)
  | .allSubRight A _ _ _ _ _ Gamma Delta =>
    (Gamma, LCS.Finset.insert A Delta)
  | .exSubLeft A _ _ _ _ _ Gamma Delta =>
    (LCS.Finset.insert A Gamma, Delta)
  | .exSubRight A _ _ _ _ _ Gamma Delta =>
    (Gamma, LCS.Finset.insert A Delta)

/-- The actual premises; quantifier rules replace exactly their stored maximal
occurrence and retain the selected-formula equation. -/
@[blueprint "chap7__definition_7_4_4"]
def premises {L : Language} [DecidableEq (FormulaN L)] :
    G2nnfRuleCore L →
    List (LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L))
  | .axiomPosId _ _ _ _ => []
  | .axiomNegId _ _ _ _ => []
  | .axiomCompRight _ _ _ _ => []
  | .axiomCompLeft _ _ _ _ => []
  | .weakLeft _ Gamma Delta => [(Gamma, Delta)]
  | .weakRight _ Gamma Delta => [(Gamma, Delta)]
  | .conjLeft1 A _ Gamma Delta =>
    [(LCS.Finset.insert A Gamma, Delta)]
  | .conjLeft2 _ B Gamma Delta =>
    [(LCS.Finset.insert B Gamma, Delta)]
  | .conjRight A B Gamma Delta =>
    [(Gamma, LCS.Finset.insert A Delta),
     (Gamma, LCS.Finset.insert B Delta)]
  | .disjLeft A B Gamma Delta =>
    [(LCS.Finset.insert A Gamma, Delta),
     (LCS.Finset.insert B Gamma, Delta)]
  | .disjRight1 A _ Gamma Delta =>
    [(Gamma, LCS.Finset.insert A Delta)]
  | .disjRight2 _ B Gamma Delta =>
    [(Gamma, LCS.Finset.insert B Delta)]
  | .cut A Lambda Theta Gamma Delta =>
    [(Gamma, LCS.Finset.insert A Delta),
     (LCS.Finset.insert A Lambda, Theta)]
  | .allSubLeft _ occurrence x B t _ Gamma Delta =>
    [(LCS.Finset.insert
        (occurrence.replace (formulaSubstN B t x))
        Gamma, Delta)]
  | .allSubRight _ occurrence x B y _ Gamma Delta =>
    [(Gamma,
      LCS.Finset.insert
        (occurrence.replace (formulaSubstN B (.var y) x)) Delta)]
  | .exSubLeft _ occurrence x B y _ Gamma Delta =>
    [(LCS.Finset.insert
        (occurrence.replace (formulaSubstN B (.var y) x)) Gamma, Delta)]
  | .exSubRight _ occurrence x B t _ Gamma Delta =>
    [(Gamma,
      LCS.Finset.insert
        (occurrence.replace (formulaSubstN B t x)) Delta)]

/-- Free-for and eigenvariable freshness at the stored inference contexts. -/
@[blueprint "chap7__definition_7_4_4"]
def LogicalSideConditions {L : Language} :
    G2nnfRuleCore L → Prop
  | .axiomPosId _ _ _ _ => True
  | .axiomNegId _ _ _ _ => True
  | .axiomCompRight _ _ _ _ => True
  | .axiomCompLeft _ _ _ _ => True
  | .weakLeft _ _ _ => True
  | .weakRight _ _ _ => True
  | .conjLeft1 _ _ _ _ => True
  | .conjLeft2 _ _ _ _ => True
  | .conjRight _ _ _ _ => True
  | .disjLeft _ _ _ _ => True
  | .disjRight1 _ _ _ _ => True
  | .disjRight2 _ _ _ _ => True
  | .cut _ _ _ _ _ => True
  | .allSubLeft _ _ x B t _ _ _ =>
    isFreeForN t x B
  | .allSubRight A _ x B y _ Gamma Delta =>
    isFreeForN (Term.var y) x B ∧
    ¬ Membership.mem (formulaFVN A) y ∧
    (∀ F, Membership.mem Gamma F → ¬ Membership.mem (formulaFVN F) y) ∧
    (∀ F, Membership.mem Delta F → ¬ Membership.mem (formulaFVN F) y)
  | .exSubLeft A _ x B y _ Gamma Delta =>
    isFreeForN (Term.var y) x B ∧
    ¬ Membership.mem (formulaFVN A) y ∧
    (∀ F, Membership.mem Gamma F → ¬ Membership.mem (formulaFVN F) y) ∧
    (∀ F, Membership.mem Delta F → ¬ Membership.mem (formulaFVN F) y)
  | .exSubRight _ _ x B t _ _ _ =>
    isFreeForN t x B

/-- Select bare atomic axiom instances; every non-axiom rule is admitted.
The context fields are empty, so an admitted zero-premise rule has exactly
one of the four printed bare conclusions. -/
@[blueprint "chap7__definition_7_4_3"]
def BareAtomicAxiom {L : Language} : G2nnfRuleCore L → Prop
  | .axiomPosId _ _ Gamma Delta | .axiomNegId _ _ Gamma Delta
    | .axiomCompRight _ _ Gamma Delta | .axiomCompLeft _ _ Gamma Delta =>
      Gamma = LCS.Finset.empty ∧ Delta = LCS.Finset.empty
  | _ => True

/-- A legal core inference has NNF premises and conclusion, satisfies the
local quantifier conditions, and retains the standing rectification convention.
NNF is checked on every formula, including cut formulae and weakening formulae. -/
@[blueprint "chap7__definition_7_4_4"]
structure SideConditions {L : Language} [DecidableEq (FormulaN L)]
    (rule : G2nnfRuleCore L) : Prop where
  logical : rule.LogicalSideConditions
  conclusionNNF : AllNNF rule.conclusion
  premisesNNF : ∀ seq ∈ rule.premises, AllNNF seq
  conclusionRectified : AllRectified rule.conclusion

end G2nnfRuleCore

/-- Shared indexed tree recursion for both calculi. Each ordinary inference
requires `admitRule` and the core side conditions. Extra axioms are permitted only
by `extraAxiom`, with explicit NNF and rectification evidence. Open leaves
require `openLeaf` and the same sequent invariants. The default admits arbitrary
NNF rectified open sequents; setting `openLeaf` to False gives proof trees. -/
@[blueprint "chap7__definition_7_4_4"]
inductive G2nnfDeductionTreeCore {L : Language} [DecidableEq (FormulaN L)]
    (admitRule : G2nnfRuleCore L → Prop)
    (extraAxiom : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) → Prop)
    (openLeaf : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) → Prop :=
      fun _ => True) :
    LCS.Finset (FormulaN L) → LCS.Finset (FormulaN L) → Type where
  | leaf (Gamma Delta : LCS.Finset (FormulaN L))
      (hOpen : openLeaf (Gamma, Delta)) (hNNF : AllNNF (Gamma, Delta))
      (hRect : AllRectified (Gamma, Delta)) :
      G2nnfDeductionTreeCore admitRule extraAxiom openLeaf Gamma Delta
  | extraAxiom (Gamma Delta : LCS.Finset (FormulaN L))
      (hExtra : extraAxiom (Gamma, Delta)) (hNNF : AllNNF (Gamma, Delta))
      (hRect : AllRectified (Gamma, Delta)) :
      G2nnfDeductionTreeCore admitRule extraAxiom openLeaf Gamma Delta
  | axiom_ (rule : G2nnfRuleCore L) (hAdmit : admitRule rule)
      (hAxiom : rule.premises.length = 0) (hSC : rule.SideConditions) :
      G2nnfDeductionTreeCore admitRule extraAxiom openLeaf
        rule.conclusion.1 rule.conclusion.2
  | onePremise (rule : G2nnfRuleCore L) (hAdmit : admitRule rule)
      (hPrem : rule.premises.length = 1) (hSC : rule.SideConditions)
      (sub : G2nnfDeductionTreeCore admitRule extraAxiom openLeaf
        (rule.premises[0]'(by omega)).1 (rule.premises[0]'(by omega)).2) :
      G2nnfDeductionTreeCore admitRule extraAxiom openLeaf
        rule.conclusion.1 rule.conclusion.2
  | twoPremise (rule : G2nnfRuleCore L) (hAdmit : admitRule rule)
      (hPrem : rule.premises.length = 2) (hSC : rule.SideConditions)
      (sub1 : G2nnfDeductionTreeCore admitRule extraAxiom openLeaf
        (rule.premises[0]'(by omega)).1 (rule.premises[0]'(by omega)).2)
      (sub2 : G2nnfDeductionTreeCore admitRule extraAxiom openLeaf
        (rule.premises[1]'(by omega)).1 (rule.premises[1]'(by omega)).2) :
      G2nnfDeductionTreeCore admitRule extraAxiom openLeaf
        rule.conclusion.1 rule.conclusion.2

/-- Closed trees use the same recursion as deductions, with open leaves
excluded at every depth. Rule admission and extra axioms remain parameters. -/
@[blueprint "chap7__definition_7_4_4"]
abbrev G2nnfProofTreeCore {L : Language} [DecidableEq (FormulaN L)]
    (admitRule : G2nnfRuleCore L → Prop)
    (extraAxiom : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) → Prop) :=
  G2nnfDeductionTreeCore admitRule extraAxiom (fun _ => False)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Every node of a core tree has an NNF conclusion, including open leaves
and extra axioms. Applying this lemma to any subtree gives the same invariant. -/
theorem G2nnfDeductionTreeCore.allNNF {L : Language} [DecidableEq (FormulaN L)]
    {admitRule : G2nnfRuleCore L → Prop}
    {extraAxiom openLeaf : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) → Prop}
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (tree : G2nnfDeductionTreeCore admitRule extraAxiom openLeaf Gamma Delta) :
    AllNNF (Gamma, Delta) := by
  cases tree with
  | leaf _ _ _ hNNF _ => exact hNNF
  | extraAxiom _ _ _ hNNF _ => exact hNNF
  | axiom_ _ _ _ hSC => exact hSC.conclusionNNF
  | onePremise _ _ _ hSC _ => exact hSC.conclusionNNF
  | twoPremise _ _ _ hSC _ _ => exact hSC.conclusionNNF
end LCS.Herbrand.NNFHauptsatz
end
