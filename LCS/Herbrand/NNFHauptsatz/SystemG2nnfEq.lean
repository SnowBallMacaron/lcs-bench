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
import LCS.Herbrand.NNFHauptsatz.RuleCore
import Attach
import LCS.Herbrand.NNFHauptsatz.SystemG2nnfEq.ProofsStamp

/-! # Herbrand.NNFHauptsatz.SystemG2nnfEq

Definition 7.4.4: the Gentzen system G2nnf= (rules, proof trees, inessential cuts,
provability).
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

-- ===================================================================
-- Definition 7.4.4: G2nnfEqRule — G2nnf_= inference rules
-- ===================================================================

/-- Definition 7.4.4: The system G2nnf_= is obtained from G1nnf_= by adding
the quantifier rules of Definition 7.4.3 and weakening. Its ordinary atomic
axioms and equality axioms are contextual. Base rules include the independent
context cut; equality schemas are reused from `G1nnfEqAxiom`. -/
@[blueprint "chap7__definition_7_4_4" (main := true)]
inductive G2nnfEqRule (L : Language) (hL : L.hasEquality = true) : Type where
  /-- A general core rule with its own stored contexts. -/
  | base (r : G2nnfRuleCore L) : G2nnfEqRule L hL
  /-- An equality axiom schema shared with G1nnf_= (Def 6.4.6) -/
  | eqAxiom (ax : G1nnfEqAxiom L hL) : G2nnfEqRule L hL

namespace G2nnfEqRule

/-- Definition 7.4.4 (companion): The cut formula of a core cut;
all other core inferences and equality axioms return none. -/
@[blueprint "chap7__definition_7_4_4"]
def cutFormula {L : Language} {hL : L.hasEquality = true} :
    G2nnfEqRule L hL → Option (FormulaN L)
  | .base (.cut A _ _ _ _) => some A
  | .base _ => none
  | .eqAxiom _ => none

/-- Definition 7.4.4 (companion): The actual stored conclusion. Ordinary
contextual axioms and independent cuts use Core; equality schemas retain
their canonical G1nnf= frames via toSequent. -/
@[blueprint "chap7__definition_7_4_4"]
noncomputable def conclusion {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] :
    G2nnfEqRule L hL → LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)
  | .base r => r.conclusion
  | .eqAxiom ax => ax.toSequent

/-- Definition 7.4.4 (companion): The stored core premises, or no premises
for an equality axiom. Ordinary contextual atomic axioms also have none. -/
@[blueprint "chap7__definition_7_4_4"]
noncomputable def premises {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] :
    G2nnfEqRule L hL → List (LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L))
  | .base r => r.premises
  | .eqAxiom _ => []

/-- Definition 7.4.4 (companion): Core rules, including contextual ordinary
axioms, satisfy Core side conditions. Equality axioms retain WellFormed for
their recursive negation closures, and every formula in the full contextual
conclusion must be NNF and rectified. No bare-axiom restriction is imposed. -/
@[blueprint "chap7__definition_7_4_4"]
noncomputable def SideConditions {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] : G2nnfEqRule L hL → Prop
  | .base r => r.SideConditions
  | .eqAxiom ax => ax.WellFormed ∧ AllNNF ax.toSequent ∧ AllRectified ax.toSequent

end G2nnfEqRule

/-- Definition 7.4.4 (companion): An extra-axiom sequent is exactly the
canonical sequent of a well-formed G1nnf= equality schema. The tree carrier
separately enforces NNF and rectification on the entire sequent. -/
@[blueprint "chap7__definition_7_4_4"]
noncomputable def G2nnfEqRule.EqualityAxiomSequent {L : Language}
    (hL : L.hasEquality = true)
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) : Prop :=
  ∃ ax : G1nnfEqAxiom L hL, ax.WellFormed ∧ ax.toSequent = seq

/-- Definition 7.4.4 (required type): Equality proofs instantiate the shared
Core recursion with contextual ordinary rules and well-formed G1nnf= equality
axioms. Every node is NNF and rectified. Open leaves are excluded at every
depth; the equality-language witness fixes the available axiom schemas. -/
@[blueprint "chap7__definition_7_4_4"]
abbrev G2nnfEqProofTree {L : Language} (hL : L.hasEquality = true)
    [DecidableEq (FormulaN L)] :=
  G2nnfProofTreeCore (L := L) (fun _ => True)
    (G2nnfEqRule.EqualityAxiomSequent hL)

/-- Definition 7.4.4 (companion): Equality deductions use the same contextual
Core rules and equality axioms as proofs, with NNF rectified open leaves. -/
@[blueprint "chap7__definition_7_4_4"]
abbrev G2nnfEqDeductionTree {L : Language} (hL : L.hasEquality = true)
    [DecidableEq (FormulaN L)] :=
  G2nnfDeductionTreeCore (L := L) (fun _ => True)
    (G2nnfEqRule.EqualityAxiomSequent hL) (fun _ => True)

namespace G2nnfEqDeductionTree

/-- Definition 7.4.4 (companion): The equality deduction's indexed conclusion. -/
@[blueprint "chap7__definition_7_4_4"]
def conclusion {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] {Gamma Delta : LCS.Finset (FormulaN L)}
    (_ : G2nnfEqDeductionTree hL Gamma Delta) :
    LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) := (Gamma, Delta)

-- retained: used by LCS.Herbrand.NNFHauptsatz.Equality.Part1, LCS.Herbrand.NNFHauptsatz.Theorem.Example, LCS.Herbrand.NNFHauptsatz.Theorem.Paths, LCS.Herbrand.SHGTheorem.Herbrand.Alteration, LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination, LCS.Herbrand.SHGTheorem.Herbrand.LowerConstruction
theorem allRectified {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfEqDeductionTree hL Gamma Delta) : AllRectified (Gamma, Delta) := by
  cases T with
  | leaf _ _ _ _ hRect => exact hRect
  | extraAxiom _ _ _ _ hRect => exact hRect
  | axiom_ _ _ _ hSC => exact hSC.conclusionRectified
  | onePremise _ _ _ hSC _ => exact hSC.conclusionRectified
  | twoPremise _ _ _ hSC _ _ => exact hSC.conclusionRectified

end G2nnfEqDeductionTree
namespace G2nnfEqProofTree

/-- Definition 7.4.4 (companion def): Returns the conclusion sequent of a G2nnf_= proof tree. For the indexed tree this is just the type index `(Γ, Δ)`. -/
@[blueprint "chap7__definition_7_4_4"]
def conclusion {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (_ : G2nnfEqProofTree hL Γ Δ) :
    LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) :=
  (Γ, Δ)

-- retained: used by LCS.Herbrand.NNFHauptsatz.Equality.Part1, LCS.Herbrand.NNFHauptsatz.Theorem.Example, LCS.Herbrand.NNFHauptsatz.Theorem.Paths, LCS.Herbrand.SHGTheorem.Herbrand.Alteration, LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination, LCS.Herbrand.SHGTheorem.Herbrand.LowerConstruction
/-- Every node conclusion in a G2nnf= proof tree satisfies §7.4's standing
rectification invariant. -/
theorem allRectified {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfEqProofTree hL Γ Δ) :
    AllRectified (Γ, Δ) := by
  cases T with
  | leaf _ _ hOpen _ _ => exact hOpen.elim
  | extraAxiom _ _ _ _ hRect => exact hRect
  | axiom_ _ _ _ hSC => exact hSC.conclusionRectified
  | onePremise _ _ _ hSC _ => exact hSC.conclusionRectified
  | twoPremise _ _ _ hSC _ _ => exact hSC.conclusionRectified

/-- Definition 7.4.4 (companion def): Extract the root-level cut formula of a G2nnf_= proof tree — that is, the `cutFormula` of the rule at the tree's root inference. Returns `none` for axiom leaves and for all non-cut inferences (equality axioms, weakening, propositional, quantifier rules). Used by `hasNoEssentialCuts` (Theorem 7.4.2). -/
@[blueprint "chap7__definition_7_4_4"]
def cutFormula {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)} :
    G2nnfEqProofTree hL Γ Δ → Option (FormulaN L)
  | .leaf _ _ hOpen _ _ => hOpen.elim
  | .extraAxiom _ _ _ _ _ => none
  | .axiom_ rule _ _ _ => (G2nnfEqRule.base (hL := hL) rule).cutFormula
  | .onePremise rule _ _ _ _ => (G2nnfEqRule.base (hL := hL) rule).cutFormula
  | .twoPremise rule _ _ _ _ _ => (G2nnfEqRule.base (hL := hL) rule).cutFormula

end G2nnfEqProofTree

/-- Theorem 7.4.2 (required def): A cut is inessential if its cut formula is a literal over the equality predicate, i.e., it has the form `s = t` or `neg(s = t)`. Inessential cuts are allowed in a "proof without essential cuts" by the sharpened Hauptsatz for G2nnf_= (Theorem 7.4.2). Mirrors the G1nnf_= notion from Def 6.4.9. -/
@[blueprint "chap7__theorem_7_4_2"]
def isInessentialCut {L : Language} : FormulaN L → Prop
  | .eq_ _ _ _ => True
  | .neg (.eq_ _ _ _) => True
  | _ => False

namespace G2nnfEqProofTree

/-- Theorem 7.4.2 (required def): A G2nnf_= proof tree has no essential cuts iff every cut application in the tree uses an inessential cut formula (literal equality `s = t` or its negation `neg(s = t)`). Defined by structural recursion: an axiom leaf has no cuts; one-premise nodes propagate the sub-tree check; two-premise nodes additionally require that if the root rule has a cut formula (i.e., is a cut), that formula is inessential. -/
@[blueprint "chap7__theorem_7_4_2"]
def hasNoEssentialCuts {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfEqProofTree hL Γ Δ → Prop
  | _, _, .leaf _ _ hOpen _ _ => hOpen.elim
  | _, _, .extraAxiom _ _ _ _ _ => True
  | _, _, .axiom_ _ _ _ _ => True
  | _, _, .onePremise _ _ _ _ sub => hasNoEssentialCuts (hL := hL) sub
  | _, _, .twoPremise rule _ _ _ sub1 sub2 =>
    (match (G2nnfEqRule.base (hL := hL) rule).cutFormula with
      | some A => isInessentialCut A
      | none => True) ∧
    hasNoEssentialCuts (hL := hL) sub1 ∧ hasNoEssentialCuts (hL := hL) sub2

end G2nnfEqProofTree

/-- Definition 7.4.4 (companion def): Provability in G2nnf_=. A sequent `(Γ, Δ)` is `g2nnfEqProvable` iff the shared NNF carrier has a closed proof with that conclusion, contextual core rules and well-formed equality axioms over the equality language. -/
@[blueprint "chap7__definition_7_4_4"]
def g2nnfEqProvable {L : Language} (hL : L.hasEquality = true)
    [DecidableEq (FormulaN L)]
    (Γ Δ : LCS.Finset (FormulaN L)) : Prop :=
  Nonempty (G2nnfEqProofTree hL Γ Δ)
end LCS.Herbrand.NNFHauptsatz
end
