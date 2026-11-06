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
import LCS.Herbrand.NNFHauptsatz.RuleCore
import Attach
import LCS.Herbrand.NNFHauptsatz.SystemG2nnf.ProofsStamp

/-! # Herbrand.NNFHauptsatz.SystemG2nnf

Definition 7.4.3: the Gentzen system G2nnf (rules, proof trees, deduction trees,
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
-- Definition 7.4.3: G2nnfRule — Inference rules of the system G2nnf
-- ===================================================================

/-- Definition 7.4.3: Rule instances of the equality-free G2nnf calculus.
The shared carrier stores all inference contexts. Ordinary zero-premise
instances are restricted to the four bare atomic schemes; contextual uses
require explicit weakening. Logical and NNF requirements are enforced by
`SideConditions` at every inference. -/
@[blueprint "chap7__definition_7_4_3" (main := true)]
abbrev G2nnfRule (L : Language) (_hL : L.withoutEquality) :=
  {rule : G2nnfRuleCore L // rule.BareAtomicAxiom}

namespace G2nnfRule

/-- Definition 7.4.3 (companion): The conclusion of the stored equality-free
rule instance. Atomic conclusions are bare; cut unions independent contexts. -/
@[blueprint "chap7__definition_7_4_3"]
def conclusion {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] (rule : G2nnfRule L hL) :
    LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) :=
  rule.val.conclusion

/-- Definition 7.4.3 (companion): The actual premises of the stored rule.
Cut has independent contexts, and quantified replacement follows the exact
constructor-carried maximal occurrence. -/
@[blueprint "chap7__definition_7_4_3"]
def premises {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] (rule : G2nnfRule L hL) :
    List (LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) :=
  rule.val.premises

/-- Definition 7.4.3 (companion): A legal equality-free inference has NNF
premises and conclusion, satisfies free-for/eigenvariable freshness, and has
a rectified conclusion. Bare atomic admission is evidence in the rule itself. -/
@[blueprint "chap7__definition_7_4_3"]
def SideConditions {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] (rule : G2nnfRule L hL) : Prop :=
  rule.val.SideConditions

namespace SideConditions

-- retained: used by LCS.Herbrand.NNFHauptsatz.Equality.Part1, LCS.Herbrand.NNFHauptsatz.Theorem.Example, LCS.Herbrand.NNFHauptsatz.Theorem.Paths, LCS.Herbrand.SHGTheorem.Herbrand.Alteration, LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination, LCS.Herbrand.SHGTheorem.Herbrand.LowerConstruction
theorem allRectified {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {rule : G2nnfRule L hL}
    (hSC : rule.SideConditions) : AllRectified rule.conclusion :=
  hSC.conclusionRectified

end SideConditions
end G2nnfRule

/-- Definition 7.4.3 (required companion): Equality-free proof trees use the
shared indexed recursion with BareAtomicAxiom admission at every inference,
no extra axioms, and no open leaves. Every node has NNF and rectification
evidence; child indices match the actual rule premises. -/
@[blueprint "chap7__definition_7_4_3"]
abbrev G2nnfProofTree {L : Language} (_hL : L.withoutEquality)
    [DecidableEq (FormulaN L)] :=
  G2nnfProofTreeCore (L := L) G2nnfRuleCore.BareAtomicAxiom (fun _ => False)

namespace G2nnfProofTree

/-- Definition 7.4.3 (companion): The conclusion is the proof tree's index. -/
@[blueprint "chap7__definition_7_4_3"]
def conclusion {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {Gamma Delta : LCS.Finset (FormulaN L)}
    (_ : G2nnfProofTree hL Gamma Delta) :
    LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) := (Gamma, Delta)

-- retained: used by LCS.Herbrand.NNFHauptsatz.Equality.Part1, LCS.Herbrand.NNFHauptsatz.Theorem.Example, LCS.Herbrand.NNFHauptsatz.Theorem.Paths, LCS.Herbrand.SHGTheorem.Herbrand.Alteration, LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination, LCS.Herbrand.SHGTheorem.Herbrand.LowerConstruction
/-- Rectification holds at every proof node. -/
theorem allRectified {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta) : AllRectified (Gamma, Delta) := by
  cases T with
  | leaf _ _ hOpen _ _ => exact hOpen.elim
  | extraAxiom _ _ hExtra _ _ => exact hExtra.elim
  | axiom_ _ _ _ hSC => exact hSC.conclusionRectified
  | onePremise _ _ _ hSC _ => exact hSC.conclusionRectified
  | twoPremise _ _ _ hSC _ _ => exact hSC.conclusionRectified

end G2nnfProofTree

/-- Definition 7.4.3 (required companion): Equality-free deductions use the
same recursion and bare-axiom admission as proofs, with NNF rectified open
leaves allowed. Extra axioms remain excluded at every depth. -/
@[blueprint "chap7__definition_7_4_3"]
abbrev G2nnfDeductionTree {L : Language} (_hL : L.withoutEquality)
    [DecidableEq (FormulaN L)] :=
  G2nnfDeductionTreeCore (L := L) G2nnfRuleCore.BareAtomicAxiom
    (fun _ => False) (fun _ => True)

namespace G2nnfDeductionTree

/-- Definition 7.4.3 (companion): The deduction's indexed conclusion. -/
@[blueprint "chap7__definition_7_4_3"]
def conclusion {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {Gamma Delta : LCS.Finset (FormulaN L)}
    (_ : G2nnfDeductionTree hL Gamma Delta) :
    LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) := (Gamma, Delta)

end G2nnfDeductionTree

/-- Definition 7.4.3 (companion): Provability in the equality-free, bare-axiom
NNF calculus, witnessed by a proof tree with the given conclusion. -/
@[blueprint "chap7__definition_7_4_3"]
def g2nnfProvable {L : Language} (hL : L.withoutEquality)
    [DecidableEq (FormulaN L)] (Gamma Delta : LCS.Finset (FormulaN L)) : Prop :=
  Nonempty (G2nnfProofTree hL Gamma Delta)
end LCS.Herbrand.NNFHauptsatz
end
