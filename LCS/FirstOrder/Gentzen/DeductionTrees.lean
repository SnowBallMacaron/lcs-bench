import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics
import LCS.FirstOrder.SemanticsN
import LCS.FirstOrder.SemanticsN.Substitution
import LCS.FirstOrder.Gentzen.SystemG
import Attach
import LCS.FirstOrder.Gentzen.DeductionTrees.ProofsStamp

/-! # Deduction trees for the system G (Section 5.4.2)

Definition 5.4.2: falsifiable and valid sequents, deduction trees, proof trees
and G-provability.
Source: Logic for Computer Science, Gallier 2015
-/

section
namespace LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution

-- ===================================================================
-- Definition 5.4.2 (companion type): GProofTree (indexed)
-- ===================================================================

/-- Definition 5.4.2: Proof trees for the Gentzen system G over a language
without equality, indexed by their conclusion sequent. Textbook: "Deduction trees and proof trees
for the system G are defined as in definition 3.4.5, but for formulae
and with the rules given in definition 5.4.1." Structural validity is
built into the type: leaves must be axiom sequents, and each rule
application constrains its premise(s) to have the form mandated by the
rule (including side conditions for quantifier rules). No separate
WellFormed predicate is needed. -/
@[blueprint "chap5__definition_5_4_2" (main := true)]
inductive GProofTree {L : Language} (hL : L.withoutEquality) : Sequent L → Type where
  | axiom_ (s : Sequent L) (h : isAxiom s) : GProofTree hL s
  | onePremise {prem conc : Sequent L}
      (rule : GentzenStep1 hL prem conc)
      (t : GProofTree hL prem) : GProofTree hL conc
  | twoPremise {prem1 prem2 conc : Sequent L}
      (rule : GentzenStep2 hL prem1 prem2 conc)
      (t1 : GProofTree hL prem1) (t2 : GProofTree hL prem2) :
      GProofTree hL conc

-- ===================================================================
-- Definition 5.4.2 (companion type): GDeductionTree (indexed)
-- ===================================================================

/-- Definition 5.4.2 (companion): Deduction trees for the Gentzen system G
    over a language without equality, indexed by their conclusion sequent. Textbook: "Deduction trees and proof
    trees for the system G are defined as in Definition 3.4.5, but for
    formulae and with the rules given in Definition 5.4.1." Parallel of
    `GProofTree` with FREE-FORM leaves (i.e. leaves are not forced to be
    axioms). Proof trees are precisely the deduction trees whose leaves are
    all axioms (see `GDeductionTree.isProof` / `GDeductionTree.toProofTree`
    for the bridge). -/
@[blueprint "chap5__definition_5_4_2" (main := true)]
inductive GDeductionTree {L : Language} (hL : L.withoutEquality) : Sequent L → Type where
  | leaf (s : Sequent L) : GDeductionTree hL s
  | onePremise {prem conc : Sequent L}
      (rule : GentzenStep1 hL prem conc)
      (t : GDeductionTree hL prem) : GDeductionTree hL conc
  | twoPremise {p1 p2 conc : Sequent L}
      (rule : GentzenStep2 hL p1 p2 conc)
      (t1 : GDeductionTree hL p1) (t2 : GDeductionTree hL p2) :
      GDeductionTree hL conc

namespace GProofTree

/-- Definition 5.4.2 (companion): The conclusion of an indexed proof
tree is its type index. Textbook Def 3.4.5 / Def 5.4.2: "The sequent
labeling the root of a proof tree is called the conclusion of the
proof tree." This lemma witnesses that fact definitionally. -/
@[blueprint "chap5__definition_5_4_2"]
def conclusion {L : Language} (hL : L.withoutEquality) {s : Sequent L}
    (_ : GProofTree hL s) : Sequent L := s

end GProofTree

namespace GDeductionTree

/-- Definition 5.4.2 (companion): The conclusion of an indexed deduction
    tree is its type index (same as for `GProofTree`). -/
@[blueprint "chap5__definition_5_4_2"]
def conclusion {L : Language} (hL : L.withoutEquality) {s : Sequent L}
    (_ : GDeductionTree hL s) : Sequent L := s

/-- Definition 5.4.2 (companion): A deduction tree is a proof tree iff all
    its leaves are axiom sequents. This is the bridge between the two Def
    5.4.2 notions. -/
@[blueprint "chap5__definition_5_4_2"]
def isProof {L : Language} (hL : L.withoutEquality) : {s : Sequent L} → GDeductionTree hL s → Prop
  | _, .leaf s => isAxiom s
  | _, .onePremise _ t => t.isProof hL
  | _, .twoPremise _ t1 t2 => t1.isProof hL ∧ t2.isProof hL

/-- Definition 5.4.2 (companion): Converts a deduction tree whose leaves
    are all axioms into a proof tree of the same conclusion. -/
def toProofTree {L : Language} (hL : L.withoutEquality) :
    {s : Sequent L} → (t : GDeductionTree hL s) → t.isProof hL → GProofTree hL s
  | _, .leaf s, hax => GProofTree.axiom_ s hax
  | _, .onePremise rule t, hp => GProofTree.onePremise rule (t.toProofTree hL hp)
  | _, .twoPremise rule t1 t2, hp =>
      GProofTree.twoPremise rule
        (t1.toProofTree hL hp.1) (t2.toProofTree hL hp.2)

end GDeductionTree

/-- Definition 5.4.2 (companion): Over a language without equality, a sequent is
G-provable iff there exists a GProofTree with that sequent as conclusion. Textbook Def 3.4.5 /
Def 5.4.2: "A sequent is provable iff there exists a proof tree of
which it is the conclusion." -/
@[blueprint "chap5__definition_5_4_2"]
def sequentProvable {L : Language} (hL : L.withoutEquality) (s : Sequent L) : Prop :=
  Nonempty (GProofTree hL s)

-- ===================================================================
-- Definition 5.4.2: sequentValid (normalized, FormulaN-based)
-- ===================================================================

/-- Definition 5.6.2 (companion): A sequent is valid iff for every structure
and assignment, truth of all antecedent formulae implies truth of some succedent
formula. This general form allows any equality flag; G_= and later chapters use it. -/
@[blueprint "chap5__definition_5_6_2"]
def sequentValid {L : Language} (seq : Sequent L) : Prop :=
  ∀ (M : Structure L) (s : Assignment M),
    (∀ A ∈ seq.antecedent, formulaEvalN M A s) →
    (∃ B, B ∈ seq.succedent ∧ formulaEvalN M B s)

/-- Definition 5.4.2: A sequent over a language without equality is valid iff
for every structure and assignment, truth of all antecedent formulae implies
truth of some succedent formula. -/
@[blueprint "chap5__definition_5_4_2" (main := true)]
def sequentValidNoEq {L : Language} (hL : L.withoutEquality)
    (seq : SequentNoEq L hL) : Prop :=
  sequentValid seq

-- Construct membership in Γ ++ [X] (snoc)

-- ===================================================================
-- coincidenceLemmaN imported from SemanticsN

-- ===================================================================
-- Definition 5.4.2 (companion): sequentFalsifiableIn
-- ===================================================================

/-- Definition 5.6.2 (companion): A sequent is falsifiable in a
given structure M iff there exists an assignment s such that all
antecedent formulae are true and all succedent formulae are false
under (M, s). This general form allows any equality flag; G_= and later chapters use it. -/
@[blueprint "chap5__definition_5_6_2"]
def sequentFalsifiableIn {L : Language} (M : Structure L)
    (seq : Sequent L) : Prop :=
  ∃ (s : Assignment M),
    (∀ A ∈ seq.antecedent, formulaEvalN M A s) ∧
    (∀ B ∈ seq.succedent, ¬ formulaEvalN M B s)

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- Lemma 5.4.2 (companion): `sequentValid seq ↔ ∀ M, ¬ sequentFalsifiableIn M seq`. -/
theorem sequentValid_iff_not_falsifiable {L : Language} (seq : Sequent L) :
    sequentValid seq ↔ ∀ M : Structure L, ¬ sequentFalsifiableIn M seq := by
-- BEGIN PROOF
  constructor
  · intro h M ⟨s, hant, hsucc⟩
    obtain ⟨B, hBmem, hBeval⟩ := h M s hant
    exact hsucc B hBmem hBeval
  · intro h M s hant
    apply Classical.byContradiction
    intro hcontra
    apply h M
    refine ⟨s, hant, fun B hB hEval => hcontra ⟨B, hB, hEval⟩⟩

end LCS.FirstOrder.Gentzen
end
