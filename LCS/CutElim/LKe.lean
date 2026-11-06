import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import Attach
import LCS.CutElim.LKe.ProofsStamp

/-! # CutElim.LKe
    Formalization of Chapter 6, Section 6.3.
    The Gentzen system LKe with equality: syntax and definitions.
-/

namespace LCS.CutElim.LKe

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.Gentzen
open LCS.CutElim.LK

-- ===================================================================
-- Definition 6.3.1: LKeEqualityAxiom — Equality axioms of LKe
-- ===================================================================

/-- Definition 6.3.1: The equality axioms that distinguish LKe from
LK. The three textbook schemas are reflexivity, function congruence,
and predicate congruence. Since built-in equality is represented by
`FormulaN.eq_` rather than an element of `L.predSymbols`, its binary
predicate-congruence instance is represented separately by `eqCong`. -/
@[blueprint "chap6__definition_6_3_1" (main := true)]
inductive LKeEqualityAxiom (L : Language) : Type where
  /-- Reflexivity axiom: for every term t, the sequent -> t = t
      is an axiom -/
  | refl (t : Term L) : LKeEqualityAxiom L
  /-- Function congruence axiom: for every n-ary function symbol f,
      s1=t1,...,sn=tn -> f(s1,...,sn) = f(t1,...,tn) is an axiom -/
  | funcCong (f : L.funSymbols)
      (ss ts : Fin (L.funArity f) → Term L) : LKeEqualityAxiom L
  /-- Predicate congruence axiom: for every n-ary predicate symbol P
      represented in `L.predSymbols`, s1=t1,...,sn=tn,
      P(s1,...,sn) -> P(t1,...,tn) is an axiom. -/
  | predCong (P : L.predSymbols)
      (ss ts : Fin (L.predArity P) → Term L) : LKeEqualityAxiom L
  /-- Equality-as-predicate congruence, the binary instance omitted
      by `predCong` because equality has its own formula constructor:
      s1=t1, s2=t2, s1=s2 -> t1=t2. -/
  | eqCong (s1 s2 t1 t2 : Term L) : LKeEqualityAxiom L

-- ===================================================================
-- Definition 6.3.1 (companion def): LKeEqualityAxiom.toSequent
-- ===================================================================

namespace LKeEqualityAxiom

/-- Definition 6.3.1 (companion): Converts an equality axiom to its
corresponding sequent. For refl t: antecedent=[], succedent=[t = t].
For funcCong f ss ts: antecedent=[s1=t1,...,sn=tn],
succedent=[f(s1,...,sn) = f(t1,...,tn)].
For predCong P ss ts: antecedent=[s1=t1,...,sn=tn, P(s1,...,sn)],
succedent=[P(t1,...,tn)]. For eqCong: antecedent=
[s1=t1, s2=t2, s1=s2], succedent=[t1=t2].
Requires `hL : L.hasEquality = true`
since LKe is the system with equality. -/
@[blueprint "chap6__definition_6_3_1"]
def toSequent {L : Language} (hL : L.hasEquality = true) :
    LKeEqualityAxiom L → Sequent L
  | .refl t =>
    { antecedent := []
      succedent := [FormulaN.eq_ hL t t] }
  | .funcCong f ss ts =>
    let eqPairs := (List.finRange (L.funArity f)).map
      (fun i => FormulaN.eq_ hL (ss i) (ts i))
    { antecedent := eqPairs
      succedent := [FormulaN.eq_ hL (Term.func f ss) (Term.func f ts)] }
  | .predCong P ss ts =>
    let eqPairs := (List.finRange (L.predArity P)).map
      (fun i => FormulaN.eq_ hL (ss i) (ts i))
    { antecedent := eqPairs ++ [FormulaN.predN P ss]
      succedent := [FormulaN.predN P ts] }
  | .eqCong s1 s2 t1 t2 =>
    { antecedent :=
        [FormulaN.eq_ hL s1 t1, FormulaN.eq_ hL s2 t2,
          FormulaN.eq_ hL s1 s2]
      succedent := [FormulaN.eq_ hL t1 t2] }

end LKeEqualityAxiom

-- ===================================================================
-- Definition 6.3.1 (companion type): LKeProofTree (indexed)
-- ===================================================================

/-- Definition 6.3.1 (companion type): Proof trees for the Gentzen
system LKe, indexed by their conclusion sequent. The carrier has the
same axiom, one-premise, and two-premise rule nodes as LK, together
with equality-axiom leaves. Consequently every ordinary LK rule can
occur above either kind of axiom leaf, and every node's exact premise
and conclusion sequents are enforced by the indices. No separate
well-formedness predicate is needed. -/
@[blueprint "chap6__definition_6_3_1"]
inductive LKeProofTree {L : Language} : Sequent L → Type where
  /-- Ordinary LK axiom leaf. -/
  | axiom_ (s : Sequent L) (h : isFOLKAxiom s) : LKeProofTree s
  /-- Equality axiom leaf: the conclusion is the axiom's toSequent.
      Requires `hL : L.hasEquality = true` to construct the equality
      formula; this matches LKe being defined only for languages with
      equality. -/
  | eqAxiom (hL : L.hasEquality = true) (ax : LKeEqualityAxiom L) :
      LKeProofTree (ax.toSequent hL)
  /-- One-premise LK rule, permitted above ordinary or equality
      leaves. -/
  | onePremise {prem conc : Sequent L}
      (rule : FOLKStep1 prem conc)
      (t : LKeProofTree prem) : LKeProofTree conc
  /-- Two-premise LK rule, permitted above arbitrary LKe subproofs. -/
  | twoPremise {prem1 prem2 conc : Sequent L}
      (rule : FOLKStep2 prem1 prem2 conc)
      (t1 : LKeProofTree prem1) (t2 : LKeProofTree prem2) :
      LKeProofTree conc

namespace LKeProofTree

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 6.3.1 (construction adapter): recursively embeds an LK
proof into the canonical LKe carrier. This preserves the established
`LKeProofTree.lk t` source construction API without retaining a
whole-tree wrapper node. -/
def lk {L : Language} :
    {s : Sequent L} → FOLKProofTree s → LKeProofTree s
  | _, .axiom_ s h => .axiom_ s h
  | _, .onePremise rule t => .onePremise rule (lk t)
  | _, .twoPremise rule t1 t2 =>
      .twoPremise rule (lk t1) (lk t2)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 6.3.1 (construction adapter): the established LKe cut
smart constructor, now represented by the canonical two-premise node. -/
def cut {L : Language} (A : FormulaN L)
    (Γ Δ Λ Θ : List (FormulaN L))
    (t1 : LKeProofTree (Sequent.mk Γ (Δ ++ [A])))
    (t2 : LKeProofTree (Sequent.mk (A :: Λ) Θ)) :
    LKeProofTree (Sequent.mk (Γ ++ Λ) (Δ ++ Θ)) :=
  .twoPremise (.cut A Γ Δ Λ Θ) t1 t2

end LKeProofTree

-- ===================================================================
-- Definition 6.3.1: LKₑ deduction trees
-- ===================================================================

/-- LKₑ deduction trees, indexed by their conclusion sequent, with arbitrary
leaf sequents and explicit equality-axiom leaves. Every inference is an LK
rule with its premise and conclusion indices enforced by the constructors. -/
@[blueprint "chap6__definition_6_3_1"]
inductive LKeDeductionTree {L : Language} : Sequent L → Type where
  /-- An arbitrary leaf sequent. -/
  | leaf (s : Sequent L) : LKeDeductionTree s
  /-- An equality-axiom leaf with its schema data. -/
  | eqAxiom (hL : L.hasEquality = true) (ax : LKeEqualityAxiom L) :
      LKeDeductionTree (ax.toSequent hL)
  /-- A one-premise LK inference. -/
  | onePremise {prem conc : Sequent L} (rule : FOLKStep1 prem conc)
      (t : LKeDeductionTree prem) : LKeDeductionTree conc
  /-- A two-premise LK inference, including cut. -/
  | twoPremise {prem1 prem2 conc : Sequent L} (rule : FOLKStep2 prem1 prem2 conc)
      (t₁ : LKeDeductionTree prem1) (t₂ : LKeDeductionTree prem2) :
      LKeDeductionTree conc

namespace LKeDeductionTree

/-- The conclusion sequent of an indexed LKₑ deduction tree. -/
@[blueprint "chap6__definition_6_3_1"]
def conclusion {L : Language} {s : Sequent L} (_ : LKeDeductionTree s) : Sequent L := s

/-- An LKₑ deduction tree is a proof exactly when every leaf is an ordinary
LK axiom or an equality axiom. Explicit equality-axiom nodes satisfy this
condition by construction. -/
@[blueprint "chap6__definition_6_3_1"]
def isProof {L : Language} : {s : Sequent L} → LKeDeductionTree s → Prop
  | _, .leaf s => isFOLKAxiom s ∨
      ∃ (hL : L.hasEquality = true) (ax : LKeEqualityAxiom L), s = ax.toSequent hL
  | _, .eqAxiom _ _ => True
  | _, .onePremise _ t => t.isProof
  | _, .twoPremise _ t₁ t₂ => t₁.isProof ∧ t₂.isProof

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Convert an LKₑ deduction tree whose leaves are axioms to an LKₑ proof
of the same sequent. At an arbitrary equality-axiom leaf, choose its schema
witness from `isProof`; all inference nodes are preserved. -/
noncomputable def toProofTree {L : Language} :
    {s : Sequent L} → (t : LKeDeductionTree s) → t.isProof → LKeProofTree s
  | _, .leaf s, hp => by
      classical
      by_cases hax : isFOLKAxiom s
      · exact .axiom_ s hax
      · have hEq : ∃ (hL : L.hasEquality = true) (ax : LKeEqualityAxiom L),
            s = ax.toSequent hL := hp.resolve_left hax
        let hL := Classical.choose hEq
        let ax := Classical.choose (Classical.choose_spec hEq)
        have hs : s = ax.toSequent hL := Classical.choose_spec (Classical.choose_spec hEq)
        exact hs.symm ▸ LKeProofTree.eqAxiom hL ax
  | _, .eqAxiom hL ax, _ => .eqAxiom hL ax
  | _, .onePremise rule t, hp => .onePremise rule (t.toProofTree hp)
  | _, .twoPremise rule t₁ t₂, hp =>
      .twoPremise rule (t₁.toProofTree hp.1) (t₂.toProofTree hp.2)

end LKeDeductionTree

-- ===================================================================
-- Definition 6.3.2: LKeCut.isAtomic
-- ===================================================================

namespace LKeCut

/-- Definition 6.3.2: A cut in an LKe-proof is atomic if its cut
formula is an atomic formula. The classification depends solely on
the formula, delegating to Formula.isAtomic from FirstOrder.Syntax. -/
@[blueprint "chap6__definition_6_3_2" (main := true)]
def isAtomic {L : Language} (A : FormulaN L) : Prop :=
  A.isAtomic

-- ===================================================================
-- Definition 6.3.2 (companion): LKeCut.isEssential
-- ===================================================================

/-- Definition 6.3.2: A cut in an LKe-proof is essential
if its cut formula is not an atomic formula. This is the negation of
isAtomic. -/
@[blueprint "chap6__definition_6_3_2" (main := true)]
def isEssential {L : Language} (A : FormulaN L) : Prop :=
  ¬ A.isAtomic

end LKeCut

-- ===================================================================
-- Definition 6.3.2 (companion def): LKeProofTree.conclusion
-- ===================================================================

namespace LKeProofTree

/-- Definition 6.3.1 (companion): The conclusion of an indexed LKe
proof tree is its type index. -/
@[blueprint "chap6__definition_6_3_1"]
def conclusion {L : Language} {s : Sequent L} (_ : LKeProofTree s) :
    Sequent L := s

/-- Lemma 6.5.1 (required helper): `y` is not bound anywhere in an
LKe proof tree. Ordinary and equality leaves inspect their exact
sequents; rule nodes inspect all indexed sequents and rule annotations
before recursively inspecting their subtrees. -/
@[blueprint "chap6__lemma_6_5_1"]
def notBoundIn {L : Language} :
    {s : Sequent L} → LKeProofTree s → Nat → Prop
  | s, .axiom_ _ _, y => sequentNotBoundIn s y
  | _, .eqAxiom hL ax, y => sequentNotBoundIn (ax.toSequent hL) y
  | _, .onePremise rule t, y =>
      rule.notBoundIn y ∧ t.notBoundIn y
  | _, .twoPremise rule t1 t2, y =>
      rule.notBoundIn y ∧ t1.notBoundIn y ∧ t2.notBoundIn y

/-- Lemma 6.5.1 (required helper): `z` has no free, bound, or
annotation-only occurrence anywhere in an LKe proof tree. Equality
axiom sequents expose all their terms, while rule nodes check their
indexed sequents, explicit annotations, and recursive premises. -/
@[blueprint "chap6__lemma_6_5_1"]
def varNotOccurs {L : Language} :
    {s : Sequent L} → LKeProofTree s → Nat → Prop
  | s, .axiom_ _ _, z => sequentVarNotOccurs s z
  | _, .eqAxiom hL ax, z => sequentVarNotOccurs (ax.toSequent hL) z
  | _, .onePremise rule t, z =>
      rule.varNotOccurs z ∧ t.varNotOccurs z
  | _, .twoPremise rule t1 t2, z =>
      rule.varNotOccurs z ∧ t1.varNotOccurs z ∧ t2.varNotOccurs z

/-- Lemma 6.5.1 (required helper): the constant symbol `c` occurs
somewhere in an LKe proof tree. The traversal includes every ordinary
rule node and annotation, every term represented by an equality-axiom
leaf, and all recursive subtrees. -/
@[blueprint "chap6__lemma_6_5_1"]
def constOccurs {L : Language} :
    {s : Sequent L} → LKeProofTree s → L.constSymbols → Prop
  | s, .axiom_ _ _, c => sequentConstOccurs s c
  | _, .eqAxiom hL ax, c => sequentConstOccurs (ax.toSequent hL) c
  | _, .onePremise rule t, c =>
      rule.constOccurs c ∨ t.constOccurs c
  | _, .twoPremise rule t1 t2, c =>
      rule.constOccurs c ∨ t1.constOccurs c ∨ t2.constOccurs c

end LKeProofTree

end LCS.CutElim.LKe
