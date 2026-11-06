import LCS.Item
import LCS.Util
import LCS.CutElim.CompletenessBridge
import LCS.CutElim.DecEqOfSymbols
import Attach
import LCS.CutElim.LK.Syntax.ProofsStamp

section
namespace LCS.CutElim.LK
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.CutElim.CompletenessBridge

/-- Definition 6.3.1 (required helper, general form, any equality flag):
A sequent is an LK axiom iff it
has the form [A] => [A] for some formula A. -/
@[blueprint "chap6__definition_6_3_1"]
def isFOLKAxiom {L : Language} (s : Sequent L) : Prop :=
  ∃ A : FormulaN L, s.antecedent = [A] ∧ s.succedent = [A]

-- ===================================================================
-- Definition 6.2.1 (indexed types): FOLKStep1 / FOLKStep2
-- ===================================================================
/-- Definition 6.3.1 (required helper, general form, any equality flag):
One-premise inference rules of LK, indexed by premise and
conclusion sequents. For quantifier rules, side conditions (free-for,
fresh variable) are fields of the constructor. The two logical rules
with a disjunctive premise in the textbook (`andLeft`, `orRight`) are
split here into constructors (`andLeftL`/`andLeftR`, `orRightL`/
`orRightR`) so each carries a single, definite premise shape. -/
@[blueprint "chap6__definition_6_3_1"]
inductive FOLKStep1 {L : Language} : Sequent L → Sequent L → Type where
  /-- Weakening left: from Gamma -> Delta infer A, Gamma -> Delta -/
  | weakenLeft (A : FormulaN L) (Γ Δ : List (FormulaN L)) :
      FOLKStep1 (Sequent.mk Γ Δ) (Sequent.mk (A :: Γ) Δ)
  /-- Weakening right: from Gamma -> Delta infer Gamma -> Delta, A -/
  | weakenRight (A : FormulaN L) (Γ Δ : List (FormulaN L)) :
      FOLKStep1 (Sequent.mk Γ Δ) (Sequent.mk Γ (Δ ++ [A]))
  /-- Contraction left: from A, A, Gamma -> Delta infer A, Gamma -> Delta -/
  | contractLeft (A : FormulaN L) (Γ Δ : List (FormulaN L)) :
      FOLKStep1 (Sequent.mk (A :: A :: Γ) Δ) (Sequent.mk (A :: Γ) Δ)
  /-- Contraction right: from Gamma -> Delta, A, A infer Gamma -> Delta, A -/
  | contractRight (A : FormulaN L) (Γ Δ : List (FormulaN L)) :
      FOLKStep1 (Sequent.mk Γ (Δ ++ [A, A])) (Sequent.mk Γ (Δ ++ [A]))
  /-- Exchange left: from Gamma, A, B, Delta -> Lambda infer
      Gamma, B, A, Delta -> Lambda -/
  | exchangeLeft (Γ : List (FormulaN L)) (A B : FormulaN L)
      (Δ Λ : List (FormulaN L)) :
      FOLKStep1 (Sequent.mk (Γ ++ [A, B] ++ Δ) Λ)
                (Sequent.mk (Γ ++ [B, A] ++ Δ) Λ)
  /-- Exchange right: from Gamma -> Delta, A, B, Lambda infer
      Gamma -> Delta, B, A, Lambda -/
  | exchangeRight (Γ Δ : List (FormulaN L)) (A B : FormulaN L)
      (Λ : List (FormulaN L)) :
      FOLKStep1 (Sequent.mk Γ (Δ ++ [A, B] ++ Λ))
                (Sequent.mk Γ (Δ ++ [B, A] ++ Λ))
  /-- Conjunction left (A-variant): from A, Gamma -> Delta infer
      A /\ B, Gamma -> Delta -/
  | andLeftL (A B : FormulaN L) (Γ Δ : List (FormulaN L)) :
      FOLKStep1 (Sequent.mk (A :: Γ) Δ)
                (Sequent.mk (FormulaN.conj A B :: Γ) Δ)
  /-- Conjunction left (B-variant): from B, Gamma -> Delta infer
      A /\ B, Gamma -> Delta -/
  | andLeftR (A B : FormulaN L) (Γ Δ : List (FormulaN L)) :
      FOLKStep1 (Sequent.mk (B :: Γ) Δ)
                (Sequent.mk (FormulaN.conj A B :: Γ) Δ)
  /-- Disjunction right (A-variant): from Gamma -> Delta, A infer
      Gamma -> Delta, A \/ B -/
  | orRightL (A B : FormulaN L) (Γ Δ : List (FormulaN L)) :
      FOLKStep1 (Sequent.mk Γ (Δ ++ [A]))
                (Sequent.mk Γ (Δ ++ [FormulaN.disj A B]))
  /-- Disjunction right (B-variant): from Gamma -> Delta, B infer
      Gamma -> Delta, A \/ B -/
  | orRightR (A B : FormulaN L) (Γ Δ : List (FormulaN L)) :
      FOLKStep1 (Sequent.mk Γ (Δ ++ [B]))
                (Sequent.mk Γ (Δ ++ [FormulaN.disj A B]))
  /-- Implication right: from A, Gamma -> Delta, B infer
      Gamma -> Delta, A => B -/
  | implRight (A B : FormulaN L) (Γ Δ : List (FormulaN L)) :
      FOLKStep1 (Sequent.mk (A :: Γ) (Δ ++ [B]))
                (Sequent.mk Γ (Δ ++ [FormulaN.impl A B]))
  /-- Negation left: from Gamma -> Delta, A infer not A, Gamma -> Delta -/
  | negLeft (A : FormulaN L) (Γ Δ : List (FormulaN L)) :
      FOLKStep1 (Sequent.mk Γ (Δ ++ [A]))
                (Sequent.mk (FormulaN.neg A :: Γ) Δ)
  /-- Negation right: from A, Gamma -> Delta infer Gamma -> Delta, not A -/
  | negRight (A : FormulaN L) (Γ Δ : List (FormulaN L)) :
      FOLKStep1 (Sequent.mk (A :: Γ) Δ)
                (Sequent.mk Γ (Δ ++ [FormulaN.neg A]))
  /-- Universal left: from A[t/x], Gamma -> Delta infer forall x A, Gamma -> Delta,
      where t is free for x in A -/
  | allLeft (t : Term L) (x : Nat) (A : FormulaN L)
      (Γ Δ : List (FormulaN L)) (hfree : isFreeForN t x A) :
      FOLKStep1 (Sequent.mk (formulaSubstN A t x :: Γ) Δ)
                (Sequent.mk (FormulaN.all x A :: Γ) Δ)
  /-- Universal right: from Gamma -> Delta, A[y/x] infer Gamma -> Delta, forall x A,
      where y is an eigenvariable not free in the conclusion -/
  | allRight (y : Nat) (x : Nat) (A : FormulaN L)
      (Γ Δ : List (FormulaN L))
      (hfresh : ∀ F ∈ (Sequent.mk Γ (Δ ++ [FormulaN.all x A])).antecedent ++
                       (Sequent.mk Γ (Δ ++ [FormulaN.all x A])).succedent,
                  y ∉ formulaFVN F)
      (hfreeFor : isFreeForN (Term.var y) x A) :
      FOLKStep1 (Sequent.mk Γ (Δ ++ [formulaSubstN A (Term.var y) x]))
                (Sequent.mk Γ (Δ ++ [FormulaN.all x A]))
  /-- Existential left: from A[y/x], Gamma -> Delta infer exists x A, Gamma -> Delta,
      where y is an eigenvariable not free in the conclusion -/
  | exLeft (y : Nat) (x : Nat) (A : FormulaN L)
      (Γ Δ : List (FormulaN L))
      (hfresh : ∀ F ∈ (Sequent.mk (FormulaN.ex x A :: Γ) Δ).antecedent ++
                       (Sequent.mk (FormulaN.ex x A :: Γ) Δ).succedent,
                  y ∉ formulaFVN F)
      (hfreeFor : isFreeForN (Term.var y) x A) :
      FOLKStep1 (Sequent.mk (formulaSubstN A (Term.var y) x :: Γ) Δ)
                (Sequent.mk (FormulaN.ex x A :: Γ) Δ)
  /-- Existential right: from Gamma -> Delta, A[t/x] infer Gamma -> Delta, exists x A,
      where t is free for x in A -/
  | exRight (t : Term L) (x : Nat) (A : FormulaN L)
      (Γ Δ : List (FormulaN L)) (hfree : isFreeForN t x A) :
      FOLKStep1 (Sequent.mk Γ (Δ ++ [formulaSubstN A t x]))
                (Sequent.mk Γ (Δ ++ [FormulaN.ex x A]))

/-- Definition 6.3.1 (required helper, general form, any equality flag):
Two-premise inference rules
of LK, indexed by premise and conclusion sequents. -/
@[blueprint "chap6__definition_6_3_1"]
inductive FOLKStep2 {L : Language} :
    Sequent L → Sequent L → Sequent L → Type where
  /-- Cut: from Gamma -> Delta, A and A, Lambda -> Theta infer
      Gamma, Lambda -> Delta, Theta. -/
  | cut (A : FormulaN L) (Γ Δ Λ Θ : List (FormulaN L)) :
      FOLKStep2 (Sequent.mk Γ (Δ ++ [A]))
                (Sequent.mk (A :: Λ) Θ)
                (Sequent.mk (Γ ++ Λ) (Δ ++ Θ))
  /-- Conjunction right: from Gamma -> Delta, A and Gamma -> Delta, B
      infer Gamma -> Delta, A /\ B -/
  | andRight (A B : FormulaN L) (Γ Δ : List (FormulaN L)) :
      FOLKStep2 (Sequent.mk Γ (Δ ++ [A]))
                (Sequent.mk Γ (Δ ++ [B]))
                (Sequent.mk Γ (Δ ++ [FormulaN.conj A B]))
  /-- Disjunction left: from A, Gamma -> Delta and B, Gamma -> Delta
      infer A \/ B, Gamma -> Delta -/
  | orLeft (A B : FormulaN L) (Γ Δ : List (FormulaN L)) :
      FOLKStep2 (Sequent.mk (A :: Γ) Δ)
                (Sequent.mk (B :: Γ) Δ)
                (Sequent.mk (FormulaN.disj A B :: Γ) Δ)
  /-- Implication left: from Gamma -> Delta, A and B, Lambda -> Theta
      infer A => B, Gamma, Lambda -> Delta, Theta -/
  | implLeft (A B : FormulaN L) (Γ Δ Λ Θ : List (FormulaN L)) :
      FOLKStep2 (Sequent.mk Γ (Δ ++ [A]))
                (Sequent.mk (B :: Λ) Θ)
                (Sequent.mk (FormulaN.impl A B :: Γ ++ Λ) (Δ ++ Θ))

/-- Lemma 6.5.3 (required helper, general form, any equality flag):
Proof trees for the Gentzen system LK, indexed
by their conclusion sequent. Structural validity is built into the
type: leaves must be LK axiom sequents, and each rule application
constrains its premise(s) to have the form mandated by the rule
(including side conditions for quantifier rules). No separate
WellFormed predicate is needed. -/
@[blueprint "chap6__lemma_6_5_3"]
inductive FOLKProofTree {L : Language} : Sequent L → Type where
  /-- Axiom leaf: a sequent of the form [A] => [A] -/
  | axiom_ (s : Sequent L) (h : isFOLKAxiom s) : FOLKProofTree s
  /-- One-premise rule application -/
  | onePremise {prem conc : Sequent L}
      (rule : FOLKStep1 prem conc)
      (t : FOLKProofTree prem) : FOLKProofTree conc
  /-- Two-premise rule application -/
  | twoPremise {prem1 prem2 conc : Sequent L}
      (rule : FOLKStep2 prem1 prem2 conc)
      (t1 : FOLKProofTree prem1) (t2 : FOLKProofTree prem2) :
      FOLKProofTree conc

namespace FOLKProofTree

/-- Lemma 6.5.3 (required helper, general form, any equality flag):
The conclusion of an indexed LK
proof tree is its type index. -/
@[blueprint "chap6__lemma_6_5_3"]
def conclusion {L : Language} {s : Sequent L} (_ : FOLKProofTree s) :
    Sequent L := s

/-- Lemma 6.5.4 (required helper, general form, any equality flag):
An LK proof tree is cut-free iff
no `cut` rule is used anywhere in it. -/
@[blueprint "chap6__lemma_6_5_4"]
def isCutFree {L : Language} : {s : Sequent L} → FOLKProofTree s → Prop
  | _, .axiom_ _ _ => True
  | _, .onePremise _ t => t.isCutFree
  | _, .twoPremise r t1 t2 =>
    (match r with | .cut .. => False | _ => True) ∧ t1.isCutFree ∧ t2.isCutFree

end FOLKProofTree

/-- Definition 6.2.1 (companion): Deduction trees for LK over a language
    without equality, indexed by
    conclusion sequent. Parallel to `FOLKProofTree` with free-form leaves.
    Textbook Def 6.2.1 implicitly admits both notions (following Def 3.4.5
    / Def 5.4.2). Proof trees are precisely the deduction trees whose leaves
    are all FOLK-axioms (see `FOLKDeductionTree.isProof` / `toProofTree`). -/
@[blueprint "chap6__definition_6_2_1"]
inductive FOLKDeductionTree {L : Language} (hL : L.withoutEquality) :
    Sequent L → Type where
  | leaf (s : Sequent L) : FOLKDeductionTree hL s
  | onePremise {prem conc : Sequent L}
      (rule : FOLKStep1 prem conc)
      (t : FOLKDeductionTree hL prem) : FOLKDeductionTree hL conc
  | twoPremise {prem1 prem2 conc : Sequent L}
      (rule : FOLKStep2 prem1 prem2 conc)
      (t1 : FOLKDeductionTree hL prem1) (t2 : FOLKDeductionTree hL prem2) :
      FOLKDeductionTree hL conc

namespace FOLKDeductionTree

/-- Definition 6.2.1 (companion): The conclusion of an indexed LK deduction
    tree over a language without equality is its type index. -/
@[blueprint "chap6__definition_6_2_1"]
def conclusion {L : Language} {hL : L.withoutEquality} {s : Sequent L}
    (_ : FOLKDeductionTree hL s) : Sequent L := s

/-- Definition 6.2.1 (companion): `isProof` predicate — true iff every leaf
    of the deduction tree over a language without equality is an LK-axiom sequent. -/
@[blueprint "chap6__definition_6_2_1"]
def isProof {L : Language} {hL : L.withoutEquality} :
    {s : Sequent L} → FOLKDeductionTree hL s → Prop
  | _, .leaf s => isFOLKAxiom s
  | _, .onePremise _ t => t.isProof
  | _, .twoPremise _ t1 t2 => t1.isProof ∧ t2.isProof

/-- Definition 6.2.1 (companion): Converts a deduction tree whose leaves
    are all LK-axioms into a `FOLKProofTree` of the same conclusion,
    over a language without equality. -/
def toProofTree {L : Language} {hL : L.withoutEquality} :
    {s : Sequent L} → (t : FOLKDeductionTree hL s) → t.isProof → FOLKProofTree s
  | _, .leaf s, hax => FOLKProofTree.axiom_ s hax
  | _, .onePremise rule t, hp => FOLKProofTree.onePremise rule (t.toProofTree hp)
  | _, .twoPremise rule t1 t2, hp =>
      FOLKProofTree.twoPremise rule (t1.toProofTree hp.1) (t2.toProofTree hp.2)

end FOLKDeductionTree

/-- Lemma 6.5.3 (required helper, general form, any equality flag):
A sequent is LK-provable if there
exists an indexed FOLKProofTree whose index is that sequent. -/
@[blueprint "chap6__lemma_6_5_3"]
def folkProvable {L : Language} (s : Sequent L) : Prop :=
  Nonempty (FOLKProofTree s)

/-- Lemma 6.5.4 (required helper, general form, any equality flag):
A sequent is LK-provable without
cut if there exists a cut-free FOLKProofTree with that conclusion. -/
@[blueprint "chap6__lemma_6_5_4"]
def folkCutFreeProvable {L : Language} (s : Sequent L) : Prop :=
  ∃ t : FOLKProofTree s, t.isCutFree

/-- Definition 6.2.1: One-premise LK rules over a language without equality. -/
@[blueprint "chap6__definition_6_2_1" (main := true)]
abbrev FOLKStep1NoEq {L : Language} (hL : L.withoutEquality) := @FOLKStep1 L

/-- Definition 6.2.1: Two-premise LK rules over a language without equality. -/
@[blueprint "chap6__definition_6_2_1" (main := true)]
abbrev FOLKStep2NoEq {L : Language} (hL : L.withoutEquality) := @FOLKStep2 L

/-- Definition 6.2.1 (companion): LK axioms over a language without equality. -/
@[blueprint "chap6__definition_6_2_1"]
def isFOLKAxiomNoEq {L : Language} (hL : L.withoutEquality) (s : Sequent L) : Prop :=
  isFOLKAxiom s

/-- Definition 6.2.1: Indexed LK proof trees over a language without equality. -/
@[blueprint "chap6__definition_6_2_1" (main := true)]
abbrev FOLKProofTreeNoEq {L : Language} (hL : L.withoutEquality) := @FOLKProofTree L

/-- Definition 6.2.1 (companion): LK-provability over a language without equality. -/
@[blueprint "chap6__definition_6_2_1"]
def folkProvableNoEq {L : Language} (hL : L.withoutEquality) (s : Sequent L) : Prop :=
  folkProvable s

/-- Definition 6.2.1 (companion): Sequents are equivalent when their
antecedents and succedents are respectively permutations. -/
@[blueprint "chap6__definition_6_2_1"]
def Sequent.permSetoid (L : Language) : Setoid (Sequent L) where
  r s s' := s.antecedent.Perm s'.antecedent ∧ s.succedent.Perm s'.succedent
  iseqv :=
    { refl := fun s => ⟨List.Perm.refl s.antecedent, List.Perm.refl s.succedent⟩
      symm := fun h => ⟨h.1.symm, h.2.symm⟩
      trans := fun h h' => ⟨h.1.trans h'.1, h.2.trans h'.2⟩ }

/-- Definition 6.2.1 (companion): Sequents viewed as pairs of multisets.
Their multiplicities are the list multiplicities; contraction and weakening
change these multiplicities. -/
@[blueprint "chap6__definition_6_2_1"]
def SequentMS (L : Language) : Type := Quotient (Sequent.permSetoid L)

end LCS.CutElim.LK
end
