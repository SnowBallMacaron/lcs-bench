import LCS.Item
import LCS.Util
import LCS.CutElim.CompletenessBridge
import LCS.CutElim.DecEqOfSymbols
import Attach
import LCS.CutElim.LK.Part1.ProofsStamp

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

-- ===================================================================
-- Lemma 6.5.1 (companion): proof-wide variable inspection
-- ===================================================================

/-- Lemma 6.5.1 (required helper): `y` is not bound in any formula of
the sequent. This is the upstream, sequent-level form of
`FormulaN.notBoundIn`, whose declaration lives in the downstream
cut-elimination module. -/
@[blueprint "chap6__lemma_6_5_1"]
def sequentNotBoundIn {L : Language} (s : Sequent L) (y : Nat) : Prop :=
  ∀ A ∈ s.antecedent ++ s.succedent, y ∉ formulaBVN A

/-- Lemma 6.5.1 (required helper): `z` has neither a free nor a bound
occurrence in `A`. -/
@[blueprint "chap6__lemma_6_5_1"]
def formulaVarNotOccurs {L : Language} (A : FormulaN L) (z : Nat) : Prop :=
  z ∉ formulaFVN A ∧ z ∉ formulaBVN A

/-- Lemma 6.5.1 (required helper): `z` has no occurrence in any formula
of the sequent. -/
@[blueprint "chap6__lemma_6_5_1"]
def sequentVarNotOccurs {L : Language} (s : Sequent L) (z : Nat) : Prop :=
  ∀ A ∈ s.antecedent ++ s.succedent, formulaVarNotOccurs A z

/-- Lemma 6.5.1 (required helper): the constant symbol `c` occurs in
the term `t`. This is intentionally independent of variable-freshness
predicates: it records positive symbol occurrence for the conditional
constant-substitution half of the lemma. -/
@[blueprint "chap6__lemma_6_5_1"]
def termConstOccurs {L : Language} : Term L → L.constSymbols → Prop
  | .var _, _ => False
  | .const d, c => c = d
  | .func _ ts, c => ∃ i, termConstOccurs (ts i) c

/-- Lemma 6.5.1 (required helper): the constant symbol `c` occurs in
the formula `A`, including inside every term argument. -/
@[blueprint "chap6__lemma_6_5_1"]
def formulaConstOccurs {L : Language} : FormulaN L → L.constSymbols → Prop
  | .predN _ ts, c => ∃ i, termConstOccurs (ts i) c
  | .eq_ _ t1 t2, c => termConstOccurs t1 c ∨ termConstOccurs t2 c
  | .neg A, c => formulaConstOccurs A c
  | .conj A B, c => formulaConstOccurs A c ∨ formulaConstOccurs B c
  | .disj A B, c => formulaConstOccurs A c ∨ formulaConstOccurs B c
  | .impl A B, c => formulaConstOccurs A c ∨ formulaConstOccurs B c
  | .all _ A, c => formulaConstOccurs A c
  | .ex _ A, c => formulaConstOccurs A c

/-- Lemma 6.5.1 (required helper): the constant symbol `c` occurs in
some formula on either side of the sequent. -/
@[blueprint "chap6__lemma_6_5_1"]
def sequentConstOccurs {L : Language} (s : Sequent L)
    (c : L.constSymbols) : Prop :=
  ∃ A ∈ s.antecedent ++ s.succedent, formulaConstOccurs A c

end LCS.CutElim.LK
end

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
namespace FOLKStep1

/-- Lemma 6.5.1 (required helper): `y` is not used as a binder anywhere
in a one-premise LK inference. Both indexed sequents are inspected, and
quantifier annotations are checked explicitly so the predicate remains
faithful even when an annotation disappears under instantiation. -/
@[blueprint "chap6__lemma_6_5_1"]
def notBoundIn {L : Language} {prem conc : Sequent L}
    (rule : FOLKStep1 prem conc) (y : Nat) : Prop :=
  sequentNotBoundIn prem y ∧ sequentNotBoundIn conc y ∧
    match rule with
    | .allLeft _ x A _ _ _ =>
        y ≠ x ∧ y ∉ formulaBVN A
    | .allRight _ x A _ _ _ _ =>
        y ≠ x ∧ y ∉ formulaBVN A
    | .exLeft _ x A _ _ _ _ =>
        y ≠ x ∧ y ∉ formulaBVN A
    | .exRight _ x A _ _ _ =>
        y ≠ x ∧ y ∉ formulaBVN A
    | _ => True

/-- Lemma 6.5.1 (required helper): `z` does not occur in a one-premise
LK inference. In addition to both indexed sequents, this checks every
quantifier binder, eigenvariable, and instantiating term carried only
as a rule annotation. -/
@[blueprint "chap6__lemma_6_5_1"]
def varNotOccurs {L : Language} {prem conc : Sequent L}
    (rule : FOLKStep1 prem conc) (z : Nat) : Prop :=
  sequentVarNotOccurs prem z ∧ sequentVarNotOccurs conc z ∧
    match rule with
    | .allLeft t x A _ _ _ =>
        z ∉ termFV t ∧ z ≠ x ∧ formulaVarNotOccurs A z
    | .allRight eigen x A _ _ _ _ =>
        z ≠ eigen ∧ z ≠ x ∧ formulaVarNotOccurs A z
    | .exLeft eigen x A _ _ _ _ =>
        z ≠ eigen ∧ z ≠ x ∧ formulaVarNotOccurs A z
    | .exRight t x A _ _ _ =>
        z ∉ termFV t ∧ z ≠ x ∧ formulaVarNotOccurs A z
    | _ => True

/-- Lemma 6.5.1 (required helper): the constant symbol `c` occurs in
a one-premise LK inference. Both indexed sequents and every principal
formula annotation are inspected. Quantifier instantiating terms are
checked explicitly because such a term may disappear when its bound
variable does not occur in the quantified formula. -/
@[blueprint "chap6__lemma_6_5_1"]
def constOccurs {L : Language} {prem conc : Sequent L}
    (rule : FOLKStep1 prem conc) (c : L.constSymbols) : Prop :=
  sequentConstOccurs prem c ∨ sequentConstOccurs conc c ∨
    match rule with
    | .weakenLeft A _ _ =>
        formulaConstOccurs A c
    | .weakenRight A _ _ =>
        formulaConstOccurs A c
    | .contractLeft A _ _ =>
        formulaConstOccurs A c
    | .contractRight A _ _ =>
        formulaConstOccurs A c
    | .exchangeLeft _ A B _ _ =>
        formulaConstOccurs A c ∨ formulaConstOccurs B c
    | .exchangeRight _ _ A B _ =>
        formulaConstOccurs A c ∨ formulaConstOccurs B c
    | .andLeftL A B _ _ =>
        formulaConstOccurs A c ∨ formulaConstOccurs B c
    | .andLeftR A B _ _ =>
        formulaConstOccurs A c ∨ formulaConstOccurs B c
    | .orRightL A B _ _ =>
        formulaConstOccurs A c ∨ formulaConstOccurs B c
    | .orRightR A B _ _ =>
        formulaConstOccurs A c ∨ formulaConstOccurs B c
    | .implRight A B _ _ =>
        formulaConstOccurs A c ∨ formulaConstOccurs B c
    | .negLeft A _ _ =>
        formulaConstOccurs A c
    | .negRight A _ _ =>
        formulaConstOccurs A c
    | .allLeft t _ A _ _ _ =>
        termConstOccurs t c ∨ formulaConstOccurs A c
    | .allRight _ _ A _ _ _ _ =>
        formulaConstOccurs A c
    | .exLeft _ _ A _ _ _ _ =>
        formulaConstOccurs A c
    | .exRight t _ A _ _ _ =>
        termConstOccurs t c ∨ formulaConstOccurs A c

end FOLKStep1
end LCS.CutElim.LK
end

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
namespace FOLKStep2

/-- Lemma 6.5.1 (required helper): `y` is not used as a binder in any
formula or annotation of a two-premise LK inference. -/
@[blueprint "chap6__lemma_6_5_1"]
def notBoundIn {L : Language} {prem1 prem2 conc : Sequent L}
    (rule : FOLKStep2 prem1 prem2 conc) (y : Nat) : Prop :=
  sequentNotBoundIn prem1 y ∧ sequentNotBoundIn prem2 y ∧
    sequentNotBoundIn conc y ∧
    match rule with
    | .cut A _ _ _ _ =>
        y ∉ formulaBVN A
    | .andRight A B _ _ =>
        y ∉ formulaBVN A ∧ y ∉ formulaBVN B
    | .orLeft A B _ _ =>
        y ∉ formulaBVN A ∧ y ∉ formulaBVN B
    | .implLeft A B _ _ _ _ =>
        y ∉ formulaBVN A ∧ y ∉ formulaBVN B

/-- Lemma 6.5.1 (required helper): `z` does not occur in either premise,
the conclusion, or any formula annotation of a two-premise LK
inference. -/
@[blueprint "chap6__lemma_6_5_1"]
def varNotOccurs {L : Language} {prem1 prem2 conc : Sequent L}
    (rule : FOLKStep2 prem1 prem2 conc) (z : Nat) : Prop :=
  sequentVarNotOccurs prem1 z ∧ sequentVarNotOccurs prem2 z ∧
    sequentVarNotOccurs conc z ∧
    match rule with
    | .cut A _ _ _ _ =>
        formulaVarNotOccurs A z
    | .andRight A B _ _ =>
        formulaVarNotOccurs A z ∧ formulaVarNotOccurs B z
    | .orLeft A B _ _ =>
        formulaVarNotOccurs A z ∧ formulaVarNotOccurs B z
    | .implLeft A B _ _ _ _ =>
        formulaVarNotOccurs A z ∧ formulaVarNotOccurs B z

/-- Lemma 6.5.1 (required helper): the constant symbol `c` occurs in
a two-premise LK inference. The traversal covers both premises, the
conclusion, and every principal formula annotation, including the cut
formula. -/
@[blueprint "chap6__lemma_6_5_1"]
def constOccurs {L : Language} {prem1 prem2 conc : Sequent L}
    (rule : FOLKStep2 prem1 prem2 conc) (c : L.constSymbols) : Prop :=
  sequentConstOccurs prem1 c ∨ sequentConstOccurs prem2 c ∨
    sequentConstOccurs conc c ∨
    match rule with
    | .cut A _ _ _ _ =>
        formulaConstOccurs A c
    | .andRight A B _ _ =>
        formulaConstOccurs A c ∨ formulaConstOccurs B c
    | .orLeft A B _ _ =>
        formulaConstOccurs A c ∨ formulaConstOccurs B c
    | .implLeft A B _ _ _ _ =>
        formulaConstOccurs A c ∨ formulaConstOccurs B c

end FOLKStep2
end LCS.CutElim.LK
end

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

end LCS.CutElim.LK
end

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
namespace FOLKProofTree

/-- Lemma 6.5.3 (required helper, general form, any equality flag):
The conclusion of an indexed LK
proof tree is its type index. -/
@[blueprint "chap6__lemma_6_5_3"]
def conclusion {L : Language} {s : Sequent L} (_ : FOLKProofTree s) :
    Sequent L := s



/-- Lemma 6.5.1 (required helper): `y` is not bound anywhere in an LK
proof tree. The recursion checks every node sequent and every rule
annotation, rather than only the root conclusion. -/
@[blueprint "chap6__lemma_6_5_1"]
def notBoundIn {L : Language} :
    {s : Sequent L} → FOLKProofTree s → Nat → Prop
  | s, .axiom_ _ _, y => sequentNotBoundIn s y
  | _, .onePremise rule t, y =>
      rule.notBoundIn y ∧ t.notBoundIn y
  | _, .twoPremise rule t1 t2, y =>
      rule.notBoundIn y ∧ t1.notBoundIn y ∧ t2.notBoundIn y

/-- Lemma 6.5.1 (required helper): `z` does not occur anywhere in an LK
proof tree. The recursion includes every node sequent and all
rule-only quantifier data: binders, eigenvariables, and instantiating
terms. -/
@[blueprint "chap6__lemma_6_5_1"]
def varNotOccurs {L : Language} :
    {s : Sequent L} → FOLKProofTree s → Nat → Prop
  | s, .axiom_ _ _, z => sequentVarNotOccurs s z
  | _, .onePremise rule t, z =>
      rule.varNotOccurs z ∧ t.varNotOccurs z
  | _, .twoPremise rule t1 t2, z =>
      rule.varNotOccurs z ∧ t1.varNotOccurs z ∧ t2.varNotOccurs z

/-- Lemma 6.5.1 (required helper): the constant symbol `c` occurs
somewhere in an LK proof tree. The recursion traverses every indexed
node sequent and every rule annotation, rather than inspecting only
the root conclusion. -/
@[blueprint "chap6__lemma_6_5_1"]
def constOccurs {L : Language} :
    {s : Sequent L} → FOLKProofTree s → L.constSymbols → Prop
  | s, .axiom_ _ _, c => sequentConstOccurs s c
  | _, .onePremise rule t, c =>
      rule.constOccurs c ∨ t.constOccurs c
  | _, .twoPremise rule t1 t2, c =>
      rule.constOccurs c ∨ t1.constOccurs c ∨ t2.constOccurs c

/-- Lemma 6.5.4 (required helper, general form, any equality flag):
An LK proof tree is cut-free iff
no `cut` rule is used anywhere in it. -/
@[blueprint "chap6__lemma_6_5_4"]
def isCutFree {L : Language} : {s : Sequent L} → FOLKProofTree s → Prop
  | _, .axiom_ _ _ => True
  | _, .onePremise _ t => t.isCutFree
  | _, .twoPremise r t1 t2 =>
    (match r with | .cut .. => False | _ => True) ∧ t1.isCutFree ∧ t2.isCutFree

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Lemma 6.4.8 (required helper): A FOLK proof-tree subtree is a
"weakening tower above an axiom" iff it consists only of axiom leaves
and `weakenLeft` / `weakenRight` rule applications. That is, the path
from the subtree's root down to its leaf contains only weakenings,
and the leaf is an axiom. Two-premise rules (cut, conjunction-right,
disjunction-left, implication-left) are forbidden in such a tower. -/
def isWeakeningAboveAxiom {L : Language} :
    {s : Sequent L} → FOLKProofTree s → Prop
  | _, .axiom_ _ _ => True
  | _, .onePremise rule t =>
    (match rule with
     | .weakenLeft _ _ _ => True
     | .weakenRight _ _ _ => True
     | _ => False) ∧ t.isWeakeningAboveAxiom
  | _, .twoPremise _ _ _ => False

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Lemma 6.4.8 (required helper): A FOLK proof tree is
weakening-normalized iff every use of `weakenLeft` or `weakenRight`
appears immediately above an axiom leaf, possibly through a
contiguous chain of further weakenings. Equivalently: at every node
whose applied rule IS a weakening, the subtree is an
`isWeakeningAboveAxiom` (i.e., only weakenings and axioms below); at
every node whose applied rule is NOT a weakening, the subtree(s) are
themselves weakening-normalized. This captures the textbook claim in
the proof sketch of Lem 6.4.8: "in an LKe-proof, all weakenings can
be moved above all other inferences." -/
def isWeakeningNormalized {L : Language} :
    {s : Sequent L} → FOLKProofTree s → Prop
  | _, .axiom_ _ _ => True
  | _, .onePremise rule t =>
    (match rule with
     | .weakenLeft _ _ _ => t.isWeakeningAboveAxiom
     | .weakenRight _ _ _ => t.isWeakeningAboveAxiom
     | _ => t.isWeakeningNormalized)
  | _, .twoPremise _ t1 t2 =>
    t1.isWeakeningNormalized ∧ t2.isWeakeningNormalized

end FOLKProofTree
end LCS.CutElim.LK
end

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

end LCS.CutElim.LK
end

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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
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
end LCS.CutElim.LK
end

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

-- ATTACH-BLOCKER: unsupported untagged abbrev
/-- Definition 6.2.1 (companion): Indexed LK deduction trees over a language
without equality. -/
abbrev FOLKDeductionTreeNoEq {L : Language} (hL : L.withoutEquality) :=
  @FOLKDeductionTree L hL

/-- Definition 6.2.1 (companion): LK-provability over a language without equality. -/
@[blueprint "chap6__definition_6_2_1"]
def folkProvableNoEq {L : Language} (hL : L.withoutEquality) (s : Sequent L) : Prop :=
  folkProvable s

/-- Definition 6.2.1 (companion): Cut-free LK-provability over a language
without equality. -/
@[blueprint "chap6__definition_6_2_1"]
def folkCutFreeProvableNoEq {L : Language} (hL : L.withoutEquality)
    (s : Sequent L) : Prop :=
  folkCutFreeProvable s

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Permuting either side of a sequent preserves LK-provability. -/
theorem folkProvable_perm {L : Language} {s s' : Sequent L}
    (hA : s.antecedent.Perm s'.antecedent)
    (hS : s.succedent.Perm s'.succedent) : folkProvable s ↔ folkProvable s' := by
  have left : ∀ {xs ys : List (FormulaN L)}, xs.Perm ys →
      ∀ pre Δ, folkProvable (Sequent.mk (pre ++ xs) Δ) →
        folkProvable (Sequent.mk (pre ++ ys) Δ) := by
    intro xs ys h
    induction h with
    | nil => intro pre Δ hp; exact hp
    | cons a _ ih =>
      intro pre Δ hp
      simpa [List.append_assoc] using
        ih (pre ++ [a]) Δ (by simpa [List.append_assoc] using hp)
    | swap a b tail =>
      intro pre Δ ⟨t⟩
      refine ⟨FOLKProofTree.onePremise ?_ t⟩
      simpa [List.append_assoc] using FOLKStep1.exchangeLeft pre b a tail Δ
    | trans _ _ ih1 ih2 =>
      intro pre Δ hp
      exact ih2 pre Δ (ih1 pre Δ hp)
  have right : ∀ {xs ys : List (FormulaN L)}, xs.Perm ys →
      ∀ Γ pre, folkProvable (Sequent.mk Γ (pre ++ xs)) →
        folkProvable (Sequent.mk Γ (pre ++ ys)) := by
    intro xs ys h
    induction h with
    | nil => intro Γ pre hp; exact hp
    | cons a _ ih =>
      intro Γ pre hp
      simpa [List.append_assoc] using
        ih Γ (pre ++ [a]) (by simpa [List.append_assoc] using hp)
    | swap a b tail =>
      intro Γ pre ⟨t⟩
      refine ⟨FOLKProofTree.onePremise ?_ t⟩
      simpa [List.append_assoc] using FOLKStep1.exchangeRight Γ pre b a tail
    | trans _ _ ih1 ih2 =>
      intro Γ pre hp
      exact ih2 Γ pre (ih1 Γ pre hp)
  rcases s with ⟨Γ, Δ⟩
  rcases s' with ⟨Γ', Δ'⟩
  exact ⟨fun hp => right hS Γ' [] (left hA [] Δ hp),
    fun hp => right hS.symm Γ [] (left hA.symm [] Δ' hp)⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 6.2.1 (companion): Over a language without equality,
permuting either side of a sequent preserves LK-provability. -/
theorem folkProvableNoEq_perm {L : Language} (hL : L.withoutEquality)
    {s s' : Sequent L} (hA : s.antecedent.Perm s'.antecedent)
    (hS : s.succedent.Perm s'.succedent) :
    folkProvableNoEq hL s ↔ folkProvableNoEq hL s' :=
  folkProvable_perm hA hS

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

/-- Definition 6.2.1 (companion): LK-provability on multiset sequents over
a language without equality, independent of the chosen list representatives. -/
@[blueprint "chap6__definition_6_2_1"]
def folkProvableMS {L : Language} (hL : L.withoutEquality) : SequentMS L → Prop :=
  Quotient.lift folkProvable (fun _ _ h => propext (folkProvableNoEq_perm hL h.1 h.2))



-- ===================================================================
-- Lemma 6.2.1: soundness_FOLK
-- ===================================================================

-- retained: used by LCS.CutElim.Interpolation.Equality.Reduction, LCS.CutElim.LKe.Equivalence.EqualityTranslation
/-- Lemma 6.2.1 (axioms valid): Every axiom of LK is valid. An axiom
has the form [A] => [A], which is trivially valid. -/
theorem lemma_6_2_1_axioms_valid {L : Language} (s : Sequent L)
    (h : isFOLKAxiom s) : sequentValid s := by
-- BEGIN PROOF
  obtain ⟨A, hAnt, hSucc⟩ := h
  intro M val hAll
  refine ⟨A, ?_, ?_⟩
  · rw [hSucc]; exact List.Mem.head _
  · exact hAll A (by rw [hAnt]; exact List.Mem.head _)

-- retained: used by LCS.CutElim.LKe.Equivalence.EqualityTranslation
/-- Lemma 6.2.1 (one-premise rules preserve validity): For every
one-premise rule of LK, if the premise is valid, then the conclusion
is valid. -/
theorem lemma_6_2_1_rules1_preserve_validity {L : Language}
    {prem conc : Sequent L} (rule : FOLKStep1 prem conc)
    (hprem : sequentValid prem) : sequentValid conc := by
-- BEGIN PROOF
  cases rule with
  | weakenLeft A Γ Δ =>
    intro M val hAll
    exact hprem M val (fun F hF => hAll F (List.Mem.tail _ hF))
  | weakenRight A Γ Δ =>
    intro M val hAll
    obtain ⟨B, hBmem, hBtrue⟩ := hprem M val hAll
    exact ⟨B, List.mem_append_left _ hBmem, hBtrue⟩
  | contractLeft A Γ Δ =>
    intro M val hAll
    apply hprem M val
    intro F hF
    have hF' : F ∈ (A :: A :: Γ) := hF
    match hF' with
    | .head _ => exact hAll F (List.Mem.head _)
    | .tail _ (.head _) => exact hAll F (List.Mem.head _)
    | .tail _ (.tail _ h) => exact hAll F (List.Mem.tail _ h)
  | contractRight A Γ Δ =>
    intro M val hAll
    obtain ⟨B, hBmem, hBtrue⟩ := hprem M val hAll
    have hBmem' : B ∈ Δ ++ [A, A] := hBmem
    have hB : B ∈ Δ ++ [A] := by
      rcases List.mem_append.mp hBmem' with h | h
      · exact List.mem_append_left _ h
      · match h with
        | .head _ => exact List.mem_append_right _ (List.Mem.head _)
        | .tail _ (.head _) => exact List.mem_append_right _ (List.Mem.head _)
        | .tail _ (.tail _ h) => exact (nomatch h)
    exact ⟨B, hB, hBtrue⟩
  | exchangeLeft Γ A B Δ' Λ =>
    intro M val hAll
    apply hprem M val
    intro F hF
    have hF' : F ∈ Γ ++ [A, B] ++ Δ' := hF
    have : F ∈ Γ ++ [B, A] ++ Δ' := by
      rcases List.mem_append.mp hF' with h | h
      · rcases List.mem_append.mp h with h1 | h1
        · exact List.mem_append_left _ (List.mem_append_left _ h1)
        · match h1 with
          | .head _ =>
            exact List.mem_append_left _
              (List.mem_append_right _ (.tail _ (.head _)))
          | .tail _ (.head _) =>
            exact List.mem_append_left _
              (List.mem_append_right _ (.head _))
          | .tail _ (.tail _ h1) => exact (nomatch h1)
      · exact List.mem_append_right _ h
    exact hAll F this
  | exchangeRight Γ Δ' A B Λ =>
    intro M val hAll
    obtain ⟨F, hFmem, hFtrue⟩ := hprem M val hAll
    have hFmem' : F ∈ Δ' ++ [A, B] ++ Λ := hFmem
    have hF : F ∈ Δ' ++ [B, A] ++ Λ := by
      rcases List.mem_append.mp hFmem' with h | h
      · rcases List.mem_append.mp h with h1 | h1
        · exact List.mem_append_left _ (List.mem_append_left _ h1)
        · match h1 with
          | .head _ =>
            exact List.mem_append_left _
              (List.mem_append_right _ (.tail _ (.head _)))
          | .tail _ (.head _) =>
            exact List.mem_append_left _
              (List.mem_append_right _ (.head _))
          | .tail _ (.tail _ h1) => exact (nomatch h1)
      · exact List.mem_append_right _ h
    exact ⟨F, hF, hFtrue⟩
  | andLeftL A B Γ Δ' =>
    intro M val hAll
    apply hprem M val
    intro F hF
    have hF' : F ∈ (A :: Γ) := hF
    match hF' with
    | .head _ =>
      have hconj := hAll (FormulaN.conj F B) (List.Mem.head _)
      simp [formulaEvalN] at hconj
      exact hconj.1
    | .tail _ h => exact hAll F (List.Mem.tail _ h)
  | andLeftR A B Γ Δ' =>
    intro M val hAll
    apply hprem M val
    intro F hF
    have hF' : F ∈ (B :: Γ) := hF
    match hF' with
    | .head _ =>
      have hconj := hAll (FormulaN.conj A F) (List.Mem.head _)
      simp [formulaEvalN] at hconj
      exact hconj.2
    | .tail _ h => exact hAll F (List.Mem.tail _ h)
  | orRightL A B Γ Δ' =>
    intro M val hAll
    obtain ⟨F, hFmem, hFtrue⟩ := hprem M val hAll
    have hFmem' : F ∈ Δ' ++ [A] := hFmem
    rcases List.mem_append.mp hFmem' with hd | ha
    · exact ⟨F, List.mem_append_left _ hd, hFtrue⟩
    · match ha with
      | .head _ =>
        refine ⟨FormulaN.disj F B,
          List.mem_append_right _ (List.Mem.head _), ?_⟩
        simp [formulaEvalN]; left; exact hFtrue
      | .tail _ ha => exact (nomatch ha)
  | orRightR A B Γ Δ' =>
    intro M val hAll
    obtain ⟨F, hFmem, hFtrue⟩ := hprem M val hAll
    have hFmem' : F ∈ Δ' ++ [B] := hFmem
    rcases List.mem_append.mp hFmem' with hd | ha
    · exact ⟨F, List.mem_append_left _ hd, hFtrue⟩
    · match ha with
      | .head _ =>
        refine ⟨FormulaN.disj A F,
          List.mem_append_right _ (List.Mem.head _), ?_⟩
        simp [formulaEvalN]; right; exact hFtrue
      | .tail _ ha => exact (nomatch ha)
  | implRight A B Γ Δ' =>
    intro M val hAll
    by_cases hA : formulaEvalN M A val
    · obtain ⟨F, hFmem, hFtrue⟩ := hprem M val (fun G hG => by
        have hG' : G ∈ (A :: Γ) := hG
        match hG' with
        | .head _ => exact hA
        | .tail _ h => exact hAll G h)
      have hFmem' : F ∈ Δ' ++ [B] := hFmem
      rcases List.mem_append.mp hFmem' with h | h
      · exact ⟨F, List.mem_append_left _ h, hFtrue⟩
      · match h with
        | .head _ =>
          refine ⟨FormulaN.impl A F,
            List.mem_append_right _ (List.Mem.head _), ?_⟩
          simp [formulaEvalN]; intro; exact hFtrue
        | .tail _ h => exact (nomatch h)
    · refine ⟨FormulaN.impl A B,
        List.mem_append_right _ (List.Mem.head _), ?_⟩
      simp [formulaEvalN]; intro hA'; exact absurd hA' hA
  | negLeft A Γ Δ' =>
    intro M val hAll
    have hneg := hAll (FormulaN.neg A) (List.Mem.head _)
    simp [formulaEvalN] at hneg
    have hΓ : ∀ F ∈ Γ, formulaEvalN M F val := fun F hF =>
      hAll F (List.Mem.tail _ hF)
    obtain ⟨F, hFmem, hFtrue⟩ := hprem M val hΓ
    have hFmem' : F ∈ Δ' ++ [A] := hFmem
    rcases List.mem_append.mp hFmem' with h | h
    · exact ⟨F, h, hFtrue⟩
    · match h with
      | .head _ => exact absurd hFtrue hneg
      | .tail _ h => exact (nomatch h)
  | negRight A Γ Δ' =>
    intro M val hAll
    by_cases hA : formulaEvalN M A val
    · obtain ⟨F, hFmem, hFtrue⟩ := hprem M val (fun G hG => by
        have hG' : G ∈ (A :: Γ) := hG
        match hG' with
        | .head _ => exact hA
        | .tail _ h => exact hAll G h)
      exact ⟨F, List.mem_append_left _ hFmem, hFtrue⟩
    · refine ⟨FormulaN.neg A,
        List.mem_append_right _ (List.Mem.head _), ?_⟩
      simp [formulaEvalN]; exact hA
  | allLeft t_sub x A Γ Δ' hfree =>
    intro M val hAll
    apply hprem M val
    intro F hF
    have hF' : F ∈ (formulaSubstN A t_sub x :: Γ) := hF
    cases hF' with
    | head =>
      have hall := hAll (FormulaN.all x A) (List.Mem.head _)
      simp [formulaEvalN] at hall
      exact (formulaSubstEvalDirectN val A t_sub x hfree).mpr
        (hall (termEval M val t_sub))
    | tail _ h => exact hAll F (List.Mem.tail _ h)
  | allRight y_eig x A Γ Δ' hfresh hfreeFor =>
    intro M val hAll
    by_cases hΔ : ∃ B ∈ Δ', formulaEvalN M B val
    · obtain ⟨B, hB, hBt⟩ := hΔ
      exact ⟨B, List.mem_append_left _ hB, hBt⟩
    · suffices hall : ∀ a, formulaEvalN M A (assignUpdate val x a) from
        ⟨FormulaN.all x A,
          List.mem_append_right _ (List.Mem.head _), hall⟩
      intro a
      have hfreshΓ : ∀ F ∈ Γ, y_eig ∉ formulaFVN F := fun F hF =>
        hfresh F (List.mem_append_left _ hF)
      have hfreshSucc : ∀ F ∈ Δ' ++ [FormulaN.all x A],
          y_eig ∉ formulaFVN F := fun F hF =>
        hfresh F (List.mem_append_right _ hF)
      have hfreshΔ : ∀ F ∈ Δ', y_eig ∉ formulaFVN F := fun F hF =>
        hfreshSucc F (List.mem_append_left _ hF)
      have hantY : ∀ F ∈ Γ,
          formulaEvalN M F (assignUpdate val y_eig a) := fun F hF => by
        have hFs := hAll F hF
        exact (coincidenceLemmaN M F val (assignUpdate val y_eig a)
          (fun y hy => by
            simp [assignUpdate]; intro hzy
            exact absurd (hzy ▸ hy) (hfreshΓ F hF))).mp hFs
      obtain ⟨B, hBmem, hBtrue⟩ :=
        hprem M (assignUpdate val y_eig a) hantY
      have hBmem' : B ∈ Δ' ++ [formulaSubstN A (Term.var y_eig) x] := hBmem
      rcases List.mem_append.mp hBmem' with hBΔ | hBsub
      · have hBs : formulaEvalN M B val := by
          exact (coincidenceLemmaN M B (assignUpdate val y_eig a) val
            (fun y hy => by
              simp [assignUpdate]; intro hzy
              exact absurd (hzy ▸ hy) (hfreshΔ B hBΔ))).mp hBtrue
        exact absurd ⟨B, hBΔ, hBs⟩ hΔ
      · have hBeq : B = formulaSubstN A (Term.var y_eig) x := by
          cases hBsub with
          | head => rfl
          | tail _ h => exact (nomatch h)
        subst hBeq
        rw [formulaSubstEvalDirectN (assignUpdate val y_eig a) A
            (Term.var y_eig) x hfreeFor] at hBtrue
        simp [termEval, assignUpdate] at hBtrue
        have yA : ∀ z, z ∈ formulaFVN A → z ≠ x → z ≠ y_eig := by
          intro z hz hzx hzy; subst hzy
          exact hfreshSucc (FormulaN.all x A)
            (List.mem_append_right _ (List.Mem.head _))
            (by simp [formulaFVN]; exact ⟨hz, hzx⟩)
        exact (coincidenceLemmaN M A
          (fun k => if k = x then a
                    else if k = y_eig then a else val k)
          (assignUpdate val x a)
          (fun z hz => by
            simp [assignUpdate]
            split
            · rfl
            · rename_i hzx; split
              · rename_i hzy
                exact absurd hzy (yA z hz hzx)
              · rfl)).mp hBtrue
  | exLeft y_eig x A Γ Δ' hfresh hfreeFor =>
    intro M val hAll
    have hexA := hAll (FormulaN.ex x A) (List.Mem.head _)
    simp [formulaEvalN] at hexA
    obtain ⟨a, ha⟩ := hexA
    have hfreshΓ : ∀ F ∈ Γ, y_eig ∉ formulaFVN F := fun F hF =>
      hfresh F (List.mem_append_left _ (List.Mem.tail _ hF))
    have hfreshΔ : ∀ F ∈ Δ', y_eig ∉ formulaFVN F := fun F hF =>
      hfresh F (List.mem_append_right _ hF)
    have yA : ∀ z, z ∈ formulaFVN A → z ≠ x → z ≠ y_eig := by
      intro z hz hzx hzy; subst hzy
      exact hfresh (FormulaN.ex x A)
        (List.mem_append_left _ (List.Mem.head _))
        (by simp [formulaFVN]; exact ⟨hz, hzx⟩)
    have hAyx : formulaEvalN M (formulaSubstN A (Term.var y_eig) x)
        (assignUpdate val y_eig a) := by
      rw [formulaSubstEvalDirectN (assignUpdate val y_eig a) A
        (Term.var y_eig) x hfreeFor]
      simp [termEval, assignUpdate]
      exact (coincidenceLemmaN M A (assignUpdate val x a)
        (fun k => if k = x then a
                  else if k = y_eig then a else val k)
        (fun z hz => by
          simp [assignUpdate]
          split
          · rfl
          · rename_i hzx; split
            · rename_i hzy
              exact absurd hzy (yA z hz hzx)
            · rfl)).mp ha
    have hΓy : ∀ F ∈ Γ,
        formulaEvalN M F (assignUpdate val y_eig a) := fun F hF => by
      have hFs := hAll F (List.Mem.tail _ hF)
      exact (coincidenceLemmaN M F val (assignUpdate val y_eig a)
        (fun y hy => by
          simp [assignUpdate]; intro hzy
          exact absurd (hzy ▸ hy) (hfreshΓ F hF))).mp hFs
    have hantY : ∀ F ∈ (formulaSubstN A (Term.var y_eig) x :: Γ),
        formulaEvalN M F (assignUpdate val y_eig a) := by
      intro F hF
      cases hF with
      | head => exact hAyx
      | tail _ h => exact hΓy F h
    obtain ⟨B, hBmem, hBtrue⟩ :=
      hprem M (assignUpdate val y_eig a) hantY
    exact ⟨B, hBmem, by
      exact (coincidenceLemmaN M B (assignUpdate val y_eig a) val
        (fun y hy => by
          simp [assignUpdate]; intro hzy
          exact absurd (hzy ▸ hy) (hfreshΔ B hBmem))).mp hBtrue⟩
  | exRight t_sub x A Γ Δ' hfree =>
    intro M val hAll
    obtain ⟨F, hFmem, hFtrue⟩ := hprem M val hAll
    have hFmem' : F ∈ Δ' ++ [formulaSubstN A t_sub x] := hFmem
    rcases List.mem_append.mp hFmem' with h | h
    · exact ⟨F, List.mem_append_left _ h, hFtrue⟩
    · have hFeq : F = formulaSubstN A t_sub x := by
        cases h with
        | head => rfl
        | tail _ h => exact (nomatch h)
      subst hFeq
      refine ⟨FormulaN.ex x A,
        List.mem_append_right _ (List.Mem.head _), ?_⟩
      simp [formulaEvalN]
      exact ⟨termEval M val t_sub,
        (formulaSubstEvalDirectN val A t_sub x hfree).mp hFtrue⟩
-- retained: used by LCS.CutElim.LKe.Equivalence.EqualityTranslation
/-- Lemma 6.2.1 (two-premise rules preserve validity): For every
two-premise rule of LK (including cut), if both premises are valid,
then the conclusion is valid. -/
theorem lemma_6_2_1_rules2_preserve_validity {L : Language}
    {prem1 prem2 conc : Sequent L} (rule : FOLKStep2 prem1 prem2 conc)
    (hprem1 : sequentValid prem1) (hprem2 : sequentValid prem2) :
    sequentValid conc := by
-- BEGIN PROOF
  cases rule with
  | cut A Γ Δ' Λ Θ =>
    intro M val hAll
    have hΓ : ∀ F ∈ Γ, formulaEvalN M F val := fun F hF =>
      hAll F (List.mem_append_left _ hF)
    have hΛ : ∀ F ∈ Λ, formulaEvalN M F val := fun F hF =>
      hAll F (List.mem_append_right _ hF)
    obtain ⟨B, hBmem, hBtrue⟩ := hprem1 M val hΓ
    have hBmem' : B ∈ Δ' ++ [A] := hBmem
    rcases List.mem_append.mp hBmem' with h | h
    · exact ⟨B, List.mem_append_left _ h, hBtrue⟩
    · match h with
      | .head _ =>
        obtain ⟨C, hCmem, hCtrue⟩ := hprem2 M val (fun F hF => by
          have hF' : F ∈ (B :: Λ) := hF
          match hF' with
          | .head _ => exact hBtrue
          | .tail _ h => exact hΛ F h)
        exact ⟨C, List.mem_append_right _ hCmem, hCtrue⟩
      | .tail _ h => exact (nomatch h)
  | andRight A B Γ Δ' =>
    intro M val hAll
    obtain ⟨F1, hF1mem, hF1true⟩ := hprem1 M val hAll
    have hF1mem' : F1 ∈ Δ' ++ [A] := hF1mem
    rcases List.mem_append.mp hF1mem' with h | h
    · exact ⟨F1, List.mem_append_left _ h, hF1true⟩
    · match h with
      | .head _ =>
        obtain ⟨F2, hF2mem, hF2true⟩ := hprem2 M val hAll
        have hF2mem' : F2 ∈ Δ' ++ [B] := hF2mem
        rcases List.mem_append.mp hF2mem' with h2 | h2
        · exact ⟨F2, List.mem_append_left _ h2, hF2true⟩
        · match h2 with
          | .head _ =>
            refine ⟨FormulaN.conj F1 F2,
              List.mem_append_right _ (List.Mem.head _), ?_⟩
            simp [formulaEvalN]
            exact ⟨hF1true, hF2true⟩
          | .tail _ h2 => exact (nomatch h2)
      | .tail _ h => exact (nomatch h)
  | orLeft A B Γ Δ' =>
    intro M val hAll
    have hdisj := hAll (FormulaN.disj A B) (List.Mem.head _)
    simp [formulaEvalN] at hdisj
    have hΓ : ∀ F ∈ Γ, formulaEvalN M F val := fun F hF =>
      hAll F (List.Mem.tail _ hF)
    cases hdisj with
    | inl hA =>
      apply hprem1 M val
      intro F hF
      have hF' : F ∈ (A :: Γ) := hF
      match hF' with
      | .head _ => exact hA
      | .tail _ h => exact hΓ F h
    | inr hB =>
      apply hprem2 M val
      intro F hF
      have hF' : F ∈ (B :: Γ) := hF
      match hF' with
      | .head _ => exact hB
      | .tail _ h => exact hΓ F h
  | implLeft A B Γ Δ' Λ Θ =>
    intro M val hAll
    have himpl := hAll (FormulaN.impl A B) (List.Mem.head _)
    simp [formulaEvalN] at himpl
    have hΓ : ∀ F ∈ Γ, formulaEvalN M F val := fun F hF =>
      hAll F (List.Mem.tail _ (List.mem_append_left _ hF))
    have hΛ : ∀ F ∈ Λ, formulaEvalN M F val := fun F hF =>
      hAll F (List.Mem.tail _ (List.mem_append_right _ hF))
    obtain ⟨F1, hF1mem, hF1true⟩ := hprem1 M val hΓ
    have hF1mem' : F1 ∈ Δ' ++ [A] := hF1mem
    rcases List.mem_append.mp hF1mem' with h | h
    · exact ⟨F1, List.mem_append_left _ h, hF1true⟩
    · match h with
      | .head _ =>
        have hB := himpl hF1true
        obtain ⟨F2, hF2mem, hF2true⟩ := hprem2 M val (fun F hF => by
          have hF' : F ∈ (B :: Λ) := hF
          match hF' with
          | .head _ => exact hB
          | .tail _ h => exact hΛ F h)
        exact ⟨F2, List.mem_append_right _ hF2mem, hF2true⟩
      | .tail _ h => exact (nomatch h)

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.LK.Part2, LCS.FOResolution.Method.Completeness.Completeness
/-- Helper: proofTreeValid — induction on the indexed FOLKProofTree
establishes validity of the (indexed) conclusion. The per-rule
validity arguments are delegated to the Lemma 6.2.1 companion
theorems `lemma_6_2_1_rules1_preserve_validity` and
`lemma_6_2_1_rules2_preserve_validity`. -/
theorem proofTreeValid {L : Language} {s : Sequent L}
    (t : FOLKProofTree s) : sequentValid s := by
-- BEGIN PROOF
  induction t with
  | axiom_ s hax => exact lemma_6_2_1_axioms_valid s hax
  | onePremise rule _t ih =>
    exact lemma_6_2_1_rules1_preserve_validity rule ih
  | twoPremise rule _t1 _t2 ih1 ih2 =>
    exact lemma_6_2_1_rules2_preserve_validity rule ih1 ih2

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.LK.Part2, LCS.FOResolution.Method.Completeness.Completeness
/-- Lemma 6.2.1 (provable sequent valid): Every LK-provable sequent
is valid. -/
theorem soundness_FOLK {L : Language} (seq : Sequent L)
    (h : folkProvable seq) : sequentValid seq := by
-- BEGIN PROOF
  obtain ⟨t⟩ := h
  exact proofTreeValid t











/-- Lemma 6.2.1: Over a language without equality, every LK axiom is valid,
every LK rule preserves validity, and every LK-provable sequent is valid. -/
@[blueprint "chap6__lemma_6_2_1" (main := true)]
theorem lemma_6_2_1NoEq {L : Language} (hL : L.withoutEquality) :
    (∀ s : Sequent L, isFOLKAxiomNoEq hL s → sequentValid s) ∧
    (∀ {prem conc : Sequent L}, (rule : FOLKStep1NoEq hL prem conc) →
      sequentValid prem → sequentValid conc) ∧
    (∀ {prem1 prem2 conc : Sequent L}, (rule : FOLKStep2NoEq hL prem1 prem2 conc) →
      sequentValid prem1 → sequentValid prem2 → sequentValid conc) ∧
    (∀ seq : Sequent L, folkProvableNoEq hL seq → sequentValid seq) 



/-- Lemma 6.2.1 (companion): LK rules do not universally preserve validity
from conclusion to premise over languages without equality. Under the
system-level reading of “not necessarily” (OD-A18), a language with one
nullary predicate supplies a right-weakening counterexample. -/
@[blueprint "chap6__lemma_6_2_1"]
theorem lk_rules_not_invertible :
    ¬ ∀ (L : Language) (hL : L.withoutEquality)
      {prem conc : Sequent L} (r : FOLKStep1NoEq hL prem conc),
      sequentValid conc → sequentValid prem 

-- ===================================================================
-- Helper lemmas for folkCutFreeProvable
-- ===================================================================

-- retained: used by LCS.CutElim.LK.Part2
theorem folkCutFree_weakenLeft {L : Language}
    (B : FormulaN L) (Γ Δ : List (FormulaN L))
    (h : folkCutFreeProvable (Sequent.mk Γ Δ)) :
    folkCutFreeProvable (Sequent.mk (B :: Γ) Δ) := by
-- BEGIN PROOF
  obtain ⟨t, hcf⟩ := h
  exact ⟨.onePremise (.weakenLeft B Γ Δ) t, hcf⟩

-- retained: used by LCS.CutElim.LK.Part2
theorem folkCutFree_weakenRight {L : Language}
    (B : FormulaN L) (Γ Δ : List (FormulaN L))
    (h : folkCutFreeProvable (Sequent.mk Γ Δ)) :
    folkCutFreeProvable (Sequent.mk Γ (Δ ++ [B])) := by
-- BEGIN PROOF
  obtain ⟨t, hcf⟩ := h
  exact ⟨.onePremise (.weakenRight B Γ Δ) t, hcf⟩

-- retained: used by LCS.CutElim.Interpolation.Equality.Axioms, LCS.CutElim.Interpolation.Equality.Replay, LCS.CutElim.LK.Part2, LCS.CutElim.LKe.Equivalence.Validity
theorem folkCutFree_axiom {L : Language} (A : FormulaN L) :
    folkCutFreeProvable (Sequent.mk [A] [A]) :=
-- BEGIN PROOF
  ⟨.axiom_ (Sequent.mk [A] [A]) ⟨A, rfl, rfl⟩, trivial⟩

-- retained: used by LCS.CutElim.LK.Part2
theorem folkCutFree_weakenLeftList {L : Language}
    (Γ' Γ Δ : List (FormulaN L))
    (h : folkCutFreeProvable (Sequent.mk Γ Δ)) :
    folkCutFreeProvable (Sequent.mk (Γ' ++ Γ) Δ) := by
-- BEGIN PROOF
  induction Γ' with
  | nil => simp; exact h
  | cons B rest ih =>
    exact folkCutFree_weakenLeft B (rest ++ Γ) Δ ih

-- retained: used by LCS.CutElim.LK.Part2
theorem folkCutFree_weakenRightList {L : Language}
    (Δ' Γ Δ : List (FormulaN L))
    (h : folkCutFreeProvable (Sequent.mk Γ Δ)) :
    folkCutFreeProvable (Sequent.mk Γ (Δ ++ Δ')) := by
-- BEGIN PROOF
  induction Δ' generalizing Δ with
  | nil => simp; exact h
  | cons B rest ih =>
    have h1 : folkCutFreeProvable (Sequent.mk Γ (Δ ++ [B])) :=
      folkCutFree_weakenRight B Γ Δ h
    have h2 := ih (Δ ++ [B]) h1
    rwa [List.append_assoc] at h2

-- retained: used by LCS.CutElim.LK.Part2
theorem folkCutFree_contractLeft_head {L : Language}
    (A : FormulaN L) (Γ Δ : List (FormulaN L))
    (h : folkCutFreeProvable (Sequent.mk (A :: A :: Γ) Δ)) :
    folkCutFreeProvable (Sequent.mk (A :: Γ) Δ) := by
-- BEGIN PROOF
  obtain ⟨t, hcf⟩ := h
  exact ⟨.onePremise (.contractLeft A Γ Δ) t, hcf⟩

-- retained: used by LCS.CutElim.LK.Part2
theorem folkCutFree_contractRight_end {L : Language}
    (A : FormulaN L) (Γ Δ : List (FormulaN L))
    (h : folkCutFreeProvable (Sequent.mk Γ (Δ ++ [A, A]))) :
    folkCutFreeProvable (Sequent.mk Γ (Δ ++ [A])) := by
-- BEGIN PROOF
  obtain ⟨t, hcf⟩ := h
  exact ⟨.onePremise (.contractRight A Γ Δ) t, hcf⟩

-- retained: used by LCS.CutElim.LK.Part2
theorem folkCutFree_exchangeLeft_adj {L : Language}
    (Γ : List (FormulaN L)) (A B : FormulaN L)
    (Δ Λ : List (FormulaN L))
    (h : folkCutFreeProvable (Sequent.mk (Γ ++ [A, B] ++ Δ) Λ)) :
    folkCutFreeProvable (Sequent.mk (Γ ++ [B, A] ++ Δ) Λ) := by
-- BEGIN PROOF
  obtain ⟨t, hcf⟩ := h
  exact ⟨.onePremise (.exchangeLeft Γ A B Δ Λ) t, hcf⟩

-- retained: used by LCS.CutElim.LK.Part2
theorem folkCutFree_exchangeRight_adj {L : Language}
    (Γ Δ : List (FormulaN L)) (A B : FormulaN L)
    (Λ : List (FormulaN L))
    (h : folkCutFreeProvable (Sequent.mk Γ (Δ ++ [A, B] ++ Λ))) :
    folkCutFreeProvable (Sequent.mk Γ (Δ ++ [B, A] ++ Λ)) := by
-- BEGIN PROOF
  obtain ⟨t, hcf⟩ := h
  exact ⟨.onePremise (.exchangeRight Γ Δ A B Λ) t, hcf⟩

-- Equality transport for folkCutFreeProvable
-- retained: used by LCS.CutElim.LK.Part2
theorem folkCutFree_of_eq {L : Language} {s1 s2 : Sequent L}
    (heq : s1 = s2) (h : folkCutFreeProvable s1) :
    folkCutFreeProvable s2 := heq ▸ h

end LCS.CutElim.LK
end

