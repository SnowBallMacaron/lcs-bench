import LCS.Item
import LCS.Util
import LCS.CutElim.CompletenessBridge
import LCS.CutElim.DecEqOfSymbols
import LCS.CutElim.LK.Syntax
import Attach
import LCS.CutElim.LK.Occurrences.ProofsStamp

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
namespace FOLKProofTree

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

end FOLKProofTree
end LCS.CutElim.LK
end
