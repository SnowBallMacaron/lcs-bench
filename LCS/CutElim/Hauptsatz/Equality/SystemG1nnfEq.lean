import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.CutElimination
import LCS.FirstOrder.Semantics
import Attach
import LCS.CutElim.Hauptsatz.Equality.SystemG1nnfEq.ProofsStamp

section
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SyntaxN.Substitution LCS.FirstOrder.SyntaxN.Variables
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS
namespace LCS.CutElim.Hauptsatz.Equality

/-- Definition 6.4.6: The equality axiom schemas for the system
G1^nnf_=. The three textbook base schemas are: (i) reflexivity:
Gamma -> Delta, t = t; (ii) function congruence: for every n-ary
function symbol f, Gamma, s_1 = t_1, ..., s_n = t_n -> Delta,
f(s_1,...,s_n) = f(t_1,...,t_n); (iii) predicate congruence: for
every n-ary predicate symbol P (including =),
Gamma, s_1 = t_1, ..., s_n = t_n, P(s_1,...,s_n) -> Delta,
P(t_1,...,t_n). The Lean carrier uses a fourth base constructor for
the equality-predicate instance because equality is represented by
`FormulaN.eq_`, not `L.predSymbols`. Additionally, all sequents obtained
from the above by applications of negation-left and negation-right rules
to their explicitly designated positive atomic formulae are included. -/
@[blueprint "chap6__definition_6_4_6" (main := true)]
inductive G1nnfEqAxiom (L : Language) (hL : L.hasEquality = true) : Type where
  /-- Reflexivity axiom (i): Gamma -> Delta, t = t -/
  | refl (t : Term L) (Gamma Delta : Finset (FormulaN L))
    : G1nnfEqAxiom L hL
  /-- Function congruence axiom (ii): for n-ary function symbol f,
      Gamma, s_1 = t_1, ..., s_n = t_n -> Delta,
      f(s_1,...,s_n) = f(t_1,...,t_n) -/
  | funCong (f : L.funSymbols)
      (ss ts : Fin (L.funArity f) → Term L)
      (Gamma Delta : Finset (FormulaN L))
    : G1nnfEqAxiom L hL
  /-- Predicate congruence axiom (iii): for an ordinary n-ary predicate
      symbol P, Gamma, s_1 = t_1, ..., s_n = t_n,
      P(s_1,...,s_n) -> Delta, P(t_1,...,t_n). The equality-predicate
      instance is represented separately by `eqCong` below. -/
  | predCong (P : L.predSymbols)
      (ss ts : Fin (L.predArity P) → Term L)
      (Gamma Delta : Finset (FormulaN L))
    : G1nnfEqAxiom L hL
  /-- Equality-as-predicate congruence axiom (iii), the binary instance
      omitted by `predCong` because equality is represented by the
      separate `FormulaN.eq_` constructor:
      Gamma, s1 = t1, s2 = t2, s1 = s2 -> Delta, t1 = t2. -/
  | eqCong (s1 s2 t1 t2 : Term L)
      (Gamma Delta : Finset (FormulaN L))
    : G1nnfEqAxiom L hL
  /-- Negation-left closure: from Gamma -> Delta, A derive
      neg A, Gamma -> Delta. Applied only to designated positive
      atomic formulae in the equality axiom schemas. -/
  | negLeft (base : G1nnfEqAxiom L hL) (A : FormulaN L)
    : G1nnfEqAxiom L hL
  /-- Negation-right closure: from A, Gamma -> Delta derive
      Gamma -> Delta, neg A. Applied only to designated positive
      atomic formulae in the equality axiom schemas. -/
  | negRight (base : G1nnfEqAxiom L hL) (A : FormulaN L)
    : G1nnfEqAxiom L hL

namespace G1nnfEqAxiom

/-- Definition 6.4.6 (companion): Returns the sequent (as a pair of
Finsets) for an equality axiom schema. Reflexivity gives
(Gamma, insert (t = t) Delta). Function congruence gives
(union eqPairs Gamma, insert (f(ss) = f(ts)) Delta). Predicate
congruence gives (insert P(ss) (union eqPairs Gamma), insert P(ts) Delta).
Equality-as-predicate congruence gives
(Gamma, s1 = t1, s2 = t2, s1 = s2 -> Delta, t1 = t2).
Negation-left erases its positive atom from the succedent and inserts
its negation in the antecedent; negation-right does the converse. -/
@[blueprint "chap6__definition_6_4_6"]
noncomputable def toSequent {L : Language} {hL : L.hasEquality = true} :
    G1nnfEqAxiom L hL → Finset (FormulaN L) × Finset (FormulaN L)
  | .refl t rG rD =>
    (rG, Finset.insert (.eq_ hL t t) rD)
  | .funCong f ss ts rG rD =>
    let eqPairs := Finset.ofList ((List.finRange (L.funArity f)).map
      fun i => FormulaN.eq_ hL (ss i) (ts i))
    (Finset.union eqPairs rG,
     Finset.insert (.eq_ hL (.func f ss) (.func f ts)) rD)
  | .predCong P ss ts rG rD =>
    let eqPairs := Finset.ofList ((List.finRange (L.predArity P)).map
      fun i => FormulaN.eq_ hL (ss i) (ts i))
    (Finset.insert (.predN P ss) (Finset.union eqPairs rG),
     Finset.insert (.predN P ts) rD)
  | .eqCong s1 s2 t1 t2 rG rD =>
    let eqPairs := Finset.ofList
      [FormulaN.eq_ hL s1 t1, FormulaN.eq_ hL s2 t2]
    (Finset.insert (.eq_ hL s1 s2) (Finset.union eqPairs rG),
     Finset.insert (.eq_ hL t1 t2) rD)
  | .negLeft base A =>
    let (ante, succ) := base.toSequent
    (Finset.insert (.neg A) ante, Finset.erase succ A)
  | .negRight base A =>
    let (ante, succ) := base.toSequent
    (Finset.erase ante A, Finset.insert (.neg A) succ)

/-- Definition 6.4.6 (companion): `A` is one of the positive atomic
formulae explicitly designated by the underlying equality axiom schema.
This deliberately excludes arbitrary atomic formulae contributed by the
ambient contexts `Gamma` and `Delta`. Negation closure preserves the
underlying schema's designated atoms. -/
@[blueprint "chap6__definition_6_4_6"]
def IsEligibleAtom {L : Language} {hL : L.hasEquality = true} :
    G1nnfEqAxiom L hL → FormulaN L → Prop
  | .refl t _ _, A =>
    A = .eq_ hL t t
  | .funCong f ss ts _ _, A =>
    (∃ i : Fin (L.funArity f), A = .eq_ hL (ss i) (ts i)) ∨
      A = .eq_ hL (.func f ss) (.func f ts)
  | .predCong P ss ts _ _, A =>
    (∃ i : Fin (L.predArity P), A = .eq_ hL (ss i) (ts i)) ∨
      A = .predN P ss ∨ A = .predN P ts
  | .eqCong s1 s2 t1 t2 _ _, A =>
    A = .eq_ hL s1 t1 ∨ A = .eq_ hL s2 t2 ∨
      A = .eq_ hL s1 s2 ∨ A = .eq_ hL t1 t2
  | .negLeft base _, A => base.IsEligibleAtom A
  | .negRight base _, A => base.IsEligibleAtom A

/-- Definition 6.4.6 (companion): Admissibility of an equality-axiom
schema. Base schemas are admissible by construction. Each negation
closure must start from an admissible schema, act on a designated
positive atomic formula, and find that formula on the source side
required by the corresponding Gentzen negation rule. -/
@[blueprint "chap6__definition_6_4_6"]
noncomputable def WellFormed {L : Language} {hL : L.hasEquality = true} :
    G1nnfEqAxiom L hL → Prop
  | .refl _ _ _ => True
  | .funCong _ _ _ _ _ => True
  | .predCong _ _ _ _ _ => True
  | .eqCong _ _ _ _ _ _ => True
  | .negLeft base A =>
    base.WellFormed ∧ base.IsEligibleAtom A ∧ A.isAtomic = true ∧
      A ∈ base.toSequent.2
  | .negRight base A =>
    base.WellFormed ∧ base.IsEligibleAtom A ∧ A.isAtomic = true ∧
      A ∈ base.toSequent.1

/-- Exact Gentzen-orientation regression for negation-left. -/
theorem toSequent_negLeft {L : Language} {hL : L.hasEquality = true}
    (base : G1nnfEqAxiom L hL) (A : FormulaN L) :
    (G1nnfEqAxiom.negLeft base A).toSequent =
      (Finset.insert (.neg A) base.toSequent.1,
       Finset.erase base.toSequent.2 A) := by
  cases h : base.toSequent
  simp [toSequent, h]

/-- Exact Gentzen-orientation regression for negation-right. -/
theorem toSequent_negRight {L : Language} {hL : L.hasEquality = true}
    (base : G1nnfEqAxiom L hL) (A : FormulaN L) :
    (G1nnfEqAxiom.negRight base A).toSequent =
      (Finset.erase base.toSequent.1 A,
       Finset.insert (.neg A) base.toSequent.2) := by
  cases h : base.toSequent
  simp [toSequent, h]

end G1nnfEqAxiom

/-- Every well-formed equality axiom of G1nnf= is valid, including its
negation-left and negation-right closures. -/
@[blueprint "chap6__definition_6_4_6"]
theorem g1nnfEqAxiom_valid {L : Language} {hL : L.hasEquality = true}
    (ax : G1nnfEqAxiom L hL) (hW : ax.WellFormed) :
    ∀ (M : Structure L) (val : Assignment M),
      (∀ A ∈ ax.toSequent.1, formulaEvalN M A val) →
      ∃ A ∈ ax.toSequent.2, formulaEvalN M A val 

-- ===================================================================
-- Definition 6.4.6 (companion type): G1nnfEqRule
-- ===================================================================
/-- Definition 6.4.6 (companion type): The inference rules of the
system G1^nnf_=. This extends G1nnfRule by adding equality axiom
schemas as additional axiom rules. A G1nnfEqRule is either a base
G1nnf rule or an equality axiom. -/
@[blueprint "chap6__definition_6_4_6"]
inductive G1nnfEqRule (L : Language) (hL : L.hasEquality = true) : Type where
  /-- A base G1nnf rule (from Definition 6.4.2) -/
  | base (r : G1nnfRule L) : G1nnfEqRule L hL
  /-- An equality axiom schema (from Definition 6.4.6) -/
  | eqAxiom (ax : G1nnfEqAxiom L hL) : G1nnfEqRule L hL

namespace G1nnfEqRule

/-- Definition 6.4.6 (helper): Extract the cut formula from a
G1nnfEqRule, if the rule is a cut (from the base G1nnf rules).
Returns none for non-cut rules and for equality axiom rules. -/
@[blueprint "chap6__definition_6_4_6"]
def cutFormula {L : Language} {hL : L.hasEquality = true} :
    G1nnfEqRule L hL → Option (FormulaN L)
  | .base r => r.cutFormula
  | .eqAxiom _ => none

/-- Definition 6.4.6 (helper): Returns the conclusion sequent
(as a pair of Finsets) of a G1nnfEq rule applied in context Finsets
Gamma and Delta. For base G1nnf rules, delegates to
G1nnfRule.conclusion. For equality axiom rules, returns the
axiom's sequent (Gamma/Delta are unused since the axiom stores
its own context). -/
@[blueprint "chap6__definition_6_4_6"]
noncomputable def conclusion {L : Language} {hL : L.hasEquality = true} :
    G1nnfEqRule L hL → Finset (FormulaN L) → Finset (FormulaN L) →
    Finset (FormulaN L) × Finset (FormulaN L)
  | .base r, Gamma, Delta => r.conclusion Gamma Delta
  | .eqAxiom ax, _, _ => ax.toSequent

/-- Definition 6.4.6 (helper): Returns the list of premise sequents
for a G1nnfEq rule. Base rules delegate to G1nnfRule.premises.
Equality axioms have no premises (they are axiom schemas). -/
@[blueprint "chap6__definition_6_4_6"]
noncomputable def premises {L : Language} {hL : L.hasEquality = true} :
    G1nnfEqRule L hL → Finset (FormulaN L) → Finset (FormulaN L) →
    List (Finset (FormulaN L) × Finset (FormulaN L))
  | .base r, Gamma, Delta => r.premises Gamma Delta
  | .eqAxiom _, _, _ => []

/-- Definition 6.4.6 (helper): Side conditions for a `G1nnfEqRule`.
Base rules delegate exactly to their `G1nnfRule.SideConditions`; equality
axioms must satisfy the admissibility predicate for their negation closures. -/
@[blueprint "chap6__definition_6_4_6"]
def SideConditions {L : Language} {hL : L.hasEquality = true} :
    G1nnfEqRule L hL → Finset (FormulaN L) → Finset (FormulaN L) → Prop
  | .base r, Gamma, Delta => r.SideConditions Gamma Delta
  | .eqAxiom ax, _, _ => ax.WellFormed

/-- A legal G1nnf= rule application satisfies the equality-aware
rule-specific side conditions and has an NNF conclusion sequent. -/
@[blueprint "chap6__definition_6_4_6"]
def ApplicationConditions {L : Language} {hL : L.hasEquality = true}
    (rule : G1nnfEqRule L hL)
    (Gamma Delta : Finset (FormulaN L)) : Prop :=
  SideConditions rule Gamma Delta ∧
    G1nnfFinsetSequent.IsNNF (rule.conclusion Gamma Delta)

end G1nnfEqRule

/-- Lemma 6.4.8 (required type): A G1nnfEq proof tree is defined
inductively, mirroring G1nnfProofTree but using G1nnfEqRule
(which includes both base G1nnf rules and equality axiom schemas).
Indexed by the conclusion antecedent and succedent as
`LCS.Finset (FormulaN L)`, matching the CutElimination.lean pattern.
Every rule application stores its complete `ApplicationConditions`,
so each indexed conclusion is in NNF. -/
@[blueprint "chap6__definition_6_4_6"]
inductive G1nnfEqProofTree {L : Language} (hL : L.hasEquality = true) :
    Finset (FormulaN L) → Finset (FormulaN L) → Type where
  /-- Axiom leaf: a G1nnfEq axiom or equality axiom rule with
  zero premises. -/
  | axiom_ (rule : G1nnfEqRule L hL) (Gamma Delta : Finset (FormulaN L))
      (hAxiom : (rule.premises Gamma Delta).length = 0)
      (hAC : rule.ApplicationConditions Gamma Delta) :
      G1nnfEqProofTree hL (rule.conclusion Gamma Delta).1
                       (rule.conclusion Gamma Delta).2
  /-- One-premise rule application: rule.premises has length 1, and
  the subtree is indexed by that single premise. -/
  | onePremise (rule : G1nnfEqRule L hL) (Gamma Delta : Finset (FormulaN L))
      (hPrem : (rule.premises Gamma Delta).length = 1)
      (hAC : rule.ApplicationConditions Gamma Delta)
      (sub : G1nnfEqProofTree hL
        ((rule.premises Gamma Delta)[0]'(by omega)).1
        ((rule.premises Gamma Delta)[0]'(by omega)).2) :
      G1nnfEqProofTree hL (rule.conclusion Gamma Delta).1
                       (rule.conclusion Gamma Delta).2
  /-- Two-premise rule application (cut, conjRight, disjLeft): rule.premises
  has length 2, with subtrees indexed by the two premises. -/
  | twoPremise (rule : G1nnfEqRule L hL) (Gamma Delta : Finset (FormulaN L))
      (hPrem : (rule.premises Gamma Delta).length = 2)
      (hAC : rule.ApplicationConditions Gamma Delta)
      (sub1 : G1nnfEqProofTree hL
        ((rule.premises Gamma Delta)[0]'(by omega)).1
        ((rule.premises Gamma Delta)[0]'(by omega)).2)
      (sub2 : G1nnfEqProofTree hL
        ((rule.premises Gamma Delta)[1]'(by omega)).1
        ((rule.premises Gamma Delta)[1]'(by omega)).2) :
      G1nnfEqProofTree hL (rule.conclusion Gamma Delta).1
                       (rule.conclusion Gamma Delta).2

namespace G1nnfEqProofTree

/-- Lemma 6.4.8 (helper): Returns the conclusion sequent of a
G1nnfEq proof tree. For the indexed tree this is just the type
index (Gamma, Delta). -/
@[blueprint "chap6__definition_6_4_6"]
def conclusion {L : Language} {hL : L.hasEquality = true}
    {Γ Δ : Finset (FormulaN L)}
    (_ : G1nnfEqProofTree hL Γ Δ) :
    Finset (FormulaN L) × Finset (FormulaN L) :=
  (Γ, Δ)

end G1nnfEqProofTree

-- ===================================================================
-- G1nnfEq proof-tree application-condition regressions
-- ===================================================================

/-- Lemma 6.4.8: (Completeness of G1^nnf_=) For the system G1nnf_equal,
every valid sequent is provable. -/
@[attach_debt, blueprint "chap6__lemma_6_4_8" (main := true)]
theorem g1nnfEq_completeness {L : Language} (hL : L.hasEquality = true)
    (Gamma Delta : Finset (FormulaN L))
    (hValid : ∀ A, A ∈ Gamma → FormulaN.isNNF A)
    (hValidD : ∀ A, A ∈ Delta → FormulaN.isNNF A)
    (hSeqValid : ∀ (M : Structure L) (val : Assignment M),
      (∀ A, A ∈ Gamma → formulaEvalN M A val) →
      (∃ A, A ∈ Delta ∧ formulaEvalN M A val)) :
    Nonempty (G1nnfEqProofTree hL Gamma Delta) 

end LCS.CutElim.Hauptsatz.Equality
end
