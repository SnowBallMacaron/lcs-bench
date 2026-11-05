import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Semantics.Substitution
import LCS.Propositional.Semantics
import Attach
import LCS.FirstOrder.ManySorted.Gentzen.Calculus.ProofsStamp

section
namespace LCS.FirstOrder.ManySorted.Gentzen
open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.Propositional.Semantics

/-- Formulae built from atoms using ∧, ∨, ⊃, ¬, ∀ and ∃. Equality atoms
are available exactly when the language permits equality. -/
@[blueprint "chap10__definition_10_4_1"]
def msIsSixConnective {L : MSLanguage} : MSFormula L → Prop
  | .falsum | .equiv_ _ _ => False
  | .pred _ _ | .eq_ _ _ _ _ => True
  | .conj A B | .disj A B | .impl A B =>
      msIsSixConnective A ∧ msIsSixConnective B
  | .neg A | .all _ _ A | .ex _ _ A => msIsSixConnective A

/-- Expand primitive ⊥ and ≡ using a supplied six-connective formula B.
Bottom abbreviates B ∧ ¬B; equivalence abbreviates the two implications.
The parameter supplies an atom-bearing formula even in signatures where
no closed formula exists. No formula is selected for an atomless language. -/
@[blueprint "chap10__definition_10_4_1"]
def msExpandAbbreviations {L : MSLanguage}
    (B : MSFormula L) (_hB : msIsSixConnective B) : MSFormula L → MSFormula L
  | .falsum => .conj B (.neg B)
  | .pred P ts => .pred P ts
  | .eq_ h s t u => .eq_ h s t u
  | .conj A C => .conj (msExpandAbbreviations B _hB A) (msExpandAbbreviations B _hB C)
  | .disj A C => .disj (msExpandAbbreviations B _hB A) (msExpandAbbreviations B _hB C)
  | .impl A C => .impl (msExpandAbbreviations B _hB A) (msExpandAbbreviations B _hB C)
  | .equiv_ A C => .conj
      (.impl (msExpandAbbreviations B _hB A) (msExpandAbbreviations B _hB C))
      (.impl (msExpandAbbreviations B _hB C) (msExpandAbbreviations B _hB A))
  | .neg A => .neg (msExpandAbbreviations B _hB A)
  | .all s x A => .all s x (msExpandAbbreviations B _hB A)
  | .ex s x A => .ex s x (msExpandAbbreviations B _hB A)

/-- The abbreviation expansion lands in the six-connective domain. -/
@[attach_debt, blueprint "chap10__definition_10_4_1"]
theorem msExpandAbbreviations_sixConnective {L : MSLanguage}
    (B : MSFormula L) (hB : msIsSixConnective B) (A : MSFormula L) :
    msIsSixConnective (msExpandAbbreviations B hB A)

/-- Abbreviation expansion preserves truth in every structure and assignment. -/
@[attach_debt, blueprint "chap10__definition_10_4_1"]
theorem msExpandAbbreviations_eval {L : MSLanguage}
    (B : MSFormula L) (hB : msIsSixConnective B) (A : MSFormula L)
    (M : MSStructure L) (v : MSAssignment M) :
    msFormulaEval M (msExpandAbbreviations B hB A) v = msFormulaEval M A v

/-- Definition 10.4.1: A many-sorted sequent is a pair of finite
sequences of many-sorted formulae. The antecedent (Γ) and succedent (Δ)
are lists of `MSFormula L`; denoted Γ → Δ. Direct many-sorted analogue
of the one-sorted `Sequent` (chap5 Def 5.4.1), with `MSFormula`
replacing `FormulaN`. -/
@[blueprint "chap10__definition_10_4_1"]
structure MSSequentCore (L : MSLanguage) where
  /-- The antecedent Γ: the sequence of formulae on the left of →. -/
  antecedent : List (MSFormula L)
  /-- The succedent Δ: the sequence of formulae on the right of →. -/
  succedent : List (MSFormula L)

/-- The six-connective domain of a finite ordered sequent. -/
@[blueprint "chap10__definition_10_4_1"]
def MSSequentCore.IsSixConnective {L : MSLanguage} (seq : MSSequentCore L) : Prop :=
  ∀ A ∈ seq.antecedent ++ seq.succedent, msIsSixConnective A

/-- Definition 10.4.1: finite ordered sequents in the equality-free,
six-connective language of G. -/
@[blueprint "chap10__definition_10_4_1" (main := true)]
def MSSequent (L : MSLanguage) (_hL : L.withoutEquality) :=
  {seq : MSSequentCore L // seq.IsSixConnective}

-- ===================================================================
-- Definition 10.4.1 (companion def): axiom predicate of G
-- ===================================================================

/-- Definition 10.4.1: A many-sorted sequent Γ → Δ is an axiom of G iff
its antecedent Γ and succedent Δ contain a common formula. The axiom set
of G is `{Γ → Δ : Γ and Δ share a formula}`. Many-sorted analogue of
one-sorted `isAxiom` (chap5 Def 5.4.1). -/
@[blueprint "chap10__definition_10_4_1"]
def MSSequentCore.isAxiom {L : MSLanguage} (s : MSSequentCore L) : Prop :=
  ∃ A : MSFormula L, A ∈ s.antecedent ∧ A ∈ s.succedent

/-- Axiom sequents of G have a common formula on the two sides. -/
@[blueprint "chap10__definition_10_4_1" (main := true)]
def MSSequent.isAxiom {L : MSLanguage} (hL : L.withoutEquality)
    (seq : MSSequent L hL) : Prop := seq.val.isAxiom

-- ===================================================================
-- Definition 10.4.1: One-premise inference rules of G
-- ===================================================================

/-- Definition 10.4.1: One-premise inference rules of the many-sorted
Gentzen system G, indexed by premise and conclusion sequents so that
each constructor fixes the exact structural relationship the rule
mandates. The 8 propositional rules are exactly the §5.4 rules with
`FormulaN` replaced by `MSFormula`; the FOUR quantifier rules
(`allLeft`, `allRight`, `exLeft`, `exRight`) carry the sort
`s : L.SortType` of the quantified/eigen variable.

  * connective rules: `conjLeft`, `disjRight`, `implRight`, `negLeft`,
    `negRight` (the §5.4 one-premise propositional rules).
  * `allLeft`/`exRight`: take an instantiation term `t : MSTerm L s` of
    sort `s` (matching the bound variable's sort), with the side
    condition `hfree : msIsFreeFor A s x t` ("t is free for x in A").
    The side formula is `msFormulaSubst A s x t = A[t/x]`; the principal
    formula is the quantified `MSFormula.all s x A` / `MSFormula.ex s x A`
    of the conclusion sequent.
  * `allRight`/`exLeft`: use the sort-`s` eigenvariable `MSTerm.var s y`,
    with the eigenvariable condition `hfresh` — the sort-`s` variable
    `(s, y)` does not occur free in any formula of the lower (conclusion)
    sequent — and `hfreeFor : msIsFreeFor A s x (MSTerm.var s y)`. Here the
    principal formula is again `MSFormula.all s x A` / `MSFormula.ex s x A`
    and the side formula is `msFormulaSubst A s x (MSTerm.var s y) = A[y/x]`.

Requires `[DecidableEq L.SortType]` because the quantifier constructors
mention `msFormulaSubst`, which is sort-gated. Direct many-sorted
analogue of one-sorted `GentzenStep1` (chap5 Def 5.4.1). -/
@[blueprint "chap10__definition_10_4_1"]
inductive MSGentzenStep1Frame {L : MSLanguage} [DecidableEq L.SortType] :
    MSSequentCore L → MSSequentCore L → Type where
  /-- (and:left): Γ, A ∧ B, Δ → Λ from Γ, A, B, Δ → Λ. -/
  | conjLeft (Γ Δ Λ : List (MSFormula L)) (A B : MSFormula L) :
      MSGentzenStep1Frame (MSSequentCore.mk (Γ ++ [A, B] ++ Δ) Λ)
                      (MSSequentCore.mk (Γ ++ [MSFormula.conj A B] ++ Δ) Λ)
  /-- (or:right): Γ → Δ, A ∨ B, Λ from Γ → Δ, A, B, Λ. -/
  | disjRight (Γ Δ Λ : List (MSFormula L)) (A B : MSFormula L) :
      MSGentzenStep1Frame (MSSequentCore.mk Γ (Δ ++ [A, B] ++ Λ))
                      (MSSequentCore.mk Γ (Δ ++ [MSFormula.disj A B] ++ Λ))
  /-- (⊃:right): Γ → Δ, A ⊃ B, Λ from A, Γ → B, Δ, Λ. -/
  | implRight (Γ Δ Λ : List (MSFormula L)) (A B : MSFormula L) :
      MSGentzenStep1Frame (MSSequentCore.mk ([A] ++ Γ) (B :: (Δ ++ Λ)))
                      (MSSequentCore.mk Γ (Δ ++ [MSFormula.impl A B] ++ Λ))
  /-- (neg:left): Γ, ¬A, Δ → Λ from Γ, Δ → A, Λ. -/
  | negLeft (Γ Δ Λ : List (MSFormula L)) (A : MSFormula L) :
      MSGentzenStep1Frame (MSSequentCore.mk (Γ ++ Δ) (A :: Λ))
                      (MSSequentCore.mk (Γ ++ [MSFormula.neg A] ++ Δ) Λ)
  /-- (neg:right): Γ → Δ, ¬A, Λ from A, Γ → Δ, Λ. -/
  | negRight (Γ Δ Λ : List (MSFormula L)) (A : MSFormula L) :
      MSGentzenStep1Frame (MSSequentCore.mk ([A] ++ Γ) (Δ ++ Λ))
                      (MSSequentCore.mk Γ (Δ ++ [MSFormula.neg A] ++ Λ))
  /-- (∀:left), sort-tagged: Γ, ∀_s x_x A, Δ → Λ from
      Γ, A[t/x], ∀_s x_x A, Δ → Λ, where `t : MSTerm L s` is a term of
      sort `s` free for x in A (`hfree`). -/
  | allLeft (s : L.SortType) (t : MSTerm L s)
      (Γ Δ Λ : List (MSFormula L)) (x : Nat) (A : MSFormula L)
      (hfree : msIsFreeFor A s x t) :
      MSGentzenStep1Frame
        (MSSequentCore.mk
          (Γ ++ [msFormulaSubst A s x t, MSFormula.all s x A] ++ Δ) Λ)
        (MSSequentCore.mk (Γ ++ [MSFormula.all s x A] ++ Δ) Λ)
  /-- (∀:right), sort-tagged: Γ → Δ, ∀_s x_x A, Λ from
      Γ → Δ, A[y/x], Λ, with sort-`s` eigenvariable `y`. The
      eigenvariable condition `hfresh` says `(s, y)` does not occur free
      in any formula of the lower sequent. -/
  | allRight (s : L.SortType) (y : Nat)
      (Γ Δ Λ : List (MSFormula L)) (x : Nat) (A : MSFormula L)
      (hfresh : ∀ F ∈ (Γ ++ (Δ ++ [MSFormula.all s x A] ++ Λ)),
        (s, y) ∉ msFormulaFV F)
      (hfreeFor : msIsFreeFor A s x (MSTerm.var s y)) :
      MSGentzenStep1Frame
        (MSSequentCore.mk Γ
          (Δ ++ [msFormulaSubst A s x (MSTerm.var s y)] ++ Λ))
        (MSSequentCore.mk Γ (Δ ++ [MSFormula.all s x A] ++ Λ))
  /-- (∃:left), sort-tagged: Γ, ∃_s x_x A, Δ → Λ from
      Γ, A[y/x], Δ → Λ, with sort-`s` eigenvariable `y` satisfying the
      eigenvariable condition `hfresh`. -/
  | exLeft (s : L.SortType) (y : Nat)
      (Γ Δ Λ : List (MSFormula L)) (x : Nat) (A : MSFormula L)
      (hfresh : ∀ F ∈ ((Γ ++ [MSFormula.ex s x A] ++ Δ) ++ Λ),
        (s, y) ∉ msFormulaFV F)
      (hfreeFor : msIsFreeFor A s x (MSTerm.var s y)) :
      MSGentzenStep1Frame
        (MSSequentCore.mk
          (Γ ++ [msFormulaSubst A s x (MSTerm.var s y)] ++ Δ) Λ)
        (MSSequentCore.mk (Γ ++ [MSFormula.ex s x A] ++ Δ) Λ)
  /-- (∃:right), sort-tagged: Γ → Δ, ∃_s x_x A, Λ from
      Γ → Δ, A[t/x], ∃_s x_x A, Λ, where `t : MSTerm L s` is a term of
      sort `s` free for x in A (`hfree`). -/
  | exRight (s : L.SortType) (t : MSTerm L s)
      (Γ Δ Λ : List (MSFormula L)) (x : Nat) (A : MSFormula L)
      (hfree : msIsFreeFor A s x t) :
      MSGentzenStep1Frame
        (MSSequentCore.mk Γ
          (Δ ++ [msFormulaSubst A s x t, MSFormula.ex s x A] ++ Λ))
        (MSSequentCore.mk Γ (Δ ++ [MSFormula.ex s x A] ++ Λ))

-- ===================================================================
-- Definition 10.4.1: Two-premise inference rules of G
-- ===================================================================

/-- Definition 10.4.1: Two-premise inference rules of the many-sorted
Gentzen system G, indexed by both premise sequents and the conclusion
sequent. These are exactly the §5.4 two-premise propositional rules with
`MSFormula` replacing `FormulaN`; no sort tagging is needed (the
quantifier rules are all one-premise), so no `DecidableEq` instance is
required. -/
@[blueprint "chap10__definition_10_4_1"]
inductive MSGentzenStep2Frame {L : MSLanguage} :
    MSSequentCore L → MSSequentCore L → MSSequentCore L → Type where
  /-- (and:right): Γ → Δ, A ∧ B, Λ from Γ → Δ, A, Λ and Γ → Δ, B, Λ. -/
  | conjRight (Γ Δ Λ : List (MSFormula L)) (A B : MSFormula L) :
      MSGentzenStep2Frame (MSSequentCore.mk Γ (Δ ++ [A] ++ Λ))
                      (MSSequentCore.mk Γ (Δ ++ [B] ++ Λ))
                      (MSSequentCore.mk Γ (Δ ++ [MSFormula.conj A B] ++ Λ))
  /-- (or:left): Γ, A ∨ B, Δ → Λ from Γ, A, Δ → Λ and Γ, B, Δ → Λ. -/
  | disjLeft (Γ Δ Λ : List (MSFormula L)) (A B : MSFormula L) :
      MSGentzenStep2Frame (MSSequentCore.mk (Γ ++ [A] ++ Δ) Λ)
                      (MSSequentCore.mk (Γ ++ [B] ++ Δ) Λ)
                      (MSSequentCore.mk (Γ ++ [MSFormula.disj A B] ++ Δ) Λ)
  /-- (⊃:left): Γ, A ⊃ B, Δ → Λ from Γ, Δ → A, Λ and B, Γ, Δ → Λ. -/
  | implLeft (Γ Δ Λ : List (MSFormula L)) (A B : MSFormula L) :
      MSGentzenStep2Frame (MSSequentCore.mk (Γ ++ Δ) (A :: Λ))
                      (MSSequentCore.mk ([B] ++ Γ ++ Δ) Λ)
                      (MSSequentCore.mk (Γ ++ [MSFormula.impl A B] ++ Δ) Λ)

/-- A one-premise rule frame with six-connective sequents, shared by G and G=. -/
@[blueprint "chap10__definition_10_4_1"]
structure MSGentzenStep1Core {L : MSLanguage} [DecidableEq L.SortType]
    (prem conc : MSSequentCore L) where
  frame : MSGentzenStep1Frame prem conc
  premiseDomain : prem.IsSixConnective
  conclusionDomain : conc.IsSixConnective

/-- A two-premise rule frame with six-connective sequents, shared by G and G=. -/
@[blueprint "chap10__definition_10_4_1"]
structure MSGentzenStep2Core {L : MSLanguage}
    (prem1 prem2 conc : MSSequentCore L) where
  frame : MSGentzenStep2Frame prem1 prem2 conc
  premise1Domain : prem1.IsSixConnective
  premise2Domain : prem2.IsSixConnective
  conclusionDomain : conc.IsSixConnective

/-- Definition 10.4.1: the one-premise rules of equality-free G. -/
@[blueprint "chap10__definition_10_4_1" (main := true)]
abbrev MSGentzenStep1 {L : MSLanguage} [DecidableEq L.SortType]
    (_hL : L.withoutEquality) (prem conc : MSSequentCore L) :=
  MSGentzenStep1Core prem conc

/-- Definition 10.4.1: the two-premise rules of equality-free G. -/
@[blueprint "chap10__definition_10_4_1" (main := true)]
abbrev MSGentzenStep2 {L : MSLanguage}
    (_hL : L.withoutEquality) (prem1 prem2 conc : MSSequentCore L) :=
  MSGentzenStep2Core prem1 prem2 conc

-- ===================================================================
-- Lemma 10.4.1 (companion type): MSGProofTreeCore
-- ===================================================================

/-- Lemma 10.4.1 (companion, §10.4.2): Proof trees for the many-sorted
Gentzen system G, indexed by their conclusion sequent. Structural
validity is built into the type: leaves must be axiom sequents
(`MSSequentCore.isAxiom`), and each rule application constrains its
premise(s) to have the form mandated by the rule (including side
conditions for quantifier rules, carried by `MSGentzenStep1Frame`). Direct
many-sorted analogue of one-sorted `GProofTree` (chap5 Def 5.4.2). -/
@[blueprint "chap10__lemma_10_4_1"]
inductive MSGProofTreeCore {L : MSLanguage} [DecidableEq L.SortType] :
    MSSequentCore L → Type where
  /-- A leaf: an axiom sequent of G. -/
  | axiom_ (s : MSSequentCore L) (hDomain : s.IsSixConnective) (h : MSSequentCore.isAxiom s) : MSGProofTreeCore s
  /-- A one-premise inference: from a proof tree of the premise and a
      one-premise rule, build a proof tree of the conclusion. -/
  | onePremise {prem conc : MSSequentCore L}
      (rule : MSGentzenStep1Core prem conc)
      (t : MSGProofTreeCore prem) : MSGProofTreeCore conc
  /-- A two-premise inference: from proof trees of both premises and a
      two-premise rule, build a proof tree of the conclusion. -/
  | twoPremise {prem1 prem2 conc : MSSequentCore L}
      (rule : MSGentzenStep2Core prem1 prem2 conc)
      (t1 : MSGProofTreeCore prem1) (t2 : MSGProofTreeCore prem2) :
      MSGProofTreeCore conc

/-- Lemma 10.4.1: G proof trees over the equality-free six-connective domain. -/
@[blueprint "chap10__lemma_10_4_1"]
abbrev MSGProofTree {L : MSLanguage} [DecidableEq L.SortType]
    (_hL : L.withoutEquality) (seq : MSSequentCore L) := MSGProofTreeCore seq

/-- Finite ordered deduction trees with arbitrary open leaves. Every node
has a six-connective sequent and every internal node uses a displayed rule. -/
@[blueprint "chap10__lemma_10_4_1"]
inductive MSGDeductionTreeCore {L : MSLanguage} [DecidableEq L.SortType] :
    MSSequentCore L → Type where
  | leaf (seq : MSSequentCore L) (hDomain : seq.IsSixConnective) :
      MSGDeductionTreeCore seq
  | onePremise {prem conc : MSSequentCore L}
      (rule : MSGentzenStep1Core prem conc) (t : MSGDeductionTreeCore prem) :
      MSGDeductionTreeCore conc
  | twoPremise {prem1 prem2 conc : MSSequentCore L}
      (rule : MSGentzenStep2Core prem1 prem2 conc)
      (t1 : MSGDeductionTreeCore prem1) (t2 : MSGDeductionTreeCore prem2) :
      MSGDeductionTreeCore conc

/-- §10.4.2: deduction trees for equality-free G may have arbitrary leaves. -/
@[blueprint "chap10__lemma_10_4_1"]
abbrev MSGDeductionTree {L : MSLanguage} [DecidableEq L.SortType]
    (_hL : L.withoutEquality) (seq : MSSequentCore L) := MSGDeductionTreeCore seq

/-- A deduction is closed exactly when each of its actual leaves is an axiom. -/
def MSGDeductionTreeCore.IsClosed {L : MSLanguage} [DecidableEq L.SortType] :
    {seq : MSSequentCore L} → MSGDeductionTreeCore seq → Prop
  | _, .leaf seq _ => seq.isAxiom
  | _, .onePremise _ t => t.IsClosed
  | _, .twoPremise _ t1 t2 => t1.IsClosed ∧ t2.IsClosed

/-- §10.4.2: proof trees are deduction trees all of whose leaves are axioms. -/
@[blueprint "chap10__lemma_10_4_1"]
def MSGDeductionTree.IsClosed {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.withoutEquality) {seq : MSSequentCore L}
    (t : MSGDeductionTree hL seq) : Prop := MSGDeductionTreeCore.IsClosed t

/-- Forget that the leaves are axioms, preserving every node and rule. -/
def MSGProofTreeCore.toDeductionTree {L : MSLanguage} [DecidableEq L.SortType] :
    {seq : MSSequentCore L} → MSGProofTreeCore seq → MSGDeductionTreeCore seq
  | _, .axiom_ seq hDomain _ => .leaf seq hDomain
  | _, .onePremise rule t => .onePremise rule t.toDeductionTree
  | _, .twoPremise rule t1 t2 => .twoPremise rule t1.toDeductionTree t2.toDeductionTree

/-- Close a deduction using the axiom evidence at each of its existing leaves. -/
def MSGDeductionTreeCore.toProofTree {L : MSLanguage} [DecidableEq L.SortType] :
    {seq : MSSequentCore L} → (t : MSGDeductionTreeCore seq) →
      t.IsClosed → MSGProofTreeCore seq
  | _, .leaf seq hDomain, h => .axiom_ seq hDomain h
  | _, .onePremise rule t, h => .onePremise rule (t.toProofTree h)
  | _, .twoPremise rule t1 t2, h =>
      .twoPremise rule (t1.toProofTree h.1) (t2.toProofTree h.2)

/-- §10.4.2: every G-proof is a deduction with the same ordered tree. -/
@[blueprint "chap10__lemma_10_4_1"]
def MSGProofTree.toDeductionTree {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.withoutEquality) {seq : MSSequentCore L}
    (t : MSGProofTree hL seq) : MSGDeductionTree hL seq :=
  MSGProofTreeCore.toDeductionTree t

/-- §10.4.2: a closed deduction specializes to a proof with the same nodes. -/
@[blueprint "chap10__lemma_10_4_1"]
def MSGDeductionTree.toProofTree {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.withoutEquality) {seq : MSSequentCore L}
    (t : MSGDeductionTree hL seq) (hClosed : MSGDeductionTree.IsClosed hL t) :
    MSGProofTree hL seq := MSGDeductionTreeCore.toProofTree t hClosed

/-- §10.4.2: a sequent has a G-proof iff it has a closed deduction. -/
@[attach_debt, blueprint "chap10__lemma_10_4_1"]
theorem msClosedDeduction_iff_provable {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.withoutEquality) (seq : MSSequentCore L) :
    (∃ t : MSGDeductionTree hL seq, MSGDeductionTree.IsClosed hL t) ↔
      Nonempty (MSGProofTree hL seq)

/-- §10.4.2: induction over the actual ordered deduction tree, with an
arbitrary-leaf case and one induction hypothesis for each premise child. -/
@[attach_debt, blueprint "chap10__lemma_10_4_1"]
theorem msDeductionTree_induction {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.withoutEquality)
    (P : (seq : MSSequentCore L) → MSGDeductionTree hL seq → Prop)
    (hLeaf : ∀ seq hDomain, P seq (.leaf seq hDomain))
    (hOne : ∀ {prem conc} (rule : MSGentzenStep1 hL prem conc)
      (t : MSGDeductionTree hL prem), P prem t → P conc (.onePremise rule t))
    (hTwo : ∀ {prem1 prem2 conc} (rule : MSGentzenStep2 hL prem1 prem2 conc)
      (t1 : MSGDeductionTree hL prem1) (t2 : MSGDeductionTree hL prem2),
      P prem1 t1 → P prem2 t2 → P conc (.twoPremise rule t1 t2))
    {seq : MSSequentCore L} (t : MSGDeductionTree hL seq) : P seq t

-- ===================================================================
-- Theorem 10.4.1 (companion type): MSSignedFormula
-- ===================================================================

/-- Theorem 10.4.1 (companion): A signed many-sorted formula `T A` /
`F A`, used by the many-sorted Hintikka-set definition in the
completeness proof. Direct many-sorted analogue of one-sorted
`SignedFormula` (chap5 Def 5.4.3). -/
@[blueprint "chap10__theorem_10_4_1"]
inductive MSSignedFormula (L : MSLanguage) : Type where
  /-- The signed formula `T A` ("A is true"). -/
  | trueF : MSFormula L → MSSignedFormula L
  /-- The signed formula `F A` ("A is false"). -/
  | falseF : MSFormula L → MSSignedFormula L

-- ===================================================================
-- Lemma 10.4.1 (companion def): G-provability
-- ===================================================================

/-- Lemma 10.4.1 (companion, §10.4.2): A many-sorted sequent is
G-provable iff there exists an `MSGProofTreeCore` with that sequent as
conclusion. Many-sorted analogue of one-sorted `sequentProvable`
(chap5 Def 5.4.2). -/
@[blueprint "chap10__lemma_10_4_1"]
def msSequentProvable {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.withoutEquality) (s : MSSequentCore L) : Prop :=
  Nonempty (MSGProofTree hL s)

-- ===================================================================
-- Lemma 10.4.1 (companion def): validity (over BoolVal)
-- ===================================================================

/-- Lemma 10.4.1 (companion): A many-sorted sequent Γ → Δ is valid iff
for every many-sorted L-structure `M` and assignment `v`, whenever all
antecedent formulae evaluate to `T` under `(M, v)`, some succedent
formula also evaluates to `T`. Phrased over the truth domain `BoolVal`
via `msFormulaEval` (`= BoolVal.T`), NOT over Prop — this is the §10.3
many-sorted semantics. Analogue of one-sorted `sequentValid`
(chap5 Def 5.4.2), transported to the `BoolVal`-valued `msFormulaEval`. -/
@[blueprint "chap10__lemma_10_4_1"]
def msSequentValid {L : MSLanguage} (seq : MSSequentCore L) : Prop :=
  ∀ (M : MSStructure L) (v : MSAssignment M),
    (∀ A ∈ seq.antecedent, msFormulaEval M A v = BoolVal.T) →
    (∃ B, B ∈ seq.succedent ∧ msFormulaEval M B v = BoolVal.T)

/-- Lemma 10.4.1 (companion): A many-sorted sequent Γ → Δ is falsifiable
in a given structure `M` iff there exists an assignment `v` under which
all antecedent formulae evaluate to `T` and all succedent formulae
evaluate to `F`. The `BoolVal`-valued many-sorted analogue of one-sorted
`sequentFalsifiableIn` (chap5 Def 5.4.2). -/
@[blueprint "chap10__lemma_10_4_1"]
def msSequentFalsifiableIn {L : MSLanguage} (M : MSStructure L)
    (seq : MSSequentCore L) : Prop :=
  ∃ v : MSAssignment M,
    (∀ A ∈ seq.antecedent, msFormulaEval M A v = BoolVal.T) ∧
    (∀ B ∈ seq.succedent, msFormulaEval M B v = BoolVal.F)

-- ===================================================================
-- Theorem 10.4.1 (companion def): many-sorted Hintikka set
-- ===================================================================

/-- Theorem 10.4.1 (companion): A many-sorted Hintikka set — the
modification of the Hintikka-set definition "so that it applies to a
many-sorted algebra" (the textbook explicitly calls for this in the
completeness proof). Here `H` is an `S`-indexed family of per-sort
term-carriers `H s : Set (MSTerm L s)`, and the closure conditions
H0–H6 are sort-aware: in particular the quantifier conditions (H3 for
`∀`-true / `∃`-false universal premises, H4 for `∀`-false / `∃`-true
witness premises) instantiate over terms `t : MSTerm L s` of the sort
`s` matching the quantifier's bound variable, drawn from `H s`.

  * H0: no atomic formula and its conjugate both lie in `S`.
  * H1 (type-A / conjunctive): both components of a conjunctive signed
    formula are in `S` (covering `T (A ∧ B)`, `F (A ∨ B)`,
    `F (A ⊃ B)`, `T ¬A`, `F ¬A`).
  * H2 (type-B / disjunctive): at least one component of a disjunctive
    signed formula is in `S` (covering `F (A ∧ B)`, `T (A ∨ B)`,
    `T (A ⊃ B)`).
  * H3 (type-C / universal): if a universally-acting quantified signed
    formula is in `S`, its sort-`s` instance is in `S` for every
    `t ∈ H s`.
  * H4 (type-D / existential): if an existentially-acting quantified
    signed formula is in `S`, its sort-`s` instance is in `S` for some
    `t ∈ H s`.
  * H5: every variable `(s, i)` free in some formula of `S` has its
    variable term in `H s`.
  * H6: instantiation terms drawn from `H s` are free for the bound
    variable in every quantified formula of `S`.

Direct many-sorted analogue of one-sorted `IsHintikkaSet`
(chap5 Def 5.4.7), sort-indexed. Referenced by the completeness (→)
direction of `msGoedelExtendedCompletenessG`. -/
@[blueprint "chap10__theorem_10_4_1"]
def MSIsHintikkaSet (L : MSLanguage) [DecidableEq L.SortType]
    (H : (s : L.SortType) → Set (MSTerm L s))
    (S : Set (MSSignedFormula L)) : Prop :=
  -- H0: no atomic formula and its conjugate are both in S.
  (∀ A : MSFormula L, A.isAtomic →
    ¬ (MSSignedFormula.trueF A ∈ S ∧ MSSignedFormula.falseF A ∈ S)) ∧
  -- H0 (falsum): `⊥` is never signed true in S (the §5.4 condition
  -- `h0_falsum`; in the one-sorted normalized `FormulaN` there is no
  -- `falsum` constructor, so this clause is automatic there, but
  -- `MSFormula` has `⊥`, so it must be stated). `F ⊥ ∈ S` is allowed
  -- (consistent with `⊥` evaluating to F).
  (MSSignedFormula.trueF MSFormula.falsum ∉ S) ∧
  -- H0 (no equality): no `eq_` formula appears signed in S. §10.4 is the
  -- system WITHOUT equality (the §5.4 standing assumption `hNoEq`); the
  -- one-sorted normalized `FormulaN` carries equality only via `eq_`,
  -- excluded from Hintikka sets by `hNoEq`.
  (∀ (hL : L.hasEquality = true) (s : L.SortType) (t1 t2 : MSTerm L s),
    MSSignedFormula.trueF (MSFormula.eq_ hL s t1 t2) ∉ S ∧
    MSSignedFormula.falseF (MSFormula.eq_ hL s t1 t2) ∉ S) ∧
  -- H0 (no equivalence): no `≡` formula appears signed in S. The §5.4
  -- normalized signed-formula decomposition (type-A/type-B) does not
  -- cover `≡` (Gallier eliminates `≡` before the search/Hintikka stage),
  -- so a faithful Hintikka set contains no `≡` formula. In the one-sorted
  -- `FormulaN` there is no `equiv_` constructor (`h0_no_equiv` automatic);
  -- `MSFormula` has `≡`, so it must be stated.
  (∀ A B : MSFormula L,
    MSSignedFormula.trueF (MSFormula.equiv_ A B) ∉ S ∧
    MSSignedFormula.falseF (MSFormula.equiv_ A B) ∉ S) ∧
  -- H1 (conjunctive / type-A): both components in S.
  (∀ A B : MSFormula L,
    (MSSignedFormula.trueF (MSFormula.conj A B) ∈ S →
      MSSignedFormula.trueF A ∈ S ∧ MSSignedFormula.trueF B ∈ S) ∧
    (MSSignedFormula.falseF (MSFormula.disj A B) ∈ S →
      MSSignedFormula.falseF A ∈ S ∧ MSSignedFormula.falseF B ∈ S) ∧
    (MSSignedFormula.falseF (MSFormula.impl A B) ∈ S →
      MSSignedFormula.trueF A ∈ S ∧ MSSignedFormula.falseF B ∈ S)) ∧
  (∀ A : MSFormula L,
    (MSSignedFormula.trueF (MSFormula.neg A) ∈ S →
      MSSignedFormula.falseF A ∈ S) ∧
    (MSSignedFormula.falseF (MSFormula.neg A) ∈ S →
      MSSignedFormula.trueF A ∈ S)) ∧
  -- H2 (disjunctive / type-B): at least one component in S.
  (∀ A B : MSFormula L,
    (MSSignedFormula.falseF (MSFormula.conj A B) ∈ S →
      MSSignedFormula.falseF A ∈ S ∨ MSSignedFormula.falseF B ∈ S) ∧
    (MSSignedFormula.trueF (MSFormula.disj A B) ∈ S →
      MSSignedFormula.trueF A ∈ S ∨ MSSignedFormula.trueF B ∈ S) ∧
    (MSSignedFormula.trueF (MSFormula.impl A B) ∈ S →
      MSSignedFormula.falseF A ∈ S ∨ MSSignedFormula.trueF B ∈ S)) ∧
  -- H3 (universal / type-C): sort-s instance for EVERY t ∈ H s.
  (∀ (s : L.SortType) (x : Nat) (A : MSFormula L),
    (MSSignedFormula.trueF (MSFormula.all s x A) ∈ S →
      ∀ t : MSTerm L s, t ∈ H s →
        MSSignedFormula.trueF (msFormulaSubst A s x t) ∈ S) ∧
    (MSSignedFormula.falseF (MSFormula.ex s x A) ∈ S →
      ∀ t : MSTerm L s, t ∈ H s →
        MSSignedFormula.falseF (msFormulaSubst A s x t) ∈ S)) ∧
  -- H4 (existential / type-D): sort-s instance for SOME t ∈ H s.
  (∀ (s : L.SortType) (x : Nat) (A : MSFormula L),
    (MSSignedFormula.falseF (MSFormula.all s x A) ∈ S →
      ∃ t : MSTerm L s, t ∈ H s ∧
        MSSignedFormula.falseF (msFormulaSubst A s x t) ∈ S) ∧
    (MSSignedFormula.trueF (MSFormula.ex s x A) ∈ S →
      ∃ t : MSTerm L s, t ∈ H s ∧
        MSSignedFormula.trueF (msFormulaSubst A s x t) ∈ S)) ∧
  -- H5: free variables of formulae in S are carried by H (per sort).
  (∀ (A : MSFormula L),
    (MSSignedFormula.trueF A ∈ S ∨ MSSignedFormula.falseF A ∈ S) →
      ∀ p : MSVar L, p ∈ msFormulaFV A → MSTerm.var p.1 p.2 ∈ H p.1) ∧
  -- H6: terms in H are free for the bound variable in quantified
  -- formulae of S (sort-matched).
  (∀ (s : L.SortType) (x : Nat) (A : MSFormula L) (t : MSTerm L s),
    t ∈ H s →
    (MSSignedFormula.trueF (MSFormula.all s x A) ∈ S ∨
     MSSignedFormula.falseF (MSFormula.all s x A) ∈ S ∨
     MSSignedFormula.trueF (MSFormula.ex s x A) ∈ S ∨
     MSSignedFormula.falseF (MSFormula.ex s x A) ∈ S) →
    msIsFreeFor A s x t)

-- ===================================================================
-- Helpers: BoolVal dichotomy + direct substitution-evaluation lemma
-- ===================================================================

-- retained: used by LCS.FirstOrder.ManySorted.Gentzen.Completeness
/-- A `BoolVal` value is either `T` or `F`; in particular, `b ≠ T → b = F`. -/
theorem boolVal_ne_T_eq_F {b : BoolVal} (h : b ≠ BoolVal.T) : b = BoolVal.F := by
  cases b with
  | T => exact absurd rfl h
  | F => rfl

-- retained: used by LCS.FirstOrder.ManySorted.Gentzen.Completeness
theorem boolVal_eq_F_ne_T {b : BoolVal} (h : b = BoolVal.F) : b ≠ BoolVal.T := by
  rw [h]; decide

-- retained: used by LCS.FirstOrder.ManySorted.Gentzen.Completeness
theorem boolVal_ne_F_eq_T {b : BoolVal} (h : b ≠ BoolVal.F) : b = BoolVal.T := by
  cases b with
  | T => rfl
  | F => exact absurd rfl h

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Direct term-level substitution-evaluation lemma (many-sorted analogue
of one-sorted `termSubstEvalDirect`): substituting a term `t` of sort `u`
for the sort-`u` variable `x` in a term `r` and evaluating equals
evaluating `r` under the assignment updated at `(u, x)` by the value of
`t`. Proved by induction on `r`; the variable case discharges the
sort-indexed cast in `msTermSubst`/`msAssignUpdate`. -/
theorem msTermSubstEvalDirect {L : MSLanguage} [DecidableEq L.SortType]
    {M : MSStructure L} (v : MSAssignment M)
    (u : L.SortType) (x : Nat) (t : MSTerm L u) :
    {s : L.SortType} → (r : MSTerm L s) →
    msTermEval M v (msTermSubst u x t r) =
      msTermEval M (msAssignUpdate M v u x (msTermEval M v t)) r := by
  intro s r
  induction r with
  | var s i =>
    simp only [msTermSubst, msTermEval, varMeaning, msAssignUpdate]
    by_cases h : s = u
    · subst h
      by_cases hi : i = x
      · subst hi; simp
      · simp [hi, msTermEval, varMeaning]
    · simp [h, msTermEval, varMeaning]
  | const s c =>
    simp only [msTermSubst, msTermEval, constM]
  | func f ts ih =>
    simp only [msTermSubst, msTermEval, funM]
    congr 1; funext j; exact ih j

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Direct formula-level substitution-evaluation lemma (many-sorted,
`BoolVal`-valued analogue of one-sorted `formulaSubstEvalDirectN`): if
`t` is free for `x` in `A`, then evaluating `A[t/x]` equals evaluating
`A` under the assignment updated at `(s, x)` by the value of `t`. Proved
by structural induction on `A`; atomic cases use `msTermSubstEvalDirect`,
connectives by congruence, quantifiers via assignment-update commutation
and the coincidence lemma for the free-for side condition. -/
theorem msFormulaSubstEvalDirect {L : MSLanguage} [DecidableEq L.SortType]
    {M : MSStructure L} (A : MSFormula L) (s : L.SortType) (x : Nat)
    (t : MSTerm L s) (hfree : msIsFreeFor A s x t) :
    ∀ v : MSAssignment M,
    msFormulaEval M (msFormulaSubst A s x t) v =
      msFormulaEval M A (msAssignUpdate M v s x (msTermEval M v t)) := by
  induction A with
  | falsum => intro v; rfl
  | pred P ts =>
    intro v
    simp only [msFormulaSubst, msFormulaEval, predM]
    congr 1; funext j
    exact msTermSubstEvalDirect v s x t (ts j)
  | eq_ hL s' t1 t2 =>
    classical
    intro v
    apply ite_cond_congr
    dsimp only
    rw [msTermSubstEvalDirect v s x t t1, msTermSubstEvalDirect v s x t t2]
  | conj A B ihA ihB =>
    intro v
    simp only [msFormulaSubst, msFormulaEval, Semantics.andM]
    rw [ihA hfree.1 v, ihB hfree.2 v]
  | disj A B ihA ihB =>
    intro v
    simp only [msFormulaSubst, msFormulaEval, Semantics.orM]
    rw [ihA hfree.1 v, ihB hfree.2 v]
  | impl A B ihA ihB =>
    intro v
    simp only [msFormulaSubst, msFormulaEval, Semantics.implM]
    rw [ihA hfree.1 v, ihB hfree.2 v]
  | equiv_ A B ihA ihB =>
    intro v
    simp only [msFormulaSubst, msFormulaEval, Semantics.equivM]
    rw [ihA hfree.1 v, ihB hfree.2 v]
  | neg A ih =>
    intro v
    simp only [msFormulaSubst, msFormulaEval, Semantics.negM]
    rw [ih hfree v]
  | all s' i A ih =>
    intro v
    simp only [msFormulaSubst]
    by_cases hb : s' = s ∧ i = x
    · -- Bound variable matches (s, x): substitution skipped.
      rw [if_pos hb]
      obtain ⟨hs, hi⟩ := hb
      subst hs; subst hi
      simp only [msFormulaEval, forallM]
      -- The outer update at (s', i) is overwritten by the quantifier's
      -- update, so it does not affect the inner evaluation.
      have hupd : ∀ a : M.carrier s',
          msFormulaEval M A (msAssignUpdate M
            (msAssignUpdate M v s' i (msTermEval M v t)) s' i a) =
          msFormulaEval M A (msAssignUpdate M v s' i a) := fun a => by
        rw [Semantics.Substitution.msAssignUpdate_idem]
      have hpe : (∀ a, msFormulaEval M A (msAssignUpdate M
            (msAssignUpdate M v s' i (msTermEval M v t)) s' i a) = BoolVal.T) =
          (∀ a, msFormulaEval M A (msAssignUpdate M v s' i a) = BoolVal.T) := by
        apply propext; constructor <;> intro h a
        · rw [← hupd a]; exact h a
        · rw [hupd a]; exact h a
      rw [hpe]
    · -- Bound variable differs from (s, x): recurse, with the free-for
      -- side condition `(s', i) ∉ FV(t)` giving update commutation.
      rw [if_neg hb]
      simp only [msFormulaEval, forallM]
      have hfree' : (s', i) ∉ msTermFV t ∧ msIsFreeFor A s x t := by
        have h : (s = s' ∧ x = i) ∨ ((s', i) ∉ msTermFV t ∧ msIsFreeFor A s x t) := hfree
        rcases h with ⟨hss, hxi⟩ | hr
        · exact absurd ⟨hss.symm, hxi.symm⟩ hb
        · exact hr
      obtain ⟨hnotin, hfreeA⟩ := hfree'
      have hupd : ∀ a : M.carrier s',
          msFormulaEval M (msFormulaSubst A s x t)
            (msAssignUpdate M v s' i a) =
          msFormulaEval M A (msAssignUpdate M
            (msAssignUpdate M v s x (msTermEval M v t)) s' i a) := fun a => by
        rw [ih hfreeA (msAssignUpdate M v s' i a)]
        -- `t`'s value is unchanged after updating at (s', i) (since
        -- (s', i) ∉ FV(t)), and the two distinct updates commute.
        have htval : msTermEval M (msAssignUpdate M v s' i a) t =
            msTermEval M v t :=
          Semantics.Substitution.msTermCoincidence M t _ v (fun y hy => by
            simp only [msAssignUpdate]
            by_cases h1 : y.1 = s'
            · subst h1
              by_cases h2 : y.2 = i
              · exact absurd (show (y.1, i) ∈ msTermFV t by rw [← h2]; exact hy) hnotin
              · simp [h2]
            · simp [h1])
        rw [htval]
        congr 1
        exact Semantics.Substitution.msAssignUpdate_swap M v s' s i x a
          (msTermEval M v t) (by
            intro hcontra; exact hb ⟨hcontra.1.symm, hcontra.2.symm⟩)
      have hpe : (∀ a, msFormulaEval M (msFormulaSubst A s x t)
            (msAssignUpdate M v s' i a) = BoolVal.T) =
          (∀ a, msFormulaEval M A (msAssignUpdate M
            (msAssignUpdate M v s x (msTermEval M v t)) s' i a) = BoolVal.T) := by
        apply propext; constructor <;> intro h a
        · rw [← hupd a]; exact h a
        · rw [hupd a]; exact h a
      rw [hpe]
  | ex s' i A ih =>
    intro v
    simp only [msFormulaSubst]
    by_cases hb : s' = s ∧ i = x
    · rw [if_pos hb]
      obtain ⟨hs, hi⟩ := hb
      subst hs; subst hi
      simp only [msFormulaEval, existsM]
      have hupd : ∀ a : M.carrier s',
          msFormulaEval M A (msAssignUpdate M
            (msAssignUpdate M v s' i (msTermEval M v t)) s' i a) =
          msFormulaEval M A (msAssignUpdate M v s' i a) := fun a => by
        rw [Semantics.Substitution.msAssignUpdate_idem]
      have hpe : (∃ a, msFormulaEval M A (msAssignUpdate M
            (msAssignUpdate M v s' i (msTermEval M v t)) s' i a) = BoolVal.T) =
          (∃ a, msFormulaEval M A (msAssignUpdate M v s' i a) = BoolVal.T) := by
        apply propext; constructor
        · rintro ⟨a, ha⟩; exact ⟨a, (hupd a) ▸ ha⟩
        · rintro ⟨a, ha⟩; exact ⟨a, (hupd a).symm ▸ ha⟩
      rw [hpe]
    · rw [if_neg hb]
      simp only [msFormulaEval, existsM]
      have hfree' : (s', i) ∉ msTermFV t ∧ msIsFreeFor A s x t := by
        have h : (s = s' ∧ x = i) ∨ ((s', i) ∉ msTermFV t ∧ msIsFreeFor A s x t) := hfree
        rcases h with ⟨hss, hxi⟩ | hr
        · exact absurd ⟨hss.symm, hxi.symm⟩ hb
        · exact hr
      obtain ⟨hnotin, hfreeA⟩ := hfree'
      have hupd : ∀ a : M.carrier s',
          msFormulaEval M (msFormulaSubst A s x t)
            (msAssignUpdate M v s' i a) =
          msFormulaEval M A (msAssignUpdate M
            (msAssignUpdate M v s x (msTermEval M v t)) s' i a) := fun a => by
        rw [ih hfreeA (msAssignUpdate M v s' i a)]
        have htval : msTermEval M (msAssignUpdate M v s' i a) t =
            msTermEval M v t :=
          Semantics.Substitution.msTermCoincidence M t _ v (fun y hy => by
            simp only [msAssignUpdate]
            by_cases h1 : y.1 = s'
            · subst h1
              by_cases h2 : y.2 = i
              · exact absurd (show (y.1, i) ∈ msTermFV t by rw [← h2]; exact hy) hnotin
              · simp [h2]
            · simp [h1])
        rw [htval]
        congr 1
        exact Semantics.Substitution.msAssignUpdate_swap M v s' s i x a
          (msTermEval M v t) (by
            intro hcontra; exact hb ⟨hcontra.1.symm, hcontra.2.symm⟩)
      have hpe : (∃ a, msFormulaEval M (msFormulaSubst A s x t)
            (msAssignUpdate M v s' i a) = BoolVal.T) =
          (∃ a, msFormulaEval M A (msAssignUpdate M
            (msAssignUpdate M v s x (msTermEval M v t)) s' i a) = BoolVal.T) := by
        apply propext; constructor
        · rintro ⟨a, ha⟩; exact ⟨a, by rw [← hupd a]; exact ha⟩
        · rintro ⟨a, ha⟩; exact ⟨a, by rw [hupd a]; exact ha⟩
      rw [hpe]

/-- Definition 5.4.5 (many-sorted companion): an `S`-indexed family of
per-sort term-carriers `H` is a (generated) term algebra iff each sort
carrier `H s` is nonempty, is closed under the matching-sort function
applications and constants, and is closed under sub-terms. Direct
many-sorted analogue of one-sorted `IsGeneratedTermAlgebra`
(chap5 Def 5.4.5), with the function/constant closure now sort-indexed:
`f`'s value lands in `H (L.funRank f).2` when its arguments lie in the
per-arity-sort carriers, and a constant of sort `s` lies in `H s`.

This is the textbook standing hypothesis "`H` is a term algebra" of
Lemma 5.4.5 (the Hintikka-set satisfiability lemma): the carrier of the
Herbrand structure built below is the sort-indexed family `{t // t ∈ H s}`,
which is a many-sorted `MSStructure` exactly because of these closure
conditions (nonemptiness gives `carrierNonempty`, function/constant
closure give `interpFunc`/`interpConst`, sub-term closure gives the
`msTermEvalIdentity` evaluation identity). -/
@[blueprint "chap10__lemma_10_4_1"]
structure MSIsGeneratedTermAlgebra (L : MSLanguage)
    (H : (s : L.SortType) → Set (MSTerm L s)) : Prop where
  /-- Each sort carrier `H s` is nonempty. -/
  nonempty : ∀ s : L.SortType, ∃ t : MSTerm L s, t ∈ H s
  /-- Closure under function symbols (sort-matched): if every argument
      `ts i` lies in the carrier of its arity sort, then `f ts` lies in
      the carrier of the output sort. -/
  closedFunc : ∀ (f : L.funSymbols)
    (ts : (i : Fin (L.funRank f).1.length) → MSTerm L ((L.funRank f).1.get i)),
    (∀ i, ts i ∈ H ((L.funRank f).1.get i)) →
    MSTerm.func f ts ∈ H (L.funRank f).2
  /-- Every constant `c` of sort `s` lies in `H s`. -/
  closedConst : ∀ (s : L.SortType) (c : L.constSymbols s),
    MSTerm.const s c ∈ H s
  /-- Sub-term closure: if `f ts` lies in the output carrier, then each
      argument `ts i` lies in the carrier of its arity sort. -/
  closedSubterm : ∀ (f : L.funSymbols)
    (ts : (i : Fin (L.funRank f).1.length) → MSTerm L ((L.funRank f).1.get i)),
    MSTerm.func f ts ∈ H (L.funRank f).2 →
    ∀ i, ts i ∈ H ((L.funRank f).1.get i)

-- ATTACH-BLOCKER: size gate: retain original helper span in front
/-- Lemma 10.4.1 (companion): if every free variable `(s', i)` of a
sort-`s` term `t` has its variable term `var s' i ∈ H s'`, then `t ∈ H s`.
Many-sorted analogue of one-sorted `termInH`. Proved by induction on `t`:
variables are in `H` by assumption, constants by `closedConst`, function
applications by `closedFunc` with the induction hypothesis. -/
theorem msTermInH {L : MSLanguage}
    {H : (s : L.SortType) → Set (MSTerm L s)}
    (hTA : MSIsGeneratedTermAlgebra L H) :
    {s : L.SortType} → (t : MSTerm L s) →
    (∀ p : MSVar L, p ∈ msTermFV t → MSTerm.var p.1 p.2 ∈ H p.1) →
    t ∈ H s := by
  intro s t
  induction t with
  | var s' i =>
    intro hvars
    exact hvars (s', i) rfl
  | const s' c =>
    intro _
    exact hTA.closedConst s' c
  | func f ts ih =>
    intro hvars
    exact hTA.closedFunc f ts (fun i => ih i (fun p hp =>
      hvars p ⟨i, hp⟩))

-- ===================================================================
-- Lemma 10.4.1 (companion): Herbrand structure on a term algebra H
-- ===================================================================

/-- Lemma 10.4.1 (companion): the Herbrand structure `H_S` built from a
many-sorted Hintikka set `S` over a term algebra `H`. The carrier of
sort `s` is the subtype `{t : MSTerm L s // t ∈ H s}`; functions and
constants are interpreted syntactically (landing back in `H` by the
term-algebra closure conditions), and the predicate interpretation tests
membership of the signed atom `T (P t…)` in `S`. Many-sorted analogue of
one-sorted `hintikkaStructure`. -/
@[blueprint "chap10__lemma_10_4_1"]
noncomputable def msHintikkaStructure {L : MSLanguage}
    (H : (s : L.SortType) → Set (MSTerm L s))
    (S : Set (MSSignedFormula L))
    (hTA : MSIsGeneratedTermAlgebra L H) : MSStructure L where
  carrier := fun s => { t : MSTerm L s // t ∈ H s }
  carrierNonempty := fun s =>
    let ⟨t, ht⟩ := hTA.nonempty s
    ⟨⟨t, ht⟩⟩
  interpFunc := fun f ts =>
    ⟨MSTerm.func f (fun i => (ts i).val),
     hTA.closedFunc f _ (fun i => (ts i).property)⟩
  interpConst := fun s c => ⟨MSTerm.const s c, hTA.closedConst s c⟩
  interpPred := fun P ts =>
    open Classical in
    if MSSignedFormula.trueF (MSFormula.pred P (fun i => (ts i).val)) ∈ S
    then BoolVal.T else BoolVal.F

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 10.4.1 (companion): the identity assignment for the Herbrand
structure. The sort-`s` variable `x_i` is sent to itself `⟨var s i, _⟩`
when `var s i ∈ H s`, otherwise to the chosen nonempty witness. Many-sorted
analogue of one-sorted `identityAssignment`. -/
noncomputable def msIdentityAssignment {L : MSLanguage}
    (H : (s : L.SortType) → Set (MSTerm L s))
    (S : Set (MSSignedFormula L))
    (hTA : MSIsGeneratedTermAlgebra L H) :
    MSAssignment (msHintikkaStructure H S hTA) :=
  fun s i =>
    open Classical in
    if h : MSTerm.var s i ∈ H s then ⟨MSTerm.var s i, h⟩
    else ⟨(hTA.nonempty s).choose, (hTA.nonempty s).choose_spec⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 10.4.1 (companion): evaluating a sort-`s` term `t ∈ H s` in the
Herbrand structure under the identity assignment yields `⟨t, ht⟩` — i.e.
`t` itself. Many-sorted analogue of one-sorted `termEvalIdentity`. Proved
by structural induction on `t`; the function case uses sub-term closure
(`closedSubterm`) so the recursive calls apply. -/
theorem msTermEvalIdentity {L : MSLanguage}
    {H : (s : L.SortType) → Set (MSTerm L s)}
    {S : Set (MSSignedFormula L)} {hTA : MSIsGeneratedTermAlgebra L H} :
    {s : L.SortType} → (t : MSTerm L s) → (ht : t ∈ H s) →
    msTermEval (msHintikkaStructure H S hTA)
      (msIdentityAssignment H S hTA) t = ⟨t, ht⟩ := by
  intro s t
  induction t with
  | var s' i =>
    intro ht
    simp only [msTermEval, varMeaning, msIdentityAssignment]
    exact dif_pos ht
  | const s' c =>
    intro _
    simp only [msTermEval, constM, msHintikkaStructure]
  | func f ts ih =>
    intro ht
    simp only [msTermEval, funM, msHintikkaStructure]
    apply Subtype.ext
    simp only
    congr 1
    funext i
    have hti : ts i ∈ H ((L.funRank f).1.get i) := hTA.closedSubterm f ts ht i
    exact congrArg Subtype.val (ih i hti)

-- ===================================================================
-- Lemma 10.4.1 (companion): formula depth, for the satisfaction induction
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 10.4.1 (companion): the connective/quantifier depth of a
many-sorted formula; atomic formulae (falsum, pred, eq_) have depth 0.
Used for the well-founded induction in the Hintikka satisfiability
proof (the quantifier cases need the claim for the same-depth instance
`A[t/x]`). Many-sorted analogue of one-sorted `formulaDepth`. -/
def msFormulaDepth {L : MSLanguage} : MSFormula L → Nat
  | .falsum       => 0
  | .pred _ _     => 0
  | .eq_ _ _ _ _  => 0
  | .neg A        => 1 + msFormulaDepth A
  | .conj A B     => 1 + msFormulaDepth A + msFormulaDepth B
  | .disj A B     => 1 + msFormulaDepth A + msFormulaDepth B
  | .impl A B     => 1 + msFormulaDepth A + msFormulaDepth B
  | .equiv_ A B   => 1 + msFormulaDepth A + msFormulaDepth B
  | .all _ _ A    => 1 + msFormulaDepth A
  | .ex _ _ A     => 1 + msFormulaDepth A

-- ATTACH-BLOCKER: size gate: retain original helper span in front
/-- Lemma 10.4.1 (companion): substitution preserves formula depth.
Many-sorted analogue of one-sorted `formulaSubstN_depth`. -/
theorem msFormulaSubst_depth {L : MSLanguage} [DecidableEq L.SortType]
    (A : MSFormula L) (u : L.SortType) (x : Nat) (t : MSTerm L u) :
    msFormulaDepth (msFormulaSubst A u x t) = msFormulaDepth A := by
  induction A with
  | falsum => rfl
  | pred _ _ => rfl
  | eq_ _ _ _ _ => rfl
  | neg A ih => simp [msFormulaSubst, msFormulaDepth, ih]
  | conj A B ihA ihB => simp [msFormulaSubst, msFormulaDepth, ihA, ihB]
  | disj A B ihA ihB => simp [msFormulaSubst, msFormulaDepth, ihA, ihB]
  | impl A B ihA ihB => simp [msFormulaSubst, msFormulaDepth, ihA, ihB]
  | equiv_ A B ihA ihB => simp [msFormulaSubst, msFormulaDepth, ihA, ihB]
  | all s i A ih =>
    simp only [msFormulaSubst]; split
    · rfl
    · simp only [msFormulaDepth]; omega
  | ex s i A ih =>
    simp only [msFormulaSubst]; split
    · rfl
    · simp only [msFormulaDepth]; omega

/-- Theorem 10.4.1 (companion): the many-sorted Hintikka-set
satisfiability bridge used by the completeness (→) direction. If `S` is
a many-sorted Hintikka set with respect to the `S`-indexed term-carrier
family `H` — which is a term algebra (`MSIsGeneratedTermAlgebra`, the
textbook standing hypothesis of Lemma 5.4.5) — then `S` is satisfiable
in the Herbrand structure built on `H`: there is a structure `M` and
assignment `v` making every `T A ∈ S` evaluate to `T` and every
`F A ∈ S` evaluate to `F`. This is the heart of the many-sorted
completeness argument (the §5.5 Hintikka satisfiability lemma transported
to the many-sorted algebra). It references `MSIsHintikkaSet`, so the
predicate is genuinely used by the completeness infrastructure.

The proof builds the Herbrand structure `msHintikkaStructure H S hTA`
with the identity assignment `msIdentityAssignment H S hTA`, then proves
the key satisfaction claim by well-founded induction on `msFormulaDepth`
(8 cases, atomic + connective + quantifier), using the H0–H6 Hintikka
conditions and the proven substitution-evaluation lemma
`msFormulaSubstEvalDirect`. Direct many-sorted analogue of one-sorted
`hintikka_set_satisfiable`. -/
@[blueprint "chap10__theorem_10_4_1"]
theorem msHintikkaSetSatisfiable {L : MSLanguage} [DecidableEq L.SortType]
    (H : (s : L.SortType) → Set (MSTerm L s))
    (S : Set (MSSignedFormula L)) (hTA : MSIsGeneratedTermAlgebra L H)
    (hHS : MSIsHintikkaSet L H S) :
    ∃ (M : MSStructure L) (v : MSAssignment M),
      (∀ A : MSFormula L, MSSignedFormula.trueF A ∈ S →
        msFormulaEval M A v = BoolVal.T) ∧
      (∀ A : MSFormula L, MSSignedFormula.falseF A ∈ S →
        msFormulaEval M A v = BoolVal.F) 

end LCS.FirstOrder.ManySorted.Gentzen
end

