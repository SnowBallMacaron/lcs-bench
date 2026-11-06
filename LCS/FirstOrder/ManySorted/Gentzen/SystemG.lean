import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Semantics.Substitution
import LCS.Propositional.Semantics
import Attach
import LCS.FirstOrder.ManySorted.Gentzen.SystemG.ProofsStamp

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

end LCS.FirstOrder.ManySorted.Gentzen
end
