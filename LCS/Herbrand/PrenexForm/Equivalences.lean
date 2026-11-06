import LCS.Item
import LCS.Util
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Semantics.Equivalence
import LCS.FirstOrder.SemanticsN.Substitution
import Attach
import LCS.Herbrand.PrenexForm.Equivalences.ProofsStamp

/-! # Herbrand.PrenexForm.Equivalences
    Chapter 7, Section 2.1: Lemma 7.2.1, the valid equivalences used to move
    quantifiers outward (quantifiers through implication, negation,
    conjunction and disjunction, distributivity, renaming of bound variables), with the
    mirrored forms pulling a quantifier out of the right operand.

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.PrenexForm
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Equivalence
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN.Substitution

-- retained: used by LCS.Herbrand.NNFHauptsatz.Soundness
/-- When x is not free in formula F, changing the assignment at x does
    not affect the evaluation of F. A direct consequence of the
    coincidence lemma (Lemma 5.3.3). -/
theorem formulaEval_assignUpdate_irrelevant {L : Language}
    {M : Structure L} (s : Assignment M) (x : Nat) (a : M.carrier)
    (F : FormulaN L) (hfree : ¬ Membership.mem (formulaFVN F) x) :
    formulaEvalN M F (assignUpdate s x a) ↔ formulaEvalN M F s :=
-- BEGIN PROOF
  coincidenceLemmaN M F (assignUpdate s x a) s (fun y hy => by
    unfold assignUpdate; split
    · rename_i heq; subst heq; exact absurd hy hfree
    · rfl)

-- Lemma 7.2.1(a) first sentence: Universal/existential implication left

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (a) (companion): Prenex equivalences -- quantifier extraction rules for pulling quantifiers through connectives. forall x(A impl B) equiv (exists x A impl B), where x does not occur free in B. The universal quantifier on the antecedent of an implication can be pulled out as an existential when x is not free in B. -/
theorem prenex_equiv_a_univ_impl_left {L : Language}
    (x : Nat) (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN B) x) :
    foLogEquivN
      (FormulaN.all x (FormulaN.impl A B))
      (FormulaN.impl (FormulaN.ex x A) B) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  constructor
  · intro h ⟨a, hA⟩
    exact (formulaEval_assignUpdate_irrelevant s x a B hfree).mp (h a hA)
  · intro h a hA
    exact (formulaEval_assignUpdate_irrelevant s x a B hfree).mpr (h ⟨a, hA⟩)

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (a) (companion): exists x(A impl B) equiv (forall x A impl B), where x does not occur free in B. The existential quantifier on the antecedent of an implication can be pulled out as a universal when x is not free in B. -/
theorem prenex_equiv_a_ex_impl_left {L : Language}
    (x : Nat) (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN B) x) :
    foLogEquivN
      (FormulaN.ex x (FormulaN.impl A B))
      (FormulaN.impl (FormulaN.all x A) B) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  constructor
  · intro ⟨a, h⟩ hAll
    exact (formulaEval_assignUpdate_irrelevant s x a B hfree).mp (h (hAll a))
  · intro h
    by_cases hall : ∀ a : M.carrier, formulaEvalN M A (assignUpdate s x a)
    · have hb := h hall
      obtain ⟨w⟩ := M.carrierNonempty
      exact ⟨w, fun _ =>
        (formulaEval_assignUpdate_irrelevant s x _ B hfree).mpr hb⟩
    · obtain ⟨a, hna⟩ := Classical.not_forall.mp hall
      exact ⟨a, fun ha => absurd ha hna⟩

-- Lemma 7.2.1(a) second sentence: Universal/existential implication right

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (a) (companion): forall x(A impl B) equiv (A impl forall x B), where x does not occur free in A. The universal quantifier on the consequent of an implication can be pulled out when x is not free in A. -/
theorem prenex_equiv_b_univ_impl_right {L : Language}
    (x : Nat) (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN A) x) :
    foLogEquivN
      (FormulaN.all x (FormulaN.impl A B))
      (FormulaN.impl A (FormulaN.all x B)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  constructor
  · intro h hA a
    have := h a
    exact this ((formulaEval_assignUpdate_irrelevant s x a A hfree).mpr hA)
  · intro h a hA
    have hA' := (formulaEval_assignUpdate_irrelevant s x a A hfree).mp hA
    exact h hA' a

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (a) (companion): exists x(A impl B) equiv (A impl exists x B), where x does not occur free in A. The existential quantifier on the consequent of an implication can be pulled out when x is not free in A. -/
theorem prenex_equiv_b_ex_impl_right {L : Language}
    (x : Nat) (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN A) x) :
    foLogEquivN
      (FormulaN.ex x (FormulaN.impl A B))
      (FormulaN.impl A (FormulaN.ex x B)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  constructor
  · intro ⟨a, h⟩ hA
    exact ⟨a, h ((formulaEval_assignUpdate_irrelevant s x a A hfree).mpr hA)⟩
  · intro h
    by_cases hA : formulaEvalN M A s
    · obtain ⟨a, hb⟩ := h hA
      exact ⟨a, fun _ => hb⟩
    · obtain ⟨w⟩ := M.carrierNonempty
      exact ⟨w, fun ha =>
        absurd ((formulaEval_assignUpdate_irrelevant s x w A hfree).mp ha) hA⟩

-- Lemma 7.2.1(b): Negation pull

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (b) (companion): not forall x A equiv exists x not A. The negation of a universal quantifier is equivalent to an existential quantifier with negated body. No side conditions. -/
theorem prenex_equiv_c_neg_all {L : Language}
    (x : Nat) (A : FormulaN L) :
    foLogEquivN
      (FormulaN.neg (FormulaN.all x A))
      (FormulaN.ex x (FormulaN.neg A)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  exact ⟨Classical.not_forall.mp, Classical.not_forall.mpr⟩

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (b) (companion): not exists x A equiv forall x not A. The negation of an existential quantifier is equivalent to a universal quantifier with negated body. No side conditions. -/
theorem prenex_equiv_c_neg_ex {L : Language}
    (x : Nat) (A : FormulaN L) :
    foLogEquivN
      (FormulaN.neg (FormulaN.ex x A))
      (FormulaN.all x (FormulaN.neg A)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  exact ⟨not_exists.mp, not_exists.mpr⟩

-- Lemma 7.2.1(c): Free-variable pull from disjunction/conjunction

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (c) (companion): (forall x A or B) equiv forall x(A or B), where x does not occur free in B. A universal quantifier can be pulled out of a disjunction when the variable is not free in the other disjunct. -/
theorem prenex_equiv_d_univ_disj {L : Language}
    (x : Nat) (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN B) x) :
    foLogEquivN
      (FormulaN.disj (FormulaN.all x A) B)
      (FormulaN.all x (FormulaN.disj A B)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  constructor
  · intro h a
    match h with
    | Or.inl hAll => exact Or.inl (hAll a)
    | Or.inr hB => exact Or.inr ((formulaEval_assignUpdate_irrelevant s x a B hfree).mpr hB)
  · intro h
    by_cases hB : formulaEvalN M B s
    · exact Or.inr hB
    · exact Or.inl (fun a => (h a).elim id (fun hb =>
        absurd ((formulaEval_assignUpdate_irrelevant s x a B hfree).mp hb) hB))

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (c) (companion): (forall x A and B) equiv forall x(A and B), where x does not occur free in B. A universal quantifier can be pulled out of a conjunction when the variable is not free in the other conjunct. -/
theorem prenex_equiv_d_univ_conj {L : Language}
    (x : Nat) (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN B) x) :
    foLogEquivN
      (FormulaN.conj (FormulaN.all x A) B)
      (FormulaN.all x (FormulaN.conj A B)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  constructor
  · intro ⟨hAll, hB⟩ a
    exact ⟨hAll a, (formulaEval_assignUpdate_irrelevant s x a B hfree).mpr hB⟩
  · intro h
    exact ⟨fun a => (h a).1,
           (formulaEval_assignUpdate_irrelevant s x (Classical.choice M.carrierNonempty)
              B hfree).mp (h (Classical.choice M.carrierNonempty)).2⟩

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (c) (companion): (exists x A or B) equiv exists x(A or B), where x does not occur free in B. An existential quantifier can be pulled out of a disjunction when the variable is not free in the other disjunct. -/
theorem prenex_equiv_d_ex_disj {L : Language}
    (x : Nat) (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN B) x) :
    foLogEquivN
      (FormulaN.disj (FormulaN.ex x A) B)
      (FormulaN.ex x (FormulaN.disj A B)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  constructor
  · intro h
    match h with
    | Or.inl ⟨a, ha⟩ => exact ⟨a, Or.inl ha⟩
    | Or.inr hB => exact ⟨Classical.choice M.carrierNonempty,
        Or.inr ((formulaEval_assignUpdate_irrelevant s x _ B hfree).mpr hB)⟩
  · intro ⟨a, h⟩
    match h with
    | Or.inl ha => exact Or.inl ⟨a, ha⟩
    | Or.inr hb => exact Or.inr ((formulaEval_assignUpdate_irrelevant s x a B hfree).mp hb)

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (c) (companion): (exists x A and B) equiv exists x(A and B), where x does not occur free in B. An existential quantifier can be pulled out of a conjunction when the variable is not free in the other conjunct. -/
theorem prenex_equiv_d_ex_conj {L : Language}
    (x : Nat) (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN B) x) :
    foLogEquivN
      (FormulaN.conj (FormulaN.ex x A) B)
      (FormulaN.ex x (FormulaN.conj A B)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  constructor
  · intro ⟨⟨a, ha⟩, hB⟩
    exact ⟨a, ha, (formulaEval_assignUpdate_irrelevant s x a B hfree).mpr hB⟩
  · intro ⟨a, ha, hb⟩
    exact ⟨⟨a, ha⟩, (formulaEval_assignUpdate_irrelevant s x a B hfree).mp hb⟩

-- Lemma 7.2.1(d): Distributive





-- Lemma 7.2.1(e): alpha-renaming

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (e) (companion): forall x A equiv forall y A[y/x], where y is free for x in A and y does not occur free in A unless y = x. Allows renaming the bound variable of a universal quantifier. -/
theorem prenex_equiv_f_univ_rename {L : Language}
    (x y : Nat) (A : FormulaN L)
    (hfreeFor : isFreeForN (Term.var y) x A)
    (hnotFree : ¬ Membership.mem (formulaFVN A) y ∨ y = x) :
    foLogEquivN
      (FormulaN.all x A)
      (FormulaN.all y (formulaSubstN A (Term.var y) x)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  have key : ∀ (a : M.carrier),
      formulaEvalN M A (assignUpdate s x a) ↔
      formulaEvalN M (formulaSubstN A (Term.var y) x) (assignUpdate s y a) := by
    intro a
    rw [formulaSubstEvalDirectN (assignUpdate s y a) A (Term.var y) x hfreeFor]
    simp only [termEval, assignUpdate, ite_true]
    exact coincidenceLemmaN M A _ _ (fun z hz => by
      unfold assignUpdate
      by_cases hzx : z = x
      · simp [hzx]
      · simp [hzx]
        by_cases hzy : z = y
        · subst hzy; exact absurd hz (hnotFree.elim id (fun heq => absurd heq hzx))
        · simp [hzy])
  exact ⟨fun h a => (key a).mp (h a), fun h a => (key a).mpr (h a)⟩

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 7.2.1 (e) (companion): exists x A equiv exists y A[y/x], where y is free for x in A and y does not occur free in A unless y = x. Allows renaming the bound variable of an existential quantifier. -/
theorem prenex_equiv_f_ex_rename {L : Language}
    (x y : Nat) (A : FormulaN L)
    (hfreeFor : isFreeForN (Term.var y) x A)
    (hnotFree : ¬ Membership.mem (formulaFVN A) y ∨ y = x) :
    foLogEquivN
      (FormulaN.ex x A)
      (FormulaN.ex y (formulaSubstN A (Term.var y) x)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  have key : ∀ (a : M.carrier),
      formulaEvalN M A (assignUpdate s x a) ↔
      formulaEvalN M (formulaSubstN A (Term.var y) x) (assignUpdate s y a) := by
    intro a
    rw [formulaSubstEvalDirectN (assignUpdate s y a) A (Term.var y) x hfreeFor]
    simp only [termEval, assignUpdate, ite_true]
    exact coincidenceLemmaN M A _ _ (fun z hz => by
      unfold assignUpdate
      by_cases hzx : z = x
      · simp [hzx]
      · simp [hzx]
        by_cases hzy : z = y
        · subst hzy; exact absurd hz (hnotFree.elim id (fun heq => absurd heq hzx))
        · simp [hzy])
  exact ⟨fun ⟨a, ha⟩ => ⟨a, (key a).mp ha⟩, fun ⟨a, ha⟩ => ⟨a, (key a).mpr ha⟩⟩

-- ===================================================================
-- Lemma 7.2.1 (unified bundle): All prenex equivalences
-- ===================================================================

/-- Lemma 7.2.1: The following formulae are valid. (a) forall x(A impl B) equiv (exists x A impl B) and exists x(A impl B) equiv (forall x A impl B), where x does not occur free in B. forall x(A impl B) equiv (A impl forall x B) and exists x(A impl B) equiv (A impl exists x B), where x does not occur free in A. (b) not forall x A equiv exists x not A and not exists x A equiv forall x not A. (c) (forall x A or B) equiv forall x(A or B), (forall x A and B) equiv forall x(A and B), (exists x A or B) equiv exists x(A or B), and (exists x A and B) equiv exists x(A and B), where x does not occur free in B. (d) forall x(A and B) equiv forall x A and forall x B, and exists x(A or B) equiv exists x A or exists x B. (e) forall x A equiv forall y A[y/x] and exists x A equiv exists y A[y/x], where y is free for x in A, and y does not occur free in A unless y = x (i.e., y is not in FV(A) - {x}). The bundle simply assembles the 14 individual equivalences already proved as `prenex_equiv_*` helpers in this file. -/
@[blueprint "chap7__lemma_7_2_1" (main := true)]
theorem lemma_7_2_1 {L : Language} :
    -- (a) implication, first sentence: x ∉ FV(B)
    (∀ (x : Nat) (A B : FormulaN L),
        ¬ Membership.mem (formulaFVN B) x →
        foLogEquivN
          (FormulaN.all x (FormulaN.impl A B))
          (FormulaN.impl (FormulaN.ex x A) B)) ∧
    (∀ (x : Nat) (A B : FormulaN L),
        ¬ Membership.mem (formulaFVN B) x →
        foLogEquivN
          (FormulaN.ex x (FormulaN.impl A B))
          (FormulaN.impl (FormulaN.all x A) B)) ∧
    -- (a) implication, second sentence: x ∉ FV(A)
    (∀ (x : Nat) (A B : FormulaN L),
        ¬ Membership.mem (formulaFVN A) x →
        foLogEquivN
          (FormulaN.all x (FormulaN.impl A B))
          (FormulaN.impl A (FormulaN.all x B))) ∧
    (∀ (x : Nat) (A B : FormulaN L),
        ¬ Membership.mem (formulaFVN A) x →
        foLogEquivN
          (FormulaN.ex x (FormulaN.impl A B))
          (FormulaN.impl A (FormulaN.ex x B))) ∧
    -- (b) negation pull
    (∀ (x : Nat) (A : FormulaN L),
        foLogEquivN
          (FormulaN.neg (FormulaN.all x A))
          (FormulaN.ex x (FormulaN.neg A))) ∧
    (∀ (x : Nat) (A : FormulaN L),
        foLogEquivN
          (FormulaN.neg (FormulaN.ex x A))
          (FormulaN.all x (FormulaN.neg A))) ∧
    -- (c) free-variable pull from disj/conj, x ∉ FV(B)
    (∀ (x : Nat) (A B : FormulaN L),
        ¬ Membership.mem (formulaFVN B) x →
        foLogEquivN
          (FormulaN.disj (FormulaN.all x A) B)
          (FormulaN.all x (FormulaN.disj A B))) ∧
    (∀ (x : Nat) (A B : FormulaN L),
        ¬ Membership.mem (formulaFVN B) x →
        foLogEquivN
          (FormulaN.conj (FormulaN.all x A) B)
          (FormulaN.all x (FormulaN.conj A B))) ∧
    (∀ (x : Nat) (A B : FormulaN L),
        ¬ Membership.mem (formulaFVN B) x →
        foLogEquivN
          (FormulaN.disj (FormulaN.ex x A) B)
          (FormulaN.ex x (FormulaN.disj A B))) ∧
    (∀ (x : Nat) (A B : FormulaN L),
        ¬ Membership.mem (formulaFVN B) x →
        foLogEquivN
          (FormulaN.conj (FormulaN.ex x A) B)
          (FormulaN.ex x (FormulaN.conj A B))) ∧
    -- (d) distributive
    (∀ (x : Nat) (A B : FormulaN L),
        foLogEquivN
          (FormulaN.all x (FormulaN.conj A B))
          (FormulaN.conj (FormulaN.all x A) (FormulaN.all x B))) ∧
    (∀ (x : Nat) (A B : FormulaN L),
        foLogEquivN
          (FormulaN.ex x (FormulaN.disj A B))
          (FormulaN.disj (FormulaN.ex x A) (FormulaN.ex x B))) ∧
    -- (e) alpha-renaming: y free for x in A, y ∉ FV(A) - {x}
    (∀ (x y : Nat) (A : FormulaN L),
        isFreeForN (Term.var y) x A →
        (¬ Membership.mem (formulaFVN A) y ∨ y = x) →
        foLogEquivN
          (FormulaN.all x A)
          (FormulaN.all y (formulaSubstN A (Term.var y) x))) ∧
    (∀ (x y : Nat) (A : FormulaN L),
        isFreeForN (Term.var y) x A →
        (¬ Membership.mem (formulaFVN A) y ∨ y = x) →
        foLogEquivN
          (FormulaN.ex x A)
          (FormulaN.ex y (formulaSubstN A (Term.var y) x)))

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Pull a universal quantifier out of the right side of conjunction. -/
theorem prenex_conj_right_all {L : Language} (x : Nat)
    (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN A) x) :
    foLogEquivN (FormulaN.conj A (FormulaN.all x B))
      (FormulaN.all x (FormulaN.conj A B)) :=
-- BEGIN PROOF
  foLogEquivN_trans (foLogEquivN_conj_comm A _)
    (foLogEquivN_trans (prenex_equiv_d_univ_conj x B A hfree)
      (foLogEquivN_all x (foLogEquivN_conj_comm B A)))

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Pull an existential quantifier out of the right side of conjunction. -/
theorem prenex_conj_right_ex {L : Language} (x : Nat)
    (A B : FormulaN L)
    (hfree : ¬ Membership.mem (formulaFVN A) x) :
    foLogEquivN (FormulaN.conj A (FormulaN.ex x B))
      (FormulaN.ex x (FormulaN.conj A B)) :=
-- BEGIN PROOF
  foLogEquivN_trans (foLogEquivN_conj_comm A _)
    (foLogEquivN_trans (prenex_equiv_d_ex_conj x B A hfree)
      (foLogEquivN_ex x (foLogEquivN_conj_comm B A)))

end LCS.Herbrand.PrenexForm
