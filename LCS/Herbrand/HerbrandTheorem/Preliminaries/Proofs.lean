import LCS.Herbrand.HerbrandTheorem.Preliminaries

namespace LCS.Herbrand.HerbrandTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.CutElim.LK
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen
open LCS.CutElim.Interpolation.Equality

helper /-- Lemma 7.5.1 (helper): If -> B is LK-provable, then
    -> forall y B is LK-provable. Applies the allRight rule with
    eigenvariable y. The eigenvariable condition is satisfied because
    y is not free in all y B. -/
theorem folkProvable_allRight {L : Language}
    (y : Nat) (B : FormulaN L)
    (hprov : folkProvable (Sequent.mk [] [B])) :
    folkProvable (Sequent.mk [] [FormulaN.all y B]) := by
-- BEGIN PROOF
  obtain ⟨t⟩ := hprov
  have hfresh :
      ∀ F ∈ (Sequent.mk [] ([] ++ [FormulaN.all y B])).antecedent ++
          (Sequent.mk [] ([] ++ [FormulaN.all y B])).succedent,
        y ∉ formulaFVN F := by
    intro F hF
    simp only [List.nil_append, List.mem_singleton] at hF
    subst F
    rintro ⟨_, hy⟩
    exact hy rfl
  have t' :
      FOLKProofTree
        (Sequent.mk [] [formulaSubstN B (Term.var y) y]) := by
    simpa only [formulaSubstN_var_self] using t
  exact ⟨.onePremise
    (.allRight y y B [] [] hfresh
      (LCS.CutElim.Interpolation.isFreeForN_var_self B y))
    t'⟩

helper /-- Lemma 7.5.1 (helper): If -> forall y B is LK-provable, then
    -> B is LK-provable. Uses cut with the derivation
    [forall y B] -> [B] obtained from allLeft + axiom. -/
theorem folkProvable_allLeft_cut {L : Language}
    (y : Nat) (B : FormulaN L)
    (hprov : folkProvable (Sequent.mk [] [FormulaN.all y B])) :
    folkProvable (Sequent.mk [] [B]) := by
-- BEGIN PROOF
  obtain ⟨t⟩ := hprov
  have tAx : FOLKProofTree (Sequent.mk [B] [B]) :=
    .axiom_ _ ⟨B, rfl, rfl⟩
  have tSub :
      FOLKProofTree
        (Sequent.mk [formulaSubstN B (Term.var y) y] [B]) := by
    simpa only [formulaSubstN_var_self] using tAx
  have tAllLeft :
      FOLKProofTree (Sequent.mk [FormulaN.all y B] [B]) :=
    .onePremise
      (.allLeft (Term.var y) y B [] [B]
        (LCS.CutElim.Interpolation.isFreeForN_var_self B y))
      tSub
  exact ⟨by
    simpa using
      FOLKProofTree.twoPremise
        (.cut (FormulaN.all y B) [] [] [] [B]) t tAllLeft⟩

helper /-- Lemma 7.5.1 (helper): For any formula A and variable list fvs,
    -> A is LK-provable iff -> universalClosure A fvs is LK-provable.
    Proved by induction on fvs using folkProvable_allRight (forward)
    and folkProvable_allLeft_cut (backward). -/
theorem universalClosure_iff_folkProvable {L : Language}
    (A : FormulaN L) (fvs : List Nat) :
    folkProvable (Sequent.mk [] [A]) ↔
    folkProvable (Sequent.mk [] [universalClosure A fvs]) := by
-- BEGIN PROOF
  induction fvs with
  | nil =>
      simp only [universalClosure, List.foldr_nil]
  | cons y ys ih =>
      constructor
      · intro hprov
        simpa only [universalClosure, List.foldr_cons] using
          folkProvable_allRight y (universalClosure A ys) (ih.mp hprov)
      · intro hprov
        apply ih.mpr
        apply folkProvable_allLeft_cut y (universalClosure A ys)
        simpa only [universalClosure, List.foldr_cons] using hprov

helper /-- Lemma 7.5.1 (LK variant): Let A be a rectified formula with
    FV(A) = {y_1, ..., y_n}. The sequent -> A is LK-provable if and
    only if the sequent -> forall y_1 ... forall y_n A is LK-provable.

    Stated as a biconditional between provability of the sequent with
    A as sole succedent and provability of the sequent with the
    universal closure of A.

    STANDING ASSUMPTION #2 (§5.3.6+): formulae are rectified; encoded
    by `hRect`.
    STANDING ASSUMPTION #11 (§5.4-5.5): LK is for languages without
    equality; encoded by `hNoEq : L.withoutEquality`.

    Proof: By induction on the list of free variables fvs. Each
    forward step applies allRight (the eigenvariable y is not free in
    all y B). Each backward step uses cut with allLeft + axiom to
    strip one universal quantifier. -/
theorem universal_closure_provability_iff_LK {L : Language}
    (A : FormulaN L)
    (hRect : isRectified A)
    (fvs : List Nat)
    (hFVs : ∀ x, x ∈ fvs ↔ Membership.mem (formulaFVN A) x)
    (hNoEq : L.withoutEquality) :
    folkProvable (Sequent.mk [] [A]) ↔
    folkProvable
      (Sequent.mk [] [universalClosure A fvs]) := by
-- BEGIN PROOF
  clear hRect hFVs hNoEq
  exact universalClosure_iff_folkProvable A fvs

helper /-- Lemma 7.5.1 (LKe variant): The same biconditional holds for
    LKe-provability: the sequent -> A is LKe-provable if and only if
    the sequent -> forall y_1 ... forall y_n A is LKe-provable,
    provided A is rectified. LKe is the sequent calculus for languages
    with equality (§6.3), so no no-equality hypothesis is required.

    STANDING ASSUMPTION #2 (§5.3.6+): formulae are rectified; encoded
    by `hRect`. -/
theorem universal_closure_provability_iff_LKe {L : Language}
    (A : FormulaN L)
    (hRect : isRectified A)
    (fvs : List Nat)
    (hFVs : ∀ x, x ∈ fvs ↔ Membership.mem (formulaFVN A) x) :
    lkeProvable (Sequent.mk [] [A]) ↔
    lkeProvable
      (Sequent.mk [] [universalClosure A fvs]) := by
-- BEGIN PROOF
  clear hRect hFVs
  have lkeProvable_all_iff (y : Nat) (B : FormulaN L) :
      lkeProvable (Sequent.mk [] [B]) ↔
      lkeProvable (Sequent.mk [] [FormulaN.all y B]) := by
    constructor
    · intro hprov
      apply lkeProvable_of_universally_valid
      intro M s
      simp only [LCS.FirstOrder.SemanticsN.formulaEvalN]
      intro a
      have hvalid := lkeProvable_valid (Sequent.mk [] [B]) hprov
      simpa using hvalid M (assignUpdate s y a) (by simp)
    · intro hprov
      apply lkeProvable_of_universally_valid
      intro M s
      have hvalid :=
        lkeProvable_valid (Sequent.mk [] [FormulaN.all y B]) hprov
      have hall :
          LCS.FirstOrder.SemanticsN.formulaEvalN M (FormulaN.all y B) s := by
        simpa using hvalid M s (by simp)
      simp only [LCS.FirstOrder.SemanticsN.formulaEvalN] at hall
      have hself : assignUpdate s y (s y) = s := by
        funext x
        simp only [assignUpdate]
        split
        · rename_i hxy
          subst x
          rfl
        · rfl
      simpa only [hself] using hall (s y)
  induction fvs with
  | nil =>
      simp only [universalClosure, List.foldr_nil]
  | cons y ys ih =>
      constructor
      · intro hprov
        simpa only [universalClosure, List.foldr_cons] using
          (lkeProvable_all_iff y (universalClosure A ys)).mp (ih.mp hprov)
      · intro hprov
        apply ih.mpr
        apply (lkeProvable_all_iff y (universalClosure A ys)).mpr
        simpa only [universalClosure, List.foldr_cons] using hprov

proof_of lemma_7_5_1 := by
  -- BEGIN PROOF
  refine ⟨fun hNoEq => ?_, ?_⟩
  · exact universal_closure_provability_iff_LK A hRect fvs hFVs hNoEq
  · exact universal_closure_provability_iff_LKe A hRect fvs hFVs

end LCS.Herbrand.HerbrandTheorem
