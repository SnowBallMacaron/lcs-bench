import LCS.Herbrand.SharpenedHauptsatz.Permutability

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.Gentzen

open LCS.CutElim.LK

open LCS.CutElim.LKe

open LCS.Herbrand.SharpenedHauptsatz

open LCS.Herbrand.PrenexForm

open LCS.FirstOrder.SemanticsN

namespace LCS.Herbrand.SharpenedHauptsatz.Permutability

helper /-- Lemma 7.3.3 (companion theorem, §7.1): If an ordinary LK propositional
inference has a prenex principal formula, each of its active side formulae is
quantifier-free. The principal formula has a propositional outer connective,
so its prenex prefix is empty. Context formulae are unrestricted. -/
theorem Herbrand.SharpenedHauptsatz.Permutability.propositionalSide_quantifierFree_of_prenex {L : Language}
    (R : AnyFOLKStep L) (hlog : R.isLogical) (hnq : ¬ R.isQuantifier)
    (P : FormulaN L) (hprincipal : R.principalFormula = some P)
    (hprenex : isPrenex P) :
    ∀ A ∈ R.sideFormulae, isQuantifierFree A := by
-- BEGIN PROOF
  cases R with
  | one r =>
    cases r <;>
      simp_all [AnyFOLKStep.isLogical, AnyFOLKStep.isQuantifier,
        AnyFOLKStep.principalFormula, AnyFOLKStep.sideFormulae,
        FOLKStep1.isLogical, FOLKStep1.isQuantifier,
        FOLKStep1.principalFormula, FOLKStep1.sideFormulae] <;>
      subst P <;> simp_all [isPrenex, isQuantifierFree]
  | two r =>
    cases r <;>
      simp_all [AnyFOLKStep.isLogical, AnyFOLKStep.isQuantifier,
        AnyFOLKStep.principalFormula, AnyFOLKStep.sideFormulae,
        FOLKStep2.isLogical, FOLKStep2.isQuantifier,
        FOLKStep2.principalFormula, FOLKStep2.sideFormulae] <;>
      subst P <;> simp_all [isPrenex, isQuantifierFree]

helper /-- Lemma 7.3.3 (companion theorem, §7.1): Prenexness of the principal formula
of an ordinary LK propositional inference excludes the side-formula obstruction:
the quantified principal formula of an ordinary quantifier inference cannot be
one of its active side formulae. This derives the syntactic proviso from local
rule shapes; it asserts no permutation or ancestry relationship. -/
theorem Herbrand.SharpenedHauptsatz.Permutability.principalNotSideOf_of_prenex {L : Language}
    (Q R : AnyFOLKStep L) (hq : Q.isQuantifier)
    (hlog : R.isLogical) (hnq : ¬ R.isQuantifier)
    (P : FormulaN L) (hprincipal : R.principalFormula = some P)
    (hprenex : isPrenex P) : principalNotSideOf Q R := by
-- BEGIN PROOF
  have hnotQF : ∀ A, Q.principalFormula = some A → ¬ isQuantifierFree A := by
    cases Q with
    | one r =>
      cases r <;>
        simp_all [AnyFOLKStep.isQuantifier, AnyFOLKStep.principalFormula,
          FOLKStep1.isQuantifier, FOLKStep1.principalFormula, isQuantifierFree]
    | two r =>
      simp_all [AnyFOLKStep.isQuantifier, FOLKStep2.isQuantifier]
  unfold principalNotSideOf
  split
  · trivial
  · rename_i A hA
    intro hside
    exact hnotQF A hA
      (propositionalSide_quantifierFree_of_prenex R hlog hnq P hprincipal hprenex A hside)

proof_of permutability_quantifier_with_rule := open LCS.Herbrand.SharpenedHauptsatz.Permutability.Proofs.Herbrand.SharpenedHauptsatz.Permutability in
  by
  -- BEGIN PROOF
    -- REPAIR(T7-40): proof pending
    sorry


proof_of permutability_quantifier_with_rule_LKe := open LCS.Herbrand.SharpenedHauptsatz.Permutability.Proofs.Herbrand.SharpenedHauptsatz.Permutability in
  by
    -- REPAIR(T7-40): proof pending
    sorry


helper theorem Herbrand.SharpenedHauptsatz.Permutability.directedQuantifierPair_conditions {L : Language} (R₁ R₂ : AnyFOLKStep L)
    (h : directedQuantifierPair R₁ R₂) : R₁.isQuantifier ∧ R₂.isLogical := by
  cases R₁ with
  | two r => simp [directedQuantifierPair, AnyFOLKStep.quantifierKind] at h
  | one r₁ =>
    cases R₂ with
    | two r =>
      cases r₁ <;> simp [directedQuantifierPair, AnyFOLKStep.quantifierKind] at h
    | one r₂ =>
      cases r₁ <;> cases r₂ <;>
        simp_all [directedQuantifierPair, AnyFOLKStep.quantifierKind,
          quantifierPermutationDirection, AnyFOLKStep.isQuantifier, AnyFOLKStep.isLogical,
          FOLKStep1.isQuantifier, FOLKStep1.isLogical]

proof_of permutability_directed_quantifiers := open LCS.Herbrand.SharpenedHauptsatz.Permutability.Proofs.Herbrand.SharpenedHauptsatz.Permutability in
  by
    obtain ⟨hq, hlog⟩ := directedQuantifierPair_conditions R₁.rule R₂.rule hpair
    exact permutability_quantifier_with_logical hL T R₁ R₂ hpure hcf hq hlog hside


proof_of permutability_directed_quantifiers_LKe := open LCS.Herbrand.SharpenedHauptsatz.Permutability.Proofs.Herbrand.SharpenedHauptsatz.Permutability in
  by
    obtain ⟨hq, hlog⟩ := directedQuantifierPair_conditions R₁.rule R₂.rule hpair
    exact (permutability_quantifier_with_rule_LKe hL T R₁ R₂ hpure hatomic).1
      hq (Or.inl hlog) hside


end LCS.Herbrand.SharpenedHauptsatz.Permutability
