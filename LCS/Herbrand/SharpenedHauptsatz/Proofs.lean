import LCS.Herbrand.SharpenedHauptsatz

namespace LCS.Herbrand.SharpenedHauptsatz

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Equality

open LCS.CutElim.LK

open LCS.CutElim.LKe

open LCS.CutElim.LKe.Equivalence

proof_of failedLocalExchange_7_1_1 := by
  -- BEGIN PROOF
    rintro ⟨t, x, A, Γ, Δ, hfree, hprem, hconc⟩
    have h := congrArg Sequent.antecedent hconc
    simp only [openConclusion_7_1_1] at h
    cases h


proof_of openExample_properSubformula_7_1_1 := by
  -- BEGIN PROOF
    refine ⟨.disjRight (.refl _), ?_⟩
    intro h
    cases h

proof_of eigenvariableSwapFreshnessFails := by
  -- BEGIN PROOF
    intro hfresh
    exact hfresh (.conj Q R) (by simp) (Or.inr hyR)

proof_of renamedAndPermutedPure := by
  -- BEGIN PROOF
    -- REPAIR(T7-120): proof pending
    sorry

proof_of pureVariableConversion_LK := by
  -- REPAIR(T7-36): proof pending
  sorry


proof_of pureVariableConversion_G := by
  -- REPAIR(T7-36): proof pending
  sorry


proof_of pureVariableConversion_LKe := by
  exact pureVariableConversion_LKe_helper T


proof_of pureVariableConversion_GEq := by
  exact pureVariableConversion_GEq_helper T


proof_of atomicAxiomReduction_LK := by
  -- BEGIN PROOF
  obtain ⟨T⟩ := hprov
  exact atomicAxiomReduction_LK_helper T

proof_of atomicAxiomReduction_LKe_helper := by
  -- BEGIN PROOF
  intro s T
  induction T with
  | axiom_ s hax =>
    obtain ⟨A, hAnt, hSucc⟩ := hax
    obtain ⟨tA, hA⟩ := atomicIdentity_LK A
    cases s with
    | mk Γ Δ =>
      simp only at hAnt hSucc
      subst Γ
      subst Δ
      exact ⟨LKeProofTree.lk tA, hasOnlyAtomicAxioms_lk tA hA⟩
  | eqAxiom hL ax =>
    exact ⟨.eqAxiom hL ax, trivial⟩
  | onePremise rule T ih =>
    obtain ⟨T', hT'⟩ := ih
    exact ⟨.onePremise rule T', hT'⟩
  | twoPremise rule T₁ T₂ ih₁ ih₂ =>
    obtain ⟨T₁', hT₁'⟩ := ih₁
    obtain ⟨T₂', hT₂'⟩ := ih₂
    exact ⟨.twoPremise rule T₁' T₂', ⟨hT₁', hT₂'⟩⟩

end LCS.Herbrand.SharpenedHauptsatz
