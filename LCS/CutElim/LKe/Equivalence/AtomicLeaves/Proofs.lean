import LCS.CutElim.LKe.Equivalence.AtomicLeaves

section
namespace LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality.Completeness
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.CompletenessBridge

helper theorem formulaWeight_zero_implies {L : Language} (A : FormulaN L)
    (h : formulaWeight A = 0) : isAtomicOrQuantified A := by
-- BEGIN PROOF
  cases A <;> simp [formulaWeight, isAtomicOrQuantified, FormulaN.isAtomic, isQuantified] at *

helper theorem perm_foldl_add_zero_all_zero {xs : List Nat}
    (h : xs.foldl (· + ·) 0 = 0) : ∀ x ∈ xs, x = 0 := by
-- BEGIN PROOF
  induction xs with
  | nil => simp
  | cons a as ih =>
    simp [List.foldl] at h; rw [perm_foldl_add_acc] at h
    intro x hx; cases hx with
    | head => omega
    | tail _ hx => exact ih (by omega) x hx

helper theorem perm_sequentWeight_zero {L : Language} (s : Sequent L)
    (h : sequentWeight s = 0) : seqAllAtomicOrQuantified s := by
-- BEGIN PROOF
  simp only [sequentWeight] at h
  constructor <;> intro A hA <;>
    exact formulaWeight_zero_implies A
      (perm_foldl_add_zero_all_zero (by omega)
        _ (List.mem_map.mpr ⟨A, hA, rfl⟩))

helper /-- For an axiom sequent, build a GProofTreeExt with conclusion s and
all leaf sequents atomic/quantified.
Proof by strong induction on sequentWeight s. At each step,
if the sequent already has all atomic/quantified formulas, return
the axiom leaf. Otherwise, find a formula and decompose it.

NOTE: With indexed proof trees, structural validity is guaranteed
by construction. The old WellFormed field is no longer needed. -/
theorem axiom_to_atomicLeaves {L : Language}
    (s : Sequent L) (hax : isAxiom s) :
    ∃ g : GProofTreeExt s,
      ∀ s' ∈ gProofTreeLeafSequents g, seqAllAtomicOrQuantified s' := by
-- BEGIN PROOF
  suffices h : ∀ n : Nat, ∀ s : Sequent L, sequentWeight s = n →
      isAxiom s →
      ∃ g : GProofTreeExt s,
        ∀ s' ∈ gProofTreeLeafSequents g, seqAllAtomicOrQuantified s' by
    exact h (sequentWeight s) s rfl hax
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rintro ⟨Γ, Δ⟩ hweight hax
    by_cases hn : n = 0
    · have hzero : sequentWeight (Sequent.mk Γ Δ) = 0 := by omega
      refine ⟨.axiom_ (Sequent.mk Γ Δ) hax, ?_⟩
      intro s' hs'
      simp only [gProofTreeLeafSequents, List.mem_singleton] at hs'
      subst s'
      exact perm_sequentWeight_zero (Sequent.mk Γ Δ) hzero
    · have ihS : ∀ (s' : Sequent L), sequentWeight s' < n →
          isAxiom s' →
          ∃ g : GProofTreeExt s',
            ∀ l ∈ gProofTreeLeafSequents g, seqAllAtomicOrQuantified l :=
        fun s' hlt hax' => ih (sequentWeight s') hlt s' rfl hax'
      obtain ⟨P, hPΓ, hPΔ⟩ := hax
      have leafProperty_transport :
          ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂)
            (g : GProofTreeExt s₁),
            (∀ l ∈ gProofTreeLeafSequents g,
              seqAllAtomicOrQuantified l) →
            ∀ l ∈ gProofTreeLeafSequents (heq ▸ g),
              seqAllAtomicOrQuantified l := by
        intro s₁ s₂ heq g hg
        cases heq
        exact hg
      by_cases hPzero : formulaWeight P = 0
      · have listWeight_zero :
            ∀ xs : List (FormulaN L),
              (∀ A ∈ xs, formulaWeight A = 0) →
              perm_listWeightSum xs = 0 := by
          intro xs
          induction xs with
          | nil => simp [perm_listWeightSum]
          | cons A xs ihxs =>
            intro hz
            rw [perm_listWeightSum, hz A (by simp)]
            simp only [Nat.zero_add]
            exact ihxs (fun B hB => hz B (by simp [hB]))
        have mem_insert_middle (X : FormulaN L)
            (xs mid ys : List (FormulaN L)) (hX : X ∈ xs ++ ys) :
            X ∈ xs ++ mid ++ ys := by
          rcases List.mem_append.mp hX with hxs | hys
          · exact List.mem_append.mpr
              (Or.inl (List.mem_append_left mid hxs))
          · exact List.mem_append.mpr (Or.inr hys)
        have hcomplex :
            (∃ A ∈ Γ, formulaWeight A > 0) ∨
            (∃ A ∈ Δ, formulaWeight A > 0) :=
          Classical.byContradiction fun hcontra => by
            have hnoΓ := fun h => hcontra (Or.inl h)
            have hnoΔ := fun h => hcontra (Or.inr h)
            have hzΓ : ∀ A ∈ Γ, formulaWeight A = 0 := fun A hA =>
              Classical.byContradiction fun hne =>
                hnoΓ ⟨A, hA, Nat.pos_of_ne_zero hne⟩
            have hzΔ : ∀ A ∈ Δ, formulaWeight A = 0 := fun A hA =>
              Classical.byContradiction fun hne =>
                hnoΔ ⟨A, hA, Nat.pos_of_ne_zero hne⟩
            have : sequentWeight (Sequent.mk Γ Δ) = 0 := by
              rw [perm_seqWeight_eq, listWeight_zero Γ hzΓ,
                listWeight_zero Δ hzΔ]
            omega
        rcases hcomplex with ⟨Q, hQΓ, hQpos⟩ | ⟨Q, hQΔ, hQpos⟩
        · obtain ⟨Γ₁, Γ₂, hΓ⟩ := perm_mem_split Q Γ hQΓ
          subst Γ
          have hPQ : P ≠ Q := by
            intro h
            subst Q
            omega
          have hPctx : P ∈ Γ₁ ++ Γ₂ := by
            simpa [List.mem_append, hPQ] using hPΓ
          cases Q with
          | predN _ _ => simp [formulaWeight] at hQpos
          | eq_ _ _ _ => simp [formulaWeight] at hQpos
          | all _ _ => simp [formulaWeight] at hQpos
          | ex _ _ => simp [formulaWeight] at hQpos
          | neg A =>
            exact axiom_atomic_left_neg L n ihS Δ P Γ₁ Γ₂ hPctx A hweight hPΔ
          | conj A B =>
            exact axiom_atomic_left_conj L n ihS Δ P mem_insert_middle Γ₁ Γ₂ hPctx A B hweight hPΔ
          | disj A B =>
            exact axiom_atomic_left_disj L n ihS Δ P mem_insert_middle Γ₁ Γ₂ hPctx A B hweight hPΔ
          | impl A B =>
            exact axiom_atomic_left_impl L n ihS Δ P Γ₁ Γ₂ hPctx A B hweight hPΔ
        · obtain ⟨Δ₁, Δ₂, hΔ⟩ := perm_mem_split Q Δ hQΔ
          subst Δ
          have hPQ : P ≠ Q := by
            intro h
            subst Q
            omega
          have hPctx : P ∈ Δ₁ ++ Δ₂ := by
            simpa [List.mem_append, hPQ] using hPΔ
          cases Q with
          | predN _ _ => simp [formulaWeight] at hQpos
          | eq_ _ _ _ => simp [formulaWeight] at hQpos
          | all _ _ => simp [formulaWeight] at hQpos
          | ex _ _ => simp [formulaWeight] at hQpos
          | neg A =>
            exact axiom_atomic_right_neg L n ihS Γ P Δ₁ Δ₂ hPctx A hweight hPΓ
          | conj A B =>
            exact axiom_atomic_right_conj L n ihS Γ P mem_insert_middle Δ₁ Δ₂ hPctx A B hweight hPΓ
          | disj A B =>
            exact axiom_atomic_right_disj L n ihS Γ P mem_insert_middle Δ₁ Δ₂ hPctx A B hweight hPΓ
          | impl A B =>
            exact axiom_atomic_right_impl L n ihS Γ P Δ₁ Δ₂ hPctx A B hweight hPΓ
      · obtain ⟨Γ₁, Γ₂, hΓ⟩ := perm_mem_split P Γ hPΓ
        obtain ⟨Δ₁, Δ₂, hΔ⟩ := perm_mem_split P Δ hPΔ
        subst Γ
        subst Δ
        cases P with
        | predN _ _ => simp [formulaWeight] at hPzero
        | eq_ _ _ _ => simp [formulaWeight] at hPzero
        | all _ _ => simp [formulaWeight] at hPzero
        | ex _ _ => simp [formulaWeight] at hPzero
        | conj A B =>
          exact axiom_atomic_both_conj L n ihS Γ₁ Γ₂ Δ₁ Δ₂ A B hweight
        | disj A B =>
          exact axiom_atomic_both_disj L n ihS Γ₁ Γ₂ Δ₁ Δ₂ A B hweight
        | neg A =>
          exact axiom_atomic_both_neg L n ihS leafProperty_transport Γ₁ Γ₂ Δ₁ Δ₂ A hweight
        | impl A B =>
          exact axiom_atomic_both_impl L n ihS Γ₁ Γ₂ Δ₁ Δ₂ A B hweight

helper /-- For any GProofTreeExt, there exists another with the same
conclusion and all leaf sequents atomic/quantified. -/
theorem gProofTree_atomicLeaves {L : Language} {s : Sequent L}
    (g : GProofTreeExt s) :
    ∃ g' : GProofTreeExt s,
      ∀ s' ∈ gProofTreeLeafSequents g', seqAllAtomicOrQuantified s' := by
-- BEGIN PROOF
  induction g with
  | axiom_ s hax =>
    exact axiom_to_atomicLeaves s hax
  | onePremise rule _ ih =>
    obtain ⟨g', hg'⟩ := ih
    exact ⟨.onePremise rule g', by
      simpa [gProofTreeLeafSequents] using hg'⟩
  | twoPremise rule _ _ ih₁ ih₂ =>
    obtain ⟨g₁, hg₁⟩ := ih₁
    obtain ⟨g₂, hg₂⟩ := ih₂
    refine ⟨.twoPremise rule g₁ g₂, ?_⟩
    intro s' hs'
    simp only [gProofTreeLeafSequents, List.mem_append] at hs'
    exact hs'.elim (hg₁ s') (hg₂ s')

proof_of permutation_lemma_geq := by
  -- BEGIN PROOF
    -- By induction on the indexed GEqProofTree
    induction T with
    | base g =>
      obtain ⟨g', hg'leaf⟩ := gProofTree_atomicLeaves g
      exact ⟨.base g', by simp [geqLeafSequents]; exact hg'leaf⟩
    | axiom_ s hAx =>
      obtain ⟨g', hg'leaf⟩ := axiom_to_atomicLeaves s hAx
      exact ⟨.base g', by simp [geqLeafSequents]; exact hg'leaf⟩
    | onePremise rule sub ih =>
      obtain ⟨T', hT'leaf⟩ := ih
      exact ⟨.onePremise rule T', by simp [geqLeafSequents]; exact hT'leaf⟩
    | twoPremise rule sub1 sub2 ih1 ih2 =>
      obtain ⟨T1', hT1'leaf⟩ := ih1
      obtain ⟨T2', hT2'leaf⟩ := ih2
      exact ⟨.twoPremise rule T1' T2', by
        simp [geqLeafSequents]; intro s' hs'
        rcases hs' with h1 | h2
        · exact hT1'leaf s' h1
        · exact hT2'leaf s' h2⟩
    | eqRefl t Γ Δ sub ih =>
      obtain ⟨T', hT'leaf⟩ := ih
      exact ⟨.eqRefl t Γ Δ T', by simp [geqLeafSequents]; exact hT'leaf⟩
    | eqFuncCong f ss ts Γ Δ sub ih =>
      obtain ⟨T', hT'leaf⟩ := ih
      exact ⟨.eqFuncCong f ss ts Γ Δ T', by simp [geqLeafSequents]; exact hT'leaf⟩
    | eqPredCong P ss ts Γ Δ sub ih =>
      obtain ⟨T', hT'leaf⟩ := ih
      exact ⟨.eqPredCong P ss ts Γ Δ T', by simp [geqLeafSequents]; exact hT'leaf⟩
    | eqGeneral axioms hne haxioms Γ Δ sub ih =>
      obtain ⟨T', hT'leaf⟩ := ih
      exact ⟨.eqGeneral axioms hne haxioms Γ Δ T',
        by simp [geqLeafSequents]; exact hT'leaf⟩

end LCS.CutElim.LKe.Equivalence
end
