import LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

namespace LCS.CutElim.Hauptsatz

helper /-- Lemma 6.4.5 (left weakening): every NNF formula may be added
with unchanged depth and cut rank, and its free variables are disjoint from
the eigenvariables of the resulting proof. -/
theorem g1nnf_weakening_left {L : Language}
    (hNoEq : L.withoutEquality)
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hNoEq Γ Δ)
    (A : FormulaN L) (hNNF : A.isNNF) :
    ∃ T' : G1nnfProofTree hNoEq (LCS.Finset.insert A Γ) Δ,
      T'.depth = T.depth ∧ T'.cutRank = T.cutRank ∧
      ∀ v, formulaFVN A v → ¬ T'.eigenvariables v := by
  obtain ⟨S, hd, hc, he⟩ := T.freshenForWeakening_exists A
  refine ⟨S.weakenTreeLeft A hNNF he,
    (S.weakenTreeLeft_depth A hNNF he).trans hd,
    (S.weakenTreeLeft_cutRank A hNNF he).trans hc, ?_⟩
  intro v hv
  rw [S.weakenTreeLeft_eigenvariables_eq A hNNF he v]
  exact he v hv

helper /-- Lemma 6.4.5 (right weakening): every NNF formula may be added
with unchanged depth and cut rank, and its free variables are disjoint from
the eigenvariables of the resulting proof. -/
theorem g1nnf_weakening_right {L : Language}
    (hNoEq : L.withoutEquality)
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hNoEq Γ Δ)
    (A : FormulaN L) (hNNF : A.isNNF) :
    ∃ T' : G1nnfProofTree hNoEq Γ (LCS.Finset.insert A Δ),
      T'.depth = T.depth ∧ T'.cutRank = T.cutRank ∧
      ∀ v, formulaFVN A v → ¬ T'.eigenvariables v := by
  obtain ⟨S, hd, hc, he⟩ := T.freshenForWeakening_exists A
  refine ⟨S.weakenTreeRight A hNNF he,
    (S.weakenTreeRight_depth A hNNF he).trans hd,
    (S.weakenTreeRight_cutRank A hNNF he).trans hc, ?_⟩
  intro v hv
  rw [S.weakenTreeRight_eigenvariables_eq A hNNF he v]
  exact he v hv

proof_of g1nnf_weakening_lemma := by
  exact ⟨g1nnf_weakening_left hNoEq T A hNNF,
    g1nnf_weakening_right hNoEq T A hNNF⟩


proof_of g1nnf_inversion_conj_right := by
  -- BEGIN PROOF
    -- DEBT(Lemma 6.4.6 inversion lemma, ∧:right case: proof pending; pre-existing placeholder)
    sorry


proof_of g1nnf_inversion_disj_left := by
  -- BEGIN PROOF
    -- DEBT(Lemma 6.4.6 inversion lemma, ∨:left case: proof pending; pre-existing placeholder)
    sorry


proof_of g1nnf_inversion_all_right := by
  -- BEGIN PROOF
    -- DEBT(Lemma 6.4.6 inversion lemma, ∀:right case: proof pending; pre-existing placeholder)
    sorry


proof_of g1nnf_inversion_ex_left := by
  -- BEGIN PROOF
    -- DEBT(Lemma 6.4.6 inversion lemma, ∃:left case: proof pending; pre-existing placeholder)
    sorry


proof_of g1nnf_reduction_lemma := by
  -- REPAIR(T6-31): proof pending (hand proof: feasibility-T6-78 §A)
  sorry


helper /-- Adding one inference level preserves the unary exponential depth bound. -/
theorem nat_succ_le_two_pow_succ {a b : Nat} (h : a ≤ 2 ^ b) :
    a + 1 ≤ 2 ^ (b + 1) := by
  have hOne : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  calc
    a + 1 ≤ 2 ^ b + 1 := Nat.add_le_add_right h 1
    _ ≤ 2 ^ b + 2 ^ b := by omega
    _ = 2 ^ (b + 1) := by omega

helper /-- Rebuilding a binary inference preserves the exponential depth bound. -/
theorem nat_max_succ_le_two_pow_max_succ
    {a₁ a₂ b₁ b₂ : Nat}
    (h₁ : a₁ ≤ 2 ^ b₁) (h₂ : a₂ ≤ 2 ^ b₂) :
    max a₁ a₂ + 1 ≤ 2 ^ (max b₁ b₂ + 1) := by
  have hPow₁ : 2 ^ b₁ ≤ 2 ^ max b₁ b₂ :=
    Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
  have hPow₂ : 2 ^ b₂ ≤ 2 ^ max b₁ b₂ :=
    Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)
  apply nat_succ_le_two_pow_succ
  exact Nat.max_le.mpr
    ⟨Nat.le_trans h₁ hPow₁, Nat.le_trans h₂ hPow₂⟩

helper /-- The sum bound from the reduction lemma fits one exponential level. -/
theorem nat_add_le_two_pow_max_succ
    {a₁ a₂ b₁ b₂ : Nat}
    (h₁ : a₁ ≤ 2 ^ b₁) (h₂ : a₂ ≤ 2 ^ b₂) :
    a₁ + a₂ ≤ 2 ^ (max b₁ b₂ + 1) := by
  have hPow₁ : 2 ^ b₁ ≤ 2 ^ max b₁ b₂ :=
    Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
  have hPow₂ : 2 ^ b₂ ≤ 2 ^ max b₁ b₂ :=
    Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)
  calc
    a₁ + a₂ ≤ 2 ^ max b₁ b₂ + 2 ^ max b₁ b₂ :=
      Nat.add_le_add (Nat.le_trans h₁ hPow₁) (Nat.le_trans h₂ hPow₂)
    _ = 2 ^ (max b₁ b₂ + 1) := by omega

helper /-- The cut-elimination recursion stops immediately at rank zero. -/
theorem g1nnf_cut_eliminate_of_rank_zero {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hL Γ Δ)
    (hEnd : finsetCrossNoFreeBound Γ Δ) (hZero : T.cutRank = 0) :
    g1nnf_cut_eliminate T hEnd = T := by
  rw [g1nnf_cut_eliminate.eq_def]
  split
  · omega
  · rfl

helper /-- At positive rank, cut elimination starts with one rank-reduction step. -/
theorem g1nnf_cut_eliminate_of_rank_pos {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hL Γ Δ)
    (hEnd : finsetCrossNoFreeBound Γ Δ) (hPos : T.cutRank > 0) :
    g1nnf_cut_eliminate T hEnd =
      g1nnf_cut_eliminate (g1nnf_cut_rank_reduce T hEnd) hEnd := by
  rw [g1nnf_cut_eliminate.eq_def]
  split
  · rfl
  · omega

proof_of g1nnf_cut_eliminate_spec := by
  induction hRank : T.cutRank using Nat.strongRecOn generalizing Γ Δ T with
  | ind n ih =>
      cases n with
      | zero =>
          rw [g1nnf_cut_eliminate_of_rank_zero T hEnd hRank]
          constructor
          · simpa only [G1nnfProofTree.isCutFree] using hRank
          · exact Nat.le_refl _
      | succ n =>
          have hPos : T.cutRank > 0 := by omega
          let T' := g1nnf_cut_rank_reduce T hEnd
          have hReduce := g1nnf_cut_rank_reduce_spec T hEnd hPos
          have hReduce' :
              T'.cutRank < T.cutRank ∧
                T'.depth ≤ 2 ^ T.depth := by
            simpa only [T'] using hReduce
          have hIH :=
            ih T'.cutRank (by omega) T' hEnd rfl
          have hEliminate :
              g1nnf_cut_eliminate T hEnd = g1nnf_cut_eliminate T' hEnd := by
            simpa only [T'] using
              g1nnf_cut_eliminate_of_rank_pos T hEnd hPos
          rw [hEliminate]
          refine ⟨hIH.1, ?_⟩
          calc
            (g1nnf_cut_eliminate T' hEnd).depth
                ≤ iterExp 2 T'.cutRank T'.depth := hIH.2
            _ ≤ iterExp 2 T'.cutRank (2 ^ T.depth) :=
              iterExp_mono_last 2 (by omega) T'.cutRank hReduce'.2
            _ = iterExp 2 (T'.cutRank + 1) T.depth :=
              (iterExp_succ_shift T'.cutRank T.depth).symm
            _ ≤ iterExp 2 (n + 1) T.depth :=
              iterExp_mono_count
                (T'.cutRank + 1) (n + 1) T.depth (by omega)


end LCS.CutElim.Hauptsatz

end

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

namespace LCS.CutElim.Hauptsatz

proof_of g1nnf_term_subst_preservation := by
  constructor
  · intro z hz
    refine ⟨T.forgetProofTree.substituteVar_isProof z y hNotBound hz
      T.forgetProofTree_isProof, ?_⟩
    -- REPAIR(T6-28): proof pending
    sorry
  · intro t hf he ht
    refine ⟨T.forgetProofTree.substTerm_isProof t y hNotBound hf he ht
      T.forgetProofTree_isProof, ?_⟩
    -- REPAIR(T6-28): proof pending
    sorry


end LCS.CutElim.Hauptsatz

end
