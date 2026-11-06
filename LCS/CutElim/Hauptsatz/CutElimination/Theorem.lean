import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.ProofTrees
import LCS.CutElim.Hauptsatz.CutElimination.CutRank
import Attach
import LCS.CutElim.Hauptsatz.CutElimination.Theorem.ProofsStamp

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

-- ===================================================================
-- Theorem 6.4.1 (companion): iterExp
-- ===================================================================
/-- Theorem 6.4.1 (required helper): Iterated exponentiation,
`iterExp m n p = m ^ (m ^ ... ^ p)` with `n` base-`m` exponentiations.
Used to state the depth bound of the cut-elimination procedure
`g1nnf_cut_eliminate`: `depth(T*) ≤ exp(2, c(T), depth(T))`. -/
@[blueprint "chap6__theorem_6_4_1"]
def iterExp : Nat → Nat → Nat → Nat
  | _, 0, p => p
  | m, n + 1, p => m ^ iterExp m n p

-- ===================================================================
-- Section D: Degree helpers
-- ===================================================================
-- ===================================================================
-- Section E: iterExp helpers
-- ===================================================================
theorem iterExp_mono_last (m : Nat) (hm : 1 ≤ m) :
    ∀ (n : Nat), ∀ {p q : Nat}, p ≤ q → iterExp m n p ≤ iterExp m n q := by
-- BEGIN PROOF
  intro n
  induction n with
  | zero => intro p q hpq; simp [iterExp]; exact hpq
  | succ n ih =>
    intro p q hpq
    simp only [iterExp]
    exact Nat.pow_le_pow_right (by omega) (ih hpq) /- retained: used by LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression.Proofs -/

theorem nat_le_pow_of_two_le (b n : Nat) (hb : 2 ≤ b) : n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hPow : 1 ≤ b ^ n := Nat.one_le_pow n b (by omega)
    calc
      n + 1 ≤ b ^ n + 1 := by omega
      _ ≤ b ^ n + b ^ n := by omega
      _ = 2 * b ^ n := by omega
      _ ≤ b * b ^ n := Nat.mul_le_mul_right (b ^ n) hb
      _ = b ^ (n + 1) := by simp [Nat.pow_succ, Nat.mul_comm] /- retained: used by LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression.Proofs -/

theorem iterExp_mono_count_of_two_le (b : Nat) (hb : 2 ≤ b) :
    ∀ (n₁ n₂ p : Nat), n₁ ≤ n₂ → iterExp b n₁ p ≤ iterExp b n₂ p := by
-- BEGIN PROOF
  intro n₁ n₂ p hn
  induction n₂ with
  | zero =>
    have : n₁ = 0 := by omega
    subst this; exact Nat.le_refl _
  | succ n₂ ih =>
    by_cases h : n₁ ≤ n₂
    · calc iterExp b n₁ p ≤ iterExp b n₂ p := ih h
      _ ≤ b ^ iterExp b n₂ p :=
        nat_le_pow_of_two_le b (iterExp b n₂ p) hb
      _ = iterExp b (n₂ + 1) p := by simp [iterExp]
    · have : n₁ = n₂ + 1 := by omega
      subst this; exact Nat.le_refl _ /- retained: used by LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression.Proofs -/

theorem iterExp_mono_count :
    ∀ (n₁ n₂ p : Nat), n₁ ≤ n₂ → iterExp 2 n₁ p ≤ iterExp 2 n₂ p := by
-- BEGIN PROOF
  intro n₁ n₂ p hn
  exact iterExp_mono_count_of_two_le 2 (by omega) n₁ n₂ p hn /- retained: used by LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression.Proofs -/

theorem iterExp_succ_shift_base :
    ∀ (b n p : Nat), iterExp b (n + 1) p = iterExp b n (b ^ p) := by
-- BEGIN PROOF
  intro b n
  induction n with
  | zero => intro p; simp [iterExp]
  | succ n ih =>
    intro p
    show b ^ iterExp b (n + 1) p = b ^ iterExp b n (b ^ p)
    congr 1
    exact ih p /- retained: used by LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression.Proofs -/

theorem iterExp_succ_shift :
    ∀ (n p : Nat), iterExp 2 (n + 1) p = iterExp 2 n (2 ^ p) := by
-- BEGIN PROOF
  intro n p
  exact iterExp_succ_shift_base 2 n p /- retained: used by LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression.Proofs -/

-- ===================================================================
-- Theorem 6.4.1: Cut elimination
-- ===================================================================

/-- Rank threshold under the adopted end-sequent convention of E-CUTFB:
no variable occurs both free and bound anywhere in the end sequent. -/
theorem g1nnf_cut_rank_threshold {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hL Γ Δ)
    (hEnd : finsetCrossNoFreeBound Γ Δ) (k : Nat) (hRank : T.cutRank ≤ k + 1) :
    ∃ T' : G1nnfProofTree hL Γ Δ,
      T'.cutRank ≤ k ∧ T'.depth ≤ 2 ^ T.depth := by
  -- REPAIR(T6-32): proof pending (hand proof: feasibility-T6-78 §A)
  sorry

/-- Theorem 6.4.1 (required helper): Single-step cut-rank reduction
procedure under the adopted end-sequent convention of E-CUTFB.
Given a G1nnf proof T, constructs
a proof T' of the same sequent with cut-rank at most c(T) − 1 and
depth bounded by `2 ^ depth(T)`. Textbook Claim inside the proof of
Theorem 6.4.1: "If c(T) > 0 then we can construct a proof T' for
Γ → Δ such that c(T') < c(T) and depth(T') ≤ 2^depth(T)". -/
noncomputable def g1nnf_cut_rank_reduce {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hL Γ Δ)
    (hEnd : finsetCrossNoFreeBound Γ Δ) : G1nnfProofTree hL Γ Δ :=
  Classical.choose
    (g1nnf_cut_rank_threshold T hEnd (T.cutRank - 1) (by omega))

/-- Bounds for the single-step cut-rank reduction
`g1nnf_cut_rank_reduce`. The constructed proof has strictly smaller
cut-rank than the input, and its depth is bounded by `2 ^ depth(T)`. -/
theorem g1nnf_cut_rank_reduce_spec {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hL Γ Δ)
    (hEnd : finsetCrossNoFreeBound Γ Δ) (hPos : T.cutRank > 0) :
    (g1nnf_cut_rank_reduce T hEnd).cutRank < T.cutRank ∧
    (g1nnf_cut_rank_reduce T hEnd).depth ≤ 2 ^ T.depth := by
  have h := Classical.choose_spec
    (g1nnf_cut_rank_threshold T hEnd (T.cutRank - 1) (by omega))
  exact ⟨Nat.lt_of_le_of_lt h.1 (by omega), h.2⟩

/-- Theorem 6.4.1: (Cut elimination theorem for G1nnf) Every G1nnf
proof T whose end sequent satisfies the §6.1 convention (the adopted
reading of E-CUTFB) can be converted to a cut-free proof T* of the same sequent
with `depth(T*) ≤ exp(2, c(T), depth(T))`. The procedure iterates the
single-step cut-rank reduction `g1nnf_cut_rank_reduce`. -/
@[blueprint "chap6__theorem_6_4_1"]
noncomputable def g1nnf_cut_eliminate {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hL Γ Δ)
    (hEnd : finsetCrossNoFreeBound Γ Δ) :
    G1nnfProofTree hL Γ Δ :=
  if hPos : T.cutRank > 0 then
    g1nnf_cut_eliminate (g1nnf_cut_rank_reduce T hEnd) hEnd
  else
    T
termination_by T.cutRank
decreasing_by
  exact (g1nnf_cut_rank_reduce_spec T hEnd hPos).1

/-- Bounds for the cut-elimination procedure `g1nnf_cut_eliminate`.
The produced proof is cut-free and its depth is bounded by
`exp(2, c(T), depth(T)) = iterExp 2 (cutRank T) (depth T)`. -/
@[blueprint "chap6__theorem_6_4_1" (main := true)]
theorem g1nnf_cut_eliminate_spec {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hL Γ Δ)
    (hEnd : finsetCrossNoFreeBound Γ Δ) :
    (g1nnf_cut_eliminate T hEnd).isCutFree ∧
    (g1nnf_cut_eliminate T hEnd).depth ≤ iterExp 2 T.cutRank T.depth 

end LCS.CutElim.Hauptsatz
end
