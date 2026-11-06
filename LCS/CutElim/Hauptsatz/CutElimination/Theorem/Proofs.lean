import LCS.CutElim.Hauptsatz.CutElimination.Theorem

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

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
