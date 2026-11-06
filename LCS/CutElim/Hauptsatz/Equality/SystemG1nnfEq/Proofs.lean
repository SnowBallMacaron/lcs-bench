import LCS.CutElim.Hauptsatz.Equality.SystemG1nnfEq

section
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SyntaxN.Substitution LCS.FirstOrder.SyntaxN.Variables
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS
namespace LCS.CutElim.Hauptsatz.Equality

proof_of g1nnfEqAxiom_valid := by
  classical
  induction ax with
  | refl t Γ Δ =>
    intro M val _
    exact ⟨.eq_ hL t t, Finset.mem_insert.mpr (Or.inl rfl), rfl⟩
  | funCong f ss ts Γ Δ =>
    intro M val hΓ
    refine ⟨.eq_ hL (.func f ss) (.func f ts),
      Finset.mem_insert.mpr (Or.inl rfl), ?_⟩
    change M.interpFunc f (fun i => termEval M val (ss i)) =
      M.interpFunc f (fun i => termEval M val (ts i))
    congr 1
    funext i
    apply hΓ (.eq_ hL (ss i) (ts i))
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_ofList.mpr
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  | predCong P ss ts Γ Δ =>
    intro M val hΓ
    refine ⟨.predN P ts, Finset.mem_insert.mpr (Or.inl rfl), ?_⟩
    have hP := hΓ (.predN P ss) (Finset.mem_insert.mpr (Or.inl rfl))
    have heq : (fun i => termEval M val (ss i)) =
        (fun i => termEval M val (ts i)) := by
      funext i
      apply hΓ (.eq_ hL (ss i) (ts i))
      apply Finset.mem_insert.mpr
      right
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_ofList.mpr
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    change M.interpPred P (fun i => termEval M val (ts i))
    change M.interpPred P (fun i => termEval M val (ss i)) at hP
    rw [← heq]
    exact hP
  | eqCong s1 s2 t1 t2 Γ Δ =>
    intro M val hΓ
    refine ⟨.eq_ hL t1 t2, Finset.mem_insert.mpr (Or.inl rfl), ?_⟩
    have h1 := hΓ (.eq_ hL s1 t1) (by
      simp [G1nnfEqAxiom.toSequent])
    have h2 := hΓ (.eq_ hL s2 t2) (by
      simp [G1nnfEqAxiom.toSequent])
    have h3 := hΓ (.eq_ hL s1 s2) (Finset.mem_insert.mpr (Or.inl rfl))
    exact h1.symm.trans (h3.trans h2)
  | negLeft base A ih =>
    intro M val hΓ
    simp only [G1nnfEqAxiom.toSequent_negLeft] at hΓ ⊢
    have hnA := hΓ (.neg A) (Finset.mem_insert.mpr (Or.inl rfl))
    obtain ⟨B, hB, hEval⟩ := ih hW.1 M val
      (fun F hF => hΓ F (Finset.mem_insert.mpr (Or.inr hF)))
    refine ⟨B, (Finset.mem_erase A B base.toSequent.2).mpr ⟨hB, ?_⟩, hEval⟩
    intro hBA
    subst B
    exact hnA hEval
  | negRight base A ih =>
    intro M val hΓ
    simp only [G1nnfEqAxiom.toSequent_negRight] at hΓ ⊢
    by_cases hA : formulaEvalN M A val
    · obtain ⟨B, hB, hEval⟩ := ih hW.1 M val (by
        intro F hF
        by_cases hFA : F = A
        · subst F
          exact hA
        · exact hΓ F ((Finset.mem_erase A F base.toSequent.1).mpr ⟨hF, hFA⟩))
      exact ⟨B, Finset.mem_insert.mpr (Or.inr hB), hEval⟩
    · exact ⟨.neg A, Finset.mem_insert.mpr (Or.inl rfl), hA⟩

proof_of g1nnfEq_completeness := by
  -- BEGIN PROOF
    -- This requires completeness of LKe (Thm 6.3.1) plus G1nnfEq simulation.
    -- Sorry'd as it depends on sorry'd Thm 6.3.1 chain.
    -- DEBT(Lemma 6.4.8: completeness of G1nnf= through Theorem 6.3.1 and the LKe simulation; proof pending)
    sorry

end LCS.CutElim.Hauptsatz.Equality
end
