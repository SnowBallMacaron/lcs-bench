import LCS.SLD.SLDForm.Completeness.PermutationLemma

section
namespace LCS.SLD.SLDForm.Completeness
open LCS.Resolution.GCNF
open LCS.SLD.SLDForm
open LCS.SLD.SLDForm.Occurrence

proof_of gcnf_permutation_at_root := by
  -- DEBT(OD-9-2: root/partition contribution of Lemma 9.2.2 kept open; not emended)
  sorry

helper /-- Lemma 9.2.2 (companion): Semantic validity of the left premise of ∨:left.
    If `S` is valid, then `(S.erase (clauseWithLiteral B'' Q)) ∪ {B''}` is
    valid. Membership of `clauseWithLiteral B'' Q` in `S` is not required for
    this semantic step (the conclusion follows from validity of `S` and the
    fact that any valuation satisfying the left premise also satisfies `S`). -/
theorem gcnf_valid_split_left (S : ClauseSequent) (B'' : Clause) (Q : Literal)
    (hValid : ClauseSequent.isValid S) :
    ClauseSequent.isValid
      (Finset.union (Finset.erase S (clauseWithLiteral B'' Q))
        (ClauseSequent.single B'')) := by
-- BEGIN PROOF
  intro ⟨v, hSat⟩
  apply hValid
  refine ⟨v, fun C hC => ?_⟩
  by_cases hCeq : C = clauseWithLiteral B'' Q
  · -- C is the split clause; use satisfaction of B'' to witness neg Q ∉ or insertion.
    subst hCeq
    have hB''sat : Clause.satisfiedBy B'' v :=
      hSat B'' ((Finset.mem_union_exp _ _ _).mpr
        (Or.inr ((mem_csingle B'' B'').mpr rfl)))
    obtain ⟨L, hLmem, hLsat⟩ := hB''sat
    -- L ∈ B'' ⊆ insert Q B'' = clauseWithLiteral B'' Q
    refine ⟨L, ?_, hLsat⟩
    show L ∈ Finset.insert Q B''
    exact (Finset.mem_insert_exp Q L B'').mpr (Or.inr hLmem)
  · -- C is in the erase, i.e., C ∈ S with C ≠ clauseWithLiteral B'' Q.
    have hCerase : C ∈ Finset.erase S (clauseWithLiteral B'' Q) :=
      (Finset.mem_erase _ _ _).mpr ⟨hC, hCeq⟩
    exact hSat C ((Finset.mem_union_exp _ _ _).mpr (Or.inl hCerase))

helper /-- Lemma 9.2.2 (companion): Semantic validity of the right premise of ∨:left.
    If `S` is valid, then `(S.erase (clauseWithLiteral B'' Q)) ∪ {{Q}}` is
    valid. Membership of `clauseWithLiteral B'' Q` in `S` is not required for
    this semantic step (the conclusion follows from validity of `S` and the
    fact that any valuation satisfying the right premise also satisfies `S`). -/
theorem gcnf_valid_split_right (S : ClauseSequent) (B'' : Clause) (Q : Literal)
    (hValid : ClauseSequent.isValid S) :
    ClauseSequent.isValid
      (Finset.union (Finset.erase S (clauseWithLiteral B'' Q))
        (ClauseSequent.single (Clause.single Q))) := by
-- BEGIN PROOF
  intro ⟨v, hSat⟩
  apply hValid
  refine ⟨v, fun C hC => ?_⟩
  by_cases hCeq : C = clauseWithLiteral B'' Q
  · -- C is the split clause; use satisfaction of {Q} to witness Q ∈ insert Q B''.
    subst hCeq
    have hQClause : Clause.single Q ∈
        Finset.union (Finset.erase S (clauseWithLiteral B'' Q))
          (ClauseSequent.single (Clause.single Q)) :=
      (Finset.mem_union_exp _ _ _).mpr
        (Or.inr ((mem_csingle (Clause.single Q) (Clause.single Q)).mpr rfl))
    have hQsat : Clause.satisfiedBy (Clause.single Q) v := hSat _ hQClause
    obtain ⟨L, hLmem, hLsat⟩ := hQsat
    have hLeqQ : L = Q := (Finset.mem_singleton L Q).mp hLmem
    -- L ∈ insert Q B'' = clauseWithLiteral B'' Q (via L = Q)
    refine ⟨L, ?_, hLsat⟩
    show L ∈ Finset.insert Q B''
    exact (Finset.mem_insert_exp Q L B'').mpr (Or.inl hLeqQ)
  · -- C is in the erase, i.e., C ∈ S with C ≠ clauseWithLiteral B'' Q.
    have hCerase : C ∈ Finset.erase S (clauseWithLiteral B'' Q) :=
      (Finset.mem_erase _ _ _).mpr ⟨hC, hCeq⟩
    exact hSat C ((Finset.mem_union_exp _ _ _).mpr (Or.inl hCerase))

proof_of gcnf_provable_clause_split := by
  -- BEGIN PROOF
    have hValid : ClauseSequent.isValid S := gcnf_soundness S hProv
    -- Left sub-sequent: validity + non-emptiness → provability
    have hValidL := gcnf_valid_split_left S B'' Q hValid
    have hValidR := gcnf_valid_split_right S B'' Q hValid
    -- Non-emptiness of clauses in left sub-sequent
    have hNeL : ∀ C ∈ Finset.union (Finset.erase S (clauseWithLiteral B'' Q))
        (ClauseSequent.single B''), C ≠ Clause.empty := by
      intro C hC
      rw [Finset.mem_union] at hC
      rcases hC with hGamma | hSing
      · exact hGammaNe C hGamma
      · rw [(mem_csingle C B'').mp hSing]; exact hB''ne
    -- Non-emptiness of clauses in right sub-sequent
    have hNeR : ∀ C ∈ Finset.union (Finset.erase S (clauseWithLiteral B'' Q))
        (ClauseSequent.single (Clause.single Q)), C ≠ Clause.empty := by
      intro C hC
      rw [Finset.mem_union] at hC
      rcases hC with hGamma | hSing
      · exact hGammaNe C hGamma
      · rw [(mem_csingle C (Clause.single Q)).mp hSing]; exact single_ne_empty Q
    refine ⟨?_, ?_⟩
    · exact (gcnf_completeness _ hValidL hNeL).1
    · exact (gcnf_completeness _ hValidR hNeR).1

end LCS.SLD.SLDForm.Completeness
end
