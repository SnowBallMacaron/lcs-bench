import LCS.SLD.SLDForm

namespace LCS.SLD.SLDForm

open LCS.Resolution.GCNF

proof_of definiteClause_iff_unit_or_nonunit := by
  constructor
  · intro hDef
    obtain ⟨Q, hQ⟩ := hDef.2
    let N : Clause := LCS.Finset.filter (fun l => match l with
      | Literal.neg _ => true | Literal.pos _ => false) C
    have hNeg : allNegative N := by
      intro l hl
      have hn := (LCS.Finset.mem_filter.mp hl).2
      cases l <;> simp_all
    have hEq : C = LCS.Finset.insert (Literal.pos Q) N := by
      apply LCS.Finset.ext
      intro l
      constructor
      · intro hl
        cases l with
        | pos P =>
          have hp := hDef.1.2 P Q hl hQ
          subst P
          exact LCS.Finset.mem_insert.mpr (Or.inl rfl)
        | neg P =>
          exact LCS.Finset.mem_insert.mpr
            (Or.inr (LCS.Finset.mem_filter.mpr ⟨hl, rfl⟩))
      · intro hl
        rcases LCS.Finset.mem_insert.mp hl with rfl | hn
        · exact hQ
        · exact (LCS.Finset.mem_filter.mp hn).1
    refine ⟨Q, N, hNeg, hEq, fun P hP => hDef.1.2 P Q hP hQ, ?_⟩
    by_cases hN : N = Clause.empty
    · left
      refine ⟨hN, hDef, Literal.pos Q, ?_⟩
      rw [hEq, hN]
      apply LCS.Finset.ext
      intro l
      simp [Clause.empty, Clause.single]
      intro hl
      exact (LCS.Finset.not_mem_empty hl).elim
    · right
      obtain ⟨l, hl⟩ := LCS.Finset.nonempty_of_ne_empty N hN
      refine ⟨hN, hDef, Literal.pos Q, l, hQ,
        (LCS.Finset.mem_filter.mp hl).1, ?_⟩
      intro he
      subst l
      exact hNeg (Literal.pos Q) hl
  · rintro ⟨Q, N, _, _, _, hCases⟩
    exact hCases.elim (fun h => h.2.1) (fun h => h.2.1)


proof_of exFirstGCNFProof_labels := by
  exact of_decide_eq_true exFirstGCNFProof_labels_check

proof_of exSLDFormProof_labels := by
  exact of_decide_eq_true exSLDFormProof_labels_check

helper theorem clause_ofList_cons_ordinary (l : Literal) (ls : List Literal) :
    Clause.isOrdinary (Clause.ofList (l :: ls)) := by
  intro h
  have hm : l ∈ Clause.ofList (l :: ls) := Finset.mem_ofList.mpr (by simp)
  rw [h] at hm
  exact Finset.not_mem_empty hm

proof_of exHornClauseSet_isDefiniteGoalSet := by
  unfold isDefiniteGoalSet exHornClauseSet
  constructor
  · -- Every clause is either definite or a goal clause
    intro C hC
    simp [List.mem_cons] at hC
    rcases hC with rfl | rfl | rfl | rfl | rfl
    · -- {pos 3}: definite (has positive literal, Horn)
      left; refine ⟨⟨by exact clause_ofList_cons_ordinary _ _, ?_⟩, ?_⟩
      · exact fun P Q hP hQ => by
          simp [Clause.ofList, Finset.mem_ofList] at hP hQ; rw [hP, hQ]
      · exact ⟨3, by simp [Clause.ofList, Finset.mem_ofList]⟩
    · -- {pos 4}: definite
      left; refine ⟨⟨by exact clause_ofList_cons_ordinary _ _, ?_⟩, ?_⟩
      · exact fun P Q hP hQ => by
          simp [Clause.ofList, Finset.mem_ofList] at hP hQ; rw [hP, hQ]
      · exact ⟨4, by simp [Clause.ofList, Finset.mem_ofList]⟩
    · -- {neg 1, neg 2}: goal clause (all negative)
      right; refine ⟨⟨by exact clause_ofList_cons_ordinary _ _, ?_⟩, ?_⟩
      · exact fun P Q hP _ => by
          simp [Clause.ofList, Finset.mem_ofList] at hP
      · exact fun l hl => by simp [Clause.ofList, Finset.mem_ofList] at hl; rcases hl with rfl | rfl <;> trivial
    · -- {neg 3, neg 4, pos 1}: definite
      left; refine ⟨⟨by exact clause_ofList_cons_ordinary _ _, ?_⟩, ?_⟩
      · exact fun P Q hP hQ => by
          simp [Clause.ofList, Finset.mem_ofList] at hP hQ; rw [hP, hQ]
      · exact ⟨1, by simp [Clause.ofList, Finset.mem_ofList]⟩
    · -- {neg 3, pos 2}: definite
      left; refine ⟨⟨by exact clause_ofList_cons_ordinary _ _, ?_⟩, ?_⟩
      · exact fun P Q hP hQ => by
          simp [Clause.ofList, Finset.mem_ofList] at hP hQ; rw [hP, hQ]
      · exact ⟨2, by simp [Clause.ofList, Finset.mem_ofList]⟩
  · -- The goal clause is unique by clause equality.
    refine ⟨Clause.ofList [Literal.neg 1, Literal.neg 2], by simp, ?_, ?_⟩
    · constructor
      · refine ⟨by exact clause_ofList_cons_ordinary _ _, ?_⟩
        intro P Q hP _
        simp [Clause.ofList, Finset.mem_ofList] at hP
      · intro l hl
        simp [Clause.ofList, Finset.mem_ofList] at hl
        rcases hl with rfl | rfl <;> trivial
    · intro C hC hGoal
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl | rfl | rfl | rfl | rfl
      · have := hGoal.2 (Literal.pos 3) (by simp [Clause.ofList])
        simp at this
      · have := hGoal.2 (Literal.pos 4) (by simp [Clause.ofList])
        simp at this
      · rfl
      · have := hGoal.2 (Literal.pos 1) (by simp [Clause.ofList])
        simp at this
      · have := hGoal.2 (Literal.pos 2) (by simp [Clause.ofList])
        simp at this

proof_of exSLDFormProof_isSLDForm := by
  exact isSLDFormB_sound exSLDFormProof.kernel exSLDFormProof_check

end LCS.SLD.SLDForm
