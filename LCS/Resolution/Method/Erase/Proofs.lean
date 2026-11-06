import LCS.Resolution.Method.Erase

namespace LCS.Resolution.Method.ResolutionTree

open LCS.Resolution.GCNF

helper theorem leavesFrom_iff_inputs_subset (T : ResolutionTree) (S : ClauseSequent) :
    T.leavesFrom S ↔ LCS.Finset.Subset T.inputs S := by
  induction T with
  | axiom_ C =>
    simp only [leavesFrom, inputs, ClauseSequent.single, LCS.Finset.Subset,
      LCS.Finset.mem_singleton]
    exact ⟨fun h _ he => he ▸ h, fun h => h C rfl⟩
  | resolve A B P ihA ihB =>
    simp only [leavesFrom, inputs, ihA, ihB,
      LCS.Finset.Subset, LCS.Finset.mem_union]
    exact ⟨fun ⟨hA, hB⟩ C h => h.elim (hA C) (hB C),
      fun h => ⟨fun C hc => h C (Or.inl hc), fun C hc => h C (Or.inr hc)⟩⟩

helper theorem replayResolve_isWellFormed (A B : ResolutionTree) (P : Literal)
    (hA : A.IsWellFormed) (hB : B.IsWellFormed) :
    (replayResolve A B P).IsWellFormed := by
  unfold replayResolve
  split
  · split
    · exact ⟨hA, hB, ‹P ∈ A.label›, ‹P.conjugate ∈ B.label›⟩
    · exact hB
  · exact hA

proof_of eraseLiteral_isWellFormed := by
  induction T with
  | axiom_ C =>
    rw [eraseLiteral]
    split <;> trivial
  | resolve A B P ihA ihB =>
    rw [eraseLiteral]
    split
    · exact replayResolve_isWellFormed _ _ P (ihA h.1) (ihB h.2.1)
    · exact h


helper theorem replayResolve_label_subset (A B A₀ B₀ : ResolutionTree)
    (P L : Literal)
    (hA : LCS.Finset.Subset A.label (GCNF.Clause.remove A₀.label L))
    (hB : LCS.Finset.Subset B.label (GCNF.Clause.remove B₀.label L)) :
    LCS.Finset.Subset (replayResolve A B P).label
      (GCNF.Clause.remove (resolve A₀ B₀ P).label L) := by
  simp only [LCS.Finset.Subset, GCNF.Clause.remove, LCS.Finset.mem_erase] at hA hB
  unfold replayResolve
  split
  · split
    · intro x hx
      simp only [label, GCNF.Clause.union, GCNF.Clause.remove,
        LCS.Finset.mem_union, LCS.Finset.mem_erase] at hx ⊢
      rcases hx with ⟨hx, hp⟩ | ⟨hx, hp⟩
      · exact ⟨Or.inl ⟨(hA x hx).1, hp⟩, (hA x hx).2⟩
      · exact ⟨Or.inr ⟨(hB x hx).1, hp⟩, (hB x hx).2⟩
    · intro x hx
      simp only [label, GCNF.Clause.union, GCNF.Clause.remove,
        LCS.Finset.mem_union, LCS.Finset.mem_erase]
      exact ⟨Or.inr ⟨(hB x hx).1, fun he => ‹P.conjugate ∉ B.label› (he ▸ hx)⟩,
        (hB x hx).2⟩
  · intro x hx
    simp only [label, GCNF.Clause.union, GCNF.Clause.remove,
      LCS.Finset.mem_union, LCS.Finset.mem_erase]
    exact ⟨Or.inl ⟨(hA x hx).1, fun he => ‹P ∉ A.label› (he ▸ hx)⟩,
      (hA x hx).2⟩

helper /-- Every surviving root literal belonged to the old root and differs from L.
Contraction can delete further literals, so the relation is inclusion. -/
theorem eraseLiteral_label_subset (T : ResolutionTree) (L : Literal) :
    LCS.Finset.Subset (T.eraseLiteral L).label (GCNF.Clause.remove T.label L) := by
  induction T with
  | axiom_ C =>
    rw [eraseLiteral]
    split
    · exact fun _ hx => hx
    · intro x hx
      exact (LCS.Finset.mem_erase _ _ _).mpr
        ⟨hx, fun he => ‹L ∉ (axiom_ C).label› (he ▸ hx)⟩
  | resolve A B P ihA ihB =>
    rw [eraseLiteral]
    split
    · exact replayResolve_label_subset _ _ A B P L ihA ihB
    · intro x hx
      exact (LCS.Finset.mem_erase _ _ _).mpr
        ⟨hx, fun he => ‹L ∉ (resolve A B P).label› (he ▸ hx)⟩

proof_of eraseLiteral_unit_label := by
  apply LCS.Finset.ext
  intro x
  constructor
  · intro hx
    have hm := eraseLiteral_label_subset T L x hx
    rw [h] at hm
    have hp := (LCS.Finset.mem_erase _ _ _).mp hm
    exact False.elim (hp.2 ((LCS.Finset.mem_singleton _ _).mp hp.1))
  · exact fun hx => False.elim ((LCS.Finset.mem_empty _).mp hx)


proof_of eraseLiteral_treeStepCount_le := by
  induction T with
  | axiom_ C =>
    rw [eraseLiteral]
    split <;> exact Nat.le_refl _
  | resolve A B P ihA ihB =>
    rw [eraseLiteral]
    split
    · unfold replayResolve
      split
      · split
        · simp only [treeStepCount]; omega
        · simp only [treeStepCount]; omega
      · simp only [treeStepCount]; omega
    · exact Nat.le_refl _

helper theorem replayResolve_inputs (A B : ResolutionTree) (P : Literal) :
    LCS.Finset.Subset (replayResolve A B P).inputs
      (LCS.Finset.union A.inputs B.inputs) := by
  unfold replayResolve
  split
  · split
    · exact fun _ hx => hx
    · exact fun _ hx => LCS.Finset.mem_union.mpr (Or.inr hx)
  · exact fun _ hx => LCS.Finset.mem_union.mpr (Or.inl hx)

helper /-- Every output input is unchanged or is an original input containing L with
exactly L removed. No other input clauses are introduced by contraction. -/
theorem eraseLiteral_inputs (T : ResolutionTree) (L : Literal) (C : Clause)
    (hC : C ∈ (T.eraseLiteral L).inputs) :
    C ∈ T.inputs ∨ ∃ A ∈ T.inputs, L ∈ A ∧ C = GCNF.Clause.remove A L := by
  induction T with
  | axiom_ A =>
    rw [eraseLiteral] at hC
    split at hC
    · have he : C = GCNF.Clause.remove A L := (LCS.Finset.mem_singleton _ _).mp hC
      exact Or.inr ⟨A, (LCS.Finset.mem_singleton _ _).mpr rfl, ‹L ∈ (axiom_ A).label›, he⟩
    · exact Or.inl hC
  | resolve A B P ihA ihB =>
    rw [eraseLiteral] at hC
    split at hC
    · have hm := replayResolve_inputs (A.eraseLiteral L) (B.eraseLiteral L) P C hC
      rcases LCS.Finset.mem_union.mp hm with hm | hm
      · rcases ihA hm with h | ⟨D, hD, hL, he⟩
        · exact Or.inl (LCS.Finset.mem_union.mpr (Or.inl h))
        · exact Or.inr ⟨D, LCS.Finset.mem_union.mpr (Or.inl hD), hL, he⟩
      · rcases ihB hm with h | ⟨D, hD, hL, he⟩
        · exact Or.inl (LCS.Finset.mem_union.mpr (Or.inr h))
        · exact Or.inr ⟨D, LCS.Finset.mem_union.mpr (Or.inr hD), hL, he⟩
    · exact Or.inl hC

proof_of eraseLiteral_novel_input_restore := by
  rcases eraseLiteral_inputs T L C hC with h | ⟨A, hA, hL, rfl⟩
  · exact False.elim (hNovel h)
  · have hRestore : clauseWithLiteral (GCNF.Clause.remove A L) L = A := by
      apply LCS.Finset.ext
      intro x
      simp only [clauseWithLiteral, GCNF.Clause.remove,
        LCS.Finset.mem_insert, LCS.Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨hx, _⟩)
        · exact hL
        · exact hx
      · intro hx
        by_cases he : x = L
        · exact Or.inl he
        · exact Or.inr ⟨hx, he⟩
    exact hRestore.symm ▸ hA


proof_of eraseLiteral_inputs_ordinary := by
  intro C hC hEmpty
  rcases eraseLiteral_inputs T L C hC with h | ⟨A, hA, hL, he⟩
  · exact hOrd C h hEmpty
  · have hRemove : GCNF.Clause.remove A L = GCNF.Clause.empty := he.symm.trans hEmpty
    have hSingle : A = GCNF.Clause.single L := by
      apply LCS.Finset.ext
      intro x
      rw [GCNF.Clause.single, LCS.Finset.mem_singleton]
      constructor
      · intro hx
        by_cases hEq : x = L
        · exact hEq
        · have hm : x ∈ GCNF.Clause.remove A L :=
            (LCS.Finset.mem_erase _ _ _).mpr ⟨hx, hEq⟩
          rw [hRemove] at hm
          exact False.elim ((LCS.Finset.mem_empty _).mp hm)
      · intro hEq
        exact hEq ▸ hL
    exact hUnit (hSingle ▸ hA)


end LCS.Resolution.Method.ResolutionTree
