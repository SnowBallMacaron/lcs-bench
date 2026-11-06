import LCS.FOResolution.Unification.Algorithm

namespace LCS.FOResolution.Unification.Algorithm

proof_of incremental_unification := by
  -- REPAIR(T8-20): proof pending
  sorry

proof_of unifyReturnInvariant_trans := by
  rcases hab with ⟨habCount, habStable⟩
  rcases hbc with ⟨hbcCount, hbcStable⟩
  refine ⟨Nat.le_trans hbcCount habCount, ?_⟩
  intro hEq
  have habEq : varCount b.tree1 b.tree2 = varCount a.tree1 a.tree2 := by omega
  have hbcEq : varCount c.tree1 c.tree2 = varCount b.tree1 b.tree2 := by omega
  exact (hbcStable hbcEq).trans (habStable habEq)


proof_of testAndSubstitute_returnInvariant := by
  -- REPAIR(T8-18): proof pending
  sorry

proof_of unification_correctness := by
  -- REPAIR(T8-21): proof pending
  sorry

proof_of exampleUnification_8_4_2_run := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩


proof_of exampleUnification_8_4_2_result := by
  -- REPAIR(T8-24): proof pending
  sorry


proof_of exampleUnification_8_4_2_disagreements := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩


proof_of exampleUnification_8_4_2_updates := by
  simp [exampleUnification_8_4_2, exTree_t1, exTree_t2, exUnifiedTree_8_4_2,
    exApplySubstitution, exSubstitutionImage]


proof_of exampleUnification_8_4_2_composition := by
  simp [exampleUnification_8_4_2, exMgu_8_4_2, exComposeSubstitution,
    exApplySubstitution, exSubstitutionImage]


end LCS.FOResolution.Unification.Algorithm
