import LCS.FOResolution.Unification.Algorithm

namespace LCS.FOResolution.Unification.Algorithm

proof_of termToRankedTree_sorted := by
  induction t with
  | var _ => trivial
  | const _ => trivial
  | func f args ih => exact ih


helper /-- Decode after encoding returns the original term. -/
theorem rankedTreeToTerm_termToRankedTree {L : LCS.FirstOrder.Basic.Language}
    (t : LCS.FirstOrder.Basic.Term L) :
    rankedTreeToTerm (termToRankedTree t) (termToRankedTree_sorted t) = t := by
  induction t with
  | var _ => rfl
  | const _ => rfl
  | func f args ih =>
      simp only [termToRankedTree, rankedTreeToTerm]
      congr 1
      funext i
      exact ih i


helper /-- Encoding the decoder recovers every term-sorted tree. -/
theorem termToRankedTree_rankedTreeToTerm {L : LCS.FirstOrder.Basic.Language}
    (t : SyntaxRankedTree L) (h : IsTermTree t) :
    termToRankedTree (rankedTreeToTerm t h) = t := by
  induction t with
  | var _ => rfl
  | node symbol children ih =>
    cases symbol with
    | constant c =>
      change RankedTreeData.node _ _ = RankedTreeData.node _ _
      congr 1
      funext i
      exact Fin.elim0 i
    | function f =>
      simp only [rankedTreeToTerm, termToRankedTree]
      congr 1
      funext i
      exact ih i (h i)
    | predicate _ => exact False.elim h
    | equality _ => exact False.elim h


proof_of termToRankedTree_bijective := by
  constructor
  · intro a b hab
    have hd := congrArg (fun t : SortedTermTree L => rankedTreeToTerm t.val t.property) hab
    simpa only [rankedTreeToTerm_termToRankedTree] using hd
  · intro t
    refine ⟨rankedTreeToTerm t.val t.property, ?_⟩
    apply Subtype.ext
    exact termToRankedTree_rankedTreeToTerm t.val t.property


proof_of atomToRankedTree_sorted := by
  cases a with
  | predN p args => exact fun i => termToRankedTree_sorted (args i)
  | eq_ hL lhs rhs =>
      intro i
      change IsTermTree (if i.val = 0 then termToRankedTree lhs else termToRankedTree rhs)
      split <;> apply termToRankedTree_sorted


proof_of atomToRankedTree_bijective := by
  -- REPAIR(T8-13a): proof pending
  sorry


proof_of repairableAt_distinct_variables := by
  exact ⟨x, .var y, rfl, rfl, h⟩


proof_of fatalDisagreement_not_unifiable := by
  -- Lift the existing var_occurs_not_unifiable and
  -- incompatible_head_not_pairwise_unifiable local obstructions
  -- through common-address subtree lookup and homomorphic substitution.
  -- REPAIR(T8-14): proof pending
  sorry


proof_of inDom_root := by
  cases t <;> rfl


proof_of not_inDom_zero := by
  cases t <;> simp [inDom, RankedTreeData.subtreeAt]


proof_of inDom_var_iff := by
  cases u <;> simp [inDom, RankedTreeData.subtreeAt]


proof_of TreeNav_leaf_iff := by
  cases h : t.subtreeAt u with
  | none => simp [inDom, h] at hu
  | some s =>
    cases s with
    | var x => simp [TreeNav, RankedTreeData.isLeaf, h, RankedTreeData.subtreeAt]
    | node f children =>
      simp only [TreeNav, RankedTreeData.isLeaf, h, beq_iff_eq, Option.bind_some,
        RankedTreeData.subtreeAt]
      constructor
      · intro hz i
        simp [hz]
      · intro hall
        by_cases hz : rank f = 0
        · exact hz
        · have hp : 0 < rank f := Nat.pos_of_ne_zero hz
          have h0 := hall 0
          simp [hp] at h0


proof_of TreeNav_variable_iff := by
  cases h : t.labelAt u with
  | none => simp [TreeNav, RankedTreeData.isVariable, h]
  | some l => cases l <;> simp [TreeNav, RankedTreeData.isVariable, h]


proof_of TreeNav_left_eq := by
  unfold inDom at hu
  simp only [TreeNav, RankedTreeData.firstChild, hu, Bool.true_and]
  by_cases hl : t.isLeaf u = true <;> simp [hl]


proof_of TreeNav_right_eq := by
  simp [TreeNav, RankedTreeData.nextSibling]


proof_of TreeNav_substitution_eq := ⟨fun _ => rfl, fun _ _ => rfl⟩


proof_of SubstOps_identity_eq := rfl


proof_of SubstOps_compose_eq := rfl


proof_of SubstOps_subtreeAt_eq := rfl


proof_of newPair_eq_singleton := by
  constructor
  · simp [newPair, SubstOps, rankedNewPair, hx, ht]
  · intro y; rfl


proof_of preorderAddresses_spec := by
  -- REPAIR(T8-16): proof pending
  sorry


proof_of occurCheck_eq_true_iff := by
  -- REPAIR(T8-15): proof pending
  sorry


proof_of testAndSubstitute_local_agreement := by
  -- REPAIR(T8-15): proof pending
  sorry


proof_of incremental_unification := by
  -- REPAIR(T8-20): proof pending
  sorry


proof_of wellFoundedLexOrder_wf := by
  -- BEGIN PROOF
    apply WellFounded.intro
    intro ⟨a, b⟩
    revert b
    induction a using Nat.strongRecOn with
    | ind a iha =>
      intro b
      induction b using Nat.strongRecOn with
      | ind b ihb =>
        constructor
        intro ⟨c, d⟩ hlt
        unfold WellFoundedLexOrder at hlt
        rcases hlt with hc | ⟨hc, hd⟩
        · exact iha c hc d
        · subst hc; exact ihb d hd


proof_of repair_decreases_varCount := by
  -- REPAIR(T8-17): proof pending
  sorry


proof_of enterChildren_decreases_measure := by
  -- REPAIR(T8-17): proof pending
  sorry


proof_of childVisit_decreases_measure := by
  -- REPAIR(T8-17): proof pending
  sorry


proof_of nextChild_decreases_measure := by
  -- REPAIR(T8-17): proof pending
  sorry


proof_of childReturn_decreases_measure := by
  -- REPAIR(T8-17): proof pending
  sorry


proof_of repair_decreases_measure := by
  exact Or.inl (repair_decreases_varCount state u hNode hLive hRepairable)


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


proof_of initialUnifyState_stores := by
  -- REPAIR(T8-19): proof pending
  sorry


proof_of testAndSubstitute_preserves_stores := by
  -- REPAIR(T8-19): proof pending
  sorry


proof_of unify_subtree_postcondition := by
  -- REPAIR(T8-19): proof pending
  sorry


proof_of unification_common_image := by
  -- REPAIR(T8-19): proof pending
  sorry


proof_of unification_correctness := by
  -- REPAIR(T8-21): proof pending
  sorry


proof_of infiniteSubstitutionLabels_ranked := by
  -- REPAIR(T8-22): proof pending
  sorry


proof_of infiniteOccursEquation_has_solution := by
  -- REPAIR(T8-22): proof pending
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
