import LCS.FirstOrder.Gentzen.Search.NoFunction.Examples

section

namespace LCS.FirstOrder.Gentzen.Hintikka

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.Search.NoFunction

helper /-- Example 5.4.3: Computed initialization, with y₀ = x₁ and AVAIL₀
    enumerating x₄, x₅, ... . -/
theorem Hintikka.exSearchInitial_5_4_3 :
    (exSearchRun_5_4_3 0).2.TERM0 = [.var 1] ∧
    ∀ n, (Init.default exSearchSeq_5_4_3).avail0.entries n = some (.var (4 + n)) := by
  exact ⟨rfl, fun _ => rfl⟩

proof_of exSearchRoundThree_5_4_3 := open LCS.FirstOrder.Gentzen.Search.NoFunction.Examples.Proofs.Hintikka in
  by
    -- REPAIR(T91): proof pending
    sorry


end LCS.FirstOrder.Gentzen.Hintikka

end

section

namespace LCS.FirstOrder.Gentzen.Hintikka

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.Search.NoFunction

helper /-- Example 5.4.4: The initial diagram, terms, and availability stream
    are computed directly from the canonical initialization. -/
theorem Hintikka.exSearchInitial_5_4_4 :
    some (exSearchRun_5_4_4 0).1.traceNodes = exSearchExpectedNodes_5_4_4[0]? ∧
    (exSearchRun_5_4_4 0).2.TERM0 = [.var 1] ∧
    ∀ n, (Init.default exSearchSeq_5_4_4).avail0.entries n = some (.var (4 + n)) := by
  exact ⟨rfl, rfl, fun _ => rfl⟩

proof_of exSearchTrace_5_4_4 := open LCS.FirstOrder.Gentzen.Search.NoFunction.Examples.Proofs.Hintikka in
  by
    -- REPAIR(T92): proof pending
    sorry


helper /-- Example 5.4.4: Every formula of Q(x₄), P → Q(x₅) is atomic,
    and no formula occurs on both sides. -/
theorem Hintikka.exSearchOpenLeaf_properties_5_4_4 :
    (∀ F ∈ exSearchOpenLeaf_5_4_4.antecedent ++ exSearchOpenLeaf_5_4_4.succedent,
      F.isAtomic = true) ∧ ¬ isAxiom exSearchOpenLeaf_5_4_4 := by
  constructor
  · intro F hF
    simp only [exSearchOpenLeaf_5_4_4, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl <;> rfl
  · rintro ⟨F, hLeft, hRight⟩
    simp only [exSearchOpenLeaf_5_4_4, List.mem_cons, List.not_mem_nil, or_false] at hLeft hRight
    rcases hLeft with rfl | rfl
    · have hfn := (FormulaN.predN.inj hRight).2
      have hval := congrFun (eq_of_heq hfn) (0 : Fin 1)
      cases hval
    · cases hRight

helper /-- Example 5.4.4: The third-round tree contains the displayed finished,
    all-atomic, non-axiom leaf with three empty branch-use records. -/
theorem Hintikka.exSearchFinishedLeaf_5_4_4 :
    (exSearchOpenLeaf_5_4_4, (⟨[[], [], []], [[], [], []]⟩ : BranchRecords exampleLangPQ)) ∈
      (exSearchRun_5_4_4 3).1.leaves ∧
    (∀ F ∈ exSearchOpenLeaf_5_4_4.antecedent ++ exSearchOpenLeaf_5_4_4.succedent,
      F.isAtomic = true) ∧
    ¬ isAxiom exSearchOpenLeaf_5_4_4 ∧
    LCS.FirstOrder.Gentzen.Search.NoFunction.SearchState.isFinishedLeaf rfl
      (exSearchRun_5_4_4 3).2 ⟨[[], [], []], [[], [], []]⟩ exSearchOpenLeaf_5_4_4 := by
  have hTrace := congrArg (fun xs => xs[3]?) exSearchTrace_5_4_4
  simp only [List.map_cons, List.map_nil, exSearchExpectedNodes_5_4_4,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hTrace
  have hNode : ([false, false, false, true, false], exSearchOpenLeaf_5_4_4,
      some (⟨[[], [], []], [[], [], []]⟩ : BranchRecords exampleLangPQ)) ∈
      (exSearchRun_5_4_4 3).1.traceNodes := by
    rw [hTrace]
    simp [exSearchExpectedNodes_5_4_4]
  have hLeaf : (exSearchOpenLeaf_5_4_4,
      (⟨[[], [], []], [[], [], []]⟩ : BranchRecords exampleLangPQ)) ∈
      (exSearchRun_5_4_4 3).1.leaves := by
    rw [← SearchTree.traceNodes_leaves]
    exact List.mem_filterMap.mpr ⟨_, hNode, rfl⟩
  obtain ⟨hAtomic, hOpen⟩ := exSearchOpenLeaf_properties_5_4_4
  refine ⟨hLeaf, hAtomic, hOpen, Or.inr ⟨?_, ?_⟩⟩
  · intro F hF
    exact Or.inl (hAtomic F (List.mem_append.mpr (Or.inl hF)))
  · intro F hF
    exact Or.inl (hAtomic F (List.mem_append.mpr (Or.inr hF)))

end LCS.FirstOrder.Gentzen.Hintikka

end
