import LCS.FOResolution.ClauseForm

namespace LCS.FOResolution.ClauseForm

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.Semantics

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.Semantics.Subformulae

proof_of clauseFormConstruction := by
  -- REPAIR(T8-29): proof pending
  sorry


proof_of exClauseOriginal_toEliminated := by
  have hA := (FormulaN.neg exClauseOriginal).toNNF_equiv M s
  have hE := exClauseEliminated.toNNF_equiv M s
  exact ⟨fun h => hE.2 (hA.1 h), fun h => hA.2 (hE.1 h)⟩


proof_of exClauseEliminated_toNNF := by
  exact ⟨(exClauseEliminated.toNNF_equiv M s).1,
    (exClauseEliminated.toNNF_equiv M s).2⟩


proof_of exClauseNNF_toSkolem := by
  -- REPAIR(T8-31): proof pending
  sorry


proof_of exClauseSkolem_toPrenex := by
  -- REPAIR(T8-31): proof pending
  sorry


proof_of exClausePrenex_toCNF := by
  simp only [exClausePrenex, exClauseCNF, formulaEvalN, LCS.FirstOrder.Basic.andM, LCS.FirstOrder.Basic.orM]
  constructor
  · intro h z x
    obtain ⟨h1, h23⟩ := h z x
    rcases h23 with ⟨h2, h3⟩ | h4
    · exact ⟨h1, Or.inl h2, Or.inl h3⟩
    · exact ⟨h1, Or.inr h4, Or.inr h4⟩
  · intro h z x
    obtain ⟨h1, h2, h3⟩ := h z x
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h4
    · rcases h3 with h3 | h4
      · exact Or.inl ⟨h2, h3⟩
      · exact Or.inr h4
    · exact Or.inr h4


proof_of exClauseCNF_toClauses := by
  -- REPAIR(T8-31): proof pending
  sorry

end LCS.FOResolution.ClauseForm
