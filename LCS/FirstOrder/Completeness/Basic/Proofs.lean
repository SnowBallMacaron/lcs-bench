import LCS.FirstOrder.Completeness.Basic

namespace LCS.FirstOrder.Completeness

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.SignedFormulae

open LCS.FirstOrder.Gentzen.Hintikka

proof_of exCounterDomainH_const := ⟨_, 0, Or.inl rfl, rfl⟩


proof_of exCounterDomainH_y1 := ⟨_, 0, Or.inr (Or.inl rfl), rfl⟩


proof_of exCounterDomainH_y2 := ⟨_, 0, Or.inr (Or.inr rfl), rfl⟩


proof_of exCounterDomainH_func := by
  obtain ⟨base, n, hb, rfl⟩ := ht
  exact ⟨base, n + 1, hb, rfl⟩

proof_of exCounterInterpWith_falsifies := by
  have hn : ¬ formulaEvalN (exCounterInterpWith p q) exFormulaPQa as := by
    intro h
    simp only [exFormulaPQa, formulaEvalN, LCS.FirstOrder.Basic.implM,
      LCS.FirstOrder.Basic.andM, termEval] at h
    exact hPf (h ⟨⟨⟨Term.var 5, exCounterDomainH_y2⟩, hP⟩, hQ⟩
      ⟨Term.var 3, exCounterDomainH_y1⟩)
  refine ⟨hn, as, ?_, ?_⟩
  · intro A h; cases h
  · intro B h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst B
    exact hn

end LCS.FirstOrder.Completeness
