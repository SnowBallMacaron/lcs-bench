import LCS.FirstOrder.Effective.Presentation

namespace LCS.FirstOrder.Effective

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.SignedFormulae LCS.FirstOrder.Completeness.Search

proof_of decodeSymbol_eq_some := by
  rcases s with ⟨c, hc⟩
  by_cases h : accept n = true
  · simp [decodeSymbol, h, Subtype.mk.injEq]
  · simp only [decodeSymbol, h, dite_false, reduceCtorEq, false_iff]
    intro heq
    subst n
    exact h hc


proof_of symbolEq_correct := by
  simp [symbolEq, Subtype.ext_iff]


proof_of EffectiveInput.mem_antecedentPrefix := by
  simp [EffectiveInput.antecedentPrefix, EffectiveInput.toInfSequent, List.mem_filterMap]


proof_of EffectiveInput.mem_succedentPrefix := by
  simp [EffectiveInput.succedentPrefix, EffectiveInput.toInfSequent, List.mem_filterMap]


end LCS.FirstOrder.Effective
