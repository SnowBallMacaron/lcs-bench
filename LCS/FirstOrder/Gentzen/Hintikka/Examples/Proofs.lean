import LCS.FirstOrder.Gentzen.Hintikka.Examples

section

namespace LCS.FirstOrder.Gentzen.Hintikka

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SemanticsN.Substitution

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.SignedFormulae

open LCS.FirstOrder.SyntaxN.Variables

proof_of exSearchCounterModel_falsifies := by
  -- BEGIN PROOF
    refine ⟨fun _ => exCounterDomain.y0, ?_, ?_⟩
    · intro A hA
      simp at hA
    · intro B hB
      rcases List.mem_singleton.mp hB with rfl
      intro hImpl
      -- ∃x(P ⊃ Q(x)) is true: witness x = y_0 gives P ⊃ Q(y_0) = T ⊃ T = T
      have hEx : formulaEvalN exSearchCounterModel
          (FormulaN.ex 0
            (FormulaN.impl
              (FormulaN.predN ExPredPQ.P (fun i => Fin.elim0 i))
              (FormulaN.predN ExPredPQ.Q (fun _ => Term.var 0))))
          (fun _ => exCounterDomain.y0) := by
        refine ⟨exCounterDomain.y0, ?_⟩
        simp [formulaEvalN, termEval, assignUpdate, exSearchCounterModel]
      -- So P ⊃ ∀z Q(z) holds under hImpl hEx.
      -- P holds (arity 0)
      have hP : formulaEvalN exSearchCounterModel
          (FormulaN.predN ExPredPQ.P (fun i => Fin.elim0 i))
          (fun _ => exCounterDomain.y0) := by
        simp [formulaEvalN, exSearchCounterModel]
      -- So ∀z Q(z) holds, but specialize at y_2 gives False.
      have hAll := (hImpl hEx) hP
      specialize hAll exCounterDomain.y2
      simp [formulaEvalN, termEval, assignUpdate, exSearchCounterModel] at hAll


proof_of exSearchCounterModelTwo_falsifies := by
  refine ⟨fun _ => exCounterDomainTwo.y1, ?_, ?_⟩
  · intro A hA; cases hA
  · intro B hB
    obtain rfl := List.mem_singleton.mp hB
    intro hImpl
    have hEx : formulaEvalN exSearchCounterModelTwo
        (.ex 0 (.impl (.predN ExPredPQ.P (fun i => Fin.elim0 i))
          (.predN ExPredPQ.Q (fun _ => .var 0))))
        (fun _ => exCounterDomainTwo.y1) := by
      refine ⟨exCounterDomainTwo.y1, ?_⟩
      simp [formulaEvalN, termEval, assignUpdate, exSearchCounterModelTwo]
    have hP : formulaEvalN exSearchCounterModelTwo
        (.predN ExPredPQ.P (fun i => Fin.elim0 i))
        (fun _ => exCounterDomainTwo.y1) := by
      simp [formulaEvalN, exSearchCounterModelTwo]
    have hAll := (hImpl hEx) hP
    specialize hAll exCounterDomainTwo.y2
    simp [formulaEvalN, termEval, assignUpdate, exSearchCounterModelTwo] at hAll


end LCS.FirstOrder.Gentzen.Hintikka

end
