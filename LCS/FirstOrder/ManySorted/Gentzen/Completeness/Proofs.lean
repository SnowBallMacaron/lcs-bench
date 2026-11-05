import LCS.FirstOrder.ManySorted.Gentzen.Completeness

section

namespace LCS.FirstOrder.ManySorted.Gentzen

open LCS.FirstOrder.ManySorted

open LCS.FirstOrder.ManySorted.Semantics

open LCS.Propositional.Semantics

proof_of msSequentValid_iff_not_falsifiable := by
  constructor
  · intro h M ⟨v, hant, hsucc⟩
    obtain ⟨B, hBmem, hBeval⟩ := h M v hant
    exact boolVal_eq_F_ne_T (hsucc B hBmem) hBeval
  · intro h M v hant
    apply Classical.byContradiction
    intro hcontra
    apply h M
    exact ⟨v, hant, fun B hB => boolVal_ne_T_eq_F (fun hEval => hcontra ⟨B, hB, hEval⟩)⟩






proof_of msRuleValidityIff1 := msRuleValidityIff1Core rule

proof_of msRuleValidityIff2 := msRuleValidityIff2Core rule

proof_of msProofTreeValid := msProofTreeValidCore t

proof_of msSoundnessG := by
  obtain ⟨finite, ⟨⟨f, _hf, hAnt⟩, ⟨g, _hg, hSucc⟩⟩, ⟨t⟩⟩ := h
  intro M v hant
  have hfinite : ∀ A ∈ finite.antecedent, msFormulaEval M A v = BoolVal.T := by
    intro A hA
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hA
    rw [← hi, hAnt i]
    exact hant (f i)
  obtain ⟨B, hB, hEval⟩ := msProofTreeValidCore t M v hfinite
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hB
  refine ⟨g j, ?_⟩
  rw [← hSucc j, hj]
  exact hEval

proof_of msSearchCompletenessValid := by
  -- REPAIR(T10-32b): proof pending — derive finite ordered G support from validity and end-sequent separation.
  sorry

proof_of msGoedelExtendedCompletenessG := by
  constructor
  · -- REPAIR(T10-32a): proof pending — completeness for the separated possibly infinite end sequent.
    sorry
  · exact msSoundnessG hL seq

end LCS.FirstOrder.ManySorted.Gentzen
end
