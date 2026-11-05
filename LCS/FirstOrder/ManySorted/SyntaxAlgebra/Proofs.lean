import LCS.FirstOrder.ManySorted.SyntaxAlgebra

namespace LCS.FirstOrder.ManySorted.SyntaxAlgebra

open LCS.FirstOrder.ManySorted.CongruenceClosure

proof_of msVarToken_injective := by
  intro ⟨s, i⟩ ⟨t, j⟩ h
  cases h
  rfl


proof_of msConstToken_injective := by
  intro ⟨s, c⟩ ⟨t, d⟩ h
  cases h
  rfl


proof_of msFunToken_injective := by
  intro f g h
  cases h
  rfl


proof_of msPredToken_injective := by
  intro P Q h
  cases h
  rfl


proof_of msSymbolFamilies_disjoint := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro a b h <;> cases h


proof_of msDataSort_injective := by
  intro s t h
  cases h
  rfl


proof_of msDataSort_ne_bool := by intro h; cases h


proof_of msConstructorToken_rank := by
  cases op <;> rfl


open LCS.FirstOrder.Basic (FirstOrderLanguage)

open LCS.FirstOrder.Syntax.Algebra (SyntaxOperation FirstOrderSort syntaxAlphabet)

proof_of msToOneSorted_from := by
  cases O
  simp [msToOneSorted, msFromOneSorted]


proof_of msOneSorted_has_singleton_presentation := by
  obtain ⟨ef, hf⟩ := O.funSymbols_countable
  obtain ⟨ec, hc⟩ := O.constSymbols_countable
  obtain ⟨ep, hp⟩ := O.predSymbols_countable
  exact ⟨msFromOneSorted O ef hf ec hc ep hp, inferInstance,
    msToOneSorted_from O ef hf ec hc ep hp⟩


proof_of msSingletonSort_inverse := by
  constructor
  · intro s
    cases s with
    | none => rfl
    | some s => exact congrArg some (Subsingleton.elim M.someSort s)
  · intro s; cases s <;> rfl


proof_of msSingletonConstructor_inverse := by
  constructor
  · intro op
    cases op with
    | const s c => cases Subsingleton.elim s M.someSort; rfl
    | eq_ h s => cases Subsingleton.elim s M.someSort; rfl
    | all s i => cases Subsingleton.elim s M.someSort; rfl
    | ex s i => cases Subsingleton.elim s M.someSort; rfl
    | _ => rfl
  · intro op; cases op <;> rfl


proof_of msSingletonConstructor_rank := by
  cases op <;> simp [msConstructorRank, msEraseSingletonSort, msEraseSingletonConstructor,
    msToOneSorted, SyntaxOperation.arity, SyntaxOperation.inputSort,
    SyntaxOperation.outputSort, List.map_map, List.map_const', Function.comp_def]


proof_of msSingletonVariable_inverse := by
  exact Prod.ext (Subsingleton.elim _ _) rfl


proof_of msAmbientBool_iff := Iff.rfl


proof_of msAmbientData_iff := Iff.rfl


proof_of msAmbientString_nonempty := by
  intro hw
  subst w
  cases s <;> simp [msAmbientStringAt, msStringHeadSort] at h


proof_of msAmbientString_cons := by
  cases s <;> simp [msAmbientStringAt, msStringHeadSort, hrank]


proof_of msAmbientString_append := by
  cases w with
  | nil => exact False.elim (msAmbientString_nonempty h rfl)
  | cons a rest =>
    cases s with
    | none => simp [msAmbientStringAt]
    | some _ => exact h


proof_of msAmbientBool_prefix := msAmbientString_append (s := none) h tail


proof_of msAmbientData_isBool := msAmbientString_nonempty h


proof_of msAmbientString_nonempty_carrier := by
  cases s with
  | none => exact ⟨msAmbientBottom L⟩
  | some s => exact ⟨msAmbientVariable L s 0⟩


proof_of msFunctionString_val := rfl


proof_of msPredicateString_val := rfl


proof_of msEqualityString_val := rfl


proof_of msPredicateString_nullary := by
  have he : List.ofFn (fun i => (args i).val) = [] :=
    List.eq_nil_of_length_eq_zero (by simp [h])
  simp only [msPredicateString, he, List.flatten_nil]


proof_of msFunctionString_rank := rfl


proof_of msPredicateString_rank := rfl


proof_of msEqualityString_rank := rfl


proof_of msConstantString_val := rfl


proof_of msPropositionalLetterString_val := rfl


proof_of msAmbientBottom_val := rfl


proof_of msConjString_val := rfl


proof_of msDisjString_val := rfl


proof_of msImplString_val := rfl


proof_of msEquivString_val := rfl


proof_of msNegString_val := rfl


proof_of msAllString_val := rfl


proof_of msExString_val := rfl


proof_of msAmbientStringAlgebra_closed := ((msAmbientStringAlgebra L).operation op args).property


proof_of msAmbientStringAlgebra_propositionalLetter := by
  apply Subtype.ext
  exact msPredicateString_nullary P h _


proof_of msGeneratedString_variable := .var s i


proof_of msGeneratedString_closed := fun op args h => .operation op args h


proof_of msGeneratedString_least := by
  induction h with
  | var s i => exact variables s i
  | operation op args _ ih => exact closed op args ih


proof_of msGeneratedStringAlgebra_operation := rfl


proof_of msGeneratedString_iff_term := by
  -- REPAIR(T10-47): proof pending
  sorry


proof_of msGeneratedString_iff_formula := by
  -- REPAIR(T10-47): proof pending
  sorry


proof_of msString_free_generation := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s w h
    cases s with
    | none => exact False.elim h
    | some s =>
      obtain ⟨i, rfl⟩ := h
      exact .var s i
  · intro op _ args h
    exact .operation op args h
  · intro D hv hc s w h
    exact msGeneratedString_least D (fun s i => hv _ _ ⟨i, rfl⟩)
      (fun op args hg => hc op True.intro args hg) h
  · -- REPAIR(T10-48): proof pending
    sorry


proof_of msTermString_free_generation := by
  -- REPAIR(T10-48): proof pending
  sorry


proof_of msFormulaString_free_generation := by
  -- REPAIR(T10-48): proof pending
  sorry


proof_of msString_operation_injective := (msString_free_generation L).free.1 op True.intro args more ha hb h


proof_of msString_operation_separated := (msString_free_generation L).free.2.1 op other True.intro True.intro hne args more ha hb


proof_of msString_operation_not_variable := (msString_free_generation L).free.2.2 op True.intro args ha


proof_of msFunctionString_separated := by
  intro h
  exact hne (msFunToken_injective L (List.cons.inj h).1)


proof_of msString_universal_extension := by
  -- REPAIR(T10-50): proof pending — unique homomorphic extension of every sorted variable assignment
  sorry

end LCS.FirstOrder.ManySorted.SyntaxAlgebra
