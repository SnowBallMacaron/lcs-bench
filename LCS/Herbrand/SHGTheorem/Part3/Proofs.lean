import LCS.Herbrand.SHGTheorem.Part3

section

namespace LCS.Herbrand.SHGTheorem

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Substitution

section SkExComputation

proof_of skExSKExistsW_eq := set_option backward.isDefEq.respectTransparency false in
  by
    simp! [skExFormula, skExSKExistsW, skExSKExistsU, skExSKExistsY, skExFullSK,
      usExFormula, usExExistsWSubformula, usExExistsUSubformula, usExExistsYSubformula,
      skolemFormExactAux, skolemSubst, exactSkolemTerm, exactSkolemArgument,
      liftFormulaSkolem, liftTermSkolem, formulaSubstN, termSubst,
      skExSpec, universalScopeAux, SkolemSpec.n, SkolemSpec.allocations, SkolemSpec.allocation,
      SkolemSpec.skolemRank, SkolemSpec.skolemScope, existentialDescriptors,
      existentialDescriptorsAux, skolemDescriptorCount,
      skExSkolemLang, SkolemSpec.language, SkolemLanguage,
      SKExSkolemFunc.f, SKExSkolemFunc.g, skExC, usExLang,
      usExVec1, usExVec2, skExVec1, skExVec2,
      funext_iff, Fin.forall_fin_succ]

    dsimp [SkolemSpec.language, SkolemLanguage, usExLang]
    simp! [Fin.forall_fin_succ, funext_iff, usExVec1, usExVec2, skExVec1, skExVec2,
      liftTermSkolem, termSubst, exactSkolemArgument, skExSpec,
      SkolemSpec.skolemScope, SkolemSpec.allocation, SkolemSpec.allocations,
      existentialDescriptors, existentialDescriptorsAux, universalScopeAux,
      usExFormula, SKExSkolemFunc.f, SKExSkolemFunc.g]
    all_goals
      repeat first
        | apply And.intro
        | rfl
        | (intro i; rcases i with ⟨i, hi⟩
           first | change i < 1 at hi | change i < 2 at hi
           have h : i = 0 ∨ i = 1 := by omega
           rcases h with h | h <;> subst i <;> first | rfl | omega)


proof_of skExSKExistsU_eq := set_option backward.isDefEq.respectTransparency false in
  by
    simp! [skExFormula, skExSKExistsW, skExSKExistsU, skExSKExistsY, skExFullSK,
      usExFormula, usExExistsWSubformula, usExExistsUSubformula, usExExistsYSubformula,
      skolemFormExactAux, skolemSubst, exactSkolemTerm, exactSkolemArgument,
      liftFormulaSkolem, liftTermSkolem, formulaSubstN, termSubst,
      skExSpec, universalScopeAux, SkolemSpec.n, SkolemSpec.allocations, SkolemSpec.allocation,
      SkolemSpec.skolemRank, SkolemSpec.skolemScope, existentialDescriptors,
      existentialDescriptorsAux, skolemDescriptorCount,
      skExSkolemLang, SkolemSpec.language, SkolemLanguage,
      SKExSkolemFunc.f, SKExSkolemFunc.g, skExC, usExLang,
      usExVec1, usExVec2, skExVec1, skExVec2,
      funext_iff, Fin.forall_fin_succ]

    dsimp [SkolemSpec.language, SkolemLanguage, usExLang]
    simp! [Fin.forall_fin_succ, funext_iff, usExVec1, usExVec2, skExVec1, skExVec2,
      liftTermSkolem, termSubst, exactSkolemArgument, skExSpec,
      SkolemSpec.skolemScope, SkolemSpec.allocation, SkolemSpec.allocations,
      existentialDescriptors, existentialDescriptorsAux, universalScopeAux,
      usExFormula, SKExSkolemFunc.f, SKExSkolemFunc.g]
    all_goals
      repeat first
        | apply And.intro
        | rfl
        | (intro i; rcases i with ⟨i, hi⟩
           first | change i < 1 at hi | change i < 2 at hi
           have h : i = 0 ∨ i = 1 := by omega
           rcases h with h | h <;> subst i <;> first | rfl | omega)


proof_of skExSKExistsY_eq := set_option backward.isDefEq.respectTransparency false in
  by
    simp! [skExFormula, skExSKExistsW, skExSKExistsU, skExSKExistsY, skExFullSK,
      usExFormula, usExExistsWSubformula, usExExistsUSubformula, usExExistsYSubformula,
      skolemFormExactAux, skolemSubst, exactSkolemTerm, exactSkolemArgument,
      liftFormulaSkolem, liftTermSkolem, formulaSubstN, termSubst,
      skExSpec, universalScopeAux, SkolemSpec.n, SkolemSpec.allocations, SkolemSpec.allocation,
      SkolemSpec.skolemRank, SkolemSpec.skolemScope, existentialDescriptors,
      existentialDescriptorsAux, skolemDescriptorCount,
      skExSkolemLang, SkolemSpec.language, SkolemLanguage,
      SKExSkolemFunc.f, SKExSkolemFunc.g, skExC, usExLang,
      usExVec1, usExVec2, skExVec1, skExVec2,
      funext_iff, Fin.forall_fin_succ]

    dsimp [SkolemSpec.language, SkolemLanguage, usExLang]
    simp! [Fin.forall_fin_succ, funext_iff, usExVec1, usExVec2, skExVec1, skExVec2,
      liftTermSkolem, termSubst, exactSkolemArgument, skExSpec,
      SkolemSpec.skolemScope, SkolemSpec.allocation, SkolemSpec.allocations,
      existentialDescriptors, existentialDescriptorsAux, universalScopeAux,
      usExFormula, SKExSkolemFunc.f, SKExSkolemFunc.g]
    all_goals
      repeat first
        | apply And.intro
        | rfl
        | (intro i; rcases i with ⟨i, hi⟩
           first | change i < 1 at hi | change i < 2 at hi
           have h : i = 0 ∨ i = 1 := by omega
           rcases h with h | h <;> subst i <;> first | rfl | omega)


proof_of skExFullSK_eq := set_option backward.isDefEq.respectTransparency false in
  by
    have h : skolemFormExactAux skExSpec
        (liftFormulaSkolem (skolemRank := skExSpec.skolemRank) usExFormula)
        [] skExSpec.indices = some (skExFullSK, 3) := by
      simp! [skExFormula, skExSKExistsW, skExSKExistsU, skExSKExistsY, skExFullSK,
      usExFormula, usExExistsWSubformula, usExExistsUSubformula, usExExistsYSubformula,
      skolemFormExactAux, skolemSubst, exactSkolemTerm, exactSkolemArgument,
      liftFormulaSkolem, liftTermSkolem, formulaSubstN, termSubst,
      skExSpec, universalScopeAux, SkolemSpec.n, SkolemSpec.allocations, SkolemSpec.allocation,
      SkolemSpec.skolemRank, SkolemSpec.skolemScope, existentialDescriptors,
      existentialDescriptorsAux, skolemDescriptorCount,
      skExSkolemLang, SkolemSpec.language, SkolemLanguage,
      SKExSkolemFunc.f, SKExSkolemFunc.g, skExC, usExLang,
      usExVec1, usExVec2, skExVec1, skExVec2,
      funext_iff, Fin.forall_fin_succ, SkolemSpec.indices, List.ofFn_succ]

      dsimp [SkolemSpec.language, SkolemLanguage, usExLang]
      simp! [Fin.forall_fin_succ, funext_iff, usExVec1, usExVec2, skExVec1, skExVec2,
        liftTermSkolem, termSubst, exactSkolemArgument, skExSpec,
        SkolemSpec.skolemScope, SkolemSpec.allocation, SkolemSpec.allocations,
        existentialDescriptors, existentialDescriptorsAux, universalScopeAux,
        usExFormula, SKExSkolemFunc.f, SKExSkolemFunc.g]
      all_goals
        repeat first
          | apply And.intro
          | rfl
          | (intro i; rcases i with ⟨i, hi⟩
             first | change i < 1 at hi | change i < 2 at hi
             have h : i = 0 ∨ i = 1 := by omega
             rcases h with h | h <;> subst i <;> first | rfl | omega)
    have ht := skolemFormExactAux_top_formula_result skExSpec
    change skolemFormExactAux skExSpec
      (liftFormulaSkolem (skolemRank := skExSpec.skolemRank) usExFormula)
      [] skExSpec.indices = some (skolemForm skExSpec, skExSpec.n) at ht
    rw [h] at ht
    exact (congrArg Prod.fst (Option.some.inj ht)).symm


end SkExComputation

end LCS.Herbrand.SHGTheorem

end

section

namespace LCS.Herbrand.SHGTheorem

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Substitution

helper /-- Example 7.6.4: the witness retains exactly the displayed source B. -/
theorem cInstExDerivation_source :
    cInstExDerivation.source = cInstExSkolemForm := rfl

proof_of cInstExCInstance_isCInstanceOf := ⟨cInstExDerivation, cInstExDerivation_source,
    cInstExDerivation_toFormula, cInstExDerivation_wellFormed⟩


proof_of usExScopeOfExistsY := by
  -- BEGIN PROOF
    simp only [universalScope, usExFormula, universalScopeAux,
               usExExistsYSubformula,
               List.mem_append, List.mem_cons, List.mem_nil_iff,
               Prod.mk.injEq, List.nil_append, or_false,
               List.append_assoc]
    right; right; right; right; left; trivial


proof_of usExScopeOfExistsU := by
  -- BEGIN PROOF
    simp only [universalScope, usExFormula, universalScopeAux,
               usExExistsUSubformula,
               List.mem_append, List.mem_cons, List.mem_nil_iff,
               Prod.mk.injEq, List.nil_append, or_false,
               List.append_assoc]
    right; right; right; right; right; right; right; right; right; right; left; trivial


proof_of usExScopeOfExistsW := by
  -- BEGIN PROOF
    simp only [universalScope, usExFormula, universalScopeAux,
               usExExistsWSubformula,
               List.mem_append, List.mem_cons, List.mem_nil_iff,
               Prod.mk.injEq, List.nil_append, or_false,
               List.append_assoc]
    right; right; right; right; right; right; right; right; right; right; right; right; left; trivial


end LCS.Herbrand.SHGTheorem

end
