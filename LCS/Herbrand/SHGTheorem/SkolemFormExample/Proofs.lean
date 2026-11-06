import LCS.Herbrand.SHGTheorem.SkolemFormExample

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
