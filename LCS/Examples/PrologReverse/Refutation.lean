import LCS.Item
import LCS.Util
import LCS.FirstOrder.SemanticsN
import LCS.FOResolution.Unification
import LCS.FOResolution.Method.Soundness
import LCS.SLD.FirstOrder
import LCS.SLD.PrologSyntax
import LCS.SLD.LogicProgramming
import LCS.SLD.LogicProgramming.Correctness
import LCS.Examples.PrologReverse.Program

section
set_option linter.unusedSimpArgs false
namespace LCS.Examples.PrologReverse
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.Unification
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.SLD.FirstOrder
open LCS.SLD.PrologSyntax
open LCS.SLD.LogicProgramming
open LCS.SLD.LogicProgramming.Correctness

/-- Type-index reduction for step 2. -/
theorem step2Idx_eq :
    step2Idx = LCS.Finset.ofList
      [reverse nil (V 15), append (V 15) ⟦b⟧ (V 11), append (V 11) ⟦a⟧ (V 100)] := by
  -- BEGIN PROOF
  unfold step2Idx
  rw [step1Idx_eq]
  apply LCS.Finset.ext
  intro A
  rw [LCS.Finset.mem_image, LCS.Finset.mem_ofList]
  constructor
  · rintro ⟨B, hB, rfl⟩
    rw [LCS.Finset.mem_union] at hB
    rcases hB with herase | himg
    · rw [LCS.Finset.mem_erase, LCS.Finset.mem_ofList] at herase
      obtain ⟨hmem, hne⟩ := herase
      simp at hmem
      rcases hmem with rfl | rfl
      · exact absurd rfl hne
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        right; right
        simp [formulaSubstAll_append, termSubstAll_cons, termSubstAll_nil,
              termSubstAll_a, termSubstAll_b, V, ovr, overrideSubst]
        rfl
    · rw [LCS.Finset.mem_ofList, List.mem_map] at himg
      obtain ⟨A', hA', rfl⟩ := himg
      simp [clauseRevRec, rule, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal] at hA'
      rcases hA' with rfl | rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        left
        simp [formulaSubstAll_reverse, termSubstAll_cons, termSubstAll_nil,
              termSubstAll_b, T, Rt, V, ovr, overrideSubst]
        rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        right; left
        simp [formulaSubstAll_append, termSubstAll_cons, termSubstAll_nil,
              termSubstAll_b, H, Rt, R', V, ovr, overrideSubst]
        rfl
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · refine ⟨reverse (V 13) (V 15), ?_, ?_⟩
      · rw [LCS.Finset.mem_union]; right
        rw [LCS.Finset.mem_ofList, List.mem_map]
        refine ⟨reverse T Rt, ?_, ?_⟩
        · simp [clauseRevRec, rule, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal]
        · show _ = reverse (V 13) (V 15)
          simp [formulaSubstAll_reverse, T, Rt, V, ovr, overrideSubst]
          rfl
      · simp [formulaSubstAll_reverse, termSubstAll_cons, termSubstAll_nil,
              V, ovr, overrideSubst]
        rfl
    · refine ⟨append (V 15) ⟦V 12⟧ (V 14), ?_, ?_⟩
      · rw [LCS.Finset.mem_union]; right
        rw [LCS.Finset.mem_ofList, List.mem_map]
        refine ⟨append Rt ⟦H⟧ R', ?_, ?_⟩
        · simp [clauseRevRec, rule, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal]
        · show _ = append (V 15) ⟦V 12⟧ (V 14)
          simp [formulaSubstAll_append, termSubstAll_cons, termSubstAll_nil,
                H, Rt, R', V, ovr, overrideSubst]
          rfl
      · simp [formulaSubstAll_append, termSubstAll_cons, termSubstAll_nil,
              termSubstAll_b, V, ovr, overrideSubst]
        rfl
    · refine ⟨append (V 11) ⟦a⟧ (V 100), ?_, ?_⟩
      · rw [LCS.Finset.mem_union]; left
        rw [LCS.Finset.mem_erase, LCS.Finset.mem_ofList]
        refine ⟨?_, ?_⟩
        · simp
        · intro h; have hp := (FOAtomCore.predN.inj h).1; cases hp
      · simp [formulaSubstAll_append, termSubstAll_cons, termSubstAll_nil,
              termSubstAll_a, V, ovr, overrideSubst]
        rfl

/-- **Step 3** — close `reverse nil (V 15)` with `clauseRevBase`.

    * ρ₃: identity (clauseRevBase has no variables).
    * σ₃: V 15 ↦ nil.
    * New current goal: `[append nil ⟦b⟧ (V 11), append (V 11) ⟦a⟧ (V 100)]`. -/
noncomputable def revSLDStep3 :
    (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ revProgram) [queryGoal]
      (((step2Idx.erase (reverse nil (V 15))).union
        (LCS.Finset.ofList
          (clauseRevBase.bodyFOAtoms.map (fun A =>
            (A.subst (hNoEq := language_noEq)) Term.var)))
        ).image (fun A => (A.subst (hNoEq := language_noEq))
          ⟦ 15 ↦ nil ⟧)) :=
  FOSLDDerivation.step
    (prev := revSLDStep2)
    (clause := clauseRevBase)
    (hClause := by change _ ∈ revProgram; simp [revProgram])
    (hDef := by simp [clauseRevBase, fact, FOHornClause.isDefinite, FOHornClauseCore.isDefinite])
    (Ak := reverse nil (V 15))
    (headA := reverse nil nil)
    (hAk := by
      show reverse nil (V 15) ∈ step2Idx
      rw [step2Idx_eq, LCS.Finset.mem_ofList]; simp)
    (hHead := by simp [clauseRevBase, fact, FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom])
    (rho := Term.var)
    (sigma := ⟦ 15 ↦ nil ⟧)
    (hMGU := by
      apply isAtomMGU_toCore language_noEq
      -- REPAIR(CH9-ROOT): proof pending
      -- DEBT(most-general-unifier proof for the base reverse step missing)
      sorry)
    (hSep := by
      change IsSeparatingPair language_noEq _ _ _ _
      -- ρ₃ = Term.var (identity), FV(clauseRevBase) empty.
      have hCongr : (clauseFV (L := revLang) (hNoEq := language_noEq))
          (step2Idx.toList.map FOLiteralCore.neg) =
          (clauseFV (L := revLang) (hNoEq := language_noEq))
            ([reverse nil (V 15), append (V 15) ⟦b⟧ (V 11),
              append (V 11) ⟦a⟧ (V 100)].map FOLiteralCore.neg) := by
        apply (clauseFV_neg_congr_of_mem_iff (hNoEq := language_noEq))
        intro f
        rw [LCS.Finset.mem_toList]
        show f ∈ step2Idx ↔ _
        rw [step2Idx_eq, LCS.Finset.mem_ofList]
      unfold IsSeparatingPair
      rw [hCongr]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x _; exact ⟨x, rfl⟩
      · intro x _; exact ⟨x, rfl⟩
      · intro x y _ _ h; cases h; rfl
      · intro x y hx _ _
        exact absurd hx (clauseRevBase_FV_empty x)
      · funext n
        apply propext
        constructor
        · rintro ⟨_, ⟨x₂, hClause, _⟩⟩
          exact absurd hClause (clauseRevBase_FV_empty x₂)
        · intro h; exact absurd h id
      · intro _ _; rfl
      · intro _ _; rfl)


/-- Abbreviation: the current-goal Finset after step 3. -/
noncomputable abbrev step3Idx : LCS.Finset (FOAtom revLang language_noEq) :=
  (((step2Idx.erase (reverse nil (V 15))).union
    (LCS.Finset.ofList
      (clauseRevBase.bodyFOAtoms.map (fun A =>
        (A.subst (hNoEq := language_noEq)) Term.var)))
    ).image (fun A => (A.subst (hNoEq := language_noEq))
      ⟦ 15 ↦ nil ⟧))

theorem step3Idx_eq :
    step3Idx = LCS.Finset.ofList
      [append nil ⟦b⟧ (V 11), append (V 11) ⟦a⟧ (V 100)] := by
  -- BEGIN PROOF
  unfold step3Idx
  rw [step2Idx_eq]
  apply LCS.Finset.ext
  intro A
  rw [LCS.Finset.mem_image, LCS.Finset.mem_ofList]
  constructor
  · rintro ⟨B, hB, rfl⟩
    rw [LCS.Finset.mem_union] at hB
    rcases hB with herase | himg
    · rw [LCS.Finset.mem_erase, LCS.Finset.mem_ofList] at herase
      obtain ⟨hmem, hne⟩ := herase
      simp at hmem
      rcases hmem with rfl | rfl | rfl
      · exact absurd rfl hne
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        left
        simp [formulaSubstAll_append, termSubstAll_cons, termSubstAll_nil,
              termSubstAll_b, V, ovr, overrideSubst]
        rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        right
        simp [formulaSubstAll_append, termSubstAll_cons, termSubstAll_nil,
              termSubstAll_a, V, ovr, overrideSubst]
        rfl
    · rw [LCS.Finset.mem_ofList] at himg
      simp [clauseRevBase, fact, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal] at himg
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · refine ⟨append (V 15) ⟦b⟧ (V 11), ?_, ?_⟩
      · rw [LCS.Finset.mem_union]; left
        rw [LCS.Finset.mem_erase, LCS.Finset.mem_ofList]
        refine ⟨?_, ?_⟩
        · simp
        · intro h; have hp := (FOAtomCore.predN.inj h).1; cases hp
      · simp [formulaSubstAll_append, termSubstAll_cons, termSubstAll_nil,
              termSubstAll_b, V, ovr, overrideSubst]
        rfl
    · refine ⟨append (V 11) ⟦a⟧ (V 100), ?_, ?_⟩
      · rw [LCS.Finset.mem_union]; left
        rw [LCS.Finset.mem_erase, LCS.Finset.mem_ofList]
        refine ⟨?_, ?_⟩
        · simp
        · intro h; have hp := (FOAtomCore.predN.inj h).1; cases hp
      · simp [formulaSubstAll_append, termSubstAll_cons, termSubstAll_nil,
              termSubstAll_a, V, ovr, overrideSubst]
        rfl

/-- **Step 4** — close `append nil ⟦b⟧ (V 11)` with `clauseAppBase`.

    * ρ₄: X ↦ V 16 (rename the unique clauseAppBase variable).
    * σ₄: V 11 ↦ ⟦b⟧, V 16 ↦ ⟦b⟧.
    * New current goal: `[append ⟦b⟧ ⟦a⟧ (V 100)]`. -/
noncomputable def revSLDStep4 :
    (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ revProgram) [queryGoal]
      (((step3Idx.erase (append nil ⟦b⟧ (V 11))).union
        (LCS.Finset.ofList
          (clauseAppBase.bodyFOAtoms.map (fun A =>
            (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 16 ⟧)))
        ).image (fun A => (A.subst (hNoEq := language_noEq))
          ⟦ 11 ↦ ⟦b⟧ | 16 ↦ ⟦b⟧ ⟧)) :=
  FOSLDDerivation.step
    (prev := revSLDStep3)
    (clause := clauseAppBase)
    (hClause := by change _ ∈ revProgram; simp [revProgram])
    (hDef := by simp [clauseAppBase, fact, FOHornClause.isDefinite, FOHornClauseCore.isDefinite])
    (Ak := append nil ⟦b⟧ (V 11))
    (headA := append nil (V 0) (V 0))
    (hAk := by
      show append nil ⟦b⟧ (V 11) ∈ step3Idx
      rw [step3Idx_eq, LCS.Finset.mem_ofList]; simp)
    (hHead := by simp [clauseAppBase, fact, FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom])
    (rho := ⟦ 0 ↦ V 16 ⟧)
    (sigma := ⟦ 11 ↦ ⟦b⟧ | 16 ↦ ⟦b⟧ ⟧)
    (hMGU := by
      apply isAtomMGU_toCore language_noEq
      -- REPAIR(CH9-ROOT): proof pending
      -- DEBT(most-general-unifier proof for the first base append step missing)
      sorry)
    (hSep := by
      change IsSeparatingPair language_noEq _ _ _ _
      -- prevGoal (step3Idx) = [append nil ⟦b⟧ (V 11), append (V 11) ⟦a⟧ (V 100)]
      -- FV ⊆ {11, 100}; FV(clauseAppBase) = {0}
      have hCongr : (clauseFV (L := revLang) (hNoEq := language_noEq))
          (step3Idx.toList.map FOLiteralCore.neg) =
          (clauseFV (L := revLang) (hNoEq := language_noEq))
            ([append nil ⟦b⟧ (V 11), append (V 11) ⟦a⟧ (V 100)].map FOLiteralCore.neg) := by
        apply (clauseFV_neg_congr_of_mem_iff (hNoEq := language_noEq))
        intro f
        rw [LCS.Finset.mem_toList]
        show f ∈ step3Idx ↔ _
        rw [step3Idx_eq, LCS.Finset.mem_ofList]
      unfold IsSeparatingPair
      rw [hCongr]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x _; exact ⟨x, rfl⟩
      · intro x _
        rcases x with _ | n
        · exact ⟨16, rfl⟩
        · exact ⟨n + 1, rfl⟩
      · intro x y _ _ h; cases h; rfl
      · intro x y hx hy _
        have hx0 := clauseAppBase_FV_subset x hx
        have hy0 := clauseAppBase_FV_subset y hy
        rw [hx0, hy0]
      · funext n
        apply propext
        constructor
        · rintro ⟨⟨x₁, hPrev, hEq₁⟩, ⟨x₂, hClause, hEq₂⟩⟩
          have hx₁ : x₁ = 11 ∨ x₁ = 100 := by
            obtain ⟨lit, hMem, hV⟩ := hPrev
            simp at hMem
            rcases hMem with rfl | rfl
            · simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_append,
                         termVars_cons, termVars_b_iff, termVars_nil_iff,
                         termVars_V, or_self, or_false, false_or] at hV
              exact Or.inl hV
            · simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_append,
                         termVars_cons, termVars_a_iff, termVars_nil_iff,
                         termVars_V, or_self, or_false, false_or] at hV
              rcases hV with h | h
              · exact Or.inl h
              · exact Or.inr h
          have hx₂0 := clauseAppBase_FV_subset x₂ hClause
          subst hx₂0
          rcases hx₁ with rfl | rfl
          · have hn : n = 11 :=
              (Term.var.injEq (L := revLang) _ _).mp hEq₁ |>.symm
            subst hn
            simp [V, ovr, overrideSubst] at hEq₂
          · have hn : n = 100 :=
              (Term.var.injEq (L := revLang) _ _).mp hEq₁ |>.symm
            subst hn
            simp [V, ovr, overrideSubst] at hEq₂
        · intro h; exact absurd h id
      · intro _ _; rfl
      · intro x hx
        rcases x with _ | n
        · exfalso; exact hx clauseAppBase_FV_0
        · rfl)


/-- Abbreviation: the current-goal Finset after step 4. -/
noncomputable abbrev step4Idx : LCS.Finset (FOAtom revLang language_noEq) :=
  (((step3Idx.erase (append nil ⟦b⟧ (V 11))).union
    (LCS.Finset.ofList
      (clauseAppBase.bodyFOAtoms.map (fun A =>
        (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 16 ⟧)))
    ).image (fun A => (A.subst (hNoEq := language_noEq))
      ⟦ 11 ↦ ⟦b⟧ | 16 ↦ ⟦b⟧ ⟧))

theorem step4Idx_eq :
    step4Idx = LCS.Finset.ofList [append ⟦b⟧ ⟦a⟧ (V 100)] := by
  -- BEGIN PROOF
  unfold step4Idx
  rw [step3Idx_eq]
  apply LCS.Finset.ext
  intro A
  rw [LCS.Finset.mem_image, LCS.Finset.mem_ofList]
  constructor
  · rintro ⟨B, hB, rfl⟩
    rw [LCS.Finset.mem_union] at hB
    rcases hB with herase | himg
    · rw [LCS.Finset.mem_erase, LCS.Finset.mem_ofList] at herase
      obtain ⟨hmem, hne⟩ := herase
      simp at hmem
      rcases hmem with rfl | rfl
      · exact absurd rfl hne
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        simp [formulaSubstAll_append, termSubstAll_cons, termSubstAll_nil,
              termSubstAll_a, termSubstAll_b, V, ovr, overrideSubst]
        rfl
    · rw [LCS.Finset.mem_ofList] at himg
      simp [clauseAppBase, fact, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal] at himg
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl
    refine ⟨append (V 11) ⟦a⟧ (V 100), ?_, ?_⟩
    · rw [LCS.Finset.mem_union]; left
      rw [LCS.Finset.mem_erase, LCS.Finset.mem_ofList]
      refine ⟨?_, ?_⟩
      · simp
      · -- LHS has FV 100, RHS does not: distinguishes.
        intro h
        have h0 : FOAtomCore.vars (append (V 11) ⟦a⟧ (V 100)) 100 ↔
                  FOAtomCore.vars (append nil ⟦b⟧ (V 11)) 100 := by
          rw [h]
        have hlhs : FOAtomCore.vars (append (V 11) ⟦a⟧ (V 100)) 100 := by
          rw [formulaVars_append]; right; right; change termVars (V 100) 100; rfl
        have hrhs := h0.mp hlhs
        rw [formulaVars_append] at hrhs
        simp only [termVars_V, termVars_cons, termVars_a_iff, termVars_nil_iff,
                   termVars_b_iff, or_self, or_false, false_or] at hrhs
        omega
    · simp [formulaSubstAll_append, termSubstAll_cons, termSubstAll_nil,
            termSubstAll_a, termSubstAll_b, V, ovr, overrideSubst]
      rfl

/-- **Step 5** — resolve `append ⟦b⟧ ⟦a⟧ (V 100)` against `clauseAppRec`.

    * ρ₅: X,Xs,Y,Zs ↦ V 17..V 20.
    * σ₅: V 17 ↦ b, V 18 ↦ nil, V 19 ↦ ⟦a⟧, V 100 ↦ ⟦b | V 20⟧.
    * New current goal: `[append nil ⟦a⟧ (V 20)]`. -/
noncomputable def revSLDStep5 :
    (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ revProgram) [queryGoal]
      (((step4Idx.erase (append ⟦b⟧ ⟦a⟧ (V 100))).union
        (LCS.Finset.ofList
          (clauseAppRec.bodyFOAtoms.map (fun A =>
            (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 17 | 1 ↦ V 18 | 2 ↦ V 19 | 3 ↦ V 20 ⟧)))
        ).image (fun A => (A.subst (hNoEq := language_noEq))
          ⟦ 17 ↦ b | 18 ↦ nil | 19 ↦ ⟦a⟧ | 100 ↦ ⟦b | V 20⟧ ⟧)) :=
  FOSLDDerivation.step
    (prev := revSLDStep4)
    (clause := clauseAppRec)
    (hClause := by change _ ∈ revProgram; simp [revProgram])
    (hDef := by simp [clauseAppRec, rule, FOHornClause.isDefinite, FOHornClauseCore.isDefinite])
    (Ak := append ⟦b⟧ ⟦a⟧ (V 100))
    (headA := append ⟦V 0 | V 1⟧ (V 2) ⟦V 0 | V 3⟧)
    (hAk := by
      show append ⟦b⟧ ⟦a⟧ (V 100) ∈ step4Idx
      rw [step4Idx_eq, LCS.Finset.mem_ofList]; simp)
    (hHead := by simp [clauseAppRec, rule, FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom])
    (rho := ⟦ 0 ↦ V 17 | 1 ↦ V 18 | 2 ↦ V 19 | 3 ↦ V 20 ⟧)
    (sigma := ⟦ 17 ↦ b | 18 ↦ nil | 19 ↦ ⟦a⟧ | 100 ↦ ⟦b | V 20⟧ ⟧)
    (hMGU := by
      apply isAtomMGU_toCore language_noEq
      -- REPAIR(CH9-ROOT): proof pending
      -- DEBT(most-general-unifier proof for the recursive append step missing)
      sorry)
    (hSep := by
      change IsSeparatingPair language_noEq _ _ _ _
      have hCongr : (clauseFV (L := revLang) (hNoEq := language_noEq))
          (step4Idx.toList.map FOLiteralCore.neg) =
          (clauseFV (L := revLang) (hNoEq := language_noEq))
            ([append ⟦b⟧ ⟦a⟧ (V 100)].map FOLiteralCore.neg) := by
        apply (clauseFV_neg_congr_of_mem_iff (hNoEq := language_noEq))
        intro f
        rw [LCS.Finset.mem_toList]
        show f ∈ step4Idx ↔ _
        rw [step4Idx_eq, LCS.Finset.mem_ofList]
      unfold IsSeparatingPair
      rw [hCongr]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x _; exact ⟨x, rfl⟩
      · intro x _
        rcases x with _ | _ | _ | _ | n
        · exact ⟨17, rfl⟩
        · exact ⟨18, rfl⟩
        · exact ⟨19, rfl⟩
        · exact ⟨20, rfl⟩
        · exact ⟨n + 4, rfl⟩
      · intro x y _ _ h; cases h; rfl
      · intro x y hx hy h
        have hxmem := clauseAppRec_FV_subset x hx
        have hymem := clauseAppRec_FV_subset y hy
        match x, hxmem, y, hymem with
        | 0, _, 0, _ => rfl
        | 0, _, 1, _ => simp [V, ovr, overrideSubst] at h
        | 0, _, 2, _ => simp [V, ovr, overrideSubst] at h
        | 0, _, 3, _ => simp [V, ovr, overrideSubst] at h
        | 1, _, 0, _ => simp [V, ovr, overrideSubst] at h
        | 1, _, 1, _ => rfl
        | 1, _, 2, _ => simp [V, ovr, overrideSubst] at h
        | 1, _, 3, _ => simp [V, ovr, overrideSubst] at h
        | 2, _, 0, _ => simp [V, ovr, overrideSubst] at h
        | 2, _, 1, _ => simp [V, ovr, overrideSubst] at h
        | 2, _, 2, _ => rfl
        | 2, _, 3, _ => simp [V, ovr, overrideSubst] at h
        | 3, _, 0, _ => simp [V, ovr, overrideSubst] at h
        | 3, _, 1, _ => simp [V, ovr, overrideSubst] at h
        | 3, _, 2, _ => simp [V, ovr, overrideSubst] at h
        | 3, _, 3, _ => rfl
      · funext n
        apply propext
        constructor
        · rintro ⟨⟨x₁, hPrev, hEq₁⟩, ⟨x₂, hClause, hEq₂⟩⟩
          have hx₁100 : x₁ = 100 := by
            obtain ⟨lit, hMem, hV⟩ := hPrev
            simp at hMem
            subst hMem
            simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_append,
                       termVars_cons, termVars_a_iff, termVars_b_iff,
                       termVars_nil_iff, termVars_V,
                       or_self, or_false, false_or] at hV
            exact hV
          subst hx₁100
          have hn : n = 100 :=
            (Term.var.injEq (L := revLang) _ _).mp hEq₁ |>.symm
          subst hn
          have hx₂mem := clauseAppRec_FV_subset x₂ hClause
          match x₂, hx₂mem with
          | 0, _ => simp [V, ovr, overrideSubst] at hEq₂
          | 1, _ => simp [V, ovr, overrideSubst] at hEq₂
          | 2, _ => simp [V, ovr, overrideSubst] at hEq₂
          | 3, _ => simp [V, ovr, overrideSubst] at hEq₂
        · intro h; exact absurd h id
      · intro _ _; rfl
      · intro x hx
        rcases x with _ | _ | _ | _ | n
        · exfalso; exact hx clauseAppRec_FV_0
        · exfalso; exact hx clauseAppRec_FV_1
        · exfalso; exact hx clauseAppRec_FV_2
        · exfalso; exact hx clauseAppRec_FV_3
        · rfl)


/-- Abbreviation: the current-goal Finset after step 5. -/
noncomputable abbrev step5Idx : LCS.Finset (FOAtom revLang language_noEq) :=
  (((step4Idx.erase (append ⟦b⟧ ⟦a⟧ (V 100))).union
    (LCS.Finset.ofList
      (clauseAppRec.bodyFOAtoms.map (fun A =>
        (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 17 | 1 ↦ V 18 | 2 ↦ V 19 | 3 ↦ V 20 ⟧)))
    ).image (fun A => (A.subst (hNoEq := language_noEq))
      ⟦ 17 ↦ b | 18 ↦ nil | 19 ↦ ⟦a⟧ | 100 ↦ ⟦b | V 20⟧ ⟧))

theorem step5Idx_eq :
    step5Idx = LCS.Finset.ofList [append nil ⟦a⟧ (V 20)] := by
  -- BEGIN PROOF
  unfold step5Idx
  rw [step4Idx_eq]
  apply LCS.Finset.ext
  intro A
  rw [LCS.Finset.mem_image, LCS.Finset.mem_ofList]
  constructor
  · rintro ⟨B, hB, rfl⟩
    rw [LCS.Finset.mem_union] at hB
    rcases hB with herase | himg
    · rw [LCS.Finset.mem_erase, LCS.Finset.mem_ofList] at herase
      obtain ⟨hmem, hne⟩ := herase
      simp at hmem
      exact absurd hmem hne
    · rw [LCS.Finset.mem_ofList, List.mem_map] at himg
      obtain ⟨A', hA', rfl⟩ := himg
      simp [clauseAppRec, rule, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal] at hA'
      subst hA'
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      simp [formulaSubstAll_append, termSubstAll_cons, termSubstAll_nil,
            termSubstAll_a, termSubstAll_b, V, ovr, overrideSubst]
      rfl
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl
    refine ⟨append (V 18) (V 19) (V 20), ?_, ?_⟩
    · rw [LCS.Finset.mem_union]; right
      rw [LCS.Finset.mem_ofList, List.mem_map]
      refine ⟨append (V 1) (V 2) (V 3), ?_, ?_⟩
      · simp [clauseAppRec, rule, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal]
      · show _ = append (V 18) (V 19) (V 20)
        simp [formulaSubstAll_append, V, ovr, overrideSubst]
        rfl
    · simp [formulaSubstAll_append, termSubstAll_cons, termSubstAll_nil,
            termSubstAll_a, V, ovr, overrideSubst]
      rfl

/-- **Step 6** — close `append nil ⟦a⟧ (V 20)` with `clauseAppBase`.

    * ρ₆: X ↦ V 21.
    * σ₆: V 20 ↦ ⟦a⟧, V 21 ↦ ⟦a⟧.
    * New current goal: `∅` (refutation!). -/
noncomputable def revSLDRefutation :
    (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ revProgram) [queryGoal] (∅ : LCS.Finset (FOAtom revLang language_noEq)) := by
  have step6raw :
      (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ revProgram) [queryGoal]
        (((step5Idx.erase (append nil ⟦a⟧ (V 20))).union
          (LCS.Finset.ofList
            (clauseAppBase.bodyFOAtoms.map (fun A =>
              (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 21 ⟧)))
          ).image (fun A => (A.subst (hNoEq := language_noEq))
            ⟦ 20 ↦ ⟦a⟧ | 21 ↦ ⟦a⟧ ⟧)) :=
    FOSLDDerivation.step
      (prev := revSLDStep5)
      (clause := clauseAppBase)
      (hClause := by change _ ∈ revProgram; simp [revProgram])
      (hDef := by simp [clauseAppBase, fact, FOHornClause.isDefinite, FOHornClauseCore.isDefinite])
      (Ak := append nil ⟦a⟧ (V 20))
      (headA := append nil (V 0) (V 0))
      (hAk := by
        show append nil ⟦a⟧ (V 20) ∈ step5Idx
        rw [step5Idx_eq, LCS.Finset.mem_ofList]; simp)
      (hHead := by simp [clauseAppBase, fact, FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom])
      (rho := ⟦ 0 ↦ V 21 ⟧)
      (sigma := ⟦ 20 ↦ ⟦a⟧ | 21 ↦ ⟦a⟧ ⟧)
      (hMGU := by
        apply isAtomMGU_toCore language_noEq
        -- REPAIR(CH9-ROOT): proof pending
        -- DEBT(most-general-unifier proof for the final base append step missing)
        sorry)
      (hSep := by
        change IsSeparatingPair language_noEq _ _ _ _
        have hCongr : (clauseFV (L := revLang) (hNoEq := language_noEq))
            (step5Idx.toList.map FOLiteralCore.neg) =
            (clauseFV (L := revLang) (hNoEq := language_noEq))
              ([append nil ⟦a⟧ (V 20)].map FOLiteralCore.neg) := by
          apply (clauseFV_neg_congr_of_mem_iff (hNoEq := language_noEq))
          intro f
          rw [LCS.Finset.mem_toList]
          show f ∈ step5Idx ↔ _
          rw [step5Idx_eq, LCS.Finset.mem_ofList]
        unfold IsSeparatingPair
        rw [hCongr]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro x _; exact ⟨x, rfl⟩
        · intro x _
          rcases x with _ | n
          · exact ⟨21, rfl⟩
          · exact ⟨n + 1, rfl⟩
        · intro x y _ _ h; cases h; rfl
        · intro x y hx hy _
          have hx0 := clauseAppBase_FV_subset x hx
          have hy0 := clauseAppBase_FV_subset y hy
          rw [hx0, hy0]
        · funext n
          apply propext
          constructor
          · rintro ⟨⟨x₁, hPrev, hEq₁⟩, ⟨x₂, hClause, hEq₂⟩⟩
            have hx₁20 : x₁ = 20 := by
              obtain ⟨lit, hMem, hV⟩ := hPrev
              simp at hMem
              subst hMem
              simp only [FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula, formulaVars_append,
                         termVars_cons, termVars_a_iff, termVars_nil_iff,
                         termVars_V, or_self, or_false, false_or] at hV
              exact hV
            subst hx₁20
            have hn : n = 20 :=
              (Term.var.injEq (L := revLang) _ _).mp hEq₁ |>.symm
            subst hn
            have hx₂0 := clauseAppBase_FV_subset x₂ hClause
            subst hx₂0
            simp [V, ovr, overrideSubst] at hEq₂
          · intro h; exact absurd h id
        · intro _ _; rfl
        · intro x hx
          rcases x with _ | n
          · exfalso; exact hx clauseAppBase_FV_0
          · rfl)

  -- Reduce the output Finset to ∅.
  have hIdx :
      (((step5Idx.erase (append nil ⟦a⟧ (V 20))).union
        (LCS.Finset.ofList
          (clauseAppBase.bodyFOAtoms.map (fun A =>
            (A.subst (hNoEq := language_noEq)) ⟦ 0 ↦ V 21 ⟧)))
        ).image (fun A => (A.subst (hNoEq := language_noEq))
          ⟦ 20 ↦ ⟦a⟧ | 21 ↦ ⟦a⟧ ⟧)) =
      (∅ : LCS.Finset (FOAtom revLang language_noEq)) := by
    apply LCS.Finset.ext
    intro A
    rw [LCS.Finset.mem_image]
    constructor
    · rintro ⟨B, hB, _⟩
      rw [LCS.Finset.mem_union] at hB
      rcases hB with herase | himg
      · rw [LCS.Finset.mem_erase, step5Idx_eq, LCS.Finset.mem_ofList] at herase
        obtain ⟨hmem, hne⟩ := herase
        simp at hmem
        exact absurd hmem hne
      · rw [LCS.Finset.mem_ofList, List.mem_map] at himg
        obtain ⟨x, hx, _⟩ := himg
        simp [clauseAppBase, fact, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, FOHornClause.fact, FOHornClause.rule, FOHornClause.goal, LCS.Finset.mem_toList, LCS.Finset.mem_ofList, finset_toList_empty, finset_toList_singleton, AtomicQuery.toGoal] at hx
    · intro h
      exact absurd h LCS.Finset.not_mem_empty
  exact hIdx ▸ step6raw

-- ===================================================================
-- §9.  Refutation-existence theorem
-- ===================================================================

/-- **The full refutation exists** — witnessed by the 6-step chain
    `revSLDRefutation`.

    The 6 resolution steps:
    1. reverse-rec on `reverse([a,b], R)`.
    2. reverse-rec on `reverse([b], V 11)`.
    3. reverse-base on `reverse([], V 15)`.
    4. append-base on `append([], [b], V 11)`.
    5. append-rec on `append([b], [a], V 100)`.
    6. append-base on `append([], [a], V 20)` → `[]`. -/
theorem revRefutation_exists :
    ∃ (cg : LCS.Finset (FOAtom revLang language_noEq))
      (R : (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ revProgram) [queryGoal] cg),
      (FOSLDDerivation.isRefutation (hNoEq := language_noEq)) R :=
  -- BEGIN PROOF
  ⟨(∅ : LCS.Finset (FOAtom revLang language_noEq)), revSLDRefutation, rfl⟩

-- ===================================================================
-- §9b.  Answer extraction:  R ↦ [b, a]
-- ===================================================================

/-- The Prolog answer substitution, composing σᵢ ∘ ρᵢ across 6 steps. -/
noncomputable def revAnswerSubst : Nat → Term revLang :=
  (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) revSLDRefutation

/-- Transport lemma: `resultSubstitution` is invariant under the Finset
    type-index rewrite used to wrap `.step` outputs. -/
theorem revResultSubstitution_cast
    {idx1 idx2 : LCS.Finset (FOAtom revLang language_noEq)} (hIdx : idx1 = idx2)
    (d : (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ revProgram) [queryGoal] idx1) :
    (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) (hIdx ▸ d) =
    (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) d := by
  subst hIdx; rfl

/-- `resultSubstitution` of `initNode` is `Term.var`. -/
theorem initNode_resultSubstitution :
    (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) initNode = Term.var := by
  unfold initNode
  erw [revResultSubstitution_cast]
  rfl

/-- Composed substitution of step 1 symbolically. -/
theorem revSLDStep1_resultSubstitution :
    (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) revSLDStep1 =
      SubstitutionCore.substCompose (SubstitutionCore.substCompose
        ⟦ 8 ↦ a | 9 ↦ ⟦b⟧ | 10 ↦ V 100 ⟧
        ⟦ 4 ↦ V 8 | 5 ↦ V 9 | 6 ↦ V 10 | 7 ↦ V 11 ⟧)
        Term.var := by
  unfold revSLDStep1
  show (SubstitutionCore.substCompose (SubstitutionCore.substCompose _ _)
        ((FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) initNode)) = _
  rw [initNode_resultSubstitution]

/-- Composed substitution of step 2 symbolically. -/
theorem revSLDStep2_resultSubstitution :
    (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) revSLDStep2 =
      SubstitutionCore.substCompose (SubstitutionCore.substCompose
        ⟦ 12 ↦ b | 13 ↦ nil | 14 ↦ V 11 ⟧
        ⟦ 4 ↦ V 12 | 5 ↦ V 13 | 6 ↦ V 14 | 7 ↦ V 15 ⟧)
        ((FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) revSLDStep1) := by
  rfl

/-- Composed substitution of step 3 symbolically. -/
theorem revSLDStep3_resultSubstitution :
    (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) revSLDStep3 =
      SubstitutionCore.substCompose (SubstitutionCore.substCompose ⟦ 15 ↦ nil ⟧ Term.var)
        ((FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) revSLDStep2) := by
  unfold revSLDStep3
  rfl

/-- Composed substitution of step 4 symbolically. -/
theorem revSLDStep4_resultSubstitution :
    (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) revSLDStep4 =
      SubstitutionCore.substCompose (SubstitutionCore.substCompose
        ⟦ 11 ↦ ⟦b⟧ | 16 ↦ ⟦b⟧ ⟧
        ⟦ 0 ↦ V 16 ⟧)
        ((FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) revSLDStep3) := by
  unfold revSLDStep4
  rfl

/-- Composed substitution of step 5 symbolically. -/
theorem revSLDStep5_resultSubstitution :
    (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) revSLDStep5 =
      SubstitutionCore.substCompose (SubstitutionCore.substCompose
        ⟦ 17 ↦ b | 18 ↦ nil | 19 ↦ ⟦a⟧ | 100 ↦ ⟦b | V 20⟧ ⟧
        ⟦ 0 ↦ V 17 | 1 ↦ V 18 | 2 ↦ V 19 | 3 ↦ V 20 ⟧)
        ((FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) revSLDStep4) := by
  unfold revSLDStep5
  rfl

/-- Machine-checked: the 6-step derivation's composed substitution
    sends `R = V 100` to `[b, a]`. -/
theorem revAnswer_eq :
    revAnswerSubst 100 = revAnswerValue := by
  unfold revAnswerSubst revAnswerValue revSLDRefutation
  erw [revResultSubstitution_cast]
  show SubstitutionCore.substCompose (SubstitutionCore.substCompose ⟦ 20 ↦ ⟦a⟧ | 21 ↦ ⟦a⟧ ⟧ ⟦ 0 ↦ V 21 ⟧)
      ((FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) revSLDStep5) 100 = ⟦b, a⟧
  rw [revSLDStep5_resultSubstitution, revSLDStep4_resultSubstitution,
      revSLDStep3_resultSubstitution, revSLDStep2_resultSubstitution,
      revSLDStep1_resultSubstitution]
  simp [SubstitutionCore.substCompose, LCS.FOResolution.Unification.termSubstAll,
        ovr, overrideSubst, idSubst, V, cons, nil, a, b]
  congr 1
  funext ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl

-- ===================================================================
-- §10.  Showcase: the final claim stated directly in Prolog syntax
-- ===================================================================

/-- A placeholder falsum formula over `revLang` — any closed atom
    serves; its only role is to stand in for `⊥` in `clauseToFormula`. -/
def revFalsum : FormulaN revLang :=
  (reverse nil nil).toFormula

/-- `revSLDRefutation`'s final current goal is `∅` — by definition. -/
theorem revSLDRefutation_isRefutation :
    (FOSLDDerivation.isRefutation (hNoEq := language_noEq)) revSLDRefutation :=
  rfl

/-- **Showcase theorem** — the full Prolog-level claim, stated with
    program and query inlined as Prolog syntax.

    Given the program
    ```prolog
    append([], L, L).
    append([X | Xs], Y, [X | Zs]) :- append(Xs, Y, Zs).
    reverse([], []).
    reverse([H | T], R) :- reverse(T, Rt), append(Rt, [H], R).
    ```
    and the query
    ```prolog
    ?- reverse([a, b], R).
    ```
    there exists an SLD-refutation `D` such that:

    **(1) Syntactic — Prolog's answer.** The composed substitution
    sends the query variable `R` to `[b, a]`.

    **(2) Semantic — Theorem 9.5.1.** Every first-order structure
    that models the program satisfies `reverse([a, b], [b, a])`
    at every assignment. -/
example :
    -- Program:  2 append clauses + 2 reverse clauses.
    let program : List (FOHornClause revLang language_noEq) :=
      [ (fact (hNoEq := language_noEq)) append(⟦⟧, V 0, V 0),
        (append(⟦V 0 | V 1⟧, V 2, ⟦V 0 | V 3⟧) :- append(V 1, V 2, V 3)),
        (fact (hNoEq := language_noEq)) reverse(⟦⟧, ⟦⟧),
        (reverse(⟦H | T⟧, R') :- reverse(T, Rt), append(Rt, ⟦H⟧, R')) ]
    -- Query:  ?- reverse([a, b], R).
    let query : FOHornClause revLang language_noEq :=
      (?- reverse(⟦a, b⟧, R)).toGoal
    -- Answer:  R ↦ [b, a].
    let answer : Term revLang := ⟦b, a⟧
    ∃ D : (FOSLDDerivation (hNoEq := language_noEq)) (fun c => c ∈ program) [query] ∅,
      -- (1) Prolog answer:  the composed substitution sends R → answer.
      (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) D 100 = answer ∧
      -- (2) Semantic entailment:  ∀ M ⊨ program, M ⊨ reverse([a, b], answer).
      (∀ (M : Structure revLang),
        (∀ c ∈ program,
          ∀ (s : Assignment M),
            formulaEvalN M ((clauseToFormula (hNoEq := language_noEq)) revFalsum (c.toFOClause (hNoEq := language_noEq))) s) →
        ∀ (s : Assignment M),
          formulaEvalN M (reverse(⟦a, b⟧, answer)).toFormula s) := by
  refine ⟨revSLDRefutation, revAnswer_eq, ?_⟩
  intro M hProgSat s
  have hInitVar : substitutedClauseSet.getInitSigma language_noEq revSLDRefutation = Term.var := by
    exact getInitSigma_eq_id language_noEq revSLDRefutation
  have h := (sldAnswer_entails (Afalsum := revFalsum) (hNoEq := language_noEq)) (P := revProgram)
    (queryAtom := reverse(⟦a, b⟧, R)) (R := revSLDRefutation)
    (hRef := revSLDRefutation_isRefutation)
    (hInitVar := hInitVar)
    M hProgSat s
  -- Push formulaSubstAll through; the only non-ground term is R = V 100,
  -- so σ R = σ 100 = ⟦b, a⟧ by `revAnswer_eq`.
  rw [← atomSubst_toFormula_formulaSubstAll] at h
  simp only [formulaSubstAll_reverse, termSubstAll_cons, termSubstAll_nil,
             termSubstAll_a, termSubstAll_b] at h
  change formulaEvalN M (reverse(⟦a, b⟧,
    (FOSLDDerivation.resultSubstitution (hNoEq := language_noEq)) revSLDRefutation 100)).toFormula s at h
  rw [show FOSLDDerivation.resultSubstitution language_noEq revSLDRefutation 100 = ⟦b, a⟧
      from revAnswer_eq] at h
  exact h

-- ===================================================================
-- Sanity-check smoke tests
-- ===================================================================

/-- Program size is 4 clauses: 2 for append + 2 for reverse. -/
example : revProgram.length = 4 := rfl

/-- Query is a single-atom goal. -/
example : queryGoal.bodyFOAtoms.length = 1 := by
  simp [queryGoal, goal, AtomicQuery.toGoal, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body]

/-- The goal atom is literally `reverse([a, b], R)`. -/
example : queryGoal.bodyFOAtoms.head? = some (reverse ⟦a, b⟧ R) := by
  simp [queryGoal, goal, AtomicQuery.toGoal, FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body]

/-- The two predicates in the language. -/
example : (revLang.predArity RevPred.append, revLang.predArity RevPred.reverse)
        = (3, 2) := rfl

end LCS.Examples.PrologReverse
end

