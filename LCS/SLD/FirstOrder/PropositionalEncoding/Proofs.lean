import LCS.SLD.FirstOrder.PropositionalEncoding

section

namespace LCS.SLD.FirstOrder

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SemanticsN

open LCS.FOResolution.ClauseForm

open LCS.FOResolution.Unification

open LCS.FOResolution.Method

open LCS.FOResolution.Method.Soundness

open LCS.FOResolution.Method.Completeness

proof_of unsat_transfer_dg_goals_via_cinstance := by
  -- BEGIN PROOF
    -- Step 1: Produce the witnesses D_g and goals_g INTERNALLY via
    -- `extractGroundClauses_from_cinstance` and `extractGroundGoals_from_cinstance`.
    obtain ⟨D_g, hDGEq, hDGInst⟩ :=
      (extractGroundClauses_from_cinstance (hNoEq := by all_goals exact hNoEq)) Afalsum hAfalsumAtomic D goals
        hAllNe spec hSpec ci hCiSrc hCiWF
    obtain ⟨goals_g, hGGEq, hGGInst⟩ :=
      (extractGroundGoals_from_cinstance (hNoEq := by all_goals exact hNoEq)) Afalsum hAfalsumAtomic D goals
        hAllNe spec hSpec ci hCiSrc hCiWF
    -- Step 2: `goals_g ≠ []` follows from `goals ≠ []` since
    -- `extractGroundGoalsFromCInstance_core` produces a non-empty flatten
    -- whenever `goals` is non-empty (see `extractGroundGoalsFromCInstance_core_ne_nil`).
    have hGoalsGNe : goals_g ≠ [] := by
      rw [hGGEq]
      exact (extractGroundGoalsFromCInstance_core_ne_nil (hNoEq := by all_goals exact hNoEq))
        Afalsum D goals spec ci hGoalsNe
    -- Step 3: `D_g ++ goals_g ≠ []` follows from `goals_g ≠ []` trivially.
    have hDGGoalsGNe : D_g ++ goals_g ≠ [] := by
      intro hEmpty
      exact hGoalsGNe (List.append_eq_nil_iff.mp hEmpty).2
    refine ⟨D_g, goals_g, hDGGoalsGNe, hDGInst, hGGInst, hGoalsGNe, ?_⟩
    -- Step 4: `FOHornClauseSet.isUnsatisfiable Afalsum (D_g ++ goals_g)`.
    -- Any model of `hornClauses_to_formulaN Afalsum (D_g ++ goals_g)` gives
    -- rise to a model of `ci.toFormula` under the trivial expansion,
    -- contradicting `hCUnsat`.
    rw [← (satisfiableN_hornClauseSet_iff (hNoEq := by all_goals exact hNoEq)) _ _ hDGGoalsGNe]
    intro hSat
    apply hCUnsat
    obtain ⟨M, s, hM⟩ := hSat
    -- Rewrite hM using hDGEq + hGGEq so it directly refers to the extract-core forms.
    rw [hDGEq, hGGEq] at hM
    -- Build the trivial expansion N : Structure spec.language with the
    -- same carrier as M, agreeing with M on all L-symbols.
    let N := spec_trivial_expansion spec M
    have hExp : LCS.Herbrand.SHGTheorem.Main.isExpansion L spec.n spec.skolemRank M N :=
      spec_trivial_expansion_isExpansion spec M
    have heq : M.carrier = N.carrier := hExp.1
    let sN : Assignment N := fun x => (heq ▸ s x : N.carrier)
    refine ⟨N, sN, ?_⟩
    -- Step 5: Decompose `ci.toFormula`'s evaluation along the conj-chain
    -- of `ci.source`. Use `ci_toFormula_eval_via_conj_chain` to reduce to
    -- per-clause sub-goals, one per element of `D ++ goals`.
    -- Per-clause case-split: dispatch to either D-helper or goals-helper.
    have hChain : isConjChainN ci.source ((D ++ goals).length) :=
      hCiSrc ▸ (SK_isConjChainN_from_source (hNoEq := by all_goals exact hNoEq)) spec (D ++ goals) Afalsum hSpec
    have hDgGoalsLen : ((D ++ goals).length) > 0 := by
      cases hLen : ((D ++ goals).length) with
      | zero =>
        exfalso
        have : D ++ goals = [] := List.length_eq_zero_iff.mp hLen
        exact hAllNe this
      | succ _ => omega
    refine ci_toFormula_eval_via_conj_chain N sN ((D ++ goals).length) ci hCiWF hChain
      ?_ hDgGoalsLen
    intro i hi subCi hProj
    by_cases hiD : i < D.length
    · -- D-case (i < D.length).
      exact (ci_subtree_eval_at_D_index (hNoEq := by all_goals exact hNoEq)) Afalsum hAfalsumAtomic D goals
        hAllNe spec hSpec ci hCiSrc hCiWF M s hM N hExp i hiD
        subCi hProj
    · -- goals-case (i ≥ D.length).
      have hiGE : D.length ≤ i := Nat.le_of_not_lt hiD
      exact (ci_subtree_eval_at_goals_index (hNoEq := by all_goals exact hNoEq)) Afalsum hAfalsumAtomic D goals
        hAllNe spec hSpec ci hCiSrc hCiWF M s hM N hExp i hi hiGE
        subCi hProj


proof_of groundAtomEncode_injective := by
  -- BEGIN PROOF
    unfold groundAtomEncode at hEq
    induction atoms with
    | nil => simp at ha
    | cons x xs ih =>
      have hxxs : x ∉ xs := (List.nodup_cons.mp hNodup).1
      have hNodupTail : xs.Nodup := (List.nodup_cons.mp hNodup).2
      simp only [List.mem_cons] at ha hb
      rw [List.idxOf_cons, List.idxOf_cons] at hEq
      simp only [Bool.cond_eq_ite, beq_iff_eq] at hEq
      by_cases hax : x = a
      · by_cases hbx : x = b
        · rw [← hax, hbx]
        · rw [if_pos hax, if_neg hbx] at hEq
          omega
      · by_cases hbx : x = b
        · rw [if_neg hax, if_pos hbx] at hEq
          omega
        · rw [if_neg hax, if_neg hbx] at hEq
          have hidx : xs.idxOf a = xs.idxOf b := by omega
          have ha' : a ∈ xs := by
            rcases ha with h | h
            · exact absurd h.symm hax
            · exact h
          have hb' : b ∈ xs := by
            rcases hb with h | h
            · exact absurd h.symm hbx
            · exact h
          exact ih hNodupTail ha' hb' hidx


proof_of groundAtomsOf_mem := by
  -- BEGIN PROOF
    unfold groundAtomsOf
    rw [List.mem_eraseDups, List.mem_flatMap]
    refine ⟨c, hc, ?_⟩
    exact List.mem_map_of_mem hlit


proof_of groundAtomsOf_nodup := by
  -- BEGIN PROOF
    unfold groundAtomsOf
    let atoms := S.flatMap (fun c => c.toFOClause.map (FOLiteral.foAtom (hNoEq := by all_goals exact hNoEq)))
    show atoms.eraseDups.Nodup
    suffices h : ∀ (n : Nat) (l : List (FOAtom L hNoEq)),
        l.length ≤ n → l.eraseDups.Nodup by
      exact h atoms.length atoms (Nat.le_refl _)
    intro n
    induction n with
    | zero =>
      intro l hLen
      cases l with
      | nil => exact List.nodup_nil
      | cons _ _ => simp at hLen
    | succ k ih =>
      intro l hLen
      cases l with
      | nil => exact List.nodup_nil
      | cons hd tl =>
        rw [List.eraseDups_cons]
        apply List.nodup_cons.mpr
        refine ⟨?_, ?_⟩
        · rw [List.mem_eraseDups, List.mem_filter]
          intro ⟨_, hne⟩
          simp at hne
        · apply ih
          have hsucc : tl.length ≤ k := by
            have : tl.length + 1 ≤ k + 1 := by simpa using hLen
            omega
          calc ((List.filter _ tl).length) ≤ tl.length := List.length_filter_le _ _
            _ ≤ k := hsucc


proof_of foHornClauseToPropClause_isHornClause := by
  -- DEBT(FIX435): the empty goal translates to a non-ordinary empty clause.
  -- REPAIR(FIX435): proof pending
  sorry


proof_of foHornClauseToPropClause_isDefinite := by
  -- BEGIN PROOF
    refine ⟨(foHornClauseToPropClause_isHornClause (hNoEq := by all_goals exact hNoEq)) atoms hNodup c hMembers, ?_⟩
    cases c with
    | rule head body =>
      refine ⟨(groundAtomEncode (hNoEq := by all_goals exact hNoEq)) head atoms, ?_⟩
      unfold foHornClauseToPropClause LCS.Resolution.GCNF.Clause.ofList
      rw [LCS.Finset.mem_ofList, List.mem_map]
      refine ⟨FOLiteralCore.pos head, ?_, ?_⟩
      · rw [FOHornClause.toFOClause, FOHornClauseCore.toFOClause]
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      · simp only [foLiteralToPropLiteral]
    | fact head =>
      refine ⟨(groundAtomEncode (hNoEq := by all_goals exact hNoEq)) head atoms, ?_⟩
      unfold foHornClauseToPropClause LCS.Resolution.GCNF.Clause.ofList
      rw [LCS.Finset.mem_ofList, List.mem_map]
      refine ⟨FOLiteralCore.pos head, ?_, ?_⟩
      · rw [FOHornClause.toFOClause, FOHornClauseCore.toFOClause]; exact List.mem_singleton.mpr rfl
      · simp only [foLiteralToPropLiteral]
    | goal body =>
      exact absurd hDef (by simp [FOHornClause.isDefinite, FOHornClauseCore.isDefinite])


proof_of foHornClauseToPropClause_isGoal := by
  -- BEGIN PROOF
    refine ⟨(foHornClauseToPropClause_isHornClause (hNoEq := by all_goals exact hNoEq)) atoms hNodup c hMembers, ?_⟩
    cases c with
    | rule head body =>
      exact absurd
        (show (FOHornClause.isDefinite (hNoEq := by all_goals exact hNoEq)) (FOHornClause.rule (hNoEq := by all_goals exact hNoEq) head body) by
          simp [FOHornClause.isDefinite, FOHornClauseCore.isDefinite])
        hGoal
    | fact head =>
      exact absurd
        (show (FOHornClause.isDefinite (hNoEq := by all_goals exact hNoEq)) (FOHornClause.fact (hNoEq := by all_goals exact hNoEq) head) by
          simp [FOHornClause.isDefinite, FOHornClauseCore.isDefinite])
        hGoal
    | goal body =>
      intro l hl
      unfold foHornClauseToPropClause LCS.Resolution.GCNF.Clause.ofList at hl
      rw [LCS.Finset.mem_ofList, List.mem_map] at hl
      obtain ⟨lit, hlitMem, hlitEq⟩ := hl
      cases lit with
      | pos a =>
        rw [FOHornClause.toFOClause, FOHornClauseCore.toFOClause, List.mem_map] at hlitMem
        obtain ⟨_, _, h⟩ := hlitMem
        cases h
      | neg a =>
        simp only [foLiteralToPropLiteral] at hlitEq
        subst hlitEq
        trivial


proof_of foHornClausesToPropSequent_isHorn := by
  -- BEGIN PROOF
    intro C hC
    unfold foHornClausesToPropSequent at hC
    rw [LCS.Finset.mem_ofList, List.mem_map] at hC
    obtain ⟨c, hcMem, hcEq⟩ := hC
    subst hcEq
    exact (foHornClauseToPropClause_isHornClause (hNoEq := by all_goals exact hNoEq)) atoms hNodup c (hMembers c hcMem)


proof_of termEval_propValToFOStructure_ground_id := by
  -- BEGIN PROOF
    induction t with
    | var n =>
      exfalso
      apply hGround n
      simp [termVars]
    | const c => rfl
    | func f args ih =>
      simp only [termEval]
      show Term.func f _ = Term.func f _
      congr 1
      funext i
      apply ih i
      intro x hx
      apply hGround x
      exact ⟨i, hx⟩


proof_of formulaEvalN_propValToFOStructure_groundAtom_iff := by
  -- BEGIN PROOF
    have hArgsEq : (fun i => termEval ((propValToFOStructure (hNoEq := by all_goals exact hNoEq)) v atoms) s (args i)) = args := by
      funext i
      exact (termEval_propValToFOStructure_ground_id (hNoEq := by all_goals exact hNoEq)) v atoms s (args i) (hGround i)
    show ((propValToFOStructure (hNoEq := by all_goals exact hNoEq)) v atoms).interpPred P _ ↔ _
    rw [hArgsEq]
    rfl


proof_of termFV_iff_termVars := by
  -- BEGIN PROOF
    induction t with
    | var n => simp [termFV, termVars, Set.singleton]
    | const c => simp only [termFV, termVars, Set.empty]
    | func f args ih =>
      simp only [termFV, termVars, Set.iUnion]
      constructor
      · rintro ⟨i, hi⟩; exact ⟨i, (ih i).mp hi⟩
      · rintro ⟨i, hi⟩; exact ⟨i, (ih i).mpr hi⟩


proof_of formulaFVN_iff_formulaVars_of_atomic := open LCS.FirstOrder.SyntaxN.Variables in
  by
  -- BEGIN PROOF
    cases A with
    | predN P ts =>
      simp only [formulaFVN, formulaVars, Set.iUnion]
      constructor
      · rintro ⟨i, hi⟩; exact ⟨i, (termFV_iff_termVars _ _).mp hi⟩
      · rintro ⟨i, hi⟩; exact ⟨i, (termFV_iff_termVars _ _).mpr hi⟩
    | eq_ _ t1 t2 =>
      simp only [formulaFVN, formulaVars, Set.union]
      constructor
      · rintro (h | h)
        · exact Or.inl ((termFV_iff_termVars _ _).mp h)
        · exact Or.inr ((termFV_iff_termVars _ _).mp h)
      · rintro (h | h)
        · exact Or.inl ((termFV_iff_termVars _ _).mpr h)
        · exact Or.inr ((termFV_iff_termVars _ _).mpr h)
    | _ => simp [FormulaN.isAtomic] at hAtomic


proof_of isAtomic_noEq_predN := by
  -- BEGIN PROOF
    cases A with
    | predN P args => exact ⟨P, args, rfl⟩
    | eq_ hL _ _ =>
      rw [Language.withoutEquality] at hNoEq
      rw [hNoEq] at hL
      exact Bool.noConfusion hL
    | _ => simp [FormulaN.isAtomic] at hAtomic


proof_of isGroundAtom_of_atomic_noEq_noVars := by
  -- BEGIN PROOF
    cases A with
    | predN P args =>
      refine ⟨P, args, rfl, ?_⟩
      intro i x hVar
      exact hNoVars x ⟨i, hVar⟩
    | eq_ hL _ _ =>
      rw [Language.withoutEquality] at hNoEq
      rw [hNoEq] at hL
      exact Bool.noConfusion hL


proof_of Clause_satisfiedBy_cons := by
  -- BEGIN PROOF
    unfold LCS.Resolution.GCNF.Clause.satisfiedBy LCS.Resolution.GCNF.Clause.ofList
    simp only [LCS.Finset.mem_ofList, List.mem_cons]
    constructor
    · rintro ⟨Lit, hMem | hT, hSat⟩
      · subst hMem; exact Or.inl hSat
      · exact Or.inr ⟨Lit, hT, hSat⟩
    · rintro (hL | ⟨Lit, hT, hSat⟩)
      · exact ⟨L, Or.inl rfl, hL⟩
      · exact ⟨Lit, Or.inr hT, hSat⟩


proof_of litToFormulaEvalN_propValToFOStructure_iff := by
  -- BEGIN PROOF
    obtain ⟨P, args, hEq, hGr⟩ := hGround
    cases lit with
    | pos A =>
      simp only [FOLiteral.foAtom] at hEq
      subst A
      simp only [clauseToFormula.litToFormula, foLiteralToPropLiteral,
        LCS.Resolution.GCNF.Literal.satisfiedBy]
      exact (formulaEvalN_propValToFOStructure_groundAtom_iff (hNoEq := by all_goals exact hNoEq)) v atoms s P args hGr
    | neg A =>
      simp only [FOLiteral.foAtom] at hEq
      subst A
      simp only [clauseToFormula.litToFormula, foLiteralToPropLiteral,
        LCS.Resolution.GCNF.Literal.satisfiedBy]
      have hEval := (formulaEvalN_propValToFOStructure_groundAtom_iff (hNoEq := by all_goals exact hNoEq)) v atoms s P args hGr
      change (¬ formulaEvalN ((propValToFOStructure (hNoEq := by all_goals exact hNoEq)) v atoms)
        (FormulaN.predN P args) s) ↔
          v ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) (FOAtomCore.predN P args) atoms) = false
      constructor
      · intro hNeg
        cases h : v ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) (FOAtomCore.predN P args) atoms) with
        | true => exact absurd (hEval.mpr h) hNeg
        | false => rfl
      · intro hF hT
        have hvT : v _ = true := hEval.mp hT
        rw [hF] at hvT
        exact Bool.noConfusion hvT


proof_of clauseToFormulaEvalN_propValToFOStructure_iff := by
  -- BEGIN PROOF
    induction C with
    | nil =>
      simp only [clauseToFormula, FormulaN.falsum, formulaEvalN, List.map]
      constructor
      · intro ⟨hA, hNegA⟩; exact absurd hA hNegA
      · intro hSat
        unfold LCS.Resolution.GCNF.Clause.satisfiedBy
          LCS.Resolution.GCNF.Clause.ofList at hSat
        obtain ⟨Lit, hLit, _⟩ := hSat
        rw [LCS.Finset.mem_ofList] at hLit
        exact absurd hLit List.not_mem_nil
    | cons hd tl ih =>
      cases tl with
      | nil =>
        simp only [clauseToFormula, List.map]
        rw [(litToFormulaEvalN_propValToFOStructure_iff (hNoEq := by all_goals exact hNoEq)) v atoms s hd
          (hGround hd List.mem_cons_self)]
        rw [Clause_satisfiedBy_cons]
        constructor
        · intro h; exact Or.inl h
        · rintro (h | h)
          · exact h
          · unfold LCS.Resolution.GCNF.Clause.satisfiedBy
              LCS.Resolution.GCNF.Clause.ofList at h
            obtain ⟨L', hL', _⟩ := h
            rw [LCS.Finset.mem_ofList] at hL'
            exact absurd hL' List.not_mem_nil
      | cons hd2 tl2 =>
        simp only [clauseToFormula, formulaEvalN]
        have hHd := (litToFormulaEvalN_propValToFOStructure_iff (hNoEq := by all_goals exact hNoEq)) v atoms s hd
          (hGround hd List.mem_cons_self)
        have hGroundTl : ∀ lit ∈ hd2 :: tl2,
            (IsGroundAtom (hNoEq := by all_goals exact hNoEq)) ((FOLiteral.foAtom (hNoEq := by all_goals exact hNoEq)) lit) :=
          fun lit hl => hGround lit (List.mem_cons_of_mem _ hl)
        have hRec := ih hGroundTl
        show (LCS.FirstOrder.Basic.orM _ _ s) ↔ _
        unfold LCS.FirstOrder.Basic.orM
        rw [hHd, hRec]
        rw [show (hd :: hd2 :: tl2).map ((foLiteralToPropLiteral (hNoEq := by all_goals exact hNoEq)) atoms) =
            (foLiteralToPropLiteral (hNoEq := by all_goals exact hNoEq)) atoms hd :: (hd2 :: tl2).map ((foLiteralToPropLiteral (hNoEq := by all_goals exact hNoEq)) atoms)
          from rfl]
        rw [Clause_satisfiedBy_cons]


proof_of groundUnsatToPropProvable := by
  -- REPAIR(T9-77a): proof pending — migration to extensional bodies / renamed-head steps
  sorry

proof_of groundAtomDecode_encode := by
  -- BEGIN PROOF
    unfold groundAtomDecode groundAtomEncode
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr ha)]
    congr 1
    induction atoms with
    | nil => cases ha
    | cons x xs ih =>
      simp only [List.idxOf_cons, Bool.cond_eq_ite, beq_iff_eq]
      by_cases hxa : x = a
      · simp [hxa]
      · simp only [hxa, if_false]
        simp only [List.mem_cons] at ha
        rcases ha with heq | hmem
        · exact absurd heq.symm hxa
        · simpa using ih hmem


proof_of List.getElem_idxOf_self := by
  -- BEGIN PROOF
    induction xs with
    | nil => cases ha
    | cons x xs ih =>
      simp only [List.idxOf_cons, Bool.cond_eq_ite, beq_iff_eq]
      by_cases hxa : x = a
      · simp [hxa]
      · simp only [hxa, if_false]
        simp only [List.mem_cons] at ha
        rcases ha with heq | hmem
        · exact absurd heq.symm hxa
        · simpa using ih hmem


proof_of foHornClause_of_propClause_mem := by
  -- BEGIN PROOF
    unfold foHornClausesToPropSequent at hC_mem
    rw [LCS.Finset.mem_ofList, List.mem_map] at hC_mem
    exact hC_mem


proof_of foLiteralPos_reflect := by
  -- BEGIN PROOF
    unfold foHornClauseToPropClause LCS.Resolution.GCNF.Clause.ofList at hMem
    rw [LCS.Finset.mem_ofList, List.mem_map] at hMem
    obtain ⟨lit, hlitMem, hlitEq⟩ := hMem
    cases lit with
    | pos a =>
      refine ⟨a, hlitMem, ?_⟩
      simp only [foLiteralToPropLiteral] at hlitEq
      injection hlitEq.symm
    | neg a =>
      simp only [foLiteralToPropLiteral] at hlitEq
      exact LCS.Resolution.GCNF.Literal.noConfusion hlitEq


proof_of foLiteralNeg_reflect := by
  -- BEGIN PROOF
    unfold foHornClauseToPropClause LCS.Resolution.GCNF.Clause.ofList at hMem
    rw [LCS.Finset.mem_ofList, List.mem_map] at hMem
    obtain ⟨lit, hlitMem, hlitEq⟩ := hMem
    cases lit with
    | pos a =>
      simp only [foLiteralToPropLiteral] at hlitEq
      exact LCS.Resolution.GCNF.Literal.noConfusion hlitEq
    | neg a =>
      refine ⟨a, hlitMem, ?_⟩
      simp only [foLiteralToPropLiteral] at hlitEq
      injection hlitEq.symm


proof_of prevProp_neg_reflect := by
  -- BEGIN PROOF
    unfold LCS.Resolution.GCNF.Clause.ofList at hMem
    rw [LCS.Finset.mem_ofList, List.mem_map] at hMem
    obtain ⟨a, ha, hEq⟩ := hMem
    refine ⟨a, ha, ?_⟩
    injection hEq.symm


proof_of definite_pos_is_head := by
  -- BEGIN PROOF
    cases c with
    | rule h b =>
      simp [FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom] at hHead
      subst headA
      simp only [FOHornClause.toFOClause, FOHornClauseCore.toFOClause, List.mem_append, List.mem_map,
        List.mem_singleton] at haPos
      rcases haPos with ⟨x, _, hx⟩ | hEq
      · exact absurd hx (by intro h; cases h)
      · injection hEq
    | fact h =>
      simp [FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom] at hHead
      subst headA
      simp only [FOHornClause.toFOClause, FOHornClauseCore.toFOClause, List.mem_singleton] at haPos
      injection haPos
    | goal _ =>
      exact absurd hDef (by simp [FOHornClause.isDefinite, FOHornClauseCore.isDefinite])


proof_of negFilter_foHornClauseToPropClause := by
  -- BEGIN PROOF
    apply LCS.Finset.ext
    intro l
    rw [LCS.Finset.mem_filter]
    unfold foHornClauseToPropClause LCS.Resolution.GCNF.Clause.ofList
    rw [LCS.Finset.mem_ofList, LCS.Finset.mem_ofList, List.mem_map, List.mem_map]
    constructor
    · rintro ⟨⟨lit, hlitMem, hlitEq⟩, hNeg⟩
      cases lit with
      | pos a =>
        simp only [foLiteralToPropLiteral] at hlitEq
        rw [← hlitEq] at hNeg
        simp at hNeg
      | neg a =>
        simp only [foLiteralToPropLiteral] at hlitEq
        refine ⟨a, ?_, hlitEq⟩
        cases c with
        | rule head body =>
          simp only [FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty, FOHornClause.toFOClause, FOHornClauseCore.toFOClause,
            List.mem_append, List.mem_map, List.mem_singleton] at hlitMem ⊢
          cases hlitMem with
          | inl h =>
            obtain ⟨a', ha', hEq⟩ := h
            cases hEq
            exact ha'
          | inr h =>
            cases h
        | fact head =>
          simp only [FOHornClause.toFOClause, FOHornClauseCore.toFOClause, List.mem_singleton] at hlitMem
          cases hlitMem
        | goal body =>
          simp only [FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty, FOHornClause.toFOClause, FOHornClauseCore.toFOClause,
            List.mem_map] at hlitMem ⊢
          obtain ⟨a', ha', hEq⟩ := hlitMem
          cases hEq
          exact ha'
    · rintro ⟨a, ha, hEq⟩
      refine ⟨⟨FOLiteralCore.neg a, ?_, ?_⟩, ?_⟩
      · cases c with
        | rule head body =>
          simp only [FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty] at ha
          simp only [FOHornClause.toFOClause, FOHornClauseCore.toFOClause, List.mem_append, List.mem_map,
            List.mem_singleton]
          exact Or.inl ⟨a, ha, rfl⟩
        | fact head =>
          simp only [FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty] at ha
          exact absurd ha List.not_mem_nil
        | goal body =>
          simp only [FOHornClause.bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty] at ha
          simp only [FOHornClause.toFOClause, FOHornClauseCore.toFOClause, List.mem_map]
          exact ⟨a, ha, rfl⟩
      · simp only [foLiteralToPropLiteral]
        exact hEq
      · rw [← hEq]


proof_of resolveStep_alignment := by
  -- BEGIN PROOF
    -- Helper: `prevGoal[idx] = selectedAtom` and `idx < prevGoal.length`.
    have hSelMem : selectedAtom ∈ prevGoal := by
      have := List.getElem?_eq_some_iff.mp hSelIdx
      rw [← this.2]; exact List.getElem_mem _
    have hSelIdxLt : idx < prevGoal.length :=
      (List.getElem?_eq_some_iff.mp hSelIdx).1
    have hSelAtomsMem : selectedAtom ∈ atoms :=
      hPrevInAtoms selectedAtom hSelMem
    -- Encoding is injective on atoms.
    have hEncInj : ∀ a b : FOAtom L hNoEq,
        a ∈ atoms → b ∈ atoms →
        (groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms =
          (groundAtomEncode (hNoEq := by all_goals exact hNoEq)) b atoms → a = b :=
      fun a b ha hb heq =>
        (groundAtomEncode_injective (hNoEq := by all_goals exact hNoEq)) atoms hNodup a b ha hb heq
    -- Unfold `resolveStep` into `union (remove Ni (neg A)) (negFilter C)`.
    -- Chase membership on both sides.
    apply LCS.Finset.ext
    intro l
    show l ∈ LCS.Resolution.GCNF.Clause.union
      (LCS.Resolution.GCNF.Clause.remove
        (LCS.Resolution.GCNF.Clause.ofList
          (prevGoal.map (fun a =>
            LCS.Resolution.GCNF.Literal.neg
              ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms))))
        (LCS.Resolution.GCNF.Literal.neg
          ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) selectedAtom atoms)))
      _ ↔ _
    unfold LCS.Resolution.GCNF.Clause.remove LCS.Resolution.GCNF.Clause.union
      LCS.Resolution.GCNF.Clause.ofList
    rw [LCS.Finset.mem_union, LCS.Finset.mem_erase, LCS.Finset.mem_ofList,
        LCS.Finset.mem_ofList]
    -- Bridge: `l ∈ Finset.filter (λ l. match l with ...) C = l ∈ Clause.ofList (body.map ...)`.
    have hFilterMem :
        l ∈ LCS.Finset.filter
          (fun l => match l with
            | LCS.Resolution.GCNF.Literal.neg a => true
            | LCS.Resolution.GCNF.Literal.pos a => false)
          ((foHornClauseToPropClause (hNoEq := by all_goals exact hNoEq)) clause atoms) ↔
        l ∈ clause.bodyFOAtoms.map (fun a =>
          LCS.Resolution.GCNF.Literal.neg
            ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms)) := by
      have h := (negFilter_foHornClauseToPropClause (L := L) (hNoEq := by all_goals exact hNoEq)) clause atoms
      constructor
      · intro hMem
        have h2 : l ∈ LCS.Resolution.GCNF.Clause.ofList
            (clause.bodyFOAtoms.map (fun a =>
              LCS.Resolution.GCNF.Literal.neg
                ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms))) := h ▸ hMem
        unfold LCS.Resolution.GCNF.Clause.ofList at h2
        exact LCS.Finset.mem_ofList.mp h2
      · intro hMem
        have h2 : l ∈ LCS.Resolution.GCNF.Clause.ofList
            (clause.bodyFOAtoms.map (fun a =>
              LCS.Resolution.GCNF.Literal.neg
                ((groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms))) := by
          unfold LCS.Resolution.GCNF.Clause.ofList
          exact LCS.Finset.mem_ofList.mpr hMem
        exact h ▸ h2
    -- Replace the second disjunct (filter mem) by (body mem) using hFilterMem, via
    -- a direct iff manipulation (avoiding rw which has match-expression issues).
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · -- h1 : l ∈ prevGoal.map (neg∘enc), h2 : l ≠ neg(enc selectedAtom)
        rw [List.mem_map] at h1
        obtain ⟨a, haPrev, rfl⟩ := h1
        have haAtoms : a ∈ atoms := hPrevInAtoms a haPrev
        obtain ⟨j, hjLen, hj⟩ : ∃ (j : Nat) (h : j < prevGoal.length), prevGoal[j] = a :=
          List.getElem_of_mem haPrev
        have haNeSel : a ≠ selectedAtom := by
          intro hEq; apply h2; rw [hEq]
        have hjNeIdx : j ≠ idx := by
          intro hEq
          subst hEq
          have hSelEq : prevGoal[j] = selectedAtom := by
            have := List.getElem?_eq_some_iff.mp hSelIdx
            exact this.2
          rw [hj] at hSelEq
          exact haNeSel hSelEq
        have haInTakeDrop : a ∈ prevGoal.take idx ++ prevGoal.drop (idx + 1) := by
          rw [← hj]
          exact getElem_in_take_append_drop prevGoal idx j hjLen hjNeIdx
        rw [List.mem_map]
        refine ⟨a, ?_, rfl⟩
        rw [List.mem_append, List.mem_append]
        rcases List.mem_append.mp haInTakeDrop with hIn | hIn
        · exact Or.inl (Or.inl hIn)
        · exact Or.inr hIn
      · have h' := hFilterMem.mp h
        rw [List.mem_map] at h'
        obtain ⟨a, haBody, rfl⟩ := h'
        rw [List.mem_map]
        refine ⟨a, ?_, rfl⟩
        rw [List.mem_append, List.mem_append]
        exact Or.inl (Or.inr haBody)
    · intro h
      rw [List.mem_map] at h
      obtain ⟨a, haMemList, rfl⟩ := h
      rw [List.mem_append, List.mem_append] at haMemList
      rcases haMemList with (haTake | haBody) | haDrop
      · -- a ∈ prev.take idx: contradict with nodup if a = selectedAtom.
        have haInPrev : a ∈ prevGoal := List.mem_of_mem_take haTake
        have haNeSel : a ≠ selectedAtom := fun hEq => by
          -- a = selectedAtom AND a ∈ prev.take idx ⇒ prev[j] = selectedAtom for some j < idx.
          -- Combined with prev[idx] = selectedAtom (hSelIdx) + Nodup, contradiction.
          obtain ⟨j, hjLen, hj⟩ : ∃ (j : Nat) (h : j < ((prevGoal.take idx).length)),
              (prevGoal.take idx)[j] = a :=
            List.getElem_of_mem haTake
          have hjInt : j < idx := by
            rw [List.length_take] at hjLen; omega
          have hjPrev : j < prevGoal.length := by
            rw [List.length_take] at hjLen; omega
          have hjAt : prevGoal[j] = a := by rw [← hj, List.getElem_take]
          have hSelAt : prevGoal[idx] = selectedAtom := by
            have := List.getElem?_eq_some_iff.mp hSelIdx
            exact this.2
          have hjNeIdx : j ≠ idx := Nat.ne_of_lt hjInt
          have hPrevAt : prevGoal[j] = prevGoal[idx] := by rw [hjAt, hSelAt, hEq]
          exact hjNeIdx ((List.getElem_inj hPrevNodup).mp hPrevAt)
        have haAtoms : a ∈ atoms := hPrevInAtoms a haInPrev
        have hEncNe :
            (groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms ≠
              (groundAtomEncode (hNoEq := by all_goals exact hNoEq)) selectedAtom atoms := by
          intro hEq
          exact haNeSel (hEncInj a selectedAtom haAtoms hSelAtomsMem hEq)
        refine Or.inl ⟨?_, ?_⟩
        · rw [List.mem_map]; exact ⟨a, haInPrev, rfl⟩
        · intro hC; injection hC with hC'; exact hEncNe hC'
      · -- a ∈ clause.bodyFOAtoms: goes to second disjunct via hFilterMem.
        refine Or.inr ?_
        apply hFilterMem.mpr
        rw [List.mem_map]
        exact ⟨a, haBody, rfl⟩
      · -- a ∈ prev.drop (idx+1): similar nodup argument.
        have haInPrev : a ∈ prevGoal := List.mem_of_mem_drop haDrop
        have haNeSel : a ≠ selectedAtom := fun hEq => by
          obtain ⟨j, hjLen, hj⟩ : ∃ (j : Nat) (h : j < ((prevGoal.drop (idx+1)).length)),
              (prevGoal.drop (idx+1))[j] = a :=
            List.getElem_of_mem haDrop
          have hjPrev : idx + 1 + j < prevGoal.length := by
            rw [List.length_drop] at hjLen; omega
          have hjAt : prevGoal[idx + 1 + j] = a := by rw [← hj, List.getElem_drop]
          have hSelAt : prevGoal[idx] = selectedAtom := by
            have := List.getElem?_eq_some_iff.mp hSelIdx
            exact this.2
          have hjNeIdx : idx + 1 + j ≠ idx := by omega
          have hPrevAt : prevGoal[idx + 1 + j] = prevGoal[idx] := by rw [hjAt, hSelAt, hEq]
          exact hjNeIdx ((List.getElem_inj hPrevNodup).mp hPrevAt)
        have haAtoms : a ∈ atoms := hPrevInAtoms a haInPrev
        have hEncNe :
            (groundAtomEncode (hNoEq := by all_goals exact hNoEq)) a atoms ≠
              (groundAtomEncode (hNoEq := by all_goals exact hNoEq)) selectedAtom atoms := by
          intro hEq
          exact haNeSel (hEncInj a selectedAtom haAtoms hSelAtomsMem hEq)
        refine Or.inl ⟨?_, ?_⟩
        · rw [List.mem_map]; exact ⟨a, haInPrev, rfl⟩
        · intro hC; injection hC with hC'; exact hEncNe hC'


proof_of postStepPrev_ground_eq := by
  -- BEGIN PROOF
    have hBodyEq : body.map ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var)) = body :=
      (map_atomSubst_id (hNoEq := by all_goals exact hNoEq)) body
    rw [hBodyEq]
    exact (map_atomSubst_id (hNoEq := by all_goals exact hNoEq)) _


end LCS.SLD.FirstOrder

end
