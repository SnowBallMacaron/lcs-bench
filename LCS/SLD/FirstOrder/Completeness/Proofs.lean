import LCS.SLD.FirstOrder.Completeness

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

proof_of list_eraseDups_nodup_generic := by
  -- BEGIN PROOF
    suffices h : ∀ (n : Nat) (l : List α),
        l.length ≤ n → l.eraseDups.Nodup by
      exact h l.length l (Nat.le_refl _)
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


proof_of ofList_image_erase_union_eq_ofList := by
  -- BEGIN PROOF
    have hBodyEq : body.map ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var)) = body :=
      (map_atomSubst_id (hNoEq := by all_goals exact hNoEq)) body
    rw [hBodyEq]
    have hImageId : LCS.Finset.image ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var))
        (((LCS.Finset.ofList prev).erase Ak) ∪ (LCS.Finset.ofList body)) =
        ((LCS.Finset.ofList prev).erase Ak) ∪ (LCS.Finset.ofList body) := by
      apply LCS.Finset.ext
      intro y
      rw [LCS.Finset.mem_image]
      constructor
      · rintro ⟨a, ha, rfl⟩
        have hAGround : ∀ x, ¬ a.vars x := by
          rw [show (a ∈ ((LCS.Finset.ofList prev).erase Ak ∪ LCS.Finset.ofList body)) ↔
              _ from LCS.Finset.mem_union] at ha
          rcases ha with hPrev | hBody
          · rw [LCS.Finset.mem_erase, LCS.Finset.mem_ofList] at hPrev
            exact hPrevGround a hPrev.1
          · rw [LCS.Finset.mem_ofList] at hBody
            exact hBodyGround a hBody
        rw [(atomSubst_id (hNoEq := by all_goals exact hNoEq))]
        exact ha
      · intro hy
        refine ⟨y, hy, ?_⟩
        have hYGround : ∀ x, ¬ y.vars x := by
          rw [show (y ∈ ((LCS.Finset.ofList prev).erase Ak ∪ LCS.Finset.ofList body)) ↔
              _ from LCS.Finset.mem_union] at hy
          rcases hy with hPrev | hBody
          · rw [LCS.Finset.mem_erase, LCS.Finset.mem_ofList] at hPrev
            exact hPrevGround y hPrev.1
          · rw [LCS.Finset.mem_ofList] at hBody
            exact hBodyGround y hBody
        exact (atomSubst_id (hNoEq := by all_goals exact hNoEq)) y
    rw [hImageId]
    apply LCS.Finset.ext
    intro x
    rw [show (x ∈ (LCS.Finset.ofList prev).erase Ak ∪ LCS.Finset.ofList body) ↔
        _ from LCS.Finset.mem_union]
    rw [LCS.Finset.mem_erase, LCS.Finset.mem_ofList,
        LCS.Finset.mem_ofList, LCS.Finset.mem_ofList, List.mem_append, List.mem_append]
    have hSelLt : idx < prev.length := (List.getElem?_eq_some_iff.mp hSelIdx).1
    have hSelEq : prev[idx] = Ak := (List.getElem?_eq_some_iff.mp hSelIdx).2
    constructor
    · rintro (⟨hxPrev, hxAk⟩ | hxBody)
      · obtain ⟨j, hjLen, hj⟩ : ∃ (j : Nat) (_h : j < prev.length), prev[j] = x :=
          List.getElem_of_mem hxPrev
        have hjNeIdx : j ≠ idx := by
          intro hEq; subst hEq
          apply hxAk; rw [← hj, hSelEq]
        have hxInTakeDrop : x ∈ prev.take idx ++ prev.drop (idx + 1) := by
          rw [← hj]
          exact getElem_in_take_append_drop prev idx j hjLen hjNeIdx
        rcases List.mem_append.mp hxInTakeDrop with h1 | h2
        · exact Or.inl (Or.inl h1)
        · exact Or.inr h2
      · exact Or.inl (Or.inr hxBody)
    · rintro ((hxTake | hxBody) | hxDrop)
      · have hxInPrev : x ∈ prev := List.mem_of_mem_take hxTake
        have hxNeAk : x ≠ Ak := by
          intro hEq
          obtain ⟨j, hjLen, hj⟩ : ∃ (j : Nat) (_h : j < ((prev.take idx).length)),
              (prev.take idx)[j] = x :=
            List.getElem_of_mem hxTake
          have hjInt : j < idx := by rw [List.length_take] at hjLen; omega
          have hjPrev : j < prev.length := by rw [List.length_take] at hjLen; omega
          have hjAt : prev[j] = x := by rw [← hj, List.getElem_take]
          have hPrevAt : prev[j] = prev[idx] := by rw [hjAt, hSelEq, hEq]
          exact (Nat.ne_of_lt hjInt) ((List.getElem_inj hPrevNodup).mp hPrevAt)
        exact Or.inl ⟨hxInPrev, hxNeAk⟩
      · exact Or.inr hxBody
      · have hxInPrev : x ∈ prev := List.mem_of_mem_drop hxDrop
        have hxNeAk : x ≠ Ak := by
          intro hEq
          obtain ⟨j, hjLen, hj⟩ : ∃ (j : Nat) (_h : j < ((prev.drop (idx+1)).length)),
              (prev.drop (idx+1))[j] = x :=
            List.getElem_of_mem hxDrop
          have hjPrev : idx + 1 + j < prev.length := by rw [List.length_drop] at hjLen; omega
          have hjAt : prev[idx + 1 + j] = x := by rw [← hj, List.getElem_drop]
          have hPrevAt : prev[idx + 1 + j] = prev[idx] := by rw [hjAt, hSelEq, hEq]
          have hjNeIdx : idx + 1 + j ≠ idx := by omega
          exact hjNeIdx ((List.getElem_inj hPrevNodup).mp hPrevAt)
        exact Or.inl ⟨hxInPrev, hxNeAk⟩


proof_of clause_ofList_map_eq_toList_map := by
  -- BEGIN PROOF
    apply LCS.Finset.ext
    intro x
    unfold LCS.Resolution.GCNF.Clause.ofList
    rw [LCS.Finset.mem_ofList, LCS.Finset.mem_ofList, List.mem_map, List.mem_map]
    constructor
    · rintro ⟨a, ha, hEq⟩
      refine ⟨a, ?_, hEq⟩
      rw [LCS.Finset.mem_toList, LCS.Finset.mem_ofList] at ha
      exact ha
    · rintro ⟨a, ha, hEq⟩
      refine ⟨a, ?_, hEq⟩
      rw [LCS.Finset.mem_toList, LCS.Finset.mem_ofList]
      exact ha


proof_of ground_unsat_to_transcript := by
  -- BEGIN PROOF
    -- Propositional SLD completeness selects some negative clause participating
    -- in the refutation.  It need not select `goals_g.head`; the pending proof
    -- must retain the existential witness supplied by that bridge.
    -- DEBT(pre-existing proof pending; chapter 9 proof closure)
    sorry

proof_of foSLD_refutation_with_first_selected_from_unsat := by
  -- REPAIR(T9-16): proof pending — lift selection of the original atom in the same successful goal
  sorry

proof_of propSeqToGroundTranscript := by
  -- REPAIR(T9-77a): proof pending — migration to extensional bodies / renamed-head steps
  sorry


end LCS.SLD.FirstOrder

end

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

namespace GroundUnsatContractRegression

open LCS.FirstOrder.SyntaxN.Variables

helper /-- The concrete counterexample lies in the equality-free fragment. -/
theorem GroundUnsatContractRegression.adversary_withoutEquality : advLang.withoutEquality := rfl

helper /-- Every formula in the concrete counterexample is a nullary atom. -/
theorem GroundUnsatContractRegression.adversary_allAtomsAtomic :
    ∀ c ∈ D ++ goals, (c.allAtomsAtomic (hNoEq := by all_goals rfl)) := by
  intro c _hc
  exact (c.allAtomsAtomic_derived (hNoEq := by all_goals rfl))

helper /-- The fact `p` and later goal `:-p` make the combined Horn set
    unsatisfiable even though the head goal is `:-q`. -/
theorem GroundUnsatContractRegression.adversary_unsatisfiable :
    (FOHornClauseSet.isUnsatisfiable (hNoEq := by all_goals rfl)) p.toFormula (D ++ goals) := by
  intro hSat
  obtain ⟨M, hM⟩ := hSat
  have hPos := FOClause.universalClosure_of_validIn (L := advLang) rfl M _ (hM [FOLiteralCore.pos p] (by
    refine ⟨FOHornClause.fact (hNoEq := by rfl) p, ?_, rfl⟩
    simp [D, goals])) p.toFormula []
  have hNeg := FOClause.universalClosure_of_validIn (L := advLang) rfl M _ (hM [FOLiteralCore.neg p] (by
    refine ⟨FOHornClause.goal (LCS.Finset.singleton p) rfl, ?_, ?_⟩
    · simp [D, goals]
    · simp [FOHornClause.toFOClause, FOHornClauseCore.toFOClause, finset_toList_singleton])) p.toFormula []
  let s : Assignment M := fun _ => Classical.choice M.carrierNonempty
  have hp := hPos s
  have hnp := hNeg s
  exact hnp hp

helper /-- No ground SLD transcript from the head goal `:-q` can refute:
    the sole program clause has head `p`, so a first step would force
    the distinct nullary atoms `q` and `p` to be equal. -/
theorem GroundUnsatContractRegression.head_goal_not_refutable :
    ¬ ∃ (t : (GroundSLDTranscript (hNoEq := by all_goals rfl)) D (LCS.Finset.ofList [q])),
      t.finalGoal = (∅ : LCS.Finset (FOAtom advLang rfl)) := by
  rintro ⟨t, ht⟩
  cases t with
  | nil =>
      change (LCS.Finset.ofList [q] : LCS.Finset (FOAtom advLang rfl)) =
        (∅ : LCS.Finset (FOAtom advLang rfl)) at ht
      have hq : q ∈ (LCS.Finset.ofList [q]) := by
        rw [LCS.Finset.mem_ofList]
        simp
      rw [ht] at hq
      exact LCS.Finset.not_mem_empty hq
  | cons step rest =>
      have hc : step.clause = FOHornClause.fact (hNoEq := by rfl) p := by
        simpa [D] using step.hClause
      have hh := step.hHead
      rw [hc] at hh
      have hHead : step.headA = p := by
        simpa [FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom] using hh.symm
      have hAk : step.Ak = q := by
        simpa [LCS.Finset.mem_ofList] using step.hAk
      have hqp : q = p :=
        hAk.symm.trans (step.hUnifGround.trans hHead)
      have hPred := FOAtomCore.predN.inj hqp
      cases hPred.1

helper /-- An equality-enabled language cannot supply the explicit no-equality
    premise of the ground propositional bridge. -/
theorem GroundUnsatContractRegression.equality_enabled_fails_noEq {L : Language}
    (hEq : L.hasEquality = true) :
    ¬ L.withoutEquality := by
  intro hNoEq
  rw [Language.withoutEquality, hEq] at hNoEq
  exact Bool.noConfusion hNoEq

helper /-- A connective is rejected at the explicit ambient-formula-to-atom
    boundary and therefore cannot be used to construct a Horn goal. -/
theorem GroundUnsatContractRegression.connective_goal_fails_allAtomsAtomic {L : Language}
    (A B : FormulaN L) :
    FOAtomCore.ofFormula? (FormulaN.conj A B) = none := by
  rfl

end GroundUnsatContractRegression

end LCS.SLD.FirstOrder

end

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

proof_of foSLD_exists_refutation_from_unsat := by
  -- REPAIR(T9-77a): proof pending — migration to extensional bodies / renamed-head steps
  sorry

proof_of foSLD_selection_order_independence := by
  -- REPAIR(T9-16): proof pending — successful continuation from the given residual selecting Bi
  sorry

proof_of foSLDResolution_complete := by
  -- REPAIR(T9-15): proof pending — finite Horn completeness with local freshening and exact closure
  sorry

proof_of foSLD_selectedAtom_requiresClauseChoice := by
  -- REPAIR(T9-35): proof pending — expose the first original clause of the successful continuation
  sorry

end LCS.SLD.FirstOrder

end
