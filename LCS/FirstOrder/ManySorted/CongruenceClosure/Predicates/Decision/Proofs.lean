import LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.Decision

section

namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates

open LCS.FirstOrder.ManySorted

open LCS.FirstOrder.ManySorted.Semantics

open LCS.FirstOrder.ManySorted.Equality

open LCS.FirstOrder.ManySorted.CongruenceClosure

open LCS.FirstOrder.ManySorted.CongruenceClosure.Decision

open LCS.Propositional.Semantics

proof_of decodeModel_interpFunc_eq := rfl


proof_of decodeInlArgRecast_heq := by
  unfold decodeInlArgRecast
  apply HEq.trans (eqRec_heq _ _)
  congr 1


proof_of decodeInrArgRecast_heq := by
  unfold decodeInrArgRecast
  apply HEq.trans (eqRec_heq _ _)
  congr 1


proof_of decode_lift_meaning_heq := by
  subst h
  rw [show (rfl : some s2 = some s2) ▸ msLiftTerm L t = msLiftTerm L t from rfl, ht]
  apply heq_of_eq
  rfl


proof_of msTermEval_decodeModel_liftTerm := by
  intro s t
  induction t with
  | var s i =>
    simp only [msLiftTerm, msTermEval, varMeaning, decodeAssignment]
  | const s c =>
    simp only [msLiftTerm, msTermEval, constM, decodeModel]
  | func f ts ih =>
    -- lifted term: `func (Sum.inl f) (fun i => hsort ▸ liftTerm (ts j))`.
    simp only [msLiftTerm, msTermEval, funM]
    show M'.interpFunc (Sum.inl f) _
      = (show (decodeModel L M').carrier (L.funRank f).2 = M'.carrier (some (L.funRank f).2)
          from rfl) ▸ _
    rw [decodeModel_interpFunc_eq]
    show M'.interpFunc (Sum.inl f) _ = M'.interpFunc (Sum.inl f) _
    congr 1
    funext i
    apply eq_of_heq
    have hj : i.val < (L.funRank f).1.length := by
      have := i.isLt
      simpa [boolExtendedLanguage, boolExtendedFunRank, List.length_map] using this
    -- RHS `i`-th arg is `decodeInlArgRecast … i` (HEq to the underlying meaning);
    -- LHS `i`-th arg is `msTermEval M' v' (hsort ▸ liftTerm (ts ⟨i.val,hj⟩))`.
    refine HEq.trans ?_ (decodeInlArgRecast_heq L M' f _ i hj).symm
    refine decode_lift_meaning_heq L M' v' _ ?_ (ih ⟨i.val, hj⟩)
    simp [boolExtendedLanguage, boolExtendedFunRank, List.get_eq_getElem, List.getElem_map]
    exact List.getElem_map some


proof_of msTopConst_eval' := by
  simp [msTopConst, msTermEval, constM, MSBoolSort]


proof_of msPredAsFuncTerm_eval_decode := by
  -- REPAIR(T10-15): proof pending — Evaluate nullary constants and positive predicate functions in the decoder.
  sorry


proof_of decodeAssignment_update := by
  funext s' k
  simp only [msAssignUpdate, decodeAssignment]
  by_cases hss : s' = s
  · subst hss
    by_cases hk : k = i
    · subst hk; simp; symm; exact dif_pos rfl
    · simp [hk]; rfl
  · refine (dif_neg hss).trans ?_
    symm
    exact dif_neg (fun hc => hss (Option.some.inj hc))


proof_of msFormulaEval_decodeModel_encode := by
  -- REPAIR(T10-15): proof pending — Extend inverse formula transfer to nullary predicate constants.
  sorry


proof_of encodeReflectsSat := let ⟨M', v', hsat⟩ := h
  ⟨decodeModel L M', decodeAssignment L v', by
    rw [msFormulaEval_decodeModel_encode L M' C v']; exact hsat⟩


proof_of noCollision_sat_direction_pred := by
  -- BEGIN PROOF
    -- (b) The encoded conjunction `C'` is a conjunction of literals all of
    -- which are (negated) equations (`encode_isConjOfLiterals` /
    -- `encode_conjuncts_isEq`), and (repackaging `hno`) it has no collision,
    -- so the GUARDED model construction gives `msSatisfiable C'` over `L'`.
    -- (c) DECODE that model back to `L` (`encodeReflectsSat`) to satisfy `C`.
    apply encodeReflectsSat L C
    refine noCollision_sat_direction_guarded (msEncodeConjunction L C)
      (encode_isConjOfLiterals L C hC hNoBot)
      (encode_conjuncts_isEq L C hC hNoBot) ?_
    -- Repackage `hno`: Decision's shape carries an extra `∃ hL`, but
    -- `(boolExtendedLanguage L).hasEquality = true` definitionally, so any such
    -- `hL` equals `rfl` by proof irrelevance, and `eq_ hL = eq_ rfl`.
    rintro ⟨hL, s, r, v, p, q, hcon, hp, hq, hcol⟩
    refine hno ⟨s, r, v, p, q, ?_, hp, hq, hcol⟩
    -- `eq_ hL s r v = eq_ rfl s r v` by proof irrelevance on `hL : … = true`.
    have hLrfl : hL = rfl := rfl
    rw [hLrfl] at hcon
    exact hcon


proof_of msUnsatisfiable_iff_collision_withPredicates := by
  -- BEGIN PROOF
    constructor
    · -- Forward: unsatisfiable ⇒ a collision exists. Contrapositive of the
      -- model construction `noCollision_sat_direction_pred`: NO collision ⇒
      -- `C` is satisfiable, so `C` is not unsatisfiable.
      intro hunsat
      refine Classical.byContradiction fun hno => ?_
      exact hunsat (noCollision_sat_direction_pred L C hC hNoBot hno)
    · -- Backward: a collision ⇒ unsatisfiable. Split on whether the colliding
      -- sort is the bool sort `none` (case (ii), via `collisionCaseAtomTop`)
      -- or a non-bool sort (case (i), via `collisionCaseNonBool`). Both fold
      -- to the same soundness core (`collisionUnsatPredCore`): a collision on
      -- a negated equation of `C'` makes `C'` unsatisfiable, and the encoding
      -- preserves satisfiability.
      rintro ⟨s, r, v, p, q, hcontains, hp, hq, hcol⟩
      exact collisionUnsatPredCore L C s r v p q hcontains hp hq hcol


end LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates

end
