import LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.Decision

section

namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates

open LCS.FirstOrder.ManySorted

open LCS.FirstOrder.ManySorted.Semantics

open LCS.FirstOrder.ManySorted.Equality

open LCS.FirstOrder.ManySorted.CongruenceClosure

open LCS.FirstOrder.ManySorted.CongruenceClosure.Decision

open LCS.Propositional.Semantics

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
