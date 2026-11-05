import LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.Encoding

section

namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates

open LCS.FirstOrder.ManySorted

open LCS.FirstOrder.ManySorted.Semantics

open LCS.FirstOrder.ManySorted.Equality

open LCS.FirstOrder.ManySorted.CongruenceClosure

open LCS.FirstOrder.ManySorted.CongruenceClosure.Decision

open LCS.Propositional.Semantics

proof_of msEqBoolAsIdentity := by
  exact msFormulaEval_eq_T_iff M rfl (MSBoolSort L) a b v


proof_of semanticEqualityRelationPred_isCongruence := by
  -- REPAIR(T10-17): proof pending — Transport semantic equality to the restricted sort-fiber graph congruence.
  sorry


proof_of encodeModel_interpFunc_inl_eq := rfl


proof_of inlArgRecast_heq := by
  unfold inlArgRecast
  apply HEq.trans (eqRec_heq _ _)
  congr 1


proof_of msTermEval_term_cast := by
  cases h; rfl


proof_of lift_meaning_heq := by
  subst h
  rw [show (rfl : some s2 = some s2) ▸ msLiftTerm L t = msLiftTerm L t from rfl, ht]
  apply heq_of_eq
  rfl


proof_of msTermEval_encodeModel_liftTerm := by
  intro s t
  induction t with
  | var s i =>
    simp only [msLiftTerm, msTermEval, varMeaning, encodeAssignment]
    rfl
  | const s c =>
    simp only [msLiftTerm, msTermEval, constM, encodeModel]
    rfl
  | func f ts ih =>
    -- The lifted term is `MSTerm.func (Sum.inl f) (fun i => hsort ▸ liftTerm (ts j))`.
    -- Its meaning is `interpFunc (Sum.inl f) (fun i => meaning of i-th arg)`, which
    -- by the computation lemma is `M.interpFunc f (inlArgRecast ...)`. Pointwise,
    -- `inlArgRecast` peels to the underlying meaning (`inlArgRecast_heq`), which by
    -- the IH (`lift_meaning_heq`) is the `M`-meaning of `ts j`.
    simp only [msLiftTerm, msTermEval, funM]
    show (encodeModel L M).interpFunc (Sum.inl f) _ = _
    rw [encodeModel_interpFunc_inl_eq]
    show M.interpFunc f _ = M.interpFunc f _
    congr 1
    funext j
    apply eq_of_heq
    have hi : j.val < (((boolExtendedLanguage L).funRank (Sum.inl f)).1).length := by
      have := j.isLt
      simpa [boolExtendedLanguage, boolExtendedFunRank, List.length_map] using this
    refine HEq.trans (inlArgRecast_heq L M f _ j hi) ?_
    -- The underlying bool-extended argument is `msTermEval` of a sort-cast lift;
    -- `lift_meaning_heq` (with the IH) gives it is HEq to the `M`-meaning of the
    -- subterm; the remaining sort-equation goal is the lifted-rank `get`/`map`
    -- identity, discharged by `simp`.
    refine lift_meaning_heq L M v _ ?_ (ih _)
    simp [boolExtendedLanguage, boolExtendedFunRank, List.get_eq_getElem, List.getElem_map]


proof_of boolVal_eq_of_T_iff := by
  cases x <;> cases y <;> simp_all


proof_of liftTerm_eq_iff := by
  rw [msTermEval_encodeModel_liftTerm, msTermEval_encodeModel_liftTerm]
  constructor
  · intro h; exact h
  · intro h; rw [h]


proof_of msTopConst_eval := by
  simp [msTopConst, msTermEval, constM, encodeModel, MSBoolSort]
  rfl


proof_of encodeModel_interpFunc_inr_eq := rfl


proof_of inrArgRecast_heq := by
  unfold inrArgRecast
  apply HEq.trans (eqRec_heq _ _)
  congr 1


proof_of inrArgRecast_eval := by
  apply eq_of_heq
  have hi : j.val < (((L.predArity P).map some)).length := by
    have := j.isLt
    simpa [boolExtendedLanguage, boolExtendedFunRank, List.length_map] using this
  refine HEq.trans (inrArgRecast_heq L M P args j hi) ?_
  rw [hargs ⟨j.val, hi⟩]
  refine lift_meaning_heq L M v _ ?_ (msTermEval_encodeModel_liftTerm L M v _)
  simp only [boolExtendedLanguage, boolExtendedFunRank, List.get_eq_getElem]
  exact List.getElem_map some


proof_of msEncodeAtom_eval := by
  -- REPAIR(T10-15): proof pending — Extend atom evaluation transfer to nullary Boolean constants.
  sorry


proof_of encodeAssignment_update := by
  funext s' k
  cases s' with
  | none => simp [msAssignUpdate, encodeAssignment]; rfl
  | some s' =>
    simp only [msAssignUpdate, encodeAssignment]
    by_cases hss : s' = s
    · subst hss; simp only []
      by_cases hk : k = i
      · subst hk; simp; exact dif_pos rfl
      · simp [hk]; exact dif_pos rfl
    · refine (dif_neg (fun hc => hss (Option.some.inj hc))).trans ?_
      symm
      exact dif_neg hss


proof_of msFormulaEval_neg' := rfl


proof_of msFormulaEval_encodeModel_encode := by
  intro C
  induction C with
  | falsum => intro v; rfl
  | pred P ts => intro v; exact msEncodeAtom_eval L M v P ts
  | eq_ hL s t u =>
    intro v
    -- encoded: eq_ rfl (some s) (liftTerm t) (liftTerm u); original: eq_ hL s t u
    apply boolVal_eq_of_T_iff
    rw [msEncodeConjunction]
    refine (msFormulaEval_eq_T_iff _ _ _ _ _ _).trans ?_
    rw [msFormulaEval_eq_T_iff, liftTerm_eq_iff]
  | conj A B ihA ihB =>
    intro v
    rw [msEncodeConjunction]
    simp only [msFormulaEval_conj, ihA, ihB]
  | disj A B ihA ihB =>
    intro v
    rw [msEncodeConjunction]
    show hOr _ _ = hOr _ _
    rw [ihA, ihB]
  | impl A B ihA ihB =>
    intro v
    rw [msEncodeConjunction]
    show hImplies _ _ = hImplies _ _
    rw [ihA, ihB]
  | equiv_ A B ihA ihB =>
    intro v
    rw [msEncodeConjunction]
    show hEquiv _ _ = hEquiv _ _
    rw [ihA, ihB]
  | neg A ihA =>
    intro v
    -- `neg (pred P ts)` has a dedicated encoder clause (`msEncodeNegAtom`); all
    -- other `neg A` reduce to `neg (encode A)` by `rfl`.
    cases A with
    | pred P ts =>
      rw [show msEncodeConjunction L (MSFormula.neg (MSFormula.pred P ts))
            = MSFormula.neg (msEncodeAtom L P (fun i => by
                have hi : i.val < (L.predArity P).length := by
                  have := i.isLt
                  simpa [boolExtendedLanguage, boolExtendedFunRank, List.length_map] using this
                have hsort :
                    (((L.predArity P).map some).get i) =
                      some ((L.predArity P).get ⟨i.val, hi⟩) := by
                  simp [boolExtendedLanguage, boolExtendedFunRank, List.get_eq_getElem, List.getElem_map]
                  all_goals exact List.getElem_map some
                exact hsort ▸ msLiftTerm L (ts ⟨i.val, hi⟩))) from rfl]
      rw [msFormulaEval_neg', msFormulaEval_neg', msEncodeAtom_eval L M v P ts]
    | falsum =>
      rw [show msEncodeConjunction L (MSFormula.neg MSFormula.falsum)
            = MSFormula.neg (msEncodeConjunction L MSFormula.falsum) from rfl,
        msFormulaEval_neg', msFormulaEval_neg', ihA]
    | eq_ hL s t u =>
      rw [show msEncodeConjunction L (MSFormula.neg (MSFormula.eq_ hL s t u))
            = MSFormula.neg (msEncodeConjunction L (MSFormula.eq_ hL s t u)) from rfl,
        msFormulaEval_neg', msFormulaEval_neg', ihA]
    | conj A B =>
      rw [show msEncodeConjunction L (MSFormula.neg (MSFormula.conj A B))
            = MSFormula.neg (msEncodeConjunction L (MSFormula.conj A B)) from rfl,
        msFormulaEval_neg', msFormulaEval_neg', ihA]
    | disj A B =>
      rw [show msEncodeConjunction L (MSFormula.neg (MSFormula.disj A B))
            = MSFormula.neg (msEncodeConjunction L (MSFormula.disj A B)) from rfl,
        msFormulaEval_neg', msFormulaEval_neg', ihA]
    | impl A B =>
      rw [show msEncodeConjunction L (MSFormula.neg (MSFormula.impl A B))
            = MSFormula.neg (msEncodeConjunction L (MSFormula.impl A B)) from rfl,
        msFormulaEval_neg', msFormulaEval_neg', ihA]
    | equiv_ A B =>
      rw [show msEncodeConjunction L (MSFormula.neg (MSFormula.equiv_ A B))
            = MSFormula.neg (msEncodeConjunction L (MSFormula.equiv_ A B)) from rfl,
        msFormulaEval_neg', msFormulaEval_neg', ihA]
    | neg A =>
      rw [show msEncodeConjunction L (MSFormula.neg (MSFormula.neg A))
            = MSFormula.neg (msEncodeConjunction L (MSFormula.neg A)) from rfl,
        msFormulaEval_neg', msFormulaEval_neg', ihA]
    | all s i A =>
      rw [show msEncodeConjunction L (MSFormula.neg (MSFormula.all s i A))
            = MSFormula.neg (msEncodeConjunction L (MSFormula.all s i A)) from rfl,
        msFormulaEval_neg', msFormulaEval_neg', ihA]
    | ex s i A =>
      rw [show msEncodeConjunction L (MSFormula.neg (MSFormula.ex s i A))
            = MSFormula.neg (msEncodeConjunction L (MSFormula.ex s i A)) from rfl,
        msFormulaEval_neg', msFormulaEval_neg', ihA]
  | all s i A ihA =>
    intro v
    rw [msEncodeConjunction]
    show forallM _ _ _ _ = forallM _ _ _ _
    simp only [forallM]
    have key : ∀ a : M.carrier s,
        msFormulaEval (encodeModel L M) (msEncodeConjunction L A)
            (msAssignUpdate (encodeModel L M) (encodeAssignment L v) (some s) i a)
          = msFormulaEval M A (msAssignUpdate M v s i a) := by
      intro a; rw [encodeAssignment_update, ihA]
    congr 1
    apply propext
    constructor
    · intro hall a; rw [← key a]; exact hall a
    · intro hall a; rw [key a]; exact hall a
  | ex s i A ihA =>
    intro v
    rw [msEncodeConjunction]
    show existsM _ _ _ _ = existsM _ _ _ _
    simp only [existsM]
    have key : ∀ a : M.carrier s,
        msFormulaEval (encodeModel L M) (msEncodeConjunction L A)
            (msAssignUpdate (encodeModel L M) (encodeAssignment L v) (some s) i a)
          = msFormulaEval M A (msAssignUpdate M v s i a) := by
      intro a; rw [encodeAssignment_update, ihA]
    congr 1
    apply propext
    constructor
    · rintro ⟨a, ha⟩; exact ⟨a, by rw [← key a]; exact ha⟩
    · rintro ⟨a, ha⟩; exact ⟨a, by rw [key a]; exact ha⟩


proof_of encodePreservesSat := let ⟨M, v, hsat⟩ := h
  -- BEGIN PROOF
    -- From a satisfying model `M, v` of `C`, the encoded model `encodeModel L M`
    -- with the lifted assignment `encodeAssignment L v` satisfies `C'`, because the
    -- formula-level transfer lemma equates their truth values.
    ⟨encodeModel L M, encodeAssignment L v, by
      rw [msFormulaEval_encodeModel_encode L M C v]; exact hsat⟩


end LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates

end
