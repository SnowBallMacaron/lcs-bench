import LCS.FirstOrder.ManySorted.Equality

namespace LCS.FirstOrder.ManySorted.Equality

open LCS.FirstOrder.ManySorted

open LCS.FirstOrder.ManySorted.Semantics

open LCS.FirstOrder.ManySorted.Gentzen

open LCS.Propositional.Semantics

proof_of msEqReflValid := by
  simp [msFormulaEval, eqM]


helper /-- Helper: `hImplies x y = T` iff (`x = T` implies `y = T`). The
`BoolVal`-valued reformulation of implication truth used to discharge
the implication-shaped congruence-validity goals. -/
theorem hImplies_eq_T_iff (x y : BoolVal) :
    hImplies x y = BoolVal.T ↔ (x = BoolVal.T → y = BoolVal.T) := by
  cases x <;> cases y <;> simp [hImplies]









helper /-- Helper: if `msConjoinFormulae default fs` evaluates to `T`, then every
constituent formula of `fs` evaluates to `T`. The many-sorted
`BoolVal`-valued analogue of one-sorted `conjoinFormulaeEval`, proved by
induction on the list structure (matching `msConjoinFormulae`'s
recursion). -/
theorem msConjoinFormulaeEval {L : MSLanguage} {M : MSStructure L}
    {v : MSAssignment M} {default : MSFormula L} {fs : List (MSFormula L)}
    (h : msFormulaEval M (msConjoinFormulae default fs) v = BoolVal.T) :
    ∀ F ∈ fs, msFormulaEval M F v = BoolVal.T := by
  induction fs with
  | nil => intro F hF; simp at hF
  | cons A rest ih =>
    intro F hF
    match rest, ih with
    | [], _ =>
      simp only [msConjoinFormulae] at h
      have : F = A := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
        exact hF
      rw [this]; exact h
    | B :: tail, ih' =>
      simp only [msConjoinFormulae] at h
      rw [msFormulaEval_conj, hAnd_eq_T_iff] at h
      rcases List.mem_cons.mp hF with rfl | hF'
      · exact h.1
      · exact ih' h.2 F hF'

proof_of msEqFuncCongValid := by
  simp only [msEqCongruenceImplFunc]
  rw [msFormulaEval_impl, hImplies_eq_T_iff]
  intro hant
  have hpairs := msConjoinFormulaeEval hant
  -- Each equality pair evaluates to T, giving equal term meanings.
  have heqs : ∀ i, msTermEval M v (ss i) = msTermEval M v (ts i) := by
    intro i
    have hi : MSFormula.eq_ hL ((L.funRank f).1.get i) (ss i) (ts i)
        ∈ msEqPairsList hL (L.funRank f).1.get ss ts := by
      simp only [msEqPairsList, List.mem_map]
      exact ⟨i, List.mem_finRange i, rfl⟩
    exact (msFormulaEval_eq_T_iff M hL _ _ _ v).mp (hpairs _ hi)
  -- Goal: the consequent equality evaluates to T.
  rw [msFormulaEval_eq_T_iff]
  simp only [msTermEval, funM]
  congr 1
  funext i
  exact heqs i


proof_of msEqPredCongValid := by
  simp only [msEqCongruenceImplPred]
  rw [msFormulaEval_impl, hImplies_eq_T_iff]
  intro hant
  have hall := msConjoinFormulaeEval hant
  -- The premise predicate P ss is true (it is the last element appended).
  have hPss : msFormulaEval M (MSFormula.pred P ss) v = BoolVal.T :=
    hall _ (List.mem_append_right _ (List.Mem.head _))
  -- Each equality pair gives equal term meanings.
  have heqs : ∀ i, msTermEval M v (ss i) = msTermEval M v (ts i) := by
    intro i
    have hi : MSFormula.eq_ hL ((L.predArity P).get i) (ss i) (ts i)
        ∈ msEqPairsList hL (L.predArity P).get ss ts
          ++ [MSFormula.pred P ss] := by
      apply List.mem_append_left
      simp only [msEqPairsList, List.mem_map]
      exact ⟨i, List.mem_finRange i, rfl⟩
    exact (msFormulaEval_eq_T_iff M hL _ _ _ v).mp (hall _ hi)
  -- Conclusion P ts: rewrite the argument meanings to those of P ss.
  show predM M P (fun i => fun w => msTermEval M w (ts i)) v = BoolVal.T
  have hargs : (fun i => msTermEval M v (ts i))
      = (fun i => msTermEval M v (ss i)) := by
    funext i; exact (heqs i).symm
  simp only [predM]
  rw [hargs]
  -- This is now exactly the premise P ss being true.
  exact hPss


proof_of msEqEqCongValid := by
  -- REPAIR(T10-07): proof pending — validity of logical equality-predicate congruence.
  sorry


proof_of msAddValidToAntecedent_iff := by
  simp only [msSequentValid]
  constructor
  · -- Forward: valid without A → valid with A (weakening the antecedent).
    intro h M v hant
    apply h M v
    intro F hF
    rcases List.mem_append.mp hF with hΓ | hΔ
    · exact hant F (by
        apply List.mem_append_left
        exact List.mem_append_left _ hΓ)
    · exact hant F (by
        apply List.mem_append_right; exact hΔ)
  · -- Backward: valid with A → valid without A (the extra A is true anyway).
    intro h M v hant
    apply h M v
    intro F hF
    rcases List.mem_append.mp hF with hΓA | hΔ
    · rcases List.mem_append.mp hΓA with hΓ | hA
      · exact hant F (List.mem_append_left _ hΓ)
      · -- F = A, which is valid.
        simp only [List.mem_singleton] at hA
        rw [hA]; exact hvalid M v
    · exact hant F (List.mem_append_right _ hΔ)


proof_of msEqTreeValid := by
  induction t with
  | base g =>
    -- §10.4 soundness of G applied to the embedded G proof tree.
    exact msProofTreeValidCore g
  | axiom_ s _hDomain hAx =>
    -- The shared common formula is true in the antecedent, hence a true
    -- witness in the succedent.
    intro M v hant
    obtain ⟨A, hA_ant, hA_suc⟩ := hAx
    exact ⟨A, hA_suc, hant A hA_ant⟩
  | onePremise rule _ ih =>
    exact (msRuleValidityIff1Core rule).mpr ih
  | twoPremise rule _ _ ih1 ih2 =>
    exact (msRuleValidityIff2Core rule).mpr ⟨ih1, ih2⟩
  | eqRefl s t Γ Δ _ ih =>
    simpa using (msAddValidToAntecedent_iff Γ [] Δ _
      (fun M v => msEqReflValid hL s t M v)).mpr (by simpa using ih)
  | eqFuncCong f ss ts Γ Δ _ ih =>
    simpa using (msAddValidToAntecedent_iff Γ [] Δ _
      (fun M v => msEqFuncCongValid hL f ss ts M v)).mpr (by simpa using ih)
  | eqPredCong P ss ts Γ Δ _ ih =>
    simpa using (msAddValidToAntecedent_iff Γ [] Δ _
      (fun M v => msEqPredCongValid hL P ss ts M v)).mpr (by simpa using ih)
  | eqEqCong s s1 s2 t1 t2 Γ Δ _ ih =>
    simpa using (msAddValidToAntecedent_iff Γ [] Δ _
      (fun M v => msEqEqCongValid hL s s1 s2 t1 t2 M v)).mpr (by simpa using ih)


proof_of msSoundnessGEq := by
  obtain ⟨finite, ⟨⟨f, _hf, hAnt⟩, ⟨g, _hg, hSucc⟩⟩, ⟨t⟩⟩ := h
  intro M v hant
  have hfinite : ∀ A ∈ finite.antecedent, msFormulaEval M A v = BoolVal.T := by
    intro A hA
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hA
    rw [← hi, hAnt i]
    exact hant (f i)
  obtain ⟨B, hB, hEval⟩ := msEqTreeValid t M v hfinite
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hB
  refine ⟨g j, ?_⟩
  rw [← hSucc j, hj]
  exact hEval


proof_of msGoedelExtendedCompletenessGEq := by
  constructor
  · -- Forward (completeness): valid → G_=-provable. The heavy direction:
    -- run the many-sorted search procedure with the equality rules and,
    -- on an infinite path, extract a many-sorted equality-Hintikka set
    -- (`MSIsHintikkaSetEq`) and an S-indexed quotient term-algebra,
    -- contradicting validity (adapting §5.6 to the many-sorted case).
    intro _hValid
    -- DEBT(pre-existing: forward completeness direction of Theorem 10.5.1, proof pending)
    sorry
  · -- Backward (soundness): G_=-provable → valid, by `msSoundnessGEq`.
    intro hProv
    exact msSoundnessGEq hL seq hProv


end LCS.FirstOrder.ManySorted.Equality
