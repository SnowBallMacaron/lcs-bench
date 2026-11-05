import LCS.FirstOrder.ManySorted.Semantics.Substitution

namespace LCS.FirstOrder.ManySorted.Semantics.Substitution

open LCS.FirstOrder.ManySorted

open LCS.FirstOrder.ManySorted.Semantics

open LCS.Propositional.Semantics

proof_of msNamingConstEval := by
  -- BEGIN PROOF
    simp [msNamingConst, msTermEval, constM, msExtendedInterp]


proof_of msTermSubstEval := by
  -- BEGIN PROOF
    intro s' r
    induction r with
    | var s' j =>
      simp only [msTermSubst, msTermEval, varMeaning, msAssignUpdate]
      split <;> rename_i h
      · subst h
        split <;> rename_i hj
        · subst hj
          exact (msNamingConstEval M v m).symm
        · simp only [msTermEval, varMeaning]
      · simp only [msTermEval, varMeaning]
    | const s' c =>
      simp only [msTermSubst, msTermEval, constM]
    | func f ts ih =>
      simp only [msTermSubst, msTermEval, funM]
      congr 1; funext j; exact ih j






proof_of msFormulaSubstEval := by
  -- BEGIN PROOF
    induction B generalizing v with
    | falsum => rfl
    | pred P ts =>
      simp only [msFormulaSubst, msFormulaEval, predM]
      congr 1; funext j
      exact msTermSubstEval M v s i m (ts j)
    | eq_ hL s' t1 t2 =>
      classical
      have hp :
          (msTermEval (msExtendedInterp M) (msAssignUpdate (msExtendedInterp M) v s i m) t1,
           msTermEval (msExtendedInterp M) (msAssignUpdate (msExtendedInterp M) v s i m) t2) =
          (msTermEval (msExtendedInterp M) v (msTermSubst (L := msExtendedLanguage L M.carrier) s i (msNamingConst m) t1),
           msTermEval (msExtendedInterp M) v (msTermSubst (L := msExtendedLanguage L M.carrier) s i (msNamingConst m) t2)) :=
        Prod.ext (msTermSubstEval M v s i m t1) (msTermSubstEval M v s i m t2)
      exact congrArg (fun p : M.carrier s' × M.carrier s' =>
        if p.1 = p.2 then BoolVal.T else BoolVal.F) hp
    | conj A B ihA ihB =>
      simp only [msFormulaSubst, msFormulaEval, andM]
      rw [ihA v, ihB v]
    | disj A B ihA ihB =>
      simp only [msFormulaSubst, msFormulaEval, orM]
      rw [ihA v, ihB v]
    | impl A B ihA ihB =>
      simp only [msFormulaSubst, msFormulaEval, implM]
      rw [ihA v, ihB v]
    | equiv_ A B ihA ihB =>
      simp only [msFormulaSubst, msFormulaEval, equivM]
      rw [ihA v, ihB v]
    | neg A ih =>
      simp only [msFormulaSubst, msFormulaEval, negM]
      rw [ih v]
    | all s' i' A ih =>
      simp only [msFormulaSubst]
      split
      · rename_i hb
        obtain ⟨hs, hi⟩ := hb
        subst hs; subst hi
        simp only [msFormulaEval, forallM]
        have hcond : ∀ a : (msExtendedInterp M).carrier s',
            msFormulaEval (msExtendedInterp M) A
              (msAssignUpdate (msExtendedInterp M)
                (msAssignUpdate (msExtendedInterp M) v s' i' m) s' i' a) =
            msFormulaEval (msExtendedInterp M) A
              (msAssignUpdate (msExtendedInterp M) v s' i' a) := fun a => by
          exact congrArg (msFormulaEval (msExtendedInterp M) A)
            (msAssignUpdate_idem (msExtendedInterp M) v s' i' m a)
        have hpe : (∀ a, msFormulaEval (msExtendedInterp M)
              A
              (msAssignUpdate (msExtendedInterp M)
                (msAssignUpdate (msExtendedInterp M) v s' i' m) s' i' a) = BoolVal.T) =
            (∀ a, msFormulaEval (msExtendedInterp M) A
              (msAssignUpdate (msExtendedInterp M) v s' i' a) = BoolVal.T) := by
          apply propext; constructor <;> intro h a
          · rw [← hcond a]; exact h a
          · rw [hcond a]; exact h a
        split
        · rename_i hc; rw [if_pos (hpe ▸ hc)]
        · rename_i hc; rw [if_neg (hpe ▸ hc)]
      · rename_i hb
        simp only [msFormulaEval, forallM]
        have hcomm : ∀ a : (msExtendedInterp M).carrier s',
            msFormulaEval (msExtendedInterp M) A
              (msAssignUpdate (msExtendedInterp M)
                (msAssignUpdate (msExtendedInterp M) v s i m) s' i' a) =
            msFormulaEval (msExtendedInterp M)
              (msFormulaSubst A s i (msNamingConst m))
              (msAssignUpdate (msExtendedInterp M) v s' i' a) := fun a => by
          rw [msAssignUpdate_swap (msExtendedInterp M) v s s' i i' m a hb]
          exact ih (msAssignUpdate (msExtendedInterp M) v s' i' a)
        have hpe : (∀ a, msFormulaEval (msExtendedInterp M)
              A
              (msAssignUpdate (msExtendedInterp M)
                (msAssignUpdate (msExtendedInterp M) v s i m) s' i' a) = BoolVal.T) =
            (∀ a, msFormulaEval (msExtendedInterp M)
              (msFormulaSubst A s i (msNamingConst m))
              (msAssignUpdate (msExtendedInterp M) v s' i' a) = BoolVal.T) := by
          apply propext; constructor <;> intro h a
          · rw [← hcomm a]; exact h a
          · rw [hcomm a]; exact h a
        split
        · rename_i hc; rw [if_pos (hpe ▸ hc)]
        · rename_i hc; rw [if_neg (hpe ▸ hc)]
    | ex s' i' A ih =>
      simp only [msFormulaSubst]
      split
      · rename_i hb
        obtain ⟨hs, hi⟩ := hb
        subst hs; subst hi
        simp only [msFormulaEval, existsM]
        have hcond : ∀ a : (msExtendedInterp M).carrier s',
            msFormulaEval (msExtendedInterp M) A
              (msAssignUpdate (msExtendedInterp M)
                (msAssignUpdate (msExtendedInterp M) v s' i' m) s' i' a) =
            msFormulaEval (msExtendedInterp M) A
              (msAssignUpdate (msExtendedInterp M) v s' i' a) := fun a => by
          exact congrArg (msFormulaEval (msExtendedInterp M) A)
            (msAssignUpdate_idem (msExtendedInterp M) v s' i' m a)
        have hpe : (∃ a, msFormulaEval (msExtendedInterp M)
              A
              (msAssignUpdate (msExtendedInterp M)
                (msAssignUpdate (msExtendedInterp M) v s' i' m) s' i' a) = BoolVal.T) =
            (∃ a, msFormulaEval (msExtendedInterp M) A
              (msAssignUpdate (msExtendedInterp M) v s' i' a) = BoolVal.T) := by
          apply propext; constructor
          · rintro ⟨a, ha⟩; exact ⟨a, (hcond a) ▸ ha⟩
          · rintro ⟨a, ha⟩; exact ⟨a, (hcond a).symm ▸ ha⟩
        split
        · rename_i hc; rw [if_pos (hpe ▸ hc)]
        · rename_i hc; rw [if_neg (hpe ▸ hc)]
      · rename_i hb
        simp only [msFormulaEval, existsM]
        have hcomm : ∀ a : (msExtendedInterp M).carrier s',
            msFormulaEval (msExtendedInterp M) A
              (msAssignUpdate (msExtendedInterp M)
                (msAssignUpdate (msExtendedInterp M) v s i m) s' i' a) =
            msFormulaEval (msExtendedInterp M)
              (msFormulaSubst A s i (msNamingConst m))
              (msAssignUpdate (msExtendedInterp M) v s' i' a) := fun a => by
          rw [msAssignUpdate_swap (msExtendedInterp M) v s s' i i' m a hb]
          exact ih (msAssignUpdate (msExtendedInterp M) v s' i' a)
        have hpe : (∃ a, msFormulaEval (msExtendedInterp M)
              A
              (msAssignUpdate (msExtendedInterp M)
                (msAssignUpdate (msExtendedInterp M) v s i m) s' i' a) = BoolVal.T) =
            (∃ a, msFormulaEval (msExtendedInterp M)
              (msFormulaSubst A s i (msNamingConst m))
              (msAssignUpdate (msExtendedInterp M) v s' i' a) = BoolVal.T) := by
          apply propext; constructor
          · rintro ⟨a, ha⟩; exact ⟨a, (hcomm a) ▸ ha⟩
          · rintro ⟨a, ha⟩; exact ⟨a, (hcomm a).symm ▸ ha⟩
        split
        · rename_i hc; rw [if_pos (hpe ▸ hc)]
        · rename_i hc; rw [if_neg (hpe ▸ hc)]


proof_of msForallSemantics := by
  -- BEGIN PROOF
    simp only [msFormulaEval, forallM]
    split
    · rename_i hP
      refine ⟨fun _ m => ?_, fun _ => rfl⟩
      rw [← msFormulaSubstEval M B v s i m]; exact hP m
    · rename_i hP
      constructor
      · intro h; exact absurd h (by decide)
      · intro h
        exact absurd (fun a => by rw [msFormulaSubstEval M B v s i a]; exact h a) hP


proof_of msExistsSemantics := by
  -- BEGIN PROOF
    simp only [msFormulaEval, existsM]
    split
    · rename_i hP
      refine ⟨fun _ => ?_, fun _ => rfl⟩
      obtain ⟨a, ha⟩ := hP
      exact ⟨a, by rw [← msFormulaSubstEval M B v s i a]; exact ha⟩
    · rename_i hP
      constructor
      · intro h; exact absurd h (by decide)
      · rintro ⟨m, hm⟩
        exact absurd ⟨m, by rw [msFormulaSubstEval M B v s i m]; exact hm⟩ hP


proof_of msTermCoincidence := by
  -- BEGIN PROOF
    induction t with
    | var s i =>
      simp only [msTermEval, varMeaning]
      exact hAgree (s, i) rfl
    | const s c =>
      simp only [msTermEval, constM]
    | func f ts ih =>
      simp only [msTermEval, funM]
      congr 1; funext j
      exact ih j (fun y hy => hAgree y ⟨j, hy⟩)


helper /-- Lemma 10.3.2 (required helper for the quantifier cases of
`msCoincidenceLemma`): if `v1` and `v2` agree on every free variable of
`A` except possibly the bound `(s, i)` (i.e. on `FV(A) \ {(s, i)}`), then
the updated assignments `v1[x_i := a]` and `v2[x_i := a]` agree on every
free variable of `A` — the bound variable is overwritten to the common
value `a`, all others fall through to `v1`/`v2`. -/
theorem msUpdateAgree {L : MSLanguage} (M : MSStructure L)
    (v1 v2 : MSAssignment M) (s : L.SortType) (i : Nat) (a : M.carrier s)
    (A : MSFormula L)
    (hAgree : ∀ y : MSVar L, y ∈ msFormulaFV A \ Set.singleton (s, i) →
      v1 y.1 y.2 = v2 y.1 y.2) :
    ∀ y : MSVar L, y ∈ msFormulaFV A →
      msAssignUpdate M v1 s i a y.1 y.2 =
        msAssignUpdate M v2 s i a y.1 y.2 := by
-- BEGIN PROOF
  intro y hy
  simp only [msAssignUpdate]
  by_cases h1 : y.1 = s
  · subst h1
    by_cases h2 : y.2 = i
    · subst h2
      simp
    · simp only [h2, if_false]
      exact hAgree y ⟨hy, by
        intro hsing
        exact h2 (congrArg Prod.snd hsing)⟩
  · simp only [dif_neg h1]
    refine hAgree y ⟨hy, ?_⟩
    intro hsing
    exact h1 (congrArg Prod.fst hsing)

proof_of msCoincidenceLemma := by
  -- BEGIN PROOF
    induction A generalizing v1 v2 with
    | falsum => rfl
    | pred P ts =>
      simp only [msFormulaEval, predM]
      congr 1; funext j
      exact msTermCoincidence M (ts j) v1 v2 (fun y hy => hAgree y ⟨j, hy⟩)
    | eq_ hL s t1 t2 =>
      classical
      have hp : (msTermEval M v1 t1, msTermEval M v1 t2) =
          (msTermEval M v2 t1, msTermEval M v2 t2) :=
        Prod.ext (msTermCoincidence M t1 v1 v2 (fun y hy => hAgree y (Or.inl hy)))
          (msTermCoincidence M t2 v1 v2 (fun y hy => hAgree y (Or.inr hy)))
      exact congrArg (fun p : M.carrier s × M.carrier s =>
        if p.1 = p.2 then BoolVal.T else BoolVal.F) hp
    | conj A B ihA ihB =>
      simp only [msFormulaEval, andM]
      rw [ihA v1 v2 (fun y hy => hAgree y (Or.inl hy)),
          ihB v1 v2 (fun y hy => hAgree y (Or.inr hy))]
    | disj A B ihA ihB =>
      simp only [msFormulaEval, orM]
      rw [ihA v1 v2 (fun y hy => hAgree y (Or.inl hy)),
          ihB v1 v2 (fun y hy => hAgree y (Or.inr hy))]
    | impl A B ihA ihB =>
      simp only [msFormulaEval, implM]
      rw [ihA v1 v2 (fun y hy => hAgree y (Or.inl hy)),
          ihB v1 v2 (fun y hy => hAgree y (Or.inr hy))]
    | equiv_ A B ihA ihB =>
      simp only [msFormulaEval, equivM]
      rw [ihA v1 v2 (fun y hy => hAgree y (Or.inl hy)),
          ihB v1 v2 (fun y hy => hAgree y (Or.inr hy))]
    | neg A ih =>
      simp only [msFormulaEval, negM]
      rw [ih v1 v2 hAgree]
    | all s i A ih =>
      simp only [msFormulaEval, forallM]
      have heq : ∀ a : M.carrier s,
          msFormulaEval M A (msAssignUpdate M v1 s i a) =
            msFormulaEval M A (msAssignUpdate M v2 s i a) := fun a =>
        ih (msAssignUpdate M v1 s i a) (msAssignUpdate M v2 s i a)
          (msUpdateAgree M v1 v2 s i a A hAgree)
      have hcond : (∀ a : M.carrier s,
            msFormulaEval M A (msAssignUpdate M v1 s i a) = BoolVal.T) =
          (∀ a : M.carrier s,
            msFormulaEval M A (msAssignUpdate M v2 s i a) = BoolVal.T) := by
        apply propext
        constructor <;> intro h a
        · rw [← heq a]; exact h a
        · rw [heq a]; exact h a
      split
      · rename_i hc1
        rw [if_pos (hcond ▸ hc1)]
      · rename_i hc1
        rw [if_neg (hcond ▸ hc1)]
    | ex s i A ih =>
      simp only [msFormulaEval, existsM]
      have heq : ∀ a : M.carrier s,
          msFormulaEval M A (msAssignUpdate M v1 s i a) =
            msFormulaEval M A (msAssignUpdate M v2 s i a) := fun a =>
        ih (msAssignUpdate M v1 s i a) (msAssignUpdate M v2 s i a)
          (msUpdateAgree M v1 v2 s i a A hAgree)
      have hcond : (∃ a : M.carrier s,
            msFormulaEval M A (msAssignUpdate M v1 s i a) = BoolVal.T) =
          (∃ a : M.carrier s,
            msFormulaEval M A (msAssignUpdate M v2 s i a) = BoolVal.T) := by
        apply propext
        constructor
        · rintro ⟨a, ha⟩; exact ⟨a, (heq a) ▸ ha⟩
        · rintro ⟨a, ha⟩; exact ⟨a, (heq a).symm ▸ ha⟩
      split
      · rename_i hc1
        rw [if_pos (hcond ▸ hc1)]
      · rename_i hc1
        rw [if_neg (hcond ▸ hc1)]


proof_of msSentenceTruthIndep := by
  -- BEGIN PROOF
    refine msCoincidenceLemma M A v1 v2 (fun y hy => ?_)
    have hfv : msFormulaFV A = ∅ := hSent
    rw [hfv] at hy
    exact absurd hy id


proof_of msAlphaEquivUniv := by
  -- REPAIR(T10-54): proof pending — universal same-sort renaming under free-for and freshness
  sorry

proof_of msAlphaEquivEx := by
  -- REPAIR(T10-54): proof pending — existential same-sort renaming under free-for and freshness
  sorry

end LCS.FirstOrder.ManySorted.Semantics.Substitution
