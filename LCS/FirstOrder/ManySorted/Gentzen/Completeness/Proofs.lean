import LCS.FirstOrder.ManySorted.Gentzen.Completeness

section

namespace LCS.FirstOrder.ManySorted.Gentzen

open LCS.FirstOrder.ManySorted

open LCS.FirstOrder.ManySorted.Semantics

open LCS.Propositional.Semantics

proof_of msHintikkaSetSatisfiable := by
  -- The Herbrand structure and its identity assignment.
  let M := msHintikkaStructure H S hTA
  let v := msIdentityAssignment H S hTA
  -- Unpack the H0–H6 conditions (the three extra H0 sub-conditions cover
  -- the `MSFormula`-only constructors falsum / eq_ / equiv_).
  obtain ⟨h0, h0falsum, h0eq, h0equiv, h1, hNeg, h2, h3, h4, h5, h6⟩ := hHS
  -- Atomic predicate case, extracted as it is used in both base and
  -- step cases of the depth induction.
  have predN_case : ∀ (P : L.predSymbols)
      (ts : (i : Fin (L.predArity P).length) → MSTerm L ((L.predArity P).get i)),
      (MSSignedFormula.trueF (MSFormula.pred P ts) ∈ S →
        msFormulaEval M (MSFormula.pred P ts) v = BoolVal.T) ∧
      (MSSignedFormula.falseF (MSFormula.pred P ts) ∈ S →
        msFormulaEval M (MSFormula.pred P ts) v = BoolVal.F) := by
    intro P ts
    -- The argument terms all lie in `H` (their free variables are in
    -- `H` by H5, hence `msTermInH`).
    have htsH : ∀ (h : MSSignedFormula L), h ∈ S →
        (h = MSSignedFormula.trueF (MSFormula.pred P ts) ∨
         h = MSSignedFormula.falseF (MSFormula.pred P ts)) →
        ∀ i, ts i ∈ H ((L.predArity P).get i) := by
      intro h hmem hcase i
      refine msTermInH hTA (ts i) (fun p hp => ?_)
      refine h5 (MSFormula.pred P ts) ?_ p ?_
      · rcases hcase with rfl | rfl
        · exact Or.inl hmem
        · exact Or.inr hmem
      · exact ⟨i, hp⟩
    classical
    have hevalEq : ∀ (hin : ∀ i, ts i ∈ H ((L.predArity P).get i)),
        msFormulaEval M (MSFormula.pred P ts) v =
          (if MSSignedFormula.trueF (MSFormula.pred P ts) ∈ S
            then BoolVal.T else BoolVal.F) := by
      intro hin
      -- First rewrite the evaluated argument terms to `⟨ts i, _⟩` (still in
      -- terms of `M`, before unfolding the structure projection).
      have hargs : (fun i => msTermEval M v (ts i)) =
          (fun i => (⟨ts i, hin i⟩ : { t // t ∈ H _ })) :=
        funext (fun i => msTermEvalIdentity (ts i) (hin i))
      simp only [msFormulaEval, predM]
      rw [hargs]
      -- Now the `interpPred` of `M = msHintikkaStructure …` is exactly the
      -- `if … ∈ S` clause, with the `(ts i)` carrier values being `ts i`.
      simp only [M, msHintikkaStructure]
    refine ⟨fun hT => ?_, fun hF => ?_⟩
    · have hin := htsH _ hT (Or.inl rfl)
      rw [hevalEq hin, if_pos hT]
    · have hin := htsH _ hF (Or.inr rfl)
      rw [hevalEq hin]
      rw [if_neg (fun hT => h0 (MSFormula.pred P ts) trivial ⟨hT, hF⟩)]
  -- The combined `key` claim, by strong induction on depth:
  -- `key A`: (T A ∈ S → A evaluates to T) ∧ (F A ∈ S → A evaluates to F).
  have key : ∀ A : MSFormula L,
      (MSSignedFormula.trueF A ∈ S → msFormulaEval M A v = BoolVal.T) ∧
      (MSSignedFormula.falseF A ∈ S → msFormulaEval M A v = BoolVal.F) := by
    suffices aux : ∀ (n : Nat) (A : MSFormula L), msFormulaDepth A ≤ n →
        (MSSignedFormula.trueF A ∈ S → msFormulaEval M A v = BoolVal.T) ∧
        (MSSignedFormula.falseF A ∈ S → msFormulaEval M A v = BoolVal.F) from
      fun A => aux (msFormulaDepth A) A (Nat.le_refl _)
    intro n
    induction n with
    | zero =>
      intro A hle
      match A with
      | .falsum =>
        -- ⊥ is atomic (depth 0). `T ⊥ ∈ S` is excluded by H0-falsum;
        -- `⊥` evaluates to F, so the F-direction is `rfl`.
        exact ⟨fun hT => absurd hT h0falsum, fun _ => rfl⟩
      | .pred P ts => exact predN_case P ts
      | .eq_ hL s' t1 t2 =>
        -- Atomic equality (depth 0). Excluded from S by H0-no-equality.
        exact ⟨fun hT => absurd hT (h0eq hL s' t1 t2).1,
               fun hF => absurd hF (h0eq hL s' t1 t2).2⟩
      | .neg _ => simp [msFormulaDepth] at hle
      | .conj _ _ => simp [msFormulaDepth] at hle
      | .disj _ _ => simp [msFormulaDepth] at hle
      | .impl _ _ => simp [msFormulaDepth] at hle
      | .equiv_ _ _ => simp [msFormulaDepth] at hle
      | .all _ _ _ => simp [msFormulaDepth] at hle
      | .ex _ _ _ => simp [msFormulaDepth] at hle
    | succ n ih_n =>
      intro A hle
      match A with
      | .falsum =>
        exact ⟨fun hT => absurd hT h0falsum, fun _ => rfl⟩
      | .pred P ts => exact predN_case P ts
      | .eq_ hL s' t1 t2 =>
        exact ⟨fun hT => absurd hT (h0eq hL s' t1 t2).1,
               fun hF => absurd hF (h0eq hL s' t1 t2).2⟩
      | .equiv_ A' B' =>
        -- `≡` is excluded from S by H0-no-equivalence (the §5.4 normalized
        -- signed decomposition does not cover `≡`).
        exact ⟨fun hT => absurd hT (h0equiv A' B').1,
               fun hF => absurd hF (h0equiv A' B').2⟩
      | .conj A' B' =>
        have ihA := ih_n A' (by simp only [msFormulaDepth] at hle; omega)
        have ihB := ih_n B' (by simp only [msFormulaDepth] at hle; omega)
        refine ⟨fun hT => ?_, fun hF => ?_⟩
        · obtain ⟨hTA', hTB'⟩ := (h1 A' B').1 hT
          simp only [msFormulaEval, Semantics.andM, ihA.1 hTA', ihB.1 hTB']
          rfl
        · rcases (h2 A' B').1 hF with hFA' | hFB'
          · simp only [msFormulaEval, Semantics.andM, ihA.2 hFA']; rfl
          · simp only [msFormulaEval, Semantics.andM, ihB.2 hFB']
            cases hb : msFormulaEval M A' v <;> rfl
      | .disj A' B' =>
        have ihA := ih_n A' (by simp only [msFormulaDepth] at hle; omega)
        have ihB := ih_n B' (by simp only [msFormulaDepth] at hle; omega)
        refine ⟨fun hT => ?_, fun hF => ?_⟩
        · rcases (h2 A' B').2.1 hT with hTA' | hTB'
          · simp only [msFormulaEval, Semantics.orM, ihA.1 hTA']; rfl
          · simp only [msFormulaEval, Semantics.orM, ihB.1 hTB']
            cases hb : msFormulaEval M A' v <;> rfl
        · obtain ⟨hFA', hFB'⟩ := (h1 A' B').2.1 hF
          simp only [msFormulaEval, Semantics.orM, ihA.2 hFA', ihB.2 hFB']
          rfl
      | .impl A' B' =>
        have ihA := ih_n A' (by simp only [msFormulaDepth] at hle; omega)
        have ihB := ih_n B' (by simp only [msFormulaDepth] at hle; omega)
        refine ⟨fun hT => ?_, fun hF => ?_⟩
        · rcases (h2 A' B').2.2 hT with hFA' | hTB'
          · simp only [msFormulaEval, Semantics.implM, ihA.2 hFA']; rfl
          · simp only [msFormulaEval, Semantics.implM, ihB.1 hTB']
            cases hb : msFormulaEval M A' v <;> rfl
        · obtain ⟨hTA', hFB'⟩ := (h1 A' B').2.2 hF
          simp only [msFormulaEval, Semantics.implM, ihA.1 hTA', ihB.2 hFB']
          rfl
      | .neg A' =>
        have ihA := ih_n A' (by simp only [msFormulaDepth] at hle; omega)
        refine ⟨fun hT => ?_, fun hF => ?_⟩
        · have hFA' := (hNeg A').1 hT
          simp only [msFormulaEval, Semantics.negM, ihA.2 hFA']; rfl
        · have hTA' := (hNeg A').2 hF
          simp only [msFormulaEval, Semantics.negM, ihA.1 hTA']; rfl
      | .all s' x A' =>
        refine ⟨fun hT => ?_, fun hF => ?_⟩
        · -- T (∀_s' x A') ∈ S → eval = T : every carrier element ⟨t, ht⟩
          -- gives A'[t/x] ∈ S (H3), evaluated to T (depth-IH), pulled back
          -- through `msFormulaSubstEvalDirect`.
          simp only [M, msFormulaEval, forallM]
          rw [if_pos]
          rintro ⟨t, ht⟩
          have hsubst : MSSignedFormula.trueF (msFormulaSubst A' s' x t) ∈ S :=
            (h3 s' x A').1 hT t ht
          have hdepth : msFormulaDepth (msFormulaSubst A' s' x t) ≤ n := by
            rw [msFormulaSubst_depth]; simp only [msFormulaDepth] at hle; omega
          have heval := (ih_n (msFormulaSubst A' s' x t) hdepth).1 hsubst
          have hfree : msIsFreeFor A' s' x t :=
            h6 s' x A' t ht (Or.inl hT)
          rw [msFormulaSubstEvalDirect A' s' x t hfree v] at heval
          rw [msTermEvalIdentity t ht] at heval
          exact heval
        · -- F (∀_s' x A') ∈ S → eval = F : witness ⟨t, ht⟩ with A'[t/x] ∈ S
          -- (H4) evaluated to F, so `forallM` is F.
          obtain ⟨t, ht, hsubst⟩ := (h4 s' x A').1 hF
          have hdepth : msFormulaDepth (msFormulaSubst A' s' x t) ≤ n := by
            rw [msFormulaSubst_depth]; simp only [msFormulaDepth] at hle; omega
          have heval := (ih_n (msFormulaSubst A' s' x t) hdepth).2 hsubst
          have hfree : msIsFreeFor A' s' x t :=
            h6 s' x A' t ht (Or.inr (Or.inl hF))
          rw [msFormulaSubstEvalDirect A' s' x t hfree v] at heval
          rw [msTermEvalIdentity t ht] at heval
          simp only [M, msFormulaEval, forallM]
          rw [if_neg]
          intro hall
          exact absurd (hall ⟨t, ht⟩) (by rw [heval]; decide)
      | .ex s' x A' =>
        refine ⟨fun hT => ?_, fun hF => ?_⟩
        · -- T (∃_s' x A') ∈ S → eval = T : witness ⟨t, ht⟩ with A'[t/x] ∈ S
          -- (H4) evaluated to T.
          obtain ⟨t, ht, hsubst⟩ := (h4 s' x A').2 hT
          have hdepth : msFormulaDepth (msFormulaSubst A' s' x t) ≤ n := by
            rw [msFormulaSubst_depth]; simp only [msFormulaDepth] at hle; omega
          have heval := (ih_n (msFormulaSubst A' s' x t) hdepth).1 hsubst
          have hfree : msIsFreeFor A' s' x t :=
            h6 s' x A' t ht (Or.inr (Or.inr (Or.inl hT)))
          rw [msFormulaSubstEvalDirect A' s' x t hfree v] at heval
          rw [msTermEvalIdentity t ht] at heval
          simp only [M, msFormulaEval, existsM]
          rw [if_pos ⟨⟨t, ht⟩, heval⟩]
        · -- F (∃_s' x A') ∈ S → eval = F : every carrier element ⟨t, ht⟩
          -- gives A'[t/x] ∈ S (H3 for ∃-false), evaluated to F.
          simp only [M, msFormulaEval, existsM]
          rw [if_neg]
          rintro ⟨⟨t, ht⟩, heval⟩
          have hsubst : MSSignedFormula.falseF (msFormulaSubst A' s' x t) ∈ S :=
            (h3 s' x A').2 hF t ht
          have hdepth : msFormulaDepth (msFormulaSubst A' s' x t) ≤ n := by
            rw [msFormulaSubst_depth]; simp only [msFormulaDepth] at hle; omega
          have hnev := (ih_n (msFormulaSubst A' s' x t) hdepth).2 hsubst
          have hfree : msIsFreeFor A' s' x t :=
            h6 s' x A' t ht (Or.inr (Or.inr (Or.inr hF)))
          rw [msFormulaSubstEvalDirect A' s' x t hfree v] at hnev
          rw [msTermEvalIdentity t ht] at hnev
          rw [hnev] at heval
          exact absurd heval (by decide)
  exact ⟨M, v, fun A hA => (key A).1 hA, fun A hA => (key A).2 hA⟩

proof_of msGoedelExtendedCompletenessG := by
  constructor
  · -- REPAIR(T10-32a): proof pending — completeness for the separated possibly infinite end sequent.
    sorry
  · exact msSoundnessG hL seq

end LCS.FirstOrder.ManySorted.Gentzen
end
