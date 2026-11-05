import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.QuotientModel

section

namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Decision

open LCS.FirstOrder.ManySorted

open LCS.FirstOrder.ManySorted.Semantics

open LCS.FirstOrder.ManySorted.Equality

open LCS.FirstOrder.ManySorted.CongruenceClosure

open LCS.Propositional.Semantics

proof_of funcNode_closureRel := by
  -- REPAIR(T10-22): proof pending — transport function ports through the occurring-sort rank list.
  sorry


proof_of funOpC_case1 := by
  -- BEGIN PROOF
    -- All arguments are `some`, and `f y_1…y_k ∈ TERM(C)`, so the first
    -- `if`-branch of `funOpC` fires.
    unfold funOpC
    have hall : ∀ i, (some (ys i)).isSome := fun _ => rfl
    rw [dif_pos hall]
    simp only [Option.get_some]
    rw [dif_pos hmem]


proof_of funOpC_case2 := by
  -- BEGIN PROOF
    unfold funOpC
    have hall : ∀ i, (some (ys i)).isSome := fun _ => rfl
    rw [dif_pos hall]
    simp only [Option.get_some]
    -- Case 1 fails by `hnot`.
    rw [dif_neg hnot]
    -- Case 2's existence holds (witnessed by `zs`), so the `some`-branch fires.
    have h2 : ∃ (zs' : (i : Fin (L.funRank f).1.length) →
          TermCarrier C ((L.funRank f).1.get i)),
        (∀ i, closureRel C ((L.funRank f).1.get i) (ys i) (zs' i)) ∧
          termSetOfSort C (L.funRank f).2 (MSTerm.func f (fun i => (zs' i).1)) :=
      ⟨zs, hcong, hmem⟩
    rw [dif_pos h2]
    -- The chosen representative `z' = h2.choose` is `R*`-congruent to `ys`,
    -- hence (transitively, with `ys ~ zs`) to `zs`; so `f z' …` and `f zs …`
    -- are `R*`-related by function congruence (2b).
    refine ⟨⟨MSTerm.func f (fun i => (h2.choose i).1), h2.choose_spec.2⟩, rfl, ?_⟩
    -- `h2.choose i  ~  ys i  ~  zs i`.
    obtain ⟨_, hsymm, htrans⟩ := positiveClosure_equivalence C
    have hcong' : ∀ i, closureRel C ((L.funRank f).1.get i) (h2.choose i) (zs i) := by
      intro i
      -- choose i ~ ys i (from choose_spec), and ys i ~ zs i (hcong).
      exact htrans
        (hsymm (h2.choose_spec.1 i)) (hcong i)
    exact funcNode_closureRel C f (h2.choose) zs h2.choose_spec.2 hmem hcong'


proof_of funOpC_case3 := by
  -- BEGIN PROOF
    unfold funOpC
    have hall : ∀ i, (some (ys i)).isSome := fun _ => rfl
    rw [dif_pos hall]
    simp only [Option.get_some]
    rw [dif_neg _hnot1, dif_neg hnot2]


proof_of closure_isAlgebraCongruence := by
  -- BEGIN PROOF
    classical
    -- Equivalence relation facts for `R*`.
    obtain ⟨hrefl, hsymm, htrans⟩ := positiveClosure_equivalence C
    -- The "has a congruent representative in TERM(C)" predicate for a family.
    let rep : ((i : Fin (L.funRank f).1.length) →
        TermCarrier C ((L.funRank f).1.get i)) → Prop :=
      fun xs => ∃ (zs' : (i : Fin (L.funRank f).1.length) →
          TermCarrier C ((L.funRank f).1.get i)),
        (∀ i, closureRel C ((L.funRank f).1.get i) (xs i) (zs' i)) ∧
          termSetOfSort C (L.funRank f).2 (MSTerm.func f (fun i => (zs' i).1))
    -- Both function values, fully unfolded, are determined by `rep`.
    -- Evaluate `funOpC C f (fun i => some (ys i))`.
    have hval : ∀ (xs : (i : Fin (L.funRank f).1.length) →
          TermCarrier C ((L.funRank f).1.get i)),
        (rep xs → ∃ w, funOpC C f (fun i => some (xs i)) = some w ∧
          (∀ (zs' : (i : Fin (L.funRank f).1.length) →
                TermCarrier C ((L.funRank f).1.get i))
              (h : (∀ i, closureRel C ((L.funRank f).1.get i) (xs i) (zs' i)) ∧
              termSetOfSort C (L.funRank f).2 (MSTerm.func f (fun i => (zs' i).1))),
            closureRel C (L.funRank f).2 w
              ⟨MSTerm.func f (fun i => (zs' i).1), h.2⟩)) ∧
        (¬ rep xs → funOpC C f (fun i => some (xs i)) = none) := by
      intro xs
      constructor
      · -- rep xs holds.
        intro hr
        by_cases h1 : termSetOfSort C (L.funRank f).2 (MSTerm.func f (fun i => (xs i).1))
        · -- Case 1: f xs ∈ TERM(C); value is `some (f xs)`.
          refine ⟨⟨MSTerm.func f (fun i => (xs i).1), h1⟩,
            funOpC_case1 C f xs h1, ?_⟩
          intro zs' h
          -- `f xs ~ f zs'` by congruence (xs ~ zs' via h.1).
          exact funcNode_closureRel C f xs zs' h1 h.2 h.1
        · -- Case 2: f xs ∉ TERM(C) but rep xs holds.
          obtain ⟨z0, hz0cong, hz0mem⟩ := hr
          obtain ⟨w, hwval, hwrel⟩ := funOpC_case2 C f xs z0 h1 hz0cong hz0mem
          refine ⟨w, hwval, ?_⟩
          intro zs' h
          -- w ~ f z0 ~ f zs' (z0 ~ xs ~ zs').
          have hz0zs' : ∀ i, closureRel C ((L.funRank f).1.get i) (z0 i) (zs' i) :=
            fun i => htrans (hsymm (hz0cong i)) (h.1 i)
          have : closureRel C (L.funRank f).2
              ⟨MSTerm.func f (fun i => (z0 i).1), hz0mem⟩
              ⟨MSTerm.func f (fun i => (zs' i).1), h.2⟩ :=
            funcNode_closureRel C f z0 zs' hz0mem h.2 hz0zs'
          exact htrans hwrel this
      · -- ¬ rep xs.
        intro hr
        have h1 : ¬ termSetOfSort C (L.funRank f).2 (MSTerm.func f (fun i => (xs i).1)) := by
          intro hmem
          -- xs is its own congruent representative.
          exact hr ⟨xs, fun i => hrefl _, hmem⟩
        exact funOpC_case3 C f xs h1 hr
    -- `rep ys ↔ rep zs` because `ys ~ zs` componentwise (transitivity).
    have hrep_iff : rep ys ↔ rep zs := by
      constructor
      · rintro ⟨z0, hz0cong, hz0mem⟩
        exact ⟨z0, fun i => htrans (hsymm (hcong i)) (hz0cong i), hz0mem⟩
      · rintro ⟨z0, hz0cong, hz0mem⟩
        exact ⟨z0, fun i => htrans (hcong i) (hz0cong i), hz0mem⟩
    by_cases hr : rep ys
    · -- Both values are `some`, and the two representatives are `R*`-related.
      obtain ⟨wy, hwy, hwyrel⟩ := (hval ys).1 hr
      obtain ⟨wz, hwz, hwzrel⟩ := (hval zs).1 (hrep_iff.mp hr)
      refine Or.inr ⟨wy, wz, hwy, hwz, ?_⟩
      -- Use `wy ~ f zs' ` for a common representative `zs'` (take `zs'` for zs).
      obtain ⟨z0, hz0cong, hz0mem⟩ := hrep_iff.mp hr
      -- wz ~ f z0 (taking zs' := z0 for zs).
      have hwz_z0 : closureRel C (L.funRank f).2 wz
          ⟨MSTerm.func f (fun i => (z0 i).1), hz0mem⟩ :=
        hwzrel z0 ⟨hz0cong, hz0mem⟩
      -- wy ~ f z0 too: z0 is congruent to ys (z0 ~ zs ~ ys → use for ys).
      have hys_z0 : ∀ i, closureRel C ((L.funRank f).1.get i) (ys i) (z0 i) :=
        fun i => htrans (hcong i) (hz0cong i)
      have hwy_z0 : closureRel C (L.funRank f).2 wy
          ⟨MSTerm.func f (fun i => (z0 i).1), hz0mem⟩ :=
        hwyrel z0 ⟨hys_z0, hz0mem⟩
      -- wy ~ f z0 ~ wz.
      exact htrans hwy_z0 (hsymm hwz_z0)
    · -- Both values are `none`.
      have hrz : ¬ rep zs := fun h => hr (hrep_iff.mpr h)
      exact Or.inl ⟨(hval ys).2 hr, (hval zs).2 hrz⟩


proof_of closureSetoid_r_iff := by
  -- BEGIN PROOF
    constructor
    · rintro ⟨p, q, hp, hq, hpq⟩
      -- `p = carrierNode C s t`, `q = carrierNode C s u` as nodes.
      have hpe : p = carrierNode C s t := Subtype.ext hp
      have hqe : q = carrierNode C s u := Subtype.ext hq
      rw [hpe, hqe] at hpq
      exact hpq
    · intro h
      exact ⟨carrierNode C s t, carrierNode C s u, rfl, rfl, h⟩


proof_of chooseRep_spec := Classical.choose_spec (Quotient.exists_rep q)
  -- BEGIN PROOF


proof_of termMeaning_eq_class := by
  -- BEGIN PROOF
    -- Induct on the underlying term, threading its `TERM(C)` membership.
    -- Generalize over the membership proof so the induction hypothesis is
    -- available for the immediate subterms (which are in `TERM(C)` by
    -- subterm-closure).
    obtain ⟨tt, htt⟩ := t
    simp only
    -- Strengthened statement quantifying over the membership proof.
    suffices H : ∀ (s' : L.SortType) (u : MSTerm L s') (hu : termSetOfSort C s' u),
        msTermEval (quotientModel C) (quotientAssignment C) u =
          some (Quotient.mk (closureSetoid C s') ⟨u, hu⟩) from H s tt htt
    intro s' u
    induction u with
    | var s'' i =>
      intro hu
      -- `x_M[v] = v(x) = some [x]` because `x ∈ TERM(C)`.
      show msTermEval (quotientModel C) (quotientAssignment C) (MSTerm.var s'' i) = _
      simp only [msTermEval, varMeaning, quotientAssignment]
      exact dif_pos hu
    | const s'' c =>
      intro hu
      -- `c_M[v] = c_M = some [c]` because `c ∈ TERM(C)`.
      show msTermEval (quotientModel C) (quotientAssignment C) (MSTerm.const s'' c) = _
      simp only [msTermEval, constM, quotientModel]
      rw [dif_pos hu]
    | func f ts ih =>
      intro hu
      -- `(f ts)_M[v] = interpFunc f (fun i => (ts i)_M[v])`. Each `ts i ∈ TERM(C)`
      -- by subterm-closure, so by IH `(ts i)_M[v] = some [ts i]`.
      have htsi : ∀ i, termSetOfSort C ((L.funRank f).1.get i) (ts i) := by
        intro i
        obtain ⟨hL, sc, t', u', hcontain, hsub⟩ := hu
        refine ⟨hL, sc, t', u', hcontain, ?_⟩
        rcases hsub with hst | hsu
        · exact Or.inl (msTermSubterms_subterm_closed t' f ts i hst)
        · exact Or.inr (msTermSubterms_subterm_closed u' f ts i hsu)
      have hevals : ∀ i, msTermEval (quotientModel C) (quotientAssignment C) (ts i)
          = some (Quotient.mk (closureSetoid C ((L.funRank f).1.get i)) ⟨ts i, htsi i⟩) :=
        fun i => ih i (htsi i)
      -- The meaning of `f ts` is `interpFunc f (fun i => (ts i)_M[v])`, which
      -- (by the structure definition) is `quotientFunOp C f (fun i => (ts i)_M[v])`.
      have hstep : msTermEval (quotientModel C) (quotientAssignment C) (MSTerm.func f ts)
          = quotientFunOp C f
              (fun i => msTermEval (quotientModel C) (quotientAssignment C) (ts i)) := by
        simp only [msTermEval, funM]
        rfl
      rw [hstep]
      -- Rewrite the argument meanings to `some [ts i]`.
      have hargs : (fun i => msTermEval (quotientModel C) (quotientAssignment C) (ts i))
          = (fun i => some (Quotient.mk (closureSetoid C ((L.funRank f).1.get i))
              ⟨ts i, htsi i⟩)) := by
        funext i; exact hevals i
      rw [hargs]
      -- Now evaluate `quotientFunOp` on all-`some` class arguments.
      unfold quotientFunOp
      have hall : ∀ i, (some (Quotient.mk (closureSetoid C ((L.funRank f).1.get i))
          ⟨ts i, htsi i⟩)).isSome := fun _ => rfl
      rw [dif_pos hall]
      simp only [Option.get_some]
      -- `chooseRep [ts i]` is `R*`-congruent to `ts i`.
      have hchoose : ∀ i, closureRel C ((L.funRank f).1.get i)
          (chooseRep C ((L.funRank f).1.get i)
            (Quotient.mk (closureSetoid C ((L.funRank f).1.get i)) ⟨ts i, htsi i⟩))
          ⟨ts i, htsi i⟩ := by
        intro i
        have hsp := chooseRep_spec C ((L.funRank f).1.get i)
          (Quotient.mk (closureSetoid C ((L.funRank f).1.get i)) ⟨ts i, htsi i⟩)
        have := Quotient.exact hsp
        exact (closureSetoid_r_iff C ((L.funRank f).1.get i) _ _).mp this
      -- `f ts ∈ TERM(C)`, so case 1 of funOpC applies for the family `ts`.
      -- The chooseRep family may differ, but its funOpC value is `R*`-equivalent
      -- to `[f ts]`; combined with well-definedness it gives the right class.
      -- funOpC on `ts` (case 1, since f ts ∈ TERM(C)).
      have htsmem : termSetOfSort C (L.funRank f).2
          (MSTerm.func f (fun i => (⟨ts i, htsi i⟩ : TermCarrier C _).1)) := by
        simpa using hu
      -- `closure_isAlgebraCongruence` on the chooseRep family vs `ts`
      -- (chooseRep i ~ ts i, that is `hchoose`).
      have hcongR := closure_isAlgebraCongruence C f
        (fun i => chooseRep C ((L.funRank f).1.get i)
          (Quotient.mk (closureSetoid C ((L.funRank f).1.get i)) ⟨ts i, htsi i⟩))
        (fun i => ⟨ts i, htsi i⟩) (fun i => hchoose i)
      have hfun_ts : funOpC C f (fun i => some (⟨ts i, htsi i⟩ : TermCarrier C _))
          = some ⟨MSTerm.func f (fun i => (ts i)), htsmem⟩ :=
        funOpC_case1 C f (fun i => ⟨ts i, htsi i⟩) htsmem
      -- From `closureRelOpt`, the reps value is `some w` with `w ~ f ts`.
      rw [hfun_ts] at hcongR
      rcases hcongR with ⟨_, hb⟩ | ⟨w, w', haw, hbw, hrel⟩
      · exact absurd hb (by simp)
      · -- `b = some (f ts)` forces `w' = ⟨f ts, _⟩`; `a = funOpC reps = some w`.
        rw [haw]
        simp only [Option.map_some]
        -- `w ~ w' = ⟨f ts, _⟩`, so `[w] = [f ts]`.
        have hw' : w' = ⟨MSTerm.func f (fun i => (ts i)), htsmem⟩ := by
          have hbw' := hbw
          rw [Option.some.injEq] at hbw'
          exact hbw'.symm
        subst hw'
        congr 1
        -- `[w] = [⟨f ts, hu⟩]` since `w ~ ⟨f ts, _⟩` and the membership proofs
        -- are irrelevant.
        apply Quotient.sound
        exact (closureSetoid_r_iff C (L.funRank f).2 w _).mpr hrel


proof_of conjunctionOfLiterals_eval_T := by
  -- BEGIN PROOF
    intro D
    induction D with
    | conj A B _ ihB =>
      intro hcl hlit
      -- `conj A B` is a conjunction-of-literals: `A` is a literal and `B` is
      -- again a conjunction-of-literals (the `isLiteral (conj A B)` disjunct is
      -- impossible: a conjunction is never atomic).
      have hcl' : MSFormula.isLiteral A ∧ msIsConjunctionOfLiterals B := by
        rcases hcl with hself | h
        · -- `conj A B` literal ⇒ atomic or neg-atomic, both impossible.
          rcases hself with hat | ⟨B', heq, _⟩
          · exact absurd hat (by simp [MSFormula.isAtomic])
          · exact absurd heq (by simp)
        · exact h
      obtain ⟨hAlit, hBcl⟩ := hcl'
      rw [msFormulaEval_conj, hAnd_eq_T_iff]
      refine ⟨?_, ?_⟩
      · -- `A` is a literal conjunct of `conj A B`.
        exact hlit A (Or.inr (Or.inl (by
          cases A <;> first | rfl | (exact absurd hAlit (by simp [MSFormula.isLiteral, MSFormula.isAtomic]))))) hAlit
      · -- Recurse on `B`.
        refine ihB hBcl ?_
        intro X hX hXlit
        exact hlit X (Or.inr (Or.inr hX)) hXlit
    | falsum =>
      intro _ hlit
      -- `falsum` is itself a literal conjunct.
      exact hlit MSFormula.falsum rfl (by simp [MSFormula.isLiteral, MSFormula.isAtomic])
    | pred P ts =>
      intro _ hlit
      exact hlit (MSFormula.pred P ts) rfl (Or.inl (by simp [MSFormula.isAtomic]))
    | eq_ hL s t u =>
      intro _ hlit
      exact hlit (MSFormula.eq_ hL s t u) rfl (Or.inl (by simp [MSFormula.isAtomic]))
    | disj A B _ _ =>
      intro hcl hlit
      exact hlit (MSFormula.disj A B) rfl hcl
    | impl A B _ _ =>
      intro hcl hlit
      exact hlit (MSFormula.impl A B) rfl hcl
    | equiv_ A B _ _ =>
      intro hcl hlit
      exact hlit (MSFormula.equiv_ A B) rfl hcl
    | neg A _ =>
      intro hcl hlit
      exact hlit (MSFormula.neg A) rfl hcl
    | all s i A _ =>
      intro hcl hlit
      exact hlit (MSFormula.all s i A) rfl hcl
    | ex s i A _ =>
      intro hcl hlit
      exact hlit (MSFormula.ex s i A) rfl hcl


proof_of posEq_mem := ⟨⟨hL, s, t, u, Or.inl hcon, Or.inl (msTermSubterms_self _)⟩,
  -- BEGIN PROOF
     ⟨hL, s, t, u, Or.inl hcon, Or.inr (msTermSubterms_self _)⟩⟩


proof_of negEq_mem := ⟨⟨hL, s, r, vt, Or.inr hcon, Or.inl (msTermSubterms_self _)⟩,
  -- BEGIN PROOF
     ⟨hL, s, r, vt, Or.inr hcon, Or.inr (msTermSubterms_self _)⟩⟩


proof_of noCollision_sat_direction := by
  -- BEGIN PROOF
    -- The candidate model and identity-class assignment.
    refine ⟨quotientModel C, quotientAssignment C, ?_⟩
    obtain ⟨hClit, hCeq⟩ := hC
    -- Discharge `eval C = T` from per-literal eval via the structural lemma.
    refine conjunctionOfLiterals_eval_T (quotientModel C) (quotientAssignment C)
      C hClit ?_
    intro X hXcon hXlit
    -- Every literal conjunct is a positive or negated equation (`hCeq`).
    rcases hCeq X hXcon hXlit with ⟨hL, s, t, u, rfl⟩ | ⟨hL, s, r, vt, rfl⟩
    · -- Positive equation `t =̇_s u`: holds because `[t] = [u]` (`t R* u` via E).
      obtain ⟨htmem, humem⟩ := posEq_mem C hL s t u hXcon
      rw [msFormulaEval_eq_T_iff]
      -- `t_M[v] = [t]`, `u_M[v] = [u]`.
      rw [termMeaning_eq_class C s ⟨t, htmem⟩, termMeaning_eq_class C s ⟨u, humem⟩]
      -- `[t] = [u]` since `t R* u`: the positive equation seeds `E ⊆ R*`.
      have hErel : positiveEquationRelation C
          (carrierNode C s ⟨t, htmem⟩) (carrierNode C s ⟨u, humem⟩) :=
        ⟨hL, s, t, u, hXcon, rfl, rfl⟩
      have hstar : msCongruenceClosure (graphOfConjunction C)
          (positiveEquationRelation C) (positiveEquationRelation_sortSupported C)
          (carrierNode C s ⟨t, htmem⟩) (carrierNode C s ⟨u, humem⟩) :=
        msCongruenceClosure_contains _ _ _ _ _ hErel
      congr 1
      apply Quotient.sound
      exact (closureSetoid_r_iff C s ⟨t, htmem⟩ ⟨u, humem⟩).mpr hstar
    · -- Negated equation `¬ r =̇_s vt`: holds because `[r] ≠ [vt]` (no collision).
      obtain ⟨hrmem, hvmem⟩ := negEq_mem C hL s r vt hXcon
      -- The terms have distinct meanings: otherwise a collision contradicts `hno`.
      have hne : msTermEval (quotientModel C) (quotientAssignment C) r
          ≠ msTermEval (quotientModel C) (quotientAssignment C) vt := by
        intro heq
        -- `[r] = [vt]`, hence `r R* vt` — a collision.
        rw [termMeaning_eq_class C s ⟨r, hrmem⟩, termMeaning_eq_class C s ⟨vt, hvmem⟩]
          at heq
        have hclasses : Quotient.mk (closureSetoid C s) (⟨r, hrmem⟩ : TermCarrier C s)
            = Quotient.mk (closureSetoid C s) ⟨vt, hvmem⟩ :=
          Option.some.injEq _ _ ▸ heq
        have hsetoid := Quotient.exact hclasses
        have hstar := (closureSetoid_r_iff C s ⟨r, hrmem⟩ ⟨vt, hvmem⟩).mp hsetoid
        exact hno ⟨hL, s, r, vt, carrierNode C s ⟨r, hrmem⟩, carrierNode C s ⟨vt, hvmem⟩,
          hXcon, rfl, rfl, hstar⟩
      -- So `r =̇_s vt` evaluates to `F`, hence its negation to `T`.
      show msFormulaEval (quotientModel C) (MSFormula.neg (MSFormula.eq_ hL s r vt))
        (quotientAssignment C) = BoolVal.T
      dsimp only [msFormulaEval, negM, eqM]
      rw [if_neg hne]
      rfl


proof_of msUnsatisfiable_iff_collision := by
  -- BEGIN PROOF
    constructor
    · -- Forward: unsatisfiable ⇒ a collision exists. Contrapositive of the
      -- model construction: NO collision ⇒ `C` is satisfiable (the quotient
      -- term model satisfies `C`), so `C` is not unsatisfiable.
      intro hunsat
      refine Classical.byContradiction fun hno => ?_
      exact hunsat (noCollision_sat_direction C hC hno)
    · -- Backward: a collision ⇒ unsatisfiable (the soundness direction).
      intro hcol
      exact collision_unsat_direction C hcol


proof_of node_eq_of_val_eq := Subtype.ext h
  -- BEGIN PROOF


proof_of exampleNode_mem := by
  -- REPAIR(T10-71): proof pending — verify membership of the six displayed subterms.
  sorry

proof_of exampleGraphNodes_exact := by
  -- REPAIR(T10-71): proof pending — prove the six-node enumeration is exhaustive and injective.
  sorry

proof_of exampleTermFibers_exact := by
  -- REPAIR(T10-71): proof pending — identify both term-set fibers.
  sorry

proof_of exampleGraphSymbols_exact := by
  -- REPAIR(T10-71): proof pending — prove the five-symbol enumeration is exhaustive and injective.
  sorry

proof_of exampleE_exact := by
  -- REPAIR(T10-71): proof pending — extract the sole positive equation from the conjunction.
  sorry

proof_of exampleClosureClasses := by
  -- REPAIR(T10-72): proof pending — prove closure equals the displayed four-block partition.
  sorry

proof_of exampleGraphRanks := by
  cases e <;> rfl

proof_of exampleGraphLabels := by
  cases n <;> rfl

proof_of exampleGraphPorts := by
  cases n <;> rfl

proof_of examplePartition_exact := by
  rcases k with ⟨k, hk⟩
  have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> cases n <;>
    simp only [examplePartition, exampleClass] <;> decide +revert

proof_of exampleClosurePairs := by
  -- BEGIN PROOF
    -- Make the four nodes concrete by substituting their underlying values,
    -- so that `Lambda`, `delta`, `successorOfNode` all reduce.
    obtain ⟨pfabv, pfabm⟩ := pfab
    obtain ⟨pcv, pcm⟩ := pc
    obtain ⟨pgfabav, pgfabam⟩ := pgfaba
    obtain ⟨pgcav, pgcam⟩ := pgca
    simp only at hpfab hpc hpgfaba hpgca
    subst hpfab; subst hpc; subst hpgfaba; subst hpgca
    -- The positive equation `f(a,b) =̇_s c` is a conjunct of C, so the seed
    -- relation `E` already relates `pfab` and `pc`.
    have hEfab : exampleE ⟨⟨ExampleSort.s, exampleTerm_fab⟩, pfabm⟩
        ⟨⟨ExampleSort.s, exampleTerm_c⟩, pcm⟩ := by
      refine ⟨rfl, ExampleSort.s, exampleTerm_fab, exampleTerm_c, ?_, rfl, rfl⟩
      -- msConjunctContains C (eq_ rfl s fab c): it is the left conjunct.
      exact Or.inr (Or.inl rfl)
    have hfab : msCongruenceClosure (graphOfConjunction exampleConjunction)
        exampleE (positiveEquationRelation_sortSupported exampleConjunction) _ _ :=
      msCongruenceClosure_contains _ exampleE (positiveEquationRelation_sortSupported exampleConjunction) _ _ hEfab
    refine ⟨hfab, ?_⟩
    -- For `g(f(a,b),a) ~ g(c,a)` use backward closure (2b): same label `g`,
    -- and successors `f(a,b) ~ c` (from `hfab`) and `a ~ a` (reflexivity).
    have hrefl := (positiveClosure_equivalence exampleConjunction).refl
    have hbc2b := (msCongruenceClosure_isCongruence
      (graphOfConjunction exampleConjunction) exampleE
      (positiveEquationRelation_sortSupported exampleConjunction)).2.2.2
    -- The labels of both g-nodes are `ConjSymbol.func g` (definitional now).
    have hlab : (graphOfConjunction exampleConjunction).Lambda
          ⟨⟨ExampleSort.s, exampleTerm_gfaba⟩, pgfabam⟩
        = (graphOfConjunction exampleConjunction).Lambda
          ⟨⟨ExampleSort.s, exampleTerm_gca⟩, pgcam⟩ := rfl
    refine hbc2b _ _ hlab ?_
    intro i
    -- Case on the value of `i` (g has arity length 2).
    rcases i with ⟨iv, hiv⟩
    have hlen : iv < 2 := hiv
    rcases iv with _ | _ | iv
    · -- successor 0 of both nodes: f(a,b) and c, related by `hfab`.
      -- The successor nodes reduce definitionally; relate via `hfab`.
      have hp : ((graphOfConjunction exampleConjunction).delta
          ⟨⟨ExampleSort.s, exampleTerm_gfaba⟩, pgfabam⟩ ⟨0, hiv⟩)
          = ⟨⟨ExampleSort.s, exampleTerm_fab⟩, pfabm⟩ := node_eq_of_val_eq rfl
      have hq : ((graphOfConjunction exampleConjunction).delta
          ⟨⟨ExampleSort.s, exampleTerm_gca⟩, pgcam⟩ (hlab ▸ ⟨0, hiv⟩))
          = ⟨⟨ExampleSort.s, exampleTerm_c⟩, pcm⟩ := node_eq_of_val_eq rfl
      rw [hp, hq]; exact hfab
    · -- successor 1 of both nodes: `a`, related by reflexivity.
      have hpq : ((graphOfConjunction exampleConjunction).delta
          ⟨⟨ExampleSort.s, exampleTerm_gfaba⟩, pgfabam⟩ ⟨1, hiv⟩)
          = ((graphOfConjunction exampleConjunction).delta
          ⟨⟨ExampleSort.s, exampleTerm_gca⟩, pgcam⟩ (hlab ▸ ⟨1, hiv⟩)) :=
        node_eq_of_val_eq rfl
      rw [hpq]; exact hrefl _
    · -- iv ≥ 2 is impossible.
      omega


proof_of exampleCandidateTable :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

proof_of exampleConjunction_contains_neg := Or.inr (Or.inr rfl)
  -- BEGIN PROOF


proof_of exampleTerm_gfaba_mem := ⟨rfl, ExampleSort.s, exampleTerm_gfaba, exampleTerm_gca,
  -- BEGIN PROOF
      Or.inr exampleConjunction_contains_neg, Or.inl (msTermSubterms_self _)⟩


proof_of exampleTerm_gca_mem := ⟨rfl, ExampleSort.s, exampleTerm_gfaba, exampleTerm_gca,
  -- BEGIN PROOF
      Or.inr exampleConjunction_contains_neg, Or.inr (msTermSubterms_self _)⟩


proof_of exampleTerm_fab_mem := ⟨rfl, ExampleSort.s, exampleTerm_fab, exampleTerm_c,
  -- BEGIN PROOF
      Or.inl (Or.inr (Or.inl rfl)), Or.inl (msTermSubterms_self _)⟩


proof_of exampleTerm_c_mem := ⟨rfl, ExampleSort.s, exampleTerm_fab, exampleTerm_c,
  -- BEGIN PROOF
      Or.inl (Or.inr (Or.inl rfl)), Or.inr (msTermSubterms_self _)⟩


proof_of exampleCollision := by
  -- BEGIN PROOF
    -- The four relevant nodes of `G(C)`.
    refine ⟨rfl, exampleTerm_gfaba, exampleTerm_gca,
      ⟨⟨ExampleSort.s, exampleTerm_gfaba⟩, exampleTerm_gfaba_mem⟩,
      ⟨⟨ExampleSort.s, exampleTerm_gca⟩, exampleTerm_gca_mem⟩,
      exampleConjunction_contains_neg, rfl, rfl, ?_⟩
    -- The closure relates the two g-nodes (`exampleClosurePairs`, part 2),
    -- using the f-node and c-node as the related successors of index 0.
    exact (exampleClosurePairs
      ⟨⟨ExampleSort.s, exampleTerm_fab⟩, exampleTerm_fab_mem⟩
      ⟨⟨ExampleSort.s, exampleTerm_c⟩, exampleTerm_c_mem⟩
      ⟨⟨ExampleSort.s, exampleTerm_gfaba⟩, exampleTerm_gfaba_mem⟩
      ⟨⟨ExampleSort.s, exampleTerm_gca⟩, exampleTerm_gca_mem⟩
      rfl rfl rfl rfl).2


proof_of exampleDecision := by
  -- BEGIN PROOF
    -- The collision on the negated equation `¬(g(f(a,b),a) =̇ g(c,a))` yields
    -- unsatisfiability via the soundness direction of Lemma 10.6.2.
    obtain ⟨hL, r, v, p, q, hneg, hp, hq, hcol⟩ := exampleCollision
    exact collision_unsat_direction exampleConjunction
      ⟨hL, ExampleSort.s, r, v, p, q, hneg, hp, hq, hcol⟩


end LCS.FirstOrder.ManySorted.CongruenceClosure.Decision

end
