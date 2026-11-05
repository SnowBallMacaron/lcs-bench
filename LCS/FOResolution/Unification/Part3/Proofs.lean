import LCS.FOResolution.Unification.Part3

section

namespace LCS.FOResolution.Unification

open LCS.FirstOrder.Basic

open LCS.FirstOrder.Syntax.FreeGeneration

open LCS.FirstOrder.SyntaxN.Variables

proof_of unifEx_isMGU_i := by
  refine ⟨⟨by simp, ?_⟩, ?_, ?_⟩
  · intro t u ht hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht hu
    rcases ht with rfl | rfl <;> rcases hu with rfl | rfl
    · rfl
    · exact unifEx_common_images_i.1.trans unifEx_common_images_i.2.symm
    · exact unifEx_common_images_i.2.trans unifEx_common_images_i.1.symm
    · rfl
  · intro x hx
    have hm : x ∈ unifEx_finite_mgu_i.support :=
      Classical.byContradiction (fun h => hx (unifEx_finite_mgu_i.outsideSupport x h))
    change x ∈ [0, 2] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨unifEx_t1_i, by simp, ⟨(0 : Fin 2), rfl⟩⟩
    · exact ⟨unifEx_t2_i, by simp, ⟨(1 : Fin 2), (0 : Fin 1), rfl⟩⟩
  · intro tau hTau
    have he := hTau.2 unifEx_t1_i unifEx_t2_i (by simp) (by simp)
    have hargs := eq_of_heq (Term.func.inj he).2
    have h0 := congrFun hargs (0 : Fin 2)
    have h1 := congrFun hargs (1 : Fin 2)
    have h12 := congrFun (eq_of_heq (Term.func.inj h1).2) (0 : Fin 1)
    change tau 1 = tau 2 at h12
    refine ⟨tau, ?_⟩
    intro x
    match x with
    | 0 => exact h0
    | 1 => rfl
    | 2 => exact h12.symm
    | n + 3 => rfl


proof_of unifEx_mostCommonInstance_i := by
  exact (mostCommonInstance_eq unifEx_finite_mgu_i
    [unifEx_t1_i, unifEx_t2_i] unifEx_isMGU_i unifEx_t2_i (by simp)).trans
      unifEx_common_images_i.2


proof_of unifEx_symbol_clash_ii := by
  have he := h.2 unifEx_t1_ii unifEx_t2_ii (by simp) (by simp)
  have hargs := eq_of_heq (Term.func.inj he).2
  have hg := congrFun hargs (1 : Fin 2)
  exact (Term.func.inj hg).1


proof_of unifEx_not_unifiable_ii := by
  rintro ⟨sigma, h⟩
  have clash := unifEx_symbol_clash_ii sigma h
  cases clash


proof_of unifEx_equations_iii := by
  have he := h.2 unifEx_t1_iii unifEx_t2_iii (by simp) (by simp)
  have hargs := eq_of_heq (Term.func.inj he).2
  have h0 := congrFun hargs (0 : Fin 3)
  have h1 := congrFun hargs (1 : Fin 3)
  have h2 := congrFun hargs (2 : Fin 3)
  have hinner := congrFun (eq_of_heq (Term.func.inj h1).2) (0 : Fin 1)
  exact ⟨h0, h2, h1, hinner, h2.symm.trans hinner⟩


proof_of unifEx_not_unifiable_iii := by
  rintro ⟨sigma, h⟩
  have hz := (unifEx_equations_iii sigma h).2.2.2.2
  exact (var_occurs_not_unifiable (L := unificationExampleLanguage3) 2
    (Term.func UnifExFunc3.g (unifVec1 (Term.var 2)))
    (by intro he; cases he) (by rfl)) ⟨sigma.map, hz⟩


proof_of unifier_iff_auxiliary_unifier := by
  -- BEGIN PROOF
    -- Case split on ts to resolve the match expression
    cases ts with
    | nil =>
      -- ts = []: arity of sharp is 0, so both sharp-terms are identical
      -- (Term.func sharp with no arguments). IsUnifierCore sigma [] is trivially true,
      -- and IsUnifierCore sigma' [t, t] is trivially true (both terms equal).
      simp only [List.length_nil] at h_arity_sharp
      constructor
      · intro _
        intro t1 t2 ht1 ht2
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht1 ht2
        rcases ht1 with rfl | rfl <;> rcases ht2 with rfl | rfl <;> try rfl
        all_goals (simp only [termSubstAll]; congr 1; funext i; exact (h_arity_sharp ▸ i).elim0)
      · intro _
        intro t1 t2 ht1 ht2; simp at ht1
    | cons hd tl =>
      -- ts = hd :: tl
      constructor
      · -- Forward: sigma unifies ts => lifted sigma unifies sharp-terms
        intro hUnif t1 t2 ht1 ht2
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht1 ht2
        -- Suffices to show the two sharp-terms unify under lifted sigma
        suffices key : termSubstAll
            (Term.func sharp (fun i => liftTerm ((hd :: tl).get (i.cast h_arity_sharp))))
            (fun x => liftTerm (sigma x)) =
          termSubstAll
            (Term.func sharp (fun _ => liftTerm hd))
            (fun x => liftTerm (sigma x)) by
          rcases ht1 with rfl | rfl <;> rcases ht2 with rfl | rfl
          · rfl
          · exact key
          · exact key.symm
          · rfl
        -- Both sides reduce via termSubstAll for func
        simp only [termSubstAll]
        congr 1; funext i
        -- LHS: termSubstAll (liftTerm ((hd :: tl)[i])) (liftTerm ∘ sigma)
        -- = liftTerm (termSubstAll ((hd :: tl)[i]) sigma)  by h_lift_subst
        rw [← h_lift_subst ((hd :: tl).get (i.cast h_arity_sharp))]
        -- RHS: termSubstAll (liftTerm hd) (liftTerm ∘ sigma)
        -- = liftTerm (termSubstAll hd sigma)  by h_lift_subst
        rw [← h_lift_subst hd]
        -- Now: liftTerm (termSubstAll ((hd::tl)[i]) sigma) = liftTerm (termSubstAll hd sigma)
        congr 1
        -- By IsUnifierCore: all terms in ts map to the same value
        apply hUnif
        · exact List.get_mem (hd :: tl) (i.cast h_arity_sharp)
        · exact .head _
      · -- Backward: lifted sigma unifies sharp-terms => sigma unifies ts
        -- Uses injectivity of liftTerm and injectivity of Term.func on arguments.
        intro hUnif t1 t2 ht1 ht2
        -- From hUnif, the two sharp-terms are equal under the lifted substitution.
        have key := hUnif
          (Term.func sharp (fun i => liftTerm ((hd :: tl).get (i.cast h_arity_sharp))))
          (Term.func sharp (fun _ => liftTerm hd))
          (.head _) (List.mem_cons.mpr (Or.inr (.head _)))
        -- Both sides reduce via termSubstAll for func
        simp only [termSubstAll] at key
        -- key : Term.func sharp (...) = Term.func sharp (...)
        -- By Term.func injectivity on arguments, all components agree.
        -- For any t ∈ (hd :: tl), show termSubstAll t sigma = termSubstAll hd sigma.
        have h_all_eq_hd : ∀ (j : Fin (hd :: tl).length),
            termSubstAll ((hd :: tl).get j) sigma = termSubstAll hd sigma := by
          intro j
          have hj_lt : j.val < L'.funArity sharp := by
            rw [h_arity_sharp]; exact j.isLt
          let idx : Fin (L'.funArity sharp) := ⟨j.val, hj_lt⟩
          -- Use injection on key to extract argument equality
          injection key with _hf_eq h_args_eq
          -- h_args_eq : (fun i => ...) = (fun _ => ...)
          have h_at_idx := congrFun h_args_eq idx
          rw [← h_lift_subst ((hd :: tl).get (idx.cast h_arity_sharp)),
              ← h_lift_subst hd] at h_at_idx
          have h_get_eq : (hd :: tl).get (idx.cast h_arity_sharp) = (hd :: tl).get j := by
            congr 1
          rw [h_get_eq] at h_at_idx
          exact h_lift_injective _ _ h_at_idx
        -- t1, t2 ∈ (hd :: tl), so their images under sigma are both equal to
        -- termSubstAll hd sigma.
        obtain ⟨i1, hi1⟩ := List.get_of_mem ht1
        obtain ⟨i2, hi2⟩ := List.get_of_mem ht2
        rw [← hi1, ← hi2, h_all_eq_hd i1, h_all_eq_hd i2]




helper theorem termSubstAll_eq_var_implies {L : Language}
    (t : Term L) (sigma : Nat → Term L) (x : Nat)
    (h : termSubstAll t sigma = Term.var x) :
    ∃ y, t = Term.var y ∧ sigma y = Term.var x := by
-- BEGIN PROOF
  cases t with
  | var y => exact ⟨y, rfl, h⟩
  | const c => simp [termSubstAll] at h
  | func f args => simp [termSubstAll] at h

helper theorem compose_roundtrip_implies_var_renaming {L : Language}
    (t : Term L) (rho rho' : Nat → Term L)
    (h : termSubstAll (termSubstAll t rho) rho' = t)
    (y : Nat) (hy : termFV t y) :
    ∃ w, rho y = Term.var w ∧ rho' w = Term.var y := by
-- BEGIN PROOF
  induction t with
  | var x =>
    have : y = x := hy
    subst this
    simp only [termSubstAll] at h
    exact termSubstAll_eq_var_implies (rho y) rho' y h
  | const c =>
    exact absurd hy id
  | func f args ih =>
    obtain ⟨j, hj⟩ : ∃ j, termFV (args j) y := hy
    simp only [termSubstAll] at h
    have h_arg : termSubstAll (termSubstAll (args j) rho) rho' = args j := by
      have hinj := Term.func.inj h
      exact congrFun (eq_of_heq hinj.2) j
    exact ih j h_arg hj

helper /-- Mutual factors send variables in the introduced/support-difference set
    to variables with a round trip under the reverse factor. -/
theorem mutualFactors_var {L : Language} (sigma theta rho inverse : Nat → Term L)
    (h : ∀ x, theta x = termSubstAll (sigma x) rho)
    (hi : ∀ x, sigma x = termSubstAll (theta x) inverse)
    (x : Nat)
    (hx : (SubstitutionCore.substIntroduced sigma ∪
      (SubstitutionCore.substSupport theta \ SubstitutionCore.substSupport sigma)) x) :
    ∃ y, rho x = Term.var y ∧ inverse y = Term.var x := by
  have round : ∀ z, termSubstAll (termSubstAll (sigma z) rho) inverse = sigma z := by
    intro z
    rw [← h z, ← hi z]
  rcases hx with ⟨z, _, hz⟩ | ⟨_, hx⟩
  · exact compose_roundtrip_implies_var_renaming (sigma z) rho inverse (round z) x hz
  · have hs : sigma x = Term.var x := Classical.byContradiction hx
    apply compose_roundtrip_implies_var_renaming (sigma x) rho inverse (round x) x
    rw [hs]
    exact rfl

helper /-- A variable image under a factor lies in the corresponding introduced/
    support-difference set of the factored substitution. -/
theorem factorImage_mem {L : Language} (sigma theta rho : Nat → Term L)
    (h : ∀ x, theta x = termSubstAll (sigma x) rho) (x y : Nat)
    (hx : (SubstitutionCore.substIntroduced sigma ∪
      (SubstitutionCore.substSupport theta \ SubstitutionCore.substSupport sigma)) x)
    (hxy : rho x = Term.var y) :
    (SubstitutionCore.substIntroduced theta ∪
      (SubstitutionCore.substSupport sigma \ SubstitutionCore.substSupport theta)) y := by
  rcases hx with ⟨z, hz, hzx⟩ | ⟨ht, hs⟩
  · have hv : termFV (theta z) y := by
      rw [h z, termFV_termSubstAll]
      exact ⟨x, hzx, by rw [hxy]; exact rfl⟩
    by_cases ht : SubstitutionCore.substSupport theta z
    · exact Or.inl ⟨z, ht, hv⟩
    · have he : theta z = Term.var z := Classical.byContradiction ht
      rw [he] at hv
      have hyz : y = z := hv
      subst y
      exact Or.inr ⟨hz, ht⟩
  · have he : sigma x = Term.var x := Classical.byContradiction hs
    apply Or.inl
    refine ⟨x, ht, ?_⟩
    rw [h x, he]
    change termFV (rho x) y
    rw [hxy]
    exact rfl

proof_of mgu_unique_up_to_renaming_relaxed := by
  classical
  obtain ⟨r, hr⟩ := h_sigma.2 theta h_theta.1
  obtain ⟨ri, hri⟩ := h_theta.2 sigma h_sigma.1
  let A : Set Nat := substIntroduced sigma ∪ (substSupport theta \ substSupport sigma)
  let B : Set Nat := substIntroduced theta ∪ (substSupport sigma \ substSupport theta)
  have hv : ∀ x, A x → ∃ y, r x = Term.var y ∧ ri y = Term.var x :=
    mutualFactors_var sigma.map theta.map r.map ri.map hr hri
  have hvi : ∀ y, B y → ∃ x, ri y = Term.var x ∧ r x = Term.var y :=
    mutualFactors_var theta.map sigma.map ri.map r.map hri hr
  have hm : ∀ x y, A x → r x = Term.var y → B y :=
    factorImage_mem sigma.map theta.map r.map hr
  have hmi : ∀ y x, B y → ri y = Term.var x → A x :=
    factorImage_mem theta.map sigma.map ri.map hri
  let rho : FiniteSubstitution L := {
    support := r.support
    map := fun x => if A x then r x else Term.var x
    outsideSupport := by
      intro x hx
      by_cases ha : A x
      · simp only [if_pos ha]
        exact r.outsideSupport x hx
      · simp only [if_neg ha] }
  let inverse : Nat → Term L := fun y => if B y then ri y else Term.var y
  have onA : ∀ x, A x → rho x = r x := by
    intro x hx
    exact if_pos hx
  have onB : ∀ y, B y → inverse y = ri y := by
    intro y hy
    exact if_pos hy
  have hsupp : substSupport rho ⊆ A := by
    intro x hx
    exact Classical.byContradiction (fun ha => hx (if_neg ha))
  have hfactor : ∀ x, theta x = substCompose sigma rho x := by
    intro x
    change theta x = termSubstAll (sigma x) rho
    by_cases hs : substSupport sigma x
    · rw [hr x]
      apply termSubstAll_ext_on_fv
      intro y hy
      exact (onA y (Or.inl ⟨x, hs, hy⟩)).symm
    · have he : sigma x = Term.var x := Classical.byContradiction hs
      rw [he]
      change theta x = rho x
      by_cases ha : A x
      · rw [onA x ha, hr x]
        change termSubstAll (sigma x) r = r x
        rw [he]
        rfl
      · have ht : ¬ substSupport theta x := fun ht => ha (Or.inr ⟨ht, hs⟩)
        have het : theta x = Term.var x := Classical.byContradiction ht
        exact het.trans (if_neg ha).symm
  have hvar : IsVarRenaming rho A := by
    intro x hx
    obtain ⟨y, hy, _⟩ := hv x hx
    exact ⟨y, (onA x hx).trans hy⟩
  refine ⟨rho, hfactor, ?_, hsupp, fun x hx => hvar x (hsupp x hx)⟩
  refine ⟨hvar, ?_, inverse, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, _⟩ := hv x hx
    exact ⟨y, hm x y hx hy, (onA x hx).trans hy⟩
  · intro y hy
    obtain ⟨x, hx, _⟩ := hvi y hy
    exact ⟨x, (onB y hy).trans hx⟩
  · intro y hy
    obtain ⟨x, hx, _⟩ := hvi y hy
    exact ⟨x, hmi y x hy hx, (onB y hy).trans hx⟩
  · intro x hx
    obtain ⟨y, hy, hiy⟩ := hv x hx
    rw [onA x hx, hy]
    exact (onB y (hm x y hx hy)).trans hiy
  · intro y hy
    obtain ⟨x, hx, hrx⟩ := hvi y hy
    rw [onB y hy, hx]
    exact (onA x (hmi y x hy hx)).trans hrx


proof_of mgu_unique_up_to_renaming := by
  exact mgu_unique_up_to_renaming_relaxed S sigma theta
    ⟨h_sigma.1, h_sigma.2.2⟩ ⟨h_theta.1, h_theta.2.2⟩


end LCS.FOResolution.Unification

end
