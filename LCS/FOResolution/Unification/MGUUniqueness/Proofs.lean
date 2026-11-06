import LCS.FOResolution.Unification.MGUUniqueness

section
namespace LCS.FOResolution.Unification
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.SyntaxN.Variables

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
