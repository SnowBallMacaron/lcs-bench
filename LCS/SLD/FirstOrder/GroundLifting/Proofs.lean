import LCS.SLD.FirstOrder.GroundLifting

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

helper /-- The adapter's outer substitution.  Odd variables encoding source-clause
    variables receive the rigidly lowered ground-instance substitution;
    every other variable, including the globally fresh even hash variable,
    is fixed. -/
noncomputable def hashTranscriptTheta {L : Language} (hNoEq : L.withoutEquality)
    (k : Nat) (sourceC : FOClause L hNoEq)
    (σ : Nat → Term (HashLanguage L)) : Nat → Term L :=
  fun y =>
    @dite (Term L)
      (y % 2 = 1 ∧ (clauseFV (hNoEq := by all_goals exact hNoEq)) sourceC (y / 2))
      (Classical.propDecidable _)
      (fun _ => hashLowerSubst k σ (y / 2))
      (fun _ => Term.var y)

helper /-- On the odd image of a source-clause variable, the adapter substitution
    returns its rigid hash-lowered instance. -/
theorem hashTranscriptTheta_odd {L : Language} (hNoEq : L.withoutEquality)
    (k : Nat) (sourceC : FOClause L hNoEq)
    (σ : Nat → Term (HashLanguage L))
    (x : Nat) (hx : (clauseFV (hNoEq := by all_goals exact hNoEq)) sourceC x) :
    (hashTranscriptTheta (hNoEq := by all_goals exact hNoEq)) k sourceC σ (2 * x + 1) =
      hashLowerSubst k σ x := by
  unfold hashTranscriptTheta
  have hMod : (2 * x + 1) % 2 = 1 := by omega
  have hDiv : (2 * x + 1) / 2 = x := by omega
  rw [dif_pos ⟨hMod, by simpa [hDiv] using hx⟩, hDiv]

helper /-- Every even variable is fixed by the adapter substitution. -/
theorem hashTranscriptTheta_even {L : Language} (hNoEq : L.withoutEquality)
    (k q : Nat) (hk : k = 2 * q)
    (sourceC : FOClause L hNoEq)
    (σ : Nat → Term (HashLanguage L)) :
    (hashTranscriptTheta (hNoEq := by all_goals exact hNoEq)) k sourceC σ k = Term.var k := by
  subst k
  unfold hashTranscriptTheta
  have hMod : (2 * q) % 2 = 0 := by omega
  rw [dif_neg]
  intro h
  omega

helper /-- The concrete odd renaming followed by the adapter substitution agrees
    with rigid lowering on every source-clause variable. -/
theorem hashTranscriptTheta_comp_rho {L : Language} (hNoEq : L.withoutEquality)
    (k : Nat) (sourceC : FOClause L hNoEq)
    (σ : Nat → Term (HashLanguage L))
    (x : Nat) (hx : (clauseFV (hNoEq := by all_goals exact hNoEq)) sourceC x) :
    SubstitutionCore.substCompose ((hashTranscriptTheta (hNoEq := by all_goals exact hNoEq)) k sourceC σ)
        ((sldLiftingSeparatingPairConcrete (hNoEq := by all_goals exact hNoEq)) sourceC) x =
      hashLowerSubst k σ x := by
  show termSubstAll ((sldLiftingSeparatingPairConcrete (hNoEq := by all_goals exact hNoEq)) sourceC x)
      ((hashTranscriptTheta (hNoEq := by all_goals exact hNoEq)) k sourceC σ) = _
  rw [(sldLiftingSeparatingPairConcrete_on_fv (hNoEq := by all_goals exact hNoEq)) sourceC x hx]
  exact (hashTranscriptTheta_odd (hNoEq := by all_goals exact hNoEq)) k sourceC σ x hx

helper /-- Structural atom lowering commutes with the ambient-formula view. -/
theorem hashLowerAtom_toFormula {L : Language} (hNoEq : L.withoutEquality)  (k : Nat)
    (A : FOAtom (HashLanguage L) hNoEq) :
    ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k A).toFormula =
      hashLowerFormula k A.toFormula := by
  cases A <;> rfl

helper /-- Lowering exactly cancels structural atom lifting. -/
theorem hashLowerAtom_hashLiftAtom {L : Language} (hNoEq : L.withoutEquality)  (k : Nat)
    (A : FOAtom L hNoEq) :
    (hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k ((hashLiftAtom (hNoEq := by all_goals exact hNoEq)) A) = A := by
  apply FOAtomCore.toFormula_injective
  rw [(hashLowerAtom_toFormula (hNoEq := by all_goals exact hNoEq)), (hashLiftAtom_toFormula (hNoEq := by all_goals exact hNoEq)),
    hashLowerFormula_hashLiftFormula]

helper /-- Freshness-qualified substitution commutation for structural atoms. -/
theorem hashLowerAtom_subst {L : Language} (hNoEq : L.withoutEquality)  (k : Nat)
    (A : FOAtom (HashLanguage L) hNoEq)
    (σ : Nat → Term (HashLanguage L))
    (hFresh : ¬ A.vars k) :
    (hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k ((A.subst (hNoEq := by all_goals exact hNoEq)) σ) =
      ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k A).subst (hNoEq := by all_goals exact hNoEq) (hashLowerSubst k σ) := by
  apply FOAtomCore.toFormula_injective
  rw [(hashLowerAtom_toFormula (hNoEq := by all_goals exact hNoEq)),
    (atomSubst_toFormula_formulaSubstAll (hNoEq := by all_goals exact hNoEq)),
    hashLowerFormula_formulaSubstAll,
    (atomSubst_toFormula_formulaSubstAll (hNoEq := by all_goals exact hNoEq)),
    (hashLowerAtom_toFormula (hNoEq := by all_goals exact hNoEq))]
  simpa only [← FOAtomCore.vars_eq_formulaVars] using hFresh

helper /-- Lowering a substituted lifted atom commutes with substitution when
    the distinguished variable is fresh in the source atom. -/
theorem hashLowerAtom_subst_hashLift {L : Language} (hNoEq : L.withoutEquality)
    (k : Nat) (A : FOAtom L hNoEq)
    (σ : Nat → Term (HashLanguage L))
    (hFresh : ¬ A.vars k) :
    (hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k (((hashLiftAtom (hNoEq := by all_goals exact hNoEq)) A).subst (hNoEq := by all_goals exact hNoEq) σ) =
      (A.subst (hNoEq := by all_goals exact hNoEq)) (hashLowerSubst k σ) := by
  rw [(hashLowerAtom_subst (hNoEq := by all_goals exact hNoEq)), (hashLowerAtom_hashLiftAtom (hNoEq := by all_goals exact hNoEq))]
  simpa only [(hashLiftAtom_vars (hNoEq := by all_goals exact hNoEq))] using hFresh

helper /-- Lowering a ground atom introduces only the distinguished variable. -/
theorem hashLowerAtom_vars_subset_singleton {L : Language} (hNoEq : L.withoutEquality)
    (k : Nat) (A : FOAtom (HashLanguage L) hNoEq)
    (hGround : ∀ x, ¬ A.vars x) :
    ∀ x, ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k A).vars x → x = k := by
  intro x hx
  apply hashLowerFormula_formulaVars_subset_singleton k A.toFormula
  · simpa only [← FOAtomCore.vars_eq_formulaVars] using hGround
  · have hx' :
        formulaVars ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k A).toFormula x := by
      rw [← FOAtomCore.vars_eq_formulaVars]
      exact hx
    rw [(hashLowerAtom_toFormula (hNoEq := by all_goals exact hNoEq))] at hx'
    exact hx'

helper /-- Atom lowering is injective on ground hash-language atoms. -/
theorem hashLowerAtom_injective_of_ground {L : Language} (hNoEq : L.withoutEquality)  (k : Nat)
    {A B : FOAtom (HashLanguage L) hNoEq}
    (hA : ∀ x, ¬ A.vars x)
    (hB : ∀ x, ¬ B.vars x)
    (h : (hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k A = (hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k B) :
    A = B := by
  apply FOAtomCore.toFormula_injective
  apply hashLowerFormula_injective_of_ground k
  · simpa only [← FOAtomCore.vars_eq_formulaVars] using hA
  · simpa only [← FOAtomCore.vars_eq_formulaVars] using hB
  · simpa only [← (hashLowerAtom_toFormula (hNoEq := by all_goals exact hNoEq))] using
      congrArg FOAtomCore.toFormula h

helper /-- Pointwise atom lowering on lists. -/
def hashLowerAtomList {L : Language} (hNoEq : L.withoutEquality)  (k : Nat)
    (xs : List (FOAtom (HashLanguage L) hNoEq)) : List (FOAtom L hNoEq) :=
  xs.map ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k)

helper
theorem hashLowerAtomList_subst_hashLift {L : Language} (hNoEq : L.withoutEquality)
    (k : Nat) (xs : List (FOAtom L hNoEq))
    (σ : Nat → Term (HashLanguage L))
    (hFresh : ∀ A ∈ xs, ¬ A.vars k) :
    (hashLowerAtomList (hNoEq := by all_goals exact hNoEq)) k
        ((xs.map (hashLiftAtom (hNoEq := by all_goals exact hNoEq))).map ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq)) σ)) =
      xs.map ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq)) (hashLowerSubst k σ)) := by
  induction xs with
  | nil => rfl
  | cons A rest ih =>
      simp only [List.map, hashLowerAtomList]
      rw [(hashLowerAtom_subst_hashLift (hNoEq := by all_goals exact hNoEq)) k A σ
        (hFresh A List.mem_cons_self)]
      congr 1
      simpa [hashLowerAtomList] using
        ih (fun B hB => hFresh B (List.mem_cons_of_mem _ hB))

helper
theorem hashLowerAtomFinset_union {L : Language} (hNoEq : L.withoutEquality)  (k : Nat)
    (S T : LCS.Finset (FOAtom (HashLanguage L) hNoEq)) :
    (hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k (S.union T) =
      ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k S).union ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k T) := by
  apply LCS.Finset.ext
  intro B
  constructor
  · intro h
    obtain ⟨A, hA, hEq⟩ :=
      ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k B (S.union T)).mp h
    exact (LCS.Finset.mem_union.mp hA).elim
      (fun hAS => LCS.Finset.mem_union.mpr <| Or.inl <|
        ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k B S).mpr ⟨A, hAS, hEq⟩)
      (fun hAT => LCS.Finset.mem_union.mpr <| Or.inr <|
        ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k B T).mpr ⟨A, hAT, hEq⟩)
  · intro h
    exact (LCS.Finset.mem_union.mp h).elim
      (fun hBS => by
        obtain ⟨A, hAS, hEq⟩ :=
          ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k B S).mp hBS
        exact ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k B (S.union T)).mpr
          ⟨A, LCS.Finset.mem_union.mpr (Or.inl hAS), hEq⟩)
      (fun hBT => by
        obtain ⟨A, hAT, hEq⟩ :=
          ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k B T).mp hBT
        exact ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k B (S.union T)).mpr
          ⟨A, LCS.Finset.mem_union.mpr (Or.inr hAT), hEq⟩)

helper
theorem hashLowerAtomFinset_ofList {L : Language} (hNoEq : L.withoutEquality)  (k : Nat)
    (xs : List (FOAtom (HashLanguage L) hNoEq)) :
    (hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k (LCS.Finset.ofList xs) =
      LCS.Finset.ofList ((hashLowerAtomList (hNoEq := by all_goals exact hNoEq)) k xs) := by
  apply LCS.Finset.ext
  intro B
  constructor
  · intro h
    obtain ⟨A, hA, hEq⟩ :=
      ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k B (LCS.Finset.ofList xs)).mp h
    exact LCS.Finset.mem_ofList.mpr <| List.mem_map.mpr
      ⟨A, LCS.Finset.mem_ofList.mp hA, hEq⟩
  · intro h
    rw [LCS.Finset.mem_ofList] at h
    obtain ⟨A, hA, hEq⟩ := List.mem_map.mp h
    exact ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k B
      (LCS.Finset.ofList xs)).mpr
        ⟨A, LCS.Finset.mem_ofList.mpr hA, hEq⟩

helper
theorem hashLowerAtomFinset_image_of_commute {L : Language} (hNoEq : L.withoutEquality)  (k : Nat)
    (S : LCS.Finset (FOAtom (HashLanguage L) hNoEq))
    (f : FOAtom (HashLanguage L) hNoEq → FOAtom (HashLanguage L) hNoEq)
    (g : FOAtom L hNoEq → FOAtom L hNoEq)
    (hComm : ∀ A ∈ S, (hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k (f A) =
      g ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k A)) :
    (hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k (LCS.Finset.image f S) =
      LCS.Finset.image g ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k S) := by
  apply LCS.Finset.ext
  intro C
  constructor
  · intro h
    obtain ⟨B, hB, hBC⟩ :=
      ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k C (LCS.Finset.image f S)).mp h
    obtain ⟨A, hA, rfl⟩ := LCS.Finset.mem_image.mp hB
    exact LCS.Finset.mem_image.mpr
      ⟨(hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k A,
        ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k A) S).mpr
          ⟨A, hA, rfl⟩,
        (hComm A hA).symm.trans hBC⟩
  · intro h
    obtain ⟨B, hB, hBC⟩ := LCS.Finset.mem_image.mp h
    obtain ⟨A, hA, rfl⟩ :=
      ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k B S).mp hB
    exact ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k C
      (LCS.Finset.image f S)).mpr
        ⟨f A, LCS.Finset.mem_image.mpr ⟨A, hA, rfl⟩,
          (hComm A hA).trans hBC⟩

helper
theorem hashLowerAtomFinset_subst {L : Language} (hNoEq : L.withoutEquality)  (k : Nat)
    (S : LCS.Finset (FOAtom (HashLanguage L) hNoEq))
    (σ : Nat → Term (HashLanguage L))
    (hFresh : ∀ A ∈ S, ¬ A.vars k) :
    (hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k
        (LCS.Finset.image ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq)) σ) S) =
      LCS.Finset.image ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq)) (hashLowerSubst k σ))
        ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k S) := by
  apply (hashLowerAtomFinset_image_of_commute (hNoEq := by all_goals exact hNoEq))
  intro A hA
  exact (hashLowerAtom_subst (hNoEq := by all_goals exact hNoEq)) k A σ (hFresh A hA)

helper
theorem hashLowerAtomFinset_erase_of_ground {L : Language} (hNoEq : L.withoutEquality)  (k : Nat)
    (A : FOAtom (HashLanguage L) hNoEq)
    (S : LCS.Finset (FOAtom (HashLanguage L) hNoEq))
    (hA : ∀ x, ¬ A.vars x)
    (hS : ∀ B ∈ S, ∀ x, ¬ B.vars x) :
    (hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k (S.erase A) =
      ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k S).erase ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k A) := by
  apply LCS.Finset.ext
  intro C
  constructor
  · intro h
    obtain ⟨B, hBErase, hEq⟩ :=
      ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k C (S.erase A)).mp h
    obtain ⟨hB, hBA⟩ := (LCS.Finset.mem_erase A B S).mp hBErase
    apply (LCS.Finset.mem_erase ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k A) C
      ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k S)).mpr
    refine ⟨((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k C S).mpr
      ⟨B, hB, hEq⟩, ?_⟩
    intro hCA
    exact hBA ((hashLowerAtom_injective_of_ground (hNoEq := by all_goals exact hNoEq)) k
      (hS B hB) hA (hEq.trans hCA))
  · intro h
    obtain ⟨hCS, hCA⟩ :=
      (LCS.Finset.mem_erase ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k A) C
        ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k S)).mp h
    obtain ⟨B, hB, hEq⟩ :=
      ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k C S).mp hCS
    apply ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k C (S.erase A)).mpr
    refine ⟨B, (LCS.Finset.mem_erase A B S).mpr ⟨hB, ?_⟩, hEq⟩
    intro hBA
    subst B
    exact hCA hEq.symm

helper
theorem hashLowerAtomFinset_erase_union_of_ground {L : Language} (hNoEq : L.withoutEquality)
    (k : Nat) (A : FOAtom (HashLanguage L) hNoEq)
    (S T : LCS.Finset (FOAtom (HashLanguage L) hNoEq))
    (hA : ∀ x, ¬ A.vars x)
    (hS : ∀ B ∈ S, ∀ x, ¬ B.vars x) :
    (hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k ((S.erase A).union T) =
      (((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k S).erase ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k A)).union
        ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k T) := by
  rw [(hashLowerAtomFinset_union (hNoEq := by all_goals exact hNoEq)),
    (hashLowerAtomFinset_erase_of_ground (hNoEq := by all_goals exact hNoEq)) k A S hA hS]

helper /-- The adapter substitution fixes the lowering of every ground
    hash-language formula. -/
theorem formulaSubstAll_hashLower_ground {L : Language} (hNoEq : L.withoutEquality)
    (k : Nat) (hkEven : ∃ q, k = 2 * q)
    (sourceC : FOClause L hNoEq)
    (σ : Nat → Term (HashLanguage L))
    (A : FormulaN (HashLanguage L))
    (hGround : ∀ x, ¬ formulaVars A x) :
    formulaSubstAll (hashLowerFormula k A)
        ((hashTranscriptTheta (hNoEq := by all_goals exact hNoEq)) k sourceC σ) =
      hashLowerFormula k A := by
  rw [show formulaSubstAll (hashLowerFormula k A)
      ((hashTranscriptTheta (hNoEq := by all_goals exact hNoEq)) k sourceC σ) =
      formulaSubstAll (hashLowerFormula k A) Term.var by
    apply formulaSubstAll_ext
    intro x hx
    have hxk :=
      hashLowerFormula_formulaVars_subset_singleton k A hGround x hx
    subst x
    obtain ⟨q, hq⟩ := hkEven
    exact (hashTranscriptTheta_even (hNoEq := by all_goals exact hNoEq)) k q hq sourceC σ]
  exact formulaSubstAll_id _

helper /-- Applying the adapter substitution to a lowered ground finite set is
    the identity image. -/
theorem image_formulaSubstAll_hashLowerFinset_ground {L : Language} (hNoEq : L.withoutEquality)
    (k : Nat) (hkEven : ∃ q, k = 2 * q)
    (sourceC : FOClause L hNoEq)
    (σ : Nat → Term (HashLanguage L))
    (S : LCS.Finset (FOAtom (HashLanguage L) hNoEq))
    (hGround : ∀ A ∈ S, ∀ x, ¬ A.vars x) :
    LCS.Finset.image
        ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq)) ((hashTranscriptTheta (hNoEq := by all_goals exact hNoEq)) k sourceC σ))
        ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k S) =
      (hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k S := by
  classical
  apply LCS.Finset.ext
  intro A
  constructor
  · intro hA
    obtain ⟨B, hB, hEq⟩ := LCS.Finset.mem_image.mp hA
    obtain ⟨C, hC, rfl⟩ :=
      ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k B S).mp hB
    have hFix :
        ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k C).subst (hNoEq := by all_goals exact hNoEq)
            ((hashTranscriptTheta (hNoEq := by all_goals exact hNoEq)) k sourceC σ) =
          (hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k C := by
      apply FOAtomCore.toFormula_injective
      rw [(atomSubst_toFormula_formulaSubstAll (hNoEq := by all_goals exact hNoEq)),
        (hashLowerAtom_toFormula (hNoEq := by all_goals exact hNoEq)),
        (formulaSubstAll_hashLower_ground (hNoEq := by all_goals exact hNoEq)) k hkEven sourceC σ C.toFormula]
      simpa only [← FOAtomCore.vars_eq_formulaVars] using hGround C hC
    rw [hFix] at hEq
    exact hEq ▸ ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k
      ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k C) S).mpr ⟨C, hC, rfl⟩
  · intro hA
    obtain ⟨C, hC, hEq⟩ :=
      ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k A S).mp hA
    apply LCS.Finset.mem_image.mpr
    refine ⟨(hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k C, ?_, ?_⟩
    · exact ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k
        ((hashLowerAtom (hNoEq := by all_goals exact hNoEq)) k C) S).mpr ⟨C, hC, rfl⟩
    · apply FOAtomCore.toFormula_injective
      rw [(atomSubst_toFormula_formulaSubstAll (hNoEq := by all_goals exact hNoEq)),
        (hashLowerAtom_toFormula (hNoEq := by all_goals exact hNoEq)),
        (formulaSubstAll_hashLower_ground (hNoEq := by all_goals exact hNoEq)) k hkEven sourceC σ C.toFormula]
      · have hEq' := congrArg FOAtomCore.toFormula hEq
        rw [(hashLowerAtom_toFormula (hNoEq := by all_goals exact hNoEq))] at hEq'
        exact hEq'
      · simpa only [← FOAtomCore.vars_eq_formulaVars] using hGround C hC

helper /-- All variables in the negative-clause view of a lowered ground goal
    equal the distinguished hash variable. -/
theorem clauseFV_hashLowerFormulaFinset_subset_singleton {L : Language} (hNoEq : L.withoutEquality)
    (k : Nat) (S : LCS.Finset (FOAtom (HashLanguage L) hNoEq))
    (hGround : ∀ A ∈ S, ∀ x, ¬ A.vars x) :
    ∀ x,
      (clauseFV (hNoEq := by all_goals exact hNoEq))
        (((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k S).toList.map FOLiteralCore.neg) x →
      x = k := by
  intro x hx
  obtain ⟨lit, hLit, hVar⟩ := hx
  rw [List.mem_map] at hLit
  obtain ⟨A, hAList, rfl⟩ := hLit
  have hA : A ∈ (hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k S :=
    (LCS.Finset.mem_toList
      ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k S) A).mp hAList
  obtain ⟨B, hB, hEq⟩ :=
    ((mem_hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k A S).mp hA
  subst A
  exact (hashLowerAtom_vars_subset_singleton (hNoEq := by all_goals exact hNoEq)) k B
    (hGround B hB) x hVar

helper /-- The globally fresh even variable makes the identity goal renaming and
    concrete odd source-clause renaming a separating pair after lowering. -/
theorem hashLowerFormulaFinset_separatingPair {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq))
    (c : FOHornClause L hNoEq)
    (S : LCS.Finset (FOAtom (HashLanguage L) hNoEq))
    (hGround : ∀ A ∈ S, ∀ x, ¬ A.vars x) :
    (IsSeparatingPair (L := L) (hNoEq := by all_goals exact hNoEq)) Term.var
      ((sldLiftingSeparatingPairConcrete (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)))
      (((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) S).toList.map
        FOLiteralCore.neg)
      (c.toFOClause (hNoEq := by all_goals exact hNoEq)) := by
  let k := (hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals
  have hkEven := (hashFreshEvenVar_even (hNoEq := by all_goals exact hNoEq)) D goals
  have hPrev :
      ∀ x,
        (clauseFV (hNoEq := by all_goals exact hNoEq))
          (((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) k S).toList.map FOLiteralCore.neg) x →
        x = k :=
    (clauseFV_hashLowerFormulaFinset_subset_singleton (hNoEq := by all_goals exact hNoEq)) k S hGround
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _
    exact ⟨x, rfl⟩
  · intro x hx
    rw [(sldLiftingSeparatingPairConcrete_on_fv (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) x hx]
    exact ⟨2 * x + 1, rfl⟩
  · intro x y _ _ h
    exact Term.var.inj h
  · intro x y hx hy h
    rw [(sldLiftingSeparatingPairConcrete_on_fv (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) x hx,
        (sldLiftingSeparatingPairConcrete_on_fv (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) y hy] at h
    have hxy := Term.var.inj h
    omega
  · funext n
    apply propext
    constructor
    · rintro ⟨⟨x, hx, hxn⟩, ⟨y, hy, hyn⟩⟩
      have hxk := hPrev x hx
      have hnk : n = k := by
        subst x
        exact (Term.var.inj hxn).symm
      have hny : n = 2 * y + 1 := by
        rw [(sldLiftingSeparatingPairConcrete_on_fv (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) y hy] at hyn
        exact (Term.var.inj hyn).symm
      obtain ⟨q, hkq⟩ := hkEven
      have hkq' : k = 2 * q := by
        simpa [k] using hkq
      rw [hnk, hkq'] at hny
      omega
    · intro h
      exact h.elim
  · intro _ _
    rfl
  · exact (sldLiftingSeparatingPairConcrete_off_fv (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq))

helper /-- The same fresh-variable invariant discharges the constructor's
    standard-apart side condition. -/
theorem hashLowerFormulaFinset_standardApart {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq))
    (c : FOHornClause L hNoEq) (hc : c ∈ D)
    (S : LCS.Finset (FOAtom (HashLanguage L) hNoEq))
    (hGround : ∀ A ∈ S, ∀ x, ¬ A.vars x) :
    ∀ x,
      (clauseFV (hNoEq := by all_goals exact hNoEq))
        (((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) S).toList.map
          FOLiteralCore.neg) x →
      ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) x := by
  intro x hx
  have hxk :=
    (clauseFV_hashLowerFormulaFinset_subset_singleton (hNoEq := by all_goals exact hNoEq))
      ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) S hGround x hx
  subst x
  exact (hashFreshEvenVar_not_program_clauseFV (hNoEq := by all_goals exact hNoEq)) D goals c hc

helper /-- The rigid lowering of the hash-language identity substitution is the
    base-language identity substitution. -/
theorem hashLowerSubst_var {L : Language} (k : Nat) :
    hashLowerSubst k (Term.var : Nat → Term (HashLanguage L)) =
      (Term.var : Nat → Term L) := by
  funext x
  by_cases hx : x = k
  · subst x
    exact hashLowerSubst_at k Term.var
  · exact hashLowerSubst_off k x Term.var hx

helper /-- The identity simultaneous-substitution image of a finite set is the
    finite set itself. -/
theorem image_formulaSubstAll_id {L : Language} (hNoEq : L.withoutEquality)
    (S : LCS.Finset (FOAtom L hNoEq)) :
    LCS.Finset.image ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) Term.var)) S = S := by
  classical
  apply LCS.Finset.ext
  intro A
  constructor
  · intro hA
    obtain ⟨B, hB, hEq⟩ := LCS.Finset.mem_image.mp hA
    rw [(atomSubst_id (hNoEq := by all_goals exact hNoEq))] at hEq
    exact hEq ▸ hB
  · intro hA
    exact LCS.Finset.mem_image.mpr ⟨A, hA, (atomSubst_id (hNoEq := by all_goals exact hNoEq)) A⟩

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

namespace HashGroundAdapterRegression

helper /-- Adversary: an exact lifted source cannot be replaced by a different
    base clause during source recovery. -/
theorem HashGroundAdapterRegression.recovered_source_unique {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)}
    {Dg : List (FOHornClause (HashLanguage L) (by all_goals exact hNoEq))}
    {prevHash : LCS.Finset (FOAtom (HashLanguage L) hNoEq)}
    {step : (GroundSLDStep (hNoEq := by all_goals exact hNoEq)) Dg prevHash}
    {sourceHash : FOHornClause (HashLanguage L) (by all_goals exact hNoEq)}
    {prev : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals
      ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) prevHash)}
    (adapted : (HashAdaptedGroundStep (hNoEq := by all_goals exact hNoEq)) D goals step sourceHash prev)
    (c : FOHornClause L hNoEq)
    (hLift : (hashLiftHornClause (hNoEq := by all_goals exact hNoEq)) c = sourceHash) :
    c = adapted.sourceClause := by
  apply (hashLiftHornClause_injective (hNoEq := by all_goals exact hNoEq))
  exact hLift.trans adapted.sourceLift.symm

helper /-- Adversary: once the first step has selected `earlier`, a distinct
    later atom cannot replace it. -/
theorem HashGroundAdapterRegression.later_selection_cannot_override {α : Type}
    (earlier later : α) (hNe : earlier ≠ later) :
    firstSelectedAppend (some earlier) (some later) ≠ some later := by
  simpa [firstSelectedAppend] using hNe

helper /-- Positive regression: a one-node correspondence directly produces a
    base-language derivation at the exactly lowered one-step goal and
    records that step's selection. -/
theorem HashGroundAdapterRegression.one_step_positive {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq))
    {Dg : List (FOHornClause (HashLanguage L) (by all_goals exact hNoEq))}
    {prevHash : LCS.Finset (FOAtom (HashLanguage L) hNoEq)}
    (prev : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals
      ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) prevHash))
    (step : (GroundSLDStep (hNoEq := by all_goals exact hNoEq)) Dg prevHash)
    (sourceHash : FOHornClause (HashLanguage L) (by all_goals exact hNoEq))
    (hSourceMem : sourceHash ∈ D.map (hashLiftHornClause (hNoEq := by all_goals exact hNoEq)))
    (σHash : Nat → Term (HashLanguage L))
    (hInst : step.clause =
      (substAllInHornClause (hNoEq := by all_goals exact hNoEq)) sourceHash σHash) :
    ∃ d : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals
        ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq))
          ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) step.nextGoal),
      (d.firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) =
        firstSelectedAppend (prev.firstSelectedAtom (hNoEq := by all_goals exact hNoEq))
          (some ((hashLowerAtom (hNoEq := by all_goals exact hNoEq))
            ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) step.Ak)) := by
  let t : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) Dg prevHash :=
    GroundSLDTranscript.cons step GroundSLDTranscript.nil
  let corr :
      (GroundSLDCorrespondence (hNoEq := by all_goals exact hNoEq))
        (D.map (hashLiftHornClause (hNoEq := by all_goals exact hNoEq))) Dg t :=
    GroundSLDCorrespondence.cons step GroundSLDTranscript.nil
      sourceHash hSourceMem σHash hInst GroundSLDCorrespondence.nil
  let adapted :=
    (hashAdaptGroundCorrespondence (hNoEq := by all_goals exact hNoEq)) D goals prev corr
  let d : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals
      ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq))
        ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) step.nextGoal) :=
    adapted.derivation
  refine ⟨d, ?_⟩
  calc
    (d.firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) = (adapted.derivation.firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) := rfl
    _ = firstSelectedAppend (prev.firstSelectedAtom (hNoEq := by all_goals exact hNoEq))
        (some ((hashLowerAtom (hNoEq := by all_goals exact hNoEq))
          ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) step.Ak)) := by
      simpa [t, GroundSLDTranscript.firstSelectedAtom] using
        adapted.firstSelected

helper /-- Positive regression: two correspondence nodes preserve the
    chronological first selection and finish at the exact lowering of
    the second node's output goal. -/
theorem HashGroundAdapterRegression.multi_step_positive {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq))
    {Dg : List (FOHornClause (HashLanguage L) (by all_goals exact hNoEq))}
    {prevHash : LCS.Finset (FOAtom (HashLanguage L) hNoEq)}
    (prev : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals
      ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) prevHash))
    (step₁ : (GroundSLDStep (hNoEq := by all_goals exact hNoEq)) Dg prevHash)
    (step₂ : (GroundSLDStep (hNoEq := by all_goals exact hNoEq)) Dg step₁.nextGoal)
    (sourceHash₁ sourceHash₂ : FOHornClause (HashLanguage L) (by all_goals exact hNoEq))
    (hSourceMem₁ : sourceHash₁ ∈ D.map (hashLiftHornClause (hNoEq := by all_goals exact hNoEq)))
    (hSourceMem₂ : sourceHash₂ ∈ D.map (hashLiftHornClause (hNoEq := by all_goals exact hNoEq)))
    (σHash₁ σHash₂ : Nat → Term (HashLanguage L))
    (hInst₁ : step₁.clause =
      (substAllInHornClause (hNoEq := by all_goals exact hNoEq)) sourceHash₁ σHash₁)
    (hInst₂ : step₂.clause =
      (substAllInHornClause (hNoEq := by all_goals exact hNoEq)) sourceHash₂ σHash₂) :
    ∃ d : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals
        ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq))
          ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) step₂.nextGoal),
      (d.firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) =
        firstSelectedAppend (prev.firstSelectedAtom (hNoEq := by all_goals exact hNoEq))
          (some ((hashLowerAtom (hNoEq := by all_goals exact hNoEq))
            ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) step₁.Ak)) := by
  let rest : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) Dg step₁.nextGoal :=
    GroundSLDTranscript.cons step₂ GroundSLDTranscript.nil
  let t : (GroundSLDTranscript (hNoEq := by all_goals exact hNoEq)) Dg prevHash :=
    GroundSLDTranscript.cons step₁ rest
  let restCorr :
      (GroundSLDCorrespondence (hNoEq := by all_goals exact hNoEq))
        (D.map (hashLiftHornClause (hNoEq := by all_goals exact hNoEq))) Dg rest :=
    GroundSLDCorrespondence.cons step₂ GroundSLDTranscript.nil
      sourceHash₂ hSourceMem₂ σHash₂ hInst₂
      GroundSLDCorrespondence.nil
  let corr :
      (GroundSLDCorrespondence (hNoEq := by all_goals exact hNoEq))
        (D.map (hashLiftHornClause (hNoEq := by all_goals exact hNoEq))) Dg t :=
    GroundSLDCorrespondence.cons step₁ rest
      sourceHash₁ hSourceMem₁ σHash₁ hInst₁ restCorr
  let adapted :=
    (hashAdaptGroundCorrespondence (hNoEq := by all_goals exact hNoEq)) D goals prev corr
  let d : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals
      ((hashLowerAtomFinset (hNoEq := by all_goals exact hNoEq))
        ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) step₂.nextGoal) :=
    adapted.derivation
  refine ⟨d, ?_⟩
  calc
    (d.firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) = (adapted.derivation.firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) := rfl
    _ = firstSelectedAppend (prev.firstSelectedAtom (hNoEq := by all_goals exact hNoEq))
        (some ((hashLowerAtom (hNoEq := by all_goals exact hNoEq))
          ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) step₁.Ak)) := by
      simpa [t, GroundSLDTranscript.firstSelectedAtom] using
        adapted.firstSelected

end HashGroundAdapterRegression

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













helper /-- Theorem 9.4.1 (required helper): Equational unfolding of `demoteTermOpt`
    on `Term.func (Sum.inl fL) args` when every subargument demotes to
    `some _`. Avoids the `dite`-based definition body and exposes the
    resulting `.func fL _` value directly. -/
theorem demoteTermOpt_func_Sum_inl
    {L : Language} {n : Nat} {skolemRank : Fin n → Nat}
    (fL : L.funSymbols)
    (args : Fin (L.funArity fL) →
      Term (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank))
    (hSome : ∀ i, (demoteTermOpt (args i)).isSome) :
    demoteTermOpt (L := L) (Term.func (Sum.inl fL) args) =
      some (Term.func fL (fun i => (demoteTermOpt (args i)).get (hSome i))) := by
-- BEGIN PROOF
  simp only [demoteTermOpt]
  rw [dif_pos hSome]

end LCS.SLD.FirstOrder

end
