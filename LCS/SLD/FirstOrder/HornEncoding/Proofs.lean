import LCS.SLD.FirstOrder.HornEncoding

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



helper /-- Finite-set lowering is the exact image of formula lowering. -/
noncomputable def hashLowerFormulaFinset {L : Language} (k : Nat)
    (S : LCS.Finset (FormulaN (HashLanguage L))) :
    LCS.Finset (FormulaN L) :=
  LCS.Finset.image (hashLowerFormula k) S

helper /-- List lowering sends the empty list to the empty list. -/
theorem hashLowerFormulaList_nil {L : Language} (k : Nat) :
    hashLowerFormulaList (L := L) k [] = [] :=
  rfl



helper /-- List lowering commutes with append. -/
theorem hashLowerFormulaList_append {L : Language} (k : Nat)
    (xs ys : List (FormulaN (HashLanguage L))) :
    hashLowerFormulaList k (xs ++ ys) =
      hashLowerFormulaList k xs ++ hashLowerFormulaList k ys := by
  simp [hashLowerFormulaList, List.map_append]

helper /-- Pointwise lowering exactly cancels pointwise lifting. -/
theorem hashLowerFormulaList_hashLiftFormula {L : Language} (k : Nat)
    (xs : List (FormulaN L)) :
    hashLowerFormulaList k (xs.map hashLiftFormula) = xs := by
  induction xs with
  | nil => rfl
  | cons A rest ih =>
    change hashLowerFormula k (hashLiftFormula A) ::
        hashLowerFormulaList k (rest.map hashLiftFormula) = A :: rest
    rw [hashLowerFormula_hashLiftFormula, ih]

helper /-- Generic list-map transport: a pointwise commuting square induces a
    commuting square on lists. -/
theorem hashLowerFormulaList_map_of_commute {L : Language} (k : Nat)
    (xs : List (FormulaN (HashLanguage L)))
    (f : FormulaN (HashLanguage L) → FormulaN (HashLanguage L))
    (g : FormulaN L → FormulaN L)
    (hComm : ∀ A ∈ xs, hashLowerFormula k (f A) =
      g (hashLowerFormula k A)) :
    hashLowerFormulaList k (xs.map f) =
      (hashLowerFormulaList k xs).map g := by
  induction xs with
  | nil => rfl
  | cons A rest ih =>
    simp only [List.map, hashLowerFormulaList_cons]
    rw [hComm A List.mem_cons_self]
    congr 1
    exact ih (fun B hB => hComm B (List.mem_cons_of_mem _ hB))

helper /-- Freshness-qualified simultaneous-substitution transport on lists. -/
theorem hashLowerFormulaList_formulaSubstAll {L : Language} (k : Nat)
    (xs : List (FormulaN (HashLanguage L)))
    (σ : Nat → Term (HashLanguage L))
    (hFresh : ∀ A ∈ xs, ¬ formulaVars A k) :
    hashLowerFormulaList k
        (xs.map (fun A => formulaSubstAll A σ)) =
      (hashLowerFormulaList k xs).map
        (fun A => formulaSubstAll A (hashLowerSubst k σ)) := by
  apply hashLowerFormulaList_map_of_commute
  intro A hA
  exact hashLowerFormula_formulaSubstAll k A σ (hFresh A hA)

helper /-- Membership in the lowered finite set has an exact source witness. -/
theorem mem_hashLowerFormulaFinset {L : Language} (k : Nat)
    (B : FormulaN L)
    (S : LCS.Finset (FormulaN (HashLanguage L))) :
    B ∈ hashLowerFormulaFinset k S ↔
      ∃ A ∈ S, hashLowerFormula k A = B := by
  classical
  unfold hashLowerFormulaFinset
  exact LCS.Finset.mem_image

helper /-- Under groundness, membership of a lowered formula reflects and
    preserves membership of its exact source. -/
theorem hashLowerFormula_mem_finset_iff_of_ground {L : Language}
    (k : Nat) (A : FormulaN (HashLanguage L))
    (S : LCS.Finset (FormulaN (HashLanguage L)))
    (hA : ∀ x, ¬ formulaVars A x)
    (hS : ∀ B ∈ S, ∀ x, ¬ formulaVars B x) :
    hashLowerFormula k A ∈ hashLowerFormulaFinset k S ↔ A ∈ S := by
  constructor
  · intro h
    obtain ⟨B, hB, hEq⟩ :=
      (mem_hashLowerFormulaFinset k (hashLowerFormula k A) S).mp h
    have hBA : B = A :=
      hashLowerFormula_injective_of_ground k (hS B hB) hA hEq
    simpa [hBA] using hB
  · intro h
    exact (mem_hashLowerFormulaFinset k (hashLowerFormula k A) S).mpr
      ⟨A, h, rfl⟩

helper /-- Finite-set lowering preserves the empty set. -/
theorem hashLowerFormulaFinset_empty {L : Language} (k : Nat) :
    hashLowerFormulaFinset (L := L) k
      (∅ : LCS.Finset (FormulaN (HashLanguage L))) =
        (∅ : LCS.Finset (FormulaN L)) := by
  classical
  apply LCS.Finset.ext
  intro B
  constructor
  · intro h
    obtain ⟨A, hA, _⟩ :=
      (mem_hashLowerFormulaFinset k B
        (∅ : LCS.Finset (FormulaN (HashLanguage L)))).mp h
    exact (LCS.Finset.mem_empty A).mp hA |>.elim
  · intro h
    exact (LCS.Finset.mem_empty B).mp h |>.elim

helper /-- Finite-set lowering commutes with insertion. -/
theorem hashLowerFormulaFinset_insert {L : Language} (k : Nat)
    (A : FormulaN (HashLanguage L))
    (S : LCS.Finset (FormulaN (HashLanguage L))) :
    hashLowerFormulaFinset k (LCS.Finset.insert A S) =
      LCS.Finset.insert (hashLowerFormula k A)
        (hashLowerFormulaFinset k S) := by
  classical
  apply LCS.Finset.ext
  intro B
  constructor
  · intro h
    obtain ⟨C, hC, hEq⟩ :=
      (mem_hashLowerFormulaFinset k B (LCS.Finset.insert A S)).mp h
    cases (LCS.Finset.mem_insert.mp hC) with
    | inl hCA =>
      apply LCS.Finset.mem_insert.mpr
      left
      exact hEq.symm.trans (congrArg (hashLowerFormula k) hCA)
    | inr hCS =>
      apply LCS.Finset.mem_insert.mpr
      right
      exact (mem_hashLowerFormulaFinset k B S).mpr ⟨C, hCS, hEq⟩
  · intro h
    cases (LCS.Finset.mem_insert.mp h) with
    | inl hBA =>
      exact (mem_hashLowerFormulaFinset k B
        (LCS.Finset.insert A S)).mpr
          ⟨A, LCS.Finset.mem_insert.mpr (Or.inl rfl), hBA.symm⟩
    | inr hBS =>
      obtain ⟨C, hCS, hEq⟩ :=
        (mem_hashLowerFormulaFinset k B S).mp hBS
      exact (mem_hashLowerFormulaFinset k B
        (LCS.Finset.insert A S)).mpr
          ⟨C, LCS.Finset.mem_insert.mpr (Or.inr hCS), hEq⟩

helper /-- Finite-set lowering commutes with union. -/
theorem hashLowerFormulaFinset_union {L : Language} (k : Nat)
    (S T : LCS.Finset (FormulaN (HashLanguage L))) :
    hashLowerFormulaFinset k (S.union T) =
      (hashLowerFormulaFinset k S).union
        (hashLowerFormulaFinset k T) := by
  classical
  apply LCS.Finset.ext
  intro B
  constructor
  · intro h
    obtain ⟨A, hA, hEq⟩ :=
      (mem_hashLowerFormulaFinset k B (S.union T)).mp h
    apply LCS.Finset.mem_union.mpr
    exact (LCS.Finset.mem_union.mp hA).elim
      (fun hAS => Or.inl
        ((mem_hashLowerFormulaFinset k B S).mpr ⟨A, hAS, hEq⟩))
      (fun hAT => Or.inr
        ((mem_hashLowerFormulaFinset k B T).mpr ⟨A, hAT, hEq⟩))
  · intro h
    cases (LCS.Finset.mem_union.mp h) with
    | inl hBS =>
      obtain ⟨A, hAS, hEq⟩ :=
        (mem_hashLowerFormulaFinset k B S).mp hBS
      exact (mem_hashLowerFormulaFinset k B (S.union T)).mpr
        ⟨A, LCS.Finset.mem_union.mpr (Or.inl hAS), hEq⟩
    | inr hBT =>
      obtain ⟨A, hAT, hEq⟩ :=
        (mem_hashLowerFormulaFinset k B T).mp hBT
      exact (mem_hashLowerFormulaFinset k B (S.union T)).mpr
        ⟨A, LCS.Finset.mem_union.mpr (Or.inr hAT), hEq⟩

helper /-- Finite-set lowering of `ofList` is `ofList` of the lowered list. -/
theorem hashLowerFormulaFinset_ofList {L : Language} (k : Nat)
    (xs : List (FormulaN (HashLanguage L))) :
    hashLowerFormulaFinset k (LCS.Finset.ofList xs) =
      LCS.Finset.ofList (hashLowerFormulaList k xs) := by
  classical
  apply LCS.Finset.ext
  intro B
  constructor
  · intro h
    obtain ⟨A, hA, hEq⟩ :=
      (mem_hashLowerFormulaFinset k B (LCS.Finset.ofList xs)).mp h
    apply LCS.Finset.mem_ofList.mpr
    unfold hashLowerFormulaList
    exact List.mem_map.mpr
      ⟨A, LCS.Finset.mem_ofList.mp hA, hEq⟩
  · intro h
    have hList : B ∈ hashLowerFormulaList k xs :=
      LCS.Finset.mem_ofList.mp h
    unfold hashLowerFormulaList at hList
    obtain ⟨A, hA, hEq⟩ := List.mem_map.mp hList
    exact (mem_hashLowerFormulaFinset k B
      (LCS.Finset.ofList xs)).mpr
        ⟨A, LCS.Finset.mem_ofList.mpr hA, hEq⟩

helper /-- Generic finite-set image transport: a commuting square on members
    induces a commuting square on `LCS.Finset.image`. -/
theorem hashLowerFormulaFinset_image_of_commute {L : Language} (k : Nat)
    (S : LCS.Finset (FormulaN (HashLanguage L)))
    (f : FormulaN (HashLanguage L) → FormulaN (HashLanguage L))
    (g : FormulaN L → FormulaN L)
    (hComm : ∀ A ∈ S, hashLowerFormula k (f A) =
      g (hashLowerFormula k A)) :
    hashLowerFormulaFinset k (LCS.Finset.image f S) =
      LCS.Finset.image g (hashLowerFormulaFinset k S) := by
  classical
  apply LCS.Finset.ext
  intro C
  constructor
  · intro h
    obtain ⟨B, hB, hBC⟩ :=
      (mem_hashLowerFormulaFinset k C (LCS.Finset.image f S)).mp h
    obtain ⟨A, hA, hAB⟩ := LCS.Finset.mem_image.mp hB
    subst B
    apply LCS.Finset.mem_image.mpr
    refine ⟨hashLowerFormula k A, ?_, ?_⟩
    · exact (mem_hashLowerFormulaFinset k
        (hashLowerFormula k A) S).mpr ⟨A, hA, rfl⟩
    · exact (hComm A hA).symm.trans hBC
  · intro h
    obtain ⟨B, hB, hBC⟩ := LCS.Finset.mem_image.mp h
    obtain ⟨A, hA, hAB⟩ :=
      (mem_hashLowerFormulaFinset k B S).mp hB
    subst B
    apply (mem_hashLowerFormulaFinset k C
      (LCS.Finset.image f S)).mpr
    refine ⟨f A, LCS.Finset.mem_image.mpr ⟨A, hA, rfl⟩, ?_⟩
    exact (hComm A hA).trans hBC

helper /-- Freshness-qualified simultaneous-substitution transport through a
    finite-set image. -/
theorem hashLowerFormulaFinset_formulaSubstAll {L : Language} (k : Nat)
    (S : LCS.Finset (FormulaN (HashLanguage L)))
    (σ : Nat → Term (HashLanguage L))
    (hFresh : ∀ A ∈ S, ¬ formulaVars A k) :
    hashLowerFormulaFinset k
        (LCS.Finset.image (fun A => formulaSubstAll A σ) S) =
      LCS.Finset.image
        (fun A => formulaSubstAll A (hashLowerSubst k σ))
        (hashLowerFormulaFinset k S) := by
  apply hashLowerFormulaFinset_image_of_commute
  intro A hA
  exact hashLowerFormula_formulaSubstAll k A σ (hFresh A hA)

helper /-- Erase transport is valid on ground hash formulae.  Ground
    injectivity is precisely what rules out a second element collapsing
    onto the erased formula after lowering. -/
theorem hashLowerFormulaFinset_erase_of_ground {L : Language} (k : Nat)
    (A : FormulaN (HashLanguage L))
    (S : LCS.Finset (FormulaN (HashLanguage L)))
    (hA : ∀ x, ¬ formulaVars A x)
    (hS : ∀ B ∈ S, ∀ x, ¬ formulaVars B x) :
    hashLowerFormulaFinset k (S.erase A) =
      (hashLowerFormulaFinset k S).erase (hashLowerFormula k A) := by
  classical
  apply LCS.Finset.ext
  intro C
  constructor
  · intro h
    obtain ⟨B, hBErase, hEq⟩ :=
      (mem_hashLowerFormulaFinset k C (S.erase A)).mp h
    obtain ⟨hB, hBA⟩ := (LCS.Finset.mem_erase A B S).mp hBErase
    apply (LCS.Finset.mem_erase (hashLowerFormula k A) C
      (hashLowerFormulaFinset k S)).mpr
    refine ⟨(mem_hashLowerFormulaFinset k C S).mpr
      ⟨B, hB, hEq⟩, ?_⟩
    intro hCA
    have hLower : hashLowerFormula k B = hashLowerFormula k A :=
      hEq.trans hCA
    exact hBA
      (hashLowerFormula_injective_of_ground k (hS B hB) hA hLower)
  · intro h
    obtain ⟨hCS, hCA⟩ :=
      (LCS.Finset.mem_erase (hashLowerFormula k A) C
        (hashLowerFormulaFinset k S)).mp h
    obtain ⟨B, hB, hEq⟩ :=
      (mem_hashLowerFormulaFinset k C S).mp hCS
    apply (mem_hashLowerFormulaFinset k C (S.erase A)).mpr
    refine ⟨B, (LCS.Finset.mem_erase A B S).mpr ⟨hB, ?_⟩, hEq⟩
    intro hBA
    subst B
    exact hCA hEq.symm

helper /-- Combined erase/union transport, matching the index shape of one
    `FOSLDDerivation.step`. -/
theorem hashLowerFormulaFinset_erase_union_of_ground {L : Language}
    (k : Nat) (A : FormulaN (HashLanguage L))
    (S T : LCS.Finset (FormulaN (HashLanguage L)))
    (hA : ∀ x, ¬ formulaVars A x)
    (hS : ∀ B ∈ S, ∀ x, ¬ formulaVars B x) :
    hashLowerFormulaFinset k ((S.erase A).union T) =
      ((hashLowerFormulaFinset k S).erase (hashLowerFormula k A)).union
        (hashLowerFormulaFinset k T) := by
  rw [hashLowerFormulaFinset_union,
      hashLowerFormulaFinset_erase_of_ground k A S hA hS]













helper /-- Goal-side specialization of global freshness. -/
theorem hashFreshEvenVar_not_goal_clauseFV {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq))
    (c : FOHornClause L hNoEq) (hc : c ∈ goals) :
    ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) :=
  (hashFreshEvenVar_not_clauseFV (hNoEq := by all_goals exact hNoEq)) D goals c
    (List.mem_append.mpr (Or.inr hc))





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

namespace HashLanguageRegression

helper /-- The unique added symbol really has rank zero. -/
theorem HashLanguageRegression.hash_rank_zero :
    hashSkolemRank (0 : Fin 1) = 0 :=
  rfl

helper /-- The concrete hash term is closed. -/
theorem HashLanguageRegression.hash_closed :
    (@hashTerm exAddLang).isClosed :=
  hashTerm_isClosed

helper /-- The concrete hash term cannot be confused with a lifted base term. -/
theorem HashLanguageRegression.hash_not_lifted_zero :
    (@hashTerm exAddLang) ≠ hashLiftTerm zeroTm :=
  hashTerm_ne_hashLiftTerm zeroTm

helper /-- Equality-freeness is retained in the running SLD example language. -/
theorem HashLanguageRegression.hash_withoutEquality :
    (HashLanguage exAddLang).withoutEquality :=
  (HashLanguage_withoutEquality_iff exAddLang).mpr rfl

helper /-- Membership reflection instantiates on a nontrivial rule/fact list. -/
theorem HashLanguageRegression.lifted_rule_membership :
    (hashLiftHornClause (hNoEq := by all_goals rfl)) exAddClause_C2 ∈
      [exAddClause_C1, exAddClause_C2].map (hashLiftHornClause (hNoEq := by all_goals rfl)) := by
  rw [(hashLiftHornClause_mem_map_iff (hNoEq := by all_goals rfl))]
  simp

helper /-- The full Horn encoding is semantically preserved on the addition clauses. -/
theorem HashLanguageRegression.concrete_encoding_commutes
    (M : Structure (HashLanguage exAddLang)) (s : Assignment M) :
    formulaEvalN M (hashLiftFormula
        ((hornClauses_to_formulaN (hNoEq := by rfl)) (mkAdd zeroTm zeroTm zeroTm)
          [exAddClause_C1, exAddClause_C2])) s ↔
      formulaEvalN M ((hornClauses_to_formulaN (hNoEq := by rfl))
        (hashLiftFormula (mkAdd zeroTm zeroTm zeroTm))
        ([exAddClause_C1, exAddClause_C2].map (hashLiftHornClause (hNoEq := by rfl)))) s :=
  hashLiftFormula_hornClauses_to_formulaN (by rfl) _ _ M s

helper /-- A known allocation-free §7.6 specification stays allocation-free
    after being lifted to its hash language. -/
theorem HashLanguageRegression.lifted_zero_spec_has_no_allocations :
    (hashLiftSkolemSpec
      LCS.Herbrand.SHGTheorem.SkolemAllocationRegression.zeroSpec).n = 0 := by
  rw [hashLiftSkolemSpec_n]
  exact LCS.Herbrand.SHGTheorem.SkolemAllocationRegression.zero_exact

helper /-- Adversary: omitting the rigid `k` override makes substitution
    commutation fail even for the closed hash term. -/
theorem HashLanguageRegression.missing_rigidity_breaks_commutation :
    hashLowerTerm 2
        (termSubstAll (@hashTerm exAddLang)
          (fun _ => hashLiftTerm zeroTm)) ≠
      termSubstAll (hashLowerTerm 2 (@hashTerm exAddLang))
        (fun x => hashLowerTerm 2
          ((fun _ => hashLiftTerm zeroTm) x)) := by
  simp [hashTerm, hashLowerTerm, termSubstAll,
    hashLowerTerm_hashLiftTerm, zeroTm]

helper /-- Adversary: with the rigid lowering substitution, commutation still
    fails when the input contains the nonfresh variable `k`. -/
theorem HashLanguageRegression.nonfresh_variable_breaks_commutation :
    hashLowerTerm 2
        (termSubstAll (hashLiftTerm (Term.var 2 : Term exAddLang))
          (fun _ => hashLiftTerm zeroTm)) ≠
      termSubstAll
        (hashLowerTerm 2 (hashLiftTerm (Term.var 2 : Term exAddLang)))
        (hashLowerSubst 2 (fun _ => hashLiftTerm zeroTm)) := by
  simp [hashLiftTerm, LCS.Herbrand.SHGTheorem.liftTermSkolem,
    hashLowerTerm, termSubstAll, hashLowerSubst, zeroTm]

helper /-- Adversary: the hash term and the lifted base variable `k` are
    distinct sources but collide after lowering.  The lifted variable
    is non-ground, which is exactly why ground injectivity remains true. -/
theorem HashLanguageRegression.base_hash_collision_without_groundness :
    (@hashTerm exAddLang) ≠
        hashLiftTerm (Term.var 2 : Term exAddLang) ∧
      hashLowerTerm 2 (@hashTerm exAddLang) =
        hashLowerTerm 2
          (hashLiftTerm (Term.var 2 : Term exAddLang)) := by
  constructor
  · exact hashTerm_ne_hashLiftTerm _
  · rw [hashLowerTerm_hashTerm, hashLowerTerm_hashLiftTerm]

helper /-- Adversary: image does not commute with erase without the groundness
    hypothesis.  The two distinct source terms above collapse to one
    lowered variable, so erasing before versus after image differs. -/
theorem HashLanguageRegression.erase_transport_fails_without_groundness :
    LCS.Finset.image (hashLowerTerm 2)
        ((LCS.Finset.ofList
          [(@hashTerm exAddLang),
            hashLiftTerm (Term.var 2 : Term exAddLang)]).erase
              (@hashTerm exAddLang)) ≠
      (LCS.Finset.image (hashLowerTerm 2)
        (LCS.Finset.ofList
          [(@hashTerm exAddLang),
            hashLiftTerm (Term.var 2 : Term exAddLang)])).erase
              (hashLowerTerm 2 (@hashTerm exAddLang)) := by
  classical
  intro hEq
  have hLeft :
      (Term.var 2 : Term exAddLang) ∈
        LCS.Finset.image (hashLowerTerm 2)
          ((LCS.Finset.ofList
            [(@hashTerm exAddLang),
              hashLiftTerm (Term.var 2 : Term exAddLang)]).erase
                (@hashTerm exAddLang)) := by
    apply LCS.Finset.mem_image.mpr
    refine ⟨hashLiftTerm (Term.var 2 : Term exAddLang), ?_, ?_⟩
    · apply (LCS.Finset.mem_erase
        (@hashTerm exAddLang)
        (hashLiftTerm (Term.var 2 : Term exAddLang))
        (LCS.Finset.ofList
          [(@hashTerm exAddLang),
            hashLiftTerm (Term.var 2 : Term exAddLang)])).mpr
      refine ⟨LCS.Finset.mem_ofList.mpr (by simp), ?_⟩
      exact Ne.symm (hashTerm_ne_hashLiftTerm _)
    · exact hashLowerTerm_hashLiftTerm 2 _
  have hRight :
      ¬ (Term.var 2 : Term exAddLang) ∈
        (LCS.Finset.image (hashLowerTerm 2)
          (LCS.Finset.ofList
            [(@hashTerm exAddLang),
              hashLiftTerm (Term.var 2 : Term exAddLang)])).erase
                (hashLowerTerm 2 (@hashTerm exAddLang)) := by
    intro h
    have hNe := (LCS.Finset.mem_erase
      (hashLowerTerm 2 (@hashTerm exAddLang))
      (Term.var 2 : Term exAddLang)
      (LCS.Finset.image (hashLowerTerm 2)
        (LCS.Finset.ofList
          [(@hashTerm exAddLang),
            hashLiftTerm (Term.var 2 : Term exAddLang)]))).mp h |>.2
    exact hNe (hashLowerTerm_hashTerm 2).symm
  rw [hEq] at hLeft
  exact hRight hLeft

end HashLanguageRegression

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























helper /-- The universal-closure `foldr` produces a formula with empty FVN when
    the dedup list covers the base's free variables. -/
theorem formulaFVN_foldr_all_empty {L : Language}
    (fvs : List Nat) (base : FormulaN L)
    (hCover : ∀ n, LCS.FirstOrder.SyntaxN.Variables.formulaFVN base n → n ∈ fvs) :
    LCS.FirstOrder.SyntaxN.Variables.formulaFVN
      (fvs.foldr (fun v acc => FormulaN.all v acc) base) = ∅ := by
-- BEGIN PROOF
  ext n
  constructor
  · intro hmem
    have ⟨hFV, hNotIn⟩ := foldr_all_FV fvs base n hmem
    exact hNotIn (hCover n hFV)
  · intro hmem; exact hmem.elim





















proof_of horn_shg_bridge := by
  have hNotSat :
      ¬ satisfiableN ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals)) := by
    rw [(satisfiableN_hornClauseSet_iff (hNoEq := by all_goals exact hNoEq)) _ _ hNe]
    exact hUnsat
  have hNotSatSource : ¬ satisfiableN spec.source := hSpec ▸ hNotSat
  have hNotSatHash :
      ¬ satisfiableN (hashLiftSkolemSpec spec).source := by
    rw [hashLiftSkolemSpec_source]
    exact
      (unsatisfiableN_hashLiftFormula_iff spec.source).mpr hNotSatSource
  let specHash := hashLiftSkolemSpec spec
  let seedHash :
      {t : Term specHash.language // Term.isClosed t} :=
    ⟨LCS.Herbrand.SHGTheorem.liftTermSkolem
        (skolemRank := specHash.skolemRank) (@hashTerm L),
      (LCS.Herbrand.SHGTheorem.Herbrand.liftTermSkolem_termFV
        (skolemRank := specHash.skolemRank) (@hashTerm L)).trans
        (@hashTerm_isClosed L)⟩
  exact
    (LCS.Herbrand.SHGTheorem.Main.shgTheorem_unsat_seed
      specHash specHash.source rfl seedHash).mp hNotSatHash


helper /-- Helper: wrapping a base formula with universal quantifiers still
    evaluates to False in any model with nonempty domain, provided
    the base formula evaluates to False under every assignment. -/
theorem forallsFalsum_false {L : Language} (M : Structure L)
    (s : Assignment M) (fvs : List Nat)
    (base : FormulaN L)
    (hbase : ∀ s' : Assignment M, ¬ formulaEvalN M base s') :
    ¬ formulaEvalN M (fvs.foldr (fun v acc => FormulaN.all v acc) base) s := by
-- BEGIN PROOF
  induction fvs generalizing s with
  | nil => exact hbase s
  | cons v rest ih =>
    simp only [List.foldr, formulaEvalN]
    intro hAll
    obtain ⟨a⟩ := M.carrierNonempty
    exact ih (assignUpdate s v a) (hAll a)

helper theorem emptyClause_not_validIn {L : Language} (hNoEq : L.withoutEquality)  (M : Structure L)
    (A : FormulaN L)
    (fvs : List Nat) (s : Assignment M) :
    ¬ formulaEvalN M ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) A ([] : FOClause L hNoEq) fvs) s := by
-- BEGIN PROOF
  apply forallsFalsum_false
  intro s'
  simp [clauseToFormula, formulaEvalN, FormulaN.falsum]

end LCS.SLD.FirstOrder

end
