import LCS.SLD.FirstOrder.Soundness

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

helper /-- formulaSubstAll preserves the atomic-constructor shape. The `predN`
    and `eq_` cases are preserved up to argument substitution; all other
    connectives remain non-atomic. -/
theorem formulaSubstAll_preserves_isAtomic {L : Language}
    (a : FormulaN L) (sigma : Nat → Term L) :
    FormulaN.isAtomic (formulaSubstAll a sigma) = FormulaN.isAtomic a := by
-- BEGIN PROOF
  cases a <;> simp [FormulaN.isAtomic, formulaSubstAll]





proof_of foSLDResolution_sound := by
  -- BEGIN PROOF
    -- Unfold unsatisfiability: show no structure satisfies all clause translations
    simp only [FOHornClauseSet.isUnsatisfiable, FOClauseSet.isUnsatisfiable]
    intro ⟨M, hSat⟩
    -- By sld_goal_invariant: clauseToFormula of current goal holds for all s
    have hInv := (sld_goal_invariant (hNoEq := by all_goals exact hNoEq)) Afalsum D goals d hGoalType M
      (fun C hC fvs _ => FOClause.universalClosure_of_validIn hNoEq M C (hSat C hC) Afalsum fvs)
    -- isRefutation: currentGoalVal = ∅
    have hEmpty : currentGoalVal = (∅ : LCS.Finset (FOAtom L hNoEq)) := hRef
    rw [hEmpty] at hInv
    -- `∅ : LCS.Finset _` has empty toList (via perm with []) so the mapped list is empty.
    have hToListEmpty : (∅ : LCS.Finset (FOAtom L hNoEq)).toList = [] := by
      have hEq := LCS.Finset.toList_ofList_eq (∅ : LCS.Finset (FOAtom L hNoEq))
      have hPerm : (∅ : LCS.Finset (FOAtom L hNoEq)).toList.Perm [] :=
        Quotient.exact hEq
      exact List.Perm.eq_nil hPerm
    rw [hToListEmpty] at hInv
    simp only [List.map] at hInv
    -- clauseToFormula [] is falsum Afalsum = Afalsum ∧ ¬Afalsum, a contradiction
    have hFalse := hInv (fun _ => Classical.choice M.carrierNonempty)
    simp only [clauseToFormula, FormulaN.falsum, formulaEvalN] at hFalse
    exact hFalse.2 hFalse.1


proof_of termSubstAll_var_ground := by
  -- BEGIN PROOF
    induction t with
    | var n => exact absurd rfl (hG n)
    | const _ => rfl
    | func f args ih =>
      show Term.func f _ = Term.func f _
      congr 1
      funext i
      exact ih i (fun x h => hG x ⟨i, h⟩)


proof_of formulaSubstAll_var_ground := by
  -- BEGIN PROOF
    induction A with
    | predN P ts =>
      show FormulaN.predN P _ = FormulaN.predN P _
      congr 1
      funext i
      exact termSubstAll_var_ground (ts i) (fun x h => hG x ⟨i, h⟩)
    | eq_ hL t1 t2 =>
      show FormulaN.eq_ hL _ _ = FormulaN.eq_ hL _ _
      rw [termSubstAll_var_ground t1 (fun x h => hG x (Or.inl h)),
          termSubstAll_var_ground t2 (fun x h => hG x (Or.inr h))]
    | conj A B ihA ihB =>
      show FormulaN.conj _ _ = FormulaN.conj _ _
      rw [ihA (fun x h => hG x (Or.inl h)),
          ihB (fun x h => hG x (Or.inr h))]
    | disj A B ihA ihB =>
      show FormulaN.disj _ _ = FormulaN.disj _ _
      rw [ihA (fun x h => hG x (Or.inl h)),
          ihB (fun x h => hG x (Or.inr h))]
    | impl A B ihA ihB =>
      show FormulaN.impl _ _ = FormulaN.impl _ _
      rw [ihA (fun x h => hG x (Or.inl h)),
          ihB (fun x h => hG x (Or.inr h))]
    | neg A ih =>
      show FormulaN.neg _ = FormulaN.neg _
      rw [ih hG]
    | all x A ih =>
      show FormulaN.all x _ = FormulaN.all x _
      rw [ih hG]
    | ex x A ih =>
      show FormulaN.ex x _ = FormulaN.ex x _
      rw [ih hG]


proof_of map_formulaSubstAll_var_ground := by
  -- BEGIN PROOF
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map]
      rw [formulaSubstAll_var_ground x (hG x List.mem_cons_self)]
      congr 1
      exact ih (fun a ha => hG a (List.mem_cons_of_mem _ ha))


proof_of formulaSubstAll_ext := by
  -- BEGIN PROOF
    rw [formulaSubstAll_eq_substFormula A sigma,
        formulaSubstAll_eq_substFormula A tau]
    exact substFormula_ext_vars A sigma tau h


proof_of formulaSubstAll_ground := by
  -- BEGIN PROOF
    rw [show formulaSubstAll A sigma = formulaSubstAll A Term.var from
        formulaSubstAll_ext A sigma Term.var
          (fun x hx => absurd hx (hG x))]
    exact formulaSubstAll_var_ground A hG


proof_of formulaSubstAll_comp := by
  -- BEGIN PROOF
    rw [formulaSubstAll_eq_substFormula A rho,
        formulaSubstAll_eq_substFormula _ theta,
        formulaSubstAll_eq_substFormula A (SubstitutionCore.substCompose theta rho)]
    exact substFormula_comp A theta rho


helper /-- Structural atom substitution is extensional on the variables of
    the atom. -/
theorem atomSubst_ext {L : Language} (hNoEq : L.withoutEquality)  (A : FOAtom L hNoEq)
    (sigma tau : Nat → Term L)
    (h : ∀ x, A.vars x → sigma x = tau x) :
    (FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) sigma A) = (A.subst (hNoEq := by all_goals exact hNoEq)) tau := by
  apply FOAtomCore.toFormula_injective
  rw [(atomSubst_toFormula_formulaSubstAll (hNoEq := by all_goals exact hNoEq)),
    (atomSubst_toFormula_formulaSubstAll (hNoEq := by all_goals exact hNoEq))]
  apply formulaSubstAll_ext
  simpa only [← FOAtomCore.vars_eq_formulaVars] using h

helper /-- An atom with no variables is fixed by every substitution. -/
theorem atomSubst_ground {L : Language} (hNoEq : L.withoutEquality)  (A : FOAtom L hNoEq)
    (sigma : Nat → Term L)
    (hG : ∀ x, ¬ A.vars x) :
    (FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) sigma A) = A := by
  apply FOAtomCore.toFormula_injective
  rw [(atomSubst_toFormula_formulaSubstAll (hNoEq := by all_goals exact hNoEq))]
  apply formulaSubstAll_ground
  simpa only [← FOAtomCore.vars_eq_formulaVars] using hG



proof_of isSeparatingPair_var_ground := by
  -- BEGIN PROOF
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx; exact absurd hx (hGA x)
    · intro x hx; exact absurd hx (hGB x)
    · intro x _ hx _ _; exact absurd hx (hGA x)
    · intro x _ hx _ _; exact absurd hx (hGB x)
    · funext _
      apply propext
      constructor
      · rintro ⟨⟨x, hx, _⟩, _⟩; exact absurd hx (hGA x)
      · intro h; exact absurd h id
    · intro _ _; rfl
    · intro _ _; rfl


proof_of sldDerivation_to_foSLD_ground := by
  -- BEGIN PROOF
    rw [(map_atomSubst_id (hNoEq := by all_goals exact hNoEq))] at hBody
    subst body
    refine ⟨t.finalGoal, (foldGroundTranscript (hNoEq := by all_goals exact hNoEq))
      (FOSLDDerivation.init (D := fun c => c ∈ D) (goals := goals) initGoal hInitMem) t, ?_⟩
    show t.finalGoal = (∅ : LCS.Finset (FOAtom L hNoEq))
    exact hRefEmpty




helper /-- Formula-body membership is preserved by substitution image (SQ16). -/
theorem bodyAtoms_substAllInHornClause {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) (σ : Nat → Term L) (A : FormulaN L) :
    A ∈ ((substAllInHornClause hNoEq c σ).bodyAtoms hNoEq) ↔
      A ∈ (c.bodyAtoms hNoEq).map (fun a => formulaSubstAll a σ) := by
  simp only [FOHornClause.bodyAtoms, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp
      ((bodyFOAtoms_substAllInHornClause hNoEq c σ a).mp ha)
    exact ⟨b.toFormula, ⟨b, hb, rfl⟩,
      (atomSubst_toFormula_formulaSubstAll hNoEq b σ).symm⟩
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨FOAtomCore.subst hNoEq σ b,
      (bodyFOAtoms_substAllInHornClause hNoEq c σ _).mpr
        (List.mem_map.mpr ⟨b, hb, rfl⟩),
      atomSubst_toFormula_formulaSubstAll hNoEq b σ⟩

helper /-- Simultaneous substitution preserves exactly the Horn-clause
    all-atoms-atomic side condition. -/
theorem allAtomsAtomic_substAllInHornClause_iff {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) (σ : Nat → Term L) :
    (((substAllInHornClause (hNoEq := by all_goals exact hNoEq)) c σ).allAtomsAtomic (hNoEq := by all_goals exact hNoEq)) ↔ (c.allAtomsAtomic (hNoEq := by all_goals exact hNoEq)) := by
  constructor <;> intro _
  · exact (FOHornClause.allAtomsAtomic_derived (hNoEq := by all_goals exact hNoEq)) c
  · exact (FOHornClause.allAtomsAtomic_derived (hNoEq := by all_goals exact hNoEq)) ((substAllInHornClause (hNoEq := by all_goals exact hNoEq)) c σ)

helper /-- Substitution commutes with the structural head view. -/
theorem headFOAtom_substAllInHornClause {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) (σ : Nat → Term L) :
    (((substAllInHornClause (hNoEq := by all_goals exact hNoEq)) c σ).headFOAtom (hNoEq := by all_goals exact hNoEq)) =
      c.headFOAtom.map ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq)) σ) := by
  cases c <;> rfl

helper /-- Theorem 9.4.1 (companion): Substitution commutes with `headAtom` up to
    `Option.map`. -/
theorem headAtom_substAllInHornClause {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) (σ : Nat → Term L) :
    (((substAllInHornClause (hNoEq := by all_goals exact hNoEq)) c σ).headAtom (hNoEq := by all_goals exact hNoEq)) =
      c.headAtom.map (fun a => formulaSubstAll a σ) := by
  cases c with
  | rule head body => exact congrArg some (atomSubst_toFormula_formulaSubstAll hNoEq head σ)
  | fact head => exact congrArg some (atomSubst_toFormula_formulaSubstAll hNoEq head σ)
  | goal body => rfl

proof_of lifting_lemma_foSLD_refutation := by
  -- REPAIR(CH9-ROOT): proof pending — statement truth open, see repairs/ch9/proof-debt.md
  -- DEBT(pre-existing, truth-open: see repairs/ch9/proof-debt.md CH9-ROOT row)
  sorry

proof_of atomic_no_eq_shape := by
  -- BEGIN PROOF
    cases a with
    | predN P args => exact ⟨P, args, rfl⟩
    | eq_ hL _ _ =>
      simp only [Language.withoutEquality] at hNoEq
      rw [hNoEq] at hL
      exact absurd hL (by decide)
    | neg _ => simp [FormulaN.isAtomic] at hAtomic
    | conj _ _ => simp [FormulaN.isAtomic] at hAtomic
    | disj _ _ => simp [FormulaN.isAtomic] at hAtomic
    | impl _ _ => simp [FormulaN.isAtomic] at hAtomic
    | all _ _ => simp [FormulaN.isAtomic] at hAtomic
    | ex _ _ => simp [FormulaN.isAtomic] at hAtomic


proof_of atomic_no_eq_same_pred := by
  -- BEGIN PROOF
    obtain ⟨P, args_a, haShape⟩ := atomic_no_eq_shape hNoEq a hAtomicA
    obtain ⟨Q, args_b, hbShape⟩ := atomic_no_eq_shape hNoEq b hAtomicB
    -- From `a = b` with `a = predN P args_a` and `b = predN Q args_b`,
    -- constructor injectivity gives `P = Q` and `args_a ≍ args_b`.
    subst haShape
    subst hbShape
    -- Now `hEq : predN P args_a = predN Q args_b`.
    cases hEq
    exact ⟨P, args_a, args_a, rfl, rfl, rfl⟩


proof_of sld_lifting_pairwise_unifier_witness := by
  -- BEGIN PROOF
    cases hHShape : headOrig with
    | eq_ hL lhs rhs =>
      rw [Language.withoutEquality] at hNoEq
      rw [hNoEq] at hL
      exact Bool.noConfusion hL
    | predN P args_headOrig =>
    -- `headA = formulaSubstAll headOrig sigma` by commuting substitution
    -- through `headAtom`.
      have hHeadASubst : headA = (FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) sigma headOrig) := by
        have hCommute := (headFOAtom_substAllInHornClause (hNoEq := by all_goals exact hNoEq)) sourceC sigma
        rw [hHeadOrig] at hCommute
        rw [← hInst] at hCommute
        rw [hStepHead] at hCommute
        simp only [Option.map_some] at hCommute
        exact Option.some_inj.mp hCommute
      have hAkShape : Ak = FOAtomCore.predN P
          (fun i => termSubstAll (args_headOrig i) sigma) := by
        rw [hUnifGround, hHeadASubst, hHShape]
        rfl
      let args_Ak : Fin (L.predArity P) → Term L :=
        fun i => termSubstAll (args_headOrig i) sigma
      have hArgsAk_def : args_Ak =
          fun i => termSubstAll (args_headOrig i) sigma :=
        rfl
      refine ⟨P, args_headOrig, args_Ak, rfl, hAkShape, ?_⟩
      intro p hp
      rw [List.mem_ofFn] at hp
      obtain ⟨i, hi⟩ := hp
      subst hi
      simp only [hArgsAk_def]
      have hArgGround :
          ∀ x, ¬ termFV (termSubstAll (args_headOrig i) sigma) x := by
        intro x hx
        apply hAkGround x
        rw [hAkShape]
        refine ⟨i, ?_⟩
        exact (termVars_iff_termFV _ x).mpr hx
      have heq1 :
          termSubstAll (termSubstAll (args_headOrig i) sigma) sigma =
          termSubstAll (termSubstAll (args_headOrig i) sigma) Term.var := by
        apply termSubstAll_ext
        intro x hx
        exact absurd hx (hArgGround x)
      have heq2 :
          termSubstAll (termSubstAll (args_headOrig i) sigma) Term.var =
          termSubstAll (args_headOrig i) sigma := by
        apply termSubstAll_var_ground
        intro x hx
        exact hArgGround x ((termVars_iff_termFV _ x).mp hx)
      exact (heq1.trans heq2).symm


proof_of sld_lifting_separating_pair := by
  -- BEGIN PROOF
    classical
    refine ⟨(fun x => if (clauseFV (hNoEq := by all_goals exact hNoEq)) sourceC x then Term.var (2 * x + 1)
                      else Term.var x), ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- substIsVarOnSet Term.var on clauseFV prevGoalLits: vacuous by hPrevGround.
      intro x hx
      exact absurd hx (hPrevGround x)
    · -- substIsVarOnSet ρ' on clauseFV sourceC: the if_pos branch gives Term.var.
      intro x hx
      simp only [if_pos hx]
      exact ⟨2 * x + 1, rfl⟩
    · -- substInjectiveOnSet Term.var on clauseFV prevGoalLits: vacuous by hPrevGround.
      intro x _ hx _ _
      exact absurd hx (hPrevGround x)
    · -- substInjectiveOnSet ρ' on clauseFV sourceC: 2 * x + 1 = 2 * y + 1 ⇒ x = y.
      intro x y hx hy h
      simp only [if_pos hx, if_pos hy] at h
      have := Term.var.inj h; omega
    · -- Range disjointness: first set is empty (clauseFV prevGoalLits is empty).
      funext n
      apply propext
      constructor
      · intro hmem
        obtain ⟨⟨x, hxA, _⟩, _⟩ := hmem
        exact absurd hxA (hPrevGround x)
      · intro h; exact h.elim
    · -- Support of Term.var: Term.var x = Term.var x trivially.
      intro _ _
      rfl
    · -- Support of ρ': on the else branch (x ∉ clauseFV sourceC) gives Term.var x.
      intro x hx
      simp only [if_neg hx]


proof_of sldLiftingSeparatingPairConcrete_on_fv := by
  -- BEGIN PROOF
    unfold sldLiftingSeparatingPairConcrete
    exact dif_pos hx


helper /-- The globally chosen hash variable is simultaneously absent from a
    source clause and outside that clause's concrete odd-renaming range. -/
theorem hashFreshEvenVar_source_disjoint {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq))
    (c : FOHornClause L hNoEq) (hc : c ∈ D ++ goals)
    (x : Nat) (hx : (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) x) :
    (¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals)) ∧
      (sldLiftingSeparatingPairConcrete (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) x ≠
        Term.var ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) := by
  refine ⟨(hashFreshEvenVar_not_clauseFV (hNoEq := by all_goals exact hNoEq)) D goals c hc, ?_⟩
  rw [(sldLiftingSeparatingPairConcrete_on_fv (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) x hx]
  exact Ne.symm ((hashFreshEvenVar_var_ne_odd (hNoEq := by all_goals exact hNoEq)) D goals x)

proof_of sldLiftingSeparatingPairConcrete_off_fv := by
  -- BEGIN PROOF
    unfold sldLiftingSeparatingPairConcrete
    exact dif_neg hx


proof_of sld_lifting_separating_pair_concrete := by
  -- BEGIN PROOF
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact absurd hx (hPrevGround x)
    · intro x hx
      rw [(sldLiftingSeparatingPairConcrete_on_fv (hNoEq := by all_goals exact hNoEq)) sourceC x hx]
      exact ⟨2 * x + 1, rfl⟩
    · intro x _ hx _ _
      exact absurd hx (hPrevGround x)
    · intro x y hx hy h
      rw [(sldLiftingSeparatingPairConcrete_on_fv (hNoEq := by all_goals exact hNoEq)) sourceC x hx,
          (sldLiftingSeparatingPairConcrete_on_fv (hNoEq := by all_goals exact hNoEq)) sourceC y hy] at h
      have := Term.var.inj h
      omega
    · funext n
      apply propext
      constructor
      · intro hmem
        obtain ⟨⟨x, hxA, _⟩, _⟩ := hmem
        exact absurd hxA (hPrevGround x)
      · intro h; exact h.elim
    · intro _ _; rfl
    · intro x hx
      exact (sldLiftingSeparatingPairConcrete_off_fv (hNoEq := by all_goals exact hNoEq)) sourceC x hx


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

namespace FOSLDDerivation



end FOSLDDerivation

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

namespace FOSLDDerivation

helper /-- Adding an outer step appends its selected atom only when the
    accumulator has no earlier resolution step. -/
theorem FOSLDDerivation.firstSelectedAtom_step_eq_append {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)}
    {prevGoal : LCS.Finset (FOAtom L hNoEq)}
    (prev : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) (fun c => c ∈ D) goals prevGoal)
    (clause : FOHornClause L hNoEq)
    (hClause : clause ∈ D)
    (hDef : (clause.isDefinite (hNoEq := by all_goals exact hNoEq)))
    (Ak headA : FOAtom L hNoEq)
    (hAk : Ak ∈ prevGoal)
    (hHead : (clause.headFOAtom (hNoEq := by all_goals exact hNoEq)) = some headA)
    (rho sigma : Nat → Term L)
    (hMGU : (IsAtomMGU (hNoEq := by all_goals exact hNoEq)) Ak ((FOAtomCore.subst (hNoEq := by all_goals exact hNoEq) rho headA)) sigma)
    (hSep : (IsSeparatingPair (L := L) (hNoEq := by all_goals exact hNoEq)) Term.var rho
      (prevGoal.toList.map FOLiteralCore.neg) (clause.toFOClause (hNoEq := by all_goals exact hNoEq)))
     :
    (firstSelectedAtom (hNoEq := by all_goals exact hNoEq))
        (FOSLDDerivation.step prev clause hClause hDef Ak headA
          hAk hHead rho sigma (isAtomMGU_toCore hNoEq hMGU) hSep ) =
      firstSelectedAppend (prev.firstSelectedAtom (hNoEq := by all_goals exact hNoEq)) (some Ak) := by
  induction prev generalizing clause Ak headA rho sigma with
  | init goal hGoal =>
    rfl
  | step prev' clause' hClause' hDef' Ak' headA' hAk' hHead'
      rho' sigma' hUnif' hSep' ih =>
    simp only [FOSLDDerivation.firstSelectedAtom]
    symm
    apply firstSelectedAppend_eq_left_of_ne_none
    exact (FOSLDDerivation.firstSelectedAtom_ne_none_of_length_pos (hNoEq := by all_goals exact hNoEq))
      (FOSLDDerivation.step prev' clause' hClause' hDef'
        Ak' headA' hAk' hHead' rho' sigma'
        hUnif' hSep' )
      (by simp [FOSLDDerivation.length])

end FOSLDDerivation

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

helper /-- Lowering preserves the outer atomic/non-atomic constructor exactly. -/
theorem hashLowerFormula_isAtomic {L : Language} (k : Nat)
    (A : FormulaN (HashLanguage L)) :
    FormulaN.isAtomic (hashLowerFormula k A) = FormulaN.isAtomic A := by
  cases A <;> rfl

helper /-- Lowering preserves quantifier-freeness exactly. -/
theorem hashLowerFormula_isQuantifierFree {L : Language} (k : Nat)
    (A : FormulaN (HashLanguage L)) :
    isQuantifierFree (hashLowerFormula k A) ↔ isQuantifierFree A := by
  induction A with
  | predN => rfl
  | eq_ => rfl
  | neg A ih => exact ih
  | conj A B ihA ihB => exact and_congr ihA ihB
  | disj A B ihA ihB => exact and_congr ihA ihB
  | impl A B ihA ihB => exact and_congr ihA ihB
  | all => rfl
  | ex => rfl

helper /-- Lowering a substituted lifted formula commutes with substitution when
    the globally reserved hash variable is absent from the source formula. -/
theorem hashLowerFormula_subst_hashLift {L : Language}
    (k : Nat) (A : FormulaN L)
    (σ : Nat → Term (HashLanguage L))
    (hFresh : ¬ formulaVars A k) :
    hashLowerFormula k (formulaSubstAll (hashLiftFormula A) σ) =
      formulaSubstAll A (hashLowerSubst k σ) := by
  rw [hashLowerFormula_formulaSubstAll]
  · rw [hashLowerFormula_hashLiftFormula]
  · rw [hashLiftFormula_formulaVars]
    exact hFresh

helper /-- List form of `hashLowerFormula_subst_hashLift`. -/
theorem hashLowerFormulaList_subst_hashLift {L : Language}
    (k : Nat) (xs : List (FormulaN L))
    (σ : Nat → Term (HashLanguage L))
    (hFresh : ∀ A ∈ xs, ¬ formulaVars A k) :
    hashLowerFormulaList k
        ((xs.map hashLiftFormula).map
          (fun A => formulaSubstAll A σ)) =
      xs.map (fun A => formulaSubstAll A (hashLowerSubst k σ)) := by
  induction xs with
  | nil => rfl
  | cons A rest ih =>
    simp only [List.map, hashLowerFormulaList_cons]
    rw [hashLowerFormula_subst_hashLift k A σ
      (hFresh A List.mem_cons_self)]
    congr 1
    exact ih (fun B hB => hFresh B (List.mem_cons_of_mem _ hB))

end LCS.SLD.FirstOrder

end

namespace LCS.SLD.FirstOrder.FOSLDDerivation
proof_of toResolutionDAG_exists := by
  -- REPAIR(T9-34): proof pending — certify the linear tree, extensional labels and empty endpoint
  sorry
end LCS.SLD.FirstOrder.FOSLDDerivation
