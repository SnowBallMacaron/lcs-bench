import LCS.FOResolution.Paramodulation

namespace LCS.FOResolution.Paramodulation

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FOResolution.Unification
open LCS.FOResolution.ClauseForm

proof_of paramodulant_isParamodulant := by
  exact ⟨choice, legal, result, computed, fun _ => Iff.rfl⟩

helper theorem substLitP_identity {L : Language} (lit : Literal L) :
    substLitP identitySubst lit = lit := by
  have h : ∀ t : Term L, termSubstAll t (Substitution.apply identitySubst) = t :=
    fun t => termSubstAll_identity t
  cases lit <;> rename_i atom <;> cases atom <;>
    simp only [substLitP, FOAtomCore.mapTerms, h]

helper theorem substClause_identity {L : Language} (A : Clause L) :
    substClause identitySubst A = A := by
  induction A with
  | nil => rfl
  | cons lit rest ih =>
    change substLitP identitySubst lit :: substClause identitySubst rest = lit :: rest
    rw [substLitP_identity, ih]

helper theorem identity_separating {L : Language} (A B : Clause L)
    (disjoint : ∀ n, A.vars n → ¬ B.vars n) :
    IsSeparatingPairP identitySubst identitySubst A B := by
  simpa [IsSeparatingPairP, SeparatingPairCore, identitySubst,
    FiniteSubstitution.identity, Method.substIsVarOnSet,
    Method.substInjectiveOnSet, Method.substRangeOnSet] using disjoint

proof_of exampleParents1_separating := by
  apply identity_separating
  intro n hA hB
  obtain ⟨a, ha, hva⟩ := hA
  obtain ⟨b, hb, hvb⟩ := hB
  have hb' := List.mem_singleton.mp hb
  subst b
  rcases List.mem_cons.mp ha with ha | ha
  · subst a
    simp [FOLiteralCore.vars, FOAtomCore.vars, termVars,
      mkF, mkG, mkH, mkA, pvec1, pvec2, mkPredP, mkPredQ, ExampleLang, Fin.exists_fin_succ] at hva hvb
    omega
  · have ha' := List.mem_singleton.mp ha
    subst a
    simp [FOLiteralCore.vars, FOAtomCore.vars, termVars,
      mkF, mkG, mkH, mkA, pvec1, pvec2, mkPredP, mkPredQ, ExampleLang, Fin.exists_fin_succ] at hva hvb
    omega

helper theorem subst_mkF (sigma : Nat → Term ExampleLang) (a b : Term ExampleLang) :
    termSubstAll (mkF a b) sigma = mkF (termSubstAll a sigma) (termSubstAll b sigma) := by
  change Term.func _ _ = Term.func _ _
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

helper theorem subst_mkG (sigma : Nat → Term ExampleLang) (a b : Term ExampleLang) :
    termSubstAll (mkG a b) sigma = mkG (termSubstAll a sigma) (termSubstAll b sigma) := by
  change Term.func _ _ = Term.func _ _
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

helper theorem subst_mkH (sigma : Nat → Term ExampleLang) (a : Term ExampleLang) :
    termSubstAll (mkH a) sigma = mkH (termSubstAll a sigma) := by
  change Term.func _ _ = Term.func _ _
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => rfl

proof_of exampleSubst1_finite := by
  match n with
  | 0 => simp at hn
  | 1 => simp at hn
  | n + 2 => rfl

proof_of exampleSubst1_images := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [subst_mkF, subst_mkH, termSubstAll, exampleSubst1, Substitution.apply]
  · simp only [subst_mkF, subst_mkH, mkA, termSubstAll, exampleSubst1, Substitution.apply]
  · simp only [subst_mkG, termSubstAll, exampleSubst1, Substitution.apply]
  · apply congrArg FOLiteralCore.pos
    apply congrArg (FOAtomCore.predN (L := ExampleLang) ExamplePred.P)
    funext i
    match i with | ⟨0, _⟩ => rfl

proof_of exampleParents2_separating := by
  apply identity_separating
  intro n hA hB
  obtain ⟨a, ha, hva⟩ := hA
  obtain ⟨b, hb, hvb⟩ := hB
  have hb' := List.mem_singleton.mp hb
  subst b
  have ha' := List.mem_singleton.mp ha
  subst a
  simp [FOLiteralCore.vars, FOAtomCore.vars, termVars,
    mkF', mkG', mkH', mkA', pvec1', pvec2', ExampleLang2, Fin.exists_fin_succ] at hva hvb
  omega

helper theorem subst_mkF' (sigma : Nat → Term ExampleLang2) (a b : Term ExampleLang2) :
    termSubstAll (mkF' a b) sigma = mkF' (termSubstAll a sigma) (termSubstAll b sigma) := by
  change Term.func _ _ = Term.func _ _
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

helper theorem subst_mkG' (sigma : Nat → Term ExampleLang2) (a : Term ExampleLang2) :
    termSubstAll (mkG' a) sigma = mkG' (termSubstAll a sigma) := by
  change Term.func _ _ = Term.func _ _
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => rfl

helper theorem subst_mkH' (sigma : Nat → Term ExampleLang2) (a : Term ExampleLang2) :
    termSubstAll (mkH' a) sigma = mkH' (termSubstAll a sigma) := by
  change Term.func _ _ = Term.func _ _
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => rfl

proof_of exampleSubst2_finite := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => simp at hn
  | 4 => simp at hn
  | n + 5 => rfl

proof_of exampleSubst2_images := by
  simp only [subst_mkF', subst_mkG', subst_mkH', mkA', termSubstAll,
    exampleSubst2, Substitution.apply, and_self]

proof_of example1_address_lookup := by
  exact ⟨rfl, rfl⟩

proof_of example1_address_replacement := by
  apply congrArg some
  apply congrArg FOLiteralCore.pos
  apply congrArg (FOAtomCore.predN (L := ExampleLang) ExamplePred.Q)
  funext i
  match i with
  | ⟨0, _⟩ =>
    apply congrArg (Term.func (L := ExampleLang) ExampleFunc.h)
    funext j
    match j with | ⟨0, _⟩ => rfl

proof_of exampleSubst1_isMGU := by
  refine ⟨⟨by simp, ?_⟩, ?_, ?_⟩
  · intro s t hs ht
    have image : ∀ u ∈ [mkF (Term.var 0) (mkH (Term.var 1)),
        mkF (mkH (Term.var 2)) (mkH mkA)],
        termSubstAll u exampleSubst1.apply = mkF (mkH (Term.var 2)) (mkH mkA) := by
      intro u hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
      rcases hu with rfl | rfl
      · exact exampleSubst1_images.1
      · exact exampleSubst1_images.2.1
    exact (image s hs).trans (image t ht).symm
  · intro x changed
    have member : x ∈ [0, 1] := by
      apply Classical.byContradiction
      intro outside
      exact changed (exampleSubst1_finite x outside)
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl <;>
      refine ⟨_, List.mem_cons_self .., ?_⟩ <;>
      simp [termFV, Set.iUnion, Set.singleton, mkF, mkH, pvec1, pvec2, ExampleLang, Fin.exists_fin_succ]
  · intro tau unified
    have h := unified.2 _ _ (List.mem_cons_self ..)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have args := eq_of_heq (Term.func.inj h).2
    have hx := congrFun args ⟨0, by decide⟩
    have hyh := congrFun args ⟨1, by decide⟩
    have hy := congrFun (eq_of_heq (Term.func.inj hyh).2) ⟨0, by decide⟩
    refine ⟨tau, ?_⟩
    intro x
    match x with
    | 0 => exact hx
    | 1 => exact hy
    | n + 2 => rfl

proof_of exampleSubst2_isMGU := by
  refine ⟨⟨by simp, ?_⟩, ?_, ?_⟩
  · intro s t hs ht
    have image : ∀ u ∈ [mkF' (Term.var 3) (Term.var 4),
        mkF' (mkG' (Term.var 0)) (Term.var 0)],
        termSubstAll u exampleSubst2.apply = mkF' (mkG' (Term.var 0)) (Term.var 0) := by
      intro u hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
      rcases hu with rfl | rfl
      · exact exampleSubst2_images.2.1
      · exact exampleSubst2_images.1
    exact (image s hs).trans (image t ht).symm
  · intro x changed
    have member : x ∈ [3, 4] := by
      apply Classical.byContradiction
      intro outside
      exact changed (exampleSubst2_finite x outside)
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl <;>
      refine ⟨_, List.mem_cons_self .., ?_⟩ <;>
      simp [termFV, Set.iUnion, Set.singleton, mkF', pvec2', ExampleLang2, Fin.exists_fin_succ]
  · intro tau unified
    have h := unified.2 _ _ (List.mem_cons_self ..)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have args := eq_of_heq (Term.func.inj h).2
    have hx := congrFun args ⟨0, by decide⟩
    have hy := congrFun args ⟨1, by decide⟩
    refine ⟨tau, ?_⟩
    intro x
    match x with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => exact hx
    | 4 => exact hy
    | n + 5 => rfl

proof_of exampleSelection1_legal := by
  have hA : exampleParents1.clauseA = clauseA_8_6_1 := substClause_identity _
  have hB : exampleParents1.clauseB = clauseB_8_6_1 := substClause_identity _
  refine ⟨?_, ?_, ?_, ?_, mkF (mkH (Term.var 2)) (mkH mkA), rfl, exampleSubst1_isMGU⟩
  · rw [hA]
    exact List.mem_cons_self ..
  · rw [hB]
    exact List.mem_cons_self ..
  · intro lit
    change lit ∈ [.pos (mkPredP (Term.var 0))] ↔ lit ∈ exampleParents1.clauseA ∧ _
    rw [hA]
    simp only [clauseA_8_6_1, List.mem_cons, List.mem_nil_iff, or_false]
    constructor
    · intro h
      subst lit
      exact ⟨Or.inr rfl, by intro h; cases h⟩
    · rintro ⟨h | h, hNe⟩
      · exact (hNe h).elim
      · exact h
  · intro lit
    simp [exampleSelection1, hB, clauseB_8_6_1]

helper theorem subst_predQ (sigma : Substitution ExampleLang) (t : Term ExampleLang) :
    substLitP sigma (.pos (mkPredQ t)) = .pos (mkPredQ (termSubstAll t sigma.apply)) := by
  apply congrArg FOLiteralCore.pos
  apply congrArg (FOAtomCore.predN (L := ExampleLang) ExamplePred.Q)
  funext i
  match i with | ⟨0, _⟩ => rfl

proof_of exampleSelection1_computes := by
  have replaced := example1_address_replacement (mkG (Term.var 0) (Term.var 1))
  change replaceLiteralAt exampleSelection1.recipient exampleSelection1.address
    exampleSelection1.right = some (.pos (mkPredQ (mkH (mkG (Term.var 0) (Term.var 1))))) at replaced
  unfold paramodulant
  change (replaceLiteralAt exampleSelection1.recipient exampleSelection1.address
    exampleSelection1.right).map _ = _
  rw [replaced]
  change some (substClause exampleSubst1
    [.pos (mkPredP (Term.var 0)), .pos (mkPredQ (mkH (mkG (Term.var 0) (Term.var 1))))]) = _
  simp only [substClause, List.map_cons, List.map_nil, exampleSubst1_images.2.2.2,
    subst_predQ, subst_mkH, exampleSubst1_images.2.2.1]

proof_of example1_ruleConsistent_isParamodulant := by
  refine ⟨exampleSelection1, exampleSelection1_legal, _, exampleSelection1_computes, ?_⟩
  intro lit
  simp only [ruleConsistentResult1, List.mem_cons, List.mem_nil_iff, or_false]
  exact or_comm

proof_of exampleSelection2_legal := by
  have hA : exampleParents2.clauseA = clauseB_8_6_2 := substClause_identity _
  have hB : exampleParents2.clauseB = clauseA_8_6_2 := substClause_identity _
  refine ⟨?_, ?_, ?_, ?_, mkF' (mkG' (Term.var 0)) (Term.var 0), rfl, exampleSubst2_isMGU⟩
  · rw [hA]
    exact List.mem_cons_self ..
  · rw [hB]
    exact List.mem_cons_self ..
  · intro lit
    simp [exampleSelection2, hA, clauseB_8_6_2]
  · intro lit
    simp [exampleSelection2, hB, clauseA_8_6_2]

proof_of examplePrintedSubst2_isMGU := by
  refine ⟨⟨by simp, ?_⟩, ?_, ?_⟩
  · intro s t hs ht
    have image : ∀ u ∈ [mkF' (Term.var 3) (Term.var 4),
        mkF' (mkG' (Term.var 0)) (Term.var 0)],
        termSubstAll u examplePrintedSubst2.apply = mkF' (mkG' (Term.var 4)) (Term.var 4) := by
      intro u hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
      rcases hu with rfl | rfl <;>
        simp only [subst_mkF', subst_mkG', termSubstAll, Substitution.apply, examplePrintedSubst2]
    exact (image s hs).trans (image t ht).symm
  · intro x changed
    have member : x ∈ [0, 3] := by
      apply Classical.byContradiction
      intro outside
      exact changed (examplePrintedSubst2.outsideSupport x outside)
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
      simp [termFV, Set.iUnion, Set.singleton, mkF', mkG', pvec1', pvec2',
        ExampleLang2, Fin.exists_fin_succ]
    · refine ⟨_, List.mem_cons_self .., ?_⟩
      simp [termFV, Set.iUnion, Set.singleton, mkF', pvec2', ExampleLang2, Fin.exists_fin_succ]
  · intro tau unified
    have h := unified.2 _ _ (List.mem_cons_self ..)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have args := eq_of_heq (Term.func.inj h).2
    have hx := congrFun args ⟨0, by decide⟩
    have hy := congrFun args ⟨1, by decide⟩
    change tau.map 3 = termSubstAll (mkG' (Term.var 0)) tau.map at hx
    rw [subst_mkG'] at hx
    change tau.map 4 = tau.map 0 at hy
    refine ⟨tau, ?_⟩
    intro x
    match x with
    | 0 => exact hy.symm
    | 1 => rfl
    | 2 => rfl
    | 3 =>
      change tau.map 3 = termSubstAll (mkG' (Term.var 4)) tau.map
      rw [subst_mkG']
      exact hx.trans (congrArg mkG' hy.symm)
    | n + 4 => rfl

proof_of examplePrintedSelection2_legal := by
  obtain ⟨donor, recipient, restA, restB, _⟩ := exampleSelection2_legal
  exact ⟨donor, recipient, restA, restB,
    mkF' (mkG' (Term.var 0)) (Term.var 0), rfl, examplePrintedSubst2_isMGU⟩

proof_of examplePrintedSelection2_computes := by
  change some [FOLiteralCore.pos (.eq_ (L := ExampleLang2) rfl
    (termSubstAll (mkH' (Term.var 4)) examplePrintedSubst2.apply)
    (termSubstAll (mkH' mkA') examplePrintedSubst2.apply))] = _
  simp only [subst_mkH']
  rfl

proof_of example2_leftSideRoot_printedResult := by
  exact paramodulant_isParamodulant exampleParents2 examplePrintedSelection2 _
    examplePrintedSelection2_legal examplePrintedSelection2_computes

proof_of general_resolution_step_simulated := by
  -- REPAIR(T8-70): proof pending
  sorry

proof_of general_resolution_refutation_simulated := by
  -- REPAIR(T8-70): proof pending
  sorry

proof_of binaryCounterexample_unsatisfiable := by
  intro model
  obtain ⟨M, satisfied⟩ := model
  let v : Assignment M := fun _ => M.interpConst ()
  have positive := satisfied _ (List.mem_cons_self ..) v
  have negative := satisfied _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) v
  have hp : M.interpPred () (fun _ => M.interpConst ()) := by
    obtain ⟨lit, member, holds⟩ := positive
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl <;> exact holds
  have hn : ¬ M.interpPred () (fun _ => M.interpConst ()) := by
    obtain ⟨lit, member, holds⟩ := negative
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl <;> exact holds
  exact hn hp

proof_of binary_only_incomplete := by
  refine ⟨binaryCounterexample_unsatisfiable, ?_⟩
  -- REPAIR(T8-70): proof pending
  sorry

proof_of binary_factoring_complete := by
  -- REPAIR(T8-70): proof pending
  sorry

end LCS.FOResolution.Paramodulation
