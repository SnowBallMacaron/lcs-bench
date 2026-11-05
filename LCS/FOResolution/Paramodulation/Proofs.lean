import LCS.FOResolution.Paramodulation

namespace LCS.FOResolution.Paramodulation

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FOResolution.Unification
open LCS.FOResolution.ClauseForm

helper theorem replaceAt_of_subtermAt {L : Language}
    (t : Term L) (addr : TreeAddress) (r replacement : Term L)
    (found : subtermAt t addr = some r) :
    ∃ newT, replaceAt t addr replacement = some newT := by
  induction addr generalizing t with
  | root => exact ⟨replacement, by cases t <;> rfl⟩
  | child n tail ih =>
    cases n with
    | zero => simp [subtermAt] at found
    | succ i =>
      cases t with
      | var x => simp [subtermAt] at found
      | const c => simp [subtermAt] at found
      | func f args =>
        by_cases hi : i < L.funArity f
        · simp only [subtermAt, hi, dite_true] at found
          obtain ⟨newT, hNew⟩ := ih (args ⟨i, hi⟩) found
          simp [replaceAt, hi, hNew]
        · simp [subtermAt, hi] at found

helper theorem replaceAtomAt_of_lookup {L : Language}
    (atom : FOAtomCore L) (addr : LiteralTermAddress) (r replacement : Term L)
    (found : literalSubtermAt (.pos atom) addr = some r) :
    ∃ newAtom, replaceAtomAt atom addr replacement = some newAtom := by
  cases atom with
  | predN p args =>
    cases addr with
    | equalityLeft suffix => simp [literalSubtermAt] at found
    | equalityRight suffix => simp [literalSubtermAt] at found
    | predicateArgument n suffix =>
      cases n with
      | zero => simp [literalSubtermAt] at found
      | succ i =>
        by_cases hi : i < L.predArity p
        · simp only [literalSubtermAt, hi, dite_true] at found
          obtain ⟨newT, hNew⟩ := replaceAt_of_subtermAt _ _ _ replacement found
          simp [replaceAtomAt, hi, hNew]
        · simp [literalSubtermAt, hi] at found
  | eq_ hEq s t =>
    cases addr with
    | predicateArgument n suffix => simp [literalSubtermAt] at found
    | equalityLeft suffix =>
      obtain ⟨newT, hNew⟩ := replaceAt_of_subtermAt s suffix r replacement found
      simp [replaceAtomAt, hNew]
    | equalityRight suffix =>
      obtain ⟨newT, hNew⟩ := replaceAt_of_subtermAt t suffix r replacement found
      simp [replaceAtomAt, hNew]

proof_of literalSubtermAt_replace_exists := by
  cases lit with
  | pos atom =>
    obtain ⟨newAtom, hNew⟩ := replaceAtomAt_of_lookup atom addr r replacement found
    exact ⟨.pos newAtom, by simp [replaceLiteralAt, hNew]⟩
  | neg atom =>
    obtain ⟨newAtom, hNew⟩ := replaceAtomAt_of_lookup atom addr r replacement found
    exact ⟨.neg newAtom, by simp [replaceLiteralAt, hNew]⟩

proof_of paramodulant_isParamodulant := by
  exact ⟨choice, legal, result, computed, fun _ => Iff.rfl⟩

proof_of legalParamodulation_computes := by
  obtain ⟨r, found, _⟩ := legal.2.2.2.2
  obtain ⟨newQ, hNew⟩ := literalSubtermAt_replace_exists choice.recipient choice.address r
    (choice.orientation.replacementSide choice.left choice.right) found
  have hComputed : paramodulant choice = some
      (substClause choice.sigma (choice.donorRemainder ++ [newQ] ++ choice.recipientRemainder)) := by
    simp [paramodulant, hNew]
  exact ⟨_, hComputed, paramodulant_isParamodulant parents choice _ legal hComputed⟩

proof_of paramodulation_leftToRight := by
  apply paramodulant_isParamodulant parents { choice with orientation := .leftToRight } _ legal
  simp only [paramodulant, ParamodulationOrientation.replacementSide, replaced, Option.map_some]

proof_of paramodulation_rightToLeft := by
  apply paramodulant_isParamodulant parents { choice with orientation := .rightToLeft } _ legal
  simp only [paramodulant, ParamodulationOrientation.replacementSide, replaced, Option.map_some]

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

proof_of identity_isLiteralMGU_singleton := by
  refine ⟨⟨by simp, ?_⟩, ?_, ?_⟩
  · intro l hl m hm
    have hl' := List.mem_singleton.mp hl
    have hm' := List.mem_singleton.mp hm
    subst l
    subst m
    rfl
  · intro x hx
    exact (hx rfl).elim
  · intro tau _
    exact ⟨tau, fun _ => rfl⟩

proof_of factor_identity := by
  refine ⟨[lit], identitySubst, ?_, ?_, identity_isLiteralMGU_singleton lit, ?_⟩
  · intro l hl
    have hl' := List.mem_singleton.mp hl
    subst l
    exact hLit
  · intro l hl m hm
    have hl' := List.mem_singleton.mp hl
    have hm' := List.mem_singleton.mp hm
    subst l
    subst m
    cases lit <;> rfl
  · intro l
    rw [substClause_identity]

proof_of empty_clause_has_no_factor := by
  rintro ⟨selected, sigma, hSubset, _, hMGU, _⟩
  cases selected with
  | nil => exact hMGU.1.1 rfl
  | cons lit rest =>
    exact List.not_mem_nil (hSubset lit (List.mem_cons_self ..))

proof_of binaryResolvent_empty_left := by
  rintro ⟨renameA, renameB, _, pivot, hPivot, _⟩
  exact List.not_mem_nil hPivot

proof_of mem_functionalReflexivityAxioms := by
  simp only [functionalReflexivityAxioms, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨f, ⟨occurs, positive⟩, equation⟩
    exact ⟨f, occurs, positive, equation⟩
  · rintro ⟨f, occurs, positive, equation⟩
    exact ⟨f, ⟨occurs, positive⟩, equation⟩

helper theorem functionalReflexivityAxiom_injective {L : Language}
    (hEq : L.hasEquality = true) (f g : L.funSymbols)
    (same : functionalReflexivityAxiom hEq f = functionalReflexivityAxiom hEq g) : f = g := by
  have head := congrArg (fun (C : Clause L) => C.head?.bind fun lit =>
    match lit with
    | .pos (.eq_ _ (.func h _) _) => some h
    | _ => none) same
  exact Option.some.inj head

proof_of functionalReflexivityAxioms_for_symbol := by
  rw [mem_functionalReflexivityAxioms]
  constructor
  · rintro ⟨g, occurs, positive, same⟩
    have equal := functionalReflexivityAxiom_injective hEq g f same
    subst g
    exact ⟨occurs, positive⟩
  · rintro ⟨occurs, positive⟩
    exact ⟨f, occurs, positive, rfl⟩

proof_of functionalReflexivityAxioms_empty := by
  rfl

proof_of functionalReflexivityAxiom_shape := by
  rfl

proof_of functionalReflexivity_variables_distinct := by
  intro same
  apply different
  apply Fin.ext
  exact Term.var.inj same

proof_of functionalReflexivityAxioms_alreadyPresent := by
  apply (mem_functionalReflexivityAxioms hEq S _).mpr
  refine ⟨f, ?_, positive, rfl⟩
  apply List.mem_flatMap.mpr
  refine ⟨functionalReflexivityAxiom hEq f, present, ?_⟩
  simp [functionalReflexivityAxiom, literalFunctionSymbolsCore, termFunctionSymbolsCore]

proof_of reflexivityAxiom_not_functional := by
  intro member
  obtain ⟨f, _, _, equation⟩ := (mem_functionalReflexivityAxioms hEq S _).mp member
  cases equation

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

proof_of exampleSubst1_printedConflict := by
  intro h
  cases h

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

proof_of exampleSubst2_leftSideRoot := by
  change some [FOLiteralCore.pos (.eq_ rfl (termSubstAll (mkH' (Term.var 4)) exampleSubst2.apply)
    (termSubstAll (mkH' mkA') exampleSubst2.apply))] = _
  rw [subst_mkH', subst_mkH']
  rfl

proof_of exampleSubst2_printedRenaming := by
  change [FOLiteralCore.pos (.eq_ rfl (termSubstAll (mkH' (Term.var 0)) exampleResultRename2.apply)
    (termSubstAll (mkH' mkA') exampleResultRename2.apply))] = _
  rw [subst_mkH', subst_mkH']
  rfl

proof_of substLitP_negativeEquality := by
  rfl

proof_of replaceLiteralAt_negativeEquality := by
  cases h : replaceAt s addr r <;> simp [replaceLiteralAt, replaceAtomAt, h]

proof_of distinct_predicates_not_unifiable := by
  intro h
  have heq := h.2 (.pos (mkPredP mkA)) (List.mem_cons_self ..)
    (.pos (mkPredQ mkA)) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hpq : ExamplePred.P = ExamplePred.Q := congrArg (fun lit =>
    match lit with
    | FOLiteralCore.pos (FOAtomCore.predN p _) => p
    | _ => ExamplePred.P) heq
  cases hpq

proof_of binaryEqualityUnits_separating := by
  apply identity_separating
  intro n hA _
  obtain ⟨lit, hLit, hVars⟩ := hA
  have heq := List.mem_singleton.mp hLit
  subst lit
  exact hVars.elim False.elim False.elim

proof_of binaryEqualityUnits_resolve := by
  let p : Literal ExampleLang := .pos (.eq_ rfl mkA mkA)
  let q : Literal ExampleLang := .neg (.eq_ rfl mkA mkA)
  refine ⟨identitySubst, identitySubst, binaryEqualityUnits_separating,
    p, List.mem_cons_self .., q, List.mem_cons_self .., identitySubst, ?_, ?_, ?_⟩
  · rfl
  · change IsLiteralMGU identitySubst [p, p]
    refine ⟨⟨by simp, ?_⟩, ?_, ?_⟩
    · intro l hl m hm
      simp only [List.mem_cons, List.mem_nil_iff, or_false, or_self] at hl hm
      subst l
      subst m
      rfl
    · intro x hx
      exact (hx rfl).elim
    · intro tau _
      exact ⟨tau, fun _ => rfl⟩
  · intro lit
    constructor
    · intro h
      exact (List.not_mem_nil h).elim
    · rintro (⟨source, hSource, hNe, _⟩ | ⟨source, hSource, hNe, _⟩)
      · exact (hNe (List.mem_singleton.mp hSource)).elim
      · exact (hNe (List.mem_singleton.mp hSource)).elim

proof_of distinct_predicates_not_complementary := by
  intro h
  have hpq : ExamplePred.P = ExamplePred.Q := congrArg (fun atom =>
    match atom with
    | FOAtomCore.predN p _ => p
    | _ => ExamplePred.P) h
  cases hpq

proof_of decodeLiteralAddress_root := by
  rfl

proof_of literalSubtermAt_predicateArgument := by
  simp [literalSubtermAt, subtermAt, i.isLt]

proof_of replaceLiteralAt_predicateArgument := by
  simp [replaceLiteralAt, replaceAtomAt, replaceAt, i.isLt]

proof_of literalSubtermAt_equalityRight := by
  exact ⟨rfl, rfl⟩

proof_of replaceLiteralAt_negativeEquality_right := by
  cases h : replaceAt t suffix r <;> simp [replaceLiteralAt, replaceAtomAt, h]

proof_of literalSubtermAt_zero_argument := by
  cases lit <;> rename_i atom <;> cases atom <;> rfl

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

proof_of paramodulation_reverse_regression := by
  let A : Clause ExampleLang := [.pos (mkPredP mkA), .pos (.eq_ rfl mkA (mkH mkA))]
  let B : Clause ExampleLang := [.pos (mkPredQ mkA), .neg (.eq_ rfl (mkH mkA) mkA)]
  have apart : IsSeparatingPairP identitySubst identitySubst A B := by
    apply identity_separating
    intro n hA _
    obtain ⟨lit, hMem, hVars⟩ := hA
    simp only [A, List.mem_cons, List.mem_nil_iff, or_false] at hMem
    rcases hMem with h | h <;> subst lit <;>
      simp [FOLiteralCore.vars, FOAtomCore.vars, termVars, mkPredP, mkA, mkH, pvec1, ExampleLang, Fin.exists_fin_succ] at hVars
  let parents : ParentOccurrences ExampleLang :=
    ⟨rfl, A, B, identitySubst, identitySubst, apart⟩
  have hPA : parents.clauseA = A := substClause_identity A
  have hPB : parents.clauseB = B := substClause_identity B
  let choice : ParamodulationSelection ExampleLang :=
    ⟨mkA, mkH mkA, .neg (.eq_ rfl (mkH mkA) mkA), [.pos (mkPredP mkA)],
      [.pos (mkPredQ mkA)], .equalityLeft .root, .rightToLeft, identitySubst⟩
  have legal : IsLegalParamodulationSelection parents choice := by
    refine ⟨?_, ?_, ?_, ?_, mkH mkA, rfl, ?_⟩
    · rw [hPA]
      exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · rw [hPB]
      exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · intro lit
      change lit ∈ [.pos (mkPredP mkA)] ↔
        lit ∈ parents.clauseA ∧ lit ≠ .pos (.eq_ rfl mkA (mkH mkA))
      rw [hPA]
      simp only [A, List.mem_cons, List.mem_nil_iff, or_false]
      constructor
      · intro h
        subst lit
        exact ⟨Or.inl rfl, by intro h; cases h⟩
      · rintro ⟨h | h, hNe⟩
        · exact h
        · exact (hNe h).elim
    · intro lit
      change lit ∈ [.pos (mkPredQ mkA)] ↔
        lit ∈ parents.clauseB ∧ lit ≠ .neg (.eq_ rfl (mkH mkA) mkA)
      rw [hPB]
      simp only [B, List.mem_cons, List.mem_nil_iff, or_false]
      constructor
      · intro h
        subst lit
        exact ⟨Or.inl rfl, by intro h; cases h⟩
      · rintro ⟨h | h, hNe⟩
        · exact h
        · exact (hNe h).elim
    · change IsMGU identitySubst [mkH mkA, mkH mkA]
      refine ⟨⟨by simp, ?_⟩, ?_, ?_⟩
      · intro t1 t2 h1 h2
        simp only [List.mem_cons, List.mem_nil_iff, or_false, or_self] at h1 h2
        subst t1
        subst t2
        rfl
      · intro x hx
        exact (hx rfl).elim
      · intro tau _
        exact ⟨tau, fun _ => rfl⟩
  refine ⟨parents, rfl, rfl, ?_⟩
  apply paramodulant_isParamodulant parents choice _ legal
  change some (substClause identitySubst
    [.pos (mkPredP mkA), .neg (.eq_ rfl mkA mkA), .pos (mkPredQ mkA)]) = _
  rw [substClause_identity]

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

proof_of example1_printed_obstruction := by
  intro same
  have member := (same (.pos (mkPredQ (mkH (mkG (mkH (Term.var 2)) mkA))))).mp
    (List.mem_cons_self ..)
  rcases List.mem_cons.mp member with h | h
  · have subterm := congrArg (fun lit => literalSubtermAt lit
      (.predicateArgument 1 (.child 1 (.child 2 .root)))) h
    change some mkA = some (mkH mkA) at subterm
    cases subterm
  · have h := List.mem_singleton.mp h
    have head := congrArg (fun lit => match lit with
      | FOLiteralCore.pos (.predN p _) => p
      | _ => ExamplePred.P) h
    cases head

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

proof_of exampleSelection2_computes := by
  exact exampleSubst2_leftSideRoot

proof_of example2_leftSideRoot_isParamodulant := by
  exact paramodulant_isParamodulant exampleParents2 exampleSelection2 _
    exampleSelection2_legal exampleSelection2_computes

proof_of example2_printed_address_obstruction := by
  rfl

proof_of example2_alternative_printedRenaming := by
  exact exampleSubst2_printedRenaming

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

proof_of paramodulation_complete_with_functional_reflexivity := by
  -- REPAIR(T8-71): proof pending
  sorry

proof_of paramodulation_complete_with_reflexivity := by
  -- REPAIR(T8-72): proof pending
  sorry

end LCS.FOResolution.Paramodulation
