import LCS.Item
import LCS.Util
import LCS.FOResolution.Method
import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.Method.HerbrandBridge
import LCS.Herbrand.SHGTheorem.Main
import LCS.FOResolution.GroundResolution
import LCS.CutElim.LK
import LCS.FOResolution.Method.Completeness.Substitutions
import Attach
import LCS.FOResolution.Method.Completeness.Lifting.ProofsStamp

section
namespace LCS.FOResolution.Method.Completeness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.GroundResolution
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.HerbrandBridge
open LCS.CutElim.LK
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open Classical
-- ATTACH-BLOCKER: size baseline: retain helper in front
/-- Membership characterization for litSetUnifTerms: t is in the
    result iff it is an argument of some predN literal in the list. -/
theorem litSetUnifTerms_mem_iff {L : Language} (hNoEq : L.withoutEquality)
    {lits : List (FOLiteral L hNoEq)} {t : Term L} :
    t ∈ (litSetUnifTerms (hNoEq := by all_goals exact hNoEq)) lits ↔
    ∃ (P : L.predSymbols) (args : Fin (L.predArity P) → Term L)
      (i : Fin (L.predArity P)),
      (FOLiteralCore.pos (.predN P args) ∈ lits ∨
       FOLiteralCore.neg (.predN P args) ∈ lits) ∧
      t = args i := by
-- BEGIN PROOF
  constructor
  · intro ht
    have h := (litSetUnifTerms_mem_iff_foldl (hNoEq := hNoEq) (acc := []) (lits := lits) (t := t))
    simp only [List.not_mem_nil, false_or] at h
    exact h.mp (by unfold litSetUnifTerms at ht; exact ht)
  · intro ⟨P, args, i, hmem, heq⟩
    subst heq
    unfold litSetUnifTerms
    have h := (litSetUnifTerms_mem_iff_foldl (hNoEq := hNoEq) (acc := []) (lits := lits) (t := args i))
    simp only [List.not_mem_nil, false_or] at h
    exact h.mpr ⟨P, args, i, hmem, rfl⟩
-- ATTACH-BLOCKER: size baseline: retain helper in front
/-- litSetUnifTerms is monotone under IsSublist: if every literal in
    l1 appears in l2, then every term in litSetUnifTerms(l1) appears
    in litSetUnifTerms(l2). -/
theorem litSetUnifTerms_sublist_mem {L : Language} (hNoEq : L.withoutEquality)
    {l1 l2 : List (FOLiteral L hNoEq)} {t : Term L}
    (hsub : IsSublist l1 l2) (ht : t ∈ (litSetUnifTerms (hNoEq := by all_goals exact hNoEq)) l1) :
    t ∈ (litSetUnifTerms (hNoEq := by all_goals exact hNoEq)) l2 := by
-- BEGIN PROOF
  rw [(litSetUnifTerms_mem_iff (hNoEq := by all_goals exact hNoEq))] at ht ⊢
  obtain ⟨P, args, i, hmem, rfl⟩ := ht
  exact ⟨P, args, i, hmem.imp (fun h => hsub _ h) (fun h => hsub _ h), rfl⟩
-- ATTACH-BLOCKER: size baseline: retain helper in front
/-- Terms extracted from litSetUnifTerms of a ground clause are ground
    (have empty free variables). -/
theorem litSetUnifTerms_ground {L : Language} (hNoEq : L.withoutEquality)
    {lits : List (FOLiteral L hNoEq)} {t : Term L}
    (hGround : (FOClause.isGround (by all_goals exact hNoEq)) lits) (ht : t ∈ (litSetUnifTerms (hNoEq := by all_goals exact hNoEq)) lits) :
    termFV t = Set.empty := by
-- BEGIN PROOF
  rw [(litSetUnifTerms_mem_iff (hNoEq := by all_goals exact hNoEq))] at ht
  obtain ⟨P, args, i, hmem, rfl⟩ := ht
  ext n; constructor
  · intro h
    rcases hmem with hmem | hmem
    · have hlit_vars : (FOLiteral.vars (by all_goals exact hNoEq)) (FOLiteralCore.pos (FOAtomCore.predN P args)) n := by
        simp only [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars]
        exact ⟨i, (termVars_iff_termFV (args i) n).mpr h⟩
      have : (FOClause.vars (by all_goals exact hNoEq)) lits n := ⟨_, hmem, hlit_vars⟩
      dsimp only [FOClause.vars] at this; rw [hGround] at this; exact this
    · have hlit_vars : (FOLiteral.vars (by all_goals exact hNoEq)) (FOLiteralCore.neg (FOAtomCore.predN P args)) n := by
        simp only [FOLiteral.vars, FOLiteralCore.vars, FOAtomCore.vars]
        exact ⟨i, (termVars_iff_termFV (args i) n).mpr h⟩
      have : (FOClause.vars (by all_goals exact hNoEq)) lits n := ⟨_, hmem, hlit_vars⟩
      dsimp only [FOClause.vars] at this; rw [hGround] at this; exact this
  · intro h; exact h.elim
-- ATTACH-BLOCKER: size baseline: retain helper in front
/-- substLit commutes with conjugation. -/
theorem substLit_conjugate {L : Language} (hNoEq : L.withoutEquality) (sigma : Nat → Term L)
    (lit : FOLiteral L hNoEq) :
    (substLit (hNoEq := by all_goals exact hNoEq)) sigma ((FOLiteral.conjugate (by all_goals exact hNoEq)) lit) =
    (FOLiteral.conjugate (by all_goals exact hNoEq)) ((substLit (hNoEq := by all_goals exact hNoEq)) sigma lit) := by
-- BEGIN PROOF
  cases lit with
  | pos B => simp [substLit, FOLiteral.conjugate, FOLiteralCore.conjugate]
  | neg B => simp [substLit, FOLiteral.conjugate, FOLiteralCore.conjugate]
-- ATTACH-BLOCKER: size baseline: retain helper in front
/-- substLits commutes with LitSetConjugate. -/
theorem substLits_LitSetConjugate {L : Language} (hNoEq : L.withoutEquality) (sigma : Nat → Term L)
    (lits : List (FOLiteral L hNoEq)) :
    (substLits (hNoEq := by all_goals exact hNoEq)) sigma ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) lits) =
    (LitSetConjugate (hNoEq := by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) sigma lits) := by
-- BEGIN PROOF
  simp only [substLits, LitSetConjugate, List.map_map]
  congr 1; funext lit
  cases lit with
  | pos B => simp [substLit, FOLiteral.conjugate, FOLiteralCore.conjugate]
  | neg B => simp [substLit, FOLiteral.conjugate, FOLiteralCore.conjugate]
-- ATTACH-BLOCKER: size baseline: retain helper in front
/-- LitSetConjugate preserves groundness: the conjugate of every
    literal in a ground clause still has no free variables. -/
theorem isGround_LitSetConjugate {L : Language} (hNoEq : L.withoutEquality)
    (lits : List (FOLiteral L hNoEq))
    (hGround : (FOClause.isGround (by all_goals exact hNoEq)) lits) :
    (FOClause.isGround (by all_goals exact hNoEq)) ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) lits) := by
-- BEGIN PROOF
  ext m; constructor
  · intro ⟨lit, hlit, hv⟩
    simp only [LitSetConjugate, List.mem_map] at hlit
    obtain ⟨lit', hlit', rfl⟩ := hlit
    have : (FOLiteral.vars (by all_goals exact hNoEq)) lit' m := by
      cases lit' with
      | pos B =>
        simp [FOLiteral.conjugate, FOLiteralCore.conjugate, FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula] at hv ⊢
        exact hv
      | neg B =>
        simp [FOLiteral.conjugate, FOLiteralCore.conjugate, FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula] at hv ⊢
        exact hv
    have : (FOClause.vars (by all_goals exact hNoEq)) lits m := ⟨lit', hlit', this⟩
    dsimp only [FOClause.vars] at this; rw [hGround] at this; exact this
  · intro h; exact h.elim
-- ATTACH-BLOCKER: size baseline: retain helper in front
/-- The variables of the conjugate of a literal are the same as the
    variables of the original literal. -/
theorem conjugate_vars {L : Language} (hNoEq : L.withoutEquality) (lit : FOLiteral L hNoEq) :
    (FOLiteral.vars (by all_goals exact hNoEq)) ((FOLiteral.conjugate (by all_goals exact hNoEq)) lit) = (FOLiteral.vars (by all_goals exact hNoEq)) lit := by
-- BEGIN PROOF
  cases lit with
  | pos B => simp [FOLiteral.conjugate, FOLiteralCore.conjugate, FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula]
  | neg B => simp [FOLiteral.conjugate, FOLiteralCore.conjugate, FOLiteral.vars, FOLiteralCore.vars, FOLiteral.formula, FOLiteralCore.formula]

-- ===================================================================
-- Lemma 8.5.3 (helper): Combined substitution factors resolvent
-- ===================================================================
-- ATTACH-BLOCKER: size baseline: retain helper in front
/-- Lemma 8.5.3 (helper): The combined substitution (built from
    sigma_1, sigma_2 through the separating pair rho, rho') equates
    corresponding predicate arguments from the lifted subsets, and the
    ground resolvent D equals this combined substitution applied to
    the lifted base terms. This captures the core technical connection
    between the ground and lifted resolution structures.
    The combined substitution sigma satisfies:
    sigma(rho(x)) = sigma_1(x) for x in FV(A), and
    sigma(rho'(x)) = sigma_2(x) for x in FV(B).
    These are well-defined since rho, rho' have disjoint ranges.
    The hGroundPositionEq hypothesis captures that corresponding
    predicate arguments from the ground images are equal (as follows
    from the faithful pairwise ground-resolution witness).
    The hDiffA_eq and hDiffB_eq hypotheses capture the correspondence
    between the lifted and ground list differences, ensuring that
    removing A' from A and then applying sigma_1 gives the same result
    as applying sigma_1 to A and then removing A'_g. -/
theorem combined_subst_unifies_and_factors {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    (A B : FOClause L hNoEq)
    (A' B' : List (FOLiteral L hNoEq))
    (sigma_1 sigma_2 : Nat → Term L)
    (rho rho' : Nat → Term L)
    (D A'_g B'_g : List (FOLiteral L hNoEq))
    (rho_g rho'_g sigma_g : Nat → Term L)
    (hSubA : IsSublist A' A)
    (hSubB : IsSublist B' B)
    (hSep : (IsSeparatingPair (hNoEq := by all_goals exact hNoEq)) rho rho' A B)
    (hDeq : D = (substLits (hNoEq := by all_goals exact hNoEq)) sigma_g
      ((substLits (hNoEq := by all_goals exact hNoEq)) rho_g (listDiff ((substLits (hNoEq := by all_goals exact hNoEq)) sigma_1 A) A'_g) ++
       (substLits (hNoEq := by all_goals exact hNoEq)) rho'_g (listDiff ((substLits (hNoEq := by all_goals exact hNoEq)) sigma_2 B) B'_g)))
    (hGroundA : (FOClause.isGround (by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) sigma_1 A))
    (hGroundB : (FOClause.isGround (by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) sigma_2 B))
    (hDiffA_eq : listDiff ((substLits (hNoEq := by all_goals exact hNoEq)) sigma_1 A) A'_g =
      (substLits (hNoEq := by all_goals exact hNoEq)) sigma_1 (listDiff A A'))
    (hDiffB_eq : listDiff ((substLits (hNoEq := by all_goals exact hNoEq)) sigma_2 B) B'_g =
      (substLits (hNoEq := by all_goals exact hNoEq)) sigma_2 (listDiff B B'))
    (P : L.predSymbols)
    (hGroundPositionEq :
      ∀ lit₁, lit₁ ∈
          ((substLits (hNoEq := by all_goals exact hNoEq)) sigma_1 A' ++
            (substLits (hNoEq := by all_goals exact hNoEq)) sigma_2 ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B')) →
      ∀ lit₂, lit₂ ∈
          ((substLits (hNoEq := by all_goals exact hNoEq)) sigma_1 A' ++
            (substLits (hNoEq := by all_goals exact hNoEq)) sigma_2 ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B')) →
      ∀ (args₁ args₂ : Fin (L.predArity P) → Term L),
        (literalAtom (hNoEq := by all_goals exact hNoEq)) lit₁ = .predN P args₁ →
        (literalAtom (hNoEq := by all_goals exact hNoEq)) lit₂ = .predN P args₂ →
        ∀ i, args₁ i = args₂ i) :
    ∃ sigma : Nat → Term L,
      (∀ lit₁, lit₁ ∈
          ((substLits (hNoEq := by all_goals exact hNoEq)) rho A' ++
            (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B')) →
        ∀ lit₂, lit₂ ∈
          ((substLits (hNoEq := by all_goals exact hNoEq)) rho A' ++
            (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B')) →
        ∀ (args₁ args₂ : Fin (L.predArity P) → Term L),
          (literalAtom (hNoEq := by all_goals exact hNoEq)) lit₁ = .predN P args₁ →
          (literalAtom (hNoEq := by all_goals exact hNoEq)) lit₂ = .predN P args₂ →
          ∀ i, termSubstAll (args₁ i) sigma =
            termSubstAll (args₂ i) sigma) ∧
      D = (substLits (hNoEq := by all_goals exact hNoEq)) sigma
        ((substLits (hNoEq := by all_goals exact hNoEq)) rho (listDiff A A') ++
         (substLits (hNoEq := by all_goals exact hNoEq)) rho' (listDiff B B')) := by
-- BEGIN PROOF
  -- The combined substitution sigma is defined using the separating
  -- pair's inverse: on range(rho), sigma = rho^{-1} ∘ sigma_1;
  -- on range(rho'), sigma = rho'^{-1} ∘ sigma_2; identity elsewhere.
  let sigma := (combinedSubst (hNoEq := by all_goals exact hNoEq)) rho rho' sigma_1 sigma_2 A B
  have hA'_eq : (substLits (hNoEq := by all_goals exact hNoEq)) sigma ((substLits (hNoEq := by all_goals exact hNoEq)) rho A') =
      (substLits (hNoEq := by all_goals exact hNoEq)) sigma_1 A' := by
    rw [(substLits_comp (hNoEq := by all_goals exact hNoEq))]; apply (substLits_ext_vars (hNoEq := by all_goals exact hNoEq))
    intro lit hlit x hx
    exact (combinedSubst_compose_rho (hNoEq := by all_goals exact hNoEq)) A B sigma_1 sigma_2 rho rho' hSep x
      ⟨lit, hSubA lit hlit, hx⟩
  have hB'_eq : (substLits (hNoEq := by all_goals exact hNoEq)) sigma ((substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B')) =
      (substLits (hNoEq := by all_goals exact hNoEq)) sigma_2 ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B') := by
    rw [(substLits_comp (hNoEq := by all_goals exact hNoEq))]; apply (substLits_ext_vars (hNoEq := by all_goals exact hNoEq))
    intro lit hlit x hx
    simp only [LitSetConjugate, List.mem_map] at hlit
    obtain ⟨b', hb'_mem, rfl⟩ := hlit
    rw [(conjugate_vars (hNoEq := by all_goals exact hNoEq))] at hx
    exact (combinedSubst_compose_rho' (hNoEq := by all_goals exact hNoEq)) A B sigma_1 sigma_2 rho rho' hSep x
      ⟨b', hSubB b' hb'_mem, hx⟩
  have hImageEq :
      (substLits (hNoEq := by all_goals exact hNoEq)) sigma
          ((substLits (hNoEq := by all_goals exact hNoEq)) rho A' ++ (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B')) =
        (substLits (hNoEq := by all_goals exact hNoEq)) sigma_1 A' ++
          (substLits (hNoEq := by all_goals exact hNoEq)) sigma_2 ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B') := by
    rw [(substLits_append (hNoEq := by all_goals exact hNoEq)), hA'_eq, hB'_eq]
  refine ⟨sigma, ?_, ?_⟩
  · intro lit₁ hMem₁ lit₂ hMem₂ args₁ args₂ hLit₁ hLit₂ i
    have hGroundMem₁ :
        (substLit (hNoEq := by all_goals exact hNoEq)) sigma lit₁ ∈
          (substLits (hNoEq := by all_goals exact hNoEq)) sigma_1 A' ++
            (substLits (hNoEq := by all_goals exact hNoEq)) sigma_2 ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B') := by
      rw [← hImageEq]
      exact List.mem_map_of_mem hMem₁
    have hGroundMem₂ :
        (substLit (hNoEq := by all_goals exact hNoEq)) sigma lit₂ ∈
          (substLits (hNoEq := by all_goals exact hNoEq)) sigma_1 A' ++
            (substLits (hNoEq := by all_goals exact hNoEq)) sigma_2 ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B') := by
      rw [← hImageEq]
      exact List.mem_map_of_mem hMem₂
    have hGroundLit₁ :
        (literalAtom (hNoEq := by all_goals exact hNoEq)) ((substLit (hNoEq := by all_goals exact hNoEq)) sigma lit₁) =
          .predN P (fun j => termSubstAll (args₁ j) sigma) := by
      rw [(literalAtom_substLit (hNoEq := by all_goals exact hNoEq)), hLit₁]
      rfl
    have hGroundLit₂ :
        (literalAtom (hNoEq := by all_goals exact hNoEq)) ((substLit (hNoEq := by all_goals exact hNoEq)) sigma lit₂) =
          .predN P (fun j => termSubstAll (args₂ j) sigma) := by
      rw [(literalAtom_substLit (hNoEq := by all_goals exact hNoEq)), hLit₂]
      rfl
    exact hGroundPositionEq
      ((substLit (hNoEq := by all_goals exact hNoEq)) sigma lit₁) hGroundMem₁
      ((substLit (hNoEq := by all_goals exact hNoEq)) sigma lit₂) hGroundMem₂
      (fun j => termSubstAll (args₁ j) sigma)
      (fun j => termSubstAll (args₂ j) sigma)
      hGroundLit₁ hGroundLit₂ i
  · -- Part 2 (Factoring): D equals sigma applied to the lifted base.
    -- Ground subexpressions
    have hGDA : (FOClause.isGround (by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) sigma_1 (listDiff A A')) :=
      (isGround_of_sublist (hNoEq := by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) sigma_1 A) _ hGroundA
        (fun x hx => by
          simp only [substLits, List.mem_map] at hx ⊢
          obtain ⟨lit, hlit_mem, rfl⟩ := hx
          exact ⟨lit, (by simp only [listDiff, List.mem_filter] at hlit_mem
                          exact hlit_mem.1), rfl⟩)
    have hGDB : (FOClause.isGround (by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) sigma_2 (listDiff B B')) :=
      (isGround_of_sublist (hNoEq := by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) sigma_2 B) _ hGroundB
        (fun x hx => by
          simp only [substLits, List.mem_map] at hx ⊢
          obtain ⟨lit, hlit_mem, rfl⟩ := hx
          exact ⟨lit, (by simp only [listDiff, List.mem_filter] at hlit_mem
                          exact hlit_mem.1), rfl⟩)
    -- Chain through the common expression via calc
    calc D
        = (substLits (hNoEq := by all_goals exact hNoEq)) sigma_g
            ((substLits (hNoEq := by all_goals exact hNoEq)) rho_g (listDiff ((substLits (hNoEq := by all_goals exact hNoEq)) sigma_1 A) A'_g) ++
             (substLits (hNoEq := by all_goals exact hNoEq)) rho'_g (listDiff ((substLits (hNoEq := by all_goals exact hNoEq)) sigma_2 B) B'_g)) :=
          hDeq
      _ = (substLits (hNoEq := by all_goals exact hNoEq)) sigma_g
            ((substLits (hNoEq := by all_goals exact hNoEq)) rho_g ((substLits (hNoEq := by all_goals exact hNoEq)) sigma_1 (listDiff A A')) ++
             (substLits (hNoEq := by all_goals exact hNoEq)) rho'_g ((substLits (hNoEq := by all_goals exact hNoEq)) sigma_2 (listDiff B B'))) := by
          rw [hDiffA_eq, hDiffB_eq]
      _ = (substLits (hNoEq := by all_goals exact hNoEq)) sigma_g
            ((substLits (hNoEq := by all_goals exact hNoEq)) sigma_1 (listDiff A A') ++
             (substLits (hNoEq := by all_goals exact hNoEq)) sigma_2 (listDiff B B')) := by
          rw [(substLits_ground_id (hNoEq := by all_goals exact hNoEq)) _ rho_g hGDA,
              (substLits_ground_id (hNoEq := by all_goals exact hNoEq)) _ rho'_g hGDB]
      _ = (substLits (hNoEq := by all_goals exact hNoEq)) sigma_1 (listDiff A A') ++
          (substLits (hNoEq := by all_goals exact hNoEq)) sigma_2 (listDiff B B') :=
          (substLits_ground_id (hNoEq := by all_goals exact hNoEq)) _ sigma_g ((isGround_append (hNoEq := by all_goals exact hNoEq)) _ _ hGDA hGDB)
      _ = (substLits (hNoEq := by all_goals exact hNoEq)) (SubstitutionCore.substCompose sigma rho) (listDiff A A') ++
          (substLits (hNoEq := by all_goals exact hNoEq)) (SubstitutionCore.substCompose sigma rho') (listDiff B B') := by
          -- SubstitutionCore.substCompose sigma rho = sigma_1 on vars of listDiff A A'
          congr 1
          · symm; apply (substLits_ext_vars (hNoEq := by all_goals exact hNoEq)); intro lit hlit x hx
            have hlit_in_A : lit ∈ A := by
              simp only [listDiff, List.mem_filter] at hlit; exact hlit.1
            exact (combinedSubst_compose_rho (hNoEq := by all_goals exact hNoEq)) A B sigma_1 sigma_2
              rho rho' hSep x ⟨lit, hlit_in_A, hx⟩
          · symm; apply (substLits_ext_vars (hNoEq := by all_goals exact hNoEq)); intro lit hlit x hx
            have hlit_in_B : lit ∈ B := by
              simp only [listDiff, List.mem_filter] at hlit; exact hlit.1
            exact (combinedSubst_compose_rho' (hNoEq := by all_goals exact hNoEq)) A B sigma_1 sigma_2
              rho rho' hSep x ⟨lit, hlit_in_B, hx⟩
      _ = (substLits (hNoEq := by all_goals exact hNoEq)) sigma ((substLits (hNoEq := by all_goals exact hNoEq)) rho (listDiff A A')) ++
          (substLits (hNoEq := by all_goals exact hNoEq)) sigma ((substLits (hNoEq := by all_goals exact hNoEq)) rho' (listDiff B B')) := by
          rw [← (substLits_comp (hNoEq := by all_goals exact hNoEq)), ← (substLits_comp (hNoEq := by all_goals exact hNoEq))]
      _ = (substLits (hNoEq := by all_goals exact hNoEq)) sigma
            ((substLits (hNoEq := by all_goals exact hNoEq)) rho (listDiff A A') ++
             (substLits (hNoEq := by all_goals exact hNoEq)) rho' (listDiff B B')) := by
          rw [← (substLits_append (hNoEq := by all_goals exact hNoEq))]

-- ===================================================================
-- Lemma 8.5.3: Lifting lemma
-- ===================================================================

/-- Lemma 8.5.3: (Lifting lemma) If D is a resolvent of sigma_1(A),
    sigma_2(B) ground, then D and theta(C) have the same literal members
    for some resolvent C of A, B. This is equality of clauses as sets. -/
@[attach_debt, blueprint "chap8__lemma_8_5_3" (main := true)]
theorem lifting_lemma {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FOLiteral L hNoEq)]
    (A B : FOClause L hNoEq)
    (sigma_1 sigma_2 : Nat → Term L)
    (D : FOClause L hNoEq)
    (hGroundA : (FOClause.isGround (by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) sigma_1 A))
    (hGroundB : (FOClause.isGround (by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) sigma_2 B))
    (hResD : (IsResolvent (hNoEq := by all_goals exact hNoEq)) D ((substLits (hNoEq := by all_goals exact hNoEq)) sigma_1 A)
                            ((substLits (hNoEq := by all_goals exact hNoEq)) sigma_2 B)) :
    ∃ (C : FOClause L hNoEq) (theta : Nat → Term L),
      (IsResolvent (hNoEq := by all_goals exact hNoEq)) C A B ∧
      ∀ lit, lit ∈ D ↔
        lit ∈ (substLits (hNoEq := by all_goals exact hNoEq)) theta C

-- ===================================================================
-- Lemma 8.5.4 (helper): groundifyTree
-- ===================================================================

/-- Lemma 8.5.4 (companion): Given a ground substitution sigma,
    recursively apply it to every node of a resolution tree,
    producing a substituted version of the tree. Resolve nodes retain
    their two children recursively; this operation alone does not supply
    a homomorphism between the quotient vertices of two DAGs. -/
@[blueprint "chap8__lemma_8_5_4"]
def groundifyTree {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FOLiteral L hNoEq)]
    (sigma : Nat → Term L) : FOResolutionTree L hNoEq → FOResolutionTree L hNoEq
  | .axiom_ C => .axiom_ ((substLits (hNoEq := by all_goals exact hNoEq)) sigma C)
  | .resolve T1 T2 rA rB _rho _rho' _sig =>
    .resolve ((groundifyTree (hNoEq := by all_goals exact hNoEq)) sigma T1) ((groundifyTree (hNoEq := by all_goals exact hNoEq)) sigma T2)
      ((substLits (hNoEq := by all_goals exact hNoEq)) sigma rA) ((substLits (hNoEq := by all_goals exact hNoEq)) sigma rB)
      (fun n => Term.var n) (fun n => Term.var n)
      (fun n => Term.var n)
-- ATTACH-BLOCKER: size baseline: retain helper in front
/-- groundifyTree preserves resolve structure: the map of a resolve node
    is a resolve node with mapped children. -/
theorem groundifyTree_resolve {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FOLiteral L hNoEq)]
    (sigma : Nat → Term L)
    (T1 T2 : FOResolutionTree L hNoEq)
    (rA rB : List (FOLiteral L hNoEq))
    (rho rho' sig : Nat → Term L) :
    (groundifyTree (hNoEq := by all_goals exact hNoEq)) sigma (.resolve T1 T2 rA rB rho rho' sig) =
      .resolve ((groundifyTree (hNoEq := by all_goals exact hNoEq)) sigma T1) ((groundifyTree (hNoEq := by all_goals exact hNoEq)) sigma T2)
        ((substLits (hNoEq := by all_goals exact hNoEq)) sigma rA) ((substLits (hNoEq := by all_goals exact hNoEq)) sigma rB)
        (fun n => Term.var n) (fun n => Term.var n)
        (fun n => Term.var n) := by
-- BEGIN PROOF
  rfl

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness
/-- Substituting the identity substitution into a literal is the identity. -/
theorem substLit_id {L : Language} (hNoEq : L.withoutEquality) (lit : FOLiteral L hNoEq) :
    (substLit (hNoEq := by all_goals exact hNoEq)) (fun n => Term.var n) lit = lit := by
-- BEGIN PROOF
  cases lit with
  | pos B =>
    simp only [substLit]
    congr 1; exact substAtom_id B
  | neg B =>
    simp only [substLit]
    congr 1; exact substAtom_id B
where
  termSubstAll_id {L : Language} (t : Term L) :
      termSubstAll t (fun n => Term.var n) = t := by
    induction t with
    | var x => rfl
    | const c => rfl
    | func f args ih =>
      simp only [termSubstAll]; congr 1; funext i; exact ih i
  substAtom_id : (atom : FOAtom L hNoEq) →
      (atom.subst (hNoEq := by all_goals exact hNoEq)) (fun n => Term.var n) = atom
    | .predN P args => by
        simp only [FOAtomCore.subst, FOAtomCore.mapTerms]
        congr 1
        funext i
        exact termSubstAll_id (args i)
    | .eq_ hL lhs rhs => by
        simp only [FOAtomCore.subst, FOAtomCore.mapTerms]
        congr 1 <;> exact termSubstAll_id _
  substFormula_id {L : Language} : (A : FormulaN L) →
      substLit.substFormula (fun n => Term.var n) A = A
    | .predN P args => by
        simp only [substLit.substFormula]; congr 1; funext i; exact termSubstAll_id (args i)
    | .eq_ _ t1 t2 => by
        simp only [substLit.substFormula]; congr 1 <;> exact termSubstAll_id _
    | .neg A => congrArg _ (substFormula_id A)
    | .conj A B => by
        simp only [substLit.substFormula]; congr 1 <;> exact substFormula_id _
    | .disj A B => by
        simp only [substLit.substFormula]; congr 1 <;> exact substFormula_id _
    | .impl A B => by
        simp only [substLit.substFormula]; congr 1 <;> exact substFormula_id _
    | .all i A => congrArg _ (substFormula_id A)
    | .ex i A => congrArg _ (substFormula_id A)

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness
/-- Substituting the identity substitution into a literal list is the identity. -/
theorem substLits_id {L : Language} (hNoEq : L.withoutEquality) (lits : List (FOLiteral L hNoEq)) :
    (substLits (hNoEq := by all_goals exact hNoEq)) (fun n => Term.var n) lits = lits := by
-- BEGIN PROOF
  simp only [substLits]
  induction lits with
  | nil => rfl
  | cons hd tl ih => simp [(substLit_id (hNoEq := by all_goals exact hNoEq)), ih]

-- ===================================================================
-- Lemma 8.5.4 (helper): allLabelsGround
-- ===================================================================

/-- Lemma 8.5.4 (companion): Predicate that all labels in a resolution
    tree are ground. For leaves, the label is the stored clause.
    For resolve nodes, the label is the resolvent plus the recursive
    property on both subtrees. -/
@[blueprint "chap8__lemma_8_5_4"]
def FOResolutionTree.allLabelsGround {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)] : FOResolutionTree L hNoEq → Prop
  | .axiom_ C => (FOClause.isGround (by all_goals exact hNoEq)) C
  | .resolve T1 T2 rA rB rho rho' sigma =>
    allLabelsGround hNoEq T1 ∧ allLabelsGround hNoEq T2 ∧
    (FOClause.isGround (by all_goals exact hNoEq))
      ((FOResolutionTree.label (hNoEq := by all_goals exact hNoEq))
        (.resolve T1 T2 rA rB rho rho' sigma))
-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- allLabelsGround implies the root label is ground. -/
theorem FOResolutionTree.allLabelsGround_label
    {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FOLiteral L hNoEq)]
    (T : FOResolutionTree L hNoEq)
    (h : allLabelsGround hNoEq T) :
    (FOClause.isGround (by all_goals exact hNoEq)) (T.label (hNoEq := by all_goals exact hNoEq)) := by
-- BEGIN PROOF
  cases T with
  | axiom_ C => exact h
  | resolve T1 T2 rA rB rho rho' sigma => exact h.2.2

/-- Lemma 8.5.4 (grounding companion): every finite resolution refutation
    of an arbitrary clause set S admits a finite set of ground instances
    of clauses of that same S and a ground resolution refutation of that set.
    Instances are taken after adjoining the permitted fresh constant #;
    their substitutions have finite support and their clause images are ground.
    The output may duplicate or reorganize nodes of the input refutation. -/
@[attach_debt, blueprint "chap8__lemma_8_5_4"]
theorem ground_refutation_exists {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    [DecidableEq (FOLiteral (FreshGroundLanguage L) hNoEq)]
    (S : FOClause L hNoEq → Prop)
    (H : FOResolutionDAG L hNoEq)
    (hH : FOResolutionDAG.isResolutionRefutation hNoEq H S) :
    ∃ (S_g : List (FOClause (FreshGroundLanguage L) hNoEq))
      (H_g : FOResolutionDAG (FreshGroundLanguage L) hNoEq),
      (∀ C_g ∈ S_g,
        FOClause.isGround (L := FreshGroundLanguage L) hNoEq C_g ∧
        ∃ (C : FOClause L hNoEq)
          (sigma : Nat → Term (FreshGroundLanguage L)) (support : List Nat),
          S C ∧
          (∀ x, x ∉ support → sigma x = Term.var x) ∧
          (∀ x, sigma x ≠ Term.var x → termFV (sigma x) = ∅) ∧
          (∀ lit, lit ∈ C_g ↔
            lit ∈ substLits (L := FreshGroundLanguage L) hNoEq sigma
              (FreshGroundLanguage.liftClause hNoEq C))) ∧
      FOResolutionDAG.isResolutionRefutation (L := FreshGroundLanguage L) hNoEq H_g (fun C => C ∈ S_g) ∧
      (∀ T ∈ H_g, FOResolutionTree.allLabelsGround (L := FreshGroundLanguage L) hNoEq T)

-- ===================================================================
-- Theorem 8.5.1 (helper): certified ground-tree bridge
-- ===================================================================

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness
/-- A ground clause has no free variables in the sense used by separating
    substitutions. -/
theorem clauseFV_eq_empty_of_ground {L : Language} (hNoEq : L.withoutEquality)
    (C : FOClause L hNoEq) (hGround : C.isGround) :
    (clauseFV (hNoEq := by all_goals exact hNoEq)) C = Set.empty := by
  ext x
  constructor
  · rintro ⟨lit, hLit, hVar⟩
    have : (FOClause.vars hNoEq C) x := ⟨lit, hLit, hVar⟩
    dsimp only [FOClause.vars] at this; rw [hGround] at this
    exact this
  · intro h
    exact h.elim

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness
/-- Identity substitutions separate two ground clauses because both clauses
    have empty free-variable sets. -/
theorem identity_isSeparatingPair_of_ground {L : Language} (hNoEq : L.withoutEquality)
    (A B : FOClause L hNoEq)
    (hA : A.isGround) (hB : B.isGround) :
    (IsSeparatingPair (hNoEq := by all_goals exact hNoEq))
      (fun n => Term.var n) (fun n => Term.var n) A B := by
  unfold IsSeparatingPair
  rw [show (clauseFV (hNoEq := by all_goals exact hNoEq)) A = Set.empty from (clauseFV_eq_empty_of_ground (hNoEq := by all_goals exact hNoEq)) A hA,
      show (clauseFV (hNoEq := by all_goals exact hNoEq)) B = Set.empty from (clauseFV_eq_empty_of_ground (hNoEq := by all_goals exact hNoEq)) B hB]
  simp [substIsVarOnSet, substInjectiveOnSet]
  ext n
  constructor
  · rintro ⟨⟨x, hx, _⟩, _⟩
    exact hx.elim
  · intro h
    exact h.elim

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness
/-- Leaf provenance is monotone under implication of source predicates. -/
theorem methodTree_leavesFrom_mono {L : Language} (hNoEq : L.withoutEquality)
    (T : FOResolutionTree L hNoEq)
    {S S' : FOClause L hNoEq → Prop}
    (hLeaves : (T.leavesFrom (hNoEq := by all_goals exact hNoEq)) S)
    (hMono : ∀ C, S C → S' C) :
    (T.leavesFrom (hNoEq := by all_goals exact hNoEq)) S' := by
  induction T with
  | axiom_ C =>
      exact hMono C hLeaves
  | resolve T1 T2 resolvedA resolvedB rho rho' sigma ih1 ih2 =>
      exact ⟨ih1 hLeaves.1, ih2 hLeaves.2⟩

end LCS.FOResolution.Method.Completeness
end
