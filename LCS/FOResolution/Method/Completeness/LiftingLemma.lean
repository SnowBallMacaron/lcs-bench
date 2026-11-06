import LCS.Item
import LCS.Util
import LCS.FOResolution.Method
import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.Method.HerbrandBridge
import LCS.Herbrand.SHGTheorem.Main
import LCS.FOResolution.GroundResolution
import LCS.CutElim.LK
import LCS.Resolution.Method.DAGs
import Attach
import LCS.FOResolution.Method.Completeness.LiftingLemma.ProofsStamp

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

-- ===================================================================
-- Lemma 8.5.3 (helper): MGU existence from unifiability
-- ===================================================================

-- ===================================================================
-- Lemma 8.5.3 (helpers): Substitution extensionality and groundness
-- ===================================================================

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting, LCS.SLD.FirstOrder.HashLanguage, LCS.SLD.FirstOrder.HornEncoding, LCS.SLD.FirstOrder.Soundness
/-- termVars (from ClauseForm) and termFV (from Syntax.Variables)
    are equivalent for the same term. -/
theorem termVars_iff_termFV {L : Language} (t : Term L) (n : Nat) :
    termVars t n ↔ termFV t n := by
  constructor
  · intro h; induction t with
    | var x => exact h | const c => exact h.elim
    | func f args ih => obtain ⟨i, hi⟩ := h; exact ⟨i, ih i hi⟩
  · intro h; induction t with
    | var x => exact h | const c => exact h.elim
    | func f args ih => obtain ⟨i, hi⟩ := h; exact ⟨i, ih i hi⟩

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness, LCS.FOResolution.Method.Completeness.Lifting
/-- A literal in a ground clause has no variables. -/
theorem isGround_lit_no_vars {L : Language} (hNoEq : L.withoutEquality) (c : FOClause L hNoEq)
    (hGround : (FOClause.isGround (by all_goals exact hNoEq)) c)
    (lit : FOLiteral L hNoEq) (hlit : lit ∈ c) :
    (FOLiteral.vars hNoEq lit) = Set.empty := by
-- BEGIN PROOF
  ext m; constructor
  · intro h
    have hHas : (FOClause.vars hNoEq c) m := ⟨lit, hlit, h⟩
    dsimp only [FOClause.vars] at hHas; rw [hGround] at hHas; exact hHas
  · intro h; exact h.elim

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness, LCS.FOResolution.Method.Completeness.Lifting
/-- Substitution on a ground clause is the identity.
    Ground means no variables, so substitution changes nothing. -/
theorem substLits_ground_id {L : Language} (hNoEq : L.withoutEquality) (c : FOClause L hNoEq)
    (sigma : Nat → Term L)
    (hGround : (FOClause.isGround (by all_goals exact hNoEq)) c) :
    (substLits (hNoEq := by all_goals exact hNoEq)) sigma c = c := by
-- BEGIN PROOF
  simp only [substLits]
  induction c with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map]; congr 1
    · -- substLit sigma hd = hd
      have hhd : FOLiteral.vars hNoEq hd = Set.empty :=
        (isGround_lit_no_vars (hNoEq := by all_goals exact hNoEq)) (hd :: tl) hGround hd List.mem_cons_self
      exact substLit_ground_id hd sigma hhd
    · exact ih (by
        ext m; constructor
        · intro ⟨l, hm, hv⟩
          have : (FOClause.vars (by all_goals exact hNoEq)) (hd :: tl) m :=
            ⟨l, List.mem_cons_of_mem _ hm, hv⟩
          dsimp only [FOClause.vars] at this; rw [hGround] at this; exact this
        · intro h; exact h.elim)
where
  /-- Inline proof: substLit on a ground literal is identity. -/
  substLit_ground_id (lit : FOLiteral L hNoEq)
      (sigma : Nat → Term L) (hGround : (FOLiteral.vars hNoEq lit) = Set.empty) :
      (substLit (hNoEq := by all_goals exact hNoEq)) sigma lit = lit := by
    cases lit with
    | pos B =>
      simp only [substLit]; congr 1
      exact substAtom_ground_id B sigma hGround
    | neg B =>
      simp only [substLit]; congr 1
      exact substAtom_ground_id B sigma hGround
  /-- Inline proof: atom substitution on a ground atom is identity. -/
  substAtom_ground_id (atom : FOAtom L hNoEq)
      (sigma : Nat → Term L) (hGround : atom.vars = Set.empty) :
      (atom.subst (hNoEq := by all_goals exact hNoEq)) sigma = atom := by
    cases atom with
    | predN P args =>
      simp only [FOAtomCore.subst, FOAtomCore.mapTerms]; congr 1; funext i
      exact termSubstAll_ground_id (args i) sigma (by
        ext n; constructor
        · intro h
          have : FOAtomCore.vars (.predN P args) n :=
            ⟨i, (termVars_iff_termFV _ n).mpr h⟩
          rw [hGround] at this; exact this
        · intro h; exact h.elim)
    | eq_ hLeq t1 t2 =>
      simp only [FOAtomCore.subst, FOAtomCore.mapTerms]; congr 1
      all_goals (apply termSubstAll_ground_id; ext n; constructor)
      · intro h; have := (show FOAtomCore.vars (.eq_ hLeq t1 t2) n from
          Or.inl ((termVars_iff_termFV _ n).mpr h)); rw [hGround] at this; exact this
      · intro h; exact h.elim
      · intro h; have := (show FOAtomCore.vars (.eq_ hLeq t1 t2) n from
          Or.inr ((termVars_iff_termFV _ n).mpr h)); rw [hGround] at this; exact this
      · intro h; exact h.elim
  /-- Inline proof: termSubstAll on ground term is identity. -/
  termSubstAll_ground_id {L : Language} (t : Term L)
      (sigma : Nat → Term L) (hGround : termFV t = Set.empty) :
      termSubstAll t sigma = t := by
    induction t with
    | var x =>
      exfalso
      have : termFV (@Term.var L x) = Set.singleton x := by
        ext n; simp [termFV, Set.singleton]
      rw [this] at hGround
      have : (Set.singleton x : Set Nat) x := rfl
      rw [hGround] at this; exact this
    | const c => rfl
    | func f args ih =>
      simp only [termSubstAll]; congr 1; funext i; apply ih i
      ext n; constructor
      · intro h
        have : termFV (Term.func f args) n :=
          show (Set.iUnion fun j => termFV (args j)) n from ⟨i, h⟩
        rw [hGround] at this; exact this
      · intro h; exact h.elim

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness, LCS.FOResolution.Method.Completeness.Lifting
/-- A sublist of a ground clause is ground. -/
theorem isGround_of_sublist {L : Language} (hNoEq : L.withoutEquality) (c sub : FOClause L hNoEq)
    (hGround : (FOClause.isGround (by all_goals exact hNoEq)) c) (hSub : IsSublist sub c) :
    (FOClause.isGround (by all_goals exact hNoEq)) sub := by
-- BEGIN PROOF
  ext m; constructor
  · intro ⟨l, hm, hv⟩
    have : (FOClause.vars (by all_goals exact hNoEq)) c m := ⟨l, hSub l hm, hv⟩
    dsimp only [FOClause.vars] at this; rw [hGround] at this; exact this
  · intro h; exact h.elim

-- retained: used by LCS.FOResolution.GroundResolution.PropositionalTranslation, LCS.FOResolution.Method.Completeness.Completeness, LCS.FOResolution.Method.Completeness.Lifting
/-- The append of two ground clauses is ground. -/
theorem isGround_append {L : Language} (hNoEq : L.withoutEquality) (c1 c2 : FOClause L hNoEq)
    (h1 : (FOClause.isGround (by all_goals exact hNoEq)) c1) (h2 : (FOClause.isGround (by all_goals exact hNoEq)) c2) :
    (FOClause.isGround (by all_goals exact hNoEq)) (c1 ++ c2) := by
-- BEGIN PROOF
  ext m; constructor
  · intro ⟨l, hm, hv⟩; rw [List.mem_append] at hm
    rcases hm with h | h
    · have : (FOClause.vars (by all_goals exact hNoEq)) c1 m := ⟨l, h, hv⟩; dsimp only [FOClause.vars] at this; rw [h1] at this; exact this
    · have : (FOClause.vars (by all_goals exact hNoEq)) c2 m := ⟨l, h, hv⟩; dsimp only [FOClause.vars] at this; rw [h2] at this; exact this
  · intro h; exact h.elim

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

end LCS.FOResolution.Method.Completeness
end
