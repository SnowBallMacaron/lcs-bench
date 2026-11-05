import LCS.Item
import LCS.Util
import LCS.SLD.Propositional
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import LCS.FOResolution.Method
import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.Method.Completeness
import LCS.Herbrand.SHGTheorem.Main
import LCS.SLD.FirstOrder.HornClauses
import Attach
import LCS.SLD.FirstOrder.HashLanguage.ProofsStamp

noncomputable section
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.Completeness

-- ATTACH-BLOCKER: scoped helper requires manual relocation
open LCS.FirstOrder.SyntaxN.Variables in
/-- Exactly the free variables of the translated clause matrix (SQ25).
    The auxiliary contradiction contributes variables only for an empty clause. -/
@[blueprint "chap9__definition_9_4_1"]
def hornClauseVarsList {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) (h : FOHornClause L hNoEq) : List Nat := by
  classical
  let matrix := clauseToFormula hNoEq Afalsum h.toFOClause
  exact ((formulaVarsList matrix).filter (fun n => decide (formulaFVN matrix n))).eraseDups

/-- Definition 9.4.1 (companion): Encode a list of Horn clauses as a
    single FormulaN sentence. Each clause is mapped to the universal
    closure of its standard-logic translation (via `toFOClause` and
    `FOClause.universalClosure`); the resulting formulae are conjoined.
    The empty-list case evaluates to the universal closure of the
    `Afalsum` placeholder to stay within the NNF grammar — the SLD
    completeness pipeline only instantiates this encoding when the
    Horn-clause set is non-empty (`goals ≠ []`). -/
@[blueprint "chap9__definition_9_4_1"]
def hornClauses_to_formulaN {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) : List (FOHornClause L hNoEq) → FormulaN L
  | [] => Afalsum
  | [h] => (FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) Afalsum (h.toFOClause (hNoEq := by all_goals exact hNoEq)) ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum h)
  | h :: rest =>
    FormulaN.conj
      ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) Afalsum (h.toFOClause (hNoEq := by all_goals exact hNoEq)) ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum h))
      ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum rest)

-- retained: used by LCS.SLD.FirstOrder.GroundInstances, LCS.SLD.FirstOrder.GroundSemantics
/-- `hornClauseVarsList` covers the free variables of the clause
    translation (literal-based free variables). -/
theorem hornClauseVarsList_covers_clause {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (h : FOHornClause L hNoEq) :
    ∀ n, (FOClause.freeVars (hNoEq := by all_goals exact hNoEq)) (h.toFOClause (hNoEq := by all_goals exact hNoEq)) n → n ∈ (hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) A h := by
  -- REPAIR(T9-13): proof pending — each literal free variable occurs in the exact clause matrix
  sorry

-- ATTACH-BLOCKER: scoped helper requires manual relocation
open LCS.FirstOrder.SyntaxN.Variables in
/-- The free variables of `clauseToFormula A C` are contained in
    `FV(A) ∪ ⋃_{lit ∈ C} FV((FOLiteralCore.formula lit))`. The `A` contribution arises
    from the empty-clause case via `FormulaN.falsum A = A ∧ ¬A`. -/
theorem clauseToFormula_FV_subset {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (C : FOClause L hNoEq) (n : Nat)
    (h : formulaFVN ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C) n) :
    formulaFVN A n ∨ ∃ lit ∈ C, formulaFVN (FOLiteralCore.formula lit) n := by
-- BEGIN PROOF
  induction C with
  | nil =>
    left
    simp only [clauseToFormula, FormulaN.falsum, formulaFVN] at h
    cases h with
    | inl hA => exact hA
    | inr hnA => exact hnA
  | cons hd tl ih =>
    cases tl with
    | nil =>
      simp only [clauseToFormula] at h
      right
      refine ⟨hd, List.mem_cons_self, ?_⟩
      cases hd with
      | pos B => simpa [clauseToFormula.litToFormula, FOLiteral.formula, FOLiteralCore.formula] using h
      | neg B => simpa [clauseToFormula.litToFormula, FOLiteral.formula, FOLiteralCore.formula, formulaFVN] using h
    | cons hd2 tl2 =>
      simp only [clauseToFormula, formulaFVN] at h
      cases h with
      | inl hLit =>
        right
        refine ⟨hd, List.mem_cons_self, ?_⟩
        cases hd with
        | pos B => simpa [clauseToFormula.litToFormula, FOLiteral.formula, FOLiteralCore.formula] using hLit
        | neg B => simpa [clauseToFormula.litToFormula, FOLiteral.formula, FOLiteralCore.formula, formulaFVN] using hLit
      | inr hRest =>
        have := ih hRest
        rcases this with h1 | ⟨lit, hlitMem, hlitFV⟩
        · left; exact h1
        · right; exact ⟨lit, List.mem_cons_of_mem hd hlitMem, hlitFV⟩

-- ATTACH-BLOCKER: scoped helper requires manual relocation
open LCS.FirstOrder.SyntaxN.Variables in
/-- Wrapping a formula with `foldr all` over `fvs` removes those
    variables from its free-variable set. -/
theorem foldr_all_FV {L : Language} (fvs : List Nat) :
    ∀ (A : FormulaN L) (n : Nat),
      formulaFVN (fvs.foldr (fun v acc => FormulaN.all v acc) A) n →
      formulaFVN A n ∧ n ∉ fvs := by
-- BEGIN PROOF
  induction fvs with
  | nil => intro A n h; exact ⟨h, fun h' => by simp at h'⟩
  | cons v rest ih =>
    intro A n h
    simp only [List.foldr, formulaFVN] at h
    have h1 := h.1
    have h2 := h.2
    have ⟨h1', h1''⟩ := ih A n h1
    refine ⟨h1', ?_⟩
    intro hcons
    rw [List.mem_cons] at hcons
    cases hcons with
    | inl heq => apply h2; show n = v; exact heq
    | inr hr => exact h1'' hr

-- ATTACH-BLOCKER: scoped helper requires manual relocation
open LCS.FirstOrder.SyntaxN.Variables in
/-- The universal closure produced by `hornClauses_to_formulaN` is a
    sentence: it has no free variables. -/
theorem hornClauses_univClosure_sentence {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (h : FOHornClause L hNoEq) :
    ∀ n, ¬ formulaFVN
      ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) A (h.toFOClause (hNoEq := by all_goals exact hNoEq)) ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) A h)) n := by
  intro n hmem
  unfold FOClause.universalClosure at hmem
  obtain ⟨hFV, hNotIn⟩ := foldr_all_FV _ _ n hmem
  apply hNotIn
  simp only [hornClauseVarsList, List.mem_eraseDups, List.mem_filter, decide_eq_true_eq]
  exact ⟨formulaVarsList_cover _ n hFV, hFV⟩

/-- Definition 9.4.1 (companion): The encoding is faithful — the
    encoded FormulaN is unsatisfiable iff the Horn clause set is
    unsatisfiable (in the standard-logic sense of
    `FOHornClauseSet.isUnsatisfiable`). Requires `S ≠ []` so that the
    encoding exactly captures the conjunction of per-clause universal
    closures; the empty case is not semantically meaningful for the
    completeness pipeline (no Horn clauses to refute). -/
@[blueprint "chap9__definition_9_4_1"]
theorem satisfiableN_hornClauseSet_iff {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) (S : List (FOHornClause L hNoEq)) (hNe : S ≠ []) :
    ¬ satisfiableN ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum S) ↔
    (FOHornClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) Afalsum S 

-- ===================================================================
-- Hash-language infrastructure for the §9.4 semantic reduction
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The sole fresh hash symbol has rank zero and is represented as a constant. -/
def hashSkolemRank (_ : Fin 1) : Nat := 0

-- ATTACH-BLOCKER: unsupported untagged abbrev
/-- The language obtained by adding one fresh nullary hash symbol to `L`.
    This is the existing §7.6 Skolem-language extension specialized to
    one rank-zero symbol, not a second language-extension mechanism. -/
@[blueprint "chap9__theorem_9_4_1"]
abbrev HashLanguage (L : Language) : Language :=
  LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) 1 hashSkolemRank

-- retained: used by LCS.SLD.FirstOrder.HornEncoding
/-- The distinguished closed hash term in `HashLanguage L`. -/
def hashTerm {L : Language} : Term (HashLanguage L) :=
  .const (Sum.inr ⟨(0 : Fin 1), rfl⟩)

-- ATTACH-BLOCKER: unsupported untagged abbrev
/-- Exact embedding of base-language terms into the hash language. -/
abbrev hashLiftTerm {L : Language} : Term L → Term (HashLanguage L) :=
  LCS.Herbrand.SHGTheorem.liftTermSkolem
    (skolemRank := hashSkolemRank)

-- ATTACH-BLOCKER: unsupported untagged abbrev
/-- Exact embedding of base-language formulae into the hash language. -/
abbrev hashLiftFormula {L : Language} :
    FormulaN L → FormulaN (HashLanguage L) :=
  LCS.Herbrand.SHGTheorem.liftFormulaSkolem
    (skolemRank := hashSkolemRank)

-- retained: used by LCS.SLD.FirstOrder.GroundLifting
/-- Exact structural embedding of base-language atoms into the hash
    language. -/
def hashLiftAtom {L : Language} (hNoEq : L.withoutEquality) :
    FOAtom L hNoEq → FOAtom (HashLanguage L) hNoEq
  | .predN P args =>
      .predN P (fun i => hashLiftTerm (args i))
  | .eq_ hL lhs rhs =>
      .eq_ hL (hashLiftTerm lhs) (hashLiftTerm rhs)

-- retained: used by LCS.SLD.FirstOrder.GroundLifting
/-- Structural atom lifting commutes with the ambient formula lift. -/
theorem hashLiftAtom_toFormula {L : Language} (hNoEq : L.withoutEquality)  (atom : FOAtom L hNoEq) :
    ((hashLiftAtom (hNoEq := by all_goals exact hNoEq)) atom).toFormula =
      hashLiftFormula atom.toFormula := by
  cases atom <;> rfl

-- retained: used by LCS.SLD.FirstOrder.HornEncoding
/-- The hash term is closed: its sole function symbol is nullary. -/
theorem hashTerm_isClosed {L : Language} : (@hashTerm L).isClosed := rfl

-- retained: used by LCS.SLD.FirstOrder.HornEncoding
/-- The fresh hash term is outside the image of the base-term lift. -/
theorem hashTerm_ne_hashLiftTerm {L : Language} (t : Term L) :
    (@hashTerm L) ≠ hashLiftTerm t := by
  intro h
  cases t with
  | var => cases h
  | const => cases h
  | func _ _ => cases h

-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.HornEncoding
/-- Hash-language formation does not change whether equality is present. -/
theorem HashLanguage_withoutEquality_iff (L : Language) :
    (HashLanguage L).withoutEquality ↔ L.withoutEquality :=
  Iff.rfl



-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.HornEncoding
/-- Lifting a formula preserves its free-variable set exactly. -/
theorem hashLiftFormula_formulaFVN {L : Language} (A : FormulaN L) :
    LCS.FirstOrder.SyntaxN.Variables.formulaFVN (hashLiftFormula A) =
      LCS.FirstOrder.SyntaxN.Variables.formulaFVN A :=
  LCS.Herbrand.SHGTheorem.Herbrand.liftFormulaSkolem_formulaFVN A

-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.HornEncoding
/-- Lifting preserves closedness of formulae exactly. -/
theorem hashLiftFormula_isClosed_iff {L : Language} (A : FormulaN L) :
    LCS.FirstOrder.SyntaxN.Variables.FormulaN.isClosed
        (hashLiftFormula A) ↔
      LCS.FirstOrder.SyntaxN.Variables.FormulaN.isClosed A := by
  unfold LCS.FirstOrder.SyntaxN.Variables.FormulaN.isClosed
  rw [hashLiftFormula_formulaFVN]



-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.HornEncoding
/-- Lifting an NNF formula leaves it in NNF. -/
theorem hashLiftFormula_isNNF {L : Language} (A : FormulaN L)
    (h : A.isNNF) :
    (hashLiftFormula A).isNNF :=
  LCS.Herbrand.SHGTheorem.Herbrand.liftFormulaSkolem_isNNF A h

-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.HornEncoding
/-- Lifting a rectified formula leaves it rectified. -/
theorem hashLiftFormula_isRectified {L : Language} (A : FormulaN L)
    (h : LCS.FirstOrder.Semantics.Subformulae.isRectified A) :
    LCS.FirstOrder.Semantics.Subformulae.isRectified (hashLiftFormula A) :=
  LCS.Herbrand.SHGTheorem.Herbrand.liftFormulaSkolem_isRectified A h

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- Lifting preserves atomicity exactly. -/
theorem hashLiftFormula_isAtomic {L : Language} (A : FormulaN L) :
    (hashLiftFormula A).isAtomic = A.isAtomic := by
  cases A <;> rfl

-- retained: used by LCS.SLD.FirstOrder.GroundLifting
/-- The term lift is injective, providing structural recovery on its
    image without a total demoter or a fallback term. -/
theorem hashLiftTerm_injective {L : Language} :
    Function.Injective (@hashLiftTerm L) := by
  intro t
  induction t with
  | var x =>
      intro u h
      cases u with
      | var y =>
          simp only [hashLiftTerm,
            LCS.Herbrand.SHGTheorem.liftTermSkolem] at h
          exact congrArg Term.var (Term.var.inj h)
      | const => cases h
      | func => cases h
  | const c =>
      intro u h
      cases u with
      | var => cases h
      | const d =>
          simp only [hashLiftTerm,
            LCS.Herbrand.SHGTheorem.liftTermSkolem] at h
          exact congrArg Term.const
            (Sum.inl.inj (Term.const.inj h))
      | func => cases h
  | func f args ih =>
      intro u h
      cases u with
      | var => cases h
      | const => cases h
      | func g args' =>
        simp only [hashLiftTerm,
          LCS.Herbrand.SHGTheorem.liftTermSkolem] at h
        have hfg : f = g := Sum.inl.inj (Term.func.inj h).1
        subst g
        congr 1
        funext i
        apply ih i
        have hargs :
            (fun i => LCS.Herbrand.SHGTheorem.liftTermSkolem
                (skolemRank := hashSkolemRank) (args i)) =
              (fun i => LCS.Herbrand.SHGTheorem.liftTermSkolem
                (skolemRank := hashSkolemRank) (args' i)) :=
          eq_of_heq (Term.func.inj h).2
        exact congrFun hargs i



-- retained: used by LCS.SLD.FirstOrder.GroundLifting
/-- The formula lift is injective, so equality of lifted syntax reflects
    equality of the source formulae. -/
theorem hashLiftFormula_injective {L : Language} :
    Function.Injective (@hashLiftFormula L) := by
  intro A
  induction A with
  | predN P args =>
      intro B h
      cases B with
      | predN Q args' =>
        simp only [hashLiftFormula,
          LCS.Herbrand.SHGTheorem.liftFormulaSkolem] at h
        have hPQ : P = Q := (FormulaN.predN.inj h).1
        subst Q
        congr 1
        funext i
        apply hashLiftTerm_injective
        have hargs :
            (fun i => LCS.Herbrand.SHGTheorem.liftTermSkolem
                (skolemRank := hashSkolemRank) (args i)) =
              (fun i => LCS.Herbrand.SHGTheorem.liftTermSkolem
                (skolemRank := hashSkolemRank) (args' i)) :=
          eq_of_heq (FormulaN.predN.inj h).2
        exact congrFun hargs i
      | eq_ => cases h
      | neg => cases h
      | conj => cases h
      | disj => cases h
      | impl => cases h
      | all => cases h
      | ex => cases h
  | eq_ _ t₁ t₂ =>
      intro B h
      cases B with
      | predN => cases h
      | eq_ _ u₁ u₂ =>
        simp only [hashLiftFormula,
          LCS.Herbrand.SHGTheorem.liftFormulaSkolem] at h
        have ht := FormulaN.eq_.inj h
        rw [hashLiftTerm_injective ht.1, hashLiftTerm_injective ht.2]
      | neg => cases h
      | conj => cases h
      | disj => cases h
      | impl => cases h
      | all => cases h
      | ex => cases h
  | neg A ih =>
      intro B h
      cases B with
      | neg B => rw [ih (FormulaN.neg.inj h)]
      | _ => cases h
  | conj A B ihA ihB =>
      intro C h
      cases C with
      | conj C D =>
        have h' := FormulaN.conj.inj h
        rw [ihA h'.1, ihB h'.2]
      | _ => cases h
  | disj A B ihA ihB =>
      intro C h
      cases C with
      | disj C D =>
        have h' := FormulaN.disj.inj h
        rw [ihA h'.1, ihB h'.2]
      | _ => cases h
  | impl A B ihA ihB =>
      intro C h
      cases C with
      | impl C D =>
        have h' := FormulaN.impl.inj h
        rw [ihA h'.1, ihB h'.2]
      | _ => cases h
  | all x A ih =>
      intro B h
      cases B with
      | all y B =>
        have h' := FormulaN.all.inj h
        rw [h'.1, ih h'.2]
      | _ => cases h
  | ex x A ih =>
      intro B h
      cases B with
      | ex y B =>
        have h' := FormulaN.ex.inj h
        rw [h'.1, ih h'.2]
      | _ => cases h



-- retained: used by LCS.SLD.FirstOrder.GroundLifting
/-- The structural atom lift is injective. -/
theorem hashLiftAtom_injective {L : Language} (hNoEq : L.withoutEquality)  :
    Function.Injective (@hashLiftAtom L (by all_goals exact hNoEq)) := by
  intro atom₁ atom₂ h
  apply FOAtomCore.toFormula_injective
  apply hashLiftFormula_injective
  simpa only [(hashLiftAtom_toFormula (hNoEq := by all_goals exact hNoEq))] using congrArg FOAtomCore.toFormula h

-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.HornEncoding
/-- Exact lift of literals into the hash language. -/
def hashLiftLiteral {L : Language} (hNoEq : L.withoutEquality) :
    FOLiteral L hNoEq → FOLiteral (HashLanguage L) hNoEq
  | .pos A => .pos ((hashLiftAtom (hNoEq := by all_goals exact hNoEq)) A)
  | .neg A => .neg ((hashLiftAtom (hNoEq := by all_goals exact hNoEq)) A)

-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.HornEncoding
/-- Exact pointwise lift of a first-order clause. -/
def hashLiftFOClause {L : Language} (hNoEq : L.withoutEquality)
    (C : FOClause L hNoEq) : FOClause (HashLanguage L) hNoEq :=
  C.map (hashLiftLiteral (hNoEq := by all_goals exact hNoEq))

-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.GroundLifting, LCS.SLD.FirstOrder.HornEncoding
/-- Exact structural lift of a PROLOG-notation Horn clause. -/
def hashLiftHornClause {L : Language} (hNoEq : L.withoutEquality) :
    FOHornClause L hNoEq → FOHornClause (HashLanguage L) (by all_goals exact hNoEq)
  | FOHornClauseCore.rule head body =>
      FOHornClauseCore.rule ((hashLiftAtom (hNoEq := by all_goals exact hNoEq)) head) (body.image (hashLiftAtom (hNoEq := by all_goals exact hNoEq)))
  | FOHornClauseCore.fact head => FOHornClauseCore.fact ((hashLiftAtom (hNoEq := by all_goals exact hNoEq)) head)
  | FOHornClauseCore.goal body => FOHornClauseCore.goal (body.image (hashLiftAtom (hNoEq := by all_goals exact hNoEq)))

-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.HornEncoding
/-- Literal projection commutes with the hash lift. -/
theorem hashLiftLiteral_formula {L : Language} (hNoEq : L.withoutEquality)  (lit : FOLiteral L hNoEq) :
    (FOLiteralCore.formula ((hashLiftLiteral (hNoEq := by all_goals exact hNoEq)) lit)) = hashLiftFormula (FOLiteralCore.formula lit) := by
  cases lit <;> apply (hashLiftAtom_toFormula (hNoEq := by all_goals exact hNoEq))



-- retained: used by LCS.SLD.FirstOrder.GroundLifting
/-- Pointwise lifting is injective on lists of atoms. -/
theorem hashLiftAtomList_injective {L : Language} (hNoEq : L.withoutEquality)  :
    Function.Injective (List.map (@hashLiftAtom L (by all_goals exact hNoEq))) := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons => cases h
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil => cases h
      | cons y ys =>
          have h' := List.cons.inj h
          rw [(hashLiftAtom_injective (hNoEq := by all_goals exact hNoEq)) h'.1, ih h'.2]



-- retained: used by LCS.SLD.FirstOrder.GroundLifting
/-- The Horn-clause lift is injective. -/
theorem hashLiftHornClause_injective {L : Language} (hNoEq : L.withoutEquality)  :
    Function.Injective (@hashLiftHornClause L (by all_goals exact hNoEq)) := by
  intro c₁ c₂ h
  have hi := finset_image_injective
    (hashLiftAtom (hNoEq := hNoEq)) (hashLiftAtom_injective (hNoEq := hNoEq))
  cases c₁ <;> cases c₂
  · injection h with hh hb
    rw [hashLiftAtom_injective (hNoEq := hNoEq) hh, hi hb]
  · cases h
  · cases h
  · cases h
  · injection h with hh
    rw [hashLiftAtom_injective (hNoEq := hNoEq) hh]
  · cases h
  · cases h
  · cases h
  · injection h with hb
    rw [hi hb]











/-- An injective image enumerates the same atoms up to permutation (SQ16). -/
theorem finset_toList_image_perm {α β : Type} [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (s : LCS.Finset α) :
    (s.image f).toList.Perm (s.toList.map f) := by
  have hn (t : LCS.Finset α) : t.toList.Nodup := by
    have h := t.nodup
    rw [← t.toList_ofList_eq] at h
    exact h
  have hm : (s.image f).toList.Nodup := by
    have h := (s.image f).nodup
    rw [← (s.image f).toList_ofList_eq] at h
    exact h
  apply LCS.list_perm_of_nodup_of_mem_iff hm ((hn s).map f (fun _ _ h heq => h (hf heq)))
  intro b
  simp only [LCS.Finset.mem_toList, LCS.Finset.mem_image, List.mem_map]

-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.HornEncoding
/-- Standard-clause translation commutes with lifting up to permutation (SQ16). -/
theorem hashLiftHornClause_toFOClause {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) :
    ((hashLiftHornClause hNoEq c).toFOClause (L := HashLanguage L) hNoEq).Perm
      (hashLiftFOClause hNoEq (c.toFOClause hNoEq)) := by
  have hp := finset_toList_image_perm (hashLiftAtom hNoEq)
    (hashLiftAtom_injective hNoEq)
  cases c with
  | rule head body =>
    simpa [hashLiftHornClause, FOHornClause.toFOClause, FOHornClauseCore.toFOClause,
      hashLiftFOClause, Function.comp_def, hashLiftLiteral, List.map_map, List.map_append] using
      (hp body).map FOLiteralCore.neg |>.append_right [FOLiteralCore.pos (hashLiftAtom hNoEq head)]
  | fact head => exact List.Perm.refl _
  | goal body =>
    simpa [hashLiftHornClause, FOHornClause.toFOClause, FOHornClauseCore.toFOClause,
      hashLiftFOClause, Function.comp_def, hashLiftLiteral, List.map_map] using
      (hp body).map FOLiteralCore.neg

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- Definite/goal classification is unchanged by lifting. -/
theorem hashLiftHornClause_isDefinite_iff {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) :
    (((hashLiftHornClause (hNoEq := by all_goals exact hNoEq)) c).isDefinite (hNoEq := by all_goals exact hNoEq)) ↔ (c.isDefinite (hNoEq := by all_goals exact hNoEq)) := by
  cases c <;> rfl



-- retained: used by LCS.SLD.FirstOrder.HornEncoding
/-- Exact membership reflection for a lifted Horn-clause list. -/
theorem hashLiftHornClause_mem_map_iff {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) (S : List (FOHornClause L hNoEq)) :
    (hashLiftHornClause (hNoEq := by all_goals exact hNoEq)) c ∈ S.map (hashLiftHornClause (hNoEq := by all_goals exact hNoEq)) ↔ c ∈ S := by
  constructor
  · intro h
    rw [List.mem_map] at h
    obtain ⟨d, hd, hdc⟩ := h
    have : d = c := (hashLiftHornClause_injective (hNoEq := by all_goals exact hNoEq)) hdc
    simpa [this] using hd
  · intro h
    exact List.mem_map.mpr ⟨c, h, rfl⟩







-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- Every member of a lifted Horn-clause list has an exact source
    witness; this records the safe range-recovery property explicitly. -/
theorem mem_hashLiftHornClause_range {L : Language} (hNoEq : L.withoutEquality)
    (c' : FOHornClause (HashLanguage L) (by all_goals exact hNoEq)) (S : List (FOHornClause L hNoEq))
    (h : c' ∈ S.map (hashLiftHornClause (hNoEq := by all_goals exact hNoEq))) :
    ∃ c ∈ S, (hashLiftHornClause (hNoEq := by all_goals exact hNoEq)) c = c' :=
  List.mem_map.mp h

-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.HornEncoding
/-- The computable term-variable enumeration is unchanged by lifting. -/
theorem hashLiftTerm_termVarsList {L : Language} (t : Term L) :
    termVarsList (hashLiftTerm t) = termVarsList t := by
  induction t with
  | var => rfl
  | const => rfl
  | func _ args ih =>
    simp only [hashLiftTerm,
      LCS.Herbrand.SHGTheorem.liftTermSkolem, termVarsList]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    exact ih i

-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.HornEncoding
/-- The computable formula-variable enumeration is unchanged by lifting. -/
theorem hashLiftFormula_formulaVarsList {L : Language} (A : FormulaN L) :
    formulaVarsList (hashLiftFormula A) = formulaVarsList A := by
  induction A with
  | predN _ args =>
    simp only [hashLiftFormula,
      LCS.Herbrand.SHGTheorem.liftFormulaSkolem, formulaVarsList]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    exact hashLiftTerm_termVarsList (args i)
  | eq_ _ t₁ t₂ =>
    simp [hashLiftFormula, LCS.Herbrand.SHGTheorem.liftFormulaSkolem,
      formulaVarsList, hashLiftTerm_termVarsList]
  | neg _ ih => exact ih
  | conj _ _ ihA ihB =>
    simp [hashLiftFormula, LCS.Herbrand.SHGTheorem.liftFormulaSkolem,
      formulaVarsList, ihA, ihB]
  | disj _ _ ihA ihB =>
    simp [hashLiftFormula, LCS.Herbrand.SHGTheorem.liftFormulaSkolem,
      formulaVarsList, ihA, ihB]
  | impl _ _ ihA ihB =>
    simp [hashLiftFormula, LCS.Herbrand.SHGTheorem.liftFormulaSkolem,
      formulaVarsList, ihA, ihB]
  | all _ _ ih => exact ih
  | ex _ _ ih => exact ih

-- retained: used by LCS.SLD.FirstOrder.GroundLifting
/-- Clause-form term variables are unchanged by lifting. -/
theorem hashLiftTerm_termVars {L : Language} (t : Term L) :
    termVars (hashLiftTerm t) = termVars t := by
  induction t with
  | var => rfl
  | const => rfl
  | func _ args ih =>
    funext x
    apply propext
    change (∃ i, termVars (hashLiftTerm (args i)) x) ↔
      ∃ i, termVars (args i) x
    exact
      ⟨fun ⟨i, hi⟩ => ⟨i, (ih i) ▸ hi⟩,
       fun ⟨i, hi⟩ => ⟨i, (ih i).symm ▸ hi⟩⟩

-- retained: used by LCS.SLD.FirstOrder.Soundness
/-- Clause-form formula variables are unchanged by lifting. -/
theorem hashLiftFormula_formulaVars {L : Language} (A : FormulaN L) :
    formulaVars (hashLiftFormula A) = formulaVars A := by
  induction A with
  | predN _ args =>
    funext x
    apply propext
    change (∃ i, termVars (hashLiftTerm (args i)) x) ↔
      ∃ i, termVars (args i) x
    exact
      ⟨fun ⟨i, hi⟩ => ⟨i, (hashLiftTerm_termVars (args i)) ▸ hi⟩,
       fun ⟨i, hi⟩ =>
        ⟨i, (hashLiftTerm_termVars (args i)).symm ▸ hi⟩⟩
  | eq_ _ t₁ t₂ =>
    simp [hashLiftFormula, LCS.Herbrand.SHGTheorem.liftFormulaSkolem,
      formulaVars, hashLiftTerm_termVars]
  | neg _ ih => exact ih
  | conj _ _ ihA ihB =>
    simp [hashLiftFormula, LCS.Herbrand.SHGTheorem.liftFormulaSkolem,
      formulaVars, ihA, ihB]
  | disj _ _ ihA ihB =>
    simp [hashLiftFormula, LCS.Herbrand.SHGTheorem.liftFormulaSkolem,
      formulaVars, ihA, ihB]
  | impl _ _ ihA ihB =>
    simp [hashLiftFormula, LCS.Herbrand.SHGTheorem.liftFormulaSkolem,
      formulaVars, ihA, ihB]
  | all _ _ ih => exact ih
  | ex _ _ ih => exact ih

-- retained: used by LCS.SLD.FirstOrder.GroundLifting
/-- Structural atom-variable sets are unchanged by lifting. -/
theorem hashLiftAtom_vars {L : Language} (hNoEq : L.withoutEquality)  (atom : FOAtom L hNoEq) :
    ((hashLiftAtom (hNoEq := by all_goals exact hNoEq)) atom).vars = atom.vars := by
  cases atom with
  | predN P args =>
      funext x
      apply propext
      change (∃ i, termVars (hashLiftTerm (args i)) x) ↔
        ∃ i, termVars (args i) x
      exact
        ⟨fun ⟨i, hi⟩ => ⟨i, (hashLiftTerm_termVars (args i)) ▸ hi⟩,
         fun ⟨i, hi⟩ =>
          ⟨i, (hashLiftTerm_termVars (args i)).symm ▸ hi⟩⟩
  | eq_ hL lhs rhs =>
      simp [hashLiftAtom, FOAtomCore.vars, hashLiftTerm_termVars]









-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.HornEncoding
/-- Closure-variable enumerations agree up to permutation after lifting (SQ16). -/
theorem hashLiftHornClause_hornClauseVarsList {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) (c : FOHornClause L hNoEq) :
    (hornClauseVarsList (L := HashLanguage L) hNoEq (hashLiftFormula Afalsum) (hashLiftHornClause hNoEq c)).Perm
      (hornClauseVarsList hNoEq Afalsum c) := by
  -- REPAIR(T9-77a): proof pending — migration to extensional bodies / renamed-head steps
  sorry

-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.HornEncoding
/-- Lifting commutes with the literal-to-formula helper. -/
theorem hashLiftLiteral_litToFormula {L : Language} (hNoEq : L.withoutEquality)  (lit : FOLiteral L hNoEq) :
    hashLiftFormula ((clauseToFormula.litToFormula (hNoEq := by all_goals exact hNoEq)) lit) =
      (clauseToFormula.litToFormula (hNoEq := by all_goals exact hNoEq)) ((hashLiftLiteral (hNoEq := by all_goals exact hNoEq)) lit) := by
  cases lit <;>
    simp [clauseToFormula.litToFormula, hashLiftLiteral,
      (hashLiftAtom_toFormula (hNoEq := by all_goals exact hNoEq)), hashLiftFormula,
      LCS.Herbrand.SHGTheorem.liftFormulaSkolem]

-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.HornEncoding
/-- Lifting commutes exactly with clause disjunction. -/
theorem hashLiftFormula_clauseToFormula {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) (C : FOClause L hNoEq) :
    hashLiftFormula ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) Afalsum C) =
      (clauseToFormula (hNoEq := by all_goals exact hNoEq)) (hashLiftFormula Afalsum) ((hashLiftFOClause (hNoEq := by all_goals exact hNoEq)) C) := by
  induction C with
  | nil => rfl
  | cons lit rest ih =>
    cases rest with
    | nil =>
      simp [clauseToFormula, hashLiftFOClause,
        (hashLiftLiteral_litToFormula (hNoEq := by all_goals exact hNoEq))]
    | cons lit₂ rest =>
      simp only [clauseToFormula, hashLiftFOClause, List.map,
        LCS.Herbrand.SHGTheorem.liftFormulaSkolem,
        (hashLiftLiteral_litToFormula (hNoEq := by all_goals exact hNoEq))]
      exact congrArg
        (FormulaN.disj
          ((clauseToFormula.litToFormula (hNoEq := by all_goals exact hNoEq)) ((hashLiftLiteral (hNoEq := by all_goals exact hNoEq)) lit))) ih

-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.HornEncoding
/-- Lifting commutes with a list-fold of universal quantifiers. -/
theorem hashLiftFormula_foldr_all {L : Language}
    (fvs : List Nat) (A : FormulaN L) :
    hashLiftFormula
        (fvs.foldr (fun v acc => FormulaN.all v acc) A) =
      fvs.foldr (fun v acc => FormulaN.all v acc) (hashLiftFormula A) := by
  induction fvs with
  | nil => rfl
  | cons v rest ih =>
    simp only [List.foldr,
      LCS.Herbrand.SHGTheorem.liftFormulaSkolem]
    exact congrArg (FormulaN.all v) ih

-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.HornEncoding
/-- Lifting commutes exactly with universal closure of a clause. -/
theorem hashLiftFormula_universalClosure {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) (C : FOClause L hNoEq) (fvs : List Nat) :
    hashLiftFormula ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) Afalsum C fvs) =
      (FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) (hashLiftFormula Afalsum)
        ((hashLiftFOClause (hNoEq := by all_goals exact hNoEq)) C) fvs := by
  unfold FOClause.universalClosure
  rw [hashLiftFormula_foldr_all, (hashLiftFormula_clauseToFormula (hNoEq := by all_goals exact hNoEq))]

-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.HornEncoding
/-- Horn-list encoding commutes semantically with hash lifting; enumerations
    may choose different disjunction and quantifier orders (SQ16). -/
theorem hashLiftFormula_hornClauses_to_formulaN {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) (S : List (FOHornClause L hNoEq))
    (M : Structure (HashLanguage L)) (s : Assignment M) :
    formulaEvalN M (hashLiftFormula (hornClauses_to_formulaN hNoEq Afalsum S)) s ↔
      formulaEvalN M (hornClauses_to_formulaN hNoEq (hashLiftFormula Afalsum)
        (S.map (hashLiftHornClause hNoEq))) s := by
  -- REPAIR(T9-77a): proof pending — migration to extensional bodies / renamed-head steps
  sorry

-- retained: used by LCS.SLD.FirstOrder.Completeness, LCS.SLD.FirstOrder.HornEncoding
/-- Lift a §7.6 Skolem specification itself into the hash language.
    Formula structure is unchanged, so all specification invariants are
    inherited from the source specification. -/
@[blueprint "chap9__theorem_9_4_1"]
def hashLiftSkolemSpec {L : Language}
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L) :
    LCS.Herbrand.SHGTheorem.SkolemSpec (HashLanguage L) where
  source := hashLiftFormula spec.source
  hNNF := hashLiftFormula_isNNF spec.source spec.hNNF
  hRect := hashLiftFormula_isRectified spec.source spec.hRect
  hSentence := (hashLiftFormula_isClosed_iff spec.source).mpr spec.hSentence

-- retained: used by LCS.SLD.FirstOrder.HornEncoding
/-- The lifted specification has exactly the lifted source. -/
theorem hashLiftSkolemSpec_source {L : Language}
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L) :
    (hashLiftSkolemSpec spec).source = hashLiftFormula spec.source :=
  rfl











-- retained: used by LCS.SLD.FirstOrder.HornEncoding
/-- Hash lifting does not alter the exact number of Skolem allocations
    computed from a specification's source. -/
theorem hashLiftSkolemSpec_n {L : Language}
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L) :
    (hashLiftSkolemSpec spec).n = spec.n := by
  rw [LCS.Herbrand.SHGTheorem.SkolemSpec.n_eq_descriptorCount,
    LCS.Herbrand.SHGTheorem.SkolemSpec.n_eq_descriptorCount]
  exact LCS.Herbrand.SHGTheorem.liftFormulaSkolem_descriptorCount
    (skolemRank := hashSkolemRank) spec.source



-- retained: used by LCS.SLD.FirstOrder.HornEncoding
/-- The base-language reduct of a hash-language structure. -/
def hashReduct {L : Language}
    (N : Structure (HashLanguage L)) : Structure L where
  carrier := N.carrier
  carrierNonempty := N.carrierNonempty
  interpFunc := fun f args => N.interpFunc (Sum.inl f) args
  interpConst := fun c => N.interpConst (Sum.inl c)
  interpPred := fun P args => N.interpPred P args

-- retained: used by LCS.SLD.FirstOrder.HornEncoding
/-- Every hash-language structure is an expansion of its reduct. -/
theorem hashReduct_isExpansion {L : Language}
    (N : Structure (HashLanguage L)) :
    LCS.Herbrand.SHGTheorem.Main.isExpansion
      L 1 hashSkolemRank (hashReduct N) N :=
  ⟨rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => Iff.rfl⟩

-- retained: used by LCS.SLD.FirstOrder.HornEncoding
/-- A canonical expansion of a base structure to the hash language.
    The fresh nullary symbol receives an arbitrary carrier element. -/
noncomputable def hashExpansion {L : Language}
    (M : Structure L) : Structure (HashLanguage L) :=
  haveI : ∀ (P : Prop), Decidable P := Classical.propDecidable
  { carrier := M.carrier
    carrierNonempty := M.carrierNonempty
    interpFunc := fun fsym args =>
      match fsym with
      | Sum.inl f => M.interpFunc f args
      | Sum.inr _ => Classical.choice M.carrierNonempty
    interpConst := fun c => match c with
      | .inl c => M.interpConst c
      | .inr _ => Classical.choice M.carrierNonempty
    interpPred := fun P args => M.interpPred P args }

-- retained: used by LCS.SLD.FirstOrder.HornEncoding
/-- The canonical hash expansion agrees with the base structure on all
    source-language symbols. -/
theorem hashExpansion_isExpansion {L : Language} (M : Structure L) :
    LCS.Herbrand.SHGTheorem.Main.isExpansion
      L 1 hashSkolemRank M (hashExpansion M) :=
  ⟨rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => Iff.rfl⟩

-- retained: used by LCS.SLD.FirstOrder.HornEncoding
/-- Evaluation of a base formula in a reduct is equivalent to evaluation
    of its exact lift in the original hash-language structure. -/
theorem hashLiftFormula_eval_reduct_iff {L : Language}
    (N : Structure (HashLanguage L))
    (s : Assignment (hashReduct N)) (A : FormulaN L) :
    formulaEvalN (hashReduct N) A s ↔
      formulaEvalN N (hashLiftFormula A) s := by
  simpa [hashLiftFormula, hashReduct_isExpansion] using
    (LCS.Herbrand.SHGTheorem.Main.liftFormulaSkolem_eval_iff
      (hashReduct N) N (hashReduct_isExpansion N) s A)

-- retained: used by LCS.SLD.FirstOrder.HornEncoding
/-- Evaluation is also preserved by the canonical expansion. -/
theorem hashLiftFormula_eval_expansion_iff {L : Language}
    (M : Structure L) (s : Assignment M) (A : FormulaN L) :
    formulaEvalN M A s ↔
      formulaEvalN (hashExpansion M) (hashLiftFormula A) s := by
  simpa [hashLiftFormula, hashExpansion_isExpansion] using
    (LCS.Herbrand.SHGTheorem.Main.liftFormulaSkolem_eval_iff
      M (hashExpansion M) (hashExpansion_isExpansion M) s A)

-- retained: used by LCS.SLD.FirstOrder.HornEncoding
/-- Formula satisfiability is reflected and preserved by exact hash lifting. -/
theorem satisfiableN_hashLiftFormula_iff {L : Language}
    (A : FormulaN L) :
    satisfiableN (hashLiftFormula A) ↔ satisfiableN A := by
  constructor
  · rintro ⟨N, s, hA⟩
    exact ⟨hashReduct N, s,
      (hashLiftFormula_eval_reduct_iff N s A).mpr hA⟩
  · rintro ⟨M, s, hA⟩
    exact ⟨hashExpansion M, s,
      (hashLiftFormula_eval_expansion_iff M s A).mp hA⟩

-- retained: used by LCS.SLD.FirstOrder.HornEncoding
/-- Formula unsatisfiability is reflected and preserved by exact lifting. -/
theorem unsatisfiableN_hashLiftFormula_iff {L : Language}
    (A : FormulaN L) :
    ¬ satisfiableN (hashLiftFormula A) ↔ ¬ satisfiableN A :=
  not_congr (satisfiableN_hashLiftFormula_iff A)

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- For a nonempty Horn list, hash lifting preserves and reflects the
    semantic unsatisfiability of the represented clause set. -/
theorem hashLiftHornClauseSet_isUnsatisfiable_iff {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) (S : List (FOHornClause L hNoEq))
    (hNe : S ≠ []) :
    (FOHornClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) (hashLiftFormula Afalsum)
        (S.map (hashLiftHornClause (hNoEq := by all_goals exact hNoEq))) ↔
      (FOHornClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) Afalsum S := by
  have hMapNe : S.map (hashLiftHornClause (hNoEq := by all_goals exact hNoEq)) ≠ [] := by
    simpa using hNe
  calc
    (FOHornClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) (hashLiftFormula Afalsum)
        (S.map (hashLiftHornClause (hNoEq := by all_goals exact hNoEq))) ↔
        ¬ satisfiableN
          ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) (hashLiftFormula Afalsum)
            (S.map (hashLiftHornClause (hNoEq := by all_goals exact hNoEq)))) :=
      ((satisfiableN_hornClauseSet_iff (hNoEq := by all_goals exact hNoEq))
        (hashLiftFormula Afalsum) (S.map (hashLiftHornClause (hNoEq := by all_goals exact hNoEq))) hMapNe).symm
    _ ↔ ¬ satisfiableN
          (hashLiftFormula ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum S)) := by
      apply not_congr
      unfold satisfiableN satisfiableInN
      apply exists_congr
      intro M
      apply exists_congr
      intro s
      exact (hashLiftFormula_hornClauses_to_formulaN hNoEq Afalsum S M s).symm
    _ ↔ ¬ satisfiableN ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum S) :=
      unsatisfiableN_hashLiftFormula_iff
        ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum S)
    _ ↔ (FOHornClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) Afalsum S :=
      (satisfiableN_hornClauseSet_iff (hNoEq := by all_goals exact hNoEq)) Afalsum S hNe

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- Forward form of lifted Horn unsatisfiability transfer. -/
theorem hashLiftHornClauseSet_isUnsatisfiable {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) (S : List (FOHornClause L hNoEq))
    (hNe : S ≠ [])
    (hUnsat : (FOHornClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) Afalsum S) :
    (FOHornClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) (hashLiftFormula Afalsum)
      (S.map (hashLiftHornClause (hNoEq := by all_goals exact hNoEq))) :=
  ((hashLiftHornClauseSet_isUnsatisfiable_iff (hNoEq := by all_goals exact hNoEq)) Afalsum S hNe).mpr hUnsat

-- ===================================================================
-- Safe hash lowering algebra for the §9.4 ground transcript adapter
-- ===================================================================

-- retained: used by LCS.SLD.FirstOrder.GroundLifting, LCS.SLD.FirstOrder.HornEncoding
/-- Lower hash-language terms to `L`: preserve base symbols and send the
    fresh constant to the caller-selected variable `k`. -/
def hashLowerTerm {L : Language} (k : Nat) :
    Term (HashLanguage L) → Term L
  | .var x => .var x
  | .const (.inl c) => .const c
  | .const (.inr _) => .var k
  | .func (Sum.inl f) args =>
      .func f (fun i => hashLowerTerm k (args i))
  | .func (Sum.inr _) _ => .var k

-- retained: used by LCS.SLD.FirstOrder.GroundLifting, LCS.SLD.FirstOrder.HornEncoding, LCS.SLD.FirstOrder.Soundness
/-- Structural formula lowering induced by `hashLowerTerm`.  Predicate
    symbols and every logical constructor are reconstructed exactly. -/
def hashLowerFormula {L : Language} (k : Nat) :
    FormulaN (HashLanguage L) → FormulaN L
  | .predN P args => .predN P (fun i => hashLowerTerm k (args i))
  | .eq_ hL t₁ t₂ =>
      .eq_ hL (hashLowerTerm k t₁) (hashLowerTerm k t₂)
  | .neg A => .neg (hashLowerFormula k A)
  | .conj A B => .conj (hashLowerFormula k A) (hashLowerFormula k B)
  | .disj A B => .disj (hashLowerFormula k A) (hashLowerFormula k B)
  | .impl A B => .impl (hashLowerFormula k A) (hashLowerFormula k B)
  | .all x A => .all x (hashLowerFormula k A)
  | .ex x A => .ex x (hashLowerFormula k A)

-- retained: used by LCS.SLD.FirstOrder.GroundLifting, LCS.SLD.FirstOrder.HornEncoding, LCS.SLD.FirstOrder.Soundness
/-- Lower a hash-language substitution while keeping the hash variable
    rigid.  The override at `k` is load-bearing: a hash head is not
    affected by source substitution, so its lowered representative must
    likewise remain `.var k`. -/
def hashLowerSubst {L : Language} (k : Nat)
    (σ : Nat → Term (HashLanguage L)) : Nat → Term L :=
  fun x => if x = k then .var k else hashLowerTerm k (σ x)

-- retained: used by LCS.SLD.FirstOrder.GroundLifting
/-- The lowered substitution fixes the distinguished hash variable. -/
theorem hashLowerSubst_at {L : Language} (k : Nat)
    (σ : Nat → Term (HashLanguage L)) :
    hashLowerSubst k σ k = Term.var k := by
  simp [hashLowerSubst]

-- retained: used by LCS.SLD.FirstOrder.GroundLifting
/-- Away from the distinguished variable, substitution lowering is
    exactly pointwise term lowering. -/
theorem hashLowerSubst_off {L : Language} (k x : Nat)
    (σ : Nat → Term (HashLanguage L)) (hx : x ≠ k) :
    hashLowerSubst k σ x = hashLowerTerm k (σ x) := by
  simp [hashLowerSubst, hx]

-- retained: used by LCS.SLD.FirstOrder.HornEncoding
/-- Lowering is an exact left inverse of the base-term lift. -/
theorem hashLowerTerm_hashLiftTerm {L : Language} (k : Nat)
    (t : Term L) :
    hashLowerTerm k (hashLiftTerm t) = t := by
  induction t with
  | var => rfl
  | const => rfl
  | func f args ih =>
    simp only [hashLiftTerm,
      LCS.Herbrand.SHGTheorem.liftTermSkolem, hashLowerTerm]
    congr 1
    funext i
    exact ih i

-- retained: used by LCS.SLD.FirstOrder.GroundLifting, LCS.SLD.FirstOrder.HornEncoding, LCS.SLD.FirstOrder.Soundness
/-- Lowering is an exact left inverse of the base-formula lift. -/
theorem hashLowerFormula_hashLiftFormula {L : Language} (k : Nat)
    (A : FormulaN L) :
    hashLowerFormula k (hashLiftFormula A) = A := by
  induction A with
  | predN P args =>
    simp only [hashLiftFormula,
      LCS.Herbrand.SHGTheorem.liftFormulaSkolem, hashLowerFormula]
    congr 1
    funext i
    exact hashLowerTerm_hashLiftTerm k (args i)
  | eq_ hL t₁ t₂ =>
    simp [hashLiftFormula,
      LCS.Herbrand.SHGTheorem.liftFormulaSkolem, hashLowerFormula,
      hashLowerTerm_hashLiftTerm]
  | neg A ih =>
    simp only [hashLiftFormula,
      LCS.Herbrand.SHGTheorem.liftFormulaSkolem, hashLowerFormula]
    rw [ih]
  | conj A B ihA ihB =>
    simp only [hashLiftFormula,
      LCS.Herbrand.SHGTheorem.liftFormulaSkolem, hashLowerFormula]
    rw [ihA, ihB]
  | disj A B ihA ihB =>
    simp only [hashLiftFormula,
      LCS.Herbrand.SHGTheorem.liftFormulaSkolem, hashLowerFormula]
    rw [ihA, ihB]
  | impl A B ihA ihB =>
    simp only [hashLiftFormula,
      LCS.Herbrand.SHGTheorem.liftFormulaSkolem, hashLowerFormula]
    rw [ihA, ihB]
  | all x A ih =>
    simp only [hashLiftFormula,
      LCS.Herbrand.SHGTheorem.liftFormulaSkolem, hashLowerFormula]
    rw [ih]
  | ex x A ih =>
    simp only [hashLiftFormula,
      LCS.Herbrand.SHGTheorem.liftFormulaSkolem, hashLowerFormula]
    rw [ih]

-- retained: used by LCS.SLD.FirstOrder.HornEncoding
/-- The distinguished hash term lowers to the selected rigid variable. -/
theorem hashLowerTerm_hashTerm {L : Language} (k : Nat) :
    hashLowerTerm k (@hashTerm L) = Term.var k :=
  rfl

-- retained: used by LCS.SLD.FirstOrder.GroundLifting, LCS.SLD.FirstOrder.HornEncoding, LCS.SLD.FirstOrder.Soundness
/-- Freshness-qualified commutation of term lowering with simultaneous
    substitution.  The sharp side condition is `k ∉ termVars t`: at a
    source occurrence `.var k`, the left side sees `σ k` whereas the
    rigid right-side substitution intentionally keeps `.var k`. -/
theorem hashLowerTerm_termSubstAll {L : Language} (k : Nat)
    (t : Term (HashLanguage L))
    (σ : Nat → Term (HashLanguage L))
    (hFresh : ¬ termVars t k) :
    hashLowerTerm k (termSubstAll t σ) =
      termSubstAll (hashLowerTerm k t) (hashLowerSubst k σ) := by
  induction t with
  | var x =>
    have hx : x ≠ k := by
      intro hx
      apply hFresh
      exact hx.symm
    simp [termSubstAll, hashLowerTerm, hashLowerSubst, hx]
  | const c => cases c <;> simp [termSubstAll, hashLowerTerm, hashLowerSubst]
  | func fs args ih =>
    cases fs with
    | inl f =>
      simp only [termSubstAll, hashLowerTerm]
      congr 1
      funext i
      apply ih i
      intro hk
      exact hFresh ⟨i, hk⟩
    | inr s =>
      simp [termSubstAll, hashLowerTerm, hashLowerSubst]

-- retained: used by LCS.SLD.FirstOrder.GroundLifting, LCS.SLD.FirstOrder.HornEncoding, LCS.SLD.FirstOrder.Soundness
/-- Freshness-qualified commutation of formula lowering with simultaneous
    substitution.  `formulaSubstAll` descends under binders, so the exact
    hypothesis uses `formulaVars` (all term-variable occurrences), not
    `formulaFVN` (which removes bound occurrences). -/
theorem hashLowerFormula_formulaSubstAll {L : Language} (k : Nat)
    (A : FormulaN (HashLanguage L))
    (σ : Nat → Term (HashLanguage L))
    (hFresh : ¬ formulaVars A k) :
    hashLowerFormula k (formulaSubstAll A σ) =
      formulaSubstAll (hashLowerFormula k A) (hashLowerSubst k σ) := by
  induction A with
  | predN P args =>
    simp only [formulaSubstAll, hashLowerFormula]
    congr 1
    funext i
    apply hashLowerTerm_termSubstAll
    intro hk
    exact hFresh ⟨i, hk⟩
  | eq_ hL t₁ t₂ =>
    simp only [formulaSubstAll, hashLowerFormula]
    rw [hashLowerTerm_termSubstAll k t₁ σ
          (fun hk => hFresh (Or.inl hk)),
        hashLowerTerm_termSubstAll k t₂ σ
          (fun hk => hFresh (Or.inr hk))]
  | neg A ih =>
    simp only [formulaSubstAll, hashLowerFormula]
    rw [ih hFresh]
  | conj A B ihA ihB =>
    simp only [formulaSubstAll, hashLowerFormula]
    rw [ihA (fun hk => hFresh (Or.inl hk)),
        ihB (fun hk => hFresh (Or.inr hk))]
  | disj A B ihA ihB =>
    simp only [formulaSubstAll, hashLowerFormula]
    rw [ihA (fun hk => hFresh (Or.inl hk)),
        ihB (fun hk => hFresh (Or.inr hk))]
  | impl A B ihA ihB =>
    simp only [formulaSubstAll, hashLowerFormula]
    rw [ihA (fun hk => hFresh (Or.inl hk)),
        ihB (fun hk => hFresh (Or.inr hk))]
  | all x A ih =>
    simp only [formulaSubstAll, hashLowerFormula]
    rw [ih hFresh]
  | ex x A ih =>
    simp only [formulaSubstAll, hashLowerFormula]
    rw [ih hFresh]

-- retained: used by LCS.SLD.FirstOrder.GroundLifting
/-- On a ground hash-language term, every variable introduced by
    lowering is the distinguished variable `k`. -/
theorem hashLowerTerm_termVars_subset_singleton {L : Language} (k : Nat)
    (t : Term (HashLanguage L))
    (hGround : ∀ x, ¬ termVars t x) :
    ∀ x, termVars (hashLowerTerm k t) x → x = k := by
  induction t with
  | var x =>
    exact (hGround x rfl).elim
  | const c =>
    cases c <;> simp [hashLowerTerm, termVars]
  | func fs args ih =>
    cases fs with
    | inl f =>
      intro x hx
      obtain ⟨i, hi⟩ := hx
      exact ih i (fun y hy => hGround y ⟨i, hy⟩) x hi
    | inr s =>
      intro x hx
      exact hx



-- retained: used by LCS.SLD.FirstOrder.GroundLifting
/-- On a ground hash-language formula, every syntactic term-variable
    introduced by lowering is the distinguished variable `k`. -/
theorem hashLowerFormula_formulaVars_subset_singleton {L : Language}
    (k : Nat) (A : FormulaN (HashLanguage L))
    (hGround : ∀ x, ¬ formulaVars A x) :
    ∀ x, formulaVars (hashLowerFormula k A) x → x = k := by
  induction A with
  | predN P args =>
    intro x hx
    obtain ⟨i, hi⟩ := hx
    exact hashLowerTerm_termVars_subset_singleton k (args i)
      (fun y hy => hGround y ⟨i, hy⟩) x hi
  | eq_ hL t₁ t₂ =>
    intro x hx
    cases hx with
    | inl h =>
      exact hashLowerTerm_termVars_subset_singleton k t₁
        (fun y hy => hGround y (Or.inl hy)) x h
    | inr h =>
      exact hashLowerTerm_termVars_subset_singleton k t₂
        (fun y hy => hGround y (Or.inr hy)) x h
  | neg A ih => exact ih hGround
  | conj A B ihA ihB =>
    intro x hx
    exact hx.elim
      (ihA (fun y hy => hGround y (Or.inl hy)) x)
      (ihB (fun y hy => hGround y (Or.inr hy)) x)
  | disj A B ihA ihB =>
    intro x hx
    exact hx.elim
      (ihA (fun y hy => hGround y (Or.inl hy)) x)
      (ihB (fun y hy => hGround y (Or.inr hy)) x)
  | impl A B ihA ihB =>
    intro x hx
    exact hx.elim
      (ihA (fun y hy => hGround y (Or.inl hy)) x)
      (ihB (fun y hy => hGround y (Or.inr hy)) x)
  | all x A ih => exact ih hGround
  | ex x A ih => exact ih hGround





end LCS.SLD.FirstOrder
end

