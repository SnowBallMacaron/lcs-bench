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
import LCS.SLD.FirstOrder.HashLanguage
import LCS.SLD.FirstOrder.HornEncoding
import LCS.SLD.FirstOrder.Soundness
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

/-- Theorem 9.4.1 (required helper): Every `(x, t)` entry in
    `ciExtractSubstFromForallChain ci` has a closed witness term `t`.

    STRUCTURAL FACT. The chain is built by recursively traversing ci through
    `.forallInst` constructors; at each level, the first witness term `t₀`
    is paired with the bound variable. The `.forallInst` constructor of
    `CInstance` requires the closedness proof `hGround₀ : isClosed t₀` as a
    field, so every `t₀` in the chain is structurally closed. -/
theorem ciExtractSubstFromForallChain_entries_closed
    {L : Language} {n : Nat} {skolemRank : Fin n → Nat} :
    ∀ (ci : LCS.Herbrand.SHGTheorem.CInstance
        (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank))
      (p : Nat × Term
        (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank)),
      p ∈ ciExtractSubstFromForallChain
        (n := n) (skolemRank := skolemRank) ci →
      LCS.FirstOrder.Basic.Term.isClosed p.2 := by
-- BEGIN PROOF
  intro ci
  match ci with
  | .atom B hAtom =>
    intro p hp; simp [ciExtractSubstFromForallChain] at hp
  | .negAtom B hAtom =>
    intro p hp; simp [ciExtractSubstFromForallChain] at hp
  | .connective star C D H K =>
    intro p hp; simp [ciExtractSubstFromForallChain] at hp
  | .forallInst x C t₀ h₀ tsRest hsRest hG₀ hGR =>
    intro p hp
    simp only [ciExtractSubstFromForallChain] at hp
    cases hp with
    | head =>
      show LCS.FirstOrder.Basic.Term.isClosed (x, t₀).2
      exact hG₀
    | tail _ hRest =>
      exact ciExtractSubstFromForallChain_entries_closed h₀ p hRest

/-- Theorem 9.4.1 (required helper): Structural predicate asserting that a
    `FormulaN` contains no existential subformula anywhere. This is
    exactly the property that makes Def 7.6.2's computed allocation
    list, and hence `SkolemSpec.n`, empty. -/
def formulaHasNoEx {L : Language} : FormulaN L → Prop
  | .predN _ _ => True
  | .eq_ _ _ _ => True
  | .neg A => formulaHasNoEx A
  | .conj A B => formulaHasNoEx A ∧ formulaHasNoEx B
  | .disj A B => formulaHasNoEx A ∧ formulaHasNoEx B
  | .impl A B => formulaHasNoEx A ∧ formulaHasNoEx B
  | .all _ A => formulaHasNoEx A
  | .ex _ _ => False

/-- Theorem 9.4.1 (required helper): atomic formulas have no existential
    subformula. -/
theorem formulaHasNoEx_of_atomic {L : Language}
    (A : FormulaN L) (hA : FormulaN.isAtomic A = true) : formulaHasNoEx A := by
-- BEGIN PROOF
  cases A with
  | predN _ _ => exact True.intro
  | eq_ _ _ _ => exact True.intro
  | _ => simp [FormulaN.isAtomic] at hA

/-- Theorem 9.4.1 (required helper): A literal's wrapped formula has
    no `.ex` whenever the underlying formula is atomic (the literal
    is either `.pos B` or `.neg B` with `B` atomic). -/
theorem formulaHasNoEx_of_litToFormula {L : Language} (hNoEq : L.withoutEquality)
    (lit : FOLiteral L hNoEq) (hAt : FormulaN.isAtomic (FOLiteralCore.formula lit) = true) :
    formulaHasNoEx ((clauseToFormula.litToFormula (hNoEq := by all_goals exact hNoEq)) lit) := by
-- BEGIN PROOF
  cases lit with
  | pos B =>
    simp only [clauseToFormula.litToFormula, FOLiteral.formula, FOLiteralCore.formula] at hAt ⊢
    exact formulaHasNoEx_of_atomic B.toFormula hAt
  | neg B =>
    simp only [clauseToFormula.litToFormula, FOLiteral.formula, FOLiteralCore.formula] at hAt ⊢
    show formulaHasNoEx (FormulaN.neg B.toFormula)
    exact formulaHasNoEx_of_atomic B.toFormula hAt

/-- Theorem 9.4.1 (required helper): `clauseToFormula` preserves
    existence-freeness: if `A` and every literal in the clause wraps an
    atomic formula, then the resulting disjunction has no `.ex`. The
    empty-clause case folds to `FormulaN.falsum A = A ∧ ¬A`, which has
    no `.ex` when `A` does. -/
theorem formulaHasNoEx_clauseToFormula {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (hA : formulaHasNoEx A)
    (C : FOClause L hNoEq)
    (hLitAt : ∀ lit ∈ C, FormulaN.isAtomic (FOLiteralCore.formula lit) = true) :
    formulaHasNoEx ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C) := by
-- BEGIN PROOF
  induction C with
  | nil =>
    show formulaHasNoEx (FormulaN.falsum A)
    exact ⟨hA, hA⟩
  | cons hd tl ih =>
    cases tl with
    | nil =>
      show formulaHasNoEx ((clauseToFormula.litToFormula (hNoEq := by all_goals exact hNoEq)) hd)
      exact (formulaHasNoEx_of_litToFormula (hNoEq := by all_goals exact hNoEq)) hd (hLitAt hd List.mem_cons_self)
    | cons hd2 tl2 =>
      show formulaHasNoEx (FormulaN.disj _ _)
      refine ⟨?_, ?_⟩
      · exact (formulaHasNoEx_of_litToFormula (hNoEq := by all_goals exact hNoEq)) hd (hLitAt hd List.mem_cons_self)
      · exact ih (fun lit hmem => hLitAt lit (List.mem_cons_of_mem _ hmem))

/-- Theorem 9.4.1 (required helper): Wrapping a formula with a
    `foldr .all` sequence preserves existence-freeness. -/
theorem formulaHasNoEx_foldr_all {L : Language}
    (fvs : List Nat) (base : FormulaN L) (hBase : formulaHasNoEx base) :
    formulaHasNoEx (fvs.foldr (fun v acc => FormulaN.all v acc) base) := by
-- BEGIN PROOF
  induction fvs with
  | nil => exact hBase
  | cons v rest ih =>
    show formulaHasNoEx (FormulaN.all v _)
    exact ih

/-- Theorem 9.4.1 (required helper): `FOClause.universalClosure` of a
    clause with atomic literals and an `.ex`-free falsum witness has
    no `.ex`. -/
theorem formulaHasNoEx_universalClosure {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (hA : formulaHasNoEx A)
    (C : FOClause L hNoEq)
    (hLitAt : ∀ lit ∈ C, FormulaN.isAtomic (FOLiteralCore.formula lit) = true)
    (fvs : List Nat) :
    formulaHasNoEx ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) A C fvs) := by
-- BEGIN PROOF
  unfold FOClause.universalClosure
  exact formulaHasNoEx_foldr_all fvs ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C)
    ((formulaHasNoEx_clauseToFormula (hNoEq := by all_goals exact hNoEq)) A hA C hLitAt)

/-- Theorem 9.4.1 (required helper): `hornClauses_to_formulaN Afalsum S`
    has no existential subformula when `Afalsum` is atomic. Clause atoms
    are atomic by their structural carrier. This fact computes
    `spec.n = 0`. -/
theorem hornClauses_to_formulaN_hasNoEx {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (hAf : FormulaN.isAtomic Afalsum = true)
    (S : List (FOHornClause L hNoEq)) :
    formulaHasNoEx ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum S) := by
-- BEGIN PROOF
  have hAfNo : formulaHasNoEx Afalsum := formulaHasNoEx_of_atomic Afalsum hAf
  induction S with
  | nil =>
    show formulaHasNoEx Afalsum
    exact hAfNo
  | cons hd tl ih =>
    cases tl with
    | nil =>
      show formulaHasNoEx ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) _ _ _)
      exact (formulaHasNoEx_universalClosure (hNoEq := by all_goals exact hNoEq)) Afalsum hAfNo (hd.toFOClause (hNoEq := by all_goals exact hNoEq))
        ((toFOClause_literal_atomic (hNoEq := by all_goals exact hNoEq)) hd) ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum hd)
    | cons hd2 tl2 =>
      show formulaHasNoEx (FormulaN.conj _ _)
      refine ⟨?_, ?_⟩
      · exact (formulaHasNoEx_universalClosure (hNoEq := by all_goals exact hNoEq)) Afalsum hAfNo (hd.toFOClause (hNoEq := by all_goals exact hNoEq))
          ((toFOClause_literal_atomic (hNoEq := by all_goals exact hNoEq)) hd) ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum hd)
      · exact ih

/-- Theorem 9.4.1 (required helper): If a formula has no `.ex` subformula,
    then `universalScopeAux` produces no pair `(FormulaN.ex _ _, _)` for
    any accumulator scope. This is the bridge from the structural
    `formulaHasNoEx` predicate to the computed allocation filter. -/
theorem formulaHasNoEx_universalScopeAux_no_ex {L : Language} :
    ∀ (A : FormulaN L) (acc : List Nat),
      formulaHasNoEx A →
      ∀ x C scope,
        (FormulaN.ex x C, scope) ∉
          LCS.Herbrand.SHGTheorem.universalScopeAux A acc
  | .predN _ _, acc, _, x, C, scope => by
    simp only [LCS.Herbrand.SHGTheorem.universalScopeAux, List.mem_singleton,
      Prod.mk.injEq]
    rintro ⟨hEq, _⟩
    cases hEq
  | .eq_ _ _ _, acc, _, x, C, scope => by
    simp only [LCS.Herbrand.SHGTheorem.universalScopeAux, List.mem_singleton,
      Prod.mk.injEq]
    rintro ⟨hEq, _⟩
    cases hEq
  | .neg A, acc, _hA, x, C, scope => by
    simp only [LCS.Herbrand.SHGTheorem.universalScopeAux, List.mem_singleton,
      Prod.mk.injEq]
    rintro ⟨hEq, _⟩
    cases hEq
  | .impl A B, acc, _hAB, x, C, scope => by
    simp only [LCS.Herbrand.SHGTheorem.universalScopeAux, List.mem_singleton,
      Prod.mk.injEq]
    rintro ⟨hEq, _⟩
    cases hEq
  | .conj A B, acc, hAB, x, C, scope => by
    simp only [LCS.Herbrand.SHGTheorem.universalScopeAux]
    intro hmem
    rw [List.mem_append, List.mem_append, List.mem_singleton,
      Prod.mk.injEq] at hmem
    rcases hmem with (⟨hEq, _⟩ | hInA) | hInB
    · cases hEq
    · exact formulaHasNoEx_universalScopeAux_no_ex A acc hAB.1 x C scope hInA
    · exact formulaHasNoEx_universalScopeAux_no_ex B acc hAB.2 x C scope hInB
  | .disj A B, acc, hAB, x, C, scope => by
    simp only [LCS.Herbrand.SHGTheorem.universalScopeAux]
    intro hmem
    rw [List.mem_append, List.mem_append, List.mem_singleton,
      Prod.mk.injEq] at hmem
    rcases hmem with (⟨hEq, _⟩ | hInA) | hInB
    · cases hEq
    · exact formulaHasNoEx_universalScopeAux_no_ex A acc hAB.1 x C scope hInA
    · exact formulaHasNoEx_universalScopeAux_no_ex B acc hAB.2 x C scope hInB
  | .all y A, acc, hA, x, C, scope => by
    simp only [LCS.Herbrand.SHGTheorem.universalScopeAux]
    intro hmem
    rw [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hmem
    cases hmem with
    | inl hHead =>
      cases hHead.1
    | inr hIn =>
      exact formulaHasNoEx_universalScopeAux_no_ex A (acc ++ [y]) hA x C scope hIn
  | .ex _ _, _, hA, _, _, _ => fun _ => hA.elim

/-- Theorem 9.4.1 (required helper): In a `SkolemSpec` constructed over
    `hornClauses_to_formulaN` (atomic Afalsum, atomic clause atoms),
    `spec.n = 0`. This is a direct consequence of Def 7.6.2's computed
    allocation list: Horn clauses have no existential subformulae. -/
theorem spec_n_eq_zero_of_hornClauses_source {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (hAf : FormulaN.isAtomic Afalsum = true)
    (S : List (FOHornClause L hNoEq))
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (hSpec : spec.source = (hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum S) :
    spec.n = 0 := by
-- BEGIN PROOF
  apply LCS.Herbrand.SHGTheorem.SkolemSpec.n_eq_zero_of_no_ex_source
  intro x C scope hmem
  rw [hSpec] at hmem
  exact formulaHasNoEx_universalScopeAux_no_ex
    ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum S) []
    ((hornClauses_to_formulaN_hasNoEx (hNoEq := by all_goals exact hNoEq)) Afalsum hAf S) x C scope hmem

/-- Theorem 9.4.1 (required helper): when `n = 0`, every term of the
    Skolem-extended language `SkolemLanguage L 0 _` automatically has
    `termNoSumInr` — because the `Sum.inr i` constructor would require
    `i : Fin 0`, which is uninhabited. Structural induction on the term. -/
theorem termNoSumInr_of_n_eq_zero {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat} (hn : n = 0) :
    ∀ (t : Term (LCS.Herbrand.SHGTheorem.SkolemLanguage
        (L := L) n skolemRank)),
      termNoSumInr t := by
-- BEGIN PROOF
  intro t
  induction t with
  | var _ => exact True.intro
  | const _ => exact True.intro
  | func f args ih =>
    cases f with
    | inl _ =>
      intro i
      exact ih i
    | inr idx =>
      subst hn
      exact idx.val.elim0

/-- Theorem 9.4.1 (required helper): `ci.source = .conj A B` together with
    `WellFormed ci` forces the constructor `.connective true A B H K`
    with WellFormed children whose sources match `A` and `B`.

    STRUCTURAL FACT. `CInstance.source` is a function by case analysis on
    the constructor: `.atom B _ → B` (atomic, not `.conj`); `.negAtom B _ →
    .neg B` (not `.conj`); `.connective true C D _ _ → .conj C D`;
    `.connective false C D _ _ → .disj C D` (not `.conj`); `.forallInst x C
    _ _ _ _ _ _ → .all x C` (not `.conj`). Only `.connective true` yields a
    `.conj`, and its operands coincide with the source's two arguments. -/
theorem ci_connective_true_of_source_conj {L : Language}
    (ci : LCS.Herbrand.SHGTheorem.CInstance L) (A B : FormulaN L)
    (hsrc : ci.source = FormulaN.conj A B)
    (hWF : LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci) :
    ∃ (H K : LCS.Herbrand.SHGTheorem.CInstance L),
      ci = LCS.Herbrand.SHGTheorem.CInstance.connective true A B H K ∧
      H.source = A ∧ K.source = B ∧
      LCS.Herbrand.SHGTheorem.CInstance.WellFormed H ∧
      LCS.Herbrand.SHGTheorem.CInstance.WellFormed K := by
-- BEGIN PROOF
  match ci, hsrc with
  | LCS.Herbrand.SHGTheorem.CInstance.connective true C D H K, hsrc =>
    simp only [LCS.Herbrand.SHGTheorem.CInstance.source] at hsrc
    injection hsrc with hC hD; subst hC; subst hD
    simp only [LCS.Herbrand.SHGTheorem.CInstance.WellFormed] at hWF
    obtain ⟨hHsrc, hKsrc, hHwf, hKwf⟩ := hWF
    exact ⟨H, K, rfl, hHsrc, hKsrc, hHwf, hKwf⟩
  | LCS.Herbrand.SHGTheorem.CInstance.atom B0 hAtom, hsrc =>
    simp only [LCS.Herbrand.SHGTheorem.CInstance.source] at hsrc; subst hsrc
    simp [FormulaN.isAtomic] at hAtom
  | LCS.Herbrand.SHGTheorem.CInstance.negAtom B0 hAtom, hsrc =>
    simp only [LCS.Herbrand.SHGTheorem.CInstance.source] at hsrc; cases hsrc
  | LCS.Herbrand.SHGTheorem.CInstance.connective false C D H K, hsrc =>
    simp only [LCS.Herbrand.SHGTheorem.CInstance.source] at hsrc; cases hsrc
  | LCS.Herbrand.SHGTheorem.CInstance.forallInst x C t₀ h₀ tsRest hsRest hG hGR, hsrc =>
    simp only [LCS.Herbrand.SHGTheorem.CInstance.source] at hsrc; cases hsrc

/-- Theorem 9.4.1 (required helper): `ci.source = .disj A B` together with
    `WellFormed ci` forces the constructor `.connective false A B H K`
    with WellFormed children whose sources match `A` and `B`.

    Mirrors `ci_connective_true_of_source_conj`: `CInstance.source` is a
    function by case analysis on the constructor; only `.connective false`
    yields a `.disj`, with its operands recorded in the source. -/
theorem ci_connective_false_of_source_disj {L : Language}
    (ci : LCS.Herbrand.SHGTheorem.CInstance L) (A B : FormulaN L)
    (hsrc : ci.source = FormulaN.disj A B)
    (hWF : LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci) :
    ∃ (H K : LCS.Herbrand.SHGTheorem.CInstance L),
      ci = LCS.Herbrand.SHGTheorem.CInstance.connective false A B H K ∧
      H.source = A ∧ K.source = B ∧
      LCS.Herbrand.SHGTheorem.CInstance.WellFormed H ∧
      LCS.Herbrand.SHGTheorem.CInstance.WellFormed K := by
-- BEGIN PROOF
  match ci, hsrc with
  | LCS.Herbrand.SHGTheorem.CInstance.connective false C D H K, hsrc =>
    simp only [LCS.Herbrand.SHGTheorem.CInstance.source] at hsrc
    injection hsrc with hC hD; subst hC; subst hD
    simp only [LCS.Herbrand.SHGTheorem.CInstance.WellFormed] at hWF
    obtain ⟨hHsrc, hKsrc, hHwf, hKwf⟩ := hWF
    exact ⟨H, K, rfl, hHsrc, hKsrc, hHwf, hKwf⟩
  | LCS.Herbrand.SHGTheorem.CInstance.atom B0 hAtom, hsrc =>
    simp only [LCS.Herbrand.SHGTheorem.CInstance.source] at hsrc; subst hsrc
    simp [FormulaN.isAtomic] at hAtom
  | LCS.Herbrand.SHGTheorem.CInstance.negAtom B0 hAtom, hsrc =>
    simp only [LCS.Herbrand.SHGTheorem.CInstance.source] at hsrc; cases hsrc
  | LCS.Herbrand.SHGTheorem.CInstance.connective true C D H K, hsrc =>
    simp only [LCS.Herbrand.SHGTheorem.CInstance.source] at hsrc; cases hsrc
  | LCS.Herbrand.SHGTheorem.CInstance.forallInst x C t₀ h₀ tsRest hsRest hG hGR, hsrc =>
    simp only [LCS.Herbrand.SHGTheorem.CInstance.source] at hsrc; cases hsrc

/-- Theorem 9.4.1 (required helper): `ci.source = .all x C` together with
    `WellFormed ci` forces the constructor `.forallInst x C t₀ h₀ tsRest
    hsRest _ _` with a first-witness child whose source is `formulaSubstN C
    t₀ x`, the tail witnesses forming a matching `WellFormedList`, and every
    witness term being closed.

    Mirrors `ci_connective_true_of_source_conj`: only `.forallInst` yields
    an `.all` source, and its bound variable + body coincide with the
    source's two arguments. -/
theorem ci_forallInst_of_source_all {L : Language}
    (ci : LCS.Herbrand.SHGTheorem.CInstance L) (x : Nat) (C : FormulaN L)
    (hsrc : ci.source = FormulaN.all x C)
    (hWF : LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci) :
    ∃ (t₀ : Term L) (h₀ : LCS.Herbrand.SHGTheorem.CInstance L)
      (tsRest : List (Term L)) (hsRest : List (LCS.Herbrand.SHGTheorem.CInstance L))
      (hG₀ : LCS.FirstOrder.Basic.Term.isClosed t₀)
      (hGR : ∀ t ∈ tsRest, LCS.FirstOrder.Basic.Term.isClosed t),
      ci = LCS.Herbrand.SHGTheorem.CInstance.forallInst x C t₀ h₀ tsRest hsRest hG₀ hGR ∧
      h₀.source = LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN C t₀ x ∧
      LCS.Herbrand.SHGTheorem.CInstance.WellFormed h₀ ∧
      LCS.Herbrand.SHGTheorem.CInstance.WellFormedList x C tsRest hsRest := by
-- BEGIN PROOF
  match ci, hsrc with
  | LCS.Herbrand.SHGTheorem.CInstance.forallInst y D t₀ h₀ tsRest hsRest hG₀ hGR, hsrc =>
    simp only [LCS.Herbrand.SHGTheorem.CInstance.source] at hsrc
    injection hsrc with hy hD; subst hy; subst hD
    simp only [LCS.Herbrand.SHGTheorem.CInstance.WellFormed] at hWF
    obtain ⟨hh0src, hh0wf, hListwf⟩ := hWF
    exact ⟨t₀, h₀, tsRest, hsRest, hG₀, hGR, rfl, hh0src, hh0wf, hListwf⟩
  | LCS.Herbrand.SHGTheorem.CInstance.atom B0 hAtom, hsrc =>
    simp only [LCS.Herbrand.SHGTheorem.CInstance.source] at hsrc; subst hsrc
    simp [FormulaN.isAtomic] at hAtom
  | LCS.Herbrand.SHGTheorem.CInstance.negAtom B0 hAtom, hsrc =>
    simp only [LCS.Herbrand.SHGTheorem.CInstance.source] at hsrc; cases hsrc
  | LCS.Herbrand.SHGTheorem.CInstance.connective true C' D H K, hsrc =>
    simp only [LCS.Herbrand.SHGTheorem.CInstance.source] at hsrc; cases hsrc
  | LCS.Herbrand.SHGTheorem.CInstance.connective false C' D H K, hsrc =>
    simp only [LCS.Herbrand.SHGTheorem.CInstance.source] at hsrc; cases hsrc

/-- Theorem 9.4.1 (required helper): `skolemFormAux` is the identity
    on formulas with no existential subformulae. Every constructor
    besides `.ex` recurses structurally, rebuilding the same node;
    `.ex` is the only branch that consumes a Skolem symbol or alters
    the formula, and `formulaHasNoEx` rules it out. -/
theorem skolemFormAux_no_ex_eq {L : Language}
    (S : LCS.Herbrand.SHGTheorem.SkolemSpec L) :
    ∀ (F : FormulaN S.language) (scope : List Nat) (i : Nat),
      formulaHasNoEx F →
      LCS.Herbrand.SHGTheorem.skolemFormAux S F scope i = (F, i) := by
-- BEGIN PROOF
  intro F
  induction F with
  | predN _ _ => intros; simp [LCS.Herbrand.SHGTheorem.skolemFormAux]
  | eq_ _ _ _ => intros; simp [LCS.Herbrand.SHGTheorem.skolemFormAux]
  | neg _ => intros; simp [LCS.Herbrand.SHGTheorem.skolemFormAux]
  | conj A B ihA ihB =>
    intros scope i hNoEx
    obtain ⟨hA, hB⟩ := hNoEx
    simp [LCS.Herbrand.SHGTheorem.skolemFormAux, ihA scope i hA, ihB scope i hB]
  | disj A B ihA ihB =>
    intros scope i hNoEx
    obtain ⟨hA, hB⟩ := hNoEx
    simp [LCS.Herbrand.SHGTheorem.skolemFormAux, ihA scope i hA, ihB scope i hB]
  | impl A B ihA ihB =>
    intros scope i hNoEx
    obtain ⟨hA, hB⟩ := hNoEx
    simp [LCS.Herbrand.SHGTheorem.skolemFormAux, ihA scope i hA, ihB scope i hB]
  | all x A ih =>
    intros scope i hNoEx
    simp [LCS.Herbrand.SHGTheorem.skolemFormAux, ih _ _ hNoEx]
  | ex _ _ _ =>
    intros _ _ hNoEx
    exact hNoEx.elim

/-- Theorem 9.4.1 (required helper): `liftFormulaSkolem` preserves the
    `formulaHasNoEx` predicate — the lift is a purely structural term
    embedding that does not introduce any `.ex` constructor. -/
theorem formulaHasNoEx_liftFormulaSkolem {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat}
    (F : FormulaN L) (hNoEx : formulaHasNoEx F) :
    formulaHasNoEx (LCS.Herbrand.SHGTheorem.liftFormulaSkolem
      (n := n) (skolemRank := skolemRank) F) := by
-- BEGIN PROOF
  induction F with
  | predN _ _ => exact True.intro
  | eq_ _ _ _ => exact True.intro
  | neg A ih =>
    simp only [LCS.Herbrand.SHGTheorem.liftFormulaSkolem, formulaHasNoEx]
    exact ih hNoEx
  | conj A B ihA ihB =>
    obtain ⟨hA, hB⟩ := hNoEx
    simp only [LCS.Herbrand.SHGTheorem.liftFormulaSkolem, formulaHasNoEx]
    exact ⟨ihA hA, ihB hB⟩
  | disj A B ihA ihB =>
    obtain ⟨hA, hB⟩ := hNoEx
    simp only [LCS.Herbrand.SHGTheorem.liftFormulaSkolem, formulaHasNoEx]
    exact ⟨ihA hA, ihB hB⟩
  | impl A B ihA ihB =>
    obtain ⟨hA, hB⟩ := hNoEx
    simp only [LCS.Herbrand.SHGTheorem.liftFormulaSkolem, formulaHasNoEx]
    exact ⟨ihA hA, ihB hB⟩
  | all x A ih =>
    simp only [LCS.Herbrand.SHGTheorem.liftFormulaSkolem, formulaHasNoEx]
    exact ih hNoEx
  | ex _ _ _ => exact hNoEx.elim

/-- Theorem 9.4.1 (required helper): When `spec.source` has no
    existential subformulae, `SK spec = liftFormulaSkolem spec.source`
    — the Skolem form degenerates to the pure language lift. The no-ex
    hypothesis forces `spec.n = 0`, so the exact top-level traversal
    reduces to `liftFormulaSkolem`. -/
theorem SK_eq_liftFormulaSkolem_of_no_ex {L : Language}
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (hNoEx : formulaHasNoEx spec.source) :
    LCS.Herbrand.SHGTheorem.SK spec =
      LCS.Herbrand.SHGTheorem.liftFormulaSkolem
        (n := spec.n) (skolemRank := spec.skolemRank) spec.source := by
-- BEGIN PROOF
  apply LCS.Herbrand.SHGTheorem.skolemForm_eq_liftFormulaSkolem_of_n_eq_zero
  apply LCS.Herbrand.SHGTheorem.SkolemSpec.n_eq_zero_of_no_ex_source
  intro x C scope hMem
  exact formulaHasNoEx_universalScopeAux_no_ex
    spec.source [] hNoEx x C scope hMem

/-- Theorem 9.4.1 (required helper): `liftFormulaSkolem` commutes with
    the `foldr .all` construction used by `FOClause.universalClosure`
    — it distributes over each `.all` node homomorphically. -/
theorem liftFormulaSkolem_foldr_all {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat}
    (fvs : List Nat) (body : FormulaN L) :
    LCS.Herbrand.SHGTheorem.liftFormulaSkolem (n := n) (skolemRank := skolemRank)
        (fvs.foldr (fun v acc => FormulaN.all v acc) body) =
      fvs.foldr (fun v acc => FormulaN.all v acc)
        (LCS.Herbrand.SHGTheorem.liftFormulaSkolem
          (n := n) (skolemRank := skolemRank) body) := by
-- BEGIN PROOF
  induction fvs with
  | nil => rfl
  | cons v rest ih =>
    simp only [List.foldr, LCS.Herbrand.SHGTheorem.liftFormulaSkolem]
    exact congrArg (FormulaN.all v) ih

/-- Theorem 9.4.1 (required helper): `formulaSubstN` commutes with the
    `foldr .all` construction when the substituted variable is not
    among the bound variables — each `.all v` matches the non-trigger
    clause of `formulaSubstN (.all v B) t x = .all v (formulaSubstN B t x)`
    whenever `x ≠ v`. Used to pass through `foldr .all`-sources during
    the forallInst-chain recursion on rectified formulas. -/
theorem formulaSubstN_foldr_all_commute {L : Language} :
    ∀ (vs : List Nat) (body : FormulaN L) (t : Term L) (x : Nat),
      x ∉ vs →
      LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN
          (vs.foldr (fun v acc => FormulaN.all v acc) body) t x =
        vs.foldr (fun v acc => FormulaN.all v acc)
          (LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN body t x) := by
-- BEGIN PROOF
  intro vs
  induction vs with
  | nil => intros; rfl
  | cons vHd vTl ih =>
    intros body t x hx
    simp only [List.foldr]
    have hNotHd : x ≠ vHd := fun h => hx (h ▸ List.mem_cons_self)
    have hNotTl : x ∉ vTl := fun h => hx (List.mem_cons_of_mem _ h)
    show LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN
      (FormulaN.all vHd _) t x = _
    simp only [LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN, bne_iff_ne]
    split
    · rw [ih _ t x hNotTl]
    · exfalso; apply hNotHd; simp_all

/-- Theorem 9.4.1 (required helper): Under `WellFormed ci` and a
    `foldr .all`-shaped source with a duplicate-free variable list,
    `ciExtractSubstFromForallChain ci` contains one entry for every
    `v ∈ vs` — the chain keys cover `vs`. The `Nodup` hypothesis is
    load-bearing: without it, `formulaSubstN` might collide with an
    inner `.all` binder and drop the variable from the chain. Proof
    by induction on `vs`, peeling one `.forallInst` layer per step via
    `ci_forallInst_of_source_all` and invoking
    `formulaSubstN_foldr_all_commute` to re-establish the `foldr .all`
    shape on the first-witness child's source. -/
theorem ciExtractSubstFromForallChain_covers_foldrAll
    {L : Language} {n : Nat} {skolemRank : Fin n → Nat} :
    ∀ (vs : List Nat) (_hNodup : vs.Nodup)
      (body : FormulaN (LCS.Herbrand.SHGTheorem.SkolemLanguage
        (L := L) n skolemRank))
      (ci : LCS.Herbrand.SHGTheorem.CInstance
        (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank))
      (_hWF : LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci)
      (_hSrc : ci.source = vs.foldr (fun v acc => FormulaN.all v acc) body)
      (v : Nat) (_hv : v ∈ vs),
      ∃ t : Term (LCS.Herbrand.SHGTheorem.SkolemLanguage
          (L := L) n skolemRank),
        (v, t) ∈ ciExtractSubstFromForallChain
          (n := n) (skolemRank := skolemRank) ci := by
-- BEGIN PROOF
  intro vs
  induction vs with
  | nil => intros _ _ _ _ _ _ hv; simp at hv
  | cons vHd vTl ih =>
    intros hNodup body ci hWF hSrc v hv
    simp only [List.foldr] at hSrc
    obtain ⟨t₀, h₀, tsRest, hsRest, hG₀, hGR, hCi, hh₀src, hh₀wf, _hList⟩ :=
      ci_forallInst_of_source_all ci vHd
        (vTl.foldr (fun v acc => FormulaN.all v acc) body) hSrc hWF
    subst hCi
    rcases List.mem_cons.mp hv with rfl | hvMem
    · refine ⟨t₀, ?_⟩
      show (v, t₀) ∈ ((v, t₀) :: ciExtractSubstFromForallChain h₀)
      exact List.mem_cons_self
    · have hNodup_tl : vTl.Nodup := hNodup.tail
      have hHd_notin : vHd ∉ vTl := (List.nodup_cons.mp hNodup).1
      have hh₀src' : h₀.source = vTl.foldr (fun v acc => FormulaN.all v acc)
          (LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN body t₀ vHd) := by
        rw [hh₀src]
        exact formulaSubstN_foldr_all_commute vTl _ t₀ vHd hHd_notin
      obtain ⟨t, ht⟩ := ih hNodup_tl
        (LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN body t₀ vHd)
        h₀ hh₀wf hh₀src' v hvMem
      refine ⟨t, ?_⟩
      show (v, t) ∈ ((vHd, t₀) :: ciExtractSubstFromForallChain h₀)
      exact List.mem_cons_of_mem _ ht

/-- Theorem 9.4.1 (required helper): Navigate `ciProjectAtClauseIndex`
    through a `liftFormulaSkolem`-lifted `hornClauses_to_formulaN` source.
    For each `k < list.length`, the returned subtree's source equals
    the lifted universal closure of `list.get ⟨k, hk⟩`, and the subtree
    is itself WellFormed.

    Proof by induction on `list`. Base case (singleton): the whole `ci`
    IS the projection and its source is `liftFormulaSkolem` of the
    single clause's universal closure. Two-or-more clauses: peel one
    `.conj` via `ci_connective_true_of_source_conj` and recurse on the
    right branch when `k ≥ 1`; return the left branch when `k = 0`. -/
theorem ciProjectAtClauseIndex_source_of_liftFormulaSkolem_hornClauses
    {L : Language} (hNoEq : L.withoutEquality)  {n : Nat} {skolemRank : Fin n → Nat} :
    ∀ (list : List (FOHornClause L hNoEq)) (Afalsum : FormulaN L)
      (k : Nat) (hk : k < list.length)
      (ci : LCS.Herbrand.SHGTheorem.CInstance
        (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank))
      (_hWF : LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci)
      (_hSrc : ci.source = LCS.Herbrand.SHGTheorem.liftFormulaSkolem
        (n := n) (skolemRank := skolemRank)
        ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum list))
      (ciClause : LCS.Herbrand.SHGTheorem.CInstance
        (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank))
      (_hProj : ciProjectAtClauseIndex (n := n) (skolemRank := skolemRank)
        ci k list.length = some ciClause),
      ciClause.source = LCS.Herbrand.SHGTheorem.liftFormulaSkolem
          (n := n) (skolemRank := skolemRank)
          ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) Afalsum ((list.get ⟨k, hk⟩).toFOClause (hNoEq := by all_goals exact hNoEq))
            ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum (list.get ⟨k, hk⟩))) ∧
        LCS.Herbrand.SHGTheorem.CInstance.WellFormed ciClause := by
-- BEGIN PROOF
  intro list
  induction list with
  | nil =>
    intros _ k hk
    simp [List.length] at hk
  | cons c1 rest ih =>
    intros Afalsum k hk ci hWF hSrc ciClause hProj
    cases rest with
    | nil =>
      have hk0 : k = 0 := by
        simp [List.length] at hk; omega
      subst hk0
      simp [ciProjectAtClauseIndex, List.length] at hProj
      subst hProj
      simp only [hornClauses_to_formulaN] at hSrc
      refine ⟨?_, hWF⟩
      show ci.source = _
      rw [hSrc]
      rfl
    | cons c2 rest' =>
      have hLen : ((c1 :: c2 :: rest').length) = (rest'.length) + 2 := by simp
      have hSrc' : ci.source = FormulaN.conj
          (LCS.Herbrand.SHGTheorem.liftFormulaSkolem
            (n := n) (skolemRank := skolemRank)
            ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) Afalsum (c1.toFOClause (hNoEq := by all_goals exact hNoEq))
              ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum c1)))
          (LCS.Herbrand.SHGTheorem.liftFormulaSkolem
            (n := n) (skolemRank := skolemRank)
            ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (c2 :: rest'))) := by
        rw [hSrc]
        simp only [hornClauses_to_formulaN,
          LCS.Herbrand.SHGTheorem.liftFormulaSkolem]
      obtain ⟨H, K, hCi, hHsrc, hKsrc, hHwf, hKwf⟩ :=
        ci_connective_true_of_source_conj ci
          (LCS.Herbrand.SHGTheorem.liftFormulaSkolem
            (n := n) (skolemRank := skolemRank)
            ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) Afalsum (c1.toFOClause (hNoEq := by all_goals exact hNoEq))
              ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum c1)))
          (LCS.Herbrand.SHGTheorem.liftFormulaSkolem
            (n := n) (skolemRank := skolemRank)
            ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (c2 :: rest')))
          hSrc' hWF
      subst hCi
      cases k with
      | zero =>
        rw [hLen] at hProj
        have hPEq : ciProjectAtClauseIndex (n := n) (skolemRank := skolemRank)
            (LCS.Herbrand.SHGTheorem.CInstance.connective true
              (LCS.Herbrand.SHGTheorem.liftFormulaSkolem
                (n := n) (skolemRank := skolemRank)
                ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) Afalsum (c1.toFOClause (hNoEq := by all_goals exact hNoEq))
                  ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum c1)))
              (LCS.Herbrand.SHGTheorem.liftFormulaSkolem
                (n := n) (skolemRank := skolemRank)
                ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (c2 :: rest')))
              H K) 0 ((rest'.length) + 2) = some H := by
          simp [ciProjectAtClauseIndex]
        rw [hPEq] at hProj
        injection hProj with heq
        subst heq
        simp only [List.get]
        exact ⟨hHsrc, hHwf⟩
      | succ k' =>
        rw [hLen] at hProj
        have hPEq : ciProjectAtClauseIndex (n := n) (skolemRank := skolemRank)
            (LCS.Herbrand.SHGTheorem.CInstance.connective true
              (LCS.Herbrand.SHGTheorem.liftFormulaSkolem
                (n := n) (skolemRank := skolemRank)
                ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) Afalsum (c1.toFOClause (hNoEq := by all_goals exact hNoEq))
                  ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum c1)))
              (LCS.Herbrand.SHGTheorem.liftFormulaSkolem
                (n := n) (skolemRank := skolemRank)
                ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (c2 :: rest')))
              H K) (k' + 1) ((rest'.length) + 2) =
          ciProjectAtClauseIndex (n := n) (skolemRank := skolemRank)
            K k' ((rest'.length) + 1) := by
          simp [ciProjectAtClauseIndex]
        rw [hPEq] at hProj
        have hk' : k' < ((c2 :: rest').length) := by simp [List.length]; omega
        have hProj' : ciProjectAtClauseIndex (n := n) (skolemRank := skolemRank)
            K k' ((c2 :: rest').length) = some ciClause := by
          rw [show ((c2 :: rest').length) = (rest'.length) + 1 from by simp]
          exact hProj
        obtain ⟨hSrcK, hWfK⟩ := ih Afalsum k' hk' K hKwf hKsrc ciClause hProj'
        refine ⟨?_, hWfK⟩
        rw [hSrcK]
        congr 2 <;> simp [List.get]

/-- Theorem 9.4.1 (required helper): Term-level free-variable coincidence:
    `termFV t x ↔ termVars t x` for every term `t`. Duplicate of the
    later `termFV_iff_termVars` — we need it ahead of
    `ciExtractSubstFromForallChain_covers_clauseFV_with_noSumInr` to
    bridge `clauseFV` (phrased via `formulaVars`) and
    `FOClause.freeVars` (phrased via `formulaFVN`) when inlining
    atomic-literal coverage. The two definitions agree pointwise since
    terms have no quantifiers. -/
theorem termFV_iff_termVars_local {L : Language} (t : Term L) (x : Nat) :
    termFV t x ↔ termVars t x := by
-- BEGIN PROOF
  induction t with
  | var n => simp [termFV, termVars, Set.singleton]
  | const c => simp only [termFV, termVars, Set.empty]
  | func f args ih =>
    simp only [termFV, termVars, Set.iUnion]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨i, (ih i).mp hi⟩
    · rintro ⟨i, hi⟩; exact ⟨i, (ih i).mpr hi⟩

/-- Theorem 9.4.1 (required helper): Under the Horn hypotheses, every
    `x ∈ FV(D[i])` has a chain entry with a `Sum.inr`-free witness,
    AND every chain entry has a `Sum.inr`-free witness.

    CONTENT. Combined coverage + `Sum.inr`-freeness claim used by
    `substFromList_ground_on_clauseFV_of_ci_projection`.

    Coverage: FULLY PROVED via
    `ciProjectAtClauseIndex_source_of_liftFormulaSkolem_hornClauses`
    (navigate ci's `.conj` tree to the i-th subtree whose source is
    the lifted `universalClosure` of D[i]) +
    `liftFormulaSkolem_foldr_all` (lift commutes with `foldr .all`) +
    `ciExtractSubstFromForallChain_covers_foldrAll` (under WellFormed
    + Nodup, chain keys cover every outer `.all` variable), tied
    together by `SK_eq_liftFormulaSkolem_of_no_ex` (Horn source ⇒
    `SK spec = liftFormulaSkolem spec.source`) and
    `hornClauseVarsList_covers_clause` (every clause FV is in the
    list). The `hornClauseVarsList_nodup` invariant is load-bearing:
    `formulaSubstN` only commutes with `foldr .all` when the
    substituted variable is distinct from all inner `.all` binders.

    `Sum.inr`-freeness of witnesses: FULLY PROVED via the computed
    `SkolemSpec.allocations` framework. `hAfalsumAtomic` + `hSpec`
    derive `spec.n = 0` through
    `spec_n_eq_zero_of_hornClauses_source`; then
    `termNoSumInr_of_n_eq_zero` gives `termNoSumInr t` for every term
    in the Skolem-extended language. -/
theorem ciExtractSubstFromForallChain_covers_clauseFV_with_noSumInr
    {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (hAfalsumAtomic : FormulaN.isAtomic Afalsum = true)
    (D goals : List (FOHornClause L hNoEq))
    (hAllNe : D ++ goals ≠ [])
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (hSpec : spec.source = (hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals))
    (ci : LCS.Herbrand.SHGTheorem.CInstance spec.language)
    (hCiSrc : ci.source = LCS.Herbrand.SHGTheorem.SK spec)
    (hCiWF : LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci)
    (i : Nat) (hiLt : i < D.length)
    (ciClause : LCS.Herbrand.SHGTheorem.CInstance spec.language)
    (hCiClauseOpt : ciProjectAtClauseIndex
      (n := spec.n) (skolemRank := spec.skolemRank) ci i
      ((D ++ goals).length) = some ciClause) :
    (∀ p, p ∈ ciExtractSubstFromForallChain
        (n := spec.n) (skolemRank := spec.skolemRank) ciClause →
      termNoSumInr p.2) ∧
    (∀ x, (clauseFV (hNoEq := by all_goals exact hNoEq)) (D[i].toFOClause (hNoEq := by all_goals exact hNoEq)) x →
      ∃ t, (x, t) ∈ ciExtractSubstFromForallChain
        (n := spec.n) (skolemRank := spec.skolemRank) ciClause) := by
-- BEGIN PROOF
  have hSpecN : spec.n = 0 :=
    (spec_n_eq_zero_of_hornClauses_source (hNoEq := by all_goals exact hNoEq)) Afalsum hAfalsumAtomic
      (D ++ goals) spec hSpec
  refine ⟨?_, ?_⟩
  · -- Sum.inr-freeness: spec.n = 0 + termNoSumInr_of_n_eq_zero.
    intro p _
    exact termNoSumInr_of_n_eq_zero hSpecN p.2
  · -- Coverage: chain keys cover FV(D[i]). Under `spec.n = 0`,
    -- `SK spec = liftFormulaSkolem spec.source`, so ci's source is the
    -- lifted Horn encoding. Navigate ci's conjunction tree to the i-th
    -- subtree whose source is the lifted universal closure of D[i];
    -- this is a `foldr .all` over `hornClauseVarsList Afalsum D[i]`
    -- (which is Nodup and covers FV(D[i])). The chain-coverage helper
    -- gives one chain entry per list member, so every `x ∈ FV(D[i])`
    -- is among the chain keys.
    intro x hxFV
    -- Turn ci.source into lifted form via SK_eq_liftFormulaSkolem_of_no_ex.
    have hNoEx : formulaHasNoEx spec.source := by
      rw [hSpec]
      exact (hornClauses_to_formulaN_hasNoEx (hNoEq := by all_goals exact hNoEq)) Afalsum hAfalsumAtomic
        (D ++ goals)
    have hSKeq : LCS.Herbrand.SHGTheorem.SK spec =
        LCS.Herbrand.SHGTheorem.liftFormulaSkolem
          (n := spec.n) (skolemRank := spec.skolemRank) spec.source :=
      SK_eq_liftFormulaSkolem_of_no_ex spec hNoEx
    have hCiSrc' : ci.source = LCS.Herbrand.SHGTheorem.liftFormulaSkolem
        (n := spec.n) (skolemRank := spec.skolemRank)
        ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals)) := by
      rw [hCiSrc, hSKeq, hSpec]
    -- i < (D ++ goals).length
    have hDlen_le : D.length ≤ ((D ++ goals).length) := by
      rw [List.length_append]; exact Nat.le_add_right _ _
    have hi_lt_total : i < ((D ++ goals).length) :=
      Nat.lt_of_lt_of_le hiLt hDlen_le
    -- Compute source of ciClause via navigation helper.
    obtain ⟨hClauseSrc, hClauseWf⟩ :=
      (ciProjectAtClauseIndex_source_of_liftFormulaSkolem_hornClauses (hNoEq := by all_goals exact hNoEq))
        (D ++ goals) Afalsum i hi_lt_total ci hCiWF hCiSrc' ciClause
        hCiClauseOpt
    -- (D ++ goals).get ⟨i, hi_lt_total⟩ = D[i] since i < D.length.
    have hGetEq : (D ++ goals).get ⟨i, hi_lt_total⟩ = D[i] := by
      show (D ++ goals)[i]'hi_lt_total = D[i]'hiLt
      exact List.getElem_append_left hiLt
    rw [hGetEq] at hClauseSrc
    -- Now ciClause.source = liftFormulaSkolem (fvs.foldr .all body)
    -- where fvs = hornClauseVarsList Afalsum D[i],
    -- body = clauseToFormula Afalsum D[i].toFOClause.
    have hNodup : ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum D[i]).Nodup :=
      (hornClauseVarsList_nodup (hNoEq := by all_goals exact hNoEq)) Afalsum D[i]
    -- Unfold universalClosure to foldr form.
    have hSrcFoldr : ciClause.source = ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum D[i]).foldr
        (fun v acc => FormulaN.all v acc)
        (LCS.Herbrand.SHGTheorem.liftFormulaSkolem
          (n := spec.n) (skolemRank := spec.skolemRank)
          ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) Afalsum (D[i].toFOClause (hNoEq := by all_goals exact hNoEq)))) := by
      erw [hClauseSrc]
      exact liftFormulaSkolem_foldr_all (n := spec.n) (skolemRank := spec.skolemRank) _ _
    -- Derive x ∈ hornClauseVarsList Afalsum D[i] from clauseFV D[i].toFOClause x.
    have hx_in_fvs : x ∈ (hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum D[i] := by
      apply (hornClauseVarsList_covers_clause (hNoEq := by all_goals exact hNoEq)) Afalsum D[i]
      -- clauseFV D[i].toFOClause x → FOClause.freeVars D[i].toFOClause x.
      -- clauseFV uses FOLiteral.vars (= formulaVars (FOLiteralCore.formula lit)),
      -- freeVars uses formulaFVN (FOLiteralCore.formula lit). Equal for atomic literals.
      obtain ⟨lit, hlit_mem, hlit_vars⟩ := hxFV
      have hLitAtomic := (toFOClause_literal_atomic (hNoEq := by all_goals exact hNoEq)) D[i] lit hlit_mem
      refine ⟨lit, hlit_mem, ?_⟩
      show LCS.FirstOrder.SyntaxN.Variables.formulaFVN (FOLiteralCore.formula lit) x
      -- hlit_vars : FOLiteral.vars lit x, which reduces to
      -- formulaVars (FOLiteralCore.formula lit) x. Unfold to formulaVars, then atomic
      -- case analysis since formulaVars / formulaFVN coincide on
      -- quantifier-free terms (termVars = termFV).
      have hlit_fv : formulaVars (FOLiteralCore.formula lit) x := by
        rw [← FOLiteralCore.vars_eq_formulaVars]
        exact hlit_vars
      -- Case split on (FOLiteralCore.formula lit). Non-atomic cases contradict hLitAtomic.
      cases hLF : (FOLiteralCore.formula lit) with
      | predN P ts =>
        rw [hLF] at hlit_fv
        simp only [LCS.FirstOrder.SyntaxN.Variables.formulaFVN, Set.iUnion,
          formulaVars] at hlit_fv ⊢
        obtain ⟨j, hj⟩ := hlit_fv
        exact ⟨j, (termFV_iff_termVars_local (ts j) x).mpr hj⟩
      | eq_ hL t1 t2 =>
        rw [hLF] at hlit_fv
        simp only [LCS.FirstOrder.SyntaxN.Variables.formulaFVN, Set.union,
          formulaVars] at hlit_fv ⊢
        rcases hlit_fv with h | h
        · exact Or.inl ((termFV_iff_termVars_local t1 x).mpr h)
        · exact Or.inr ((termFV_iff_termVars_local t2 x).mpr h)
      | neg _ =>
        exfalso; rw [hLF] at hLitAtomic; simp [FormulaN.isAtomic] at hLitAtomic
      | conj _ _ =>
        exfalso; rw [hLF] at hLitAtomic; simp [FormulaN.isAtomic] at hLitAtomic
      | disj _ _ =>
        exfalso; rw [hLF] at hLitAtomic; simp [FormulaN.isAtomic] at hLitAtomic
      | impl _ _ =>
        exfalso; rw [hLF] at hLitAtomic; simp [FormulaN.isAtomic] at hLitAtomic
      | all _ _ =>
        exfalso; rw [hLF] at hLitAtomic; simp [FormulaN.isAtomic] at hLitAtomic
      | ex _ _ =>
        exfalso; rw [hLF] at hLitAtomic; simp [FormulaN.isAtomic] at hLitAtomic
    -- Apply coverage helper.
    exact ciExtractSubstFromForallChain_covers_foldrAll
      ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum D[i]) hNodup
      (LCS.Herbrand.SHGTheorem.liftFormulaSkolem
        (n := spec.n) (skolemRank := spec.skolemRank)
        ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) Afalsum (D[i].toFOClause (hNoEq := by all_goals exact hNoEq))))
      ciClause hClauseWf hSrcFoldr x hx_in_fvs

/-- Theorem 9.4.1 (required helper): The σ built from ciClause's forallInst
    chain is ground on the free variables of `D[i]`.

    CONTENT. `σ := substFromList (ciExtractSubstFromForallChain ciClause)`
    maps each entry-variable to `demoteTerm t` where `t` is the
    corresponding forallInst-witness term. Under the Horn hypotheses,
    the chain has one entry for every free variable of `D[i]` (so no
    variable of `D[i]` falls into `substFromList`'s `.var x` fallback
    branch), and every chain-witness term is closed and `Sum.inr`-free
    (so `demoteTerm t` recovers a closed base-language term).

    PROOF STATUS. FULLY PROVED. Body delegated to three helpers:
    `ciExtractSubstFromForallChain_covers_clauseFV_with_noSumInr` (chain
    coverage + `Sum.inr`-free witnesses, fully proved via
    `ciProjectAtClauseIndex_source_of_liftFormulaSkolem_hornClauses` +
    `ciExtractSubstFromForallChain_covers_foldrAll`),
    `demoteTermOpt_some_ground_of_noSumInr_closed` (demotion succeeds
    on closed + `Sum.inr`-free terms), and
    `ciExtractSubstFromForallChain_entries_closed` (witnesses are
    closed). No residual sorry. -/
theorem substFromList_ground_on_clauseFV_of_ci_projection {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (hAfalsumAtomic : FormulaN.isAtomic Afalsum = true)
    (D goals : List (FOHornClause L hNoEq))
    (hAllNe : D ++ goals ≠ [])
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (hSpec : spec.source = (hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals))
    (ci : LCS.Herbrand.SHGTheorem.CInstance spec.language)
    (hCiSrc : ci.source = LCS.Herbrand.SHGTheorem.SK spec)
    (hCiWF : LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci)
    (i : Nat) (hiLt : i < D.length)
    (ciClause : LCS.Herbrand.SHGTheorem.CInstance spec.language)
    (hCiClauseOpt : ciProjectAtClauseIndex
      (n := spec.n) (skolemRank := spec.skolemRank) ci i
      ((D ++ goals).length) = some ciClause) :
    ∀ x, (clauseFV (hNoEq := by all_goals exact hNoEq)) (D[i].toFOClause (hNoEq := by all_goals exact hNoEq)) x →
      ∀ y, ¬ termVars
        (substFromList
          (ciExtractSubstFromForallChain
            (n := spec.n) (skolemRank := spec.skolemRank) ciClause) x) y := by
-- BEGIN PROOF
  intro x hx y hy
  -- Combined coverage + Sum.inr-freeness from the narrow sub-sorry.
  obtain ⟨hAllNo, hCov⟩ :=
    (ciExtractSubstFromForallChain_covers_clauseFV_with_noSumInr (hNoEq := by all_goals exact hNoEq))
      Afalsum hAfalsumAtomic D goals hAllNe spec hSpec
      ci hCiSrc hCiWF i hiLt ciClause hCiClauseOpt
  -- Coverage: some chain entry has key x.
  obtain ⟨tWit, hWitMem⟩ := hCov x hx
  unfold substFromList at hy
  -- Case split: either find? returns some entry or none.
  cases hFind : (ciExtractSubstFromForallChain
    (n := spec.n) (skolemRank := spec.skolemRank) ciClause).find?
      (fun p => decide (p.1 = x)) with
  | none =>
    -- find? = none contradicts hWitMem (entry with key x exists).
    rw [List.find?_eq_none] at hFind
    exact absurd (decide_eq_true rfl) (hFind (x, tWit) hWitMem)
  | some entry =>
    rw [hFind] at hy
    have hEntryMem : entry ∈ ciExtractSubstFromForallChain
        (n := spec.n) (skolemRank := spec.skolemRank) ciClause :=
      List.mem_of_find?_eq_some hFind
    -- Entry's second component is Sum.inr-free and closed.
    have hEntryNo : termNoSumInr entry.2 := hAllNo entry hEntryMem
    have hEntryCl : LCS.FirstOrder.Basic.Term.isClosed entry.2 :=
      ciExtractSubstFromForallChain_entries_closed
        (n := spec.n) (skolemRank := spec.skolemRank) ciClause entry hEntryMem
    -- Demotion succeeds and produces a ground term.
    obtain ⟨t', hDem, hGnd⟩ :=
      demoteTermOpt_some_ground_of_noSumInr_closed
        (n := spec.n) (skolemRank := spec.skolemRank) entry.2 hEntryNo hEntryCl
    -- Reduce demoteTerm entry.2 via hDem.
    simp only [demoteTerm] at hy
    rw [hDem] at hy
    exact hGnd y hy

/-- Theorem 9.4.1 (required helper): Groundness of the per-clause ground
    instance built from a `CInstance` projection.

    CONTENT. For `i < D.length` with the i-th clause subtree `ciClause`
    obtained from `ciProjectAtClauseIndex ci i (D ++ goals).length = some
    ciClause`, the per-variable substitution
      `σ := substFromList (ciExtractSubstFromForallChain ciClause)`
    makes `substAllInHornClause D[i] σ` ground (no free variables in its
    literal translation).

    JUSTIFICATION. In the Horn setting `spec.n = 0` (forced by the
    caller at `foSLD_exists_refutation_from_unsat` via the
    `⟨…, 0, Fin.elim0, …⟩` spec construction), every closed
    `Term spec.language` is `Sum.inr`-free, so `demoteTerm` is total
    and recovers a closed `Term L`. Moreover, `ci.source = SK spec =
    liftFormulaSkolem spec.source` preserves the universal closures
    in `hornClauses_to_formulaN`, and `WellFormed ci` forces the
    i-th clause subtree `ciClause` to be a full `forallInst` chain
    of length equal to `(hornClauseVarsList Afalsum D[i]).length`
    (one witness per universally quantified free variable of D[i]).
    Therefore `ciExtractSubstFromForallChain ciClause` produces
    entries covering every `FV(D[i])`, and `substFromList` maps each
    such variable to a ground `Term L`.

    PROOF STATUS. The theorem is fully decomposed: the body now
    delegates the groundness-of-clause claim to
    `substAllInHornClause_ground_of_subst_ground_on_fv` (FULLY PROVED,
    ZERO SORRY) which reduces to "σ is ground on FV(D[i])". That
    narrower claim is encapsulated in the dedicated helper
    `substFromList_ground_on_clauseFV_of_ci_projection` which retains
    the single structural sub-sorry for the Cor 7.6.1 chain-coverage-
    plus-demotion invariant. -/
theorem groundness_of_substAllInHornClause_via_ci {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (hAfalsumAtomic : FormulaN.isAtomic Afalsum = true)
    (D goals : List (FOHornClause L hNoEq))
    (hAllNe : D ++ goals ≠ [])
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (hSpec : spec.source = (hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals))
    (ci : LCS.Herbrand.SHGTheorem.CInstance spec.language)
    (hCiSrc : ci.source = LCS.Herbrand.SHGTheorem.SK spec)
    (hCiWF : LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci)
    (i : Nat) (hiLt : i < D.length)
    (ciClause : LCS.Herbrand.SHGTheorem.CInstance spec.language)
    (hCiClauseOpt : ciProjectAtClauseIndex
      (n := spec.n) (skolemRank := spec.skolemRank) ci i
      ((D ++ goals).length) = some ciClause) :
    ∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq))
      (((substAllInHornClause (hNoEq := by all_goals exact hNoEq)) D[i]
        (substFromList
          (ciExtractSubstFromForallChain
            (n := spec.n) (skolemRank := spec.skolemRank) ciClause))).toFOClause (hNoEq := by all_goals exact hNoEq)) x := by
-- BEGIN PROOF
  exact (substAllInHornClause_ground_of_subst_ground_on_fv (hNoEq := by all_goals exact hNoEq)) D[i] _
    ((substFromList_ground_on_clauseFV_of_ci_projection (hNoEq := by all_goals exact hNoEq))
      Afalsum hAfalsumAtomic D goals hAllNe spec hSpec ci hCiSrc hCiWF
      i hiLt ciClause hCiClauseOpt)

-- Theorem 9.4.1 (required helper): Multi-path analogue of
-- `ciExtractSubstFromForallChain_entries_closed`. Every `(x, t)` entry
-- in every path from `ciExtractAllSubstPaths ci` has a closed witness
-- term `t` — inherited from `.forallInst`'s `hGround₀ / hGroundRest`
-- fields. Companion helper handles tsRest/hsRest traversal.
mutual
theorem ciExtractAllSubstPaths_entries_closed
    {L : Language}  {n : Nat} {skolemRank : Fin n → Nat} :
    ∀ (ci : LCS.Herbrand.SHGTheorem.CInstance
        (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank))
      (entries : List (Nat × Term
        (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank)))
      (_hEntries : entries ∈ ciExtractAllSubstPaths
        (n := n) (skolemRank := skolemRank) ci)
      (p : Nat × Term
        (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank))
      (_hp : p ∈ entries),
      LCS.FirstOrder.Basic.Term.isClosed p.2
  | .atom B hAtom, entries, hEntries, p, hp => by
    simp only [ciExtractAllSubstPaths, List.mem_singleton] at hEntries
    subst hEntries
    simp at hp
  | .negAtom B hAtom, entries, hEntries, p, hp => by
    simp only [ciExtractAllSubstPaths, List.mem_singleton] at hEntries
    subst hEntries
    simp at hp
  | .connective star C D H K, entries, hEntries, p, hp => by
    simp only [ciExtractAllSubstPaths, List.mem_singleton] at hEntries
    subst hEntries
    simp at hp
  | .forallInst x C t₀ h₀ tsRest hsRest hG₀ hGR, entries, hEntries, p, hp => by
    simp only [ciExtractAllSubstPaths, List.mem_append, List.mem_map] at hEntries
    rcases hEntries with ⟨path, hPathMem, hEntriesEq⟩ | hRestMem
    · -- Head branch: entries = (x, t₀) :: path, with path ∈ (ciExtractAllSubstPaths h₀).
      subst hEntriesEq
      cases hp with
      | head =>
        show LCS.FirstOrder.Basic.Term.isClosed (x, t₀).2
        exact hG₀
      | tail _ hp' =>
        exact ciExtractAllSubstPaths_entries_closed h₀ path hPathMem p hp'
    · -- Rest branch: entries ∈ ciExtractAllSubstPathsList x tsRest hsRest.
      exact ciExtractAllSubstPathsList_entries_closed x tsRest hsRest hGR
        entries hRestMem p hp

theorem ciExtractAllSubstPathsList_entries_closed
    {L : Language} {n : Nat} {skolemRank : Fin n → Nat}
    (x : Nat) :
    ∀ (ts : List (Term (LCS.Herbrand.SHGTheorem.SkolemLanguage
        (L := L) n skolemRank)))
      (hs : List (LCS.Herbrand.SHGTheorem.CInstance
        (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank)))
      (_hGR : ∀ t ∈ ts, LCS.FirstOrder.Basic.Term.isClosed t)
      (entries : List (Nat × Term
        (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank)))
      (_hEntries : entries ∈ ciExtractAllSubstPathsList
        (n := n) (skolemRank := skolemRank) x ts hs)
      (p : Nat × Term
        (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank))
      (_hp : p ∈ entries),
      LCS.FirstOrder.Basic.Term.isClosed p.2
  | [], _, _, entries, hEntries, p, hp => by
    simp [ciExtractAllSubstPathsList] at hEntries
  | _ :: _, [], _, entries, hEntries, p, hp => by
    simp [ciExtractAllSubstPathsList] at hEntries
  | t :: tsRest, h :: hsRest, hGR, entries, hEntries, p, hp => by
    simp only [ciExtractAllSubstPathsList, List.mem_append, List.mem_map]
      at hEntries
    rcases hEntries with ⟨path, hPathMem, hEntriesEq⟩ | hRestMem
    · -- Head branch: entries = (x, t) :: path, with path ∈ (ciExtractAllSubstPaths h).
      subst hEntriesEq
      cases hp with
      | head =>
        show LCS.FirstOrder.Basic.Term.isClosed (x, t).2
        exact hGR t List.mem_cons_self
      | tail _ hp' =>
        exact ciExtractAllSubstPaths_entries_closed h path hPathMem p hp'
    · -- Rest branch: entries ∈ ciExtractAllSubstPathsList x tsRest hsRest.
      have hGRRest : ∀ t' ∈ tsRest, LCS.FirstOrder.Basic.Term.isClosed t' :=
        fun t' ht' => hGR t' (List.mem_cons_of_mem _ ht')
      exact ciExtractAllSubstPathsList_entries_closed x tsRest hsRest hGRRest
        entries hRestMem p hp
end

-- Theorem 9.4.1 (required helper): Companion list traversal for
-- `ciExtractAllSubstPaths_covers_foldrAll`. Shows that every entries
-- in ciExtractAllSubstPathsList x tsRest hsRest covers v ∈ x :: vTl,
-- using the `ih` from the outer induction.
theorem ciExtractAllSubstPathsList_covers_foldrAll
    {L : Language} {n : Nat} {skolemRank : Fin n → Nat}
    (x : Nat) (vTl : List Nat) (_hNodup : (x :: vTl).Nodup)
    (body : FormulaN (LCS.Herbrand.SHGTheorem.SkolemLanguage
      (L := L) n skolemRank))
    (ih : vTl.Nodup →
      ∀ (body' : FormulaN (LCS.Herbrand.SHGTheorem.SkolemLanguage
          (L := L) n skolemRank))
        (ci' : LCS.Herbrand.SHGTheorem.CInstance
          (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank))
        (_hWF' : LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci')
        (_hSrc' : ci'.source = vTl.foldr (fun v acc => FormulaN.all v acc) body')
        (entries' : List (Nat × Term
          (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank)))
        (_hEntries' : entries' ∈ ciExtractAllSubstPaths
          (n := n) (skolemRank := skolemRank) ci')
        (v' : Nat) (_hv' : v' ∈ vTl),
        ∃ t' : Term (LCS.Herbrand.SHGTheorem.SkolemLanguage
            (L := L) n skolemRank),
          (v', t') ∈ entries') :
    ∀ (tsRest : List (Term (LCS.Herbrand.SHGTheorem.SkolemLanguage
        (L := L) n skolemRank)))
      (hsRest : List (LCS.Herbrand.SHGTheorem.CInstance
        (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank)))
      (_hList : LCS.Herbrand.SHGTheorem.CInstance.WellFormedList x
        (vTl.foldr (fun v acc => FormulaN.all v acc) body) tsRest hsRest)
      (entries : List (Nat × Term
        (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank)))
      (_hEntries : entries ∈ ciExtractAllSubstPathsList
        (n := n) (skolemRank := skolemRank) x tsRest hsRest)
      (v : Nat) (_hv : v ∈ x :: vTl),
      ∃ t : Term (LCS.Herbrand.SHGTheorem.SkolemLanguage
          (L := L) n skolemRank),
        (v, t) ∈ entries := by
-- BEGIN PROOF
  intro tsRest
  induction tsRest with
  | nil =>
    intros hsRest _ entries hEntries _ _
    cases hsRest with
    | nil => simp [ciExtractAllSubstPathsList] at hEntries
    | cons _ _ => simp [ciExtractAllSubstPathsList] at hEntries
  | cons t tsRest' ihList =>
    intros hsRest hList entries hEntries v hv
    cases hsRest with
    | nil => exact absurd hList id
    | cons h hsRest' =>
      obtain ⟨hhsrc, hhwf, hRestList⟩ := hList
      simp only [ciExtractAllSubstPathsList, List.mem_append, List.mem_map]
        at hEntries
      rcases hEntries with ⟨path, hPathMem, hEntriesEq⟩ | hRestMem
      · -- Head branch: entries = (x, t) :: path, path ∈ ciExtractAllSubstPaths h.
        subst hEntriesEq
        rcases List.mem_cons.mp hv with rfl | hvMem
        · -- v = x: entry is the head.
          exact ⟨t, List.mem_cons_self⟩
        · -- v ∈ vTl: inductive descent via `ih` on path into h.
          have hNodup_tl : vTl.Nodup := _hNodup.tail
          have hx_notin : x ∉ vTl := (List.nodup_cons.mp _hNodup).1
          have hhsrc' : h.source = vTl.foldr (fun v acc => FormulaN.all v acc)
              (LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN body t x) := by
            rw [hhsrc]
            exact formulaSubstN_foldr_all_commute vTl _ t x hx_notin
          obtain ⟨t', ht'⟩ := ih hNodup_tl
            (LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN body t x)
            h hhwf hhsrc' path hPathMem v hvMem
          exact ⟨t', List.mem_cons_of_mem _ ht'⟩
      · -- Rest branch: entries ∈ ciExtractAllSubstPathsList x tsRest' hsRest'.
        exact ihList hsRest' hRestList entries hRestMem v hv

-- Theorem 9.4.1 (required helper): Multi-path extension of
-- `ciExtractSubstFromForallChain_covers_foldrAll`. Under WellFormed ci
-- and a `foldr .all vs body` source with `vs.Nodup`, EVERY path in
-- `ciExtractAllSubstPaths ci` contains one entry for every `v ∈ vs`.
theorem ciExtractAllSubstPaths_covers_foldrAll
    {L : Language} {n : Nat} {skolemRank : Fin n → Nat} :
    ∀ (vs : List Nat) (_hNodup : vs.Nodup)
      (body : FormulaN (LCS.Herbrand.SHGTheorem.SkolemLanguage
        (L := L) n skolemRank))
      (ci : LCS.Herbrand.SHGTheorem.CInstance
        (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank))
      (_hWF : LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci)
      (_hSrc : ci.source = vs.foldr (fun v acc => FormulaN.all v acc) body)
      (entries : List (Nat × Term
        (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank)))
      (_hEntries : entries ∈ ciExtractAllSubstPaths
        (n := n) (skolemRank := skolemRank) ci)
      (v : Nat) (_hv : v ∈ vs),
      ∃ t : Term (LCS.Herbrand.SHGTheorem.SkolemLanguage
          (L := L) n skolemRank),
        (v, t) ∈ entries := by
-- BEGIN PROOF
  intro vs
  induction vs with
  | nil => intros _ _ _ _ _ _ _ _ hv; simp at hv
  | cons vHd vTl ih =>
    intros hNodup body ci hWF hSrc entries hEntries v hv
    simp only [List.foldr] at hSrc
    obtain ⟨t₀, h₀, tsRest, hsRest, hG₀, hGR, hCi, hh₀src, hh₀wf, hList⟩ :=
      ci_forallInst_of_source_all ci vHd
        (vTl.foldr (fun v acc => FormulaN.all v acc) body) hSrc hWF
    subst hCi
    -- entries ∈ ciExtractAllSubstPaths of .forallInst ...
    -- Either entries is from headPrepended or from restPaths.
    simp only [ciExtractAllSubstPaths, List.mem_append, List.mem_map]
      at hEntries
    rcases hEntries with ⟨path, hPathMem, hEntriesEq⟩ | hRestMem
    · -- Head branch: entries = (vHd, t₀) :: path.
      subst hEntriesEq
      rcases List.mem_cons.mp hv with rfl | hvMem
      · -- v = vHd: entry is the head.
        exact ⟨t₀, List.mem_cons_self⟩
      · -- v ∈ vTl: inductive descent on path into h₀.
        have hNodup_tl : vTl.Nodup := hNodup.tail
        have hHd_notin : vHd ∉ vTl := (List.nodup_cons.mp hNodup).1
        have hh₀src' : h₀.source = vTl.foldr (fun v acc => FormulaN.all v acc)
            (LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN body t₀ vHd) := by
          rw [hh₀src]
          exact formulaSubstN_foldr_all_commute vTl _ t₀ vHd hHd_notin
        obtain ⟨t, ht⟩ := ih hNodup_tl
          (LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN body t₀ vHd)
          h₀ hh₀wf hh₀src' path hPathMem v hvMem
        exact ⟨t, List.mem_cons_of_mem _ ht⟩
    · -- Rest branch: entries ∈ ciExtractAllSubstPathsList vHd tsRest hsRest.
      -- Delegate to the list helper with the outer IH.
      exact ciExtractAllSubstPathsList_covers_foldrAll vHd vTl hNodup body
        ih tsRest hsRest hList entries hRestMem v hv

/-- Theorem 9.4.1 (required helper): Multi-path extension of
    `substFromList_ground_on_clauseFV_of_ci_projection` — every path
    from `ciExtractAllSubstPaths ciClause` yields a substitution that
    is ground on `FV(D[i])`.

    CONTENT. Each path `entries ∈ ciExtractAllSubstPaths ciClause` is a
    COMPLETE witness-chain through SOME branch choice at each forallInst
    node (Def 7.6.3(iii) allows k ≥ 1 witnesses per node, and
    `ciExtractAllSubstPaths` enumerates every such branching choice).
    All paths have the same length = depth of the forallInst chain =
    `|FV(D[i])|`, and all paths contain a closed, `Sum.inr`-free term
    for every `x ∈ FV(D[i])` (the witness terms are structurally closed
    via `hGround₀ / hGroundRest` of `.forallInst`).

    PROOF STATUS. FULLY PROVED. Body delegates to
    `ciExtractAllSubstPaths_covers_foldrAll` (coverage), and the
    demotion infrastructure from the single-path version — every path's
    entries' witness term satisfies the same closed + no-Sum.inr
    invariant as the first-path version. -/
theorem multi_path_ground_on_clauseFV {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (hAfalsumAtomic : FormulaN.isAtomic Afalsum = true)
    (D goals : List (FOHornClause L hNoEq))
    (hAllNe : D ++ goals ≠ [])
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (hSpec : spec.source = (hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals))
    (ci : LCS.Herbrand.SHGTheorem.CInstance spec.language)
    (hCiSrc : ci.source = LCS.Herbrand.SHGTheorem.SK spec)
    (hCiWF : LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci)
    (i : Nat) (hiLt : i < D.length)
    (ciClause : LCS.Herbrand.SHGTheorem.CInstance spec.language)
    (hCiClauseOpt : ciProjectAtClauseIndex
      (n := spec.n) (skolemRank := spec.skolemRank) ci i
      ((D ++ goals).length) = some ciClause)
    (entries : List (Nat × Term
      (LCS.Herbrand.SHGTheorem.SkolemLanguage
        (L := L) spec.n spec.skolemRank)))
    (hEntriesMem : entries ∈ ciExtractAllSubstPaths
      (n := spec.n) (skolemRank := spec.skolemRank) ciClause) :
    ∀ x, (clauseFV (hNoEq := by all_goals exact hNoEq)) (D[i].toFOClause (hNoEq := by all_goals exact hNoEq)) x →
      ∀ y, ¬ termVars
        (substFromList (n := spec.n) (skolemRank := spec.skolemRank)
          entries x) y := by
-- BEGIN PROOF
  -- Structural groundness mirrors the single-path version: every entry's
  -- term is closed + Sum.inr-free, and every FV(D[i]) is covered by the
  -- path. Delegate to the new multi-path coverage + closedness helpers.
  have hSpecN : spec.n = 0 :=
    (spec_n_eq_zero_of_hornClauses_source (hNoEq := by all_goals exact hNoEq)) Afalsum hAfalsumAtomic
      (D ++ goals) spec hSpec
  -- Closedness of entries: reuse the mutual helper.
  have hEntriesClosed : ∀ p ∈ entries,
      LCS.FirstOrder.Basic.Term.isClosed p.2 := by
    intro p hp
    exact ciExtractAllSubstPaths_entries_closed (n := spec.n) (skolemRank := spec.skolemRank) ciClause entries
      hEntriesMem p hp
  -- Sum.inr-freeness: spec.n = 0 forces termNoSumInr on every term.
  have hEntriesNo : ∀ p ∈ entries, termNoSumInr p.2 := by
    intro p _
    exact termNoSumInr_of_n_eq_zero hSpecN p.2
  -- Coverage: every x ∈ FV(D[i]) appears as key in entries. This requires
  -- ciClause.source = foldr .all vs body shape + Nodup, derived from
  -- ciProjectAtClauseIndex's navigation through SK spec's conj-chain.
  have hNoEx : formulaHasNoEx spec.source := by
    rw [hSpec]
    exact (hornClauses_to_formulaN_hasNoEx (hNoEq := by all_goals exact hNoEq)) Afalsum hAfalsumAtomic
      (D ++ goals)
  have hSKeq : LCS.Herbrand.SHGTheorem.SK spec =
      LCS.Herbrand.SHGTheorem.liftFormulaSkolem
        (n := spec.n) (skolemRank := spec.skolemRank) spec.source :=
    SK_eq_liftFormulaSkolem_of_no_ex spec hNoEx
  have hCiSrc' : ci.source = LCS.Herbrand.SHGTheorem.liftFormulaSkolem
      (n := spec.n) (skolemRank := spec.skolemRank)
      ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals)) := by
    rw [hCiSrc, hSKeq, hSpec]
  have hDlen_le : D.length ≤ ((D ++ goals).length) := by
    rw [List.length_append]; exact Nat.le_add_right _ _
  have hi_lt_total : i < ((D ++ goals).length) :=
    Nat.lt_of_lt_of_le hiLt hDlen_le
  obtain ⟨hClauseSrc, hClauseWf⟩ :=
    (ciProjectAtClauseIndex_source_of_liftFormulaSkolem_hornClauses (hNoEq := by all_goals exact hNoEq))
      (D ++ goals) Afalsum i hi_lt_total ci hCiWF hCiSrc' ciClause
      hCiClauseOpt
  have hGetEq : (D ++ goals).get ⟨i, hi_lt_total⟩ = D[i] := by
    show (D ++ goals)[i]'hi_lt_total = D[i]'hiLt
    exact List.getElem_append_left hiLt
  rw [hGetEq] at hClauseSrc
  have hNodup : ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum D[i]).Nodup :=
    (hornClauseVarsList_nodup (hNoEq := by all_goals exact hNoEq)) Afalsum D[i]
  have hSrcFoldr : ciClause.source = ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum D[i]).foldr
      (fun v acc => FormulaN.all v acc)
      (LCS.Herbrand.SHGTheorem.liftFormulaSkolem
        (n := spec.n) (skolemRank := spec.skolemRank)
        ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) Afalsum (D[i].toFOClause (hNoEq := by all_goals exact hNoEq)))) := by
    erw [hClauseSrc]
    exact liftFormulaSkolem_foldr_all (n := spec.n) (skolemRank := spec.skolemRank) _ _
  -- Now do the groundness argument per variable.
  intro x hxFV y hy
  -- Derive x ∈ hornClauseVarsList Afalsum D[i] from clauseFV D[i].toFOClause x.
  have hx_in_fvs : x ∈ (hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum D[i] := by
    apply (hornClauseVarsList_covers_clause (hNoEq := by all_goals exact hNoEq)) Afalsum D[i]
    obtain ⟨lit, hlit_mem, hlit_vars⟩ := hxFV
    have hLitAtomic := (toFOClause_literal_atomic (hNoEq := by all_goals exact hNoEq)) D[i] lit hlit_mem
    refine ⟨lit, hlit_mem, ?_⟩
    show LCS.FirstOrder.SyntaxN.Variables.formulaFVN (FOLiteralCore.formula lit) x
    have hlit_fv : formulaVars (FOLiteralCore.formula lit) x := by
      rw [← FOLiteralCore.vars_eq_formulaVars]
      exact hlit_vars
    cases hLF : (FOLiteralCore.formula lit) with
    | predN P ts =>
      rw [hLF] at hlit_fv
      simp only [LCS.FirstOrder.SyntaxN.Variables.formulaFVN, Set.iUnion,
        formulaVars] at hlit_fv ⊢
      obtain ⟨j, hj⟩ := hlit_fv
      exact ⟨j, (termFV_iff_termVars_local (ts j) x).mpr hj⟩
    | eq_ hL t1 t2 =>
      rw [hLF] at hlit_fv
      simp only [LCS.FirstOrder.SyntaxN.Variables.formulaFVN, Set.union,
        formulaVars] at hlit_fv ⊢
      rcases hlit_fv with h | h
      · exact Or.inl ((termFV_iff_termVars_local t1 x).mpr h)
      · exact Or.inr ((termFV_iff_termVars_local t2 x).mpr h)
    | neg _ =>
      exfalso; rw [hLF] at hLitAtomic; simp [FormulaN.isAtomic] at hLitAtomic
    | conj _ _ =>
      exfalso; rw [hLF] at hLitAtomic; simp [FormulaN.isAtomic] at hLitAtomic
    | disj _ _ =>
      exfalso; rw [hLF] at hLitAtomic; simp [FormulaN.isAtomic] at hLitAtomic
    | impl _ _ =>
      exfalso; rw [hLF] at hLitAtomic; simp [FormulaN.isAtomic] at hLitAtomic
    | all _ _ =>
      exfalso; rw [hLF] at hLitAtomic; simp [FormulaN.isAtomic] at hLitAtomic
    | ex _ _ =>
      exfalso; rw [hLF] at hLitAtomic; simp [FormulaN.isAtomic] at hLitAtomic
  -- Coverage via multi-path helper.
  obtain ⟨tWit, hWitMem⟩ :=
    ciExtractAllSubstPaths_covers_foldrAll
      (n := spec.n) (skolemRank := spec.skolemRank)
      ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum D[i]) hNodup
      (LCS.Herbrand.SHGTheorem.liftFormulaSkolem
        (n := spec.n) (skolemRank := spec.skolemRank)
        ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) Afalsum (D[i].toFOClause (hNoEq := by all_goals exact hNoEq))))
      ciClause hClauseWf hSrcFoldr entries hEntriesMem x hx_in_fvs
  -- Now replicate the single-path groundness argument with `entries`.
  unfold substFromList at hy
  cases hFind : entries.find? (fun p => decide (p.1 = x)) with
  | none =>
    rw [List.find?_eq_none] at hFind
    exact absurd (decide_eq_true rfl) (hFind (x, tWit) hWitMem)
  | some entry =>
    rw [hFind] at hy
    have hEntryMem : entry ∈ entries := List.mem_of_find?_eq_some hFind
    have hEntryNo : termNoSumInr entry.2 := hEntriesNo entry hEntryMem
    have hEntryCl : LCS.FirstOrder.Basic.Term.isClosed entry.2 :=
      hEntriesClosed entry hEntryMem
    obtain ⟨t', hDem, hGnd⟩ :=
      demoteTermOpt_some_ground_of_noSumInr_closed
        (n := spec.n) (skolemRank := spec.skolemRank) entry.2 hEntryNo hEntryCl
    simp only [demoteTerm] at hy
    rw [hDem] at hy
    exact hGnd y hy

/-- Theorem 9.4.1 (required helper): Predicate capturing "F is the root of a
    right-associated `.conj`-chain with at least `N` levels" — i.e. `F =
    A₁ ∧ (A₂ ∧ (... ∧ B))` where the tail below the first `N-1` conjuncts
    can be anything. For `N ≤ 1`, the predicate is vacuously true (a single
    formula counts as a 1-chain). For `N ≥ 2`, `F = .conj A B` with `B` a
    chain of length `N-1`.

    This predicate abstracts the shape invariant needed by
    `ciProjectAtClauseIndex_some_of_wellformed_horn`: every time
    `ciProjectAtClauseIndex` recurses, it consumes one `.conj` layer. -/
def isConjChainN {L : Language} : FormulaN L → Nat → Prop
  | _F, 0 => True
  | _F, 1 => True
  | F, Nat.succ (Nat.succ m) =>
    ∃ (A B : FormulaN L), F = FormulaN.conj A B ∧ isConjChainN B (Nat.succ m)

/-- Theorem 9.4.1 (required helper): `hornClauses_to_formulaN Afalsum list`
    is a conj-chain of length `list.length`. When `list = c :: rest` with
    `rest.length ≥ 1`, the encoding left-associates with `.conj (univClos c)
    (hornClauses_to_formulaN Afalsum rest)`, so the chain advances by one
    level per recursion. -/
theorem hornClauses_to_formulaN_isConjChainN {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) :
    ∀ (list : List (FOHornClause L hNoEq)),
      isConjChainN ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum list) list.length := by
-- BEGIN PROOF
  intro list
  induction list with
  | nil => trivial
  | cons c1 rest ih =>
    cases rest with
    | nil => trivial
    | cons c2 rest' =>
      show isConjChainN ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (c1 :: c2 :: rest'))
        ((rest'.length) + 2)
      simp only [isConjChainN]
      refine ⟨_, _, rfl, ?_⟩
      have ih' := ih
      simp [List.length] at ih'
      exact ih'

/-- Theorem 9.4.1 (required helper): `liftFormulaSkolem` preserves
    `isConjChainN` — it maps `.conj A B` to `.conj (lift A) (lift B)`
    homomorphically, so the conj-chain structure is maintained at every
    level. -/
theorem liftFormulaSkolem_isConjChainN {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat}
    (F : FormulaN L) (N : Nat) (hChain : isConjChainN F N) :
    isConjChainN
      (LCS.Herbrand.SHGTheorem.liftFormulaSkolem (n := n) (skolemRank := skolemRank) F) N := by
-- BEGIN PROOF
  induction N generalizing F with
  | zero => trivial
  | succ N' ihN =>
    cases N' with
    | zero => trivial
    | succ m =>
      simp only [isConjChainN] at hChain
      obtain ⟨A, B, hEq, hChainB⟩ := hChain
      subst hEq
      show isConjChainN
        (FormulaN.conj
          (LCS.Herbrand.SHGTheorem.liftFormulaSkolem A)
          (LCS.Herbrand.SHGTheorem.liftFormulaSkolem B)) (m + 2)
      simp only [isConjChainN]
      exact ⟨_, _, rfl, ihN B hChainB⟩

end LCS.SLD.FirstOrder
end

