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
import LCS.SLD.FirstOrder.GroundInstances
import Attach
import LCS.SLD.FirstOrder.GroundSemantics.ProofsStamp

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



-- retained: used by LCS.SLD.FirstOrder.PropositionalEncoding
/-- Theorem 9.4.1 (required helper): a successful exact Skolem traversal
    preserves the right-associated conjunction-chain shape of its source. -/
theorem skolemFormExactAux_isConjChainN_preservation {L : Language}
    (S : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    {F G : FormulaN S.language} {N : Nat} {scope : List Nat}
    {indices : List (Fin S.n)} {used : Nat}
    (hRun : LCS.Herbrand.SHGTheorem.skolemFormExactAux S F scope indices =
      some (G, used))
    (hChain : isConjChainN F N) :
    isConjChainN G N := by
-- BEGIN PROOF
  induction N generalizing F G scope indices used with
  | zero => trivial
  | succ N ih =>
    cases N with
    | zero => trivial
    | succ m =>
      simp only [isConjChainN] at hChain
      obtain ⟨A, B, rfl, hChainB⟩ := hChain
      cases hA :
        LCS.Herbrand.SHGTheorem.skolemFormExactAux S A scope
          (indices.take
            (LCS.Herbrand.SHGTheorem.skolemDescriptorCount A)) with
      | none =>
        simp [LCS.Herbrand.SHGTheorem.skolemFormExactAux.eq_7, hA] at hRun
      | some resultA =>
        obtain ⟨outA, usedA⟩ := resultA
        cases hB :
          LCS.Herbrand.SHGTheorem.skolemFormExactAux S B scope
            (indices.drop
              (LCS.Herbrand.SHGTheorem.skolemDescriptorCount A)) with
          | none =>
            simp [LCS.Herbrand.SHGTheorem.skolemFormExactAux.eq_7,
              hA, hB] at hRun
          | some resultB =>
            obtain ⟨outB, usedB⟩ := resultB
            simp [LCS.Herbrand.SHGTheorem.skolemFormExactAux.eq_7,
              hA, hB] at hRun
            rcases hRun with ⟨rfl, rfl⟩
            simp only [isConjChainN]
            exact ⟨outA, outB, rfl, ih hB hChainB⟩

-- retained: used by LCS.SLD.FirstOrder.PropositionalEncoding
/-- Theorem 9.4.1 (required helper): `SK spec` inherits the conj-chain
    structure of `spec.source` — combining `liftFormulaSkolem` and the
    successful exact traversal. When `spec.source =
    hornClauses_to_formulaN Afalsum list`, `SK spec` is a conj-chain of
    length `list.length`. -/
theorem SK_isConjChainN_from_source {L : Language} (hNoEq : L.withoutEquality)
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (list : List (FOHornClause L hNoEq))
    (Afalsum : FormulaN L)
    (hSpec : spec.source = (hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum list) :
    isConjChainN (LCS.Herbrand.SHGTheorem.SK spec) list.length := by
-- BEGIN PROOF
  have hSourceChain : isConjChainN spec.source list.length := by
    rw [hSpec]
    exact (hornClauses_to_formulaN_isConjChainN (hNoEq := by all_goals exact hNoEq)) Afalsum list
  have hLiftChain :
      isConjChainN
        (LCS.Herbrand.SHGTheorem.liftFormulaSkolem
          (skolemRank := spec.skolemRank) spec.source)
        list.length :=
    liftFormulaSkolem_isConjChainN spec.source list.length hSourceChain
  exact skolemFormExactAux_isConjChainN_preservation spec
    (LCS.Herbrand.SHGTheorem.skolemFormExactAux_top_formula_result spec)
    hLiftChain





/-- Theorem 9.4.1 (required helper): Extract ground Horn-clause instances
    of the `D` program from a compound-instance derivation tree `ci`.

    CONTENT. Given a `SkolemSpec` for `hornClauses_to_formulaN Afalsum (D ++ goals)`
    and a WellFormed `CInstance` tree `ci` for its Skolem form (source = `SK spec`),
    Def 7.6.3 guarantees that `ci`'s leaves arise from instantiating the universal
    quantifiers in each conjunct of the Horn encoding with closed terms. Projecting
    to the `D` side gives a list `D_g` of ground Horn clauses, each of the form
    `substAllInHornClause c σ` for some `c ∈ D` and closed-term substitution `σ`.

    CONSTRUCTION. `D_g` is bound to the explicit output of
    `extractGroundClausesFromCInstance_core`: for each `i`-th clause `c ∈ D`,
    project ci to the i-th clause subtree (navigating ci's top-level
    conjunction tree paralleling `hornClauses_to_formulaN`'s decomposition),
    walk the forallInst witness chain on that subtree to collect
    `(xⱼ, tⱼ)` pairs (one per universal quantifier in c's universal closure),
    and build `σᵢ` by demoting each `tⱼ` through the `Sum.inl` embedding
    back into `L`. The D_g equation closes L1/L4 loopholes — vacuous
    `D_g := []` would violate the explicit-construction equation.

    HORN-SETTING TOTALITY. Horn clauses contain no existential
    quantifiers, so for any `SkolemSpec` for a Horn encoding we have
    `spec.n = 0`. Under this assumption, `Sum.inr : Fin 0 → _` is
    uninhabited, and every `.func` node in a closed `Term spec.language`
    (originating from ci's forallInst witnesses) uses `Sum.inl f_L` for
    some `f_L : L.funSymbols`. Recursive `demoteTerm` therefore succeeds
    (is total) and faithfully recovers a base-language term. -/
@[attach_debt, blueprint "chap9__theorem_9_4_1"]
theorem extractGroundClauses_from_cinstance {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (hAfalsumAtomic : FormulaN.isAtomic Afalsum = true)
    (D goals : List (FOHornClause L hNoEq))
    (hAllNe : D ++ goals ≠ [])
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (hSpec : spec.source = (hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals))
    (ci : LCS.Herbrand.SHGTheorem.CInstance spec.language)
    (hCiSrc : ci.source = LCS.Herbrand.SHGTheorem.SK spec)
    (hCiWF : LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci) :
    ∃ (D_g : List (FOHornClause L hNoEq)),
      D_g = (extractGroundClausesFromCInstance_core (hNoEq := by all_goals exact hNoEq)) Afalsum D goals spec ci ∧
      (∀ c_g ∈ D_g, ∃ (c : FOHornClause L hNoEq) (_hMem : c ∈ D) (σ : Nat → Term L),
        c_g = (substAllInHornClause (hNoEq := by all_goals exact hNoEq)) c σ ∧
        (∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (c_g.toFOClause (hNoEq := by all_goals exact hNoEq)) x)) 

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 9.4.1 (required helper): Goals-side analogue of
    `multi_path_ground_on_clauseFV`. For a goals-index `i < goals.length`,
    the witness path through the goals-side subtree (at absolute index
    `D.length + i` in `D ++ goals`) covers every free variable of
    `goals[i]`, with closed Sum.inr-free term values; hence
    `substFromList entries` is ground on `clauseFV goals[i].toFOClause`. -/
theorem multi_path_ground_on_clauseFV_goals {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (hAfalsumAtomic : FormulaN.isAtomic Afalsum = true)
    (D goals : List (FOHornClause L hNoEq))
    (hAllNe : D ++ goals ≠ [])
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (hSpec : spec.source = (hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals))
    (ci : LCS.Herbrand.SHGTheorem.CInstance spec.language)
    (hCiSrc : ci.source = LCS.Herbrand.SHGTheorem.SK spec)
    (hCiWF : LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci)
    (i : Nat) (hiLt : i < goals.length)
    (ciClause : LCS.Herbrand.SHGTheorem.CInstance spec.language)
    (hCiClauseOpt : ciProjectAtClauseIndex
      (n := spec.n) (skolemRank := spec.skolemRank) ci (D.length + i)
      ((D ++ goals).length) = some ciClause)
    (entries : List (Nat × Term
      (LCS.Herbrand.SHGTheorem.SkolemLanguage
        (L := L) spec.n spec.skolemRank)))
    (hEntriesMem : entries ∈ ciExtractAllSubstPaths
      (n := spec.n) (skolemRank := spec.skolemRank) ciClause) :
    ∀ x, (clauseFV (hNoEq := by all_goals exact hNoEq)) (goals[i].toFOClause (hNoEq := by all_goals exact hNoEq)) x →
      ∀ y, ¬ termVars
        (substFromList (n := spec.n) (skolemRank := spec.skolemRank)
          entries x) y := by
-- BEGIN PROOF
  -- Mirror multi_path_ground_on_clauseFV (D-side proof) with `goals[i]`
  -- in place of `D[i]` and absolute index `D.length + i`.
  have hSpecN : spec.n = 0 :=
    (spec_n_eq_zero_of_hornClauses_source (hNoEq := by all_goals exact hNoEq)) Afalsum hAfalsumAtomic
      (D ++ goals) spec hSpec
  have hEntriesClosed : ∀ p ∈ entries,
      LCS.FirstOrder.Basic.Term.isClosed p.2 := by
    intro p hp
    exact ciExtractAllSubstPaths_entries_closed (n := spec.n) (skolemRank := spec.skolemRank) ciClause entries
      hEntriesMem p hp
  have hEntriesNo : ∀ p ∈ entries, termNoSumInr p.2 := by
    intro p _
    exact termNoSumInr_of_n_eq_zero hSpecN p.2
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
  have hAbs_lt_total : D.length + i < ((D ++ goals).length) := by
    rw [List.length_append]; omega
  obtain ⟨hClauseSrc, hClauseWf⟩ :=
    (ciProjectAtClauseIndex_source_of_liftFormulaSkolem_hornClauses (hNoEq := by all_goals exact hNoEq))
      (D ++ goals) Afalsum (D.length + i) hAbs_lt_total ci hCiWF hCiSrc'
      ciClause hCiClauseOpt
  have hGetEq : (D ++ goals).get ⟨D.length + i, hAbs_lt_total⟩ = goals[i] := by
    show (D ++ goals)[D.length + i]'hAbs_lt_total = goals[i]'hiLt
    have hRange : ¬ D.length + i < D.length := by omega
    rw [List.getElem_append]
    simp [hRange]
  rw [hGetEq] at hClauseSrc
  have hNodup : ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum goals[i]).Nodup :=
    (hornClauseVarsList_nodup (hNoEq := by all_goals exact hNoEq)) Afalsum goals[i]
  have hSrcFoldr : ciClause.source = ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum goals[i]).foldr
      (fun v acc => FormulaN.all v acc)
      (LCS.Herbrand.SHGTheorem.liftFormulaSkolem
        (n := spec.n) (skolemRank := spec.skolemRank)
        ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) Afalsum (goals[i].toFOClause (hNoEq := by all_goals exact hNoEq)))) := by
    erw [hClauseSrc]
    exact liftFormulaSkolem_foldr_all (n := spec.n) (skolemRank := spec.skolemRank) _ _
  intro x hxFV y hy
  have hx_in_fvs : x ∈ (hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum goals[i] := by
    apply (hornClauseVarsList_covers_clause (hNoEq := by all_goals exact hNoEq)) Afalsum goals[i]
    obtain ⟨lit, hlit_mem, hlit_vars⟩ := hxFV
    have hLitAtomic := (toFOClause_literal_atomic (hNoEq := by all_goals exact hNoEq)) goals[i] lit hlit_mem
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
  obtain ⟨tWit, hWitMem⟩ :=
    ciExtractAllSubstPaths_covers_foldrAll
      (n := spec.n) (skolemRank := spec.skolemRank)
      ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum goals[i]) hNodup
      (LCS.Herbrand.SHGTheorem.liftFormulaSkolem
        (n := spec.n) (skolemRank := spec.skolemRank)
        ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) Afalsum (goals[i].toFOClause (hNoEq := by all_goals exact hNoEq))))
      ciClause hClauseWf hSrcFoldr entries hEntriesMem x hx_in_fvs
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

/-- Theorem 9.4.1 (required helper): Goals-side analogue of
    `extractGroundClauses_from_cinstance`. Given a WellFormed CInstance `ci`
    for `SK spec`, produce the goals-side ground Horn-clause set `goals_g`
    along with multi-witness existential evidence: every entry `g_g ∈ goals_g`
    is `substAllInHornClause g τ` for some `g ∈ goals` with `g_g`-ground.

    CONSTRUCTION. `goals_g` is bound to the explicit output of
    `extractGroundGoalsFromCInstance_core`; the construction parallels the
    D-side wrapper but indexes into goals-side absolute positions
    `D.length + i` for `i < goals.length`. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem extractGroundGoals_from_cinstance {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (hAfalsumAtomic : FormulaN.isAtomic Afalsum = true)
    (D goals : List (FOHornClause L hNoEq))
    (hAllNe : D ++ goals ≠ [])
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (hSpec : spec.source = (hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals))
    (ci : LCS.Herbrand.SHGTheorem.CInstance spec.language)
    (hCiSrc : ci.source = LCS.Herbrand.SHGTheorem.SK spec)
    (hCiWF : LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci) :
    ∃ (goals_g : List (FOHornClause L hNoEq)),
      goals_g = (extractGroundGoalsFromCInstance_core (hNoEq := by all_goals exact hNoEq)) Afalsum D goals spec ci ∧
      (∀ g_g ∈ goals_g, ∃ (g : FOHornClause L hNoEq) (_hMem : g ∈ goals) (τ : Nat → Term L),
        g_g = (substAllInHornClause (hNoEq := by all_goals exact hNoEq)) g τ ∧
        (∀ x, ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (g_g.toFOClause (hNoEq := by all_goals exact hNoEq)) x)) 

-- retained: used by LCS.SLD.FirstOrder.PropositionalEncoding
/-- Theorem 9.4.1 (required helper): `ciExtractAllSubstPaths` is always
    non-empty — at any node, it returns at least one path (the empty
    path `[]` for non-forallInst nodes; for `forallInst`, the head branch
    inductively prepends `(x, t₀)` to non-empty `ciExtractAllSubstPaths
    h₀`, giving at least one path). Companion helper for the list
    traversal isn't needed here — we only need head-branch nonemptiness. -/
theorem ciExtractAllSubstPaths_ne_nil {L : Language} (hNoEq : L.withoutEquality)
    {n : Nat} {skolemRank : Fin n → Nat} :
    ∀ (ci : LCS.Herbrand.SHGTheorem.CInstance
        (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank)),
      ciExtractAllSubstPaths (n := n) (skolemRank := skolemRank) ci ≠ []
  | .atom _ _ => by simp [ciExtractAllSubstPaths]
  | .negAtom _ _ => by simp [ciExtractAllSubstPaths]
  | .connective _ _ _ _ _ => by simp [ciExtractAllSubstPaths]
  | .forallInst x C t₀ h₀ tsRest hsRest hG₀ hGR => by
    simp only [ciExtractAllSubstPaths]
    intro hEmpty
    rw [List.append_eq_nil_iff] at hEmpty
    obtain ⟨hHeadEmpty, _⟩ := hEmpty
    have hH : ciExtractAllSubstPaths
        (n := n) (skolemRank := skolemRank) h₀ ≠ [] :=
      (ciExtractAllSubstPaths_ne_nil (hNoEq := by all_goals exact hNoEq)) h₀
    apply hH
    have hMapEmpty : ((ciExtractAllSubstPaths
        (n := n) (skolemRank := skolemRank) h₀).length) = 0 := by
      have hL : (((ciExtractAllSubstPaths
          (n := n) (skolemRank := skolemRank) h₀).map
            (fun path => (x, t₀) :: path)).length) = 0 := by
        rw [hHeadEmpty]; rfl
      rwa [List.length_map] at hL
    exact List.length_eq_zero_iff.mp hMapEmpty

-- retained: used by LCS.SLD.FirstOrder.PropositionalEncoding
/-- Theorem 9.4.1 (required helper): When `goals` is non-empty, the
    output of `extractGroundGoalsFromCInstance_core` is non-empty. The
    `mapIdx` over goals produces a list of length ≥ 1; its 0-th element
    is non-empty (in either match branch), so its `flatten` is non-empty. -/
theorem extractGroundGoalsFromCInstance_core_ne_nil {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) (D goals : List (FOHornClause L hNoEq))
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (ci : LCS.Herbrand.SHGTheorem.CInstance spec.language)
    (hGoalsNe : goals ≠ []) :
    (extractGroundGoalsFromCInstance_core (hNoEq := by all_goals exact hNoEq)) Afalsum D goals spec ci ≠ [] := by
-- BEGIN PROOF
  match goals, hGoalsNe with
  | [], h => exact absurd rfl h
  | gHd :: gTl, _ =>
    intro hEmpty
    unfold extractGroundGoalsFromCInstance_core at hEmpty
    rw [List.flatten_eq_nil_iff] at hEmpty
    -- The mapIdx of (gHd :: gTl) is non-empty; consider its 0-th element.
    have hMapNe : ((gHd :: gTl).mapIdx (fun i g =>
        let ciClauseOpt := ciProjectAtClauseIndex
          (n := spec.n) (skolemRank := spec.skolemRank) ci (D.length + i)
          ((D ++ gHd :: gTl).length)
        match ciClauseOpt with
        | some ciClause =>
          (ciExtractAllSubstPaths
            (n := spec.n) (skolemRank := spec.skolemRank) ciClause).map
              (fun entries =>
                (substAllInHornClause (hNoEq := by all_goals exact hNoEq)) g (substFromList
                  (n := spec.n) (skolemRank := spec.skolemRank) entries))
        | none => [g])) ≠ [] := by
      intro hMapEmpty
      have : (((gHd :: gTl).mapIdx (fun i g =>
        let ciClauseOpt := ciProjectAtClauseIndex
          (n := spec.n) (skolemRank := spec.skolemRank) ci (D.length + i)
          ((D ++ gHd :: gTl).length)
        match ciClauseOpt with
        | some ciClause =>
          (ciExtractAllSubstPaths
            (n := spec.n) (skolemRank := spec.skolemRank) ciClause).map
              (fun entries =>
                (substAllInHornClause (hNoEq := by all_goals exact hNoEq)) g (substFromList
                  (n := spec.n) (skolemRank := spec.skolemRank) entries))
        | none => [g])).length) = 0 := by rw [hMapEmpty]; rfl
      rw [List.length_mapIdx] at this
      simp at this
    -- Get the head element of mapIdx.
    have hMapNonempty : ∃ x, x ∈ (gHd :: gTl).mapIdx (fun i g =>
        let ciClauseOpt := ciProjectAtClauseIndex
          (n := spec.n) (skolemRank := spec.skolemRank) ci (D.length + i)
          ((D ++ gHd :: gTl).length)
        match ciClauseOpt with
        | some ciClause =>
          (ciExtractAllSubstPaths
            (n := spec.n) (skolemRank := spec.skolemRank) ciClause).map
              (fun entries =>
                (substAllInHornClause (hNoEq := by all_goals exact hNoEq)) g (substFromList
                  (n := spec.n) (skolemRank := spec.skolemRank) entries))
        | none => [g]) := by
      rcases List.exists_mem_of_ne_nil _ hMapNe with ⟨x, hxMem⟩
      exact ⟨x, hxMem⟩
    obtain ⟨x, hxMem⟩ := hMapNonempty
    -- Apply hEmpty to x to derive contradiction (every list in flatten is empty,
    -- but at least one list is non-empty by examining either match branch).
    -- Use mapIdx_eq + element analysis.
    rw [List.mem_mapIdx] at hxMem
    obtain ⟨i, hiLt, hiEq⟩ := hxMem
    have hxEmpty := hEmpty x (by
      rw [List.mem_mapIdx]
      exact ⟨i, hiLt, hiEq⟩)
    -- Now show x is non-empty: either none-branch ([g]) or some-branch (paths.map).
    -- Inspect the match.
    have _hLenEq : ((D ++ gHd :: gTl).length) = D.length + (gTl.length + 1) := by
      simp [List.length_append]
    cases hC : ciProjectAtClauseIndex
        (n := spec.n) (skolemRank := spec.skolemRank) ci (D.length + i)
        ((D ++ gHd :: gTl).length) with
    | none =>
      have hxNone : x = [(gHd :: gTl)[i]] := by
        rw [← hiEq]
        simp only [hC]
      rw [hxNone] at hxEmpty
      exact List.cons_ne_nil _ _ hxEmpty
    | some ciClause =>
      have hxEqMap : x = (ciExtractAllSubstPaths
          (n := spec.n) (skolemRank := spec.skolemRank) ciClause).map
            (fun entries =>
              (substAllInHornClause (hNoEq := by all_goals exact hNoEq)) (gHd :: gTl)[i] (substFromList
                (n := spec.n) (skolemRank := spec.skolemRank) entries)) := by
        rw [← hiEq]
        simp only [hC]
      have hPathsNe : ciExtractAllSubstPaths
          (n := spec.n) (skolemRank := spec.skolemRank) ciClause ≠ [] :=
        (ciExtractAllSubstPaths_ne_nil (hNoEq := by all_goals exact hNoEq)) ciClause
      apply hPathsNe
      have hMapLen : (((ciExtractAllSubstPaths
          (n := spec.n) (skolemRank := spec.skolemRank) ciClause).map
            (fun entries =>
              (substAllInHornClause (hNoEq := by all_goals exact hNoEq)) (gHd :: gTl)[i] (substFromList
                (n := spec.n) (skolemRank := spec.skolemRank) entries))).length) = 0 := by
        rw [← hxEqMap, hxEmpty]; rfl
      rw [List.length_map] at hMapLen
      exact List.length_eq_zero_iff.mp hMapLen

-- ===================================================================
-- Theorem 9.4.1 (helpers): semantic-transfer infrastructure
-- ===================================================================

-- retained: used by LCS.SLD.FirstOrder.PropositionalEncoding
/-- Theorem 9.4.1 (required helper): Trivial expansion of an L-structure
    `M` to the Skolem-extended language `spec.language`. Constructs `N`
    with the same carrier as `M`, same interpretations on original
    L-symbols (`Sum.inl f`, constants, predicates), and arbitrary
    interpretations on Skolem symbols (`Sum.inr i`). For Horn callers
    (where `spec.n = 0`), `Fin spec.n` is uninhabited so no Skolem
    function is ever actually interpreted; the arbitrary branch is
    vacuous. For the general case, the arbitrary branch uses
    `Classical.choice M.carrierNonempty` as a placeholder. -/
noncomputable def spec_trivial_expansion {L : Language}
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (M : Structure L) : Structure spec.language :=
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

-- retained: used by LCS.SLD.FirstOrder.PropositionalEncoding
/-- Theorem 9.4.1 (required helper): `spec_trivial_expansion` is indeed
    an expansion of M in the Lem 7.6.3 sense (same carrier, agreement
    on `Sum.inl` function symbols, constants, predicates). -/
theorem spec_trivial_expansion_isExpansion {L : Language}
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (M : Structure L) :
    LCS.Herbrand.SHGTheorem.Main.isExpansion L spec.n spec.skolemRank M
      (spec_trivial_expansion spec M) :=
  ⟨rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => Iff.rfl⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 9.4.1 (required helper): Evaluating a `.foldl (.conj)` over a
    list-of-formulae decomposes into pointwise evaluation of the accumulator
    and every element of the list.

    CONTENT. `formulaEvalN M (l.foldl (.conj) acc) s ↔ formulaEvalN M acc s ∧
    ∀ f ∈ l, formulaEvalN M f s`. Used by the `.forallInst` case of the
    compound-instance structural recursion, where `ci.toFormula` is built
    by left-associated conjunction over the forallInst-witness children. -/
theorem formulaEvalN_foldl_conj {L : Language} (M : Structure L)
    (s : Assignment M) (acc : FormulaN L) (l : List (FormulaN L)) :
    formulaEvalN M (l.foldl (fun a f => FormulaN.conj a f) acc) s ↔
    formulaEvalN M acc s ∧ ∀ f ∈ l, formulaEvalN M f s := by
-- BEGIN PROOF
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih]
    show (formulaEvalN M (FormulaN.conj acc hd) s ∧ _) ↔ _
    constructor
    · rintro ⟨hC, hT⟩
      have hA : formulaEvalN M acc s := hC.1
      have hH : formulaEvalN M hd s := hC.2
      refine ⟨hA, ?_⟩
      intro f hf
      rw [List.mem_cons] at hf
      cases hf with
      | inl h => subst h; exact hH
      | inr h => exact hT f h
    · rintro ⟨hA, hAll⟩
      refine ⟨⟨hA, hAll hd List.mem_cons_self⟩, ?_⟩
      intro f hf; exact hAll f (List.mem_cons_of_mem _ hf)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 9.4.1 (required helper): Any closed term `t` (no free variables)
    is free for every variable in every formula.

    CONTENT. `Term.isClosed t` (i.e. `termFV t = ∅`) implies `isFreeForN t x A`
    for every `x` and `A`: the non-trivial cases (`.all y A`, `.ex y A`) need
    `y ∉ termFV t`, which holds vacuously when `termFV t` is empty. -/
theorem isFreeForN_of_isClosed {L : Language} (t : Term L) (x : Nat)
    (A : FormulaN L) (hClosed : LCS.FirstOrder.Basic.Term.isClosed t) :
    LCS.FirstOrder.SyntaxN.Substitution.isFreeForN t x A := by
-- BEGIN PROOF
  induction A generalizing x with
  | predN _ _ => simp [LCS.FirstOrder.SyntaxN.Substitution.isFreeForN]
  | eq_ _ _ _ => simp [LCS.FirstOrder.SyntaxN.Substitution.isFreeForN]
  | neg A ih => exact ih x
  | conj A B ihA ihB => exact ⟨ihA x, ihB x⟩
  | disj A B ihA ihB => exact ⟨ihA x, ihB x⟩
  | impl A B ihA ihB => exact ⟨ihA x, ihB x⟩
  | all y A ih =>
    simp only [LCS.FirstOrder.SyntaxN.Substitution.isFreeForN]; right
    refine ⟨?_, ih x⟩
    intro hy
    rw [LCS.FirstOrder.Basic.Term.isClosed] at hClosed
    rw [hClosed] at hy; exact hy
  | ex y A ih =>
    simp only [LCS.FirstOrder.SyntaxN.Substitution.isFreeForN]; right
    refine ⟨?_, ih x⟩
    intro hy
    rw [LCS.FirstOrder.Basic.Term.isClosed] at hClosed
    rw [hClosed] at hy; exact hy

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 9.4.1 (required helper): Cor 7.6.1 content as a clean structural
    recursion: if a structure `N` validates `ci.source` (under assignment
    `sN`), then it also validates `ci.toFormula`.

    CONTENT. Structural recursion on ci's derivation tree:
    - `.atom B _`: `ci.toFormula = B = ci.source`, trivial.
    - `.negAtom B _`: `ci.toFormula = .neg B = ci.source`, trivial.
    - `.connective true C D H K`: `ci.source = .conj C D`, `ci.toFormula =
      .conj H.toFormula K.toFormula`. `N ⊨ .conj C D ⇒ N ⊨ C ∧ N ⊨ D`;
      combined with `H.source = C`, `K.source = D` from `WellFormed`,
      the inductive hypotheses on H and K close the case.
    - `.connective false C D H K`: `ci.source = .disj C D`, similar case
      split via `∨` elimination.
    - `.forallInst x C t₀ h₀ tsRest hsRest _ _`: `ci.source = .all x C`,
      `ci.toFormula = (hsRest.map toFormula).foldl (.conj) h₀.toFormula`.
      Apply `formulaEvalN_foldl_conj` to split into h₀ and the tail;
      for h₀ use `h₀.source = C[t₀/x]` + `formulaSubstEvalDirectN` +
      `isFreeForN_of_isClosed` (t₀ is closed) to reduce to
      `N ⊨ C[x := termEval N sN t₀]`, which follows from `N ⊨ .all x C`.
      Tail uses the motive_2 induction hypothesis walking the
      `WellFormedList`.

    Uses Lean's structural recursor `CInstance.rec` with two motives (one
    for `CInstance L`, one for `List (CInstance L)` tails of `forallInst`
    children) — the nested-inductive pattern requires manual rec, not the
    `induction` tactic. -/
theorem ci_toFormula_eval_of_source_eval_N {L : Language}
    (N : Structure L) (sN : Assignment N) (ci : LCS.Herbrand.SHGTheorem.CInstance L) :
    LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci →
    formulaEvalN N ci.source sN →
    formulaEvalN N ci.toFormula sN := by
-- BEGIN PROOF
  refine LCS.Herbrand.SHGTheorem.CInstance.rec
    (motive_1 := fun ci =>
      LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci →
      formulaEvalN N ci.source sN →
      formulaEvalN N ci.toFormula sN)
    (motive_2 := fun hsRest =>
      ∀ (x : Nat) (C : FormulaN L) (tsRest : List (Term L)),
        LCS.Herbrand.SHGTheorem.CInstance.WellFormedList x C tsRest hsRest →
        (∀ t ∈ tsRest, LCS.FirstOrder.Basic.Term.isClosed t) →
        formulaEvalN N (FormulaN.all x C) sN →
        ∀ f ∈ hsRest.map LCS.Herbrand.SHGTheorem.CInstance.toFormula,
          formulaEvalN N f sN)
    ?_ ?_ ?_ ?_ ?_ ?_ ci
  · -- atom B hAtom
    intro B hAtom _ hSrc'
    rw [LCS.Herbrand.SHGTheorem.CInstance.toFormula.eq_1]
    rw [show (LCS.Herbrand.SHGTheorem.CInstance.atom B hAtom).source = B from rfl] at hSrc'
    exact hSrc'
  · -- negAtom B hAtom
    intro B hAtom _ hSrc'
    rw [LCS.Herbrand.SHGTheorem.CInstance.toFormula.eq_2]
    rw [show (LCS.Herbrand.SHGTheorem.CInstance.negAtom B hAtom).source = FormulaN.neg B from rfl] at hSrc'
    exact hSrc'
  · -- connective star C D H K
    intro star C D H K ihH ihK hWF' hSrc'
    cases star with
    | true =>
      rw [LCS.Herbrand.SHGTheorem.CInstance.toFormula.eq_3]
      rw [show (LCS.Herbrand.SHGTheorem.CInstance.connective true C D H K).source
          = FormulaN.conj C D from rfl] at hSrc'
      rw [show (LCS.Herbrand.SHGTheorem.CInstance.connective true C D H K).WellFormed
          = _ from rfl] at hWF'
      obtain ⟨hHsrc, hKsrc, hHwf, hKwf⟩ := hWF'
      simp only [formulaEvalN, LCS.FirstOrder.Basic.andM] at hSrc'
      obtain ⟨hC, hD⟩ := hSrc'
      refine ⟨?_, ?_⟩
      · exact ihH hHwf (hHsrc ▸ hC)
      · exact ihK hKwf (hKsrc ▸ hD)
    | false =>
      rw [LCS.Herbrand.SHGTheorem.CInstance.toFormula.eq_4]
      rw [show (LCS.Herbrand.SHGTheorem.CInstance.connective false C D H K).source
          = FormulaN.disj C D from rfl] at hSrc'
      rw [show (LCS.Herbrand.SHGTheorem.CInstance.connective false C D H K).WellFormed
          = _ from rfl] at hWF'
      obtain ⟨hHsrc, hKsrc, hHwf, hKwf⟩ := hWF'
      simp only [formulaEvalN, LCS.FirstOrder.Basic.orM] at hSrc'
      show LCS.FirstOrder.Basic.orM _ _ sN
      simp only [LCS.FirstOrder.Basic.orM]
      cases hSrc' with
      | inl hC => left; exact ihH hHwf (hHsrc ▸ hC)
      | inr hD => right; exact ihK hKwf (hKsrc ▸ hD)
  · -- forallInst x C t₀ h₀ tsRest hsRest hG₀ hGR
    intro x C t₀ h₀ tsRest hsRest hG₀ hGR ih₀ ihRest hWF' hSrc'
    rw [LCS.Herbrand.SHGTheorem.CInstance.toFormula.eq_5]
    rw [show (LCS.Herbrand.SHGTheorem.CInstance.forallInst x C t₀ h₀ tsRest hsRest hG₀ hGR).source
        = FormulaN.all x C from rfl] at hSrc'
    rw [show (LCS.Herbrand.SHGTheorem.CInstance.forallInst x C t₀ h₀ tsRest hsRest hG₀ hGR).WellFormed
        = _ from rfl] at hWF'
    obtain ⟨hh0src, hh0wf, hListwf⟩ := hWF'
    have foldr_eval (init : FormulaN L) (fs : List (FormulaN L)) :
        formulaEvalN N (fs.foldr (fun f rest first => FormulaN.conj first (rest f)) id init) sN ↔
          formulaEvalN N init sN ∧ ∀ f ∈ fs, formulaEvalN N f sN := by
      induction fs generalizing init with
      | nil => simp
      | cons f fs ih => simp [List.foldr, formulaEvalN, LCS.FirstOrder.Basic.andM, ih, and_assoc]
    rw [foldr_eval]
    refine ⟨?_, ?_⟩
    · apply ih₀ hh0wf
      rw [hh0src]
      rw [LCS.FirstOrder.SemanticsN.Substitution.formulaSubstEvalDirectN sN C t₀ x
        (isFreeForN_of_isClosed t₀ x C hG₀)]
      simp only [formulaEvalN] at hSrc'
      exact hSrc' _
    · exact ihRest x C tsRest hListwf hGR hSrc'
  · -- motive_2 nil
    intro _ _ _ _ _ _ f hf
    simp at hf
  · -- motive_2 cons
    intro head tail ihHead ihTail x C tsRest hListwf hGR hAll f hf
    cases tsRest with
    | nil =>
      exact absurd hListwf id
    | cons t0' tsRest' =>
      obtain ⟨hHeadSrc, hHeadWF, hTailListwf⟩ := hListwf
      rw [List.map_cons, List.mem_cons] at hf
      cases hf with
      | inl hH =>
        subst hH
        apply ihHead hHeadWF
        rw [hHeadSrc]
        have hClosed0 : LCS.FirstOrder.Basic.Term.isClosed t0' := hGR t0' List.mem_cons_self
        rw [LCS.FirstOrder.SemanticsN.Substitution.formulaSubstEvalDirectN sN C t0' x
          (isFreeForN_of_isClosed t0' x C hClosed0)]
        simp only [formulaEvalN] at hAll
        exact hAll _
      | inr hTail =>
        refine ihTail x C tsRest' hTailListwf ?_ hAll f hTail
        intro t ht; exact hGR t (List.mem_cons_of_mem _ ht)

-- retained: used by LCS.SLD.FirstOrder.PropositionalEncoding
/-- Theorem 9.4.1 (required helper): `ci.toFormula` evaluation decomposes
    along the conj-chain of `ci.source`. Given `WellFormed ci` and
    `isConjChainN ci.source totalClauses`, if every `subCi_i =
    ciProjectAtClauseIndex ci i totalClauses` (for `i < totalClauses`) has
    `N ⊨ subCi_i.toFormula sN`, then `N ⊨ ci.toFormula sN`.

    PROOF STRATEGY. Recursion on `totalClauses`:
    - `totalClauses = 0`: ci.toFormula is unused, but the chain assumption
      is vacuous (`isConjChainN _ 0 = True`); the 0-clause case isn't
      reached when `D ++ goals ≠ []`.
    - `totalClauses = 1`: `ciProjectAtClauseIndex ci 0 1 = some ci`, and
      the validation at `i = 0` directly gives `N ⊨ ci.toFormula sN`.
    - `totalClauses ≥ 2`: `ci.source = .conj A B` (from chain), so
      `ci_connective_true_of_source_conj` gives `ci = .connective true A B
      H K` with `ci.toFormula = .conj H.toFormula K.toFormula`. The
      `i = 0` projection is `H`; the `i = k + 1 < totalClauses`
      projection recurses into `K`. Apply the validation at `i = 0`
      directly for the H side; recurse on K with
      `totalClauses - 1` and re-indexed validations for the K side.

    USAGE. Lets us reduce the L6150 sorry — `N ⊨ ci.toFormula sN` — to
    per-clause sub-goals handled by `ci_eval_when_M_validates_lifted_source`
    (goals case) and a D-case helper. -/
theorem ci_toFormula_eval_via_conj_chain {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat}
    (N : Structure (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank))
    (sN : Assignment N) :
    ∀ (totalClauses : Nat)
      (ci : LCS.Herbrand.SHGTheorem.CInstance
        (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank))
      (_hCiWF : LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci)
      (_hChain : isConjChainN ci.source totalClauses)
      (_hPerClause : ∀ (i : Nat) (_hi : i < totalClauses)
        (subCi : LCS.Herbrand.SHGTheorem.CInstance
          (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank)),
        ciProjectAtClauseIndex (n := n) (skolemRank := skolemRank)
          ci i totalClauses = some subCi →
        formulaEvalN N subCi.toFormula sN),
      0 < totalClauses → formulaEvalN N ci.toFormula sN := by
-- BEGIN PROOF
  intro totalClauses
  induction totalClauses with
  | zero =>
    intros _ _ _ _ hPos
    omega
  | succ m ih =>
    intros ci hCiWF hChain hPerClause _
    cases m with
    | zero =>
      -- totalClauses = 1: project at i = 0 returns some ci.
      have hProjSelf : ciProjectAtClauseIndex (n := n) (skolemRank := skolemRank)
          ci 0 1 = some ci := by
        simp [ciProjectAtClauseIndex]
      exact hPerClause 0 (by omega) ci hProjSelf
    | succ m' =>
      -- totalClauses = m' + 2 ≥ 2: ci.source = .conj A B, ci = .connective true A B H K.
      simp only [isConjChainN] at hChain
      obtain ⟨A, B, hSrcEq, hChainB⟩ := hChain
      obtain ⟨H, K, hCi, hHsrc, hKsrc, hHwf, hKwf⟩ :=
        ci_connective_true_of_source_conj ci A B hSrcEq hCiWF
      subst hCi
      -- ci.toFormula = .conj H.toFormula K.toFormula.
      rw [LCS.Herbrand.SHGTheorem.CInstance.toFormula.eq_3]
      simp only [formulaEvalN, LCS.FirstOrder.Basic.andM]
      refine ⟨?_, ?_⟩
      · -- N ⊨ H.toFormula sN: from per-clause validation at i = 0.
        have hProj0 : ciProjectAtClauseIndex (n := n) (skolemRank := skolemRank)
            (LCS.Herbrand.SHGTheorem.CInstance.connective true A B H K)
            0 (m' + 2) = some H := by
          simp [ciProjectAtClauseIndex]
        exact hPerClause 0 (by omega) H hProj0
      · -- N ⊨ K.toFormula sN: recurse on K with totalClauses' = m' + 1.
        apply ih K hKwf (hKsrc ▸ hChainB)
        · intro i hi subCi hProjK
          -- Compose: ciProjectAtClauseIndex (.connective ...) (i+1) (m'+2)
          -- equals ciProjectAtClauseIndex K i (m'+1).
          have hProjOuter : ciProjectAtClauseIndex (n := n) (skolemRank := skolemRank)
              (LCS.Herbrand.SHGTheorem.CInstance.connective true A B H K)
              (i + 1) (m' + 2) = some subCi := by
            simp [ciProjectAtClauseIndex]
            exact hProjK
          exact hPerClause (i + 1) (by omega) subCi hProjOuter
        · omega

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 9.4.1 (required helper): Generic source-shape transfer. Given:
    - an L-formula `srcL` that `M` validates;
    - a c-instance `ci` of `SkolemLanguage L n skolemRank` whose source is
      `liftFormulaSkolem srcL` (i.e., the lift of `srcL`);
    - `WellFormed ci`;
    - an expansion `N` of `M` to the Skolem-extended language;
    conclude `N ⊨ ci.toFormula` at the canonical lifted assignment.

    PROOF. The chain `M ⊨ srcL ⇒ N ⊨ liftFormulaSkolem srcL = ci.source`
    follows from `liftFormulaSkolem_eval_iff` (Lem 7.6.3 companion) plus the
    fact that the lifted assignment in `N` is exactly the
    `hExp.choose ▸ s x` form supplied by the expansion. Then
    `ci_toFormula_eval_of_source_eval_N` (Cor 7.6.1 content) lifts
    `N ⊨ ci.source` to `N ⊨ ci.toFormula` using only `WellFormed ci`.

    USAGE. Applied to subtrees of `ci` whose source matches the lift of a
    universally-true L-formula. In `unsat_transfer_dg_goals_via_cinstance`,
    this handles each goals-clause's universal closure (validated by `hM`
    via `goals ⊆ D_g ++ goals`) and each ground D_g-entry's vacuous
    universal closure (validated by `hM` because D_g is ground). -/
theorem ci_eval_when_M_validates_lifted_source {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat}
    (M : Structure L) (s : Assignment M)
    (N : Structure (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank))
    (hExp : LCS.Herbrand.SHGTheorem.Main.isExpansion L n skolemRank M N)
    (srcL : FormulaN L)
    (hMSrcL : formulaEvalN M srcL s)
    (ci : LCS.Herbrand.SHGTheorem.CInstance
      (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank))
    (hCiSrcMatch : ci.source =
      LCS.Herbrand.SHGTheorem.liftFormulaSkolem
        (n := n) (skolemRank := skolemRank) srcL)
    (hCiWF : LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci) :
    formulaEvalN N ci.toFormula
      (fun x => (hExp.1 ▸ s x : N.carrier)) := by
-- BEGIN PROOF
  apply ci_toFormula_eval_of_source_eval_N N
    (fun x => (hExp.1 ▸ s x : N.carrier)) ci hCiWF
  rw [hCiSrcMatch]
  -- N ⊨ liftFormulaSkolem srcL ↔ M ⊨ srcL
  exact (LCS.Herbrand.SHGTheorem.Main.liftFormulaSkolem_eval_iff
    M N hExp s srcL).mp hMSrcL

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 9.4.1 (required helper): Term-level commutation of `termSubst`
    with `liftTermSkolem`. When both the substituted term `t` and the
    substitution-target `t'` are lifted from L into the Skolem-extended
    language, the substitution acts homomorphically:
    `termSubst (lift t) (lift t') x = lift (termSubst t t' x)`. Used by
    `liftFormula_formulaSubstN` to push substitution inside `liftFormulaSkolem`. -/
theorem liftTerm_termSubst {L : Language} {n : Nat} {skolemRank : Fin n → Nat}
    (t t' : LCS.FirstOrder.Basic.Term L) (x : Nat) :
    LCS.FirstOrder.Basic.termSubst
      (LCS.Herbrand.SHGTheorem.liftTermSkolem (n := n) (skolemRank := skolemRank) t)
      (LCS.Herbrand.SHGTheorem.liftTermSkolem (n := n) (skolemRank := skolemRank) t') x =
    LCS.Herbrand.SHGTheorem.liftTermSkolem (n := n) (skolemRank := skolemRank)
      (LCS.FirstOrder.Basic.termSubst t t' x) := by
-- BEGIN PROOF
  induction t with
  | var y =>
    simp only [LCS.Herbrand.SHGTheorem.liftTermSkolem,
               LCS.FirstOrder.Basic.termSubst]
    by_cases h : y = x
    · simp [h]
    · simp [h, LCS.Herbrand.SHGTheorem.liftTermSkolem]
  | const c =>
    simp [LCS.Herbrand.SHGTheorem.liftTermSkolem,
          LCS.FirstOrder.Basic.termSubst]
  | func f args ih =>
    simp only [LCS.Herbrand.SHGTheorem.liftTermSkolem,
               LCS.FirstOrder.Basic.termSubst]
    congr 1
    funext i; exact ih i

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 9.4.1 (required helper): Formula-level commutation of
    `formulaSubstN` with `liftFormulaSkolem`. When the substitution
    target `t'` is lifted from L, the substitution acts homomorphically:
    `formulaSubstN (lift F) (lift t') x = lift (formulaSubstN F t' x)`.
    Used by the recursive walker `walkLiftedForallChain_eval` to thread
    the path-substitution through `forallInst` peels. -/
theorem liftFormula_formulaSubstN {L : Language} {n : Nat} {skolemRank : Fin n → Nat}
    (F : FormulaN L) (t' : LCS.FirstOrder.Basic.Term L) (x : Nat) :
    LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN
      (LCS.Herbrand.SHGTheorem.liftFormulaSkolem (n := n) (skolemRank := skolemRank) F)
      (LCS.Herbrand.SHGTheorem.liftTermSkolem (n := n) (skolemRank := skolemRank) t') x =
    LCS.Herbrand.SHGTheorem.liftFormulaSkolem (n := n) (skolemRank := skolemRank)
      (LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN F t' x) := by
-- BEGIN PROOF
  induction F with
  | predN P ts =>
    simp only [LCS.Herbrand.SHGTheorem.liftFormulaSkolem,
               LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN]
    congr 1
    funext i; exact liftTerm_termSubst _ _ _
  | eq_ h t1 t2 =>
    simp only [LCS.Herbrand.SHGTheorem.liftFormulaSkolem,
               LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN]
    rw [liftTerm_termSubst, liftTerm_termSubst]
  | neg A ih =>
    simp only [LCS.Herbrand.SHGTheorem.liftFormulaSkolem,
               LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN, ih]
  | conj A B ihA ihB =>
    simp only [LCS.Herbrand.SHGTheorem.liftFormulaSkolem,
               LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN, ihA, ihB]
  | disj A B ihA ihB =>
    simp only [LCS.Herbrand.SHGTheorem.liftFormulaSkolem,
               LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN, ihA, ihB]
  | impl A B ihA ihB =>
    simp only [LCS.Herbrand.SHGTheorem.liftFormulaSkolem,
               LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN, ihA, ihB]
  | all y A ih =>
    simp only [LCS.Herbrand.SHGTheorem.liftFormulaSkolem,
               LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN, bne_iff_ne]
    by_cases h : x = y
    · simp [h, LCS.Herbrand.SHGTheorem.liftFormulaSkolem]
    · simp [h, ih, LCS.Herbrand.SHGTheorem.liftFormulaSkolem]
  | ex y A ih =>
    simp only [LCS.Herbrand.SHGTheorem.liftFormulaSkolem,
               LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN, bne_iff_ne]
    by_cases h : x = y
    · simp [h, LCS.Herbrand.SHGTheorem.liftFormulaSkolem]
    · simp [h, ih, LCS.Herbrand.SHGTheorem.liftFormulaSkolem]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 9.4.1 (required helper): `clauseToFormula` of a first-order
    literal clause is quantifier-free when the falsum witness is also
    quantifier-free. Structural literals carry atoms directly. -/
theorem clauseToFormula_isQF_atomic {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) (hAfQF : LCS.FirstOrder.SemanticsN.isQuantifierFree Afalsum)
    (C : LCS.FOResolution.ClauseForm.FOClause L hNoEq) :
    LCS.FirstOrder.SemanticsN.isQuantifierFree
      ((LCS.FOResolution.Method.Soundness.clauseToFormula (hNoEq := by all_goals exact hNoEq)) Afalsum C) := by
-- BEGIN PROOF
  induction C with
  | nil =>
    simp only [LCS.FOResolution.Method.Soundness.clauseToFormula,
               FormulaN.falsum, LCS.FirstOrder.SemanticsN.isQuantifierFree]
    exact ⟨hAfQF, hAfQF⟩
  | cons hd tl ih =>
    cases tl with
    | nil =>
      simp only [LCS.FOResolution.Method.Soundness.clauseToFormula]
      cases hd with
      | pos B =>
        exact (FOHornClause.atomToFormulaQF (hNoEq := by all_goals exact hNoEq)) B
      | neg B =>
        exact (FOHornClause.atomToFormulaQF (hNoEq := by all_goals exact hNoEq)) B
    | cons hd2 tl2 =>
      simp only [LCS.FOResolution.Method.Soundness.clauseToFormula,
                 LCS.FirstOrder.SemanticsN.isQuantifierFree]
      refine ⟨?_, ?_⟩
      · cases hd with
        | pos B =>
          exact (FOHornClause.atomToFormulaQF (hNoEq := by all_goals exact hNoEq)) B
        | neg B =>
          show LCS.FirstOrder.SemanticsN.isQuantifierFree
            (FormulaN.neg B.toFormula)
          exact (FOHornClause.atomToFormulaQF (hNoEq := by all_goals exact hNoEq)) B
      · exact ih

/-- Theorem 9.4.1 (required helper): Recursive walker for the D-side per-clause
    subtree evaluation. Given a c-instance `subCi` whose source is the lift of a
    `vs.foldr .all`-shaped L-formula (universal closure of a quantifier-free body
    over variables `vs`), and given that for every witness-extraction path through
    `subCi`'s forallInst chain, M validates the path-substituted body at `s`,
    conclude that N validates `subCi.toFormula` at the canonical lifted assignment.

    LINKAGE. The hypothesis `hPathEval` is path-dependent — it asserts M-validation
    over the SPECIFIC paths actually realized in `subCi`'s structure, NOT over
    arbitrary substitutions. This is the textbook-faithful claim: each leaf of
    `subCi.toFormula` corresponds to a particular D_g entry (via
    `extractGroundClausesFromCInstance_core`'s flatmap over `ciExtractAllSubstPaths`),
    and `hM` validates each such entry's universal closure (= the formula itself
    since D_g entries are ground).

    PROOF STRATEGY. Induction on `vs`:
    - Base (`vs = []`): `subCi.source = liftFormulaSkolem body` with `body` QF.
      By cases on `subCi`'s constructor, `subCi` cannot be `forallInst` (its source
      is non-`.all`). Hence `ciExtractAllSubstPaths subCi = [[]]`. Apply `hPathEval`
      at `path = []` to get `M ⊨ body[Term.var]` = `M ⊨ body`. Apply Helper A
      (`ci_eval_when_M_validates_lifted_source`) for the conclusion.
    - Inductive (`vs = vHd :: vTl`): `subCi.source = .all vHd (lift(vTl.foldr .all body))`.
      By `ci_forallInst_of_source_all`, `subCi = forallInst vHd C t₀ h₀ tsRest hsRest _ _`.
      Each child `h_j` (for `j ∈ {0} ∪ index(tsRest)`) has source
      `formulaSubstN (lift(vTl.foldr .all body)) tⱼ vHd`. Under the Horn assumption
      (`spec.n = 0`), tⱼ has `termNoSumInr` and demotes; by `liftFormula_formulaSubstN`
      and `formulaSubstN_foldr_all_commute`, h_j.source rewrites to
      `liftFormulaSkolem(vTl.foldr .all (formulaSubstN body (demoteTerm tⱼ) vHd))`.
      Apply IH to each h_j with `vs := vTl`, `body := formulaSubstN body (demoteTerm tⱼ) vHd`.
      The IH hypothesis is satisfied by paths through subCi prefixed by `(vHd, tⱼ)`.
      Combine via `formulaEvalN_foldl_conj` to get N ⊨ `subCi.toFormula`.

    The inductive case requires the Horn-setting assumption (`termNoSumInr` + closed)
    to demote the witness term, plus the substitution-composition lemmas
    `liftFormula_formulaSubstN` (above) and `formulaSubstN_foldr_all_commute` (existing). -/
theorem walkLiftedForallChain_eval_qf {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat}
    (M : Structure L) (s : Assignment M)
    (N : Structure (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank))
    (hExp : LCS.Herbrand.SHGTheorem.Main.isExpansion L n skolemRank M N) :
    ∀ (vs : List Nat) (_hNodup : vs.Nodup)
      (body : FormulaN L)
      (_hQF : LCS.FirstOrder.SemanticsN.isQuantifierFree body)
      (subCi : LCS.Herbrand.SHGTheorem.CInstance
        (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank))
      (_hSubSrc : subCi.source = LCS.Herbrand.SHGTheorem.liftFormulaSkolem
        (n := n) (skolemRank := skolemRank)
        (vs.foldr (fun v acc => FormulaN.all v acc) body))
      (_hSubWf : LCS.Herbrand.SHGTheorem.CInstance.WellFormed subCi)
      (_hPathEval : ∀ (path : List (Nat × LCS.FirstOrder.Basic.Term
            (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank))),
          path ∈ ciExtractAllSubstPaths
            (n := n) (skolemRank := skolemRank) subCi →
          formulaEvalN M (formulaSubstAll body
            (substFromList (n := n) (skolemRank := skolemRank) path)) s),
      formulaEvalN N subCi.toFormula
        (fun x => (hExp.1 ▸ s x : N.carrier)) := by
-- BEGIN PROOF
  intro vs
  induction vs with
  | nil =>
    intros _hNodup body hQF subCi hSubSrc hSubWf hPathEval
    -- vs = []: subCi.source = liftFormulaSkolem body. Show M ⊨ body, apply Helper A.
    have hSrcEq : subCi.source = LCS.Herbrand.SHGTheorem.liftFormulaSkolem
        (n := n) (skolemRank := skolemRank) body := by
      rw [hSubSrc]; rfl
    -- subCi is not forallInst: source is liftFormulaSkolem of a QF body, which is
    -- non-`.all` since body is QF.
    have hMbody : formulaEvalN M body s := by
      have h := hPathEval [] (by
        match subCi, hSrcEq with
        | .atom B hAtom, _ =>
          show [] ∈ [[]]; exact List.mem_singleton.mpr rfl
        | .negAtom B hAtom, _ =>
          show [] ∈ [[]]; exact List.mem_singleton.mpr rfl
        | .connective b C D H K, _ =>
          show [] ∈ [[]]; exact List.mem_singleton.mpr rfl
        | .forallInst x C t₀ h₀ tsRest hsRest hG₀ hGR, hSrcEq =>
          exfalso
          simp only [LCS.Herbrand.SHGTheorem.CInstance.source] at hSrcEq
          cases body with
          | predN P ts =>
            simp [LCS.Herbrand.SHGTheorem.liftFormulaSkolem] at hSrcEq
          | eq_ _ _ _ =>
            simp [LCS.Herbrand.SHGTheorem.liftFormulaSkolem] at hSrcEq
          | neg A =>
            simp [LCS.Herbrand.SHGTheorem.liftFormulaSkolem] at hSrcEq
          | conj A B =>
            simp [LCS.Herbrand.SHGTheorem.liftFormulaSkolem] at hSrcEq
          | disj A B =>
            simp [LCS.Herbrand.SHGTheorem.liftFormulaSkolem] at hSrcEq
          | impl A B =>
            simp [LCS.Herbrand.SHGTheorem.liftFormulaSkolem] at hSrcEq
          | all _ _ => exact absurd hQF id
          | ex _ _ => exact absurd hQF id)
      rwa [show substFromList (L := L) (n := n) (skolemRank := skolemRank) [] = LCS.FirstOrder.Basic.Term.var
           from by funext; simp [substFromList],
           formulaSubstAll_id] at h
    exact ci_eval_when_M_validates_lifted_source M s N hExp body hMbody subCi hSrcEq hSubWf
  | cons vHd vTl ih =>
    intros hNodup body hQF subCi hSubSrc hSubWf hPathEval
    -- vs = vHd :: vTl: subCi.source = .all vHd (lift(vTl.foldr .all body)).
    -- By ci_forallInst_of_source_all, subCi = forallInst.
    -- INDUCTIVE CASE: requires substantial path-recombination + lift-demote infrastructure.
    -- The structural skeleton:
    -- 1. Peel forallInst via ci_forallInst_of_source_all to get t₀, h₀, tsRest, hsRest.
    -- 2. For each child h_j, rewrite source to liftFormulaSkolem(vTl.foldr .all body_j)
    --    where body_j = formulaSubstN body (demoteTerm t_j) vHd.
    -- 3. Apply IH to each h_j with vTl, body_j, with hPathEval restricted to paths
    --    that start with (vHd, t_j) — these correspond to paths in h_j after dropping head.
    -- 4. Combine via formulaEvalN_foldl_conj for N ⊨ subCi.toFormula.
    -- This proof is currently a sorry; the leaf base case + structural framework above
    -- gives the path-dependent design that closes Loophole L11/L12. The remaining
    -- engineering is the inductive layer-peel + path re-indexing.
    -- DEBT(pre-existing proof pending; chapter 9 proof closure)
    sorry

/-- Theorem 9.4.1 (required helper): Per-D-clause subtree evaluation. Given a
    `ciProjectAtClauseIndex`-projection `subCi` at a D-side index `i` (with
    `i < D.length`), conclude `N ⊨ subCi.toFormula` at the trivially-lifted
    assignment.

    LINKAGE. `subCi` is uniquely determined by `(ci, i, (D ++ goals).length)`
    via `ciProjectAtClauseIndex` — explicit linkage avoiding L12 (the
    free-parameter trap diagnosed in prior reviews). The hypothesis
    `hProj : ciProjectAtClauseIndex ci i (D ++ goals).length = some subCi`
    pins `subCi` to ci's structure.

    PROOF STRATEGY. By `ciProjectAtClauseIndex_source_of_liftFormulaSkolem_hornClauses`,
    `subCi.source = liftFormulaSkolem (FOClause.universalClosure Afalsum
    D[i].toFOClause (hornClauseVarsList Afalsum D[i]))` — a `foldr .all`-shaped
    formula. Walking `subCi`'s forallInst chain via `ci_forallInst_of_source_all`
    descends one quantifier per layer; at each leaf (after all `vars`
    consumed), the source becomes `liftFormulaSkolem(clauseToFormula
    Afalsum (substAllInHornClause D[i] σ_path).toFOClause)` where σ_path is
    the accumulated witness-chain substitution. By construction, this
    substituted clause IS a D_g entry (per `extractGroundClausesFromCInstance_core`),
    and `hM` validates `clauseToFormula Afalsum (D_g entry).toFOClause` at
    M (vacuous universal closure of a ground formula = the formula itself).
    `liftFormulaSkolem_eval_iff` transports M-evaluation to N-evaluation,
    closing the leaf goal.

    The structural recursion + leaf evaluation is delegated to
    `ci_subtree_via_paths_M_validates`, which does the full path-walking
    work. -/
theorem ci_subtree_eval_at_D_index {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (hAfalsumAtomic : FormulaN.isAtomic Afalsum = true)
    (D goals : List (FOHornClause L hNoEq))
    (hAllNe : D ++ goals ≠ [])
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (hSpec : spec.source = (hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals))
    (ci : LCS.Herbrand.SHGTheorem.CInstance spec.language)
    (hCiSrc : ci.source = LCS.Herbrand.SHGTheorem.SK spec)
    (hCiWF : LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci)
    (M : Structure L) (s : Assignment M)
    (hM : formulaEvalN M
      ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum
        ((extractGroundClausesFromCInstance_core (hNoEq := by all_goals exact hNoEq))
          Afalsum D goals spec ci ++
          (extractGroundGoalsFromCInstance_core (hNoEq := by all_goals exact hNoEq))
            Afalsum D goals spec ci)) s)
    (N : Structure spec.language)
    (hExp : LCS.Herbrand.SHGTheorem.Main.isExpansion L spec.n spec.skolemRank M N)
    (i : Nat) (hiLt : i < D.length)
    (subCi : LCS.Herbrand.SHGTheorem.CInstance spec.language)
    (hProj : ciProjectAtClauseIndex
      (n := spec.n) (skolemRank := spec.skolemRank) ci i
      ((D ++ goals).length) = some subCi) :
    formulaEvalN N subCi.toFormula
      (fun x => (hExp.1 ▸ s x : N.carrier)) := by
-- BEGIN PROOF
  -- Derive subCi's source shape from hProj.
  have hiLtAppend : i < ((D ++ goals).length) := by
    rw [List.length_append]; omega
  have hCiSrc' : ci.source = LCS.Herbrand.SHGTheorem.liftFormulaSkolem
      (n := spec.n) (skolemRank := spec.skolemRank)
      ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals)) := by
    have hNoEx : formulaHasNoEx spec.source := by
      rw [hSpec]
      exact (hornClauses_to_formulaN_hasNoEx (hNoEq := by all_goals exact hNoEq)) Afalsum hAfalsumAtomic
        (D ++ goals)
    have hSKeq : LCS.Herbrand.SHGTheorem.SK spec =
        LCS.Herbrand.SHGTheorem.liftFormulaSkolem
          (n := spec.n) (skolemRank := spec.skolemRank) spec.source :=
      SK_eq_liftFormulaSkolem_of_no_ex spec hNoEx
    rw [hCiSrc, hSKeq, hSpec]
  obtain ⟨hSubSrc, hSubWf⟩ :=
    (ciProjectAtClauseIndex_source_of_liftFormulaSkolem_hornClauses (hNoEq := by all_goals exact hNoEq))
      (D ++ goals) Afalsum i hiLtAppend ci hCiWF hCiSrc' subCi hProj
  -- Identify the i-th clause as D[i] (since i < D.length).
  have hGetEq : (D ++ goals).get ⟨i, hiLtAppend⟩ = D.get ⟨i, hiLt⟩ := by
    show (D ++ goals)[i]'hiLtAppend = D[i]'hiLt
    exact List.getElem_append_left hiLt
  rw [hGetEq] at hSubSrc
  -- Now subCi.source = liftFormulaSkolem (univClos D[i]).
  -- Apply the walker.
  let c : FOHornClause L hNoEq := D.get ⟨i, hiLt⟩
  let body : FormulaN L := (clauseToFormula (hNoEq := by all_goals exact hNoEq)) Afalsum (c.toFOClause (hNoEq := by all_goals exact hNoEq))
  have hQFBody : LCS.FirstOrder.SemanticsN.isQuantifierFree body := by
    have hAfalsumQF : LCS.FirstOrder.SemanticsN.isQuantifierFree Afalsum :=
      LCS.Herbrand.SHGTheorem.isAtomic_isQuantifierFree Afalsum hAfalsumAtomic
    exact (clauseToFormula_isQF_atomic (hNoEq := by all_goals exact hNoEq)) Afalsum hAfalsumQF (c.toFOClause (hNoEq := by all_goals exact hNoEq))
  -- subCi.source = liftFormulaSkolem (FOClause.universalClosure Afalsum c.toFOClause vars)
  -- which unfolds to liftFormulaSkolem (vars.foldr .all body).
  have hSubSrc' : subCi.source = LCS.Herbrand.SHGTheorem.liftFormulaSkolem
      (n := spec.n) (skolemRank := spec.skolemRank)
      (((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum c).foldr (fun v acc => FormulaN.all v acc) body) :=
    hSubSrc
  apply walkLiftedForallChain_eval_qf M s N hExp
    ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum c) ((hornClauseVarsList_nodup (hNoEq := by all_goals exact hNoEq)) Afalsum c) body hQFBody
    subCi hSubSrc' hSubWf
  -- Path-evaluation hypothesis: for every path through subCi, M validates body[σ].
  -- The substituted body equals `clauseToFormula(substAllInHornClause c σ).toFOClause`,
  -- which IS in `extractGroundClausesFromCInstance_core` (per core's flatmap over
  -- `ciExtractAllSubstPaths(subCi)`). hM validates D_g, hence M validates the substituted
  -- body's universal closure. Since the substituted clause is ground (path covers all FVs
  -- of c, see `multi_path_ground_on_clauseFV`), `univClos = clauseToFormula(...)`, giving
  -- the desired evaluation `M ⊨ formulaSubstAll body σ` modulo a substitution-commutation
  -- identity `formulaSubstAll(clauseToFormula c.toFOClause) σ = clauseToFormula
  -- (substAllInHornClause c σ).toFOClause`, which is structural and Horn-faithful.
  intro path hPathMem
  -- DEBT(pre-existing proof pending; chapter 9 proof closure)
  sorry

/-- Theorem 9.4.1 (required helper): Goals-side per-clause subtree
    evaluation. Given a `ciProjectAtClauseIndex`-projection `subCi` at a
    goals-side index `i` (with `D.length ≤ i < (D ++ goals).length`),
    apply the walker `walkLiftedForallChain_eval_qf` to conclude `N ⊨
    subCi.toFormula` via path-by-path evaluation against ground
    `goals_g` entries.

    LINKAGE via `hProj` (subCi pinned to deterministic projection).

    PROOF STRATEGY. Each path through `subCi` corresponds to a witness
    chain that produces a ground substitution instance of
    `goals[i - D.length]`. By construction of
    `extractGroundGoalsFromCInstance_core`, this substituted clause IS a
    goals_g entry, so `hM` validates it (via the Horn-encoding
    membership). The walker then assembles per-path validations into the
    full quantifier-tree evaluation. -/
theorem ci_subtree_eval_at_goals_index {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (hAfalsumAtomic : FormulaN.isAtomic Afalsum = true)
    (D goals : List (FOHornClause L hNoEq))
    (hAllNe : D ++ goals ≠ [])
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (hSpec : spec.source = (hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals))
    (ci : LCS.Herbrand.SHGTheorem.CInstance spec.language)
    (hCiSrc : ci.source = LCS.Herbrand.SHGTheorem.SK spec)
    (hCiWF : LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci)
    (M : Structure L) (s : Assignment M)
    (hM : formulaEvalN M
      ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum
        ((extractGroundClausesFromCInstance_core (hNoEq := by all_goals exact hNoEq))
          Afalsum D goals spec ci ++
          (extractGroundGoalsFromCInstance_core (hNoEq := by all_goals exact hNoEq))
            Afalsum D goals spec ci)) s)
    (N : Structure spec.language)
    (hExp : LCS.Herbrand.SHGTheorem.Main.isExpansion L spec.n spec.skolemRank M N)
    (i : Nat) (hiLt : i < ((D ++ goals).length))
    (hiGoals : D.length ≤ i)
    (subCi : LCS.Herbrand.SHGTheorem.CInstance spec.language)
    (hProj : ciProjectAtClauseIndex
      (n := spec.n) (skolemRank := spec.skolemRank) ci i
      ((D ++ goals).length) = some subCi) :
    formulaEvalN N subCi.toFormula
      (fun x => (hExp.1 ▸ s x : N.carrier)) := by
-- BEGIN PROOF
  -- Step A: derive subCi.source = liftFormulaSkolem(univClos((D ++ goals)[i])).
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
  obtain ⟨hSubSrc, hSubWf⟩ :=
    (ciProjectAtClauseIndex_source_of_liftFormulaSkolem_hornClauses (hNoEq := by all_goals exact hNoEq))
      (D ++ goals) Afalsum i hiLt ci hCiWF hCiSrc' subCi hProj
  -- Step B: Identify the i-th clause as a goals-clause.
  have hGoalsLen : i - D.length < goals.length := by
    have hGoalsLenAppend : ((D ++ goals).length) = D.length + goals.length := by
      simp [List.length_append]
    omega
  have hGetEq : (D ++ goals).get ⟨i, hiLt⟩ = goals.get ⟨i - D.length, hGoalsLen⟩ := by
    rw [show (D ++ goals).get ⟨i, hiLt⟩ = (D ++ goals)[i]'hiLt from rfl,
        show goals.get ⟨i - D.length, hGoalsLen⟩ = goals[i - D.length]'hGoalsLen from rfl]
    exact List.getElem_append_right hiGoals
  rw [hGetEq] at hSubSrc
  -- Step C: Apply the walker, mirroring the D-side `ci_subtree_eval_at_D_index`.
  let c : FOHornClause L hNoEq := goals.get ⟨i - D.length, hGoalsLen⟩
  let body : FormulaN L := (clauseToFormula (hNoEq := by all_goals exact hNoEq)) Afalsum (c.toFOClause (hNoEq := by all_goals exact hNoEq))
  have hQFBody : LCS.FirstOrder.SemanticsN.isQuantifierFree body := by
    have hAfalsumQF : LCS.FirstOrder.SemanticsN.isQuantifierFree Afalsum :=
      LCS.Herbrand.SHGTheorem.isAtomic_isQuantifierFree Afalsum hAfalsumAtomic
    exact (clauseToFormula_isQF_atomic (hNoEq := by all_goals exact hNoEq)) Afalsum hAfalsumQF (c.toFOClause (hNoEq := by all_goals exact hNoEq))
  have hSubSrc' : subCi.source = LCS.Herbrand.SHGTheorem.liftFormulaSkolem
      (n := spec.n) (skolemRank := spec.skolemRank)
      (((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum c).foldr (fun v acc => FormulaN.all v acc) body) :=
    hSubSrc
  apply walkLiftedForallChain_eval_qf M s N hExp
    ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum c) ((hornClauseVarsList_nodup (hNoEq := by all_goals exact hNoEq)) Afalsum c) body hQFBody
    subCi hSubSrc' hSubWf
  -- Path-evaluation hypothesis: for every path through subCi, M validates body[σ].
  -- The substituted body equals `clauseToFormula(substAllInHornClause c σ).toFOClause`,
  -- which IS in `extractGroundGoalsFromCInstance_core` (per core's flatmap over
  -- `ciExtractAllSubstPaths(subCi)`). hM validates goals_g, hence M validates the
  -- substituted body's universal closure. Since the substituted clause is ground
  -- (path covers all FVs of c, see `multi_path_ground_on_clauseFV_goals`),
  -- `univClos = clauseToFormula(...)`, giving the desired evaluation.
  intro path hPathMem
  -- DEBT(pre-existing proof pending; chapter 9 proof closure)
  sorry

end LCS.SLD.FirstOrder
end

