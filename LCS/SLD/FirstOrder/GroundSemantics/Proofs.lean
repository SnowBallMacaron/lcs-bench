import LCS.SLD.FirstOrder.GroundSemantics

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

helper /-- Theorem 9.4.1 (required helper): `skolemFormAux` preserves
    `isConjChainN` at any scope/counter state — `skolemFormAux` on `.conj A
    B` recurses into each operand and rebuilds the `.conj`, so the
    top-level conj-chain structure is maintained. -/
theorem skolemFormAux_isConjChainN_preservation {L : Language}
    (S : LCS.Herbrand.SHGTheorem.SkolemSpec L) :
    ∀ (F : FormulaN S.language) (N : Nat) (scope : List Nat) (i : Nat),
      isConjChainN F N →
      isConjChainN
        (LCS.Herbrand.SHGTheorem.skolemFormAux S F scope i).1 N := by
-- BEGIN PROOF
  intro F N scope i hChain
  induction N generalizing F scope i with
  | zero => trivial
  | succ N' ihN =>
    cases N' with
    | zero => trivial
    | succ m =>
      simp only [isConjChainN] at hChain
      obtain ⟨A, B, hEq, hChainB⟩ := hChain
      subst hEq
      rw [LCS.Herbrand.SHGTheorem.skolemFormAux.eq_4]
      simp only [isConjChainN]
      refine ⟨(LCS.Herbrand.SHGTheorem.skolemFormAux S A scope i).1,
              (LCS.Herbrand.SHGTheorem.skolemFormAux S B scope
                (LCS.Herbrand.SHGTheorem.skolemFormAux S A scope i).2).1,
              ?_, ?_⟩
      · rfl
      · exact ihN B scope
          (LCS.Herbrand.SHGTheorem.skolemFormAux S A scope i).2 hChainB





helper /-- Theorem 9.4.1 (required helper): Given a WellFormed CInstance whose
    source is a conj-chain of length `N`, `ciProjectAtClauseIndex ci k N`
    returns `some` at any index `k < N`. Proved by strong induction on `N`,
    using `ci_connective_true_of_source_conj` to peel off one `.connective
    true` layer per recursion step, matching `ciProjectAtClauseIndex`'s
    own recursion. -/
theorem ci_project_some_of_conj_chain {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat} :
    ∀ (N : Nat)
      (ci : LCS.Herbrand.SHGTheorem.CInstance
        (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank))
      (_hCiWF : LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci)
      (_hChain : isConjChainN ci.source N)
      (k : Nat) (_hK : k < N),
    ∃ ciClause : LCS.Herbrand.SHGTheorem.CInstance
        (LCS.Herbrand.SHGTheorem.SkolemLanguage (L := L) n skolemRank),
      ciProjectAtClauseIndex (n := n) (skolemRank := skolemRank) ci k N = some ciClause := by
-- BEGIN PROOF
  intro N
  induction N with
  | zero => intros ci _ _ k hK; omega
  | succ N' ihN =>
    intro ci hWF hChain k hK
    cases N' with
    | zero =>
      have hk0 : k = 0 := by omega
      subst hk0
      refine ⟨ci, ?_⟩
      simp [ciProjectAtClauseIndex]
    | succ m =>
      simp only [isConjChainN] at hChain
      obtain ⟨A, B, hEq, hChainB⟩ := hChain
      obtain ⟨H, K, hCi, hHsrc, hKsrc, hHwf, hKwf⟩ :=
        ci_connective_true_of_source_conj ci A B hEq hWF
      subst hCi
      cases hk : k with
      | zero =>
        refine ⟨H, ?_⟩
        show ciProjectAtClauseIndex (n := n) (skolemRank := skolemRank)
          (LCS.Herbrand.SHGTheorem.CInstance.connective true A B H K) 0 (m + 2) = some H
        rfl
      | succ k' =>
        have hK' : k' < m + 1 := by omega
        have hKchain : isConjChainN K.source (m + 1) := hKsrc ▸ hChainB
        obtain ⟨ciClause, hcc⟩ := ihN K hKwf hKchain k' hK'
        refine ⟨ciClause, ?_⟩
        have hRec : ciProjectAtClauseIndex (n := n) (skolemRank := skolemRank)
          (LCS.Herbrand.SHGTheorem.CInstance.connective true A B H K) (k' + 1) (m + 2)
          = ciProjectAtClauseIndex (n := n) (skolemRank := skolemRank) K k' (m + 1) := by
          simp [ciProjectAtClauseIndex]
        rw [hRec]; exact hcc

helper /-- Theorem 9.4.1 (required helper): Under the full hypotheses of
    `extractGroundClauses_from_cinstance`, `ciProjectAtClauseIndex`
    returns `some _` at any `D`-index.

    CONTENT. When ci is WellFormed for `SK spec`, `spec.source =
    hornClauses_to_formulaN Afalsum (D ++ goals)`, `D ++ goals ≠ []`,
    and `i < D.length ≤ (D ++ goals).length`, the projection
    `ciProjectAtClauseIndex ci i (D ++ goals).length` cannot be
    `none`. The `none` branches of `ciProjectAtClauseIndex` correspond
    to (a) `totalClauses = 0` (ruled out by `hAllNe` + `i < D.length`),
    (b) `totalClauses = 1 ∧ k ≠ 0` (ruled out by `i < D.length ≤ 1`),
    or (c) `totalClauses ≥ 2` with a top-level `ci` that is not
    `connective true _ _ _ _` (ruled out by `WellFormed ci` +
    `ci.source = SK spec = .conj (SK _) (SK _)` forcing the constructor).

    PROOF STATUS. FULLY PROVED via the `isConjChainN` abstraction — the
    structural fact that `ci.source = .conj _ _` forces ci to be
    `.connective true _ _ _ _` is delegated to
    `ci_connective_true_of_source_conj`; preservation of the conj-chain
    shape through `hornClauses_to_formulaN`, `liftFormulaSkolem`, and
    `skolemFormAux` is delegated to `SK_isConjChainN_from_source`; and
    the resulting recursive projection is closed by
    `ci_project_some_of_conj_chain`. -/
theorem ciProjectAtClauseIndex_some_of_wellformed_horn {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (D goals : List (FOHornClause L hNoEq))
    (hAllNe : D ++ goals ≠ [])
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (hSpec : spec.source = (hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals))
    (ci : LCS.Herbrand.SHGTheorem.CInstance spec.language)
    (hCiSrc : ci.source = LCS.Herbrand.SHGTheorem.SK spec)
    (hCiWF : LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci)
    (i : Nat) (hiLt : i < D.length) :
    ∃ ciClause : LCS.Herbrand.SHGTheorem.CInstance spec.language,
      ciProjectAtClauseIndex
        (n := spec.n) (skolemRank := spec.skolemRank) ci i
        ((D ++ goals).length) = some ciClause := by
-- BEGIN PROOF
  have hDlen_le : D.length ≤ ((D ++ goals).length) := by
    rw [List.length_append]; exact Nat.le_add_right _ _
  have hi_lt_total : i < ((D ++ goals).length) :=
    Nat.lt_of_lt_of_le hiLt hDlen_le
  have hChain : isConjChainN ci.source ((D ++ goals).length) :=
    hCiSrc ▸ (SK_isConjChainN_from_source (hNoEq := by all_goals exact hNoEq)) spec (D ++ goals) Afalsum hSpec
  exact ci_project_some_of_conj_chain ((D ++ goals).length) ci hCiWF hChain i hi_lt_total

proof_of extractGroundClauses_from_cinstance := by
  -- BEGIN PROOF
    refine ⟨(extractGroundClausesFromCInstance_core (hNoEq := by all_goals exact hNoEq)) Afalsum D goals spec ci, rfl, ?_⟩
    intro c_g hc_g
    -- Unfold the multi-witness core construction. D_g is
    -- `(D.mapIdx (fun i c => ...)).flatten`, so a membership of `c_g ∈ D_g`
    -- factors through `List.mem_flatten` + `List.mem_mapIdx`.
    unfold extractGroundClausesFromCInstance_core at hc_g
    rw [List.mem_flatten] at hc_g
    obtain ⟨clauseOutputs, hOutputsMem, hcgInOutputs⟩ := hc_g
    rw [List.mem_mapIdx] at hOutputsMem
    obtain ⟨i, hiLt, hOutputsEq⟩ := hOutputsMem
    -- `c := D[i]` is at position `i` in `D`, so `c ∈ D`.
    have hcMem : D[i] ∈ D := List.getElem_mem hiLt
    refine ⟨D[i], hcMem, ?_⟩
    -- By `ciProjectAtClauseIndex_some_of_wellformed_horn`, the `none`
    -- branch is unreachable under the Horn + WellFormed assumptions, so
    -- `clauseOutputs` is `paths.map (fun entries => substAllInHornClause c σ_entries)`.
    obtain ⟨ciClause, hCiClauseOpt⟩ :=
      (ciProjectAtClauseIndex_some_of_wellformed_horn (hNoEq := by all_goals exact hNoEq))
        Afalsum D goals hAllNe spec hSpec ci hCiSrc hCiWF i hiLt
    -- Substitute the `some ciClause` branch in `hOutputsEq`.
    rw [hCiClauseOpt] at hOutputsEq
    subst hOutputsEq
    -- Now `c_g ∈ (paths.map ...)` gives a specific path `entries` with
    -- `c_g = substAllInHornClause D[i] (substFromList entries)`.
    rw [List.mem_map] at hcgInOutputs
    obtain ⟨entries, _hEntriesMem, hcgFromEntries⟩ := hcgInOutputs
    let σ : Nat → Term L :=
      substFromList (n := spec.n) (skolemRank := spec.skolemRank) entries
    refine ⟨σ, hcgFromEntries.symm, ?_⟩
    -- GROUNDNESS. The `entries` is SOME witness path from
    -- `ciExtractAllSubstPaths ciClause`. We need:
    --   ∀ y, ¬ clauseFV (substAllInHornClause D[i] σ).toFOClause y
    -- Delegate to `substAllInHornClause_ground_of_subst_ground_on_fv`,
    -- which reduces to proving σ is ground on FV(D[i]). The latter is a
    -- NEW sub-sorry: path-agnostic groundness via multi-witness paths.
    -- TRUTH: by the structural argument (WellFormed ci + foldrAll source
    -- shape), every free variable of D[i] is covered by every path of
    -- ciExtractAllSubstPaths ciClause.
    rw [← hcgFromEntries]
    exact (substAllInHornClause_ground_of_subst_ground_on_fv (hNoEq := by all_goals exact hNoEq)) D[i] σ
      ((multi_path_ground_on_clauseFV (hNoEq := by all_goals exact hNoEq))
        Afalsum hAfalsumAtomic D goals hAllNe spec hSpec ci hCiSrc hCiWF
        i hiLt ciClause hCiClauseOpt entries _hEntriesMem)


proof_of extractGroundGoals_from_cinstance := by
  -- BEGIN PROOF
    refine ⟨(extractGroundGoalsFromCInstance_core (hNoEq := by all_goals exact hNoEq)) Afalsum D goals spec ci, rfl, ?_⟩
    intro g_g hg_g
    unfold extractGroundGoalsFromCInstance_core at hg_g
    rw [List.mem_flatten] at hg_g
    obtain ⟨goalOutputs, hOutputsMem, hggInOutputs⟩ := hg_g
    rw [List.mem_mapIdx] at hOutputsMem
    obtain ⟨i, hiLt, hOutputsEq⟩ := hOutputsMem
    have hgMem : goals[i] ∈ goals := List.getElem_mem hiLt
    refine ⟨goals[i], hgMem, ?_⟩
    -- Project at absolute index D.length + i.
    have hAbs_lt_total : D.length + i < ((D ++ goals).length) := by
      rw [List.length_append]; omega
    have hChain : isConjChainN ci.source ((D ++ goals).length) :=
      hCiSrc ▸ (SK_isConjChainN_from_source (hNoEq := by all_goals exact hNoEq)) spec (D ++ goals) Afalsum hSpec
    obtain ⟨ciClause, hCiClauseOpt⟩ :=
      ci_project_some_of_conj_chain ((D ++ goals).length) ci hCiWF hChain
        (D.length + i) hAbs_lt_total
    rw [hCiClauseOpt] at hOutputsEq
    subst hOutputsEq
    rw [List.mem_map] at hggInOutputs
    obtain ⟨entries, _hEntriesMem, hggFromEntries⟩ := hggInOutputs
    let τ : Nat → Term L :=
      substFromList (n := spec.n) (skolemRank := spec.skolemRank) entries
    refine ⟨τ, hggFromEntries.symm, ?_⟩
    rw [← hggFromEntries]
    exact (substAllInHornClause_ground_of_subst_ground_on_fv (hNoEq := by all_goals exact hNoEq)) goals[i] τ
      ((multi_path_ground_on_clauseFV_goals (hNoEq := by all_goals exact hNoEq))
        Afalsum hAfalsumAtomic D goals hAllNe spec hSpec ci hCiSrc hCiWF
        i hiLt ciClause hCiClauseOpt entries _hEntriesMem)












end LCS.SLD.FirstOrder

end
