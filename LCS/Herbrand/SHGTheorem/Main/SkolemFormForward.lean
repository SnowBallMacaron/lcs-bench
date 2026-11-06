import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.SHGTheorem.Herbrand
import LCS.Herbrand.SHGTheorem.Main.Expansions

section
namespace LCS.Herbrand.SHGTheorem.Main
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.SHGTheorem.Herbrand
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.CutElim.Hauptsatz
open LCS.FirstOrder.SemanticsN.Substitution

-- ===================================================================
-- Lemma 7.6.3 (exact-traversal semantic invariant)
-- ===================================================================

/-- A successful, allocation-aligned exact traversal reflects truth.
The scope side condition is the capture invariant: variables used as
arguments of the next exact Skolem term are not rebound in the current
formula. -/
private theorem skolemFormExactAux_forward_semantics {L : Language}
    (S : SkolemSpec L) (N : Structure S.language) :
    ∀ (m : Nat) (A : FormulaN S.language) (scope : List Nat)
      (indices : List (Fin S.n)) (B : FormulaN S.language) (used : Nat),
      formulaQuantCount A = m →
      FormulaN.isNNF A →
      indices.length = skolemDescriptorCount A →
      indices.map S.skolemScope = existentialScopesAux A scope →
      skolemFormExactAux S A scope indices = some (B, used) →
      distinctQuantifierBindings A →
      (∀ y ∈ scope, y ∉ formulaBVN A) →
      ∀ s : Assignment N,
        formulaEvalN N B s → formulaEvalN N A s := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro A scope indices Out used hCount hNNF hLength hScopes hRun
      hDistinct hScopeFresh s hOut
    match A, hCount, hNNF, hLength, hDistinct with
    | .predN P ts, _, _, hLength, _ =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.predN P ts) scope [] =
            some (.predN P ts, 0) := by
        simp [skolemFormExactAux]
      have hFormula :=
        skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact hOut
    | .eq_ h t₁ t₂, _, _, hLength, _ =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.eq_ h t₁ t₂) scope [] =
            some (.eq_ h t₁ t₂, 0) := by
        simp [skolemFormExactAux]
      have hFormula :=
        skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact hOut
    | .neg C, _, hNNF, hLength, _ =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.neg C) scope [] =
            some (.neg C, 0) := by
        simp [skolemFormExactAux]
      have hFormula :=
        skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact hOut
    | .conj C D, hCount, hNNF, hLength, hDistinct =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qC : formulaQuantCount C < m := by omega
      have qD : formulaQuantCount D < m := by omega
      have hCLe : skolemDescriptorCount C ≤ indices.length := by
        rw [hLength]
        exact Nat.le_add_right _ _
      have hLeftLength :
          (indices.take (skolemDescriptorCount C)).length =
            skolemDescriptorCount C :=
        List.length_take_of_le hCLe
      have hRightLength :
          (indices.drop (skolemDescriptorCount C)).length =
            skolemDescriptorCount D := by
        rw [List.length_drop, hLength]
        simp [skolemDescriptorCount]
      have hLeftScopes :
          (indices.take (skolemDescriptorCount C)).map S.skolemScope =
            existentialScopesAux C scope := by
        calc
          _ = (indices.map S.skolemScope).take
                (skolemDescriptorCount C) := List.map_take
          _ = (existentialScopesAux C scope ++
                existentialScopesAux D scope).take
                (skolemDescriptorCount C) := by
              rw [hScopes]
              rfl
          _ = existentialScopesAux C scope := by
              rw [← existentialScopesAux_length C scope]
              exact List.take_left
      have hRightScopes :
          (indices.drop (skolemDescriptorCount C)).map S.skolemScope =
            existentialScopesAux D scope := by
        calc
          _ = (indices.map S.skolemScope).drop
                (skolemDescriptorCount C) := List.map_drop
          _ = (existentialScopesAux C scope ++
                existentialScopesAux D scope).drop
                (skolemDescriptorCount C) := by
              rw [hScopes]
              rfl
          _ = existentialScopesAux D scope := by
              rw [← existentialScopesAux_length C scope]
              exact List.drop_left
      obtain ⟨C', hC'⟩ :=
        skolemFormExactAux_result S _ C scope
          (indices.take (skolemDescriptorCount C)) rfl hLeftLength
      obtain ⟨D', hD'⟩ :=
        skolemFormExactAux_result S _ D scope
          (indices.drop (skolemDescriptorCount C)) rfl hRightLength
      have hFreshC : ∀ y ∈ scope, y ∉ formulaBVN C := by
        intro y hyScope hyBound
        exact hScopeFresh y hyScope (Or.inl hyBound)
      have hFreshD : ∀ y ∈ scope, y ∉ formulaBVN D := by
        intro y hyScope hyBound
        exact hScopeFresh y hyScope (Or.inr hyBound)
      have hSemC :=
        ih _ qC C scope (indices.take (skolemDescriptorCount C))
          C' _ rfl hNNF.1 hLeftLength hLeftScopes hC'
          hDistinct.1 hFreshC
      have hSemD :=
        ih _ qD D scope (indices.drop (skolemDescriptorCount C))
          D' _ rfl hNNF.2 hRightLength hRightScopes hD'
          hDistinct.2.1 hFreshD
      have hCanonical :
          skolemFormExactAux S (.conj C D) scope indices =
            some (.conj C' D',
              skolemDescriptorCount C + skolemDescriptorCount D) := by
        simp [skolemFormExactAux, hC', hD']
      have hFormula :=
        skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact ⟨hSemC s hOut.1, hSemD s hOut.2⟩
    | .disj C D, hCount, hNNF, hLength, hDistinct =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qC : formulaQuantCount C < m := by omega
      have qD : formulaQuantCount D < m := by omega
      have hCLe : skolemDescriptorCount C ≤ indices.length := by
        rw [hLength]
        exact Nat.le_add_right _ _
      have hLeftLength :
          (indices.take (skolemDescriptorCount C)).length =
            skolemDescriptorCount C :=
        List.length_take_of_le hCLe
      have hRightLength :
          (indices.drop (skolemDescriptorCount C)).length =
            skolemDescriptorCount D := by
        rw [List.length_drop, hLength]
        simp [skolemDescriptorCount]
      have hLeftScopes :
          (indices.take (skolemDescriptorCount C)).map S.skolemScope =
            existentialScopesAux C scope := by
        calc
          _ = (indices.map S.skolemScope).take
                (skolemDescriptorCount C) := List.map_take
          _ = (existentialScopesAux C scope ++
                existentialScopesAux D scope).take
                (skolemDescriptorCount C) := by
              rw [hScopes]
              rfl
          _ = existentialScopesAux C scope := by
              rw [← existentialScopesAux_length C scope]
              exact List.take_left
      have hRightScopes :
          (indices.drop (skolemDescriptorCount C)).map S.skolemScope =
            existentialScopesAux D scope := by
        calc
          _ = (indices.map S.skolemScope).drop
                (skolemDescriptorCount C) := List.map_drop
          _ = (existentialScopesAux C scope ++
                existentialScopesAux D scope).drop
                (skolemDescriptorCount C) := by
              rw [hScopes]
              rfl
          _ = existentialScopesAux D scope := by
              rw [← existentialScopesAux_length C scope]
              exact List.drop_left
      obtain ⟨C', hC'⟩ :=
        skolemFormExactAux_result S _ C scope
          (indices.take (skolemDescriptorCount C)) rfl hLeftLength
      obtain ⟨D', hD'⟩ :=
        skolemFormExactAux_result S _ D scope
          (indices.drop (skolemDescriptorCount C)) rfl hRightLength
      have hFreshC : ∀ y ∈ scope, y ∉ formulaBVN C := by
        intro y hyScope hyBound
        exact hScopeFresh y hyScope (Or.inl hyBound)
      have hFreshD : ∀ y ∈ scope, y ∉ formulaBVN D := by
        intro y hyScope hyBound
        exact hScopeFresh y hyScope (Or.inr hyBound)
      have hSemC :=
        ih _ qC C scope (indices.take (skolemDescriptorCount C))
          C' _ rfl hNNF.1 hLeftLength hLeftScopes hC'
          hDistinct.1 hFreshC
      have hSemD :=
        ih _ qD D scope (indices.drop (skolemDescriptorCount C))
          D' _ rfl hNNF.2 hRightLength hRightScopes hD'
          hDistinct.2.1 hFreshD
      have hCanonical :
          skolemFormExactAux S (.disj C D) scope indices =
            some (.disj C' D',
              skolemDescriptorCount C + skolemDescriptorCount D) := by
        simp [skolemFormExactAux, hC', hD']
      have hFormula :=
        skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      rcases hOut with hOut | hOut
      · exact Or.inl (hSemC s hOut)
      · exact Or.inr (hSemD s hOut)
    | .impl _ _, _, hNNF, _, _ => exact hNNF.elim
    | .all x C, hCount, hNNF, hLength, hDistinct =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qC : formulaQuantCount C < m := by omega
      have hBodyLength :
          indices.length = skolemDescriptorCount C := by
        simpa [skolemDescriptorCount] using hLength
      have hBodyScopes :
          indices.map S.skolemScope =
            existentialScopesAux C (scope ++ [x]) := by
        simpa [existentialScopesAux] using hScopes
      obtain ⟨C', hC'⟩ :=
        skolemFormExactAux_result S _ C (scope ++ [x])
          indices rfl hBodyLength
      have hFreshC :
          ∀ y ∈ scope ++ [x], y ∉ formulaBVN C := by
        intro y hyScope hyBound
        rcases List.mem_append.mp hyScope with hyScope | hyLast
        · exact hScopeFresh y hyScope (Or.inl hyBound)
        · have hyx : y = x := List.mem_singleton.mp hyLast
          subst y
          exact hDistinct.2 hyBound
      have hSemC :=
        ih _ qC C (scope ++ [x]) indices C' _
          rfl hNNF hBodyLength hBodyScopes hC'
          hDistinct.1 hFreshC
      have hCanonical :
          skolemFormExactAux S (.all x C) scope indices =
            some (.all x C', skolemDescriptorCount C) := by
        simp [skolemFormExactAux, hC']
      have hFormula :=
        skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      intro a
      exact hSemC (assignUpdate s x a) (hOut a)
    | .ex x C, hCount, hNNF, hLength, hDistinct =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      cases indices with
      | nil =>
        simp [skolemDescriptorCount] at hLength
        omega
      | cons i rest =>
        have hRestLength :
            rest.length = skolemDescriptorCount C := by
          simp [skolemDescriptorCount] at hLength
          omega
        have hScopesAt := hScopes
        simp only [List.map_cons, existentialScopesAux] at hScopesAt
        have hHeadScope : S.skolemScope i = scope :=
          (List.cons.inj hScopesAt).1
        have hRestScopes :
            rest.map S.skolemScope = existentialScopesAux C scope :=
          (List.cons.inj hScopesAt).2
        let CSub := formulaSubstN C (exactSkolemTerm S i) x
        have qCSub : formulaQuantCount CSub < m := by
          simp only [CSub]
          rw [formulaSubst_quantCount]
          omega
        have hNNFSub : FormulaN.isNNF CSub :=
          formulaSubstN_isNNF C (exactSkolemTerm S i) x hNNF
        have hSubLength :
            rest.length = skolemDescriptorCount CSub := by
          rw [formulaSubstN_descriptorCount]
          exact hRestLength
        have hSubScopes :
            rest.map S.skolemScope =
              existentialScopesAux CSub scope := by
          rw [existentialScopesAux_formulaSubstN]
          exact hRestScopes
        obtain ⟨C', hC'⟩ :=
          skolemFormExactAux_result S _ CSub scope rest rfl hSubLength
        have hDistinctSub : distinctQuantifierBindings CSub :=
          distinctQuantifierBindings_of_formulaSubstN
            C (exactSkolemTerm S i) x hDistinct.1
        have hFreshSub :
            ∀ y ∈ scope, y ∉ formulaBVN CSub := by
          intro y hyScope hyBound
          apply hScopeFresh y hyScope
          apply Or.inl
          have hyBoundC : formulaBVN C y := by
            change formulaBVN CSub y at hyBound
            simpa only [CSub,
              LCS.CutElim.Interpolation.formulaBV_formulaSubst] using hyBound
          exact hyBoundC
        have hFree : isFreeForN (exactSkolemTerm S i) x C := by
          apply LCS.FirstOrder.Gentzen.Hintikka.isFreeForN_of_bv_disjoint
          intro y hyTerm hyBound
          apply hScopeFresh y
          · rw [← hHeadScope]
            exact exactSkolemTerm_fv S i y hyTerm
          · exact Or.inl hyBound
        have hSemC :=
          ih _ qCSub CSub scope rest C' _
            rfl hNNFSub hSubLength hSubScopes hC'
            hDistinctSub hFreshSub
        have hCanonical :
            skolemFormExactAux S (.ex x C) scope (i :: rest) =
              some (C', skolemDescriptorCount CSub + 1) := by
          simp [skolemFormExactAux, skolemSubst, CSub, hC']
        have hFormula :=
          skolemFormExactAux_formula_unique hCanonical hRun
        subst Out
        have hEvalSub : formulaEvalN N CSub s := hSemC s hOut
        refine ⟨termEval N s (exactSkolemTerm S i), ?_⟩
        exact
          (formulaSubstEvalDirectN s C (exactSkolemTerm S i) x hFree).mp
            hEvalSub

-- ===================================================================
-- Lemma 7.6.3 (forward generalized): skolemForm_forward_genN
-- ===================================================================

/-- Lemma 7.6.3 forward (FormulaN version): if a Skolem-extended
structure N satisfies the Skolem form `SK spec`, then (transported back
via `liftFormulaSkolem_eval_iff`) the base structure satisfies
`spec.source`. The Skolem-form argument is fully packaged as
`spec : SkolemSpec L` (Def 7.6.2). -/
theorem skolemForm_forward_genN {L : Language}
    (spec : SkolemSpec L)
    (N : Structure spec.language) (_sN : Assignment N)
    (_h : formulaEvalN N (SK spec) _sN)
    (M : Structure L) (s : Assignment M)
    (_hExp : isExpansion L spec.n spec.skolemRank M N) :
    formulaEvalN M spec.source s := by
-- BEGIN PROOF
  unfold SkolemSpec.language at N
  let A :=
    liftFormulaSkolem (skolemRank := spec.skolemRank) spec.source
  have hNNF : FormulaN.isNNF A :=
    liftFormulaSkolem_isNNF spec.source spec.hNNF
  have hDistinct : distinctQuantifierBindings A := by
    simpa [A] using
      liftFormulaSkolem_distinctQuantifierBindings
        spec.source spec.hRect.2
  have hScopeFresh : ∀ y ∈ ([] : List Nat), y ∉ formulaBVN A := by
    intro y hy
    simp at hy
  have hRun :
      skolemFormExactAux spec A [] spec.indices =
        some (SK spec, spec.n) := by
    simpa [A] using skolemFormExactAux_top_formula_result spec
  have hLiftAtSN : formulaEvalN N A _sN :=
    skolemFormExactAux_forward_semantics spec N _ A [] spec.indices
      (SK spec) spec.n rfl hNNF
      spec.indices_length_eq_lifted_descriptorCount
      spec.indices_scopes_lifted hRun hDistinct hScopeFresh _sN _h
  have hClosedLift : formulaFVN A = (∅ : Set Nat) := by
    rw [show formulaFVN A = formulaFVN spec.source by
      simpa [A] using liftFormulaSkolem_formulaFVN spec.source]
    exact spec.hSentence
  have hLiftAtTransport :
      formulaEvalN N A
        (fun x => (_hExp.choose ▸ s x : N.carrier)) :=
    (coincidenceLemmaN N A _sN
      (fun x => (_hExp.choose ▸ s x : N.carrier))
      (fun y hy => by
        rw [hClosedLift] at hy
        exact hy.elim)).mp hLiftAtSN
  exact
    (liftFormulaSkolem_eval_iff M N _hExp s spec.source).mpr
      (by simpa [A] using hLiftAtTransport)

end LCS.Herbrand.SHGTheorem.Main
end
