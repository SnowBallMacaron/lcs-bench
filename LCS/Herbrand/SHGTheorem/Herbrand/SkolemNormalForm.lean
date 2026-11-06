import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.SkolemFormShape

section
namespace LCS.Herbrand.SHGTheorem.Herbrand
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.Equality
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.Herbrand.PrenexForm
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae

/-- Every free variable of an exact Skolem term is one of the variables
in that allocation's ordered universal scope. -/
theorem exactSkolemTerm_fv {L : Language} (S : SkolemSpec L)
    (i : Fin S.n) :
    ∀ y ∈ termFV (exactSkolemTerm S i), y ∈ S.skolemScope i := by
  intro y hy
  unfold exactSkolemTerm at hy
  split at hy
  · exact hy.elim
  · change ∃ k, _ at hy
    obtain ⟨k, hk⟩ := hy
    change y = (S.skolemScope i).get k at hk
    rw [hk]
    exact List.get_mem _ _

/-- On an allocation-aligned run, every free variable of the exact
traversal's output belongs to the current universal scope, provided
the same is true of the input. The scope-alignment hypothesis is what
connects each consumed index to its exact descriptor occurrence. -/
theorem skolemFormExactAux_fv_bound {L : Language}
    (S : SkolemSpec L) :
    ∀ (m : Nat) (A : FormulaN S.language) (scope : List Nat)
      (indices : List (Fin S.n)) (B : FormulaN S.language) (used : Nat),
      formulaQuantCount A = m →
      FormulaN.isNNF A →
      indices.length = skolemDescriptorCount A →
      indices.map S.skolemScope = existentialScopesAux A scope →
      skolemFormExactAux S A scope indices = some (B, used) →
      (∀ y ∈ formulaFVN A, y ∈ scope) →
      ∀ y ∈ formulaFVN B, y ∈ scope := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro A scope indices Out used hCount hNNF hLength hScopes hRun hFV
    match A, hCount, hNNF, hLength with
    | .predN P ts, _, _, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.predN P ts) scope [] =
            some (.predN P ts, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact hFV
    | .eq_ h t₁ t₂, _, _, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.eq_ h t₁ t₂) scope [] =
            some (.eq_ h t₁ t₂, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact hFV
    | .neg C, _, hNNF, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.neg C) scope [] =
            some (.neg C, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact hFV
    | .conj C D, hCount, hNNF, hLength =>
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
      have hFVC : ∀ y ∈ formulaFVN C, y ∈ scope := by
        intro y hy
        exact hFV y (Or.inl hy)
      have hFVD : ∀ y ∈ formulaFVN D, y ∈ scope := by
        intro y hy
        exact hFV y (Or.inr hy)
      have hPropC :=
        ih _ qC C scope (indices.take (skolemDescriptorCount C))
          C' _ rfl hNNF.1 hLeftLength hLeftScopes hC' hFVC
      have hPropD :=
        ih _ qD D scope (indices.drop (skolemDescriptorCount C))
          D' _ rfl hNNF.2 hRightLength hRightScopes hD' hFVD
      have hCanonical :
          skolemFormExactAux S (.conj C D) scope indices =
            some (.conj C' D',
              skolemDescriptorCount C + skolemDescriptorCount D) := by
        simp [skolemFormExactAux, hC', hD']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      intro y hy
      rcases hy with hy | hy
      · exact hPropC y hy
      · exact hPropD y hy
    | .disj C D, hCount, hNNF, hLength =>
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
      have hFVC : ∀ y ∈ formulaFVN C, y ∈ scope := by
        intro y hy
        exact hFV y (Or.inl hy)
      have hFVD : ∀ y ∈ formulaFVN D, y ∈ scope := by
        intro y hy
        exact hFV y (Or.inr hy)
      have hPropC :=
        ih _ qC C scope (indices.take (skolemDescriptorCount C))
          C' _ rfl hNNF.1 hLeftLength hLeftScopes hC' hFVC
      have hPropD :=
        ih _ qD D scope (indices.drop (skolemDescriptorCount C))
          D' _ rfl hNNF.2 hRightLength hRightScopes hD' hFVD
      have hCanonical :
          skolemFormExactAux S (.disj C D) scope indices =
            some (.disj C' D',
              skolemDescriptorCount C + skolemDescriptorCount D) := by
        simp [skolemFormExactAux, hC', hD']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      intro y hy
      rcases hy with hy | hy
      · exact hPropC y hy
      · exact hPropD y hy
    | .impl _ _, _, hNNF, _ => exact hNNF.elim
    | .all x C, hCount, hNNF, hLength =>
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
      have hFVC : ∀ y ∈ formulaFVN C, y ∈ scope ++ [x] := by
        intro y hy
        by_cases hyx : y = x
        · subst y
          simp
        · apply List.mem_append.mpr
          apply Or.inl
          apply hFV y
          exact ⟨hy, fun hxy => hyx hxy⟩
      have hPropC :=
        ih _ qC C (scope ++ [x]) indices C' _
          rfl hNNF hBodyLength hBodyScopes hC' hFVC
      have hCanonical :
          skolemFormExactAux S (.all x C) scope indices =
            some (.all x C', skolemDescriptorCount C) := by
        simp [skolemFormExactAux, hC']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      intro y hy
      obtain ⟨hyC, hyNe⟩ := hy
      rcases List.mem_append.mp (hPropC y hyC) with hyScope | hyLast
      · exact hyScope
      · have hyEq : y = x := List.mem_singleton.mp hyLast
        exact absurd hyEq hyNe
    | .ex x C, hCount, hNNF, hLength =>
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
          isNNF_formulaSubstN C _ _ hNNF
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
        have hFVSub : ∀ y ∈ formulaFVN CSub, y ∈ scope := by
          intro y hy
          rcases LCS.FirstOrder.Gentzen.Hintikka.formulaFVN_formulaSubstN
              C (exactSkolemTerm S i) x y hy with
            ⟨hyC, hyNe⟩ | hyTerm
          · exact hFV y ⟨hyC, hyNe⟩
          · rw [← hHeadScope]
            exact exactSkolemTerm_fv S i y hyTerm
        have hPropC :=
          ih _ qCSub CSub scope rest C' _
            rfl hNNFSub hSubLength hSubScopes hC' hFVSub
        have hCanonical :
            skolemFormExactAux S (.ex x C) scope (i :: rest) =
              some (C', skolemDescriptorCount CSub + 1) := by
          simp [skolemFormExactAux, skolemSubst, CSub, hC']
        have hOut := skolemFormExactAux_formula_unique hCanonical hRun
        subst Out
        exact hPropC

/-- Exact Skolemization never introduces a bound variable. Every
bound variable in a successful output was already bound in the input. -/
theorem skolemFormExactAux_bv_bound {L : Language}
    (S : SkolemSpec L) :
    ∀ (m : Nat) (A : FormulaN S.language) (scope : List Nat)
      (indices : List (Fin S.n)) (B : FormulaN S.language) (used : Nat),
      formulaQuantCount A = m →
      FormulaN.isNNF A →
      indices.length = skolemDescriptorCount A →
      skolemFormExactAux S A scope indices = some (B, used) →
      ∀ y ∈ formulaBVN B, y ∈ formulaBVN A := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro A scope indices Out used hCount hNNF hLength hRun
    match A, hCount, hNNF, hLength with
    | .predN P ts, _, _, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.predN P ts) scope [] =
            some (.predN P ts, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact fun _ hy => hy
    | .eq_ h t₁ t₂, _, _, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.eq_ h t₁ t₂) scope [] =
            some (.eq_ h t₁ t₂, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact fun _ hy => hy
    | .neg C, _, hNNF, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.neg C) scope [] =
            some (.neg C, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact fun _ hy => hy
    | .conj C D, hCount, hNNF, hLength =>
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
      obtain ⟨C', hC'⟩ :=
        skolemFormExactAux_result S _ C scope
          (indices.take (skolemDescriptorCount C)) rfl hLeftLength
      obtain ⟨D', hD'⟩ :=
        skolemFormExactAux_result S _ D scope
          (indices.drop (skolemDescriptorCount C)) rfl hRightLength
      have hPropC :=
        ih _ qC C scope (indices.take (skolemDescriptorCount C))
          C' _ rfl hNNF.1 hLeftLength hC'
      have hPropD :=
        ih _ qD D scope (indices.drop (skolemDescriptorCount C))
          D' _ rfl hNNF.2 hRightLength hD'
      have hCanonical :
          skolemFormExactAux S (.conj C D) scope indices =
            some (.conj C' D',
              skolemDescriptorCount C + skolemDescriptorCount D) := by
        simp [skolemFormExactAux, hC', hD']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      intro y hy
      rcases hy with hy | hy
      · exact Or.inl (hPropC y hy)
      · exact Or.inr (hPropD y hy)
    | .disj C D, hCount, hNNF, hLength =>
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
      obtain ⟨C', hC'⟩ :=
        skolemFormExactAux_result S _ C scope
          (indices.take (skolemDescriptorCount C)) rfl hLeftLength
      obtain ⟨D', hD'⟩ :=
        skolemFormExactAux_result S _ D scope
          (indices.drop (skolemDescriptorCount C)) rfl hRightLength
      have hPropC :=
        ih _ qC C scope (indices.take (skolemDescriptorCount C))
          C' _ rfl hNNF.1 hLeftLength hC'
      have hPropD :=
        ih _ qD D scope (indices.drop (skolemDescriptorCount C))
          D' _ rfl hNNF.2 hRightLength hD'
      have hCanonical :
          skolemFormExactAux S (.disj C D) scope indices =
            some (.disj C' D',
              skolemDescriptorCount C + skolemDescriptorCount D) := by
        simp [skolemFormExactAux, hC', hD']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      intro y hy
      rcases hy with hy | hy
      · exact Or.inl (hPropC y hy)
      · exact Or.inr (hPropD y hy)
    | .impl _ _, _, hNNF, _ => exact hNNF.elim
    | .all x C, hCount, hNNF, hLength =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qC : formulaQuantCount C < m := by omega
      have hBodyLength :
          indices.length = skolemDescriptorCount C := by
        simpa [skolemDescriptorCount] using hLength
      obtain ⟨C', hC'⟩ :=
        skolemFormExactAux_result S _ C (scope ++ [x])
          indices rfl hBodyLength
      have hPropC :=
        ih _ qC C (scope ++ [x]) indices C' _
          rfl hNNF hBodyLength hC'
      have hCanonical :
          skolemFormExactAux S (.all x C) scope indices =
            some (.all x C', skolemDescriptorCount C) := by
        simp [skolemFormExactAux, hC']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      intro y hy
      rcases hy with hy | hy
      · exact Or.inl (hPropC y hy)
      · exact Or.inr hy
    | .ex x C, hCount, hNNF, hLength =>
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
        let CSub := formulaSubstN C (exactSkolemTerm S i) x
        have qCSub : formulaQuantCount CSub < m := by
          simp only [CSub]
          rw [formulaSubst_quantCount]
          omega
        have hNNFSub : FormulaN.isNNF CSub :=
          isNNF_formulaSubstN C _ _ hNNF
        have hSubLength :
            rest.length = skolemDescriptorCount CSub := by
          rw [formulaSubstN_descriptorCount]
          exact hRestLength
        obtain ⟨C', hC'⟩ :=
          skolemFormExactAux_result S _ CSub scope rest rfl hSubLength
        have hPropC :=
          ih _ qCSub CSub scope rest C' _
            rfl hNNFSub hSubLength hC'
        have hCanonical :
            skolemFormExactAux S (.ex x C) scope (i :: rest) =
              some (C', skolemDescriptorCount CSub + 1) := by
          simp [skolemFormExactAux, skolemSubst, CSub, hC']
        have hOut := skolemFormExactAux_formula_unique hCanonical hRun
        subst Out
        intro y hy
        apply Or.inl
        rw [← LCS.CutElim.Interpolation.formulaBV_formulaSubst
          C (exactSkolemTerm S i) x]
        exact hPropC y hy

/-- Helper: lifting a term into the Skolem-extended language preserves
its free-variable set. The lift embeds constant and function symbols
and leaves variables unchanged. -/
theorem liftTermSkolem_termFV {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat} (t : Term L) :
    termFV (liftTermSkolem (skolemRank := skolemRank) t) = termFV t := by
-- BEGIN PROOF
  induction t with
  | var _ => rfl
  | const _ => rfl
  | func f ts ih =>
    simp only [liftTermSkolem, termFV]
    ext y
    show (∃ j, termFV (liftTermSkolem (ts j)) y) ↔ (∃ j, termFV (ts j) y)
    exact ⟨fun ⟨j, hj⟩ => ⟨j, (ih j) ▸ hj⟩,
           fun ⟨j, hj⟩ => ⟨j, (ih j).symm ▸ hj⟩⟩

/-- Helper: lifting a formula into the Skolem-extended language preserves
its free-variable set. The lift embeds constant and function symbols
at the term level; quantifier/propositional structure is
untouched, and term-level free variables propagate unchanged via
`liftTermSkolem_termFV`. -/
theorem liftFormulaSkolem_formulaFVN {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat} (A : FormulaN L) :
    formulaFVN (liftFormulaSkolem (skolemRank := skolemRank) A) = formulaFVN A := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    simp only [liftFormulaSkolem, formulaFVN]
    ext y
    show (∃ j, termFV (liftTermSkolem (ts j)) y) ↔ (∃ j, termFV (ts j) y)
    exact ⟨fun ⟨j, hj⟩ => ⟨j, (liftTermSkolem_termFV (ts j)) ▸ hj⟩,
           fun ⟨j, hj⟩ => ⟨j, (liftTermSkolem_termFV (ts j)).symm ▸ hj⟩⟩
  | eq_ _ t1 t2 =>
    simp only [liftFormulaSkolem, formulaFVN,
      liftTermSkolem_termFV]
  | neg _ ih => simp only [liftFormulaSkolem, formulaFVN, ih]
  | conj _ _ ihA ihB => simp only [liftFormulaSkolem, formulaFVN, ihA, ihB]
  | disj _ _ ihA ihB => simp only [liftFormulaSkolem, formulaFVN, ihA, ihB]
  | impl _ _ ihA ihB => simp only [liftFormulaSkolem, formulaFVN, ihA, ihB]
  | all _ _ ih => simp only [liftFormulaSkolem, formulaFVN, ih]
  | ex _ _ ih => simp only [liftFormulaSkolem, formulaFVN, ih]

/-- Helper: lifting a formula into the Skolem-extended language preserves
its bound-variable set. The lift does not add/remove quantifiers, and
BV is defined purely in terms of `.all`/`.ex` binders. -/
theorem liftFormulaSkolem_formulaBVN {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat} (A : FormulaN L) :
    formulaBVN (liftFormulaSkolem (skolemRank := skolemRank) A) = formulaBVN A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg _ ih => simp only [liftFormulaSkolem, formulaBVN, ih]
  | conj _ _ ihA ihB => simp only [liftFormulaSkolem, formulaBVN, ihA, ihB]
  | disj _ _ ihA ihB => simp only [liftFormulaSkolem, formulaBVN, ihA, ihB]
  | impl _ _ ihA ihB => simp only [liftFormulaSkolem, formulaBVN, ihA, ihB]
  | all _ _ ih => simp only [liftFormulaSkolem, formulaBVN, ih]
  | ex _ _ ih => simp only [liftFormulaSkolem, formulaBVN, ih]

-- retained: used by LCS.Herbrand.SHGTheorem.Main.SkolemEquisatisfiability, LCS.Herbrand.SHGTheorem.Main.SkolemSemanticsBase
/-- Helper: lifting preserves `distinctQuantifierBindings`. Structural
induction: the lift does not change formula-level structure (quantifiers,
connectives), and BV is preserved by `liftFormulaSkolem_formulaBVN`. -/
theorem liftFormulaSkolem_distinctQuantifierBindings {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat} (A : FormulaN L)
    (h : LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings A) :
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings
      (liftFormulaSkolem (skolemRank := skolemRank) A) := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => exact trivial
  | eq_ _ _ _ => exact trivial
  | neg _ ih =>
    simp only [liftFormulaSkolem,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings] at *
    exact ih h
  | conj _ _ ihA ihB =>
    simp only [liftFormulaSkolem,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
      liftFormulaSkolem_formulaBVN] at *
    exact ⟨ihA h.1, ihB h.2.1, h.2.2⟩
  | disj _ _ ihA ihB =>
    simp only [liftFormulaSkolem,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
      liftFormulaSkolem_formulaBVN] at *
    exact ⟨ihA h.1, ihB h.2.1, h.2.2⟩
  | impl _ _ ihA ihB =>
    simp only [liftFormulaSkolem,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
      liftFormulaSkolem_formulaBVN] at *
    exact ⟨ihA h.1, ihB h.2.1, h.2.2⟩
  | all _ _ ih =>
    simp only [liftFormulaSkolem,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
      liftFormulaSkolem_formulaBVN] at *
    exact ⟨ih h.1, h.2⟩
  | ex _ _ ih =>
    simp only [liftFormulaSkolem,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
      liftFormulaSkolem_formulaBVN] at *
    exact ⟨ih h.1, h.2⟩

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.Herbrand.SHGTheorem.Main.SHG, LCS.Herbrand.SHGTheorem.Main.SkolemEquisatisfiability, LCS.Herbrand.SHGTheorem.Main.SkolemSemanticsBase
/-- Substitution preserves `distinctQuantifierBindings`. Substitution
rewrites terms inside the formula but leaves the quantifier tree
structure (and thus BV) intact. -/
theorem distinctQuantifierBindings_of_formulaSubstN {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat)
    (h : LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings A) :
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings
      (formulaSubstN A t x) := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => exact trivial
  | eq_ _ _ _ => exact trivial
  | neg _ ih =>
    simp only [formulaSubstN,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings]
    exact ih h
  | conj B C ihB ihC =>
    simp only [formulaSubstN,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
      LCS.CutElim.Interpolation.formulaBV_formulaSubst] at *
    exact ⟨ihB h.1, ihC h.2.1, h.2.2⟩
  | disj B C ihB ihC =>
    simp only [formulaSubstN,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
      LCS.CutElim.Interpolation.formulaBV_formulaSubst] at *
    exact ⟨ihB h.1, ihC h.2.1, h.2.2⟩
  | impl B C ihB ihC =>
    simp only [formulaSubstN,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
      LCS.CutElim.Interpolation.formulaBV_formulaSubst] at *
    exact ⟨ihB h.1, ihC h.2.1, h.2.2⟩
  | all y B ih =>
    simp only [formulaSubstN]
    split
    · simp only [LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
        LCS.CutElim.Interpolation.formulaBV_formulaSubst] at *
      exact ⟨ih h.1, h.2⟩
    · exact h
  | ex y B ih =>
    simp only [formulaSubstN]
    split
    · simp only [LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
        LCS.CutElim.Interpolation.formulaBV_formulaSubst] at *
      exact ⟨ih h.1, h.2⟩
    · exact h

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.Herbrand.SHGTheorem.Main.SHG
/-- Exact Skolemization preserves distinct quantifier bindings.
Disjointness at binary nodes follows from the bound-variable subset
theorem, and the eliminated existential case uses substitution's
invariance of the quantifier tree. -/
theorem skolemFormExactAux_distinctQuantifierBindings {L : Language}
    (S : SkolemSpec L) :
    ∀ (m : Nat) (A : FormulaN S.language) (scope : List Nat)
      (indices : List (Fin S.n)) (B : FormulaN S.language) (used : Nat),
      formulaQuantCount A = m →
      FormulaN.isNNF A →
      indices.length = skolemDescriptorCount A →
      skolemFormExactAux S A scope indices = some (B, used) →
      distinctQuantifierBindings A →
      distinctQuantifierBindings B := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro A scope indices Out used hCount hNNF hLength hRun hDQ
    match A, hCount, hNNF, hLength, hDQ with
    | .predN P ts, _, _, hLength, _ =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.predN P ts) scope [] =
            some (.predN P ts, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      trivial
    | .eq_ h t₁ t₂, _, _, hLength, _ =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.eq_ h t₁ t₂) scope [] =
            some (.eq_ h t₁ t₂, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      trivial
    | .neg C, _, hNNF, hLength, hDQ =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.neg C) scope [] =
            some (.neg C, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact hDQ
    | .conj C D, hCount, hNNF, hLength, hDQ =>
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
      obtain ⟨C', hC'⟩ :=
        skolemFormExactAux_result S _ C scope
          (indices.take (skolemDescriptorCount C)) rfl hLeftLength
      obtain ⟨D', hD'⟩ :=
        skolemFormExactAux_result S _ D scope
          (indices.drop (skolemDescriptorCount C)) rfl hRightLength
      have hDQC :=
        ih _ qC C scope (indices.take (skolemDescriptorCount C))
          C' _ rfl hNNF.1 hLeftLength hC' hDQ.1
      have hDQD :=
        ih _ qD D scope (indices.drop (skolemDescriptorCount C))
          D' _ rfl hNNF.2 hRightLength hD' hDQ.2.1
      have hBVC :=
        skolemFormExactAux_bv_bound S _ C scope
          (indices.take (skolemDescriptorCount C)) C' _
          rfl hNNF.1 hLeftLength hC'
      have hBVD :=
        skolemFormExactAux_bv_bound S _ D scope
          (indices.drop (skolemDescriptorCount C)) D' _
          rfl hNNF.2 hRightLength hD'
      have hCanonical :
          skolemFormExactAux S (.conj C D) scope indices =
            some (.conj C' D',
              skolemDescriptorCount C + skolemDescriptorCount D) := by
        simp [skolemFormExactAux, hC', hD']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      refine ⟨hDQC, hDQD, ?_⟩
      intro y hy
      exact hDQ.2.2 y ⟨hBVC y hy.1, hBVD y hy.2⟩
    | .disj C D, hCount, hNNF, hLength, hDQ =>
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
      obtain ⟨C', hC'⟩ :=
        skolemFormExactAux_result S _ C scope
          (indices.take (skolemDescriptorCount C)) rfl hLeftLength
      obtain ⟨D', hD'⟩ :=
        skolemFormExactAux_result S _ D scope
          (indices.drop (skolemDescriptorCount C)) rfl hRightLength
      have hDQC :=
        ih _ qC C scope (indices.take (skolemDescriptorCount C))
          C' _ rfl hNNF.1 hLeftLength hC' hDQ.1
      have hDQD :=
        ih _ qD D scope (indices.drop (skolemDescriptorCount C))
          D' _ rfl hNNF.2 hRightLength hD' hDQ.2.1
      have hBVC :=
        skolemFormExactAux_bv_bound S _ C scope
          (indices.take (skolemDescriptorCount C)) C' _
          rfl hNNF.1 hLeftLength hC'
      have hBVD :=
        skolemFormExactAux_bv_bound S _ D scope
          (indices.drop (skolemDescriptorCount C)) D' _
          rfl hNNF.2 hRightLength hD'
      have hCanonical :
          skolemFormExactAux S (.disj C D) scope indices =
            some (.disj C' D',
              skolemDescriptorCount C + skolemDescriptorCount D) := by
        simp [skolemFormExactAux, hC', hD']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      refine ⟨hDQC, hDQD, ?_⟩
      intro y hy
      exact hDQ.2.2 y ⟨hBVC y hy.1, hBVD y hy.2⟩
    | .impl _ _, _, hNNF, _, _ => exact hNNF.elim
    | .all x C, hCount, hNNF, hLength, hDQ =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qC : formulaQuantCount C < m := by omega
      have hBodyLength :
          indices.length = skolemDescriptorCount C := by
        simpa [skolemDescriptorCount] using hLength
      obtain ⟨C', hC'⟩ :=
        skolemFormExactAux_result S _ C (scope ++ [x])
          indices rfl hBodyLength
      have hDQC :=
        ih _ qC C (scope ++ [x]) indices C' _
          rfl hNNF hBodyLength hC' hDQ.1
      have hBVC :=
        skolemFormExactAux_bv_bound S _ C (scope ++ [x])
          indices C' _ rfl hNNF hBodyLength hC'
      have hCanonical :
          skolemFormExactAux S (.all x C) scope indices =
            some (.all x C', skolemDescriptorCount C) := by
        simp [skolemFormExactAux, hC']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      refine ⟨hDQC, ?_⟩
      intro hx
      exact hDQ.2 (hBVC x hx)
    | .ex x C, hCount, hNNF, hLength, hDQ =>
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
        let CSub := formulaSubstN C (exactSkolemTerm S i) x
        have qCSub : formulaQuantCount CSub < m := by
          simp only [CSub]
          rw [formulaSubst_quantCount]
          omega
        have hNNFSub : FormulaN.isNNF CSub :=
          isNNF_formulaSubstN C _ _ hNNF
        have hSubLength :
            rest.length = skolemDescriptorCount CSub := by
          rw [formulaSubstN_descriptorCount]
          exact hRestLength
        obtain ⟨C', hC'⟩ :=
          skolemFormExactAux_result S _ CSub scope rest rfl hSubLength
        have hDQSub : distinctQuantifierBindings CSub :=
          distinctQuantifierBindings_of_formulaSubstN
            C (exactSkolemTerm S i) x hDQ.1
        have hDQC :=
          ih _ qCSub CSub scope rest C' _
            rfl hNNFSub hSubLength hC' hDQSub
        have hCanonical :
            skolemFormExactAux S (.ex x C) scope (i :: rest) =
              some (C', skolemDescriptorCount CSub + 1) := by
          simp [skolemFormExactAux, skolemSubst, CSub, hC']
        have hOut := skolemFormExactAux_formula_unique hCanonical hRun
        subst Out
        exact hDQC

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.Herbrand.SHGTheorem.Main.SHG
/-- Exact descriptor alignment discharges all traversal obligations
internally: the Skolem form of every bundled rectified NNF sentence is
closed, rectified, and contains no existential quantifier. No
allocation or rank-zero side condition is exposed to callers. -/
theorem skolemForm_isSkolemNormalForm' {L : Language}
    (spec : SkolemSpec L) :
    isSkolemNormalForm (skolemForm spec) := by
  let A :=
    liftFormulaSkolem (skolemRank := spec.skolemRank) spec.source
  have hNNFLift : FormulaN.isNNF A :=
    liftFormulaSkolem_isNNF spec.source spec.hNNF
  have hRun :
      skolemFormExactAux spec A [] spec.indices =
        some (skolemFormTraversal spec) := by
    simp [A, skolemFormTraversal]
  have hShape :=
    skolemFormExactAux_shape_nnf spec _ A [] spec.indices
      (skolemFormTraversal spec).1 (skolemFormTraversal spec).2
      rfl hNNFLift spec.indices_length_eq_lifted_descriptorCount hRun
  have hFVSource : ∀ y ∈ formulaFVN A, y ∈ ([] : List Nat) := by
    intro y hy
    have hFVlift :
        formulaFVN A = formulaFVN spec.source := by
      simpa [A] using liftFormulaSkolem_formulaFVN spec.source
    have hySource : y ∈ formulaFVN spec.source := hFVlift ▸ hy
    rw [spec.hSentence] at hySource
    exact hySource.elim
  have hFV :=
    skolemFormExactAux_fv_bound spec _ A [] spec.indices
      (skolemFormTraversal spec).1 (skolemFormTraversal spec).2
      rfl hNNFLift spec.indices_length_eq_lifted_descriptorCount
      spec.indices_scopes_lifted hRun hFVSource
  have hDQlift : distinctQuantifierBindings A := by
    simpa [A] using
      liftFormulaSkolem_distinctQuantifierBindings
        spec.source spec.hRect.2
  have hDQ :=
    skolemFormExactAux_distinctQuantifierBindings spec _ A []
      spec.indices (skolemFormTraversal spec).1
      (skolemFormTraversal spec).2 rfl hNNFLift
      spec.indices_length_eq_lifted_descriptorCount hRun hDQlift
  change
    isSkolemNormalFormShape (skolemFormTraversal spec).1 ∧
      isRectified (skolemFormTraversal spec).1 ∧
      FormulaN.isClosed (skolemFormTraversal spec).1
  refine ⟨hShape.2, ?_, ?_⟩
  · refine ⟨?_, hDQ⟩
    intro y hy
    exact List.not_mem_nil (hFV y hy.1)
  · unfold FormulaN.isClosed
    funext y
    apply propext
    constructor
    · intro hy
      exact (List.not_mem_nil (hFV y hy)).elim
    · intro hy
      exact hy.elim

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix
/-- The exact top-level traversal preserves NNF. -/
theorem skolemForm_isNNF' {L : Language}
    (spec : SkolemSpec L) :
    FormulaN.isNNF (skolemForm spec) := by
  let A :=
    liftFormulaSkolem (skolemRank := spec.skolemRank) spec.source
  have hNNFLift : FormulaN.isNNF A :=
    liftFormulaSkolem_isNNF spec.source spec.hNNF
  have hRun :
      skolemFormExactAux spec A [] spec.indices =
        some (skolemFormTraversal spec) := by
    simp [A, skolemFormTraversal]
  have hShape :=
    skolemFormExactAux_shape_nnf spec _ A [] spec.indices
      (skolemFormTraversal spec).1 (skolemFormTraversal spec).2
      rfl hNNFLift spec.indices_length_eq_lifted_descriptorCount hRun
  exact hShape.1

end LCS.Herbrand.SHGTheorem.Herbrand
end
