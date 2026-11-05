import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.SHGTheorem.Herbrand
import LCS.Herbrand.SHGTheorem.Main.SkolemSemanticsBase
import Attach
import LCS.Herbrand.SHGTheorem.Main.SkolemEquisatisfiability.ProofsStamp

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

-- ATTACH-BLOCKER: private declaration
/-- Context-strengthened semantic invariant for the backward direction.
`processed` records the Skolem symbols already fixed by enclosing or
earlier occurrences.  The returned interpretation changes only
`indices`, so later disjoint traversal segments cannot invalidate an
earlier result.  The guard `P` permits disjunction branches to select
witnesses pointwise in their current universal-scope values. -/
private theorem skolemFormExactAux_backward_semantics {L : Language}
    (S : SkolemSpec L) (M : Structure L) :
    ∀ (m : Nat) (A : FormulaN S.language) (scope : List Nat)
      (indices : List (Fin S.n)) (B : FormulaN S.language) (used : Nat)
      (processed : List (Fin S.n))
      (K : SkolemInterpretation S M)
      (P : (Nat → M.carrier) → Prop),
      formulaQuantCount A = m →
      FormulaN.isNNF A →
      indices.length = skolemDescriptorCount A →
      indices.map S.skolemScope = existentialScopesAux A scope →
      skolemFormExactAux S A scope indices = some (B, used) →
      distinctQuantifierBindings A →
      (∀ y ∈ scope, y ∉ formulaBVN A) →
      (∀ y ∈ formulaFVN A, y ∈ scope) →
      skolemFormulaSupported S processed A →
      (processed ++ indices).Nodup →
      (∀ s, P s →
        formulaEvalN (interpretationExpansion S M K) A s) →
      ∃ K' : SkolemInterpretation S M,
        (∀ i, i ∉ indices → ∀ args, K' i args = K i args) ∧
        (∀ s, P s →
          formulaEvalN (interpretationExpansion S M K') B s) ∧
        skolemFormulaSupported S (processed ++ indices) B := by
  classical
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro A scope indices Out used processed K P hCount hNNF hLength
      hScopes hRun hDistinct hScopeFresh hFV hSupport hNodup hPrem
    match A, hCount, hNNF, hLength, hDistinct with
    | .predN Q ts, _, _, hLength, _ =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.predN Q ts) scope [] =
            some (.predN Q ts, 0) := by
        simp [skolemFormExactAux]
      have hFormula :=
        skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      refine ⟨K, ?_, hPrem, ?_⟩
      · intro i hi args
        rfl
      · simpa using hSupport
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
      refine ⟨K, ?_, hPrem, ?_⟩
      · intro i hi args
        rfl
      · simpa using hSupport
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
      refine ⟨K, ?_, hPrem, ?_⟩
      · intro i hi args
        rfl
      · simpa using hSupport
    | .conj C D, hCount, hNNF, hLength, hDistinct =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qC : formulaQuantCount C < m := by omega
      have qD : formulaQuantCount D < m := by omega
      let left := indices.take (skolemDescriptorCount C)
      let right := indices.drop (skolemDescriptorCount C)
      have hCLe : skolemDescriptorCount C ≤ indices.length := by
        rw [hLength]
        exact Nat.le_add_right _ _
      have hLeftLength : left.length = skolemDescriptorCount C := by
        exact List.length_take_of_le hCLe
      have hRightLength : right.length = skolemDescriptorCount D := by
        simp only [right, List.length_drop, hLength, skolemDescriptorCount]
        omega
      have hLeftScopes :
          left.map S.skolemScope = existentialScopesAux C scope := by
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
          right.map S.skolemScope = existentialScopesAux D scope := by
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
        skolemFormExactAux_result S _ C scope left rfl hLeftLength
      obtain ⟨D', hD'⟩ :=
        skolemFormExactAux_result S _ D scope right rfl hRightLength
      have hPartition :
          ((processed ++ left) ++ right).Nodup := by
        simp only [left, right, List.append_assoc,
          List.take_append_drop]
        exact hNodup
      have hNodupLeft : (processed ++ left).Nodup :=
        (List.nodup_append.mp hPartition).1
      have hFreshC : ∀ y ∈ scope, y ∉ formulaBVN C := by
        intro y hyScope hyBound
        exact hScopeFresh y hyScope (Or.inl hyBound)
      have hFreshD : ∀ y ∈ scope, y ∉ formulaBVN D := by
        intro y hyScope hyBound
        exact hScopeFresh y hyScope (Or.inr hyBound)
      have hFVC : ∀ y ∈ formulaFVN C, y ∈ scope := by
        intro y hy
        exact hFV y (Or.inl hy)
      have hFVD : ∀ y ∈ formulaFVN D, y ∈ scope := by
        intro y hy
        exact hFV y (Or.inr hy)
      obtain ⟨K₁, hFrame₁, hEvalC₁, hSupportC'⟩ :=
        ih _ qC C scope left C' _ processed K P rfl hNNF.1
          hLeftLength hLeftScopes hC' hDistinct.1 hFreshC hFVC
          hSupport.1 hNodupLeft
          (fun s hs => (hPrem s hs).1)
      have hAgreeProcessed :
          skolemInterpretationsAgreeOn S M processed K K₁ :=
        skolemInterpretationsAgreeOn_of_frame S M hFrame₁
          (fun i hi =>
            not_mem_right_of_nodup_append hNodupLeft hi)
      have hSupportD₁ :
          skolemFormulaSupported S (processed ++ left) D :=
        skolemFormulaSupported_mono S
          (fun i hi => List.mem_append_left left hi) D hSupport.2
      have hPremD₁ :
          ∀ s, P s →
            formulaEvalN (interpretationExpansion S M K₁) D s := by
        intro s hs
        exact
          (formulaEvalN_interpretationExpansion_iff
            S M processed K K₁ hAgreeProcessed D hSupport.2 s).mp
            (hPrem s hs).2
      obtain ⟨K₂, hFrame₂, hEvalD₂, hSupportD'⟩ :=
        ih _ qD D scope right D' _ (processed ++ left) K₁ P
          rfl hNNF.2 hRightLength hRightScopes hD'
          hDistinct.2.1 hFreshD hFVD hSupportD₁ hPartition hPremD₁
      have hAgreeLeft :
          skolemInterpretationsAgreeOn S M (processed ++ left) K₁ K₂ :=
        skolemInterpretationsAgreeOn_of_frame S M hFrame₂
          (fun i hi =>
            not_mem_right_of_nodup_append hPartition hi)
      have hCanonical :
          skolemFormExactAux S (.conj C D) scope indices =
            some (.conj C' D',
              skolemDescriptorCount C + skolemDescriptorCount D) := by
        simp [skolemFormExactAux, left, right, hC', hD']
      have hFormula :=
        skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      refine ⟨K₂, ?_, ?_, ?_⟩
      · intro i hi args
        have hiLeft : i ∉ left := by
          intro hi'
          exact hi (List.mem_of_mem_take hi')
        have hiRight : i ∉ right := by
          intro hi'
          exact hi (List.mem_of_mem_drop hi')
        exact (hFrame₂ i hiRight args).trans (hFrame₁ i hiLeft args)
      · intro s hs
        refine ⟨?_, hEvalD₂ s hs⟩
        exact
          (formulaEvalN_interpretationExpansion_iff
            S M (processed ++ left) K₁ K₂ hAgreeLeft
            C' hSupportC' s).mp (hEvalC₁ s hs)
      · have hSupportC'Full :
            skolemFormulaSupported S
              ((processed ++ left) ++ right) C' :=
          skolemFormulaSupported_mono S
            (fun i hi => List.mem_append_left right hi) C' hSupportC'
        have hFull :
            (processed ++ left) ++ right = processed ++ indices := by
          simp only [left, right, List.append_assoc,
            List.take_append_drop]
        rw [← hFull]
        exact ⟨hSupportC'Full, hSupportD'⟩
    | .disj C D, hCount, hNNF, hLength, hDistinct =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qC : formulaQuantCount C < m := by omega
      have qD : formulaQuantCount D < m := by omega
      let left := indices.take (skolemDescriptorCount C)
      let right := indices.drop (skolemDescriptorCount C)
      have hCLe : skolemDescriptorCount C ≤ indices.length := by
        rw [hLength]
        exact Nat.le_add_right _ _
      have hLeftLength : left.length = skolemDescriptorCount C := by
        exact List.length_take_of_le hCLe
      have hRightLength : right.length = skolemDescriptorCount D := by
        simp only [right, List.length_drop, hLength, skolemDescriptorCount]
        omega
      have hLeftScopes :
          left.map S.skolemScope = existentialScopesAux C scope := by
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
          right.map S.skolemScope = existentialScopesAux D scope := by
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
        skolemFormExactAux_result S _ C scope left rfl hLeftLength
      obtain ⟨D', hD'⟩ :=
        skolemFormExactAux_result S _ D scope right rfl hRightLength
      have hPartition :
          ((processed ++ left) ++ right).Nodup := by
        simp only [left, right, List.append_assoc,
          List.take_append_drop]
        exact hNodup
      have hNodupLeft : (processed ++ left).Nodup :=
        (List.nodup_append.mp hPartition).1
      have hFreshC : ∀ y ∈ scope, y ∉ formulaBVN C := by
        intro y hyScope hyBound
        exact hScopeFresh y hyScope (Or.inl hyBound)
      have hFreshD : ∀ y ∈ scope, y ∉ formulaBVN D := by
        intro y hyScope hyBound
        exact hScopeFresh y hyScope (Or.inr hyBound)
      have hFVC : ∀ y ∈ formulaFVN C, y ∈ scope := by
        intro y hy
        exact hFV y (Or.inl hy)
      have hFVD : ∀ y ∈ formulaFVN D, y ∈ scope := by
        intro y hy
        exact hFV y (Or.inr hy)
      let PLeft : (Nat → M.carrier) → Prop :=
        fun s => P s ∧
          formulaEvalN (interpretationExpansion S M K) C s
      let PRight : (Nat → M.carrier) → Prop :=
        fun s => P s ∧
          ¬ formulaEvalN (interpretationExpansion S M K) C s
      obtain ⟨K₁, hFrame₁, hEvalC₁, hSupportC'⟩ :=
        ih _ qC C scope left C' _ processed K PLeft rfl hNNF.1
          hLeftLength hLeftScopes hC' hDistinct.1 hFreshC hFVC
          hSupport.1 hNodupLeft (fun s hs => hs.2)
      have hAgreeProcessed :
          skolemInterpretationsAgreeOn S M processed K K₁ :=
        skolemInterpretationsAgreeOn_of_frame S M hFrame₁
          (fun i hi =>
            not_mem_right_of_nodup_append hNodupLeft hi)
      have hSupportD₁ :
          skolemFormulaSupported S (processed ++ left) D :=
        skolemFormulaSupported_mono S
          (fun i hi => List.mem_append_left left hi) D hSupport.2
      have hPremD₁ :
          ∀ s, PRight s →
            formulaEvalN (interpretationExpansion S M K₁) D s := by
        intro s hs
        have hD :
            formulaEvalN (interpretationExpansion S M K) D s := by
          rcases hPrem s hs.1 with hC | hD
          · exact (hs.2 hC).elim
          · exact hD
        exact
          (formulaEvalN_interpretationExpansion_iff
            S M processed K K₁ hAgreeProcessed D hSupport.2 s).mp hD
      obtain ⟨K₂, hFrame₂, hEvalD₂, hSupportD'⟩ :=
        ih _ qD D scope right D' _ (processed ++ left) K₁ PRight
          rfl hNNF.2 hRightLength hRightScopes hD'
          hDistinct.2.1 hFreshD hFVD hSupportD₁ hPartition hPremD₁
      have hAgreeLeft :
          skolemInterpretationsAgreeOn S M (processed ++ left) K₁ K₂ :=
        skolemInterpretationsAgreeOn_of_frame S M hFrame₂
          (fun i hi =>
            not_mem_right_of_nodup_append hPartition hi)
      have hCanonical :
          skolemFormExactAux S (.disj C D) scope indices =
            some (.disj C' D',
              skolemDescriptorCount C + skolemDescriptorCount D) := by
        simp [skolemFormExactAux, left, right, hC', hD']
      have hFormula :=
        skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      refine ⟨K₂, ?_, ?_, ?_⟩
      · intro i hi args
        have hiLeft : i ∉ left := by
          intro hi'
          exact hi (List.mem_of_mem_take hi')
        have hiRight : i ∉ right := by
          intro hi'
          exact hi (List.mem_of_mem_drop hi')
        exact (hFrame₂ i hiRight args).trans (hFrame₁ i hiLeft args)
      · intro s hs
        by_cases hC :
            formulaEvalN (interpretationExpansion S M K) C s
        · exact Or.inl
            ((formulaEvalN_interpretationExpansion_iff
              S M (processed ++ left) K₁ K₂ hAgreeLeft
              C' hSupportC' s).mp
              (hEvalC₁ s ⟨hs, hC⟩))
        · exact Or.inr (hEvalD₂ s ⟨hs, hC⟩)
      · have hSupportC'Full :
            skolemFormulaSupported S
              ((processed ++ left) ++ right) C' :=
          skolemFormulaSupported_mono S
            (fun i hi => List.mem_append_left right hi) C' hSupportC'
        have hFull :
            (processed ++ left) ++ right = processed ++ indices := by
          simp only [left, right, List.append_assoc,
            List.take_append_drop]
        rw [← hFull]
        exact ⟨hSupportC'Full, hSupportD'⟩
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
      have hFVC : ∀ y ∈ formulaFVN C, y ∈ scope ++ [x] := by
        intro y hy
        by_cases hyx : y = x
        · subst y
          simp
        · exact List.mem_append.mpr
            (Or.inl (hFV y ⟨hy, hyx⟩))
      let PBody : (Nat → M.carrier) → Prop :=
        fun t => ∃ s a, P s ∧ t = assignUpdate s x a
      have hPremBody :
          ∀ t, PBody t →
            formulaEvalN (interpretationExpansion S M K) C t := by
        rintro t ⟨s, a, hs, rfl⟩
        exact hPrem s hs a
      obtain ⟨K', hFrame, hEvalC', hSupportC'⟩ :=
        ih _ qC C (scope ++ [x]) indices C' _ processed K PBody
          rfl hNNF hBodyLength hBodyScopes hC' hDistinct.1
          hFreshC hFVC hSupport hNodup hPremBody
      have hCanonical :
          skolemFormExactAux S (.all x C) scope indices =
            some (.all x C', skolemDescriptorCount C) := by
        simp [skolemFormExactAux, hC']
      have hFormula :=
        skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      refine ⟨K', hFrame, ?_, hSupportC'⟩
      intro s hs a
      exact hEvalC' (assignUpdate s x a) ⟨s, a, hs, rfl⟩
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
        have hiNotProcessed : i ∉ processed := by
          have hAsAppend :
              (processed ++ (i :: rest)).Nodup := hNodup
          exact not_mem_left_of_nodup_append hAsAppend (by simp)
        let witnessExists :
            (Fin (S.skolemRank i) → M.carrier) → Prop :=
          fun args =>
            ∃ d s₀, P s₀ ∧ exactScopeValues S M i s₀ = args ∧
              formulaEvalN (interpretationExpansion S M K) C
                (assignUpdate s₀ x d)
        let witness :
            (Fin (S.skolemRank i) → M.carrier) → M.carrier :=
          fun args =>
            if h : witnessExists args then Classical.choose h
            else Classical.choice M.carrierNonempty
        let K₁ : SkolemInterpretation S M :=
          fun j =>
            if hji : j = i then hji ▸ witness else K j
        have hFrame₁ :
            ∀ j, j ∉ [i] → ∀ args, K₁ j args = K j args := by
          intro j hj args
          have hji : j ≠ i := by simpa using hj
          simp [K₁, hji]
        have hAgreeProcessed :
            skolemInterpretationsAgreeOn S M processed K K₁ :=
          skolemInterpretationsAgreeOn_of_frame S M hFrame₁
            (fun j hj => by
              intro hjSingle
              have hji : j = i := by simpa using hjSingle
              subst j
              exact hiNotProcessed hj)
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
        have hFVSub : ∀ y ∈ formulaFVN CSub, y ∈ scope := by
          intro y hy
          rcases LCS.FirstOrder.Gentzen.Hintikka.formulaFVN_formulaSubstN
              C (exactSkolemTerm S i) x y hy with
            ⟨hyC, hyNe⟩ | hyTerm
          · exact hFV y ⟨hyC, hyNe⟩
          · rw [← hHeadScope]
            exact exactSkolemTerm_fv S i y hyTerm
        have hFree : isFreeForN (exactSkolemTerm S i) x C := by
          apply LCS.FirstOrder.Gentzen.Hintikka.isFreeForN_of_bv_disjoint
          intro y hyTerm hyBound
          apply hScopeFresh y
          · rw [← hHeadScope]
            exact exactSkolemTerm_fv S i y hyTerm
          · exact Or.inl hyBound
        have hSupportC :
            skolemFormulaSupported S (processed ++ [i]) C :=
          skolemFormulaSupported_mono S
            (fun j hj => List.mem_append_left [i] hj) C hSupport
        have hSupportTerm :
            skolemTermSupported S (processed ++ [i])
              (exactSkolemTerm S i) :=
          exactSkolemTerm_supported S i (processed ++ [i]) (by simp)
        have hSupportSub :
            skolemFormulaSupported S (processed ++ [i]) CSub :=
          formulaSubstN_supported S (processed ++ [i])
            C (exactSkolemTerm S i) x hSupportC hSupportTerm
        have hPremSub :
            ∀ s, P s →
              formulaEvalN (interpretationExpansion S M K₁) CSub s := by
          intro s hs
          obtain ⟨d, hd⟩ := hPrem s hs
          have hExists :
              witnessExists (exactScopeValues S M i s) := by
            exact ⟨d, s, hs, rfl, hd⟩
          have hChosen :
              ∃ s₀, P s₀ ∧
                exactScopeValues S M i s₀ =
                  exactScopeValues S M i s ∧
                formulaEvalN (interpretationExpansion S M K) C
                  (assignUpdate s₀ x
                    (witness (exactScopeValues S M i s))) := by
            have hWitnessEq :
                witness (exactScopeValues S M i s) =
                  Classical.choose hExists := by
              dsimp only [witness]
              split
              · rename_i hExists'
                rw [show hExists' = hExists from Subsingleton.elim _ _]
                rfl
              · rename_i hNot
                exact (hNot hExists).elim
            rw [hWitnessEq]
            exact Classical.choose_spec hExists
          obtain ⟨s₀, hs₀, hArgs, hEval₀⟩ := hChosen
          have hAssignments :
              ∀ y, y ∈ formulaFVN C →
                assignUpdate s₀ x
                    (witness (exactScopeValues S M i s)) y =
                  assignUpdate s x
                    (witness (exactScopeValues S M i s)) y := by
            intro y hy
            simp only [assignUpdate]
            split
            · rfl
            · rename_i hyx
              have hyScope : y ∈ scope := hFV y ⟨hy, hyx⟩
              rw [← hHeadScope] at hyScope
              obtain ⟨k, hk⟩ := List.get_of_mem hyScope
              let k' : Fin (S.skolemRank i) :=
                ⟨k.val, by
                  simpa [SkolemSpec.skolemRank] using k.isLt⟩
              have hAt := congrFun hArgs k'
              simp only [exactScopeValues] at hAt
              have hAt' :
                  s₀ ((S.skolemScope i).get k) =
                    s ((S.skolemScope i).get k) := by
                simpa [k'] using hAt
              exact (congrArg s₀ hk).symm.trans
                (hAt'.trans (congrArg s hk))
          have hEvalK :
              formulaEvalN (interpretationExpansion S M K) C
                (assignUpdate s x
                  (witness (exactScopeValues S M i s))) :=
            (coincidenceLemmaN
              (interpretationExpansion S M K) C
              (assignUpdate s₀ x
                (witness (exactScopeValues S M i s)))
              (assignUpdate s x
                (witness (exactScopeValues S M i s)))
              hAssignments).mp hEval₀
          have hEvalK₁ :
              formulaEvalN (interpretationExpansion S M K₁) C
                (assignUpdate s x
                  (witness (exactScopeValues S M i s))) :=
            (formulaEvalN_interpretationExpansion_iff
              S M processed K K₁ hAgreeProcessed C hSupport
              (assignUpdate s x
                (witness (exactScopeValues S M i s)))).mp hEvalK
          rw [formulaSubstEvalDirectN
            (M := interpretationExpansion S M K₁)
            s C (exactSkolemTerm S i) x hFree]
          rw [termEval_exactSkolemTerm S M K₁ i s]
          have hK₁i :
              K₁ i (exactScopeValues S M i s) =
                witness (exactScopeValues S M i s) := by
            simp [K₁]
          rw [hK₁i]
          exact hEvalK₁
        have hNodupRest :
            ((processed ++ [i]) ++ rest).Nodup := by
          simpa [List.append_assoc] using hNodup
        obtain ⟨K₂, hFrame₂, hEvalC₂, hSupportC'⟩ :=
          ih _ qCSub CSub scope rest C' _ (processed ++ [i]) K₁ P
            rfl hNNFSub hSubLength hSubScopes hC' hDistinctSub
            hFreshSub hFVSub hSupportSub hNodupRest hPremSub
        have hCanonical :
            skolemFormExactAux S (.ex x C) scope (i :: rest) =
              some (C', skolemDescriptorCount CSub + 1) := by
          simp [skolemFormExactAux, skolemSubst, CSub, hC']
        have hFormula :=
          skolemFormExactAux_formula_unique hCanonical hRun
        subst Out
        refine ⟨K₂, ?_, hEvalC₂, ?_⟩
        · intro j hj args
          have hjRest : j ∉ rest := by
            intro hj'
            exact hj (by simp [hj'])
          have hji : j ≠ i := by
            intro hji
            subst j
            exact hj (by simp)
          have hjSingle : j ∉ [i] := by simpa using hji
          exact (hFrame₂ j hjRest args).trans (hFrame₁ j hjSingle args)
        · simpa [List.append_assoc] using hSupportC'

-- ===================================================================
-- Lemma 7.6.3 (backward generalized): skolemForm_backward_genN
-- ===================================================================

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Lemma 7.6.3 backward (FormulaN version): if M satisfies
`spec.source`, then a coordinated expansion N of M to the
Skolem-extended language satisfies `SK spec`. The public
`witnessSelectingExpansion` supplies only the initial interpretation
seed `K₀`; the contextual traversal refines it to a coordinated
interpretation `K`, and `interpretationExpansion spec M K` is the final
structure. The Skolem-form argument is fully packaged as
`spec : SkolemSpec L` (Def 7.6.2). -/
theorem skolemForm_backward_genN {L : Language}
    (spec : SkolemSpec L)
    (M : Structure L) (s : Assignment M)
    (_h : formulaEvalN M spec.source s) :
    ∃ (N : Structure spec.language) (sN : Assignment N),
      isExpansion L spec.n spec.skolemRank M N ∧
      formulaEvalN N (SK spec) sN := by
-- BEGIN PROOF
  classical
  let A :=
    liftFormulaSkolem (skolemRank := spec.skolemRank) spec.source
  let scopeVarMap :
      (i : Fin spec.n) → Fin (spec.skolemRank i) → Nat :=
    fun i k =>
      (spec.skolemScope i).get
        ⟨k.val, by
          simpa [SkolemSpec.skolemRank] using k.isLt⟩
  let W :=
    witnessSelectingExpansion M
      (skolemAllocationBinderBody spec) scopeVarMap
  let K₀ : SkolemInterpretation spec M :=
    fun i args =>
      if hRank : spec.skolemRank i = 0 then
        W.interpConst (Sum.inr ⟨i, hRank⟩)
      else
        W.interpFunc (Sum.inr ⟨i, Nat.pos_of_ne_zero hRank⟩) args
  let N₀ := interpretationExpansion spec M K₀
  unfold SkolemSpec.language at N₀
  have hExp₀ :
      isExpansion L spec.n spec.skolemRank M N₀ :=
    interpretationExpansion_isExpansion spec M K₀
  have hSourceAll :
      ∀ t : Assignment M, formulaEvalN M spec.source t := by
    intro t
    exact
      (coincidenceLemmaN M spec.source s t
        (fun y hy => by
          rw [spec.hSentence] at hy
          exact hy.elim)).mp _h
  have hClosedA : formulaFVN A = (∅ : Set Nat) := by
    rw [show formulaFVN A = formulaFVN spec.source by
      simpa [A] using liftFormulaSkolem_formulaFVN spec.source]
    exact spec.hSentence
  have hLiftAll :
      ∀ t : Nat → M.carrier, formulaEvalN N₀ A t := by
    intro t
    have hAtTransport :
        formulaEvalN N₀ A
          (fun x => (hExp₀.choose ▸ t x : N₀.carrier)) := by
      simpa [A] using
        (liftFormulaSkolem_eval_iff M N₀ hExp₀ t spec.source).mp
          (hSourceAll t)
    exact
      (coincidenceLemmaN N₀ A
        (fun x => (hExp₀.choose ▸ t x : N₀.carrier)) t
        (fun y hy => by
          rw [hClosedA] at hy)).mp hAtTransport
  have hNNF : FormulaN.isNNF A :=
    liftFormulaSkolem_isNNF spec.source spec.hNNF
  have hDistinct : distinctQuantifierBindings A := by
    simpa [A] using
      liftFormulaSkolem_distinctQuantifierBindings
        spec.source spec.hRect.2
  have hScopeFresh : ∀ y ∈ ([] : List Nat), y ∉ formulaBVN A := by
    intro y hy
    simp at hy
  have hFV : ∀ y ∈ formulaFVN A, y ∈ ([] : List Nat) := by
    intro y hy
    rw [hClosedA] at hy
    exact hy.elim
  have hSupport :
      skolemFormulaSupported spec [] A := by
    simpa [A] using liftFormulaSkolem_supported_nil spec spec.source
  have hRun :
      skolemFormExactAux spec A [] spec.indices =
        some (SK spec, spec.n) := by
    simpa [A] using skolemFormExactAux_top_formula_result spec
  obtain ⟨K, _hFrame, hEval, _hSupportOut⟩ :=
    skolemFormExactAux_backward_semantics spec M _ A [] spec.indices
      (SK spec) spec.n [] K₀ (fun _ => True) rfl hNNF
      spec.indices_length_eq_lifted_descriptorCount
      spec.indices_scopes_lifted hRun hDistinct hScopeFresh hFV
      hSupport (by simpa using skolemSpec_indices_nodup spec)
      (fun t _ => hLiftAll t)
  let N := interpretationExpansion spec M K
  refine ⟨N, s, interpretationExpansion_isExpansion spec M K, ?_⟩
  exact hEval s trivial

-- ===================================================================
-- Lemma 7.6.3 (companion theorem): skolem_form_backward
-- ===================================================================



-- ===================================================================
-- Lemma 7.6.3: skolem_form_sat_iff
-- ===================================================================

/-- Lemma 7.6.3: Let L be a first-order language with or without
equality. Let A be a rectified L-sentence in NNF, and let B be its
Skolem normal form in the Skolem-extended language. The sentence A is
satisfiable iff its Skolem form B is satisfiable. In the forward
direction, `witnessSelectingExpansion` supplies only the initial
interpretation seed `K₀`; `skolemForm_backward_genN` contextually refines
it to the coordinated interpretation `K`, whose
`interpretationExpansion` is the final structure satisfying B. In the
backward direction, `skolemForm_forward_genN` reflects satisfaction to
the lifted A and `liftFormulaSkolem_eval_iff` transports it back to the
base language. -/
@[blueprint "chap7__lemma_7_6_3" (main := true)]
theorem skolem_form_sat_iff {L : Language}
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (B : FormulaN spec.language)
    (_hSkolem : SK spec = B) :
    satisfiableN A ↔ satisfiableN B 

-- ===================================================================
-- Theorem 7.6.1 (part a, helper): g1nnf_provable_of_unsat
-- ===================================================================

/-- Completeness bridge for an unsatisfiable formula in a language without
 equality: the singleton antecedent sequent is G1nnf-provable. -/
theorem g1nnf_provable_of_unsat {L : Language}
    (hL : L.withoutEquality)
    (A : FormulaN L)
    (_hUnsat : ¬ satisfiableN A) :
    LCS.Herbrand.NNFHauptsatz.Theorem.G1nnfProvableSet hL
      (({A} : LCS.Finset (FormulaN L)),
       (∅ : LCS.Finset (FormulaN L))) := by
  -- DEBT(completeness bridge: an unsatisfiable sentence of an equality-free language has a G1nnf proof of A →; pre-existing placeholder, chapter 7 proof-closing pass)
  sorry

/-- Completeness bridge for an unsatisfiable formula in a language with
 equality: the singleton antecedent sequent is G1nnf=-provable. -/
theorem g1nnfEq_provable_of_unsat {L : Language}
    (hL : L.hasEquality = true)
    (A : FormulaN L)
    (_hUnsat : ¬ satisfiableN A) :
    LCS.Herbrand.NNFHauptsatz.Equality.G1nnfEqProvable_Set hL
      (({A} : LCS.Finset (FormulaN L)),
       (∅ : LCS.Finset (FormulaN L))) := by
  -- REPAIR(T6-21d): proof pending (G1nnf= completeness for the SHG with-equality case)
  sorry

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness
/-- No-equality, closed-NNF completeness bridge for a singleton
antecedent.  The closedness hypothesis discharges the cross-formula
free/bound-variable condition of `g1nnf_completeness`; the resulting
set-level derivation is converted to the indexed proof-tree presentation
consumed by the Chapter 7/8 Herbrand infrastructure. -/
theorem g1nnf_provable_of_unsat_closed_nnf_noeq {L : Language}
    [DecidableEq (FormulaN L)]
    (hNoEq : L.withoutEquality)
    (A : FormulaN L)
    (hNNF : FormulaN.isNNF A)
    (hClosed : FormulaN.isClosed A)
    (hUnsat : ¬ satisfiableN A) :
    LCS.Herbrand.NNFHauptsatz.Theorem.G1nnfProvableSet hNoEq
      (({A} : LCS.Finset (FormulaN L)),
       (∅ : LCS.Finset (FormulaN L))) := by
  let s : G1nnfSequent L hNoEq :=
    { ante := fun F => F = A
      succ := Set.empty
      ante_nnf := by
        intro F hF
        exact hF ▸ hNNF
      succ_nnf := by
        intro F hF
        exact hF.elim
      ante_finite := ⟨[A], fun F => by simp⟩
      succ_finite := Set.Finite.empty }
  have hsValid : s.isValid := by
    intro M σ hAnte
    exact (hUnsat ⟨M, σ, hAnte A rfl⟩).elim
  have hsNoFreeBound :
      ∀ x : Nat,
        (∃ F, (F ∈ s.ante ∨ F ∈ s.succ) ∧
          x ∈ formulaFVN F) →
        (∀ B, (B ∈ s.ante ∨ B ∈ s.succ) →
          x ∉ formulaBVN B) := by
    intro x hx
    have hxFalse : False := by
      change
        (∃ F : FormulaN L,
          (F = A ∨ False) ∧ x ∈ formulaFVN F) at hx
      obtain ⟨F, hF, hxF⟩ := hx
      rcases hF with hFA | hF
      · subst F
        rw [hClosed] at hxF
        exact hxF
      · exact hF
    exact hxFalse.elim
  have hSetDerivable :
      LCS.CutElim.Hauptsatz.Completeness.G1nnfSetDerivable
        s.ante s.succ :=
    LCS.CutElim.Hauptsatz.Completeness.g1nnf_completeness
      hNoEq s hsValid hsNoFreeBound
  have hAnte :
      ∀ F, F ∈ ({A} : LCS.Finset (FormulaN L)) ↔ s.ante F := by
    intro F
    exact LCS.Finset.mem_singleton F A
  have hSucc :
      ∀ F, F ∈ (∅ : LCS.Finset (FormulaN L)) ↔ s.succ F := by
    intro F
    exact LCS.Finset.mem_empty F
  have hFinsetNNF :
      G1nnfFinsetSequent.IsNNF
        (({A} : LCS.Finset (FormulaN L)),
         (∅ : LCS.Finset (FormulaN L))) := by
    constructor
    · intro F hF
      exact (LCS.Finset.mem_singleton F A).1 hF ▸ hNNF
    · intro F hF
      exact (LCS.Finset.not_mem_empty hF).elim
  exact
    LCS.CutElim.Hauptsatz.g1nnfProofTree_of_setDerivable
      hSetDerivable hAnte hSucc hFinsetNNF

-- ===================================================================
-- Theorem 7.6.1 (part a, required companion): shg_unsat_cinstance
-- ===================================================================

-- retained: used by LCS.Herbrand.SHGTheorem.Main.SHG
/-- Internal closed-seed core of the forward direction of Theorem 7.6.1.
    Chapter 7 obtains this seed from its standing base-language constant
    assumption; later callers may instead supply a closed term already
    living in the selected Skolem language. The language equality flag selects
    G1nnf completeness and the G1nnf half lemma, or their equality-system
    counterparts. -/
noncomputable def shg_unsat_cinstance_seed {L : Language}
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (seed : {t : Term spec.language // Term.isClosed t})
    (hUnsat : ¬ satisfiableN A) :
    CInstance spec.language :=
  if hL : L.hasEquality = true then
    let hProv := g1nnfEq_provable_of_unsat hL A hUnsat
    let hEx :=
      Herbrand.herbrand_half_lemma_G1nnfEq_seed hL spec A hSource seed hProv
    Classical.choose (Classical.choose_spec hEx).1
  else
    have hNoEq : L.withoutEquality := by
      cases h : L.hasEquality <;> simp_all [Language.withoutEquality]
    let hProv := g1nnf_provable_of_unsat hNoEq A hUnsat
    let hEx :=
      Herbrand.herbrand_half_lemma_G1nnf_seed hNoEq spec A hSource seed hProv
    Classical.choose (Classical.choose_spec hEx).1

-- retained: used by LCS.Herbrand.SHGTheorem.Main.SHG
/-- Specification of the internal closed-seed c-instance constructor. -/
theorem shg_unsat_cinstance_seed_spec {L : Language}
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (seed : {t : Term spec.language // Term.isClosed t})
    (hUnsat : ¬ satisfiableN A) :
    (shg_unsat_cinstance_seed spec A hSource seed hUnsat).source = SK spec ∧
    CInstance.WellFormed
      (shg_unsat_cinstance_seed spec A hSource seed hUnsat) ∧
    ¬ satisfiableN
      (shg_unsat_cinstance_seed spec A hSource seed hUnsat).toFormula := by
  unfold shg_unsat_cinstance_seed
  split
  · rename_i hL
    have hEx :=
      Herbrand.herbrand_half_lemma_G1nnfEq_seed hL spec A hSource seed
        (g1nnfEq_provable_of_unsat hL A hUnsat)
    obtain ⟨hCinstOf, _hQF, hG2⟩ := Classical.choose_spec hEx
    obtain ⟨hSrc, hToF, hWF⟩ := Classical.choose_spec hCinstOf
    refine ⟨hSrc, hWF, ?_⟩
    rw [hToF]
    intro hSat
    obtain ⟨M, s, hEval⟩ := hSat
    have hValid :=
      LCS.Herbrand.NNFHauptsatz.Equality.g2nnfEq_provable_implies_valid
        (L := spec.language) hL _ _ hG2
    obtain ⟨B, hB, _⟩ := hValid M s (by
      intro A' hA'
      have hEq := (LCS.Finset.mem_singleton A' (Classical.choose hEx)).mp hA'
      exact hEq ▸ hEval)
    exact LCS.Finset.not_mem_empty hB
  · rename_i hL
    have hNoEq : L.withoutEquality := by
      cases h : L.hasEquality <;> simp_all [Language.withoutEquality]
    have hEx :=
      LCS.Herbrand.SHGTheorem.Herbrand.herbrand_half_lemma_G1nnf_seed
        hNoEq spec A hSource seed (g1nnf_provable_of_unsat hNoEq A hUnsat)
    have hCprop := Classical.choose_spec hEx
    obtain ⟨hCinstOf, _hQF, hG2⟩ := hCprop
    have hCiProp := Classical.choose_spec hCinstOf
    obtain ⟨hSrc, hToF, hWF⟩ := hCiProp
    refine ⟨hSrc, hWF, ?_⟩
    rw [hToF]
    intro hSat
    obtain ⟨M, s, hEval⟩ := hSat
    have hValid :
        LCS.Herbrand.NNFHauptsatz.Soundness.setSequentValid
          ({Classical.choose hEx} : LCS.Finset (FormulaN spec.language))
          (∅ : LCS.Finset (FormulaN spec.language)) :=
      LCS.Herbrand.NNFHauptsatz.Soundness.g2nnf_provable_implies_valid
        (show spec.language.withoutEquality from hNoEq) _ _ hG2
    have hImpossible :
        ∃ B, Membership.mem
            (∅ : LCS.Finset (FormulaN spec.language)) B ∧
          formulaEvalN M B s := by
      apply hValid M s
      intro A' hA'
      have hAeq : A' = Classical.choose hEx :=
        (LCS.Finset.mem_singleton (α := FormulaN spec.language)
          A' (Classical.choose hEx)).mp hA'
      rw [hAeq]
      exact hEval
    obtain ⟨B, hB, _hEvalB⟩ := hImpossible
    exact absurd hB LCS.Finset.not_mem_empty

-- retained: used by LCS.Herbrand.SHGTheorem.Main.SHG
/-- Theorem 7.6.1 (part a, required companion): Given an unsatisfiable rectified L-sentence A in NNF with Skolem spec `spec` (so `A = spec.source`), constructs a compound instance of `SK spec` that is unsatisfiable. The closed-seed construction selects G1nnf or G1nnf= completeness and the corresponding Herbrand half lemma according to the language equality flag. -/
noncomputable def shg_unsat_cinstance {L : Language}
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (hConst : Nonempty L.constSymbols)
    (hUnsat : ¬ satisfiableN A) :
    CInstance spec.language :=
  let seed : {t : Term spec.language // Term.isClosed t} :=
    ⟨.const (.inl (Classical.choice hConst)), by
      simp [Term.isClosed, termFV]⟩
  shg_unsat_cinstance_seed spec A hSource seed hUnsat

-- retained: used by LCS.Herbrand.SHGTheorem.Main.SHG
/-- Spec lemma for `shg_unsat_cinstance`: the produced c-instance has
source `SK spec`, is WellFormed, and its extracted quantifier-free
formula is unsatisfiable. -/
theorem shg_unsat_cinstance_spec {L : Language}
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (hConst : Nonempty L.constSymbols)
    (hUnsat : ¬ satisfiableN A) :
    (shg_unsat_cinstance spec A hSource hConst hUnsat).source = SK spec ∧
    CInstance.WellFormed
      (shg_unsat_cinstance spec A hSource hConst hUnsat) ∧
    ¬ satisfiableN
      (shg_unsat_cinstance spec A hSource hConst hUnsat).toFormula := by
  unfold shg_unsat_cinstance
  exact shg_unsat_cinstance_seed_spec spec A hSource _ hUnsat

-- ===================================================================
-- Theorem 7.6.1 (helper): closed terms evaluate assignment-independently
-- ===================================================================



-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.Herbrand.SHGTheorem.Main.SHG
/-- Helper: a closed term is free for any variable in any formula. -/
theorem isFreeForN_of_closed {L : Language}
    (t : Term L) (hClosed : LCS.FirstOrder.Basic.Term.isClosed t)
    (x : Nat) (A : FormulaN L) :
    isFreeForN t x A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => simp [isFreeForN]
  | eq_ _ _ _ => simp [isFreeForN]
  | neg _ ih => simp [isFreeForN]; exact ih
  | conj _ _ ihA ihB => simp [isFreeForN]; exact ⟨ihA, ihB⟩
  | disj _ _ ihA ihB => simp [isFreeForN]; exact ⟨ihA, ihB⟩
  | impl _ _ ihA ihB => simp [isFreeForN]; exact ⟨ihA, ihB⟩
  | all y _ ih =>
    simp [isFreeForN]
    by_cases hxy : x = y
    · left; exact hxy
    · right
      refine ⟨?_, ih⟩
      intro hy
      rw [hClosed] at hy
      exact hy
  | ex y _ ih =>
    simp [isFreeForN]
    by_cases hxy : x = y
    · left; exact hxy
    · right
      refine ⟨?_, ih⟩
      intro hy
      rw [hClosed] at hy
      exact hy

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.Herbrand.SHGTheorem.Main.SHG
/-- Helper: for a closed term `t`, the evaluation of `A[t/x]` at
`s` equals the evaluation of `A` at `s[x := termEval M s t]`. -/
theorem formulaSubstEval_closed {L : Language} {M : Structure L}
    (A : FormulaN L) (t : Term L) (x : Nat)
    (hClosed : LCS.FirstOrder.Basic.Term.isClosed t)
    (s : Assignment M) :
    formulaEvalN M (formulaSubstN A t x) s ↔
    formulaEvalN M A (assignUpdate s x (termEval M s t)) :=
-- BEGIN PROOF
  formulaSubstEvalDirectN s A t x (isFreeForN_of_closed t hClosed x A)

end LCS.Herbrand.SHGTheorem.Main
end

