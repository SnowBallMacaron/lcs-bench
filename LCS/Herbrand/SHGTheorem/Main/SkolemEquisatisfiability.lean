import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.SHGTheorem.Herbrand
import LCS.Herbrand.SHGTheorem.Main.SkolemFormForward
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

-- ===================================================================
-- Lemma 7.6.3 (contextual witness-selection infrastructure)
-- ===================================================================

/-- Interpretations of the exact finite family of Skolem symbols over
the carrier of a fixed base structure. -/
abbrev SkolemInterpretation {L : Language}
    (S : SkolemSpec L) (M : Structure L) :=
  (i : Fin S.n) →
    (Fin (S.skolemRank i) → M.carrier) → M.carrier

/-- Expansion determined by a complete interpretation of the exact
Skolem-symbol family. -/
noncomputable def interpretationExpansion {L : Language}
    (S : SkolemSpec L) (M : Structure L)
    (K : SkolemInterpretation S M) : Structure S.language :=
  { carrier := M.carrier
    carrierNonempty := M.carrierNonempty
    interpFunc := fun f args =>
      match f with
      | Sum.inl g => M.interpFunc g args
      | Sum.inr i => K i.val args
    interpConst := fun
      | Sum.inl c => M.interpConst c
      | Sum.inr i => K i.val (fun j => Fin.elim0 (Fin.cast i.property j))
    interpPred := M.interpPred }

theorem interpretationExpansion_isExpansion {L : Language}
    (S : SkolemSpec L) (M : Structure L)
    (K : SkolemInterpretation S M) :
    isExpansion L S.n S.skolemRank M
      (interpretationExpansion S M K) :=
  ⟨rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => Iff.rfl⟩

/-- Every Skolem constant or function head in a term belongs to `available`. -/
def skolemTermSupported {L : Language} (S : SkolemSpec L)
    (available : List (Fin S.n)) : Term S.language → Prop
  | .var _ => True
  | .const (Sum.inl _) => True
  | .const (Sum.inr i) => i.val ∈ available
  | .func (Sum.inl _) ts =>
      ∀ j, skolemTermSupported S available (ts j)
  | .func (Sum.inr i) ts =>
      i.val ∈ available ∧
      ∀ j, skolemTermSupported S available (ts j)

/-- Every Skolem head occurring in a formula belongs to `available`. -/
def skolemFormulaSupported {L : Language} (S : SkolemSpec L)
    (available : List (Fin S.n)) : FormulaN S.language → Prop
  | .predN _ ts =>
      ∀ j, skolemTermSupported S available (ts j)
  | .eq_ _ t₁ t₂ =>
      skolemTermSupported S available t₁ ∧
      skolemTermSupported S available t₂
  | .neg A => skolemFormulaSupported S available A
  | .conj A B =>
      skolemFormulaSupported S available A ∧
      skolemFormulaSupported S available B
  | .disj A B =>
      skolemFormulaSupported S available A ∧
      skolemFormulaSupported S available B
  | .impl A B =>
      skolemFormulaSupported S available A ∧
      skolemFormulaSupported S available B
  | .all _ A => skolemFormulaSupported S available A
  | .ex _ A => skolemFormulaSupported S available A

theorem skolemTermSupported_mono {L : Language}
    (S : SkolemSpec L) {xs ys : List (Fin S.n)}
    (hSub : ∀ i, i ∈ xs → i ∈ ys) :
    ∀ t, skolemTermSupported S xs t →
      skolemTermSupported S ys t := by
  intro t
  induction t with
  | var _ => exact fun _ => trivial
  | const c =>
    cases c with
    | inl _ => exact fun _ => trivial
    | inr i => exact hSub i.val
  | func f ts ih =>
    cases f with
    | inl f =>
      intro h j
      exact ih j (h j)
    | inr i =>
      intro h
      exact ⟨hSub i.val h.1, fun j => ih j (h.2 j)⟩

theorem skolemFormulaSupported_mono {L : Language}
    (S : SkolemSpec L) {xs ys : List (Fin S.n)}
    (hSub : ∀ i, i ∈ xs → i ∈ ys) :
    ∀ A, skolemFormulaSupported S xs A →
      skolemFormulaSupported S ys A := by
  intro A
  induction A with
  | predN _ ts =>
    intro h j
    exact skolemTermSupported_mono S hSub (ts j) (h j)
  | eq_ _ t₁ t₂ =>
    intro h
    exact
      ⟨skolemTermSupported_mono S hSub t₁ h.1,
       skolemTermSupported_mono S hSub t₂ h.2⟩
  | neg A ih => exact ih
  | conj A B ihA ihB =>
    intro h
    exact ⟨ihA h.1, ihB h.2⟩
  | disj A B ihA ihB =>
    intro h
    exact ⟨ihA h.1, ihB h.2⟩
  | impl A B ihA ihB =>
    intro h
    exact ⟨ihA h.1, ihB h.2⟩
  | all _ A ih => exact ih
  | ex _ A ih => exact ih

theorem liftTermSkolem_supported_nil {L : Language}
    (S : SkolemSpec L) :
    ∀ t : Term L,
      skolemTermSupported S [] (liftTermSkolem t) := by
  intro t
  induction t with
  | var _ => trivial
  | const _ => trivial
  | func _ ts ih =>
    exact fun j => ih j

theorem liftFormulaSkolem_supported_nil {L : Language}
    (S : SkolemSpec L) :
    ∀ A : FormulaN L,
      skolemFormulaSupported S [] (liftFormulaSkolem A) := by
  intro A
  induction A with
  | predN _ ts =>
    exact fun j => liftTermSkolem_supported_nil S (ts j)
  | eq_ _ t₁ t₂ =>
    exact
      ⟨liftTermSkolem_supported_nil S t₁,
       liftTermSkolem_supported_nil S t₂⟩
  | neg _ ih => exact ih
  | conj _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | disj _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | impl _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | all _ _ ih => exact ih
  | ex _ _ ih => exact ih

theorem exactSkolemTerm_supported {L : Language}
    (S : SkolemSpec L) (i : Fin S.n)
    (available : List (Fin S.n)) (hi : i ∈ available) :
    skolemTermSupported S available (exactSkolemTerm S i) := by
  unfold exactSkolemTerm
  split
  · exact hi
  · exact ⟨hi, fun _ => trivial⟩

theorem termSubst_supported {L : Language}
    (S : SkolemSpec L) (available : List (Fin S.n)) :
    ∀ r t : Term S.language, skolemTermSupported S available r →
      skolemTermSupported S available t →
      ∀ x, skolemTermSupported S available (termSubst r t x) := by
  intro r
  induction r with
  | var y =>
    intro t _ ht x
    simp only [termSubst]
    split
    · exact ht
    · trivial
  | const c =>
    intro t hr _ x
    exact hr
  | func f ts ih =>
    intro t hr ht x
    cases f with
    | inl f =>
      intro j
      exact ih j t (hr j) ht x
    | inr i =>
      exact ⟨hr.1, fun j => ih j t (hr.2 j) ht x⟩

theorem formulaSubstN_supported {L : Language}
    (S : SkolemSpec L) (available : List (Fin S.n)) :
    ∀ A t x,
      skolemFormulaSupported S available A →
      skolemTermSupported S available t →
      skolemFormulaSupported S available (formulaSubstN A t x) := by
  intro A
  induction A with
  | predN P ts =>
    intro t x hA ht j
    exact termSubst_supported S available (ts j) t (hA j) ht x
  | eq_ h t₁ t₂ =>
    intro t x hA ht
    exact
      ⟨termSubst_supported S available t₁ t hA.1 ht x,
       termSubst_supported S available t₂ t hA.2 ht x⟩
  | neg A ih =>
    intro t x hA ht
    exact ih t x hA ht
  | conj A B ihA ihB =>
    intro t x hA ht
    exact ⟨ihA t x hA.1 ht, ihB t x hA.2 ht⟩
  | disj A B ihA ihB =>
    intro t x hA ht
    exact ⟨ihA t x hA.1 ht, ihB t x hA.2 ht⟩
  | impl A B ihA ihB =>
    intro t x hA ht
    exact ⟨ihA t x hA.1 ht, ihB t x hA.2 ht⟩
  | all y A ih =>
    intro t x hA ht
    simp only [formulaSubstN]
    split
    · exact ih t x hA ht
    · exact hA
  | ex y A ih =>
    intro t x hA ht
    simp only [formulaSubstN]
    split
    · exact ih t x hA ht
    · exact hA

/-- Pointwise agreement of two Skolem interpretations on a list of
allocated symbols. -/
def skolemInterpretationsAgreeOn {L : Language}
    (S : SkolemSpec L) (M : Structure L)
    (available : List (Fin S.n))
    (K K' : SkolemInterpretation S M) : Prop :=
  ∀ i, i ∈ available → ∀ args, K i args = K' i args

theorem termEval_interpretationExpansion_eq {L : Language}
    (S : SkolemSpec L) (M : Structure L)
    (available : List (Fin S.n))
    (K K' : SkolemInterpretation S M)
    (hAgree : skolemInterpretationsAgreeOn S M available K K')
    (s : Nat → M.carrier) :
    ∀ t, skolemTermSupported S available t →
      termEval (interpretationExpansion S M K) s t =
        termEval (interpretationExpansion S M K') s t := by
  intro t
  induction t with
  | var _ => exact fun _ => rfl
  | const c =>
    cases c with
    | inl _ => exact fun _ => rfl
    | inr i => exact fun h => hAgree i.val h _
  | func f ts ih =>
    cases f with
    | inl f =>
      intro h
      simp only [termEval, interpretationExpansion]
      congr 1
      funext j
      exact ih j (h j)
    | inr i =>
      intro h
      simp only [termEval, interpretationExpansion]
      calc
        K i.val (fun j => termEval (interpretationExpansion S M K) s (ts j)) =
            K i.val (fun j => termEval (interpretationExpansion S M K') s (ts j)) := by
              congr 1
              funext j
              exact ih j (h.2 j)
        _ = K' i.val
            (fun j => termEval (interpretationExpansion S M K') s (ts j)) :=
              hAgree i.val h.1 _

theorem formulaEvalN_interpretationExpansion_iff {L : Language}
    (S : SkolemSpec L) (M : Structure L)
    (available : List (Fin S.n))
    (K K' : SkolemInterpretation S M)
    (hAgree : skolemInterpretationsAgreeOn S M available K K') :
    ∀ (A : FormulaN S.language),
      skolemFormulaSupported S available A →
      ∀ s : Nat → M.carrier,
        formulaEvalN (interpretationExpansion S M K) A s ↔
          formulaEvalN (interpretationExpansion S M K') A s := by
  intro A
  induction A with
  | predN P ts =>
    intro h s
    simp only [formulaEvalN]
    have hArgs :
        (fun j => termEval (interpretationExpansion S M K) s (ts j)) =
          (fun j => termEval (interpretationExpansion S M K') s (ts j)) := by
      funext j
      exact termEval_interpretationExpansion_eq
        S M available K K' hAgree s (ts j) (h j)
    rw [hArgs]
    rfl
  | eq_ h t₁ t₂ =>
    intro hSupport s
    simp only [formulaEvalN]
    rw [termEval_interpretationExpansion_eq
          S M available K K' hAgree s t₁ hSupport.1,
        termEval_interpretationExpansion_eq
          S M available K K' hAgree s t₂ hSupport.2]
    exact Iff.rfl
  | neg A ih =>
    intro h s
    exact not_congr (ih h s)
  | conj A B ihA ihB =>
    intro h s
    exact and_congr (ihA h.1 s) (ihB h.2 s)
  | disj A B ihA ihB =>
    intro h s
    exact or_congr (ihA h.1 s) (ihB h.2 s)
  | impl A B ihA ihB =>
    intro h s
    exact imp_congr (ihA h.1 s) (ihB h.2 s)
  | all x A ih =>
    intro h s
    exact forall_congr' fun a => ih h (assignUpdate s x a)
  | ex x A ih =>
    intro h s
    exact exists_congr fun a => ih h (assignUpdate s x a)

theorem not_mem_right_of_nodup_append {α : Type}
    {xs ys : List α} (h : (xs ++ ys).Nodup)
    {a : α} (ha : a ∈ xs) : a ∉ ys := by
  intro ha'
  exact (List.nodup_append.mp h).2.2 a ha a ha' rfl

theorem not_mem_left_of_nodup_append {α : Type}
    {xs ys : List α} (h : (xs ++ ys).Nodup)
    {a : α} (ha : a ∈ ys) : a ∉ xs := by
  intro ha'
  exact (List.nodup_append.mp h).2.2 a ha' a ha rfl

theorem skolemInterpretationsAgreeOn_of_frame {L : Language}
    (S : SkolemSpec L) (M : Structure L)
    {available changed : List (Fin S.n)}
    {K K' : SkolemInterpretation S M}
    (hFrame : ∀ i, i ∉ changed → ∀ args, K' i args = K i args)
    (hDisjoint : ∀ i, i ∈ available → i ∉ changed) :
    skolemInterpretationsAgreeOn S M available K K' := by
  intro i hi args
  exact (hFrame i (hDisjoint i hi) args).symm

/-- Values of the exact ordered universal scope under an assignment. -/
def exactScopeValues {L : Language}
    (S : SkolemSpec L) (M : Structure L) (i : Fin S.n)
    (s : Nat → M.carrier) :
    Fin (S.skolemRank i) → M.carrier :=
  fun k =>
    s ((S.skolemScope i).get
      ⟨k.val, by
        simpa [SkolemSpec.skolemRank] using k.isLt⟩)

theorem termEval_exactSkolemTerm {L : Language}
    (S : SkolemSpec L) (M : Structure L)
    (K : SkolemInterpretation S M) (i : Fin S.n)
    (s : Nat → M.carrier) :
    termEval (interpretationExpansion S M K) s
        (exactSkolemTerm S i) =
      K i (exactScopeValues S M i s) := by
  unfold exactSkolemTerm
  split
  · rename_i hRank
    simp only [termEval, interpretationExpansion]
    apply congrArg (K i)
    funext j
    exact Fin.elim0 (Fin.cast hRank j)
  · rfl

theorem skolemSpec_indices_nodup {L : Language}
    (S : SkolemSpec L) : S.indices.Nodup := by
  unfold SkolemSpec.indices
  change List.Pairwise (fun x₁ x₂ : Fin S.n => x₁ ≠ x₂)
    (List.ofFn fun i : Fin S.n => i)
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [List.getElem_ofFn, List.getElem_ofFn]
  intro hEq
  have hVal := congrArg Fin.val hEq
  simp at hVal
  omega

/-- Every computed allocation is backed by an existential descriptor;
the filter-map representation cannot allocate any other constructor. -/
theorem skolemAllocation_isExistential {L : Language}
    (S : SkolemSpec L) (i : Fin S.n) :
    ∃ x D, (S.allocation i).1 = FormulaN.ex x D := by
  have hMem : S.allocation i ∈ S.allocations :=
    List.get_mem S.allocations i
  unfold SkolemSpec.allocations existentialDescriptors
    existentialDescriptorsAux at hMem
  obtain ⟨pair, _hPairMem, hPair⟩ := List.mem_filterMap.mp hMem
  rcases pair with ⟨F, scope⟩
  cases F with
  | predN _ _ => simp at hPair
  | eq_ _ _ _ => simp at hPair
  | neg _ => simp at hPair
  | conj _ _ => simp at hPair
  | disj _ _ => simp at hPair
  | impl _ _ => simp at hPair
  | all _ _ => simp at hPair
  | ex x D =>
    have hEq :
        (FormulaN.ex x D, scope) = S.allocation i :=
      Option.some.inj hPair
    exact ⟨x, D, by rw [← hEq]⟩

/-- Proof-backed binder/body map used to seed the public
`witnessSelectingExpansion`. -/
noncomputable def skolemAllocationBinderBody {L : Language}
    (S : SkolemSpec L) (i : Fin S.n) : Nat × FormulaN L :=
  let h := skolemAllocation_isExistential S i
  (Classical.choose h, Classical.choose (Classical.choose_spec h))

/-- Context-strengthened semantic invariant for the backward direction.
`processed` records the Skolem symbols already fixed by enclosing or
earlier occurrences.  The returned interpretation changes only
`indices`, so later disjoint traversal segments cannot invalidate an
earlier result.  The guard `P` permits disjunction branches to select
witnesses pointwise in their current universal-scope values. -/
theorem skolemFormExactAux_backward_semantics {L : Language}
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

end LCS.Herbrand.SHGTheorem.Main
end
