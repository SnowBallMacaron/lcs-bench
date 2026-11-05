import LCS.SLD.Propositional.Part1

section

namespace LCS.SLD.Propositional

open LCS.Resolution.GCNF

open LCS.SLD.SLDForm

proof_of sldResolutionMethod_unsatisfiable := by
  -- REPAIR(T9-31): proof pending — propagate satisfaction along the validated trace to its empty endpoint
  sorry

proof_of sldRefutation_continueWithSelectedAtom := by
  -- REPAIR(T9-32): proof pending — reorder a successful suffix while preserving the original inputs and prefix
  sorry

proof_of exMultiGoal_distinct_singleGoal_provable := by
  -- REPAIR(T9-33): proof pending — certify GCNF provability of the common input and both distinct one-goal restrictions
  sorry

proof_of exLeftSubtree_linearize_eq := by
  -- REPAIR(T9-50): proof pending — evaluate the exact left subtree linearization
  sorry

proof_of exRightSubtree_linearize_eq := by
  -- REPAIR(T9-50): proof pending — evaluate the exact right subtree linearization
  sorry

proof_of exSLDFormProof_linearize_eq := by
  -- REPAIR(T9-50): proof pending — evaluate the exact full-tree linearization
  sorry

proof_of exLinearizationResult_eq := by
  exact ⟨exSLDFormProof_linearize_eq,
    of_decide_eq_true exLinearizationConcatenation_check⟩

proof_of sldDerivation_isLinearInput := by
  refine ⟨by simp [SLDDerivation.inputUses], ?_⟩
  intro i
  refine ⟨by simp [SLDDerivation.inputUses], (d.stepValid i).1, ?_⟩
  rw [(d.stepValid i).2.2]
  exact resolveStep_isResolvent _ _ _
    (d.definiteValid _ (d.stepValid i).1) (d.stepValid i).2.1


proof_of SLDDerivation.toResolutionDAG_exists := by
  refine ⟨d.resolutionGraph, rfl, ?_⟩
  -- REPAIR(T9-30): proof pending
  -- Certify this concrete table's resolution rows, reachability and endpoint.
  sorry


proof_of exMultiGoalRefutation1_clauses_subset := by
  -- BEGIN PROOF
    change ∀ C, exMultiGoalRefutation1.definiteClauses C → C ∈ exMultiGoalClauseSet
    simp [exMultiGoalRefutation1, exMultiGoalClauseSet]


proof_of exSLDRefutation_isRefutation := by
  -- BEGIN PROOF
    unfold isSLDRefutation exSLDRefutation exLinearizationResult
    simp [List.getLast]


proof_of exMultiGoalRefutation1_isRefutation := by
  -- BEGIN PROOF
    unfold isSLDRefutation exMultiGoalRefutation1
    simp [List.getLast]


proof_of exMultiGoalRefutation2_isRefutation := by
  -- BEGIN PROOF
    unfold isSLDRefutation exMultiGoalRefutation2
    simp [List.getLast]






helper /-- A goal clause cannot be in the image of clauseWithLiteral · (pos P),
    because clauseWithLiteral inserts pos P into the clause, contradicting
    the all-negative property of goal clauses. -/
theorem goal_not_in_mapset_pos
    (Gamma As : ClauseSequent) (P : Nat) (goal : Clause)
    (hGoal : goal ∈ Finset.union Gamma
      (ClauseSequent.mapSet As (fun A => clauseWithLiteral A (Literal.pos P))))
    (hGoalPred : isGoalClause goal) :
    goal ∈ Gamma := by
-- BEGIN PROOF
  rw [Finset.mem_union] at hGoal
  rcases hGoal with hG | hMap
  · exact hG
  · exfalso
    obtain ⟨A, _, rfl⟩ := (mem_image_iff _ _ _).mp hMap
    have := hGoalPred.2 (Literal.pos P)
      ((Finset.mem_insert_exp (Literal.pos P) (Literal.pos P) A).mpr (Or.inl rfl))
    simp at this



helper /-- In the pos P rule case, clauses in Gamma1 ∪ Cs inherit the
    definite/goal property from S. Elements of Gamma1 are in S (via
    hG1Sub). Elements of Cs are pre-images under clauseWithLiteral · (pos P);
    if they have no positive literal, they are goal clauses; if they have
    a positive literal, it must be pos P (by Horn), making them definite. -/
theorem defOrGoal_subtree_pos
    (Gamma As Cs Gamma1 : ClauseSequent) (P : Nat)
    (hAsOrd : As.isOrdinary)
    (hCsSub : Finset.Subset Cs As)
    (hG1Sub : Finset.Subset Gamma1
      (Finset.union Gamma (ClauseSequent.mapSet As
        (fun A => clauseWithLiteral A (Literal.pos P)))))
    (hDef : ∀ C ∈ Finset.union Gamma
      (ClauseSequent.mapSet As
        (fun A => clauseWithLiteral A (Literal.pos P))),
      isDefiniteClause C ∨ isGoalClause C) :
    ∀ C ∈ Finset.union Gamma1 Cs,
      isDefiniteClause C ∨ isGoalClause C := by
  intro C hC
  rcases Finset.mem_union.mp hC with hG1 | hCs
  · exact hDef C (hG1Sub C hG1)
  · have hCWLInS : clauseWithLiteral C (Literal.pos P) ∈
        Finset.union Gamma (ClauseSequent.mapSet As
          (fun A => clauseWithLiteral A (Literal.pos P))) :=
      Finset.mem_union.mpr (Or.inr ((mem_image_iff _ _ _).mpr
        ⟨C, hCsSub C hCs, rfl⟩))
    have hHorn := (hDef _ hCWLInS).elim And.left And.left
    have hHornC := LCS.SLD.SLDForm.Completeness.isHornClause_of_subset
      _ C hHorn (fun l hl => Finset.mem_insert.mpr (Or.inr hl))
      (hAsOrd C (hCsSub C hCs))
    by_cases hPos : ∃ P, Literal.pos P ∈ C
    · exact Or.inl ⟨hHornC, hPos⟩
    · apply Or.inr
      refine ⟨hHornC, ?_⟩
      intro l hl
      cases l with
      | neg _ => trivial
      | pos P => exact False.elim (hPos ⟨P, hl⟩)

helper /-- In the neg Q rule case (left subtree), clauses in Gamma1 ∪ Cs inherit
    the definite/goal property. Elements of Gamma1 are in S. Elements of
    Cs have clauseWithLiteral C (neg Q) in S; since neg Q is negative,
    the positive literals of C are exactly those of clauseWithLiteral C (neg Q). -/
theorem defOrGoal_subtree_neg_left
    (Gamma As Cs Gamma1 : ClauseSequent) (Q : Nat)
    (hAsOrd : As.isOrdinary)
    (hCsSub : Finset.Subset Cs As)
    (hG1Sub : Finset.Subset Gamma1
      (Finset.union Gamma (ClauseSequent.mapSet As
        (fun A => clauseWithLiteral A (Literal.neg Q)))))
    (hDef : ∀ C ∈ Finset.union Gamma
      (ClauseSequent.mapSet As
        (fun A => clauseWithLiteral A (Literal.neg Q))),
      isDefiniteClause C ∨ isGoalClause C) :
    ∀ C ∈ Finset.union Gamma1 Cs,
      isDefiniteClause C ∨ isGoalClause C := by
  intro C hC
  rcases Finset.mem_union.mp hC with hG1 | hCs
  · exact hDef C (hG1Sub C hG1)
  · have hCWLInS : clauseWithLiteral C (Literal.neg Q) ∈
        Finset.union Gamma (ClauseSequent.mapSet As
          (fun A => clauseWithLiteral A (Literal.neg Q))) :=
      Finset.mem_union.mpr (Or.inr ((mem_image_iff _ _ _).mpr
        ⟨C, hCsSub C hCs, rfl⟩))
    have hHorn := (hDef _ hCWLInS).elim And.left And.left
    have hHornC := LCS.SLD.SLDForm.Completeness.isHornClause_of_subset
      _ C hHorn (fun l hl => Finset.mem_insert.mpr (Or.inr hl))
      (hAsOrd C (hCsSub C hCs))
    by_cases hPos : ∃ P, Literal.pos P ∈ C
    · exact Or.inl ⟨hHornC, hPos⟩
    · apply Or.inr
      refine ⟨hHornC, ?_⟩
      intro l hl
      cases l with
      | neg _ => trivial
      | pos P => exact False.elim (hPos ⟨P, hl⟩)

helper /-- In the neg Q rule case (right subtree), clauses in Gamma2 ∪ {{neg Q}}
    inherit the definite/goal property. Elements of Gamma2 are in S.
    The singleton {neg Q} is a goal clause. -/
theorem defOrGoal_subtree_neg_right
    (Gamma As Gamma2 : ClauseSequent) (Q : Nat)
    (hG2Sub : Finset.Subset Gamma2
      (Finset.union Gamma (ClauseSequent.mapSet As
        (fun A => clauseWithLiteral A (Literal.neg Q)))))
    (hDef : ∀ C ∈ Finset.union Gamma
      (ClauseSequent.mapSet As
        (fun A => clauseWithLiteral A (Literal.neg Q))),
      isDefiniteClause C ∨ isGoalClause C) :
    ∀ C ∈ Finset.union Gamma2
      (ClauseSequent.single (Clause.single (Literal.neg Q))),
      isDefiniteClause C ∨ isGoalClause C := by
-- BEGIN PROOF
  intro C hC
  rw [Finset.mem_union] at hC
  rcases hC with hG2 | hSing
  · exact hDef C (hG2Sub C hG2)
  · right
    have hCeq : C = Clause.single (Literal.neg Q) :=
      (Finset.mem_singleton _ _).mp hSing
    rw [hCeq]; exact isGoalClause_single_neg' Q



helper /-- The last element of the linearization is always the empty clause. -/
theorem linearize_last_empty : {S : ClauseSequent} → (T : GCNFProofTree S) →
    (linearize T).getLast (linearize_nonempty T) = Clause.empty
  | _, .axiom_ _S _hOrd _hTriv => by simp [linearize, List.getLast]
  | _, .rule Gamma As B _Cs _ _ _hGammaOrd _hAsOrd leftTree rightTree _hNe _hSub _ _ => by
    classical
    by_cases hAx : ClauseSequent.isTrivial (Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)))
    · simp [linearize, hAx, List.getLast]
    have ihLeft := linearize_last_empty leftTree
    have ihRight := linearize_last_empty rightTree
    cases B with
    | pos _P =>
      simp only [linearize, dif_neg hAx]
      rw [List.getLast_cons (linearize_nonempty leftTree)]
      exact ihLeft
    | neg _ =>
      simp only [linearize, dif_neg hAx]
      rw [List.getLast_append_of_ne_nil _ (linearize_nonempty rightTree)]
      exact ihRight

helper /-- Resolving a singleton negative clause {neg P} against the unit definite
    clause {pos P} with selected atom P yields the empty clause. -/
theorem resolveStep_singleton_unit (P : Nat) :
    resolveStep (Clause.single (Literal.neg P)) P (Clause.single (Literal.pos P)) =
      Clause.empty := by
-- BEGIN PROOF
  unfold resolveStep
  apply Finset.ext; intro l
  simp only [Clause.remove, Clause.union, Clause.single, Clause.empty]
  constructor
  · intro hl; rw [Finset.mem_union] at hl
    rcases hl with hE | hF
    · rw [Finset.mem_erase] at hE
      exact absurd ((Finset.mem_singleton _ _).mp hE.1) hE.2
    · rw [Finset.mem_filter] at hF
      have := (Finset.mem_singleton _ _).mp hF.1; subst this; simp at hF
  · intro hl; exact ((Finset.mem_empty l).mp hl).elim



helper /-- A singleton positive clause {pos P} is a definite clause. -/
theorem isDefiniteClause_single_pos (P : Nat) :
    isDefiniteClause (Clause.single (Literal.pos P)) :=
  ⟨LCS.SLD.SLDForm.Completeness.isHornClause_single _,
    ⟨P, (Finset.mem_singleton _ _).mpr rfl⟩⟩

helper /-- Resolving {neg P} against {pos P} ∪ head (where head is all-negative)
    yields head. Used in the resolution rule case of linearize_yields_sld_refutation. -/
theorem resolveStep_singleton_neg_insert' (P : Nat) (head : Clause)
    (h : ∀ l ∈ head, match l with | Literal.neg _ => True | _ => False) :
    resolveStep (Clause.single (Literal.neg P)) P (Finset.insert (Literal.pos P) head)
    = head := by
  unfold resolveStep
  simp only [Clause.single, Clause.remove, Clause.union]
  apply Finset.ext; intro l; constructor
  · intro hl; rw [Finset.mem_union] at hl
    rcases hl with hE | hF
    · rw [Finset.mem_erase] at hE
      exact absurd ((Finset.mem_singleton _ _).mp hE.1) hE.2
    · rw [Finset.mem_filter] at hF; rw [Finset.mem_insert] at hF
      rcases hF with ⟨rfl | hmem, hf⟩
      · exact absurd hf (by simp)
      · exact hmem
  · intro hl; rw [Finset.mem_union]; right; rw [Finset.mem_filter]
    exact ⟨(Finset.mem_insert_exp _ _ _).mpr (Or.inr hl),
      by have := h l hl; cases l with | neg _ => rfl | pos _ => simp at this⟩

helper /-- Inserting a positive literal into an all-negative clause yields a definite clause. -/
theorem insert_pos_allNeg_isDefinite (P : Nat) (head : Clause)
    (h : ∀ l ∈ head, match l with | Literal.neg _ => True | _ => False) :
    isDefiniteClause (Finset.insert (Literal.pos P) head) := by
-- BEGIN PROOF
  constructor
  · refine ⟨Clause.ordinary_of_mem (Finset.mem_insert.mpr (Or.inl rfl)), ?_⟩
    intro Q R hQ hR
    rw [Finset.mem_insert] at hQ hR
    rcases hQ with hQ | hQ <;> rcases hR with hR | hR
    · have := Literal.pos.inj hQ; have := Literal.pos.inj hR; omega
    · exact absurd (h _ hR) (by simp)
    · exact absurd (h _ hQ) (by simp)
    · exact absurd (h _ hQ) (by simp)
  · exact ⟨P, (Finset.mem_insert_exp _ _ _).mpr (Or.inl rfl)⟩

helper /-- List.get at index 0 equals List.head. -/
theorem list_get_zero_eq_head (l : List α) (hne : l ≠ []) (h0 : 0 < l.length) :
    l.get ⟨0, h0⟩ = l.head hne := by
-- BEGIN PROOF
  cases l with | nil => exact absurd rfl hne | cons a rest => rfl

end LCS.SLD.Propositional

end
