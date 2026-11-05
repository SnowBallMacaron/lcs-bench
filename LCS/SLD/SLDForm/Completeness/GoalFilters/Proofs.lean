import LCS.SLD.SLDForm.Completeness.GoalFilters

section

namespace LCS.SLD.SLDForm.Completeness

open LCS.Resolution.GCNF

open LCS.SLD.SLDForm

open LCS.SLD.SLDForm.Occurrence

helper /-- Clauses in goalFilter are goal clauses. -/
theorem goalFilter_goal (S : ClauseSequent) :
    ∀ C ∈ goalFilter S, isGoalClause C := by
-- BEGIN PROOF
  intro C hC
  exact isGoalClauseB_sound C ((Finset.mem_filter_exp _ _ _).mp hC).2

helper /-- Clauses in defFilter are definite clauses with ≥2 literals. -/
theorem defFilter_definite (S : ClauseSequent)
    (hHorn : ∀ C ∈ S, isHornClause C) (hNe : ∀ C ∈ S, ∃ L : Literal, L ∈ C) :
    ∀ C ∈ defFilter S, isDefiniteClause C ∧ (∃ l₁ l₂, l₁ ∈ C ∧ l₂ ∈ C ∧ l₁ ≠ l₂) := by
-- BEGIN PROOF
  intro C hC
  have ⟨hCS, hPred⟩ := (Finset.mem_filter_exp _ _ _).mp hC
  have hNotGoal : isGoalClauseB C = false := by
    cases hv : isGoalClauseB C
    · rfl
    · simp [hv] at hPred
  have hBig : 1 < C.card := by
    have hD : decide (1 < C.card) = true := by
      cases hv : decide (1 < C.card) with
      | true => rfl
      | false => simp [hNotGoal, hv] at hPred
    exact of_decide_eq_true hD
  -- C is Horn, not all-negative, card > 1 → has exactly one positive + negatives
  have hH := hHorn C hCS
  -- Not all-negative means ∃ positive literal
  have hExPos : ∃ P, Literal.pos P ∈ C := Classical.byContradiction fun hNo => by
    have : isGoalClauseB C = true := by
      rw [isGoalClauseB, Bool.and_eq_true]
      refine ⟨decide_eq_true (hHorn C hCS).1, ?_⟩
      apply Multiset.all_eq_true.mpr; intro l hl
      match l with
      | .neg _ => rfl
      | .pos P => exact absurd (⟨P, hl⟩ : ∃ P, Literal.pos P ∈ C) hNo
    rw [this] at hNotGoal; exact absurd hNotGoal (by decide)
  obtain ⟨P, hP⟩ := hExPos
  constructor
  · exact ⟨hH, ⟨P, hP⟩⟩
  · -- card > 1 → ∃ two distinct elements
    obtain ⟨L, hL⟩ := hNe C hCS
    by_cases hLeq : L = Literal.pos P
    · subst hLeq
      have hExOther : ∃ M, M ∈ C ∧ M ≠ Literal.pos P := Classical.byContradiction fun hAll => by
        have hAll' : ∀ M ∈ C, M = Literal.pos P :=
          fun M hM => Classical.byContradiction fun hne => hAll ⟨M, hM, hne⟩
        have hCard1 : C = Clause.single (Literal.pos P) := by
          apply Finset.ext; intro l
          exact ⟨fun hl => (Finset.mem_singleton _ _).mpr (hAll' l hl),
                 fun hl => (Finset.mem_singleton _ _).mp hl ▸ hP⟩
        have : C.card = 1 := by
          rw [hCard1]; unfold Clause.single Finset.singleton Finset.card Multiset.card; rfl
        omega
      obtain ⟨M, hM, hMne⟩ := hExOther
      exact ⟨M, Literal.pos P, hM, hP, hMne⟩
    · exact ⟨L, Literal.pos P, hL, hP, hLeq⟩

helper /-- goalFilter S converted to a list via the noncomputable `toList`. -/
noncomputable def goalFilterList (S : ClauseSequent) : List Clause := (goalFilter S).toList

helper /-- defFilter S converted to a list via the noncomputable `toList`. -/
noncomputable def defFilterList (S : ClauseSequent) : List Clause := (defFilter S).toList

helper /-- ofList of a Finset's toList gives back the Finset. -/
theorem ofList_toList_eq (s : ClauseSequent) : Finset.ofList s.toList = s := by
-- BEGIN PROOF
  apply Finset.ext; intro a; rw [Finset.mem_ofList]; exact Finset.mem_toList s a

helper /-- ofList of goalFilterList gives goalFilter. -/
theorem ofList_goalFilterList (S : ClauseSequent) :
    ClauseSequent.ofList (goalFilterList S) = goalFilter S := ofList_toList_eq _

helper /-- ofList of defFilterList gives defFilter. -/
theorem ofList_defFilterList (S : ClauseSequent) :
    ClauseSequent.ofList (defFilterList S) = defFilter S := ofList_toList_eq _

helper /-- goalFilterList is nonempty when S has a goal clause. -/
theorem goalFilterList_nonempty (S : ClauseSequent) (hEx : ∃ C ∈ S, isGoalClause C) :
    goalFilterList S ≠ [] := by
-- BEGIN PROOF
  obtain ⟨C, hCS, hG⟩ := hEx
  intro hEmpty
  have hCfilt : C ∈ goalFilter S :=
    (Finset.mem_filter_exp _ _ _).mpr ⟨hCS, isGoalClauseB_complete C hG⟩
  have hCtl : C ∈ (goalFilter S).toList := (Finset.mem_toList (goalFilter S) C).mpr hCfilt
  rw [show (goalFilter S).toList = goalFilterList S from rfl, hEmpty] at hCtl
  exact List.not_mem_nil hCtl

helper /-- Every clause in G ∪ As is Horn, given S' partition properties and IsStrictIWW data. -/
theorem left_subtree_horn
    (G As : ClauseSequent) (B : Literal)
    (J' : ClauseSequent) (goals' defs' : List Clause)
    (hJ' : ∀ C ∈ J', ∃ P : Nat, C = Clause.single (Literal.pos P))
    (hGoals' : ∀ C ∈ goals', isGoalClause C)
    (hDefs' : ∀ C ∈ defs', isDefiniteClause C ∧ (∃ l₁ l₂, l₁ ∈ C ∧ l₂ ∈ C ∧ l₁ ≠ l₂))
    (hAsOrd : As.isOrdinary)
    (hS' : Finset.union G (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)) =
      Finset.union (Finset.union J' (ClauseSequent.ofList defs')) (ClauseSequent.ofList goals')) :
    ∀ C ∈ Finset.union G As, isHornClause C := by
-- BEGIN PROOF
  intro C hC
  rw [Finset.mem_union] at hC
  rcases hC with hCG | hCA
  · -- C ∈ G → C ∈ S' → classified
    have hCS : C ∈ Finset.union G (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)) :=
      (Finset.mem_union_exp _ _ _).mpr (Or.inl hCG)
    rw [hS'] at hCS
    rw [Finset.mem_union] at hCS
    rcases hCS with hJD | hGoal
    · rw [Finset.mem_union] at hJD
      rcases hJD with hJ | hD
      · obtain ⟨P, hPeq⟩ := hJ' _ hJ; rw [hPeq]
        refine ⟨Clause.single_ordinary _, ?_⟩
        intro P' Q hP' hQ
        exact Literal.pos.inj ((Finset.mem_singleton _ _).mp hP' |>.trans
          ((Finset.mem_singleton _ _).mp hQ).symm)
      · exact (hDefs' _ ((Finset.mem_ofList_exp _ _).mp hD)).1.1
    · exact (hGoals' _ ((Finset.mem_ofList_exp _ _).mp hGoal)).1
  · -- C ∈ As → cwl(C, B) ∈ S' → cwl(C,B) is Horn → C ⊆ cwl(C,B) is Horn
    have hCwl : clauseWithLiteral C B ∈
        Finset.union G (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)) :=
      (Finset.mem_union_exp _ _ _).mpr (Or.inr ((mem_image_iff _ _ _).mpr ⟨C, hCA, rfl⟩))
    rw [hS'] at hCwl
    rw [Finset.mem_union] at hCwl
    have hHornCwl : isHornClause (clauseWithLiteral C B) := by
      rcases hCwl with hJD | hGoal
      · rw [Finset.mem_union] at hJD
        rcases hJD with hJ | hD
        · obtain ⟨P, hPeq⟩ := hJ' _ hJ
          rw [hPeq]; refine ⟨Clause.single_ordinary _, ?_⟩
          intro P' Q hP' hQ
          have := (Finset.mem_singleton _ _).mp hP'
          have := (Finset.mem_singleton _ _).mp hQ
          simp_all
        · exact (hDefs' _ ((Finset.mem_ofList_exp _ _).mp hD)).1.1
      · exact (hGoals' _ ((Finset.mem_ofList_exp _ _).mp hGoal)).1
    -- C ⊆ cwl(C, B), so Horn transfers
    refine ⟨hAsOrd C hCA, ?_⟩
    intro P Q hP hQ
    exact hHornCwl.2 P Q ((Finset.mem_insert_exp _ _ _).mpr (Or.inr hP))
      ((Finset.mem_insert_exp _ _ _).mpr (Or.inr hQ))

helper /-- Right subtree G ∪ {{B}} is all Horn. -/
theorem right_subtree_horn
    (G : ClauseSequent) (B : Literal) (As : ClauseSequent)
    (J' : ClauseSequent) (goals' defs' : List Clause)
    (hJ' : ∀ C ∈ J', ∃ P : Nat, C = Clause.single (Literal.pos P))
    (hGoals' : ∀ C ∈ goals', isGoalClause C)
    (hDefs' : ∀ C ∈ defs', isDefiniteClause C ∧ (∃ l₁ l₂, l₁ ∈ C ∧ l₂ ∈ C ∧ l₁ ≠ l₂))
    (hS' : Finset.union G (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)) =
      Finset.union (Finset.union J' (ClauseSequent.ofList defs')) (ClauseSequent.ofList goals')) :
    ∀ C ∈ Finset.union G (ClauseSequent.single (Clause.single B)), isHornClause C := by
-- BEGIN PROOF
  intro C hC
  rw [Finset.mem_union] at hC
  rcases hC with hCG | hCB
  · have hCS : C ∈ Finset.union G (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)) :=
      (Finset.mem_union_exp _ _ _).mpr (Or.inl hCG)
    rw [hS'] at hCS; rw [Finset.mem_union] at hCS
    rcases hCS with hJD | hGoal
    · rw [Finset.mem_union] at hJD
      rcases hJD with hJ | hD
      · obtain ⟨P, hPeq⟩ := hJ' _ hJ; rw [hPeq]
        refine ⟨Clause.single_ordinary _, ?_⟩
        intro P' Q hP' hQ
        exact Literal.pos.inj ((Finset.mem_singleton _ _).mp hP' |>.trans
          ((Finset.mem_singleton _ _).mp hQ).symm)
      · exact (hDefs' _ ((Finset.mem_ofList_exp _ _).mp hD)).1.1
    · exact (hGoals' _ ((Finset.mem_ofList_exp _ _).mp hGoal)).1
  · rw [mem_csingle] at hCB; subst hCB
    refine ⟨Clause.single_ordinary _, ?_⟩
    intro P Q hP hQ
    have hPeq := (Finset.mem_singleton _ _).mp hP
    have hQeq := (Finset.mem_singleton _ _).mp hQ
    -- hPeq : Literal.pos P = B, hQeq : Literal.pos Q = B
    -- So Literal.pos P = Literal.pos Q
    have := hPeq.trans hQeq.symm
    exact Literal.pos.inj this

helper /-- Left subtree has a goal clause. -/
theorem left_subtree_has_goal
    (G As : ClauseSequent) (B : Literal)
    (J' : ClauseSequent) (defs' : List Clause)
    (goals' : List Clause) (hGoalsNe' : goals' ≠ [])
    (hGoals' : ∀ C ∈ goals', isGoalClause C)
    (hS' : Finset.union G (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)) =
      Finset.union (Finset.union J' (ClauseSequent.ofList defs')) (ClauseSequent.ofList goals'))
    (hNonempty : ∀ C ∈ Finset.union G As, ∃ L : Literal, L ∈ C) :
    ∃ C ∈ Finset.union G As, isGoalClause C := by
-- BEGIN PROOF
  -- Either a goal from goals' is in G, or all goals are in mapSet → the A parts are goals
  cases goals' with
  | nil => exact absurd rfl hGoalsNe'
  | cons g gs =>
    have hgGoal := hGoals' g (List.mem_cons.mpr (Or.inl rfl))
    have hgS : g ∈ Finset.union G (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)) := by
      rw [hS']; exact (Finset.mem_union_exp _ _ _).mpr (Or.inr ((Finset.mem_ofList_exp _ _).mpr
        (List.mem_cons.mpr (Or.inl rfl))))
    rw [Finset.mem_union] at hgS
    rcases hgS with hgG | hgMap
    · exact ⟨g, (Finset.mem_union_exp _ _ _).mpr (Or.inl hgG), hgGoal⟩
    · -- g ∈ mapSet(As, cwl·B). So g = cwl(A, B) for some A ∈ As.
      obtain ⟨A, hA, hgEq⟩ := (mem_image_iff _ _ _).mp hgMap
      -- g is a goal (all negative). cwl(A,B) = g is all negative.
      -- B must be negative (otherwise pos B ∈ g contradicts isGoalClause).
      -- A ⊆ cwl(A,B) = g is all negative → A is a goal clause.
      have hAinGA : A ∈ Finset.union G As := (Finset.mem_union_exp _ _ _).mpr (Or.inr hA)
      have hAGoal : isGoalClause A := by
        constructor
        · refine ⟨?_, ?_⟩
          · obtain ⟨l, hl⟩ := hNonempty A hAinGA
            exact Clause.ordinary_of_mem hl
          intro P Q hP hQ
          have hP' : Literal.pos P ∈ clauseWithLiteral A B :=
            (Finset.mem_insert_exp _ _ _).mpr (Or.inr hP)
          rw [hgEq] at hP'
          exact absurd (hgGoal.2 _ hP') (by simp)
        · intro l hl
          have hl' : l ∈ clauseWithLiteral A B := (Finset.mem_insert_exp _ _ _).mpr (Or.inr hl)
          rw [hgEq] at hl'
          exact hgGoal.2 l hl'
      exact ⟨A, hAinGA, hAGoal⟩

helper /-- Right subtree has a goal clause. -/
theorem right_subtree_has_goal
    (G : ClauseSequent) (B : Literal) (As : ClauseSequent)
    (J' : ClauseSequent) (defs' : List Clause)
    (goals' : List Clause) (hGoalsNe' : goals' ≠ [])
    (hGoals' : ∀ C ∈ goals', isGoalClause C)
    (hS' : Finset.union G (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)) =
      Finset.union (Finset.union J' (ClauseSequent.ofList defs')) (ClauseSequent.ofList goals')) :
    ∃ C ∈ Finset.union G (ClauseSequent.single (Clause.single B)), isGoalClause C := by
-- BEGIN PROOF
  cases goals' with
  | nil => exact absurd rfl hGoalsNe'
  | cons g gs =>
    have hgGoal := hGoals' g (List.mem_cons.mpr (Or.inl rfl))
    have hgS : g ∈ Finset.union G (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)) := by
      rw [hS']; exact (Finset.mem_union_exp _ _ _).mpr (Or.inr ((Finset.mem_ofList_exp _ _).mpr
        (List.mem_cons.mpr (Or.inl rfl))))
    rw [Finset.mem_union] at hgS
    rcases hgS with hgG | hgMap
    · exact ⟨g, (Finset.mem_union_exp _ _ _).mpr (Or.inl hgG), hgGoal⟩
    · -- g = cwl(A,B) is a goal → B is negative → {B} is a goal
      obtain ⟨A, _, hgEq⟩ := (mem_image_iff _ _ _).mp hgMap
      have hBneg : ∃ P, B = Literal.neg P := by
        match B with
        | .neg P => exact ⟨P, rfl⟩
        | .pos P =>
          have : Literal.pos P ∈ clauseWithLiteral A (Literal.pos P) :=
            (Finset.mem_insert_exp _ _ _).mpr (Or.inl rfl)
          rw [hgEq] at this
          exact absurd (hgGoal.2 _ this) (by simp)
      obtain ⟨P, rfl⟩ := hBneg
      exact ⟨Clause.single (Literal.neg P),
        (Finset.mem_union_exp _ _ _).mpr (Or.inr ((Finset.mem_singleton _ _).mpr rfl)),
        singleton_neg_is_goal P⟩

helper /-- A clause in jFilter or defFilter is NOT a goal (isGoalClauseB = false). -/
theorem filter_nongoal (S : ClauseSequent) (C : Clause)
    (hC : C ∈ jFilter S ∨ C ∈ defFilter S) : isGoalClauseB C = false := by
  cases hv : isGoalClauseB C with
  | false => rfl
  | true =>
    exfalso
    rcases hC with h | h
    · have := ((Finset.mem_filter_exp _ _ _).mp h).2; simp [hv] at this
    · have := ((Finset.mem_filter_exp _ _ _).mp h).2; simp [hv] at this

helper /-- For S_R = G ∪ {{neg P}}, every non-goal clause is from G and hence in JD'. -/
theorem right_neg_nongoal_subset_JD (G As : ClauseSequent) (P : Nat)
    (J' : ClauseSequent) (defs' goals' : List Clause)
    (hGoals' : ∀ C ∈ goals', isGoalClause C)
    (hSConc : Finset.union G (ClauseSequent.mapSet As (fun A => clauseWithLiteral A (Literal.neg P))) =
      Finset.union (Finset.union J' (ClauseSequent.ofList defs')) (ClauseSequent.ofList goals'))
    (C : Clause)
    (hC : C ∈ jFilter (Finset.union G (ClauseSequent.single (Clause.single (Literal.neg P)))) ∨
          C ∈ defFilter (Finset.union G (ClauseSequent.single (Clause.single (Literal.neg P))))) :
    C ∈ Finset.union J' (ClauseSequent.ofList defs') := by
-- BEGIN PROOF
  have hCinSR : C ∈ Finset.union G (ClauseSequent.single (Clause.single (Literal.neg P))) := by
    rcases hC with h | h <;> exact ((Finset.mem_filter_exp _ _ _).mp h).1
  have hNotGoalB := filter_nongoal _ C hC
  rw [Finset.mem_union] at hCinSR
  have hCinG : C ∈ G := by
    rcases hCinSR with hG | hSing
    · exact hG
    · exfalso
      have hCeq := mem_csingle C (Clause.single (Literal.neg P)) |>.mp hSing; subst hCeq
      have hGB : isGoalClauseB (Clause.single (Literal.neg P)) = true :=
        isGoalClauseB_complete _ (singleton_neg_is_goal P)
      simp [hGB] at hNotGoalB
  have hCS' := (Finset.mem_union_exp _ _ _).mpr (Or.inl hCinG) |> (hSConc ▸ ·)
  rw [Finset.mem_union] at hCS'
  rcases hCS' with hJD | hGoal
  · exact hJD
  · exfalso
    have hGC := isGoalClauseB_complete C (hGoals' C ((Finset.mem_ofList_exp _ _).mp hGoal))
    simp [hGC] at hNotGoalB

helper /-- A goal clause in G is in ofList(goals'). -/
theorem goal_in_G_mem_goals (G As : ClauseSequent) (B : Literal)
    (J' : ClauseSequent) (defs' goals' : List Clause)
    (hJ' : ∀ C ∈ J', ∃ P : Nat, C = Clause.single (Literal.pos P))
    (hDefs' : ∀ C ∈ defs', isDefiniteClause C ∧ (∃ l₁ l₂, l₁ ∈ C ∧ l₂ ∈ C ∧ l₁ ≠ l₂))
    (hSConc : Finset.union G (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)) =
      Finset.union (Finset.union J' (ClauseSequent.ofList defs')) (ClauseSequent.ofList goals'))
    (C : Clause) (hCG : C ∈ G) (hGoal : isGoalClause C) :
    C ∈ ClauseSequent.ofList goals' := by
-- BEGIN PROOF
  have hCS' : C ∈ Finset.union (Finset.union J' (ClauseSequent.ofList defs'))
      (ClauseSequent.ofList goals') := hSConc ▸ (Finset.mem_union_exp _ _ _).mpr (Or.inl hCG)
  rw [Finset.mem_union] at hCS'
  rcases hCS' with hJD | hGoalM
  · rw [Finset.mem_union] at hJD
    rcases hJD with hCJ | hCD
    · obtain ⟨Q, hQ⟩ := hJ' _ hCJ; subst hQ
      exact absurd (hGoal.2 (Literal.pos Q) ((Finset.mem_singleton _ _).mpr rfl)) (by simp)
    · obtain ⟨⟨_, ⟨Q, hQ⟩⟩, _⟩ := hDefs' _ ((Finset.mem_ofList_exp _ _).mp hCD)
      exact absurd (hGoal.2 (Literal.pos Q) hQ) (by simp)
  · exact hGoalM

helper /-- For B = pos P, every non-goal clause in G ∪ As is in JD'.
    Key insight: if A ∈ As has pos Q with Q ≠ P, then cwl(A, pos P) has
    two positive literals, contradicting Horn-ness of S'. So every non-goal
    A ∈ As must contain pos P, hence cwl(A, pos P) = A, so A ∈ S' ∩ JD'. -/
theorem left_pos_nongoal_subset_JD (G As : ClauseSequent) (P : Nat)
    (J' : ClauseSequent) (defs' goals' : List Clause)
    (hGoals' : ∀ C ∈ goals', isGoalClause C)
    (hJ' : ∀ C ∈ J', ∃ Q : Nat, C = Clause.single (Literal.pos Q))
    (hDefs' : ∀ C ∈ defs', isDefiniteClause C ∧ (∃ l₁ l₂, l₁ ∈ C ∧ l₂ ∈ C ∧ l₁ ≠ l₂))
    (hSConc : Finset.union G (ClauseSequent.mapSet As (fun A => clauseWithLiteral A (Literal.pos P))) =
      Finset.union (Finset.union J' (ClauseSequent.ofList defs')) (ClauseSequent.ofList goals'))
    (hHornS : ∀ C ∈ Finset.union G (ClauseSequent.mapSet As (fun A => clauseWithLiteral A (Literal.pos P))),
      isHornClause C)
    (hAsOrd : As.isOrdinary)
    (C : Clause)
    (hC : C ∈ jFilter (Finset.union G As) ∨ C ∈ defFilter (Finset.union G As)) :
    C ∈ Finset.union J' (ClauseSequent.ofList defs') := by
-- BEGIN PROOF
  have hCinSL : C ∈ Finset.union G As := by
    rcases hC with h | h <;> exact ((Finset.mem_filter_exp _ _ _).mp h).1
  rw [Finset.mem_union] at hCinSL
  have hNotGoalB := filter_nongoal _ C hC
  have hNotGoal : ¬isGoalClause C := by
    intro hGC; simp [isGoalClauseB_complete C hGC] at hNotGoalB
  rcases hCinSL with hCG | hCA
  · have hCS' := hSConc ▸ (Finset.mem_union_exp _ _ _).mpr (Or.inl hCG)
    rw [Finset.mem_union] at hCS'
    rcases hCS' with hJD | hGoal
    · exact hJD
    · exact absurd (hGoals' C ((Finset.mem_ofList_exp _ _).mp hGoal)) hNotGoal
  · have hCwlInS : clauseWithLiteral C (Literal.pos P) ∈
        Finset.union G (ClauseSequent.mapSet As (fun A => clauseWithLiteral A (Literal.pos P))) :=
      (Finset.mem_union_exp _ _ _).mpr (Or.inr ((mem_image_iff _ _ _).mpr ⟨C, hCA, rfl⟩))
    have hHornCwl := hHornS _ hCwlInS
    have hExPos : ∃ Q, Literal.pos Q ∈ C := Classical.byContradiction fun hNoPos => by
      have hNoPos' : ∀ Q, Literal.pos Q ∉ C := fun Q hQ => hNoPos ⟨Q, hQ⟩
      apply hNotGoal; constructor
      · exact ⟨hAsOrd C hCA, fun Q R hQ _ => absurd hQ (hNoPos' Q)⟩
      · intro l hl; match l with
        | .neg _ => trivial
        | .pos Q => exact absurd hl (hNoPos' Q)
    obtain ⟨Q, hQ⟩ := hExPos
    have hQP : Q = P := hHornCwl.2 Q P
      ((Finset.mem_insert_exp _ _ _).mpr (Or.inr hQ))
      ((Finset.mem_insert_exp _ _ _).mpr (Or.inl rfl))
    rw [hQP] at hQ
    have hCwlEq : clauseWithLiteral C (Literal.pos P) = C := by
      unfold clauseWithLiteral
      apply Finset.ext; intro x; constructor
      · intro hx; rw [Finset.mem_insert] at hx; rcases hx with rfl | hxC; exact hQ; exact hxC
      · intro hx; exact (Finset.mem_insert_exp _ _ _).mpr (Or.inr hx)
    rw [hCwlEq] at hCwlInS; rw [hSConc] at hCwlInS; rw [Finset.mem_union] at hCwlInS
    rcases hCwlInS with hJD | hGoal
    · exact hJD
    · exact absurd (hGoals' C ((Finset.mem_ofList_exp _ _).mp hGoal)) hNotGoal

proof_of goal_reduction := by
  -- BEGIN PROOF
    let JD := Finset.union J (ClauseSequent.ofList defs)
    have hValid := gcnf_soundness S hProv
    -- JD satisfies the intersection preservation property
    have hJDprop : ∀ C ∈ JD, (∃ P : Nat, C = Clause.single (Literal.pos P)) ∨ isDefiniteClause C := by
      intro C hC; rw [Finset.mem_union] at hC
      rcases hC with hCJ | hCD
      · exact Or.inl (hJ C hCJ)
      · exact Or.inr (hDefs C ((Finset.mem_ofList_exp C _).mp hCD)).1
    -- Helper: show no empty clauses in JD ∪ {goals.get i} when goals.get i ≠ ∅
    have hNoEmptyHelper : ∀ i : Fin goals.length, goals.get i ≠ Clause.empty →
        ∀ C ∈ Finset.union JD (ClauseSequent.single (goals.get i)), C ≠ Clause.empty := by
      intro i hNeI C hC hCeq; rw [Finset.mem_union] at hC
      rcases hC with hCJD | hCSingle
      · rw [Finset.mem_union] at hCJD
        rcases hCJD with hCJ | hCD
        · obtain ⟨P, rfl⟩ := hJ _ hCJ
          have : Literal.pos P ∈ Clause.single (Literal.pos P) := (Finset.mem_singleton _ _).mpr rfl
          rw [hCeq] at this; exact (Finset.mem_empty _).mp this
        · obtain ⟨_, l₁, _, hl₁, _, _⟩ := hDefs _ ((Finset.mem_ofList_exp C _).mp hCD)
          rw [hCeq] at hl₁; exact (Finset.mem_empty _).mp hl₁
      · have hCSingle' := (Finset.mem_singleton C _).mp hCSingle
        rw [hCSingle'] at hCeq; exact hNeI hCeq
    -- Helper: find ∃ i such that JD ∪ {N_i} is valid and N_i ≠ ∅
    -- (semantic argument via model combination)
    have hFindValidI : (∀ C ∈ goals, C = Clause.empty) ∨
        ∃ i : Fin goals.length,
          ClauseSequent.isValid (Finset.union JD (ClauseSequent.single (goals.get i))) ∧
          goals.get i ≠ Clause.empty := by
      by_cases hAllEmpty : ∀ C ∈ goals, C = Clause.empty
      · exact Or.inl hAllEmpty
      · right
        have hExNonEmpty : ∃ C, C ∈ goals ∧ C ≠ Clause.empty :=
          Classical.byContradiction fun hNone =>
            hAllEmpty (fun C hC =>
              Classical.byContradiction fun hNe => hNone ⟨C, hC, hNe⟩)
        by_cases hNoEmpty : ∀ C ∈ goals, C ≠ Clause.empty
        · -- All goals non-empty. By contradiction via model combination.
          exact Classical.byContradiction fun hNoValid => hValid (by
            rw [hS]
            have hEachSat : ∀ i : Fin goals.length, ∃ v : Nat → Bool,
                ClauseSequent.satisfiedBy JD v ∧ Clause.satisfiedBy (goals.get i) v := by
              intro i
              have hNe := hNoEmpty _ (List.get_mem goals i)
              have hNotValid : ¬ClauseSequent.isValid (Finset.union JD (ClauseSequent.single (goals.get i))) :=
                fun hV => hNoValid ⟨i, hV, hNe⟩
              rw [ClauseSequent.isValid] at hNotValid
              have hSatI : ∃ v, ClauseSequent.satisfiedBy (Finset.union JD (ClauseSequent.single (goals.get i))) v :=
                Classical.byContradiction fun h => hNotValid (fun ⟨v, hv⟩ => h ⟨v, hv⟩)
              obtain ⟨v, hSat⟩ := hSatI
              exact ⟨v, fun C hC => hSat C ((Finset.mem_union_exp _ _ _).mpr (Or.inl hC)),
                hSat _ ((Finset.mem_union_exp _ _ _).mpr (Or.inr ((Finset.mem_singleton _ _).mpr rfl)))⟩
            obtain ⟨v, hvJD, hvGoals⟩ := horn_all_goals_sat_of_each_sat JD goals hJDprop hGoals hGoalsNe hEachSat
            refine ⟨v, fun C hC => ?_⟩
            rw [Finset.mem_union] at hC
            rcases hC with hCJD | hCGoals
            · exact hvJD C hCJD
            · exact hvGoals C ((Finset.mem_ofList_exp C goals).mp hCGoals))
        · -- Mixed case: some goals empty, some non-empty.
          obtain ⟨T⟩ := hProv
          have hValidErased := gcnf_soundness _ (gcnf_provable_erase_empty T)
          have hErasedEq : Finset.erase S Clause.empty =
              Finset.union JD (Finset.erase (ClauseSequent.ofList goals) Clause.empty) := by
            rw [hS]; apply Finset.ext; intro C; constructor
            · intro hC
              have ⟨hMem, hNe⟩ := (Finset.mem_erase _ _ _).mp hC
              rw [Finset.mem_union] at hMem ⊢
              rcases hMem with hJD | hG
              · exact Or.inl hJD
              · exact Or.inr ((Finset.mem_erase _ _ _).mpr ⟨hG, hNe⟩)
            · intro hC
              rw [Finset.mem_union] at hC
              rcases hC with hJD | hG
              · have hNe : C ≠ Clause.empty := by
                  intro hCeq; rw [Finset.mem_union] at hJD
                  rcases hJD with hCJ | hCD
                  · obtain ⟨P, rfl⟩ := hJ _ hCJ
                    exact (Finset.mem_empty _).mp
                      (hCeq ▸ (Finset.mem_singleton _ _).mpr rfl : Literal.pos P ∈ Clause.empty)
                  · obtain ⟨_, l₁, _, hl₁, _, _⟩ := hDefs _ ((Finset.mem_ofList_exp C _).mp hCD)
                    exact (Finset.mem_empty _).mp (hCeq ▸ hl₁ : l₁ ∈ Clause.empty)
                exact (Finset.mem_erase _ _ _).mpr ⟨(Finset.mem_union_exp _ _ _).mpr (Or.inl hJD), hNe⟩
              · have ⟨hMem, hNe⟩ := (Finset.mem_erase _ _ _).mp hG
                exact (Finset.mem_erase _ _ _).mpr ⟨(Finset.mem_union_exp _ _ _).mpr (Or.inr hMem), hNe⟩
          rw [hErasedEq] at hValidErased
          exact Classical.byContradiction fun hNoValid => by
            let neGoals := goals.filter (fun C => decide (C ≠ Clause.empty))
            have hNeGoalsNe : neGoals ≠ [] := by
              intro h; obtain ⟨C, hCmem, hCne⟩ := hExNonEmpty
              exact absurd
                (h ▸ (List.mem_filter.mpr ⟨hCmem, decide_eq_true hCne⟩) : C ∈ ([] : List Clause))
                List.not_mem_nil
            have hNeGoalsGoal : ∀ C ∈ neGoals, isGoalClause C :=
              fun C hC => hGoals C (List.mem_filter.mp hC).1
            have hEachSat : ∀ i : Fin neGoals.length, ∃ v : Nat → Bool,
                ClauseSequent.satisfiedBy JD v ∧ Clause.satisfiedBy (neGoals.get i) v := by
              intro ⟨j, hj⟩
              have hMem := List.get_mem neGoals ⟨j, hj⟩
              have hNe : neGoals.get ⟨j, hj⟩ ≠ Clause.empty :=
                of_decide_eq_true (List.mem_filter.mp hMem).2
              obtain ⟨k, hk, hkEq⟩ := List.mem_iff_getElem.mp ((List.mem_filter.mp hMem).1)
              rw [← hkEq]
              have hNek : goals.get ⟨k, hk⟩ ≠ Clause.empty := by
                rw [show goals.get ⟨k, hk⟩ = goals[k] from rfl, hkEq]; exact hNe
              have hNotV : ¬ClauseSequent.isValid (Finset.union JD
                  (ClauseSequent.single (goals.get ⟨k, hk⟩))) :=
                fun hV => hNoValid ⟨⟨k, hk⟩, hV, hNek⟩
              unfold ClauseSequent.isValid at hNotV
              have hSat : ∃ v, ClauseSequent.satisfiedBy (Finset.union JD
                  (ClauseSequent.single (goals.get ⟨k, hk⟩))) v :=
                Classical.byContradiction fun h => hNotV h
              obtain ⟨v, hSat⟩ := hSat
              exact ⟨v, fun C hC => hSat C ((Finset.mem_union_exp _ _ _).mpr (Or.inl hC)),
                hSat _ ((Finset.mem_union_exp _ _ _).mpr (Or.inr ((Finset.mem_singleton _ _).mpr rfl)))⟩
            obtain ⟨v, hvJD, hvGoals⟩ := horn_all_goals_sat_of_each_sat
              JD neGoals hJDprop hNeGoalsGoal hNeGoalsNe hEachSat
            apply hValidErased
            refine ⟨v, fun C hC => ?_⟩
            rw [Finset.mem_union] at hC
            rcases hC with hCJD | hCGoals
            · exact hvJD C hCJD
            · have ⟨hCmem, hCne⟩ := (Finset.mem_erase _ _ _).mp hCGoals
              exact hvGoals C
                (List.mem_filter.mpr ⟨(Finset.mem_ofList_exp _ _).mp hCmem, decide_eq_true hCne⟩)
    -- Now produce the conjunction ⟨part_a, part_b⟩
    constructor
    · -- Part (a): ∃ i, GCNFProvable (JD ∪ {goals.get i})
      rcases hFindValidI with hAllEmpty | ⟨i, hValidI, hNeI⟩
      · -- All goals are ∅. Pick i = 0.
        have hIdx : 0 < goals.length := by
          cases goals with | nil => exact absurd rfl hGoalsNe | cons _ _ => simp
        refine ⟨⟨0, hIdx⟩, ?_⟩
        have hGoalsEq : ClauseSequent.ofList goals = ClauseSequent.single (goals.get ⟨0, hIdx⟩) := by
          have hGi : goals.get ⟨0, hIdx⟩ = Clause.empty := hAllEmpty _ (List.get_mem goals ⟨0, hIdx⟩)
          rw [hGi, ClauseSequent.ofList, ClauseSequent.single]
          apply Finset.ext; intro D; rw [Finset.mem_ofList, Finset.mem_singleton]
          exact ⟨hAllEmpty D, fun h => by rw [h]; cases goals with
            | nil => exact absurd rfl hGoalsNe
            | cons g gs => rw [hAllEmpty g (List.mem_cons.mpr (Or.inl rfl))]; exact List.mem_cons.mpr (Or.inl rfl)⟩
        rw [hS, hGoalsEq] at hProv; exact hProv
      · -- Some goal non-empty with valid single-goal subset
        exact ⟨i, (gcnf_completeness _ hValidI (hNoEmptyHelper i hNeI)).1⟩
    · -- Part (b): structural induction on T (textbook Cases 1-3)
      -- Proof by strong induction on proofDepth T, universally over partition.
      intro T hIWW hLit
      suffices h : ∀ (n : Nat) (J' : ClauseSequent) (goals' : List Clause) (defs' : List Clause)
          (hJ' : ∀ C ∈ J', ∃ P : Nat, C = Clause.single (Literal.pos P))
          (hGoals' : ∀ C ∈ goals', isGoalClause C) (hGoalsNe' : goals' ≠ [])
          (hDefs' : ∀ C ∈ defs', isDefiniteClause C ∧ (∃ l₁ l₂, l₁ ∈ C ∧ l₂ ∈ C ∧ l₁ ≠ l₂))
          (S' : ClauseSequent)
          (hS' : S' = Finset.union (Finset.union J' (ClauseSequent.ofList defs'))
            (ClauseSequent.ofList goals'))
          (T' : GCNFProofTree S') (hIWW' : IsStrictIWW T')
          (hLit' : T'.axiomsAllSingleLiteral) (hDepth' : proofDepth T' = n),
          ∃ (i : Fin goals'.length)
            (T'' : GCNFProofTree (Finset.union (Finset.union J' (ClauseSequent.ofList defs'))
              (ClauseSequent.single (goals'.get i)))),
            proofDepth T'' ≤ n by
        obtain ⟨i, T'', hd⟩ := h (proofDepth T) J goals defs hJ hGoals hGoalsNe hDefs S hS T hIWW hLit rfl
        exact ⟨i, T'', hd⟩
      intro n
      induction n using Nat.strongRecOn with
      | _ n ih =>
        intro J' goals' defs' hJ' hGoals' hGoalsNe' hDefs' S' hS' T' hIWW' hLit' hDepth'
        have hRootOrd : S'.isOrdinary := T'.ordinary
        have hJDOrd : ClauseSequent.isOrdinary (Finset.union J' (ClauseSequent.ofList defs')) := by
          apply ClauseSequent.ordinary_union
          · exact ordinary_of_singletons (fun C hC => by obtain ⟨P, hP⟩ := hJ' C hC; exact ⟨_, hP⟩)
          · intro C hC
            exact ordinary_of_definite (hDefs' C (Finset.mem_ofList.mp hC)).1
        match T', hIWW', hLit', hDepth' with
        | .axiom_ _S hOrd hTriv, _, hLit', hDepth' =>
          -- Case 1: axiom with complementary pair {pos P, neg P}
          obtain ⟨P, hPosP, hNegP⟩ := hTriv
          rw [hS'] at hNegP hPosP
          have hNegInGoals : Clause.single (Literal.neg P) ∈ ClauseSequent.ofList goals' := by
            rw [Finset.mem_union] at hNegP
            rcases hNegP with hJD | hGoal
            · rw [Finset.mem_union] at hJD
              rcases hJD with hCJ | hCD
              · obtain ⟨Q, hQ⟩ := hJ' _ hCJ
                have hmem : Literal.neg P ∈ Clause.single (Literal.neg P) :=
                  (Finset.mem_singleton _ _).mpr rfl
                rw [hQ] at hmem
                exact absurd ((Finset.mem_singleton _ _).mp hmem) Literal.noConfusion
              · obtain ⟨_, l₁, l₂, hl₁, hl₂, hNe⟩ := hDefs' _ ((Finset.mem_ofList_exp _ _).mp hCD)
                exact absurd ((Finset.mem_singleton l₂ _).mp hl₂ ▸
                  (Finset.mem_singleton l₁ _).mp hl₁) hNe
            · exact hGoal
          have hPosJD : Clause.single (Literal.pos P) ∈
              Finset.union J' (ClauseSequent.ofList defs') := by
            rw [Finset.mem_union] at hPosP
            rcases hPosP with hJD | hGoalP
            · exact hJD
            · have ⟨_, hG⟩ := hGoals' _ ((Finset.mem_ofList_exp _ _).mp hGoalP)
              exact absurd (hG _ ((Finset.mem_singleton _ _).mpr rfl)) (by simp)
          obtain ⟨i, hi, hieq⟩ :=
            List.mem_iff_getElem.mp ((Finset.mem_ofList_exp _ _).mp hNegInGoals)
          refine ⟨⟨i, hi⟩, .axiom_ _ (ClauseSequent.ordinary_union hJDOrd
            (ClauseSequent.ordinary_single (by rw [show goals'.get ⟨i, hi⟩ = goals'[i] from rfl, hieq]; exact Clause.single_ordinary _))) ⟨P,
            (Finset.mem_union_exp _ _ _).mpr (Or.inl hPosJD),
            (Finset.mem_union_exp _ _ _).mpr (Or.inr ?_)⟩, by simp [proofDepth]⟩
          rw [show goals'.get ⟨i, hi⟩ = goals'[i] from rfl, hieq]
          exact (Finset.mem_singleton _ _).mpr rfl
        | .rule G As B Cs G1 G2 hGammaOrd hAsOrd lT rT hNe hCSub hG1Sub hG2Sub, hIWW', hLit', hDepth' =>
          -- Case 2/3: Rule node. Extract IsStrictIWW data.
          have hCsAs : Cs = As := hIWW'.1
          have hG1eq : G1 = G := hIWW'.2.1
          have hG2eq : G2 = G := hIWW'.2.2.1
          have hIWWL : IsStrictIWW lT := hIWW'.2.2.2.1
          have hIWWR : IsStrictIWW rT := hIWW'.2.2.2.2
          have hLitL : lT.axiomsAllSingleLiteral := hLit'.1
          have hLitR : rT.axiomsAllSingleLiteral := hLit'.2
          -- Transport subtrees to canonical types
          have hLeq : Finset.union G1 Cs = Finset.union G As := by rw [hG1eq, hCsAs]
          have hReq : Finset.union G2 (ClauseSequent.single (Clause.single B)) =
              Finset.union G (ClauseSequent.single (Clause.single B)) := by rw [hG2eq]
          let lT' : GCNFProofTree (Finset.union G As) := hLeq ▸ lT
          let rT' : GCNFProofTree (Finset.union G (ClauseSequent.single (Clause.single B))) := hReq ▸ rT
          have hIWWL' : IsStrictIWW lT' := IsStrictIWW_transport hLeq lT hIWWL
          have hIWWR' : IsStrictIWW rT' := IsStrictIWW_transport hReq rT hIWWR
          have hLitL' : lT'.axiomsAllSingleLiteral := axiomsAllSingleLiteral_transport hLeq lT hLitL
          have hLitR' : rT'.axiomsAllSingleLiteral := axiomsAllSingleLiteral_transport hReq rT hLitR
          have hDepthL : proofDepth lT' < n := by
            rw [show proofDepth lT' = proofDepth lT from proofDepth_eq_transport hLeq lT]
            simp [proofDepth] at hDepth'; omega
          have hDepthR : proofDepth rT' < n := by
            rw [show proofDepth rT' = proofDepth rT from proofDepth_eq_transport hReq rT]
            simp [proofDepth] at hDepth'; omega
          -- The conclusion S' = G ∪ mapSet(As, cwl·B) = JD' ∪ ofList(goals')
          let S_L := Finset.union G As
          let S_R := Finset.union G (ClauseSequent.single (Clause.single B))
          -- Nonemptiness of clauses in subtrees (from IsStrictIWW + axiomsAllSingleLiteral)
          have hNeL : ∀ C ∈ S_L, ∃ L : Literal, L ∈ C :=
            root_clauses_nonempty lT' hIWWL' hLitL'
          have hNeR : ∀ C ∈ S_R, ∃ L : Literal, L ∈ C :=
            root_clauses_nonempty rT' hIWWR' hLitR'
          -- Horn-ness of subtrees
          have hSConc : Finset.union G (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)) =
              Finset.union (Finset.union J' (ClauseSequent.ofList defs')) (ClauseSequent.ofList goals') := hS'
          have hHornL : ∀ C ∈ S_L, isHornClause C :=
            left_subtree_horn G As B J' goals' defs' hJ' hGoals' hDefs' (fun C hC => lT'.ordinary C (Finset.mem_union.mpr (Or.inr hC))) hSConc
          have hHornR : ∀ C ∈ S_R, isHornClause C :=
            right_subtree_horn G B As J' goals' defs' hJ' hGoals' hDefs' hSConc
          -- Goal existence in subtrees
          have hGoalExL : ∃ C ∈ S_L, isGoalClause C :=
            left_subtree_has_goal G As B J' defs' goals' hGoalsNe' hGoals' hSConc hNeL
          have hGoalExR : ∃ C ∈ S_R, isGoalClause C :=
            right_subtree_has_goal G B As J' defs' goals' hGoalsNe' hGoals' hSConc
          -- Apply the IH to BOTH subtrees using filter partitions.
          -- Helper: apply IH to a subtree
          have applyIH := fun (S_sub : ClauseSequent)
              (T_sub : GCNFProofTree S_sub) (hIWW_sub : IsStrictIWW T_sub)
              (hLit_sub : T_sub.axiomsAllSingleLiteral) (hDepth_sub : proofDepth T_sub < n)
              (hHorn_sub : ∀ C ∈ S_sub, isHornClause C)
              (hNe_sub : ∀ C ∈ S_sub, ∃ L : Literal, L ∈ C)
              (hGoalEx_sub : ∃ C ∈ S_sub, isGoalClause C) =>
            ih (proofDepth T_sub) hDepth_sub
              (jFilter S_sub) (goalFilterList S_sub) (defFilterList S_sub)
              (jFilter_unit_pos S_sub hHorn_sub hNe_sub)
              (fun C hC => goalFilter_goal S_sub C (by rw [← ofList_goalFilterList]; exact (Finset.mem_ofList_exp _ _).mpr hC))
              (goalFilterList_nonempty S_sub hGoalEx_sub)
              (fun C hC => defFilter_definite S_sub hHorn_sub hNe_sub C (by rw [← ofList_defFilterList]; exact (Finset.mem_ofList_exp _ _).mpr hC))
              S_sub (by rw [ofList_defFilterList, ofList_goalFilterList]; exact filter_covers S_sub)
              T_sub hIWW_sub hLit_sub rfl
          obtain ⟨i_R, T_R, hd_R⟩ := applyIH S_R rT' hIWWR' hLitR' hDepthR hHornR hNeR hGoalExR
          obtain ⟨i_L, T_L, hd_L⟩ := applyIH S_L lT' hIWWL' hLitL' hDepthL hHornL hNeL hGoalExL
          -- Extract the chosen goals and their properties
          let goal_R := (goalFilterList S_R).get i_R
          let goal_L := (goalFilterList S_L).get i_L
          have hGoalR_mem : goal_R ∈ goalFilter S_R := by
            have h : goal_R ∈ goalFilterList S_R := List.get_mem _ _
            exact (Finset.mem_toList (goalFilter S_R) goal_R).mp h
          have hGoalL_mem : goal_L ∈ goalFilter S_L := by
            have h : goal_L ∈ goalFilterList S_L := List.get_mem _ _
            exact (Finset.mem_toList (goalFilter S_L) goal_L).mp h
          have hGoalR_goal : isGoalClause goal_R := goalFilter_goal S_R goal_R hGoalR_mem
          have hGoalL_goal : isGoalClause goal_L := goalFilter_goal S_L goal_L hGoalL_mem
          -- Helper: given a goal from G, it's in ofList(goals')
          have goalFromG : ∀ g, g ∈ G → isGoalClause g → g ∈ ClauseSequent.ofList goals' :=
            fun g hg hgGoal => goal_in_G_mem_goals G As B J' defs' goals' hJ' hDefs' hSConc g hg hgGoal
          -- Helper: produce the result from a goal in goals' via superset weakening
          have fromSubset : ∀ (S_sub : ClauseSequent) (i_sub : Fin (goalFilterList S_sub).length)
              (T_sub : GCNFProofTree (Finset.union (Finset.union (jFilter S_sub)
                (ClauseSequent.ofList (defFilterList S_sub)))
                (ClauseSequent.single ((goalFilterList S_sub).get i_sub))))
              (hd_sub : proofDepth T_sub ≤ proofDepth lT' ∨ proofDepth T_sub ≤ proofDepth rT')
              (hNonGoalJD : ∀ C, (C ∈ jFilter S_sub ∨ C ∈ defFilter S_sub) →
                C ∈ Finset.union J' (ClauseSequent.ofList defs'))
              (j : Nat) (hj : j < goals'.length)
              (hjeq : goals'[j] = (goalFilterList S_sub).get i_sub),
              ∃ (i : Fin goals'.length)
                (T'' : GCNFProofTree (Finset.union (Finset.union J' (ClauseSequent.ofList defs'))
                  (ClauseSequent.single (goals'.get i)))),
                proofDepth T'' ≤ n := by
            intro S_sub i_sub T_sub hd_sub hNonGoalJD j hj hjeq
            refine ⟨⟨j, hj⟩, ?_⟩
            have hSub : ∀ C, C ∈ Finset.union (Finset.union (jFilter S_sub)
                (ClauseSequent.ofList (defFilterList S_sub)))
                (ClauseSequent.single ((goalFilterList S_sub).get i_sub)) →
                C ∈ Finset.union (Finset.union J' (ClauseSequent.ofList defs'))
                  (ClauseSequent.single (goals'.get ⟨j, hj⟩)) := by
              intro C hC; rw [Finset.mem_union] at hC
              rcases hC with hJD | hGoalC
              · rw [Finset.mem_union] at hJD
                exact (Finset.mem_union_exp _ _ _).mpr (Or.inl (hNonGoalJD C (by
                  rcases hJD with h | h
                  · exact Or.inl h
                  · exact Or.inr (by rw [ofList_defFilterList] at h; exact h))))
              · rw [(Finset.mem_singleton C _).mp hGoalC,
                    show goals'.get ⟨j, hj⟩ = goals'[j] from rfl, hjeq]
                exact (Finset.mem_union_exp _ _ _).mpr (Or.inr ((Finset.mem_singleton _ _).mpr rfl))
            have hd_bound : proofDepth T_sub < n := by
              rcases hd_sub with h | h
              · exact Nat.lt_of_le_of_lt h hDepthL
              · exact Nat.lt_of_le_of_lt h hDepthR
            obtain ⟨T'', hd''⟩ := gcnf_superset_bounded _ _ hSub T_sub _ (Nat.le_of_lt hd_bound) (by
                      repeat first
                        | exact hJDOrd
                        | exact ordinary_right T_L
                        | exact ordinary_right T_R
                        | exact ClauseSequent.ordinary_single (Clause.single_ordinary _)
                        | apply ClauseSequent.ordinary_union
                        | exact ClauseSequent.ordinary_subset hAsOrd (fun C hC => (Finset.mem_filter.mp hC).1)
                        | exact ClauseSequent.ordinary_subset hAsOrd (fun C hC => (Finset.mem_union.mp hC).elim id id)
                        | (intro C hC; apply hRootOrd C; rw [hS']; exact Finset.mem_union.mpr (Or.inr (Finset.mem_ofList.mpr (by rw [(mem_csingle _ _).mp hC]; exact List.get_mem _ _)))))
            exact ⟨T'', by omega⟩
          -- The IH applied to both subtrees gives single-goal proofs with bounded depth.
          -- Case analysis on B's polarity and location of the IH-picked goal:
          --   * B = neg P: use T_R (S_R = G ∪ {{neg P}}) path, right_neg_nongoal_subset_JD.
          --   * B = pos P: use T_L (S_L = G ∪ As) path, left_pos_nongoal_subset_JD.
          -- Each case has sub-cases for the location of the IH-picked goal.
          -- S' is Horn (needed for left_pos_nongoal_subset_JD in the pos case).
          have hHornS_all : ∀ C ∈ Finset.union G (ClauseSequent.mapSet As
              (fun A => clauseWithLiteral A B)), isHornClause C := by
            intro C hC
            rw [hSConc] at hC
            rw [Finset.mem_union] at hC
            rcases hC with hJD | hGoal
            · rw [Finset.mem_union] at hJD
              rcases hJD with hJ | hD
              · obtain ⟨Q, rfl⟩ := hJ' _ hJ
                exact isHornClause_single _
              · exact (hDefs' _ ((Finset.mem_ofList_exp _ _).mp hD)).1.1
            · exact (hGoals' _ ((Finset.mem_ofList_exp _ _).mp hGoal)).1
          -- Handle each polarity of B.
          cases hB_pol : B with
          | neg P =>
            -- Case 2 (textbook): B = neg P. Use right subtree path.
            -- goal_R ∈ S_R = G ∪ {{neg P}}. Classify by whether goal_R ∈ G or goal_R = {{neg P}}.
            subst hB_pol
            have hNonGoalR : ∀ C, (C ∈ jFilter S_R ∨ C ∈ defFilter S_R) →
                C ∈ Finset.union J' (ClauseSequent.ofList defs') := fun C hC =>
              right_neg_nongoal_subset_JD G As P J' defs' goals' hGoals' hSConc C hC
            -- goal_R ∈ S_R; split on G vs {{neg P}}.
            have hGoalR_inSR : goal_R ∈ S_R := ((Finset.mem_filter_exp _ _ _).mp hGoalR_mem).1
            rw [show S_R = Finset.union G (ClauseSequent.single (Clause.single (Literal.neg P)))
                from rfl, Finset.mem_union] at hGoalR_inSR
            rcases hGoalR_inSR with hGR_G | hGR_single
            · -- goal_R ∈ G → goal_R ∈ ofList(goals'). Direct weakening via fromSubset.
              have hGR_goals : goal_R ∈ ClauseSequent.ofList goals' :=
                goalFromG goal_R hGR_G hGoalR_goal
              obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp
                ((Finset.mem_ofList_exp _ _).mp hGR_goals)
              exact fromSubset S_R i_R T_R (Or.inr hd_R) hNonGoalR j hj hjeq
            · -- goal_R = {{neg P}}. Sub-case dispatch on goal_L location.
              have _hGR_eq : goal_R = Clause.single (Literal.neg P) :=
                mem_csingle _ _ |>.mp hGR_single
              have hGoalL_inSL : goal_L ∈ S_L := ((Finset.mem_filter_exp _ _ _).mp hGoalL_mem).1
              rw [show S_L = Finset.union G As from rfl, Finset.mem_union] at hGoalL_inSL
              -- Non-goal A ∈ As: cwl(A, neg P) = A ∪ {neg P} is non-goal (has pos),
              -- so cwl(A, neg P) ∈ JD'.
              have cwlAsNg_in_JD : ∀ A ∈ As, ¬isGoalClause A →
                  clauseWithLiteral A (Literal.neg P) ∈
                    Finset.union J' (ClauseSequent.ofList defs') := by
                intro A hA hAng
                -- cwl(A, neg P) is non-goal because A is non-goal and adding neg P preserves that
                have hCwlInS : clauseWithLiteral A (Literal.neg P) ∈
                    Finset.union G (ClauseSequent.mapSet As
                      (fun A => clauseWithLiteral A (Literal.neg P))) :=
                  (Finset.mem_union_exp _ _ _).mpr
                    (Or.inr ((mem_image_iff _ _ _).mpr ⟨A, hA, rfl⟩))
                rw [hSConc] at hCwlInS
                rw [Finset.mem_union] at hCwlInS
                rcases hCwlInS with hJD | hGoalC
                · exact hJD
                · exfalso
                  apply hAng
                  have hCwlGoal : isGoalClause (clauseWithLiteral A (Literal.neg P)) :=
                    hGoals' _ ((Finset.mem_ofList_exp _ _).mp hGoalC)
                  -- A ⊆ cwl(A, neg P); goal property propagates to subset
                  refine ⟨?_, ?_⟩
                  · refine ⟨lT'.ordinary A (Finset.mem_union.mpr (Or.inr hA)), ?_⟩
                    intro Q R hQ hR
                    exact hCwlGoal.1.2 Q R
                      ((Finset.mem_insert_exp _ _ _).mpr (Or.inr hQ))
                      ((Finset.mem_insert_exp _ _ _).mpr (Or.inr hR))
                  · intro l hl
                    exact hCwlGoal.2 l ((Finset.mem_insert_exp _ _ _).mpr (Or.inr hl))
              -- Goal A ∈ As: cwl(A, neg P) = A ∪ {neg P} is all-negative, hence in goals'.
              have cwlAsG_in_goals : ∀ A ∈ As, isGoalClause A →
                  clauseWithLiteral A (Literal.neg P) ∈ ClauseSequent.ofList goals' := by
                intro A hA hAg
                have hCwlInS : clauseWithLiteral A (Literal.neg P) ∈
                    Finset.union G (ClauseSequent.mapSet As
                      (fun A => clauseWithLiteral A (Literal.neg P))) :=
                  (Finset.mem_union_exp _ _ _).mpr
                    (Or.inr ((mem_image_iff _ _ _).mpr ⟨A, hA, rfl⟩))
                rw [hSConc] at hCwlInS
                rw [Finset.mem_union] at hCwlInS
                rcases hCwlInS with hJD | hGoalC
                · exfalso
                  -- cwl(A, neg P) ∈ JD' means single-positive or definite with ≥2 lits
                  -- Either way it has a positive literal, but cwl of a goal + neg P is all-negative.
                  have hCwlG : isGoalClause (clauseWithLiteral A (Literal.neg P)) := by
                    refine ⟨?_, ?_⟩
                    · refine ⟨Clause.ordinary_of_mem (Finset.mem_insert.mpr (Or.inl rfl)), ?_⟩
                      intro Q R hQ hR
                      have hQ' := (Finset.mem_insert_exp _ _ _).mp hQ
                      have hR' := (Finset.mem_insert_exp _ _ _).mp hR
                      rcases hQ' with hQN | hQA
                      · exact Literal.noConfusion hQN
                      · rcases hR' with hRN | hRA
                        · exact absurd hRN Literal.noConfusion
                        · exact hAg.1.2 Q R hQA hRA
                    · intro l hl
                      have hl' := (Finset.mem_insert_exp _ _ _).mp hl
                      rcases hl' with rfl | hlA
                      · trivial
                      · exact hAg.2 l hlA
                  rw [Finset.mem_union] at hJD
                  rcases hJD with hJ | hD
                  · obtain ⟨Q, hQ⟩ := hJ' _ hJ
                    exact absurd (hCwlG.2 (Literal.pos Q) (hQ ▸ (Finset.mem_singleton _ _).mpr rfl))
                      (by simp)
                  · obtain ⟨⟨_, ⟨Q, hQ⟩⟩, _⟩ := hDefs' _ ((Finset.mem_ofList_exp _ _).mp hD)
                    exact absurd (hCwlG.2 (Literal.pos Q) hQ) (by simp)
                · exact hGoalC
              -- JD' ∪ (mapSet As_ng cwl) = JD' when As_ng only has non-goals.
              have mapSet_Asng_sub_JD : ∀ C ∈ ClauseSequent.mapSet
                  (Finset.filter (fun A => !isGoalClauseB A) As)
                  (fun A => clauseWithLiteral A (Literal.neg P)),
                  C ∈ Finset.union J' (ClauseSequent.ofList defs') := by
                intro C hC
                obtain ⟨A, hA, rfl⟩ := (mem_image_iff _ _ _).mp hC
                have ⟨hAAs, hAng⟩ := (Finset.mem_filter_exp _ _ _).mp hA
                exact cwlAsNg_in_JD A hAAs (fun hg => by
                  rw [isGoalClauseB_complete A hg] at hAng; exact absurd hAng (by decide))
              rcases hGoalL_inSL with hGL_G | hGL_As
              · -- goal_L ∈ G → goal_L is a goal in G → goal_L ∈ goals'.
                have hGL_goals : goal_L ∈ ClauseSequent.ofList goals' :=
                  goalFromG goal_L hGL_G hGoalL_goal
                obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp
                  ((Finset.mem_ofList_exp _ _).mp hGL_goals)
                -- Decide whether As has a non-goal element.
                by_cases hAsNg : ∃ A ∈ As, ¬isGoalClause A
                · -- As_ng nonempty: rule reconstruction.
                  let As_ng : ClauseSequent := Finset.filter (fun A => !isGoalClauseB A) As
                  obtain ⟨A0, hA0As, hA0ng⟩ := hAsNg
                  have hA0ngB : isGoalClauseB A0 = false := by
                    cases hv : isGoalClauseB A0 with
                    | false => rfl
                    | true => exact absurd (isGoalClauseB_sound A0 hv) hA0ng
                  have hA0_inAsng : A0 ∈ As_ng :=
                    (Finset.mem_filter_exp _ _ _).mpr ⟨hA0As, by simp [hA0ngB]⟩
                  have hAsng_sub_As : ∀ A, A ∈ As_ng → A ∈ As := fun A hA =>
                    ((Finset.mem_filter_exp _ _ _).mp hA).1
                  -- JD_L ⊆ JD' ∪ As_ng
                  have hJDL_sub : ∀ C, C ∈ Finset.union (Finset.union (jFilter S_L)
                      (ClauseSequent.ofList (defFilterList S_L))) (ClauseSequent.single goal_L) →
                      C ∈ Finset.union (Finset.union J' (ClauseSequent.ofList defs'))
                        (Finset.union (ClauseSequent.single goal_L) As_ng) := by
                    intro C hC
                    rw [Finset.mem_union] at hC
                    rcases hC with hJD | hGoalC
                    · -- C ∈ JD_L
                      have hC_inSL : C ∈ S_L := by
                        rw [Finset.mem_union] at hJD
                        rcases hJD with h | h
                        · exact ((Finset.mem_filter_exp _ _ _).mp h).1
                        · rw [ofList_defFilterList] at h
                          exact ((Finset.mem_filter_exp _ _ _).mp h).1
                      have hCng : isGoalClauseB C = false := filter_nongoal _ C (by
                        rw [Finset.mem_union] at hJD
                        rcases hJD with h | h
                        · exact Or.inl h
                        · rw [ofList_defFilterList] at h; exact Or.inr h)
                      rw [show S_L = Finset.union G As from rfl, Finset.mem_union] at hC_inSL
                      rcases hC_inSL with hCG | hCA
                      · -- C ∈ G non-goal → C ∈ JD' (via hSConc)
                        have hCinS' : C ∈ Finset.union (Finset.union J' (ClauseSequent.ofList defs'))
                            (ClauseSequent.ofList goals') :=
                          hSConc ▸ (Finset.mem_union_exp _ _ _).mpr (Or.inl hCG)
                        rw [Finset.mem_union] at hCinS'
                        rcases hCinS' with hJD' | hGoal'
                        · exact (Finset.mem_union_exp _ _ _).mpr (Or.inl hJD')
                        · exfalso
                          have := isGoalClauseB_complete C
                            (hGoals' _ ((Finset.mem_ofList_exp _ _).mp hGoal'))
                          rw [this] at hCng; exact absurd hCng (by decide)
                      · -- C ∈ As non-goal → C ∈ As_ng
                        refine (Finset.mem_union_exp _ _ _).mpr (Or.inr
                          ((Finset.mem_union_exp _ _ _).mpr (Or.inr ?_)))
                        exact (Finset.mem_filter_exp _ _ _).mpr ⟨hCA, by simp [hCng]⟩
                    · -- C = goal_L
                      refine (Finset.mem_union_exp _ _ _).mpr (Or.inr
                        ((Finset.mem_union_exp _ _ _).mpr (Or.inl hGoalC)))
                  -- Build the weakened leftTree
                  have hDepthTL : proofDepth T_L ≤ proofDepth lT' := hd_L
                  obtain ⟨leftTree_new, hdL_new⟩ := gcnf_superset_bounded _ _ hJDL_sub
                    T_L (proofDepth lT') hDepthTL (by
                      repeat first
                        | exact hJDOrd
                        | exact ordinary_right T_L
                        | exact ordinary_right T_R
                        | exact ClauseSequent.ordinary_single (Clause.single_ordinary _)
                        | apply ClauseSequent.ordinary_union
                        | exact ClauseSequent.ordinary_subset hAsOrd (fun C hC => (Finset.mem_filter.mp hC).1)
                        | exact ClauseSequent.ordinary_subset hAsOrd (fun C hC => (Finset.mem_union.mp hC).elim id id)
                        | (intro C hC; apply hRootOrd C; rw [hS']; exact Finset.mem_union.mpr (Or.inr (Finset.mem_ofList.mpr (by rw [(mem_csingle _ _).mp hC]; exact List.get_mem _ _)))))
                  -- Now build the weakened rightTree: T_R : JD_R ∪ {goal_R=(neg P)}
                  -- We need JD' ∪ {goal_L} ∪ {{neg P}}
                  have hJDR_sub : ∀ C, C ∈ Finset.union (Finset.union (jFilter S_R)
                      (ClauseSequent.ofList (defFilterList S_R))) (ClauseSequent.single goal_R) →
                      C ∈ Finset.union (Finset.union (Finset.union J' (ClauseSequent.ofList defs'))
                        (ClauseSequent.single goal_L))
                        (ClauseSequent.single (Clause.single (Literal.neg P))) := by
                    intro C hC
                    rw [Finset.mem_union] at hC
                    rcases hC with hJD | hGoalC
                    · -- C ∈ JD_R → C ∈ JD'
                      have hCJD' : C ∈ Finset.union J' (ClauseSequent.ofList defs') :=
                        hNonGoalR C (by
                          rw [Finset.mem_union] at hJD
                          rcases hJD with h | h
                          · exact Or.inl h
                          · rw [ofList_defFilterList] at h; exact Or.inr h)
                      exact (Finset.mem_union_exp _ _ _).mpr (Or.inl
                        ((Finset.mem_union_exp _ _ _).mpr (Or.inl hCJD')))
                    · -- C = goal_R = {{neg P}}
                      rw [(Finset.mem_singleton C _).mp hGoalC, _hGR_eq]
                      exact (Finset.mem_union_exp _ _ _).mpr (Or.inr
                        ((Finset.mem_singleton _ _).mpr rfl))
                  have hDepthTR : proofDepth T_R ≤ proofDepth rT' := hd_R
                  obtain ⟨rightTree_new, hdR_new⟩ := gcnf_superset_bounded _ _ hJDR_sub
                    T_R (proofDepth rT') hDepthTR (by
                      repeat first
                        | exact hJDOrd
                        | exact ordinary_right T_L
                        | exact ordinary_right T_R
                        | exact ClauseSequent.ordinary_single (Clause.single_ordinary _)
                        | apply ClauseSequent.ordinary_union
                        | exact ClauseSequent.ordinary_subset hAsOrd (fun C hC => (Finset.mem_filter.mp hC).1)
                        | exact ClauseSequent.ordinary_subset hAsOrd (fun C hC => (Finset.mem_union.mp hC).elim id id)
                        | (intro C hC; apply hRootOrd C; rw [hS']; exact Finset.mem_union.mpr (Or.inr (Finset.mem_ofList.mpr (by rw [(mem_csingle _ _).mp hC]; exact List.get_mem _ _)))))
                  -- Apply rule with Gamma = JD' ∪ {goal_L}, As = As_ng, B = neg P, Cs = As_ng
                  let Gamma_new : ClauseSequent := Finset.union
                    (Finset.union J' (ClauseSequent.ofList defs'))
                    (ClauseSequent.single goal_L)
                  have hLeftIdx : Finset.union (Finset.union J' (ClauseSequent.ofList defs'))
                      (Finset.union (ClauseSequent.single goal_L) As_ng) =
                      Finset.union Gamma_new As_ng := by
                    apply Finset.ext; intro C
                    constructor
                    · intro hC
                      rw [Finset.mem_union] at hC
                      rcases hC with h | hInner
                      · exact (Finset.mem_union_exp _ _ _).mpr (Or.inl
                          ((Finset.mem_union_exp _ _ _).mpr (Or.inl h)))
                      · rw [Finset.mem_union] at hInner
                        rcases hInner with h | h
                        · exact (Finset.mem_union_exp _ _ _).mpr (Or.inl
                            ((Finset.mem_union_exp _ _ _).mpr (Or.inr h)))
                        · exact (Finset.mem_union_exp _ _ _).mpr (Or.inr h)
                    · intro hC
                      rw [Finset.mem_union] at hC
                      rcases hC with hG | h
                      · rw [show Gamma_new = Finset.union (Finset.union J' (ClauseSequent.ofList defs'))
                            (ClauseSequent.single goal_L) from rfl, Finset.mem_union] at hG
                        rcases hG with h | h
                        · exact (Finset.mem_union_exp _ _ _).mpr (Or.inl h)
                        · exact (Finset.mem_union_exp _ _ _).mpr (Or.inr
                            ((Finset.mem_union_exp _ _ _).mpr (Or.inl h)))
                      · exact (Finset.mem_union_exp _ _ _).mpr (Or.inr
                          ((Finset.mem_union_exp _ _ _).mpr (Or.inr h)))
                  let leftTree_final : GCNFProofTree (Finset.union Gamma_new As_ng) :=
                    hLeftIdx ▸ leftTree_new
                  let rightTree_final : GCNFProofTree (Finset.union Gamma_new
                    (ClauseSequent.single (Clause.single (Literal.neg P)))) :=
                    rightTree_new
                  -- Rule node
                  let ruleTree : GCNFProofTree (Finset.union Gamma_new
                      (ClauseSequent.mapSet As_ng (fun A => clauseWithLiteral A (Literal.neg P)))) :=
                    GCNFProofTree.rule Gamma_new As_ng (Literal.neg P) As_ng
                      Gamma_new Gamma_new (ordinary_left leftTree_final) (ordinary_right leftTree_final) leftTree_final rightTree_final
                      ⟨A0, hA0_inAsng⟩ (fun C hC => hC)
                      (fun C hC => (Finset.mem_union_exp _ _ _).mpr (Or.inl hC))
                      (fun C hC => (Finset.mem_union_exp _ _ _).mpr (Or.inl hC))
                  -- The conclusion equals JD' ∪ {goal_L}
                  have hConclEq : Finset.union Gamma_new
                      (ClauseSequent.mapSet As_ng (fun A => clauseWithLiteral A (Literal.neg P))) =
                      Finset.union (Finset.union J' (ClauseSequent.ofList defs'))
                        (ClauseSequent.single (goals'.get ⟨j, hj⟩)) := by
                    apply Finset.ext; intro C
                    constructor
                    · intro hC
                      rw [Finset.mem_union] at hC
                      rcases hC with hGamma | hMap
                      · rw [show Gamma_new = Finset.union
                            (Finset.union J' (ClauseSequent.ofList defs'))
                            (ClauseSequent.single goal_L) from rfl, Finset.mem_union] at hGamma
                        rcases hGamma with hJD | hGL
                        · exact (Finset.mem_union_exp _ _ _).mpr (Or.inl hJD)
                        · rw [(Finset.mem_singleton C _).mp hGL,
                              show goals'.get ⟨j, hj⟩ = goals'[j] from rfl, hjeq]
                          exact (Finset.mem_union_exp _ _ _).mpr
                            (Or.inr ((Finset.mem_singleton _ _).mpr rfl))
                      · exact (Finset.mem_union_exp _ _ _).mpr
                          (Or.inl (mapSet_Asng_sub_JD C hMap))
                    · intro hC
                      rw [Finset.mem_union] at hC
                      rcases hC with hJD | hGL
                      · refine (Finset.mem_union_exp _ _ _).mpr (Or.inl ?_)
                        show C ∈ Finset.union (Finset.union J' _) _
                        exact (Finset.mem_union_exp _ _ _).mpr (Or.inl hJD)
                      · rw [(Finset.mem_singleton C _).mp hGL,
                            show goals'.get ⟨j, hj⟩ = goals'[j] from rfl, hjeq]
                        refine (Finset.mem_union_exp _ _ _).mpr (Or.inl ?_)
                        show goal_L ∈ Finset.union (Finset.union J' _) (ClauseSequent.single goal_L)
                        exact (Finset.mem_union_exp _ _ _).mpr
                          (Or.inr ((Finset.mem_singleton _ _).mpr rfl))
                  refine ⟨⟨j, hj⟩, hConclEq ▸ ruleTree, ?_⟩
                  rw [proofDepth_eq_transport hConclEq ruleTree]
                  show 1 + max (proofDepth leftTree_final) (proofDepth rightTree_final) ≤ n
                  have hPDLF : proofDepth leftTree_final = proofDepth leftTree_new :=
                    proofDepth_eq_transport hLeftIdx leftTree_new
                  have hPDRF : proofDepth rightTree_final = proofDepth rightTree_new := rfl
                  rw [hPDLF, hPDRF]
                  have hn : n = 1 + max (proofDepth lT') (proofDepth rT') := by
                    rw [← hDepth',
                        show proofDepth lT' = proofDepth lT from proofDepth_eq_transport hLeq lT,
                        show proofDepth rT' = proofDepth rT from proofDepth_eq_transport hReq rT]
                    rfl
                  omega
                · -- As_ng empty: all A ∈ As are goals, so JD_L ⊆ JD'. Direct weakening.
                  -- Rewrite hAsNg : ¬∃ A ∈ As, ¬isGoalClause A  ⟹  ∀ A ∈ As, isGoalClause A
                  have hAllAsGoal : ∀ A, A ∈ As → isGoalClause A := fun A hA =>
                    Classical.byContradiction fun hng => hAsNg ⟨A, hA, hng⟩
                  have hJDL_sub : ∀ C, C ∈ Finset.union (Finset.union (jFilter S_L)
                      (ClauseSequent.ofList (defFilterList S_L))) (ClauseSequent.single goal_L) →
                      C ∈ Finset.union (Finset.union J' (ClauseSequent.ofList defs'))
                        (ClauseSequent.single (goals'.get ⟨j, hj⟩)) := by
                    intro C hC
                    rw [Finset.mem_union] at hC
                    rcases hC with hJD | hGoalC
                    · have hC_inSL : C ∈ S_L := by
                        rw [Finset.mem_union] at hJD
                        rcases hJD with h | h
                        · exact ((Finset.mem_filter_exp _ _ _).mp h).1
                        · rw [ofList_defFilterList] at h
                          exact ((Finset.mem_filter_exp _ _ _).mp h).1
                      have hCng : isGoalClauseB C = false := filter_nongoal _ C (by
                        rw [Finset.mem_union] at hJD
                        rcases hJD with h | h
                        · exact Or.inl h
                        · rw [ofList_defFilterList] at h; exact Or.inr h)
                      have hCng' : ¬isGoalClause C := fun hg => by
                        rw [isGoalClauseB_complete C hg] at hCng; exact absurd hCng (by decide)
                      rw [show S_L = Finset.union G As from rfl, Finset.mem_union] at hC_inSL
                      rcases hC_inSL with hCG | hCA
                      · have hCinS' : C ∈ Finset.union (Finset.union J' (ClauseSequent.ofList defs'))
                            (ClauseSequent.ofList goals') :=
                          hSConc ▸ (Finset.mem_union_exp _ _ _).mpr (Or.inl hCG)
                        rw [Finset.mem_union] at hCinS'
                        rcases hCinS' with hJD' | hGoal'
                        · exact (Finset.mem_union_exp _ _ _).mpr (Or.inl hJD')
                        · exact absurd (hGoals' _ ((Finset.mem_ofList_exp _ _).mp hGoal')) hCng'
                      · exact absurd (hAllAsGoal C hCA) hCng'
                    · rw [(Finset.mem_singleton C _).mp hGoalC,
                          show goals'.get ⟨j, hj⟩ = goals'[j] from rfl, hjeq]
                      exact (Finset.mem_union_exp _ _ _).mpr
                        (Or.inr ((Finset.mem_singleton _ _).mpr rfl))
                  have hDepthTL : proofDepth T_L ≤ proofDepth lT' := hd_L
                  obtain ⟨T'', hd''⟩ := gcnf_superset_bounded _ _ hJDL_sub
                    T_L (proofDepth lT') hDepthTL (by
                      repeat first
                        | exact hJDOrd
                        | exact ordinary_right T_L
                        | exact ordinary_right T_R
                        | exact ClauseSequent.ordinary_single (Clause.single_ordinary _)
                        | apply ClauseSequent.ordinary_union
                        | exact ClauseSequent.ordinary_subset hAsOrd (fun C hC => (Finset.mem_filter.mp hC).1)
                        | exact ClauseSequent.ordinary_subset hAsOrd (fun C hC => (Finset.mem_union.mp hC).elim id id)
                        | (intro C hC; apply hRootOrd C; rw [hS']; exact Finset.mem_union.mpr (Or.inr (Finset.mem_ofList.mpr (by rw [(mem_csingle _ _).mp hC]; exact List.get_mem _ _)))))
                  exact ⟨⟨j, hj⟩, T'', by omega⟩
              · -- goal_L ∈ As. cwl(goal_L, neg P) ∈ ofList(goals'). Rule reconstruction.
                have hGL_goalClause : isGoalClause goal_L := hGoalL_goal
                have hCwlGL_goals : clauseWithLiteral goal_L (Literal.neg P) ∈
                    ClauseSequent.ofList goals' := cwlAsG_in_goals goal_L hGL_As hGL_goalClause
                obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp
                  ((Finset.mem_ofList_exp _ _).mp hCwlGL_goals)
                -- As_ng = non-goal As, then As_new = {goal_L} ∪ As_ng.
                let As_ng : ClauseSequent := Finset.filter (fun A => !isGoalClauseB A) As
                let As_new : ClauseSequent :=
                  Finset.union (ClauseSequent.single goal_L) As_ng
                have hAs_new_nonempty : ∃ A, A ∈ As_new :=
                  ⟨goal_L, (Finset.mem_union_exp _ _ _).mpr
                    (Or.inl ((Finset.mem_singleton _ _).mpr rfl))⟩
                have hAs_new_sub_As : ∀ A, A ∈ As_new → A ∈ As := by
                  intro A hA
                  rw [show As_new = Finset.union (ClauseSequent.single goal_L) As_ng from rfl,
                      Finset.mem_union] at hA
                  rcases hA with h | h
                  · rw [(Finset.mem_singleton _ _).mp h]; exact hGL_As
                  · exact ((Finset.mem_filter_exp _ _ _).mp h).1
                -- JD_L ⊆ JD' ∪ As_new (since goal_L ∈ As_new, As_ng ⊆ As_new)
                have hJDL_sub : ∀ C, C ∈ Finset.union (Finset.union (jFilter S_L)
                    (ClauseSequent.ofList (defFilterList S_L))) (ClauseSequent.single goal_L) →
                    C ∈ Finset.union (Finset.union J' (ClauseSequent.ofList defs')) As_new := by
                  intro C hC
                  rw [Finset.mem_union] at hC
                  rcases hC with hJD | hGoalC
                  · have hC_inSL : C ∈ S_L := by
                      rw [Finset.mem_union] at hJD
                      rcases hJD with h | h
                      · exact ((Finset.mem_filter_exp _ _ _).mp h).1
                      · rw [ofList_defFilterList] at h
                        exact ((Finset.mem_filter_exp _ _ _).mp h).1
                    have hCng : isGoalClauseB C = false := filter_nongoal _ C (by
                      rw [Finset.mem_union] at hJD
                      rcases hJD with h | h
                      · exact Or.inl h
                      · rw [ofList_defFilterList] at h; exact Or.inr h)
                    rw [show S_L = Finset.union G As from rfl, Finset.mem_union] at hC_inSL
                    rcases hC_inSL with hCG | hCA
                    · have hCinS' : C ∈ Finset.union (Finset.union J' (ClauseSequent.ofList defs'))
                          (ClauseSequent.ofList goals') :=
                        hSConc ▸ (Finset.mem_union_exp _ _ _).mpr (Or.inl hCG)
                      rw [Finset.mem_union] at hCinS'
                      rcases hCinS' with hJD' | hGoal'
                      · exact (Finset.mem_union_exp _ _ _).mpr (Or.inl hJD')
                      · exfalso
                        have := isGoalClauseB_complete C
                          (hGoals' _ ((Finset.mem_ofList_exp _ _).mp hGoal'))
                        rw [this] at hCng; exact absurd hCng (by decide)
                    · refine (Finset.mem_union_exp _ _ _).mpr (Or.inr ?_)
                      show C ∈ Finset.union (ClauseSequent.single goal_L) As_ng
                      exact (Finset.mem_union_exp _ _ _).mpr
                        (Or.inr ((Finset.mem_filter_exp _ _ _).mpr ⟨hCA, by simp [hCng]⟩))
                  · refine (Finset.mem_union_exp _ _ _).mpr (Or.inr ?_)
                    show C ∈ Finset.union (ClauseSequent.single goal_L) As_ng
                    exact (Finset.mem_union_exp _ _ _).mpr (Or.inl hGoalC)
                have hDepthTL : proofDepth T_L ≤ proofDepth lT' := hd_L
                obtain ⟨leftTree_new, hdL_new⟩ := gcnf_superset_bounded _ _ hJDL_sub
                  T_L (proofDepth lT') hDepthTL (by
                      repeat first
                        | exact hJDOrd
                        | exact ordinary_right T_L
                        | exact ordinary_right T_R
                        | exact ClauseSequent.ordinary_single (Clause.single_ordinary _)
                        | apply ClauseSequent.ordinary_union
                        | exact ClauseSequent.ordinary_subset hAsOrd (fun C hC => (Finset.mem_filter.mp hC).1)
                        | exact ClauseSequent.ordinary_subset hAsOrd (fun C hC => (Finset.mem_union.mp hC).elim id id)
                        | (intro C hC; apply hRootOrd C; rw [hS']; exact Finset.mem_union.mpr (Or.inr (Finset.mem_ofList.mpr (by rw [(mem_csingle _ _).mp hC]; exact List.get_mem _ _)))))
                -- JD_R ⊆ JD' (T_R's goal_R = {{neg P}})
                have hJDR_sub : ∀ C, C ∈ Finset.union (Finset.union (jFilter S_R)
                    (ClauseSequent.ofList (defFilterList S_R))) (ClauseSequent.single goal_R) →
                    C ∈ Finset.union (Finset.union J' (ClauseSequent.ofList defs'))
                      (ClauseSequent.single (Clause.single (Literal.neg P))) := by
                  intro C hC
                  rw [Finset.mem_union] at hC
                  rcases hC with hJD | hGoalC
                  · have hCJD' : C ∈ Finset.union J' (ClauseSequent.ofList defs') :=
                      hNonGoalR C (by
                        rw [Finset.mem_union] at hJD
                        rcases hJD with h | h
                        · exact Or.inl h
                        · rw [ofList_defFilterList] at h; exact Or.inr h)
                    exact (Finset.mem_union_exp _ _ _).mpr (Or.inl hCJD')
                  · rw [(Finset.mem_singleton C _).mp hGoalC, _hGR_eq]
                    exact (Finset.mem_union_exp _ _ _).mpr
                      (Or.inr ((Finset.mem_singleton _ _).mpr rfl))
                have hDepthTR : proofDepth T_R ≤ proofDepth rT' := hd_R
                obtain ⟨rightTree_new, hdR_new⟩ := gcnf_superset_bounded _ _ hJDR_sub
                  T_R (proofDepth rT') hDepthTR (by
                      repeat first
                        | exact hJDOrd
                        | exact ordinary_right T_L
                        | exact ordinary_right T_R
                        | exact ClauseSequent.ordinary_single (Clause.single_ordinary _)
                        | apply ClauseSequent.ordinary_union
                        | exact ClauseSequent.ordinary_subset hAsOrd (fun C hC => (Finset.mem_filter.mp hC).1)
                        | exact ClauseSequent.ordinary_subset hAsOrd (fun C hC => (Finset.mem_union.mp hC).elim id id)
                        | (intro C hC; apply hRootOrd C; rw [hS']; exact Finset.mem_union.mpr (Or.inr (Finset.mem_ofList.mpr (by rw [(mem_csingle _ _).mp hC]; exact List.get_mem _ _)))))
                let Gamma_new : ClauseSequent := Finset.union J' (ClauseSequent.ofList defs')
                let ruleTree : GCNFProofTree (Finset.union Gamma_new
                    (ClauseSequent.mapSet As_new (fun A => clauseWithLiteral A (Literal.neg P)))) :=
                  GCNFProofTree.rule Gamma_new As_new (Literal.neg P) As_new
                    Gamma_new Gamma_new (ordinary_left leftTree_new) (ordinary_right leftTree_new) leftTree_new rightTree_new
                    hAs_new_nonempty (fun C hC => hC)
                    (fun C hC => (Finset.mem_union_exp _ _ _).mpr (Or.inl hC))
                    (fun C hC => (Finset.mem_union_exp _ _ _).mpr (Or.inl hC))
                have hConclEq : Finset.union Gamma_new
                    (ClauseSequent.mapSet As_new (fun A => clauseWithLiteral A (Literal.neg P))) =
                    Finset.union (Finset.union J' (ClauseSequent.ofList defs'))
                      (ClauseSequent.single (goals'.get ⟨j, hj⟩)) := by
                  apply Finset.ext; intro C
                  constructor
                  · intro hC
                    rw [Finset.mem_union] at hC
                    rcases hC with hGamma | hMap
                    · exact (Finset.mem_union_exp _ _ _).mpr (Or.inl hGamma)
                    · obtain ⟨A, hA, rfl⟩ := (mem_image_iff _ _ _).mp hMap
                      rw [show As_new = Finset.union (ClauseSequent.single goal_L) As_ng from rfl,
                          Finset.mem_union] at hA
                      rcases hA with hAgl | hAng
                      · rw [(Finset.mem_singleton A _).mp hAgl,
                            show goals'.get ⟨j, hj⟩ = goals'[j] from rfl, hjeq]
                        exact (Finset.mem_union_exp _ _ _).mpr
                          (Or.inr ((Finset.mem_singleton _ _).mpr rfl))
                      · have ⟨hAAs, hAng'⟩ := (Finset.mem_filter_exp _ _ _).mp hAng
                        have hAng'' : ¬isGoalClause A := fun hg => by
                          rw [isGoalClauseB_complete A hg] at hAng'; exact absurd hAng' (by decide)
                        exact (Finset.mem_union_exp _ _ _).mpr
                          (Or.inl (cwlAsNg_in_JD A hAAs hAng''))
                  · intro hC
                    rw [Finset.mem_union] at hC
                    rcases hC with hJD | hGL
                    · exact (Finset.mem_union_exp _ _ _).mpr (Or.inl hJD)
                    · rw [(Finset.mem_singleton C _).mp hGL,
                          show goals'.get ⟨j, hj⟩ = goals'[j] from rfl, hjeq]
                      refine (Finset.mem_union_exp _ _ _).mpr (Or.inr ?_)
                      exact (mem_image_iff _ _ _).mpr ⟨goal_L,
                        (Finset.mem_union_exp _ _ _).mpr (Or.inl ((Finset.mem_singleton _ _).mpr rfl)),
                        rfl⟩
                refine ⟨⟨j, hj⟩, hConclEq ▸ ruleTree, ?_⟩
                rw [proofDepth_eq_transport hConclEq ruleTree]
                show 1 + max (proofDepth leftTree_new) (proofDepth rightTree_new) ≤ n
                have hn : n = 1 + max (proofDepth lT') (proofDepth rT') := by
                  rw [← hDepth',
                      show proofDepth lT' = proofDepth lT from proofDepth_eq_transport hLeq lT,
                      show proofDepth rT' = proofDepth rT from proofDepth_eq_transport hReq rT]
                  rfl
                omega
          | pos P =>
            -- Case 3 (textbook): B = pos P. Use left subtree path.
            -- goal_L ∈ S_L = G ∪ As. Classify by whether goal_L ∈ G or goal_L ∈ As.
            subst hB_pol
            have hNonGoalL : ∀ C, (C ∈ jFilter S_L ∨ C ∈ defFilter S_L) →
                C ∈ Finset.union J' (ClauseSequent.ofList defs') := fun C hC =>
              left_pos_nongoal_subset_JD G As P J' defs' goals' hGoals' hJ' hDefs' hSConc
                hHornS_all (fun C hC => lT'.ordinary C (Finset.mem_union.mpr (Or.inr hC))) C hC
            have hGoalL_inSL : goal_L ∈ S_L := ((Finset.mem_filter_exp _ _ _).mp hGoalL_mem).1
            rw [show S_L = Finset.union G As from rfl, Finset.mem_union] at hGoalL_inSL
            rcases hGoalL_inSL with hGL_G | hGL_As
            · -- goal_L ∈ G → goal_L ∈ ofList(goals') via goalFromG. Direct weakening.
              have hGL_goals : goal_L ∈ ClauseSequent.ofList goals' :=
                goalFromG goal_L hGL_G hGoalL_goal
              obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp
                ((Finset.mem_ofList_exp _ _).mp hGL_goals)
              exact fromSubset S_L i_L T_L (Or.inl hd_L) hNonGoalL j hj hjeq
            · -- goal_L ∈ As. cwl(goal_L, pos P) has pos P, so non-goal → in JD'.
              -- Rule reconstruction using goal_R from T_R in outer Gamma.
              -- cwl(goal_L, pos P) is non-goal (has pos P), so it's in JD'.
              have hCwlGL_JD : clauseWithLiteral goal_L (Literal.pos P) ∈
                  Finset.union J' (ClauseSequent.ofList defs') := by
                have hCwlInS : clauseWithLiteral goal_L (Literal.pos P) ∈
                    Finset.union G (ClauseSequent.mapSet As
                      (fun A => clauseWithLiteral A (Literal.pos P))) :=
                  (Finset.mem_union_exp _ _ _).mpr
                    (Or.inr ((mem_image_iff _ _ _).mpr ⟨goal_L, hGL_As, rfl⟩))
                rw [hSConc] at hCwlInS
                rw [Finset.mem_union] at hCwlInS
                rcases hCwlInS with hJD | hGoalC
                · exact hJD
                · exfalso
                  -- cwl(goal_L, pos P) in goals' means it's a goal, but it contains pos P
                  have hCwlG : isGoalClause (clauseWithLiteral goal_L (Literal.pos P)) :=
                    hGoals' _ ((Finset.mem_ofList_exp _ _).mp hGoalC)
                  have hPosInCwl : Literal.pos P ∈ clauseWithLiteral goal_L (Literal.pos P) :=
                    (Finset.mem_insert_exp _ _ _).mpr (Or.inl rfl)
                  exact absurd (hCwlG.2 _ hPosInCwl) (by simp)
              -- goal_R ∈ S_R = G ∪ {{pos P}}. {pos P} is not a goal (has positive),
              -- so goal_R ∈ G and is a goal clause → goal_R ∈ goals'.
              have hGoalR_inSR : goal_R ∈ S_R := ((Finset.mem_filter_exp _ _ _).mp hGoalR_mem).1
              rw [show S_R = Finset.union G (ClauseSequent.single (Clause.single (Literal.pos P)))
                  from rfl, Finset.mem_union] at hGoalR_inSR
              have hGR_inG : goal_R ∈ G := by
                rcases hGoalR_inSR with hG | hSing
                · exact hG
                · exfalso
                  have hGReq : goal_R = Clause.single (Literal.pos P) :=
                    mem_csingle _ _ |>.mp hSing
                  have hPosInGR : Literal.pos P ∈ goal_R :=
                    hGReq ▸ (Finset.mem_singleton _ _).mpr rfl
                  exact absurd (hGoalR_goal.2 _ hPosInGR) (by simp)
              have hGR_goals : goal_R ∈ ClauseSequent.ofList goals' :=
                goalFromG goal_R hGR_inG hGoalR_goal
              obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp
                ((Finset.mem_ofList_exp _ _).mp hGR_goals)
              -- Rule reconstruction:
              --   Gamma_new = JD' ∪ {goal_R}
              --   As_new = Cs_new = {goal_L}
              --   B = pos P
              --   Conclusion: (JD' ∪ {goal_R}) ∪ {cwl(goal_L, pos P)} = JD' ∪ {goal_R} since
              --     cwl(goal_L, pos P) ∈ JD'
              let Gamma_new : ClauseSequent := Finset.union
                (Finset.union J' (ClauseSequent.ofList defs')) (ClauseSequent.single goal_R)
              let As_new : ClauseSequent := ClauseSequent.single goal_L
              have hAs_new_nonempty : ∃ A, A ∈ As_new :=
                ⟨goal_L, (Finset.mem_singleton _ _).mpr rfl⟩
              -- leftTree_new : Gamma_new ∪ As_new = JD' ∪ {goal_R} ∪ {goal_L}
              -- From T_L : JD_L ∪ {goal_L}. JD_L ⊆ JD' via hNonGoalL.
              have hJDL_sub : ∀ C, C ∈ Finset.union (Finset.union (jFilter S_L)
                  (ClauseSequent.ofList (defFilterList S_L))) (ClauseSequent.single goal_L) →
                  C ∈ Finset.union Gamma_new As_new := by
                intro C hC
                rw [Finset.mem_union] at hC
                rcases hC with hJD | hGL
                · have hCJD' : C ∈ Finset.union J' (ClauseSequent.ofList defs') :=
                    hNonGoalL C (by
                      rw [Finset.mem_union] at hJD
                      rcases hJD with h | h
                      · exact Or.inl h
                      · rw [ofList_defFilterList] at h; exact Or.inr h)
                  refine (Finset.mem_union_exp _ _ _).mpr (Or.inl ?_)
                  show C ∈ Finset.union (Finset.union J' _) (ClauseSequent.single goal_R)
                  exact (Finset.mem_union_exp _ _ _).mpr (Or.inl hCJD')
                · refine (Finset.mem_union_exp _ _ _).mpr (Or.inr ?_)
                  show C ∈ ClauseSequent.single goal_L
                  exact hGL
              have hDepthTL : proofDepth T_L ≤ proofDepth lT' := hd_L
              obtain ⟨leftTree_new, hdL_new⟩ := gcnf_superset_bounded _ _ hJDL_sub
                T_L (proofDepth lT') hDepthTL (by
                      repeat first
                        | exact hJDOrd
                        | exact ordinary_right T_L
                        | exact ordinary_right T_R
                        | exact ClauseSequent.ordinary_single (Clause.single_ordinary _)
                        | apply ClauseSequent.ordinary_union
                        | exact ClauseSequent.ordinary_subset hAsOrd (fun C hC => (Finset.mem_filter.mp hC).1)
                        | exact ClauseSequent.ordinary_subset hAsOrd (fun C hC => (Finset.mem_union.mp hC).elim id id)
                        | (intro C hC; apply hRootOrd C; rw [hS']; exact Finset.mem_union.mpr (Or.inr (Finset.mem_ofList.mpr (by rw [(mem_csingle _ _).mp hC]; exact List.get_mem _ _)))))
              -- rightTree_new : Gamma_new ∪ {{pos P}} = JD' ∪ {goal_R} ∪ {{pos P}}
              -- From T_R : JD_R ∪ {goal_R}. JD_R ⊆ JD' ∪ {{pos P}}.
              have hJDR_sub : ∀ C, C ∈ Finset.union (Finset.union (jFilter S_R)
                  (ClauseSequent.ofList (defFilterList S_R))) (ClauseSequent.single goal_R) →
                  C ∈ Finset.union Gamma_new
                    (ClauseSequent.single (Clause.single (Literal.pos P))) := by
                intro C hC
                rw [Finset.mem_union] at hC
                rcases hC with hJD | hGR
                · -- C is in jFilter(S_R) or defFilter(S_R) — C is in S_R and non-goal.
                  have hC_inSR : C ∈ S_R := by
                    rw [Finset.mem_union] at hJD
                    rcases hJD with h | h
                    · exact ((Finset.mem_filter_exp _ _ _).mp h).1
                    · rw [ofList_defFilterList] at h
                      exact ((Finset.mem_filter_exp _ _ _).mp h).1
                  have hCng : isGoalClauseB C = false := filter_nongoal _ C (by
                    rw [Finset.mem_union] at hJD
                    rcases hJD with h | h
                    · exact Or.inl h
                    · rw [ofList_defFilterList] at h; exact Or.inr h)
                  rw [show S_R = Finset.union G (ClauseSequent.single
                      (Clause.single (Literal.pos P))) from rfl, Finset.mem_union] at hC_inSR
                  rcases hC_inSR with hCG | hCSing
                  · -- C ∈ G non-goal → C ∈ JD'
                    have hCinS' : C ∈ Finset.union (Finset.union J' (ClauseSequent.ofList defs'))
                        (ClauseSequent.ofList goals') :=
                      hSConc ▸ (Finset.mem_union_exp _ _ _).mpr (Or.inl hCG)
                    rw [Finset.mem_union] at hCinS'
                    rcases hCinS' with hJD' | hGoal'
                    · refine (Finset.mem_union_exp _ _ _).mpr (Or.inl ?_)
                      show C ∈ Finset.union (Finset.union J' _) (ClauseSequent.single goal_R)
                      exact (Finset.mem_union_exp _ _ _).mpr (Or.inl hJD')
                    · exfalso
                      have := isGoalClauseB_complete C
                        (hGoals' _ ((Finset.mem_ofList_exp _ _).mp hGoal'))
                      rw [this] at hCng; exact absurd hCng (by decide)
                  · -- C = {{pos P}}
                    exact (Finset.mem_union_exp _ _ _).mpr (Or.inr hCSing)
                · -- C = goal_R
                  refine (Finset.mem_union_exp _ _ _).mpr (Or.inl ?_)
                  show C ∈ Finset.union (Finset.union J' _) (ClauseSequent.single goal_R)
                  exact (Finset.mem_union_exp _ _ _).mpr (Or.inr hGR)
              have hDepthTR : proofDepth T_R ≤ proofDepth rT' := hd_R
              obtain ⟨rightTree_new, hdR_new⟩ := gcnf_superset_bounded _ _ hJDR_sub
                T_R (proofDepth rT') hDepthTR (by
                      repeat first
                        | exact hJDOrd
                        | exact ordinary_right T_L
                        | exact ordinary_right T_R
                        | exact ClauseSequent.ordinary_single (Clause.single_ordinary _)
                        | apply ClauseSequent.ordinary_union
                        | exact ClauseSequent.ordinary_subset hAsOrd (fun C hC => (Finset.mem_filter.mp hC).1)
                        | exact ClauseSequent.ordinary_subset hAsOrd (fun C hC => (Finset.mem_union.mp hC).elim id id)
                        | (intro C hC; apply hRootOrd C; rw [hS']; exact Finset.mem_union.mpr (Or.inr (Finset.mem_ofList.mpr (by rw [(mem_csingle _ _).mp hC]; exact List.get_mem _ _)))))
              let ruleTree : GCNFProofTree (Finset.union Gamma_new
                  (ClauseSequent.mapSet As_new (fun A => clauseWithLiteral A (Literal.pos P)))) :=
                GCNFProofTree.rule Gamma_new As_new (Literal.pos P) As_new
                  Gamma_new Gamma_new (ordinary_left leftTree_new) (ordinary_right leftTree_new) leftTree_new rightTree_new
                  hAs_new_nonempty (fun C hC => hC)
                  (fun C hC => (Finset.mem_union_exp _ _ _).mpr (Or.inl hC))
                  (fun C hC => (Finset.mem_union_exp _ _ _).mpr (Or.inl hC))
              have hConclEq : Finset.union Gamma_new
                  (ClauseSequent.mapSet As_new (fun A => clauseWithLiteral A (Literal.pos P))) =
                  Finset.union (Finset.union J' (ClauseSequent.ofList defs'))
                    (ClauseSequent.single (goals'.get ⟨j, hj⟩)) := by
                apply Finset.ext; intro C
                constructor
                · intro hC
                  rw [Finset.mem_union] at hC
                  rcases hC with hGamma | hMap
                  · rw [show Gamma_new = Finset.union
                        (Finset.union J' (ClauseSequent.ofList defs'))
                        (ClauseSequent.single goal_R) from rfl, Finset.mem_union] at hGamma
                    rcases hGamma with hJD | hGR
                    · exact (Finset.mem_union_exp _ _ _).mpr (Or.inl hJD)
                    · rw [(Finset.mem_singleton C _).mp hGR,
                          show goals'.get ⟨j, hj⟩ = goals'[j] from rfl, hjeq]
                      exact (Finset.mem_union_exp _ _ _).mpr
                        (Or.inr ((Finset.mem_singleton _ _).mpr rfl))
                  · obtain ⟨A, hA, rfl⟩ := (mem_image_iff _ _ _).mp hMap
                    have hAeq : A = goal_L := (Finset.mem_singleton _ _).mp hA
                    subst hAeq
                    exact (Finset.mem_union_exp _ _ _).mpr (Or.inl hCwlGL_JD)
                · intro hC
                  rw [Finset.mem_union] at hC
                  rcases hC with hJD | hGR
                  · refine (Finset.mem_union_exp _ _ _).mpr (Or.inl ?_)
                    show C ∈ Finset.union (Finset.union J' _) (ClauseSequent.single goal_R)
                    exact (Finset.mem_union_exp _ _ _).mpr (Or.inl hJD)
                  · rw [(Finset.mem_singleton C _).mp hGR,
                        show goals'.get ⟨j, hj⟩ = goals'[j] from rfl, hjeq]
                    refine (Finset.mem_union_exp _ _ _).mpr (Or.inl ?_)
                    show goal_R ∈ Finset.union (Finset.union J' _) (ClauseSequent.single goal_R)
                    exact (Finset.mem_union_exp _ _ _).mpr
                      (Or.inr ((Finset.mem_singleton _ _).mpr rfl))
              refine ⟨⟨j, hj⟩, hConclEq ▸ ruleTree, ?_⟩
              rw [proofDepth_eq_transport hConclEq ruleTree]
              show 1 + max (proofDepth leftTree_new) (proofDepth rightTree_new) ≤ n
              have hn : n = 1 + max (proofDepth lT') (proofDepth rT') := by
                rw [← hDepth',
                    show proofDepth lT' = proofDepth lT from proofDepth_eq_transport hLeq lT,
                    show proofDepth rT' = proofDepth rT from proofDepth_eq_transport hReq rT]
                rfl
              omega


end LCS.SLD.SLDForm.Completeness

end
