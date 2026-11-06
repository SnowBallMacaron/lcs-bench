import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm.Occurrence
import LCS.SLD.SLDForm.Completeness.Basics
import LCS.SLD.SLDForm.Completeness.WithoutWeakenings
import Attach
import LCS.SLD.SLDForm.Completeness.AxiomLabeling.ProofsStamp

/-! # Axiom labeling and Horn provability (Lemmas 9.2.3, 9.2.4)

Section 9.2.3: the labeling of the axioms of a weakening-free proof, and the consequence that a GCNF'-provable set of Horn clauses contains a single positive literal and a goal. -/

section
namespace LCS.SLD.SLDForm.Completeness
open LCS.Resolution.GCNF
open LCS.SLD.SLDForm
open LCS.SLD.SLDForm.Occurrence

-- retained: used by LCS.SLD.SLDForm.Completeness.RootPartition
/-- By induction on the proof tree: any GCNFProofTree for a set of Horn clauses
    has a positive unit clause in its conclusion. -/
theorem gcnf_tree_has_pos_unit {S : ClauseSequent}
    (T : GCNFProofTree S)
    (hHorn : ∀ C ∈ S, isHornClause C) :
    ∃ P : Nat, Clause.single (Literal.pos P) ∈ S := by
-- BEGIN PROOF
  induction T with
  | axiom_ S hOrd hTriv => exact ⟨hTriv.choose, hTriv.choose_spec.1⟩
  | rule Gamma As B Cs Gamma1 Gamma2 hGammaOrd hAsOrd leftTree rightTree hCsNe hCsSub hG1Sub hG2Sub ihL ihR =>
    have hHornRight : ∀ C ∈ Finset.union Gamma2 (ClauseSequent.single (Clause.single B)), isHornClause C := by
      intro C hC; rw [Finset.mem_union] at hC
      rcases hC with hG2 | hSing
      · exact hHorn C (hG2Sub C hG2)
      · rw [mem_csingle] at hSing; rw [hSing]; exact isHornClause_single B
    obtain ⟨Q, hQ⟩ := ihR hHornRight
    rw [Finset.mem_union] at hQ
    rcases hQ with hQG2 | hQSing
    · exact ⟨Q, hG2Sub _ hQG2⟩
    · rw [mem_csingle] at hQSing
      have hLit : Literal.pos Q = B := single_eq_implies_lit_eq (Literal.pos Q) B hQSing
      have hHornLeft : ∀ C ∈ Finset.union Gamma1 Cs, isHornClause C := by
        intro C hC; rw [Finset.mem_union] at hC
        rcases hC with hG1 | hCs
        · exact hHorn C (hG1Sub C hG1)
        · exact isHornClause_of_subset (clauseWithLiteral C B) C
            (hHorn _ ((Finset.mem_union_exp _ _ _).mpr (Or.inr ((mem_image_iff _ _ _).mpr ⟨C, hCsSub C hCs, rfl⟩))))
            (fun l hl => (Finset.mem_insert_exp B l C).mpr (Or.inr hl))
            (hAsOrd C (hCsSub C hCs))
      obtain ⟨R, hR⟩ := ihL hHornLeft
      rw [Finset.mem_union] at hR
      rcases hR with hRG1 | hRCs
      · exact ⟨R, hG1Sub _ hRG1⟩
      · have hRAs := hCsSub _ hRCs
        have hCwl_in : clauseWithLiteral (Clause.single (Literal.pos R)) B ∈
            Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)) :=
          (Finset.mem_union_exp _ _ _).mpr (Or.inr ((mem_image_iff _ _ _).mpr
            ⟨Clause.single (Literal.pos R), hRAs, rfl⟩))
        have hH := hHorn _ hCwl_in
        have hReqQ : R = Q := by
          rw [← hLit] at hH
          exact horn_cwl_pos_unique (Clause.single (Literal.pos R)) Q R hH
            ((Finset.mem_singleton _ _).mpr rfl)
        rw [hReqQ] at hCwl_in
        have hSimp : clauseWithLiteral (Clause.single (Literal.pos Q)) B =
            Clause.single (Literal.pos Q) := by
          rw [← hLit]; exact clauseWithLiteral_single_self _
        rw [hSimp] at hCwl_in
        exact ⟨Q, hCwl_in⟩

-- ========= Helper defs for Lemma 9.2.3: clause classification =========

/-- Lemma 9.2.3 (companion): The subset of clauses in a ClauseSequent
    that contain more than one literal. -/
@[blueprint "chap9__lemma_9_2_3"]
def multiLiteralClauses (S : ClauseSequent) : ClauseSequent :=
  Finset.filter (fun C => decide (1 < C.card)) S

/-- Lemma 9.2.3 (companion): The subset of clauses in a ClauseSequent
    that consist of exactly one literal. -/
@[blueprint "chap9__lemma_9_2_3"]
def oneLiteralClauses (S : ClauseSequent) : ClauseSequent :=
  Finset.filter (fun C => decide (C.card = 1)) S

-- ========= Helper: collect axiom leaves of a proof tree =========

/-- Lemma 9.2.3 (required helper): Collects the list of axiom leaf sequents
    from a GCNFProofTree by recursion on the tree structure. -/
@[blueprint "chap9__lemma_9_2_3"]
def axiomLeaves : {S : ClauseSequent} → GCNFProofTree S → List ClauseSequent
  | _, .axiom_ S hOrd _ => [S]
  | _, .rule _ _ _ _ _ _ hGammaOrd hAsOrd leftTree rightTree _ _ _ _ =>
    axiomLeaves leftTree ++ axiomLeaves rightTree

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- Under IsStrictIWW and axiomsAllSingleLiteral, every clause in the root
    sequent is nonempty. This is because empty clauses propagate through
    Gamma (which equals Gamma1 = Gamma2 in IsStrictIWW) all the way to
    axiom leaves, contradicting axiomsAllSingleLiteral. -/
theorem root_clauses_nonempty {S : ClauseSequent} (T : GCNFProofTree S)
    (hWk : IsStrictIWW T) (hMin : T.axiomsAllSingleLiteral) :
    ∀ C ∈ S, ∃ L : Literal, L ∈ C := by
-- BEGIN PROOF
  induction T with
  | axiom_ S' hOrd hTriv =>
    intro C hC; obtain ⟨L, rfl⟩ := hMin C hC
    exact ⟨L, (Finset.mem_singleton L L).mpr rfl⟩
  | rule Gamma As B Cs Gamma1 Gamma2 hGammaOrd hAsOrd leftTree rightTree hCsNe hCsSub hG1Sub hG2Sub ihL ihR =>
    intro C hC; rw [Finset.mem_union] at hC
    rcases hC with hG | hMap
    · exact ihL hWk.2.2.2.1 hMin.1 C
        ((Finset.mem_union_exp C _ _).mpr (Or.inl (hWk.2.1 ▸ hG)))
    · obtain ⟨A, _, rfl⟩ := (mem_image_iff _ _ _).mp hMap
      exact ⟨B, (Finset.mem_insert_exp B B A).mpr (Or.inl rfl)⟩

-- ========= Lemma 9.2.3: Axiom labeling structure =========




/-- Lemma 9.2.3: Each actual leaf of a weakening-free, genuine GCNF' proof
    with literal axioms is exactly the selected singleton clauses together
    with the unit clauses J. One literal is selected from each nonunit root
    clause; the finite-set image collapses repeated selections. -/
@[blueprint "chap9__lemma_9_2_3" (main := true)]
theorem axiom_labeling_structure (S : ClauseSequent)
    (T : GCNFProofTree S)
    (hWk : IsStrictIWW T)
    (hGen : GenuineDecompositions T)
    (hMin : T.axiomsAllSingleLiteral) :
    let multiClauses := multiLiteralClauses S
    let J := oneLiteralClauses S
    ∀ (leaf : ClauseSequent), leaf ∈ axiomLeaves T →
      ∃ select : Clause → Literal,
        (∀ C ∈ multiClauses, select C ∈ C) ∧
        leaf = Finset.union
          (ClauseSequent.mapSet multiClauses (fun C => Clause.single (select C))) J 

-- ========= Lemma 9.2.4: Horn provable requires positive and goal =========

/-- Lemma 9.2.4: If a Horn clause set S is GCNF'-provable, then S contains at least one
    single positive literal clause and at least one goal (negative) clause. -/
@[blueprint "chap9__lemma_9_2_4" (main := true)]
theorem horn_provable_has_positive_and_goal (S : ClauseSequent)
    (hHorn : ∀ C ∈ S, isHornClause C)
    (hProv : GCNFProvable S) :
    (∃ P : Nat, Clause.single (Literal.pos P) ∈ S) ∧
    (∃ goal ∈ S, isGoalClause goal) 

-- ========= Helpers for Lemma 9.2.5: Horn clause model combination =========

-- Intersection of models preserves definite clause satisfaction.
-- Uses the Horn property: at most one positive literal.
-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters, LCS.SLD.SLDForm.Completeness.GoalReduction
theorem definite_clause_and (C : Clause) (hDef : isDefiniteClause C)
    (v w : Nat → Bool) (hv : Clause.satisfiedBy C v) (hw : Clause.satisfiedBy C w) :
    Clause.satisfiedBy C (fun n => v n && w n) := by
-- BEGIN PROOF
  obtain ⟨Lv, hLv, hSatLv⟩ := hv
  cases Lv with
  | neg Pv => exact ⟨_, hLv, by simp [Literal.satisfiedBy] at hSatLv ⊢; rw [hSatLv]; simp⟩
  | pos Pv =>
    obtain ⟨Lw, hLw, hSatLw⟩ := hw
    cases Lw with
    | neg Pw => exact ⟨_, hLw, by simp [Literal.satisfiedBy] at hSatLw ⊢; rw [hSatLw]; simp⟩
    | pos Pw =>
      rw [hDef.1.2 Pv Pw hLv hLw] at hSatLv
      exact ⟨_, hLw, by simp [Literal.satisfiedBy] at *; rw [hSatLv, hSatLw]; simp⟩

-- Goal clause satisfaction is antimonotone under valuation intersection:
-- if v satisfies goal N, then (v AND w) also satisfies N.
-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters, LCS.SLD.SLDForm.Completeness.GoalReduction
theorem goal_and_sat (N : Clause) (hGoal : isGoalClause N)
    (v w : Nat → Bool) (hv : Clause.satisfiedBy N v) :
    Clause.satisfiedBy N (fun n => v n && w n) := by
-- BEGIN PROOF
  obtain ⟨L, hL, hSat⟩ := hv
  cases L with
  | pos _ => exact absurd (hGoal.2 _ hL) (by simp)
  | neg P => exact ⟨_, hL, by simp [Literal.satisfiedBy] at hSat ⊢; rw [hSat]; simp⟩

-- Symmetric version: (w AND v) also satisfies N.
-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters, LCS.SLD.SLDForm.Completeness.GoalReduction
theorem goal_and_sat_right (N : Clause) (hGoal : isGoalClause N)
    (v w : Nat → Bool) (hv : Clause.satisfiedBy N v) :
    Clause.satisfiedBy N (fun n => w n && v n) := by
-- BEGIN PROOF
  obtain ⟨L, hL, hSat⟩ := hv
  cases L with
  | pos _ => exact absurd (hGoal.2 _ hL) (by simp)
  | neg P => exact ⟨_, hL, by simp [Literal.satisfiedBy] at hSat ⊢; rw [hSat]; simp⟩

-- Valuation intersection preserves satisfaction of JD = J ∪ defs
-- (positive singletons and definite clauses).
-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters, LCS.SLD.SLDForm.Completeness.GoalReduction
theorem jd_and_sat (JD : ClauseSequent)
    (hJD : ∀ C ∈ JD, (∃ P : Nat, C = Clause.single (Literal.pos P)) ∨ isDefiniteClause C)
    (v w : Nat → Bool) (hv : ClauseSequent.satisfiedBy JD v) (hw : ClauseSequent.satisfiedBy JD w) :
    ClauseSequent.satisfiedBy JD (fun n => v n && w n) := by
-- BEGIN PROOF
  intro C hC
  rcases hJD C hC with ⟨P, rfl⟩ | hDef
  · have hvC := hv _ hC; have hwC := hw _ hC
    obtain ⟨L, hL, hSat⟩ := hvC; have := (Finset.mem_singleton L _).mp hL; subst this
    obtain ⟨L', hL', hSat'⟩ := hwC; have := (Finset.mem_singleton L' _).mp hL'; subst this
    exact ⟨_, (Finset.mem_singleton _ _).mpr rfl,
      by simp [Literal.satisfiedBy] at *; rw [hSat, hSat']; simp⟩
  · exact definite_clause_and C hDef v w (hv C hC) (hw C hC)

-- If each single-goal subset is satisfiable, then JD ∪ (all goals) is satisfiable.
-- Proved by iterated model combination (binary AND of valuations).
-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters, LCS.SLD.SLDForm.Completeness.GoalReduction
theorem horn_all_goals_sat_of_each_sat
    (JD : ClauseSequent) (goals : List Clause)
    (hJD : ∀ C ∈ JD, (∃ P : Nat, C = Clause.single (Literal.pos P)) ∨ isDefiniteClause C)
    (hGoals : ∀ C ∈ goals, isGoalClause C)
    (hGoalsNe : goals ≠ [])
    (hEach : ∀ i : Fin goals.length, ∃ v : Nat → Bool,
      ClauseSequent.satisfiedBy JD v ∧ Clause.satisfiedBy (goals.get i) v) :
    ∃ v : Nat → Bool, ClauseSequent.satisfiedBy JD v ∧ ∀ g ∈ goals, Clause.satisfiedBy g v := by
-- BEGIN PROOF
  induction goals with
  | nil => exact absurd rfl hGoalsNe
  | cons g gs ih =>
    have hv0 := hEach ⟨0, by simp⟩; simp at hv0
    obtain ⟨v0, hv0JD, hv0g⟩ := hv0
    by_cases hgs : gs = []
    · subst hgs
      refine ⟨v0, hv0JD, fun g' hg' => ?_⟩
      rw [List.mem_cons] at hg'; rcases hg' with rfl | h
      · exact hv0g
      · exact absurd h List.not_mem_nil
    · have hGoalsGS : ∀ C ∈ gs, isGoalClause C :=
        fun C hC => hGoals C (List.mem_cons.mpr (Or.inr hC))
      have hSatGS : ∀ i : Fin gs.length, ∃ v,
          ClauseSequent.satisfiedBy JD v ∧ Clause.satisfiedBy (gs.get i) v := by
        intro ⟨i, hi⟩
        have h := hEach ⟨i + 1, by simp; exact hi⟩
        simpa using h
      obtain ⟨vc, hvcJD, hvcgs⟩ := ih hGoalsGS hgs hSatGS
      refine ⟨fun n => vc n && v0 n, jd_and_sat JD hJD vc v0 hvcJD hv0JD, fun g' hg' => ?_⟩
      rw [List.mem_cons] at hg'
      rcases hg' with rfl | hgs'
      · exact goal_and_sat_right g' (hGoals g' (List.mem_cons.mpr (Or.inl rfl))) v0 vc hv0g
      · exact goal_and_sat g' (hGoalsGS g' hgs') vc v0 (hvcgs g' hgs')

end LCS.SLD.SLDForm.Completeness
end
