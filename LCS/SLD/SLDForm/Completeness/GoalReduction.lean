import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm.Occurrence
import LCS.SLD.SLDForm.Completeness.Basics
import LCS.SLD.SLDForm.Completeness.WithoutWeakenings
import LCS.SLD.SLDForm.Completeness.PermutationLemma
import LCS.SLD.SLDForm.Completeness.AxiomLabeling
import Attach
import LCS.SLD.SLDForm.Completeness.GoalReduction.ProofsStamp

/-! # Reduction to a single goal (Lemma 9.2.5)

Section 9.2.3: a GCNF'-provable set of Horn clauses with several goals remains provable with only one of its goals. -/

section
namespace LCS.SLD.SLDForm.Completeness
open LCS.Resolution.GCNF
open LCS.SLD.SLDForm
open LCS.SLD.SLDForm.Occurrence

-- retained: used by LCS.SLD.Propositional.Part1, LCS.SLD.SLDForm.Completeness.GoalFilters, LCS.SLD.SLDForm.Completeness.GoalReduction
/-- Singleton negative clause is a goal clause. -/
theorem singleton_neg_is_goal (P : Nat) : isGoalClause (Clause.single (Literal.neg P)) := by
  constructor
  · refine ⟨Clause.single_ordinary _, ?_⟩
    intro Q R hQ hR
    exact absurd ((Finset.mem_singleton _ _).mp hQ) Literal.noConfusion
  · intro l hl
    have := (Finset.mem_singleton _ _).mp hl; subst this; trivial

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- Bool-valued test: is C ordinary and all-negative? -/
def isGoalClauseB (C : Clause) : Bool :=
  decide (C ≠ Clause.empty) && allNegativeB C

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- isGoalClauseB is sound for isGoalClause. -/
theorem isGoalClauseB_sound (C : Clause) (h : isGoalClauseB C = true) : isGoalClause C := by
  simp only [isGoalClauseB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hOrd, hNeg⟩ := h
  have hn := allNegativeB_spec C hNeg
  exact ⟨⟨hOrd, fun P Q hP _ => False.elim (hn _ hP)⟩, hn⟩

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- The ordinary goal test accepts every goal clause. -/
theorem isGoalClauseB_complete (C : Clause) (h : isGoalClause C) : isGoalClauseB C = true := by
  simp only [isGoalClauseB, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h.1.1, allNegativeB_of_goal h⟩

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- The subset of S that consists of goal clauses (Bool filter). -/
def goalFilter (S : ClauseSequent) : ClauseSequent :=
  Finset.filter isGoalClauseB S

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- The subset of S that consists of non-goal clauses with card > 1. -/
def defFilter (S : ClauseSequent) : ClauseSequent :=
  Finset.filter (fun C => !isGoalClauseB C && decide (1 < C.card)) S

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- The subset of S that consists of non-goal clauses with card ≤ 1. -/
def jFilter (S : ClauseSequent) : ClauseSequent :=
  Finset.filter (fun C => !isGoalClauseB C && !decide (1 < C.card)) S

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- Every clause in S belongs to exactly one of goalFilter, defFilter, jFilter. -/
theorem filter_trichotomy (S : ClauseSequent) (C : Clause) (hC : C ∈ S) :
    C ∈ goalFilter S ∨ C ∈ defFilter S ∨ C ∈ jFilter S := by
-- BEGIN PROOF
  by_cases hG : isGoalClauseB C = true
  · exact Or.inl ((Finset.mem_filter_exp _ _ _).mpr ⟨hC, hG⟩)
  · by_cases hD : decide (1 < C.card) = true
    · exact Or.inr (Or.inl ((Finset.mem_filter_exp _ _ _).mpr ⟨hC, by simp [hG, hD]⟩))
    · exact Or.inr (Or.inr ((Finset.mem_filter_exp _ _ _).mpr ⟨hC, by simp [hG, hD]⟩))

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- The three filters cover S. -/
theorem filter_covers (S : ClauseSequent) :
    S = Finset.union (Finset.union (jFilter S) (defFilter S)) (goalFilter S) := by
-- BEGIN PROOF
  apply Finset.ext; intro C
  rw [Finset.mem_union, Finset.mem_union]
  constructor
  · intro hC
    rcases filter_trichotomy S C hC with hG | hD | hJ
    · exact Or.inr hG
    · exact Or.inl (Or.inr hD)
    · exact Or.inl (Or.inl hJ)
  · intro hC
    rcases hC with (hJ | hD) | hG
    · exact ((Finset.mem_filter_exp _ _ _).mp hJ).1
    · exact ((Finset.mem_filter_exp _ _ _).mp hD).1
    · exact ((Finset.mem_filter_exp _ _ _).mp hG).1

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- Helper: if a Finset has card 1, all elements are equal to any given member. -/
theorem card_one_all_eq (C : Clause) (hCard : C.card = 1) (a b : Literal)
    (ha : a ∈ C) (hb : b ∈ C) : a = b :=
-- BEGIN PROOF
  finset_card_one_eq hCard a b ha hb

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- Clauses in jFilter are unit positive literals (for nonempty Horn clauses). -/
theorem jFilter_unit_pos (S : ClauseSequent)
    (hHorn : ∀ C ∈ S, isHornClause C) (hNe : ∀ C ∈ S, ∃ L : Literal, L ∈ C) :
    ∀ C ∈ jFilter S, ∃ P : Nat, C = Clause.single (Literal.pos P) := by
-- BEGIN PROOF
  intro C hC
  have ⟨hCS, hPred⟩ := (Finset.mem_filter_exp _ _ _).mp hC
  have hNotGoal : isGoalClauseB C = false := by
    cases hv : isGoalClauseB C
    · rfl
    · simp [hv] at hPred
  have hSmall : ¬(1 < C.card) := by
    cases hv : decide (1 < C.card) with
    | true => simp [hNotGoal, hv] at hPred
    | false => exact of_decide_eq_false hv
  obtain ⟨L, hL⟩ := hNe C hCS
  have hCard1 : C.card = 1 := by
    have hPos : 1 ≤ C.card := by
      show 1 ≤ C.val.card
      cases C with | mk v nd =>
      induction v using Multiset.ind with
      | _ lst =>
        have hL' : L ∈ lst := hL
        show 1 ≤ lst.length
        cases hv : lst with
        | nil => rw [hv] at hL'; exact absurd hL' List.not_mem_nil
        | cons _ _ => simp [List.length]
    omega
  match L with
  | .neg P =>
    exfalso
    have hGoalB : isGoalClauseB C = true := by
      rw [isGoalClauseB, Bool.and_eq_true]
      refine ⟨decide_eq_true (hHorn C hCS).1, ?_⟩
      apply Multiset.all_eq_true.mpr; intro l hl
      have := card_one_all_eq C hCard1 l (Literal.neg P) hl hL
      subst this; rfl
    rw [hGoalB] at hNotGoal; exact absurd hNotGoal (by decide)
  | .pos P =>
    refine ⟨P, ?_⟩
    apply Finset.ext; intro l; constructor
    · intro hl
      exact (Finset.mem_singleton _ _).mpr (card_one_all_eq C hCard1 l (Literal.pos P) hl hL)
    · intro hl; rw [(Finset.mem_singleton _ _).mp hl]; exact hL

-- ========= Helpers for goal_reduction rule case =========









-- ========= Lemma 9.2.5: Goal reduction =========

/-- Lemma 9.2.5: If a Horn set S (J, goals N_1,...,N_k, definite C_1,...,C_m) is
    GCNF'-provable, then some J ∪ {C_1,...,C_m} ∪ {N_i} is GCNF'-provable. -/
@[blueprint "chap9__lemma_9_2_5" (main := true)]
theorem goal_reduction
    (J : ClauseSequent)
    (goals : List Clause)
    (defs : List Clause)
    (hJ : ∀ C ∈ J, ∃ P : Nat, C = Clause.single (Literal.pos P))
    (hGoals : ∀ C ∈ goals, isGoalClause C)
    (hGoalsNe : goals ≠ [])
    (hDefs : ∀ C ∈ defs, isDefiniteClause C ∧ (∃ l₁ l₂, l₁ ∈ C ∧ l₂ ∈ C ∧ l₁ ≠ l₂))
    (S : ClauseSequent)
    (hS : S = Finset.union (Finset.union J (ClauseSequent.ofList defs)) (ClauseSequent.ofList goals))
    (hProv : GCNFProvable S) :
    -- Part (a): some single-goal subset is provable
    (∃ (i : Fin goals.length),
      GCNFProvable (Finset.union (Finset.union J (ClauseSequent.ofList defs))
        (ClauseSequent.single (goals.get i)))) ∧
    -- Part (b): for any specific proof, some single-goal subset has bounded depth
    (∀ T : GCNFProofTree S,
      IsStrictIWW T → T.axiomsAllSingleLiteral →
      ∃ (i : Fin goals.length),
        ∃ T' : GCNFProofTree (Finset.union (Finset.union J (ClauseSequent.ofList defs))
          (ClauseSequent.single (goals.get i))),
          proofDepth T' ≤ proofDepth T) 

end LCS.SLD.SLDForm.Completeness
end
