import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm.Occurrence
import LCS.SLD.SLDForm.Completeness.Basics
import LCS.SLD.SLDForm.Completeness.WithoutWeakenings
import LCS.SLD.SLDForm.Completeness.PermutationLemma
import LCS.SLD.SLDForm.Completeness.AxiomLabeling
import LCS.SLD.SLDForm.Completeness.GoalReduction
import Attach
import LCS.SLD.SLDForm.Completeness.Theorems.ProofsStamp

/-! # Completeness of proofs in SLD-form (Theorems 9.2.1, 9.2.2)

Section 9.2.3: every GCNF'-provable set of definite clauses with one goal has a GCNF'-proof in SLD-form (by induction on the total number of literals), and the extension to several goals. -/

section
namespace LCS.SLD.SLDForm.Completeness
open LCS.Resolution.GCNF
open LCS.SLD.SLDForm
open LCS.SLD.SLDForm.Occurrence

-- ========= totalLits measure (Phase A4-sub1 infrastructure) =========
--
-- For the main step of Thm 9.2.1 we need a strictly decreasing measure
-- on `ClauseSequent`s whose decrease is justified by replacing one clause
-- with a strictly smaller one. `totalLits S` is the sum over `S` of each
-- clause's literal count. Because `ClauseSequent = LCS.Finset Clause` is a
-- quotient of lists under permutation, we first lift `List.sum ∘ List.map`
-- through `List.Perm`.

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalReduction
/-- Permutation preserves `List.sum` on `Nat` lists. Used to lift summation
    through the quotient `LCS.Multiset = Quotient List.isSetoid`. -/
theorem listPerm_sum_eq {l1 l2 : List Nat} (h : l1.Perm l2) :
    l1.sum = l2.sum := by
-- BEGIN PROOF
  induction h with
  | nil => rfl
  | cons x _ ih => simp [List.sum_cons, ih]
  | swap => simp [List.sum_cons]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalReduction
/-- Generic `Nat`-valued sum over an `LCS.Finset`, parameterised by a weight
    function `f`. Defined by quotient lift of `List.map f |>.sum`. -/
def finsetSum {α : Type} (s : LCS.Finset α) (f : α → Nat) : Nat :=
  Quot.liftOn s.val (fun l => (l.map f).sum)
    (fun _ _ hp => listPerm_sum_eq (hp.map f))

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalReduction
/-- Total literal count of a `ClauseSequent`: sum over `S` of each clause's
    `card`. This is the termination measure for the inductive construction
    in Thm 9.2.1 (replace an oversized clause by a strictly smaller one). -/
def totalLits (S : ClauseSequent) : Nat := finsetSum S (fun C => C.card)

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalReduction
/-- Delta lemma: inserting a fresh clause adds its cardinality to `totalLits`. -/
theorem totalLits_insert (S : ClauseSequent) (C : Clause) (hC : C ∉ S) :
    totalLits (Finset.insert C S) = totalLits S + C.card := by
-- BEGIN PROOF
  cases S with | mk v nd =>
  revert nd hC
  induction v using LCS.Multiset.ind with
  | _ l =>
    intro nd hC
    have hCl : C ∉ l := hC
    show ((if C ∈ l then l else C :: l).map (fun D => D.card)).sum
        = (l.map (fun D => D.card)).sum + C.card
    simp [hCl, List.sum_cons]; omega

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalReduction
/-- Delta lemma: erasing a present clause decreases `totalLits` by its
    cardinality. Stated in additive form to avoid `Nat` truncated subtraction. -/
theorem totalLits_erase_add (S : ClauseSequent) (C : Clause) (hC : C ∈ S) :
    totalLits (S.erase C) + C.card = totalLits S := by
-- BEGIN PROOF
  cases S with | mk v nd =>
  revert nd hC
  induction v using LCS.Multiset.ind with
  | _ l =>
    intro nd hC
    have hCl : C ∈ l := hC
    show ((l.erase C).map (fun D => D.card)).sum + C.card
        = (l.map (fun D => D.card)).sum
    have hp : l.Perm (C :: l.erase C) := List.perm_cons_erase hCl
    have hmp : (l.map (fun D => D.card)).Perm ((C :: l.erase C).map (fun D => D.card)) :=
      hp.map (fun D => D.card)
    have hsum := listPerm_sum_eq hmp
    simp [List.sum_cons] at hsum
    omega

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalReduction
/-- Main delta lemma: replacing a clause `C ∈ S` by a strictly smaller clause
    `C'` (absent from `S.erase C`) strictly decreases `totalLits`. This is the
    termination argument for the Thm 9.2.1 main step. -/
theorem totalLits_replace_with_smaller
    (S : ClauseSequent) (C C' : Clause)
    (hC : C ∈ S) (hC' : C' ∉ S.erase C) (hLt : C'.card < C.card) :
    totalLits (Finset.insert C' (S.erase C)) < totalLits S := by
-- BEGIN PROOF
  have h1 := totalLits_insert (S.erase C) C' hC'
  have h2 := totalLits_erase_add S C hC
  rw [h1]; omega

-- ========= Helpers for the outer goal-split right-subtree witness =========

























-- ========= Theorem 9.2.1: Completeness of proofs in SLD-form =========

/-- Theorem 9.2.1: (Completeness of proofs in SLD-form) If a set S of definite
    clauses with a single goal B = {neg P_1, ..., neg P_n} (with n ≥ 1) is
    GCNF'-provable, it has a GCNF'-proof in SLD-form. The hypothesis
    `hBne : B ≠ Clause.empty` encodes the textbook's implicit assumption that
    the goal is a nonempty set of negative literals (the n ≥ 1 side condition
    in Def 9.2.1's goal-clause shape {neg P_1, ..., neg P_n}). -/
@[blueprint "chap9__theorem_9_2_1" (main := true)]
theorem sld_form_completeness (S : ClauseSequent)
    (hDef : ∀ C ∈ S, isDefiniteClause C ∨ isGoalClause C)
    (B : Clause)
    (hB : B ∈ S)
    (hGoalB : isGoalClause B)
    (hBne : B ≠ Clause.empty)
    (hUnique : ∀ C ∈ S, isGoalClause C → C = B)
    (hProv : GCNFProvable S) :
    ∃ T : GCNFProofTree S, isSLDForm T 

-- ========= Theorem 9.2.2: SLD-form completeness for multiple goals =========

/-- Theorem 9.2.2: If a set S of Horn clauses (with J, goals N_1,...,N_k, definite
    C_1,...,C_m) is GCNF'-provable, some single-goal subset has a GCNF'-proof in
    SLD-form. Each goal N_j is required to be nonempty (textbook's implicit n ≥ 1
    in Def 9.2.1's goal-clause shape), propagated to Thm 9.2.1. -/
@[blueprint "chap9__theorem_9_2_2" (main := true)]
theorem sld_form_completeness_multiple_goals
    (J : ClauseSequent)
    (goals : List Clause)
    (defs : List Clause)
    (hJ : ∀ C ∈ J, ∃ P : Nat, C = Clause.single (Literal.pos P))
    (hGoals : ∀ C ∈ goals, isGoalClause C)
    (hGoalsNonempty : ∀ C ∈ goals, C ≠ Clause.empty)
    (hGoalsNe : goals ≠ [])
    (hDefs : ∀ C ∈ defs, isDefiniteClause C ∧ (∃ l₁ l₂, l₁ ∈ C ∧ l₂ ∈ C ∧ l₁ ≠ l₂))
    (S : ClauseSequent)
    (hS : S = Finset.union (Finset.union J (ClauseSequent.ofList defs)) (ClauseSequent.ofList goals))
    (hProv : GCNFProvable S) :
    ∃ (i : Fin goals.length),
      ∃ T : GCNFProofTree (Finset.union (Finset.union J (ClauseSequent.ofList defs)) (ClauseSequent.single (goals.get i))),
        isSLDForm T 

end LCS.SLD.SLDForm.Completeness
end
