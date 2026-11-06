import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm.Occurrence

/-! # Shared clause-set facts for Section 9.2.3

Ordinary-clause, Horn-clause, singleton and finite-set facts used by several of the lemmas of Section 9.2.3. -/

section
namespace LCS.SLD.SLDForm.Completeness
open LCS.Resolution.GCNF
open LCS.SLD.SLDForm
open LCS.SLD.SLDForm.Occurrence

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters, LCS.SLD.SLDForm.Completeness.RootPartition
/-- Literal-only sequents satisfy the GCNF' clause grammar. -/
theorem ordinary_of_singletons {S : ClauseSequent}
    (h : ∀ C ∈ S, ∃ L : Literal, C = Clause.single L) : S.isOrdinary := by
  intro C hC
  obtain ⟨L, rfl⟩ := h C hC
  exact Clause.single_ordinary L

/-- A premise certifies ordinariness of each half of its context. -/
theorem ordinary_left {G A : ClauseSequent} (T : GCNFProofTree (Finset.union G A)) :
    G.isOrdinary :=
  ClauseSequent.ordinary_subset T.ordinary (fun _ h => Finset.mem_union.mpr (Or.inl h))

theorem ordinary_right {G A : ClauseSequent} (T : GCNFProofTree (Finset.union G A)) :
    A.isOrdinary :=
  ClauseSequent.ordinary_subset T.ordinary (fun _ h => Finset.mem_union.mpr (Or.inr h))

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters, LCS.SLD.SLDForm.Completeness.GoalReduction
/-- A positive literal witnesses nonemptiness of a definite clause. -/
theorem ordinary_of_definite {C : Clause} (h : isDefiniteClause C) : C.isOrdinary := by
  obtain ⟨P, hP⟩ := h.2
  exact Clause.ordinary_of_mem hP

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalReduction
theorem ordinary_insert {D : Clause} {S : ClauseSequent}
    (hD : D.isOrdinary) (hS : S.isOrdinary) : ClauseSequent.isOrdinary (Finset.insert D S) := by
  intro C hC
  rcases Finset.mem_insert.mp hC with rfl | hC
  · exact hD
  · exact hS C hC

-- ========= Helper lemmas for Horn clause reasoning =========

-- retained: used by LCS.SLD.Propositional.Part1, LCS.SLD.SLDForm.Completeness.GoalReduction
/-- An ordinary subset of an ordinary Horn clause is Horn. -/
theorem isHornClause_of_subset (C D : Clause) (hHorn : isHornClause C)
    (hSub : ∀ l ∈ D, l ∈ C) (hD : D.isOrdinary) : isHornClause D :=
  ⟨hD, fun P Q hP hQ => hHorn.2 P Q (hSub _ hP) (hSub _ hQ)⟩

-- retained: used by LCS.SLD.SLDForm.Completeness.RootPartition
/-- If cwl A (pos Q) is Horn and pos R ∈ A, then R = Q. -/
theorem horn_cwl_pos_unique (A : Clause) (Q R : Nat)
    (hHorn : isHornClause (clauseWithLiteral A (Literal.pos Q)))
    (hR : Literal.pos R ∈ A) : R = Q :=
-- BEGIN PROOF
  hHorn.2 R Q
    ((Finset.mem_insert_exp (Literal.pos Q) (Literal.pos R) A).mpr (Or.inr hR))
    ((Finset.mem_insert_exp (Literal.pos Q) (Literal.pos Q) A).mpr (Or.inl rfl))

/-- Singleton clause equality implies literal equality. -/
theorem single_eq_implies_lit_eq (L B : Literal) (h : Clause.single L = Clause.single B) : L = B := by
-- BEGIN PROOF
  have hL : L ∈ Clause.single B := h ▸ (Finset.mem_singleton L L).mpr rfl
  exact (Finset.mem_singleton L B).mp hL

-- retained: used by LCS.SLD.Propositional.Part1, LCS.SLD.SLDForm.Completeness.GoalFilters, LCS.SLD.SLDForm.Completeness.GoalReduction
/-- Singleton clause is Horn. -/
theorem isHornClause_single (L : Literal) : isHornClause (Clause.single L) := by
-- BEGIN PROOF
  refine ⟨Clause.single_ordinary _, ?_⟩
  intro P Q hP hQ
  have hP' := (Finset.mem_singleton (Literal.pos P) L).mp hP
  have hQ' := (Finset.mem_singleton (Literal.pos Q) L).mp hQ
  cases L with
  | pos n => injection hP' with hp; injection hQ' with hq; rw [hp, hq]
  | neg n => exact absurd hP' (by intro h; exact Literal.noConfusion h)

-- ========= Admissible weakening for GCNF' =========

-- retained: used by LCS.SLD.SLDForm.Completeness.RootPartition
/-- Finset union right-commutativity: (a ∪ b) ∪ c = (a ∪ c) ∪ b. -/
theorem finset_union_right_comm (a b c : ClauseSequent) :
    Finset.union (Finset.union a b) c = Finset.union (Finset.union a c) b := by
-- BEGIN PROOF
  apply Finset.ext; intro x; simp [Finset.mem_union]
  constructor
  · intro h; rcases h with (ha | hb) | hc
    all_goals first | exact Or.inl (Or.inl ‹_›) | exact Or.inl (Or.inr ‹_›) | exact Or.inr ‹_›
  · intro h; rcases h with (ha | hc) | hb
    all_goals first | exact Or.inl (Or.inl ‹_›) | exact Or.inl (Or.inr ‹_›) | exact Or.inr ‹_›

-- retained: used by LCS.SLD.SLDForm.Completeness.RootPartition
/-- If Gamma1 ⊆ Gamma ∪ M, then Gamma1 ∪ D ⊆ (Gamma ∪ D) ∪ M. -/
theorem subset_weaken_union (Gamma1 Gamma D M : ClauseSequent)
    (h : Finset.Subset Gamma1 (Finset.union Gamma M)) :
    Finset.Subset (Finset.union Gamma1 D) (Finset.union (Finset.union Gamma D) M) := by
-- BEGIN PROOF
  intro x hx; rw [Finset.mem_union] at hx ⊢
  rcases hx with hG1 | hD
  · rcases (Finset.mem_union_exp x Gamma M).mp (h x hG1) with hG | hM
    · exact Or.inl ((Finset.mem_union_exp x Gamma D).mpr (Or.inl hG))
    · exact Or.inr hM
  · exact Or.inl ((Finset.mem_union_exp x Gamma D).mpr (Or.inr hD))

-- ========= Helper lemmas for empty clause removal =========

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalReduction
/-- Singleton clause is nonempty. -/
theorem single_ne_empty (L : Literal) : Clause.single L ≠ Clause.empty := by
-- BEGIN PROOF
  intro h; have h1 : L ∈ Clause.single L := (Finset.mem_singleton L L).mpr rfl
  rw [h] at h1; exact (Finset.mem_empty L).mp h1

-- retained: used by LCS.SLD.SLDForm.Completeness.GoalFilters
/-- Removing empty clause from a proof tree: if T proves S, then S.erase ∅ is provable. -/
theorem gcnf_provable_erase_empty {S : ClauseSequent} (T : GCNFProofTree S) :
    GCNFProvable (Finset.erase S Clause.empty) := by
-- BEGIN PROOF
  have hEq : Finset.erase S Clause.empty = S := by
    apply Finset.ext
    intro C
    simp only [Finset.mem_erase]
    exact ⟨And.left, fun hC => ⟨hC, T.ordinary C hC⟩⟩
  rw [hEq]
  exact ⟨T⟩

-- ========= Helper lemmas for Lemma 9.2.3 =========

/-- If a Finset of literals has card 1, then any two elements are equal. -/
theorem finset_card_one_eq {S : Finset Literal} (hCard : S.card = 1) (a b : Literal)
    (ha : a ∈ S) (hb : b ∈ S) : a = b := by
-- BEGIN PROOF
  cases S with | mk v nd =>
  revert nd hCard ha hb
  induction v using Multiset.ind with
  | _ l =>
    intro hnd hCard ha hb
    have hLen : l.length = 1 := by
      show l.length = 1; exact hCard
    have ha' : a ∈ l := ha; have hb' : b ∈ l := hb
    cases hv : l with
    | nil => rw [hv] at hLen; simp at hLen
    | cons x xs =>
      rw [hv] at hLen ha' hb'
      have hxs : xs = [] := by cases xs with | nil => rfl | cons _ _ => simp at hLen
      rw [hxs] at ha' hb'
      exact (by rw [List.mem_cons] at ha'; rcases ha' with rfl | h; rfl
                exact absurd h List.not_mem_nil : a = x).trans
            (by rw [List.mem_cons] at hb'; rcases hb' with rfl | h; rfl
                exact absurd h List.not_mem_nil : x = b)

/-- A finite set containing an element has positive cardinality. -/
theorem finset_card_pos_of_mem {α : Type} {S : Finset α} {a : α}
    (ha : a ∈ S) : 0 < S.card := by
  cases S with | mk v nd =>
  revert nd ha
  induction v using Multiset.ind with
  | _ l =>
    intro hnd ha
    change 0 < l.length
    have ha' : a ∈ l := ha
    cases l with
    | nil => exact absurd ha' List.not_mem_nil
    | cons _ _ => simp

end LCS.SLD.SLDForm.Completeness
end
