import LCS.Item
import LCS.Util
import LCS.CutElim.CompletenessBridge
import LCS.CutElim.DecEqOfSymbols
import LCS.CutElim.LK.Syntax

section
namespace LCS.CutElim.LK
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.CutElim.CompletenessBridge

-- ===================================================================
-- Helper lemmas for folkCutFreeProvable
-- ===================================================================
-- retained: used by LCS.CutElim.LK.Part2
theorem folkCutFree_weakenLeft {L : Language}
    (B : FormulaN L) (Γ Δ : List (FormulaN L))
    (h : folkCutFreeProvable (Sequent.mk Γ Δ)) :
    folkCutFreeProvable (Sequent.mk (B :: Γ) Δ) := by
-- BEGIN PROOF
  obtain ⟨t, hcf⟩ := h
  exact ⟨.onePremise (.weakenLeft B Γ Δ) t, hcf⟩

-- retained: used by LCS.CutElim.LK.Part2
theorem folkCutFree_weakenRight {L : Language}
    (B : FormulaN L) (Γ Δ : List (FormulaN L))
    (h : folkCutFreeProvable (Sequent.mk Γ Δ)) :
    folkCutFreeProvable (Sequent.mk Γ (Δ ++ [B])) := by
-- BEGIN PROOF
  obtain ⟨t, hcf⟩ := h
  exact ⟨.onePremise (.weakenRight B Γ Δ) t, hcf⟩

-- retained: used by LCS.CutElim.Interpolation.Equality.Axioms, LCS.CutElim.Interpolation.Equality.Replay, LCS.CutElim.LK.Part2, LCS.CutElim.LKe.Equivalence.Validity
theorem folkCutFree_axiom {L : Language} (A : FormulaN L) :
    folkCutFreeProvable (Sequent.mk [A] [A]) :=
-- BEGIN PROOF
  ⟨.axiom_ (Sequent.mk [A] [A]) ⟨A, rfl, rfl⟩, trivial⟩

-- retained: used by LCS.CutElim.LK.Part2
theorem folkCutFree_weakenLeftList {L : Language}
    (Γ' Γ Δ : List (FormulaN L))
    (h : folkCutFreeProvable (Sequent.mk Γ Δ)) :
    folkCutFreeProvable (Sequent.mk (Γ' ++ Γ) Δ) := by
-- BEGIN PROOF
  induction Γ' with
  | nil => simp; exact h
  | cons B rest ih =>
    exact folkCutFree_weakenLeft B (rest ++ Γ) Δ ih

-- retained: used by LCS.CutElim.LK.Part2
theorem folkCutFree_weakenRightList {L : Language}
    (Δ' Γ Δ : List (FormulaN L))
    (h : folkCutFreeProvable (Sequent.mk Γ Δ)) :
    folkCutFreeProvable (Sequent.mk Γ (Δ ++ Δ')) := by
-- BEGIN PROOF
  induction Δ' generalizing Δ with
  | nil => simp; exact h
  | cons B rest ih =>
    have h1 : folkCutFreeProvable (Sequent.mk Γ (Δ ++ [B])) :=
      folkCutFree_weakenRight B Γ Δ h
    have h2 := ih (Δ ++ [B]) h1
    rwa [List.append_assoc] at h2

-- retained: used by LCS.CutElim.LK.Part2
theorem folkCutFree_exchangeLeft_adj {L : Language}
    (Γ : List (FormulaN L)) (A B : FormulaN L)
    (Δ Λ : List (FormulaN L))
    (h : folkCutFreeProvable (Sequent.mk (Γ ++ [A, B] ++ Δ) Λ)) :
    folkCutFreeProvable (Sequent.mk (Γ ++ [B, A] ++ Δ) Λ) := by
-- BEGIN PROOF
  obtain ⟨t, hcf⟩ := h
  exact ⟨.onePremise (.exchangeLeft Γ A B Δ Λ) t, hcf⟩

-- retained: used by LCS.CutElim.LK.Part2
theorem folkCutFree_exchangeRight_adj {L : Language}
    (Γ Δ : List (FormulaN L)) (A B : FormulaN L)
    (Λ : List (FormulaN L))
    (h : folkCutFreeProvable (Sequent.mk Γ (Δ ++ [A, B] ++ Λ))) :
    folkCutFreeProvable (Sequent.mk Γ (Δ ++ [B, A] ++ Λ)) := by
-- BEGIN PROOF
  obtain ⟨t, hcf⟩ := h
  exact ⟨.onePremise (.exchangeRight Γ Δ A B Λ) t, hcf⟩

-- Equality transport for folkCutFreeProvable
-- retained: used by LCS.CutElim.LK.Part2
theorem folkCutFree_of_eq {L : Language} {s1 s2 : Sequent L}
    (heq : s1 = s2) (h : folkCutFreeProvable s1) :
    folkCutFreeProvable s2 := heq ▸ h

-- Sink an element from front past a segment
theorem folkCutFree_sinkLeftPast {L : Language}
    (pre mid post : List (FormulaN L)) (Λ : List (FormulaN L))
    (A : FormulaN L)
    (h : folkCutFreeProvable (Sequent.mk (pre ++ [A] ++ mid ++ post) Λ)) :
    folkCutFreeProvable (Sequent.mk (pre ++ mid ++ [A] ++ post) Λ) := by
-- BEGIN PROOF
  induction mid generalizing pre with
  | nil => simp at h ⊢; exact h
  | cons B rest ih =>
    have h1 : folkCutFreeProvable
        (Sequent.mk (pre ++ [A, B] ++ (rest ++ post)) Λ) :=
      folkCutFree_of_eq (by simp) h
    have h2 := folkCutFree_exchangeLeft_adj pre A B (rest ++ post) Λ h1
    have h3 : folkCutFreeProvable
        (Sequent.mk ((pre ++ [B]) ++ [A] ++ rest ++ post) Λ) :=
      folkCutFree_of_eq (by simp) h2
    have h4 := ih (pre ++ [B]) h3
    exact folkCutFree_of_eq (by simp) h4

-- Sink an element from the end past a segment
theorem folkCutFree_sinkRightPast {L : Language}
    (pre mid post : List (FormulaN L)) (Γ : List (FormulaN L))
    (A : FormulaN L)
    (h : folkCutFreeProvable (Sequent.mk Γ (pre ++ mid ++ [A] ++ post))) :
    folkCutFreeProvable (Sequent.mk Γ (pre ++ [A] ++ mid ++ post)) := by
-- BEGIN PROOF
  induction mid generalizing pre with
  | nil => simp at h ⊢; exact h
  | cons B rest ih =>
    have h1 : folkCutFreeProvable
        (Sequent.mk Γ ((pre ++ [B]) ++ rest ++ [A] ++ post)) :=
      folkCutFree_of_eq (by simp) h
    have h2 : folkCutFreeProvable
        (Sequent.mk Γ ((pre ++ [B]) ++ [A] ++ rest ++ post)) :=
      ih (pre ++ [B]) h1
    have h3 : folkCutFreeProvable
        (Sequent.mk Γ (pre ++ [B, A] ++ (rest ++ post))) :=
      folkCutFree_of_eq (by simp) h2
    have h4 := folkCutFree_exchangeRight_adj Γ pre B A (rest ++ post) h3
    exact folkCutFree_of_eq (by simp) h4

theorem list_split_mem {L : Language} {A : FormulaN L} {lst : List (FormulaN L)}
    (h : A ∈ lst) : ∃ before after, lst = before ++ [A] ++ after := by
-- BEGIN PROOF
  induction lst with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | hxs
    · exact ⟨[], xs, by simp⟩
    · obtain ⟨before, after, heq⟩ := ih hxs
      exact ⟨x :: before, after, by simp [heq]⟩

-- Weaken left by appending after current antecedent
theorem folkCutFree_weakenLeftAppend {L : Language}
    (Γ' Γ Δ : List (FormulaN L))
    (h : folkCutFreeProvable (Sequent.mk Γ Δ)) :
    folkCutFreeProvable (Sequent.mk (Γ ++ Γ') Δ) := by
-- BEGIN PROOF
  induction Γ' generalizing Γ with
  | nil => simp; exact h
  | cons B rest ih =>
    have h1 := folkCutFree_weakenLeft B Γ Δ h
    have h2 := folkCutFree_sinkLeftPast [] Γ [] Δ B
      (folkCutFree_of_eq (by simp) h1)
    have h3 : folkCutFreeProvable (Sequent.mk (Γ ++ [B]) Δ) :=
      folkCutFree_of_eq (by simp) h2
    have h4 := ih (Γ ++ [B]) h3
    rwa [List.append_assoc] at h4

-- Weaken right by prepending before current succedent
theorem folkCutFree_weakenRightPrepend {L : Language}
    (Δ' Γ Δ : List (FormulaN L))
    (h : folkCutFreeProvable (Sequent.mk Γ Δ)) :
    folkCutFreeProvable (Sequent.mk Γ (Δ' ++ Δ)) := by
-- BEGIN PROOF
  induction Δ' with
  | nil => simp; exact h
  | cons B rest ih =>
    have h1 := ih
    have h2 := folkCutFree_weakenRight B Γ (rest ++ Δ) h1
    have h3 := folkCutFree_sinkRightPast [] (rest ++ Δ) [] Γ B
      (folkCutFree_of_eq (by simp) h2)
    exact folkCutFree_of_eq (by simp) h3

-- Shared axiom: from isAxiom to folkCutFreeProvable
theorem folkCutFree_shared_axiom {L : Language}
    (s : Sequent L) (h : isAxiom s) :
    folkCutFreeProvable s := by
-- BEGIN PROOF
  obtain ⟨A, hAnt, hASucc⟩ := h
  have base := folkCutFree_axiom A
  obtain ⟨Γ, Δ⟩ := s
  change A ∈ Γ at hAnt
  change A ∈ Δ at hASucc
  obtain ⟨before_a, after_a, ha_eq⟩ := list_split_mem hAnt
  obtain ⟨before_s, after_s, hs_eq⟩ := list_split_mem hASucc
  have h1 := folkCutFree_weakenLeftList before_a [A] [A] base
  have h2 := folkCutFree_weakenLeftAppend after_a (before_a ++ [A]) [A] h1
  have h2' : folkCutFreeProvable (Sequent.mk Γ [A]) := by
    rw [ha_eq]; simpa [List.append_assoc] using h2
  have h3 := folkCutFree_weakenRightPrepend before_s Γ [A] h2'
  have h4 := folkCutFree_weakenRightList after_s Γ (before_s ++ [A]) h3
  rw [hs_eq]; simpa [List.append_assoc] using h4

theorem folkCutFree_orLeft_head {L : Language}
    (A B : FormulaN L) (Γ Δ : List (FormulaN L))
    (h1 : folkCutFreeProvable (Sequent.mk (A :: Γ) Δ))
    (h2 : folkCutFreeProvable (Sequent.mk (B :: Γ) Δ)) :
    folkCutFreeProvable (Sequent.mk (FormulaN.disj A B :: Γ) Δ) := by
-- BEGIN PROOF
  obtain ⟨t1, hcf1⟩ := h1
  obtain ⟨t2, hcf2⟩ := h2
  exact ⟨.twoPremise (.orLeft A B Γ Δ) t1 t2, ⟨trivial, hcf1, hcf2⟩⟩

theorem folkCutFree_implLeft_head {L : Language}
    (A B : FormulaN L) (Γ Δ Λ Θ : List (FormulaN L))
    (h1 : folkCutFreeProvable (Sequent.mk Γ (Δ ++ [A])))
    (h2 : folkCutFreeProvable (Sequent.mk (B :: Λ) Θ)) :
    folkCutFreeProvable (Sequent.mk (FormulaN.impl A B :: Γ ++ Λ) (Δ ++ Θ)) := by
-- BEGIN PROOF
  obtain ⟨t1, hcf1⟩ := h1
  obtain ⟨t2, hcf2⟩ := h2
  exact ⟨.twoPremise (.implLeft A B Γ Δ Λ Θ) t1 t2, ⟨trivial, hcf1, hcf2⟩⟩

theorem folkCutFree_implRight_head {L : Language}
    (A B : FormulaN L) (Γ Δ : List (FormulaN L))
    (h : folkCutFreeProvable (Sequent.mk (A :: Γ) (Δ ++ [B]))) :
    folkCutFreeProvable (Sequent.mk Γ (Δ ++ [FormulaN.impl A B])) := by
-- BEGIN PROOF
  obtain ⟨t, hcf⟩ := h
  exact ⟨.onePremise (.implRight A B Γ Δ) t, hcf⟩

theorem folkCutFree_negLeft_head {L : Language}
    (A : FormulaN L) (Γ Δ : List (FormulaN L))
    (h : folkCutFreeProvable (Sequent.mk Γ (Δ ++ [A]))) :
    folkCutFreeProvable (Sequent.mk (FormulaN.neg A :: Γ) Δ) := by
-- BEGIN PROOF
  obtain ⟨t, hcf⟩ := h
  exact ⟨.onePremise (.negLeft A Γ Δ) t, hcf⟩

theorem folkCutFree_allLeft_head {L : Language}
    (t_term : Term L) (x : Nat) (A : FormulaN L)
    (Γ Δ : List (FormulaN L))
    (hfree : isFreeForN t_term x A)
    (h : folkCutFreeProvable (Sequent.mk (formulaSubstN A t_term x :: Γ) Δ)) :
    folkCutFreeProvable (Sequent.mk (FormulaN.all x A :: Γ) Δ) := by
-- BEGIN PROOF
  obtain ⟨t, hcf⟩ := h
  exact ⟨.onePremise (.allLeft t_term x A Γ Δ hfree) t, hcf⟩

end LCS.CutElim.LK
end
