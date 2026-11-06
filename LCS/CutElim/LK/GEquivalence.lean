import LCS.Item
import LCS.Util
import LCS.CutElim.CompletenessBridge
import LCS.CutElim.DecEqOfSymbols
import LCS.CutElim.LK.Syntax
import LCS.CutElim.LK.Soundness
import Attach
import LCS.CutElim.LK.GEquivalence.ProofsStamp

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
section

local notation "CutFreeTree" => (fun s => {t : FOLKProofTree s // FOLKProofTree.isCutFree t})

/-- Theorem 6.2.1 (G → cut-free LK): Compute a cut-free LK-proof tree
from a G-proof tree of the same sequent, using the extended quantifier
rules of §5.4.8. The effective procedure assumes decidable predicate,
function and constant symbols. Its cut-free guarantee is given separately
by `convert_g_to_folkCutFree_isCutFree`. -/
@[blueprint "chap6__theorem_6_2_1"]
def convert_g_to_folkCutFree {L : Language}
    [DecidableEq L.predSymbols] [DecidableEq L.funSymbols] [DecidableEq L.constSymbols]
    {seq : Sequent L} (t : GProofTreeExt seq) : FOLKProofTree seq :=
  (convert t).val
where
  folkCutFree_weakenLeft {L : Language}
      (B : FormulaN L) (Γ Δ : List (FormulaN L))
      (h : CutFreeTree (Sequent.mk Γ Δ)) :
      CutFreeTree (Sequent.mk (B :: Γ) Δ) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.weakenLeft B Γ Δ) t, hcf⟩

  folkCutFree_weakenRight {L : Language}
      (B : FormulaN L) (Γ Δ : List (FormulaN L))
      (h : CutFreeTree (Sequent.mk Γ Δ)) :
      CutFreeTree (Sequent.mk Γ (Δ ++ [B])) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.weakenRight B Γ Δ) t, hcf⟩

  folkCutFree_axiom {L : Language} (A : FormulaN L) :
      CutFreeTree (Sequent.mk [A] [A]) :=
    ⟨.axiom_ (Sequent.mk [A] [A]) ⟨A, rfl, rfl⟩, trivial⟩

  folkCutFree_weakenLeftList {L : Language}
      (Γ' Γ Δ : List (FormulaN L))
      (h : CutFreeTree (Sequent.mk Γ Δ)) :
      CutFreeTree (Sequent.mk (Γ' ++ Γ) Δ) := by
    cases Γ' with
    | nil => exact folkCutFree_of_eq (by simp) h
    | cons B rest =>
      have ih := folkCutFree_weakenLeftList rest Γ Δ h
      exact folkCutFree_weakenLeft B (rest ++ Γ) Δ ih
  termination_by structural Γ'

  folkCutFree_weakenRightList {L : Language}
      (Δ' Γ Δ : List (FormulaN L))
      (h : CutFreeTree (Sequent.mk Γ Δ)) :
      CutFreeTree (Sequent.mk Γ (Δ ++ Δ')) := by
    cases Δ' with
    | nil => exact folkCutFree_of_eq (by simp) h
    | cons B rest =>
      have ih := fun Δ h => folkCutFree_weakenRightList rest Γ Δ h
      have h1 : CutFreeTree (Sequent.mk Γ (Δ ++ [B])) :=
        folkCutFree_weakenRight B Γ Δ h
      have h2 := ih (Δ ++ [B]) h1
      exact folkCutFree_of_eq (by simp) h2
  termination_by structural Δ'

  folkCutFree_contractLeft_head {L : Language}
      (A : FormulaN L) (Γ Δ : List (FormulaN L))
      (h : CutFreeTree (Sequent.mk (A :: A :: Γ) Δ)) :
      CutFreeTree (Sequent.mk (A :: Γ) Δ) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.contractLeft A Γ Δ) t, hcf⟩

  folkCutFree_contractRight_end {L : Language}
      (A : FormulaN L) (Γ Δ : List (FormulaN L))
      (h : CutFreeTree (Sequent.mk Γ (Δ ++ [A, A]))) :
      CutFreeTree (Sequent.mk Γ (Δ ++ [A])) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.contractRight A Γ Δ) t, hcf⟩

  folkCutFree_exchangeLeft_adj {L : Language}
      (Γ : List (FormulaN L)) (A B : FormulaN L)
      (Δ Λ : List (FormulaN L))
      (h : CutFreeTree (Sequent.mk (Γ ++ [A, B] ++ Δ) Λ)) :
      CutFreeTree (Sequent.mk (Γ ++ [B, A] ++ Δ) Λ) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.exchangeLeft Γ A B Δ Λ) t, hcf⟩

  folkCutFree_exchangeRight_adj {L : Language}
      (Γ Δ : List (FormulaN L)) (A B : FormulaN L)
      (Λ : List (FormulaN L))
      (h : CutFreeTree (Sequent.mk Γ (Δ ++ [A, B] ++ Λ))) :
      CutFreeTree (Sequent.mk Γ (Δ ++ [B, A] ++ Λ)) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.exchangeRight Γ Δ A B Λ) t, hcf⟩

  -- Equality transport for CutFreeTree
  folkCutFree_of_eq {L : Language} {s1 s2 : Sequent L}
      (heq : s1 = s2) (h : CutFreeTree s1) :
      CutFreeTree s2 := heq ▸ h

  -- Float an element from inside a left list to the front
  folkCutFree_floatLeftPast {L : Language}
      (pre mid post : List (FormulaN L)) (Λ : List (FormulaN L))
      (A : FormulaN L)
      (h : CutFreeTree (Sequent.mk (pre ++ mid ++ [A] ++ post) Λ)) :
      CutFreeTree (Sequent.mk (pre ++ [A] ++ mid ++ post) Λ) := by
    cases mid with
    | nil => exact folkCutFree_of_eq (by simp) h
    | cons B rest =>
      have ih := fun pre h => folkCutFree_floatLeftPast pre rest post Λ A h
      have h1 : CutFreeTree
          (Sequent.mk ((pre ++ [B]) ++ rest ++ [A] ++ post) Λ) :=
        folkCutFree_of_eq (by simp) h
      have h2 : CutFreeTree
          (Sequent.mk ((pre ++ [B]) ++ [A] ++ rest ++ post) Λ) :=
        ih (pre ++ [B]) h1
      have h3 : CutFreeTree
          (Sequent.mk (pre ++ [B, A] ++ (rest ++ post)) Λ) :=
        folkCutFree_of_eq (by simp) h2
      have h4 := folkCutFree_exchangeLeft_adj pre B A (rest ++ post) Λ h3
      exact folkCutFree_of_eq (by simp) h4
  termination_by structural mid

  -- Sink an element from front past a segment
  folkCutFree_sinkLeftPast {L : Language}
      (pre mid post : List (FormulaN L)) (Λ : List (FormulaN L))
      (A : FormulaN L)
      (h : CutFreeTree (Sequent.mk (pre ++ [A] ++ mid ++ post) Λ)) :
      CutFreeTree (Sequent.mk (pre ++ mid ++ [A] ++ post) Λ) := by
    cases mid with
    | nil => exact folkCutFree_of_eq (by simp) h
    | cons B rest =>
      have ih := fun pre h => folkCutFree_sinkLeftPast pre rest post Λ A h
      have h1 : CutFreeTree
          (Sequent.mk (pre ++ [A, B] ++ (rest ++ post)) Λ) :=
        folkCutFree_of_eq (by simp) h
      have h2 := folkCutFree_exchangeLeft_adj pre A B (rest ++ post) Λ h1
      have h3 : CutFreeTree
          (Sequent.mk ((pre ++ [B]) ++ [A] ++ rest ++ post) Λ) :=
        folkCutFree_of_eq (by simp) h2
      have h4 := ih (pre ++ [B]) h3
      exact folkCutFree_of_eq (by simp) h4
  termination_by structural mid

  -- Float an element from inside a right list to the end
  folkCutFree_floatRightPast {L : Language}
      (pre mid post : List (FormulaN L)) (Γ : List (FormulaN L))
      (A : FormulaN L)
      (h : CutFreeTree (Sequent.mk Γ (pre ++ [A] ++ mid ++ post))) :
      CutFreeTree (Sequent.mk Γ (pre ++ mid ++ [A] ++ post)) := by
    cases mid with
    | nil => exact folkCutFree_of_eq (by simp) h
    | cons B rest =>
      have ih := fun pre h => folkCutFree_floatRightPast pre rest post Γ A h
      have h1 : CutFreeTree
          (Sequent.mk Γ (pre ++ [A, B] ++ (rest ++ post))) :=
        folkCutFree_of_eq (by simp) h
      have h2 := folkCutFree_exchangeRight_adj Γ pre A B (rest ++ post) h1
      have h3 : CutFreeTree
          (Sequent.mk Γ ((pre ++ [B]) ++ [A] ++ rest ++ post)) :=
        folkCutFree_of_eq (by simp) h2
      have h4 := ih (pre ++ [B]) h3
      exact folkCutFree_of_eq (by simp) h4
  termination_by structural mid

  -- Sink an element from the end past a segment
  folkCutFree_sinkRightPast {L : Language}
      (pre mid post : List (FormulaN L)) (Γ : List (FormulaN L))
      (A : FormulaN L)
      (h : CutFreeTree (Sequent.mk Γ (pre ++ mid ++ [A] ++ post))) :
      CutFreeTree (Sequent.mk Γ (pre ++ [A] ++ mid ++ post)) := by
    cases mid with
    | nil => exact folkCutFree_of_eq (by simp) h
    | cons B rest =>
      have ih := fun pre h => folkCutFree_sinkRightPast pre rest post Γ A h
      have h1 : CutFreeTree
          (Sequent.mk Γ ((pre ++ [B]) ++ rest ++ [A] ++ post)) :=
        folkCutFree_of_eq (by simp) h
      have h2 : CutFreeTree
          (Sequent.mk Γ ((pre ++ [B]) ++ [A] ++ rest ++ post)) :=
        ih (pre ++ [B]) h1
      have h3 : CutFreeTree
          (Sequent.mk Γ (pre ++ [B, A] ++ (rest ++ post))) :=
        folkCutFree_of_eq (by simp) h2
      have h4 := folkCutFree_exchangeRight_adj Γ pre B A (rest ++ post) h3
      exact folkCutFree_of_eq (by simp) h4
  termination_by structural mid

  /-- Split at the first occurrence, computing both list segments. -/
  list_split_mem {L : Language} [DecidableEq (FormulaN L)]
      {A : FormulaN L} {lst : List (FormulaN L)} (h : A ∈ lst) :
      Σ before, {after // lst = before ++ [A] ++ after} := by
    cases lst with
    | nil => exact False.elim (by simpa using h)
    | cons x xs =>
      if hx : A = x then
        subst x
        exact ⟨[], xs, rfl⟩
      else
        have hm : A ∈ xs := (List.mem_cons.mp h).resolve_left hx
        obtain ⟨before, after, heq⟩ := list_split_mem hm
        exact ⟨x :: before, after, by simp [heq]⟩
  termination_by structural lst

  /-- Find the first antecedent formula that also belongs to the succedent. -/
  sharedFormula {L : Language} [DecidableEq (FormulaN L)]
      (Γ Δ : List (FormulaN L)) (h : ∃ A ∈ Γ, A ∈ Δ) :
      {A // A ∈ Γ ∧ A ∈ Δ} := by
    cases Γ with
    | nil => exact False.elim (by simpa using h)
    | cons A rest =>
      if hA : A ∈ Δ then
        exact ⟨A, List.mem_cons_self, hA⟩
      else
        have hr : ∃ B ∈ rest, B ∈ Δ := by
          obtain ⟨B, hB, hΔ⟩ := h
          rcases List.mem_cons.mp hB with rfl | hB
          · exact False.elim (hA hΔ)
          · exact ⟨B, hB, hΔ⟩
        let result := sharedFormula rest Δ hr
        exact ⟨result.val, List.mem_cons_of_mem _ result.property.1, result.property.2⟩
  termination_by structural Γ

  -- Weaken left by appending after current antecedent
  folkCutFree_weakenLeftAppend {L : Language}
      (Γ' Γ Δ : List (FormulaN L))
      (h : CutFreeTree (Sequent.mk Γ Δ)) :
      CutFreeTree (Sequent.mk (Γ ++ Γ') Δ) := by
    cases Γ' with
    | nil => exact folkCutFree_of_eq (by simp) h
    | cons B rest =>
      have ih := fun Γ h => folkCutFree_weakenLeftAppend rest Γ Δ h
      have h1 := folkCutFree_weakenLeft B Γ Δ h
      have h2 := folkCutFree_sinkLeftPast [] Γ [] Δ B
        (folkCutFree_of_eq (by simp) h1)
      have h3 : CutFreeTree (Sequent.mk (Γ ++ [B]) Δ) :=
        folkCutFree_of_eq (by simp) h2
      have h4 := ih (Γ ++ [B]) h3
      exact folkCutFree_of_eq (by simp) h4
  termination_by structural Γ'

  -- Weaken right by prepending before current succedent
  folkCutFree_weakenRightPrepend {L : Language}
      (Δ' Γ Δ : List (FormulaN L))
      (h : CutFreeTree (Sequent.mk Γ Δ)) :
      CutFreeTree (Sequent.mk Γ (Δ' ++ Δ)) := by
    cases Δ' with
    | nil => exact folkCutFree_of_eq (by simp) h
    | cons B rest =>
      have ih := folkCutFree_weakenRightPrepend rest Γ Δ h
      have h1 := ih
      have h2 := folkCutFree_weakenRight B Γ (rest ++ Δ) h1
      have h3 := folkCutFree_sinkRightPast [] (rest ++ Δ) [] Γ B
        (folkCutFree_of_eq (by simp) h2)
      exact folkCutFree_of_eq (by simp) h3
  termination_by structural Δ'

  -- Shared axiom: from isAxiom to CutFreeTree
  folkCutFree_shared_axiom {L : Language} [DecidableEq (FormulaN L)]
      (s : Sequent L) (h : isAxiom s) :
      CutFreeTree s := by
    obtain ⟨A, hAnt, hASucc⟩ := sharedFormula s.antecedent s.succedent h
    have base := folkCutFree_axiom A
    obtain ⟨Γ, Δ⟩ := s
    change A ∈ Γ at hAnt
    change A ∈ Δ at hASucc
    obtain ⟨before_a, after_a, ha_eq⟩ := list_split_mem hAnt
    obtain ⟨before_s, after_s, hs_eq⟩ := list_split_mem hASucc
    have h1 := folkCutFree_weakenLeftList before_a [A] [A] base
    have h2 := folkCutFree_weakenLeftAppend after_a (before_a ++ [A]) [A] h1
    have h2' : CutFreeTree (Sequent.mk Γ [A]) := by
      exact folkCutFree_of_eq (by simp [ha_eq]) h2
    have h3 := folkCutFree_weakenRightPrepend before_s Γ [A] h2'
    have h4 := folkCutFree_weakenRightList after_s Γ (before_s ++ [A]) h3
    exact folkCutFree_of_eq (by simp [hs_eq]) h4

  -- Logical rule helpers
  folkCutFree_andLeftL_head {L : Language}
      (A B : FormulaN L) (Γ Δ : List (FormulaN L))
      (h : CutFreeTree (Sequent.mk (A :: Γ) Δ)) :
      CutFreeTree (Sequent.mk (FormulaN.conj A B :: Γ) Δ) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.andLeftL A B Γ Δ) t, hcf⟩

  folkCutFree_andLeftR_head {L : Language}
      (A B : FormulaN L) (Γ Δ : List (FormulaN L))
      (h : CutFreeTree (Sequent.mk (B :: Γ) Δ)) :
      CutFreeTree (Sequent.mk (FormulaN.conj A B :: Γ) Δ) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.andLeftR A B Γ Δ) t, hcf⟩

  folkCutFree_andRight_end {L : Language}
      (A B : FormulaN L) (Γ Δ : List (FormulaN L))
      (h1 : CutFreeTree (Sequent.mk Γ (Δ ++ [A])))
      (h2 : CutFreeTree (Sequent.mk Γ (Δ ++ [B]))) :
      CutFreeTree (Sequent.mk Γ (Δ ++ [FormulaN.conj A B])) := by
    obtain ⟨t1, hcf1⟩ := h1
    obtain ⟨t2, hcf2⟩ := h2
    exact ⟨.twoPremise (.andRight A B Γ Δ) t1 t2, ⟨trivial, hcf1, hcf2⟩⟩

  folkCutFree_orLeft_head {L : Language}
      (A B : FormulaN L) (Γ Δ : List (FormulaN L))
      (h1 : CutFreeTree (Sequent.mk (A :: Γ) Δ))
      (h2 : CutFreeTree (Sequent.mk (B :: Γ) Δ)) :
      CutFreeTree (Sequent.mk (FormulaN.disj A B :: Γ) Δ) := by
    obtain ⟨t1, hcf1⟩ := h1
    obtain ⟨t2, hcf2⟩ := h2
    exact ⟨.twoPremise (.orLeft A B Γ Δ) t1 t2, ⟨trivial, hcf1, hcf2⟩⟩

  folkCutFree_orRightL_end {L : Language}
      (A B : FormulaN L) (Γ Δ : List (FormulaN L))
      (h : CutFreeTree (Sequent.mk Γ (Δ ++ [A]))) :
      CutFreeTree (Sequent.mk Γ (Δ ++ [FormulaN.disj A B])) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.orRightL A B Γ Δ) t, hcf⟩

  folkCutFree_orRightR_end {L : Language}
      (A B : FormulaN L) (Γ Δ : List (FormulaN L))
      (h : CutFreeTree (Sequent.mk Γ (Δ ++ [B]))) :
      CutFreeTree (Sequent.mk Γ (Δ ++ [FormulaN.disj A B])) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.orRightR A B Γ Δ) t, hcf⟩

  folkCutFree_implLeft_head {L : Language}
      (A B : FormulaN L) (Γ Δ Λ Θ : List (FormulaN L))
      (h1 : CutFreeTree (Sequent.mk Γ (Δ ++ [A])))
      (h2 : CutFreeTree (Sequent.mk (B :: Λ) Θ)) :
      CutFreeTree (Sequent.mk (FormulaN.impl A B :: Γ ++ Λ) (Δ ++ Θ)) := by
    obtain ⟨t1, hcf1⟩ := h1
    obtain ⟨t2, hcf2⟩ := h2
    exact ⟨.twoPremise (.implLeft A B Γ Δ Λ Θ) t1 t2, ⟨trivial, hcf1, hcf2⟩⟩

  folkCutFree_implRight_head {L : Language}
      (A B : FormulaN L) (Γ Δ : List (FormulaN L))
      (h : CutFreeTree (Sequent.mk (A :: Γ) (Δ ++ [B]))) :
      CutFreeTree (Sequent.mk Γ (Δ ++ [FormulaN.impl A B])) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.implRight A B Γ Δ) t, hcf⟩

  folkCutFree_negLeft_head {L : Language}
      (A : FormulaN L) (Γ Δ : List (FormulaN L))
      (h : CutFreeTree (Sequent.mk Γ (Δ ++ [A]))) :
      CutFreeTree (Sequent.mk (FormulaN.neg A :: Γ) Δ) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.negLeft A Γ Δ) t, hcf⟩

  folkCutFree_negRight_head {L : Language}
      (A : FormulaN L) (Γ Δ : List (FormulaN L))
      (h : CutFreeTree (Sequent.mk (A :: Γ) Δ)) :
      CutFreeTree (Sequent.mk Γ (Δ ++ [FormulaN.neg A])) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.negRight A Γ Δ) t, hcf⟩

  folkCutFree_allLeft_head {L : Language}
      (t_term : Term L) (x : Nat) (A : FormulaN L)
      (Γ Δ : List (FormulaN L))
      (hfree : isFreeForN t_term x A)
      (h : CutFreeTree (Sequent.mk (formulaSubstN A t_term x :: Γ) Δ)) :
      CutFreeTree (Sequent.mk (FormulaN.all x A :: Γ) Δ) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.allLeft t_term x A Γ Δ hfree) t, hcf⟩

  folkCutFree_allRight_end {L : Language}
      (y : Nat) (x : Nat) (A : FormulaN L)
      (Γ Δ : List (FormulaN L))
      (hfresh : ∀ F ∈ (Sequent.mk Γ (Δ ++ [FormulaN.all x A])).antecedent ++
                       (Sequent.mk Γ (Δ ++ [FormulaN.all x A])).succedent,
                  y ∉ formulaFVN F)
      (hfreeFor : isFreeForN (Term.var y) x A)
      (h : CutFreeTree (Sequent.mk Γ (Δ ++ [formulaSubstN A (Term.var y) x]))) :
      CutFreeTree (Sequent.mk Γ (Δ ++ [FormulaN.all x A])) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.allRight y x A Γ Δ hfresh hfreeFor) t, hcf⟩

  folkCutFree_exLeft_head {L : Language}
      (y : Nat) (x : Nat) (A : FormulaN L)
      (Γ Δ : List (FormulaN L))
      (hfresh : ∀ F ∈ (Sequent.mk (FormulaN.ex x A :: Γ) Δ).antecedent ++
                       (Sequent.mk (FormulaN.ex x A :: Γ) Δ).succedent,
                  y ∉ formulaFVN F)
      (hfreeFor : isFreeForN (Term.var y) x A)
      (h : CutFreeTree (Sequent.mk (formulaSubstN A (Term.var y) x :: Γ) Δ)) :
      CutFreeTree (Sequent.mk (FormulaN.ex x A :: Γ) Δ) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.exLeft y x A Γ Δ hfresh hfreeFor) t, hcf⟩

  folkCutFree_exRight_end {L : Language}
      (t_term : Term L) (x : Nat) (A : FormulaN L)
      (Γ Δ : List (FormulaN L))
      (hfree : isFreeForN t_term x A)
      (h : CutFreeTree (Sequent.mk Γ (Δ ++ [formulaSubstN A t_term x]))) :
      CutFreeTree (Sequent.mk Γ (Δ ++ [FormulaN.ex x A])) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.exRight t_term x A Γ Δ hfree) t, hcf⟩

  -- Contract left list helper
  folkCutFree_contractLeftList {L : Language}
      (pfx lst : List (FormulaN L)) (Δ : List (FormulaN L))
      (h : CutFreeTree (Sequent.mk (pfx ++ lst ++ lst) Δ)) :
      CutFreeTree (Sequent.mk (pfx ++ lst) Δ) := by
    cases lst with
    | nil => exact folkCutFree_of_eq (by simp) h
    | cons A rest =>
      have ih := fun pfx h => folkCutFree_contractLeftList pfx rest Δ h
      have step1 := folkCutFree_floatLeftPast (pfx ++ [A]) rest rest Δ A
        (folkCutFree_of_eq (by simp) h)
      have step2 := folkCutFree_floatLeftPast [] (pfx ++ [A]) (rest ++ rest) Δ A
        (folkCutFree_of_eq (by simp) step1)
      have step3 := folkCutFree_floatLeftPast [A] pfx (rest ++ rest) Δ A
        (folkCutFree_of_eq (by simp) step2)
      have step4 := folkCutFree_contractLeft_head A (pfx ++ rest ++ rest) Δ
        (folkCutFree_of_eq (by simp) step3)
      have step5 := folkCutFree_sinkLeftPast [] pfx (rest ++ rest) Δ A
        (folkCutFree_of_eq (by simp) step4)
      have step6 := ih (pfx ++ [A]) (folkCutFree_of_eq (by simp) step5)
      exact folkCutFree_of_eq (by simp) step6
  termination_by structural lst

  -- Contract right list helper
  folkCutFree_contractRightList {L : Language}
      (pfx lst : List (FormulaN L)) (Γ : List (FormulaN L))
      (h : CutFreeTree (Sequent.mk Γ (pfx ++ lst ++ lst))) :
      CutFreeTree (Sequent.mk Γ (pfx ++ lst)) := by
    cases lst with
    | nil => exact folkCutFree_of_eq (by simp) h
    | cons A rest =>
      have ih := fun pfx h => folkCutFree_contractRightList pfx rest Γ h
      have step1 := folkCutFree_sinkRightPast (pfx ++ [A]) rest rest Γ A
        (folkCutFree_of_eq (by simp) h)
      have step2 := folkCutFree_floatRightPast (pfx ++ [A]) (rest ++ rest) [] Γ A
        (folkCutFree_of_eq (by simp) step1)
      have step3 := folkCutFree_floatRightPast pfx (rest ++ rest ++ [A]) [] Γ A
        (folkCutFree_of_eq (by simp) step2)
      have step4 := folkCutFree_contractRight_end A Γ (pfx ++ rest ++ rest)
        (folkCutFree_of_eq (by simp) step3)
      have step5 := folkCutFree_sinkRightPast pfx (rest ++ rest) [] Γ A
        (folkCutFree_of_eq (by simp) step4)
      have step6 := ih (pfx ++ [A]) (folkCutFree_of_eq (by simp) step5)
      exact folkCutFree_of_eq (by simp) step6
  termination_by structural lst

  -- ===================================================================
  -- Theorem 6.2.1: gProofTree_to_folkCutFree
  -- ===================================================================

  -- k-term ∀:left helper: from the §5.4.8 extended-rule premise shape
  -- (Γ ++ [A[t₁/x],...,A[tₖ/x]] ++ [∀x.A] ++ Δ ⟹ Λ) derive the conclusion
  -- shape (Γ ++ [∀x.A] ++ Δ ⟹ Λ) by induction on ts, peeling one term at a
  -- time: apply the single-term allLeft to tHead, then contract the two
  -- resulting ∀x.A's using the structural helpers.
  folkCutFree_allLeftN {L : Language}
      (ts : List (Term L)) (Γ Δ Λ : List (FormulaN L))
      (x : Nat) (A : FormulaN L)
      (hne : ts ≠ [])
      (hfree : ∀ t ∈ ts, isFreeForN t x A)
      (h : CutFreeTree
        (Sequent.mk (Γ ++ ts.map (fun t => formulaSubstN A t x) ++
                     [FormulaN.all x A] ++ Δ) Λ)) :
      CutFreeTree (Sequent.mk (Γ ++ [FormulaN.all x A] ++ Δ) Λ) := by
    cases ts with
    | nil => exact absurd rfl hne
    | cons tHead rest =>
      have ih := fun {Γ} hne hfree h => folkCutFree_allLeftN rest Γ Δ Λ x A hne hfree h
      have htFree : isFreeForN tHead x A := hfree tHead List.mem_cons_self
      have s1 : CutFreeTree
          (Sequent.mk ([formulaSubstN A tHead x] ++ Γ ++
            rest.map (fun t => formulaSubstN A t x) ++
            [FormulaN.all x A] ++ Δ) Λ) :=
        folkCutFree_of_eq (by simp [List.cons_append])
          (folkCutFree_floatLeftPast [] Γ
            (rest.map (fun t => formulaSubstN A t x) ++
              [FormulaN.all x A] ++ Δ) Λ (formulaSubstN A tHead x)
            (folkCutFree_of_eq (by simp) h))
      have s2 : CutFreeTree
          (Sequent.mk (FormulaN.all x A :: (Γ ++
            rest.map (fun t => formulaSubstN A t x) ++
            [FormulaN.all x A] ++ Δ)) Λ) :=
        folkCutFree_allLeft_head tHead x A
          (Γ ++ rest.map (fun t => formulaSubstN A t x) ++
            [FormulaN.all x A] ++ Δ) Λ htFree
          (folkCutFree_of_eq (by simp) s1)
      have s3 : CutFreeTree
          (Sequent.mk ([FormulaN.all x A] ++ [FormulaN.all x A] ++
            (Γ ++ rest.map (fun t => formulaSubstN A t x)) ++ Δ) Λ) :=
        folkCutFree_of_eq (by simp)
          (folkCutFree_floatLeftPast [FormulaN.all x A]
            (Γ ++ rest.map (fun t => formulaSubstN A t x)) Δ Λ
            (FormulaN.all x A)
            (folkCutFree_of_eq (by simp) s2))
      have s4 : CutFreeTree
          (Sequent.mk (FormulaN.all x A ::
            (Γ ++ rest.map (fun t => formulaSubstN A t x) ++ Δ)) Λ) :=
        folkCutFree_contractLeft_head (FormulaN.all x A)
          (Γ ++ rest.map (fun t => formulaSubstN A t x) ++ Δ) Λ
          (folkCutFree_of_eq (by simp) s3)
      have s5 : CutFreeTree
          (Sequent.mk (Γ ++ rest.map (fun t => formulaSubstN A t x) ++
            [FormulaN.all x A] ++ Δ) Λ) :=
        folkCutFree_of_eq (by simp)
          (folkCutFree_sinkLeftPast []
            (Γ ++ rest.map (fun t => formulaSubstN A t x)) Δ Λ
            (FormulaN.all x A) (folkCutFree_of_eq (by simp) s4))
      letI : Decidable (rest = []) := decidable_of_iff (rest.length = 0) (by simp)
      by_cases hrest : rest = []
      · subst hrest
        exact folkCutFree_of_eq (by simp) s5
      · exact ih (Γ := Γ) hrest
          (fun t' ht' => hfree t' (List.mem_cons_of_mem _ ht')) s5
  termination_by structural ts

  -- k-term ∃:right helper: dual of `folkCutFree_allLeftN` on the succedent.
  folkCutFree_exRightN {L : Language}
      (ts : List (Term L)) (Γ Δ Λ : List (FormulaN L))
      (x : Nat) (A : FormulaN L)
      (hne : ts ≠ [])
      (hfree : ∀ t ∈ ts, isFreeForN t x A)
      (h : CutFreeTree
        (Sequent.mk Γ (Δ ++ ts.map (fun t => formulaSubstN A t x) ++
                     [FormulaN.ex x A] ++ Λ))) :
      CutFreeTree (Sequent.mk Γ (Δ ++ [FormulaN.ex x A] ++ Λ)) := by
    cases ts with
    | nil => exact absurd rfl hne
    | cons tHead rest =>
      have ih := fun {Δ} hne hfree h => folkCutFree_exRightN rest Γ Δ Λ x A hne hfree h
      have htFree : isFreeForN tHead x A := hfree tHead List.mem_cons_self
      have s1 : CutFreeTree
          (Sequent.mk Γ ((Δ ++ rest.map (fun t => formulaSubstN A t x) ++
            [FormulaN.ex x A] ++ Λ) ++ [formulaSubstN A tHead x])) :=
        folkCutFree_of_eq (by simp)
          (folkCutFree_floatRightPast Δ
            (rest.map (fun t => formulaSubstN A t x) ++
              [FormulaN.ex x A] ++ Λ) [] Γ (formulaSubstN A tHead x)
            (folkCutFree_of_eq (by simp) h))
      have s2 : CutFreeTree
          (Sequent.mk Γ ((Δ ++ rest.map (fun t => formulaSubstN A t x) ++
            [FormulaN.ex x A] ++ Λ) ++ [FormulaN.ex x A])) :=
        folkCutFree_exRight_end tHead x A Γ
          (Δ ++ rest.map (fun t => formulaSubstN A t x) ++
            [FormulaN.ex x A] ++ Λ) htFree s1
      have s3 : CutFreeTree
          (Sequent.mk Γ
            (Δ ++ rest.map (fun t => formulaSubstN A t x) ++ Λ ++
              [FormulaN.ex x A] ++ [FormulaN.ex x A])) :=
        folkCutFree_of_eq (by simp)
          (folkCutFree_floatRightPast
            (Δ ++ rest.map (fun t => formulaSubstN A t x)) Λ
            [FormulaN.ex x A] Γ (FormulaN.ex x A)
            (folkCutFree_of_eq (by simp) s2))
      have s4 : CutFreeTree
          (Sequent.mk Γ
            (Δ ++ rest.map (fun t => formulaSubstN A t x) ++ Λ ++
              [FormulaN.ex x A])) :=
        folkCutFree_contractRight_end (FormulaN.ex x A) Γ
          (Δ ++ rest.map (fun t => formulaSubstN A t x) ++ Λ)
          (folkCutFree_of_eq (by simp) s3)
      have s5 : CutFreeTree
          (Sequent.mk Γ
            (Δ ++ rest.map (fun t => formulaSubstN A t x) ++
              [FormulaN.ex x A] ++ Λ)) :=
        folkCutFree_of_eq (by simp)
          (folkCutFree_sinkRightPast
            (Δ ++ rest.map (fun t => formulaSubstN A t x)) Λ []
            Γ (FormulaN.ex x A) (folkCutFree_of_eq (by simp) s4))
      letI : Decidable (rest = []) := decidable_of_iff (rest.length = 0) (by simp)
      by_cases hrest : rest = []
      · subst hrest
        exact folkCutFree_of_eq (by simp) s5
      · exact ih (Δ := Δ) hrest
          (fun t' ht' => hfree t' (List.mem_cons_of_mem _ ht')) s5
  termination_by structural ts

  /-- Theorem 6.2.1 (companion, G-tree to cut-free LK algorithm): Every
  indexed `GProofTreeExt` (under the §5.4.8 standing assumption) can be
  converted to a cut-free FOLKProofTree with the same conclusion. This
  is the constructive witness for the G → LK−{cut} conjunct of Theorem
  6.2.1. -/
  convert {L : Language}
      [DecidableEq L.predSymbols] [DecidableEq L.funSymbols] [DecidableEq L.constSymbols]
      {s : Sequent L} (t : GProofTreeExt s) :
      CutFreeTree s := by
    cases t with
    | axiom_ s hax =>
      letI : DecidableEq (FormulaN L) := FormulaN.decEqOfSymbols
      exact folkCutFree_shared_axiom s hax
    | onePremise rule sub =>
      have ih := convert sub
      cases rule with
      | conjLeft Γ Δ Λ A B =>
        have s1 : CutFreeTree
            (Sequent.mk ([] ++ Γ ++ [A] ++ ([B] ++ Δ)) Λ) :=
          folkCutFree_of_eq (by simp) ih
        have s2 := folkCutFree_floatLeftPast [] Γ ([B] ++ Δ) Λ A s1
        have s3 : CutFreeTree
            (Sequent.mk (A :: (Γ ++ [B] ++ Δ)) Λ) :=
          folkCutFree_of_eq (by simp) s2
        have s4 := folkCutFree_andLeftL_head A B (Γ ++ [B] ++ Δ) Λ s3
        have s5 : CutFreeTree
            (Sequent.mk (FormulaN.conj A B :: Γ ++ [B] ++ Δ) Λ) := s4
        have s6 := folkCutFree_floatLeftPast []
          (FormulaN.conj A B :: Γ) Δ Λ B s5
        have s7 : CutFreeTree
            (Sequent.mk (B :: (FormulaN.conj A B :: Γ ++ Δ)) Λ) :=
          folkCutFree_of_eq (by simp) s6
        have s8 := folkCutFree_andLeftR_head A B
          (FormulaN.conj A B :: Γ ++ Δ) Λ s7
        have s9 : CutFreeTree
            (Sequent.mk (FormulaN.conj A B :: FormulaN.conj A B :: Γ ++ Δ)
              Λ) := s8
        have s10 := folkCutFree_contractLeft_head
          (FormulaN.conj A B) (Γ ++ Δ) Λ s9
        have s11 : CutFreeTree
            (Sequent.mk (FormulaN.conj A B :: Γ ++ Δ) Λ) := s10
        have s12 := folkCutFree_sinkLeftPast [] Γ Δ Λ
          (FormulaN.conj A B) (folkCutFree_of_eq (by simp) s11)
        exact folkCutFree_of_eq (by simp) s12
      | disjRight Γ Δ Λ A B =>
        have i1 : CutFreeTree
            (Sequent.mk Γ (Δ ++ [A] ++ ([B] ++ Λ) ++ [])) :=
          folkCutFree_of_eq (by simp) ih
        have s1 : CutFreeTree
            (Sequent.mk Γ ((Δ ++ [B] ++ Λ) ++ [A])) :=
          folkCutFree_of_eq (by simp)
            (folkCutFree_floatRightPast Δ ([B] ++ Λ) [] Γ A i1)
        have s2 := folkCutFree_orRightL_end A B Γ (Δ ++ [B] ++ Λ) s1
        have s3 : CutFreeTree
            (Sequent.mk Γ (Δ ++ [B] ++ (Λ ++ [FormulaN.disj A B]) ++ [])) :=
          folkCutFree_of_eq (by simp) s2
        have s4 : CutFreeTree
            (Sequent.mk Γ ((Δ ++ Λ ++ [FormulaN.disj A B]) ++ [B])) :=
          folkCutFree_of_eq (by simp)
            (folkCutFree_floatRightPast Δ (Λ ++ [FormulaN.disj A B]) []
              Γ B s3)
        have s5 := folkCutFree_orRightR_end A B Γ
          (Δ ++ Λ ++ [FormulaN.disj A B]) s4
        have s6 : CutFreeTree
            (Sequent.mk Γ
              ((Δ ++ Λ) ++ [FormulaN.disj A B, FormulaN.disj A B])) :=
          folkCutFree_of_eq (by simp) s5
        have s7 := folkCutFree_contractRight_end (FormulaN.disj A B)
          Γ (Δ ++ Λ) s6
        have s8 : CutFreeTree
            (Sequent.mk Γ (Δ ++ Λ ++ [FormulaN.disj A B] ++ [])) :=
          folkCutFree_of_eq (by simp) s7
        exact folkCutFree_of_eq (by simp)
          (folkCutFree_sinkRightPast Δ Λ [] Γ (FormulaN.disj A B) s8)
      | implRight Γ Δ Λ A B =>
        have i1 : CutFreeTree
            (Sequent.mk ([A] ++ Γ) ([] ++ [B] ++ (Δ ++ Λ) ++ [])) :=
          folkCutFree_of_eq (by simp) ih
        have s1 : CutFreeTree
            (Sequent.mk (A :: Γ) ((Δ ++ Λ) ++ [B])) :=
          folkCutFree_of_eq (by simp)
            (folkCutFree_floatRightPast [] (Δ ++ Λ) [] ([A] ++ Γ) B i1)
        have s2 := folkCutFree_implRight_head A B Γ (Δ ++ Λ) s1
        have s3 : CutFreeTree
            (Sequent.mk Γ (Δ ++ Λ ++ [FormulaN.impl A B] ++ [])) :=
          folkCutFree_of_eq (by simp) s2
        exact folkCutFree_of_eq (by simp)
          (folkCutFree_sinkRightPast Δ Λ [] Γ (FormulaN.impl A B) s3)
      | negLeft Γ Δ Λ A =>
        have i1 : CutFreeTree (Sequent.mk (Γ ++ Δ) (Λ ++ [A])) :=
          folkCutFree_of_eq (by simp)
            (folkCutFree_floatRightPast [] Λ [] (Γ ++ Δ) A
              (folkCutFree_of_eq (by simp) ih))
        have s1 := folkCutFree_negLeft_head A (Γ ++ Δ) Λ i1
        have s2 : CutFreeTree
            (Sequent.mk (FormulaN.neg A :: (Γ ++ Δ)) Λ) := s1
        exact folkCutFree_of_eq (by simp)
          (folkCutFree_sinkLeftPast [] Γ Δ Λ (FormulaN.neg A)
            (folkCutFree_of_eq (by simp) s2))
      | negRight Γ Δ Λ A =>
        have i1 : CutFreeTree (Sequent.mk (A :: Γ) (Δ ++ Λ)) :=
          folkCutFree_of_eq (by simp) ih
        have s1 := folkCutFree_negRight_head A Γ (Δ ++ Λ) i1
        have s2 : CutFreeTree
            (Sequent.mk Γ (Δ ++ Λ ++ [FormulaN.neg A] ++ [])) :=
          folkCutFree_of_eq (by simp) s1
        exact folkCutFree_of_eq (by simp)
          (folkCutFree_sinkRightPast Δ Λ [] Γ (FormulaN.neg A) s2)
      | allLeft ts Γ Δ Λ x A hne hfree =>
        exact folkCutFree_allLeftN ts Γ Δ Λ x A hne hfree ih
      | allRight y_eig Γ Δ Λ x A hfresh hfreeFor =>
        have s0 := folkCutFree_floatRightPast Δ Λ [] Γ
          (formulaSubstN A (Term.var y_eig) x)
          (folkCutFree_of_eq (by simp) ih)
        have s1 : CutFreeTree
            (Sequent.mk Γ ((Δ ++ Λ) ++
              [formulaSubstN A (Term.var y_eig) x])) :=
          folkCutFree_of_eq (by simp) s0
        have hfr : ∀ F ∈ (Sequent.mk Γ ((Δ ++ Λ) ++
                  [FormulaN.all x A])).antecedent ++
                    (Sequent.mk Γ ((Δ ++ Λ) ++
                  [FormulaN.all x A])).succedent,
                   y_eig ∉ formulaFVN F := by
          intro F hF; apply hfresh F
          simp at hF ⊢
          rcases hF with h1 | h2 | h3 | h4 <;> simp_all
        have s2 := folkCutFree_allRight_end y_eig x A Γ (Δ ++ Λ)
          hfr hfreeFor s1
        have s3 : CutFreeTree
            (Sequent.mk Γ (Δ ++ Λ ++ [FormulaN.all x A] ++ [])) :=
          folkCutFree_of_eq (by simp) s2
        exact folkCutFree_of_eq (by simp)
          (folkCutFree_sinkRightPast Δ Λ [] Γ (FormulaN.all x A) s3)
      | exLeft y_eig Γ Δ Λ x A hfresh hfreeFor =>
        have s0 := folkCutFree_floatLeftPast [] Γ Δ Λ
          (formulaSubstN A (Term.var y_eig) x) ih
        have s1 : CutFreeTree
            (Sequent.mk (formulaSubstN A (Term.var y_eig) x ::
              (Γ ++ Δ)) Λ) :=
          folkCutFree_of_eq (by simp) s0
        have hfr : ∀ F ∈ (Sequent.mk
                    (FormulaN.ex x A :: Γ ++ Δ) Λ).antecedent ++
                    (Sequent.mk (FormulaN.ex x A :: Γ ++ Δ) Λ).succedent,
                   y_eig ∉ formulaFVN F := by
          intro F hF; apply hfresh F
          simp at hF ⊢
          rcases hF with h1 | h2 | h3 | h4 <;> simp_all
        have s2 := folkCutFree_exLeft_head y_eig x A
          (Γ ++ Δ) Λ hfr hfreeFor s1
        have s3 : CutFreeTree
            (Sequent.mk (FormulaN.ex x A :: (Γ ++ Δ)) Λ) := s2
        exact folkCutFree_of_eq (by simp)
          (folkCutFree_sinkLeftPast [] Γ Δ Λ (FormulaN.ex x A)
            (folkCutFree_of_eq (by simp) s3))
      | exRight ts Γ Δ Λ x A hne hfree =>
        exact folkCutFree_exRightN ts Γ Δ Λ x A hne hfree ih
    | twoPremise rule sub1 sub2 =>
      have ih1 := convert sub1
      have ih2 := convert sub2
      cases rule with
      | conjRight Γ Δ Λ A B =>
        have ia : CutFreeTree
            (Sequent.mk Γ (Δ ++ [A] ++ Λ ++ [])) :=
          folkCutFree_of_eq (by simp) ih1
        have ib : CutFreeTree
            (Sequent.mk Γ (Δ ++ [B] ++ Λ ++ [])) :=
          folkCutFree_of_eq (by simp) ih2
        have sa : CutFreeTree
            (Sequent.mk Γ ((Δ ++ Λ) ++ [A])) :=
          folkCutFree_of_eq (by simp)
            (folkCutFree_floatRightPast Δ Λ [] Γ A ia)
        have sb : CutFreeTree
            (Sequent.mk Γ ((Δ ++ Λ) ++ [B])) :=
          folkCutFree_of_eq (by simp)
            (folkCutFree_floatRightPast Δ Λ [] Γ B ib)
        have s1 := folkCutFree_andRight_end A B Γ (Δ ++ Λ) sa sb
        have s2 : CutFreeTree
            (Sequent.mk Γ (Δ ++ Λ ++ [FormulaN.conj A B] ++ [])) :=
          folkCutFree_of_eq (by simp) s1
        have s3 := folkCutFree_sinkRightPast Δ Λ [] Γ
          (FormulaN.conj A B) s2
        exact folkCutFree_of_eq (by simp) s3
      | disjLeft Γ Δ Λ A B =>
        have sa : CutFreeTree
            (Sequent.mk (A :: (Γ ++ Δ)) Λ) :=
          folkCutFree_of_eq (by simp)
            (folkCutFree_floatLeftPast [] Γ Δ Λ A ih1)
        have sb : CutFreeTree
            (Sequent.mk (B :: (Γ ++ Δ)) Λ) :=
          folkCutFree_of_eq (by simp)
            (folkCutFree_floatLeftPast [] Γ Δ Λ B ih2)
        have s1 := folkCutFree_orLeft_head A B (Γ ++ Δ) Λ sa sb
        have s2 : CutFreeTree
            (Sequent.mk (FormulaN.disj A B :: (Γ ++ Δ)) Λ) := s1
        exact folkCutFree_of_eq (by simp)
          (folkCutFree_sinkLeftPast [] Γ Δ Λ (FormulaN.disj A B)
            (folkCutFree_of_eq (by simp) s2))
      | implLeft Γ Δ Λ A B =>
        have i1 : CutFreeTree (Sequent.mk (Γ ++ Δ) (Λ ++ [A])) :=
          folkCutFree_of_eq (by simp)
            (folkCutFree_floatRightPast [] Λ [] (Γ ++ Δ) A
              (folkCutFree_of_eq (by simp) ih1))
        have s1 := folkCutFree_implLeft_head A B (Γ ++ Δ) Λ
          (Γ ++ Δ) Λ i1 ih2
        have s2 : CutFreeTree
            (Sequent.mk ([FormulaN.impl A B] ++ (Γ ++ Δ) ++ (Γ ++ Δ))
              (Λ ++ Λ)) :=
          folkCutFree_of_eq (by simp) s1
        have s3 := folkCutFree_contractLeftList
          [FormulaN.impl A B] (Γ ++ Δ) (Λ ++ Λ) s2
        have s4 : CutFreeTree
            (Sequent.mk (FormulaN.impl A B :: (Γ ++ Δ))
              ([] ++ Λ ++ Λ)) :=
          folkCutFree_of_eq (by simp) s3
        have s5 := folkCutFree_contractRightList [] Λ
          (FormulaN.impl A B :: Γ ++ Δ) s4
        have s6 : CutFreeTree
            (Sequent.mk (FormulaN.impl A B :: (Γ ++ Δ)) Λ) :=
          folkCutFree_of_eq (by simp) s5
        exact folkCutFree_of_eq (by simp)
          (folkCutFree_sinkLeftPast [] Γ Δ Λ (FormulaN.impl A B)
            (folkCutFree_of_eq (by simp) s6))
  termination_by structural t

end

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 6.2.1 (companion, G-tree to cut-free LK algorithm): Every
indexed `GProofTreeExt` (under the §5.4.8 standing assumption) can be
converted to a cut-free FOLKProofTree with the same conclusion. This
is the constructive witness for the G → LK−{cut} conjunct of Theorem
6.2.1. -/
theorem gProofTree_to_folkCutFree {L : Language}
    {s : Sequent L} (t : GProofTreeExt s) :
    folkCutFreeProvable s := by
  classical
  let result := convert_g_to_folkCutFree.convert t
  exact ⟨result.val, result.property⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 6.2.1 (companion, G to cut-free LK): If a sequent is
G-provable (under the §5.4.8 standing assumption, `sequentProvableExt`),
then it is LK-provable without cut. This is one of the two conjuncts
of Theorem 6.2.1 at the provability level. -/
theorem gProvable_folkCutFreeProvable {L : Language}
    (seq : Sequent L) (h : sequentProvableExt seq) :
    folkCutFreeProvable seq := by
-- BEGIN PROOF
  obtain ⟨t⟩ := h
  exact gProofTree_to_folkCutFree t

-- ===================================================================
-- Theorem 6.2.1: folk_g_equivalence
-- ===================================================================
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 6.2.1 (companion, bidirectional equivalence): Over a language
without equality, a sequent satisfying the §6.1 sequent-level free/bound
convention is LK-provable if and only if it is G-provable. The convention
on the end sequent supplies the LK-to-G direction under E-CUTFB. -/
theorem folk_g_equivalence {L : Language} [Countable (Term L)]
    (hL : L.withoutEquality) (seq : Sequent L)
    (hCross : crossNoFreeBound seq) :
    folkProvable seq ↔ sequentProvableExt seq := by
-- BEGIN PROOF
  constructor
  · intro hfolk
    have hvalid : sequentValid seq := soundness_FOLK seq hfolk
    exact completenessG_cross hL seq hCross hvalid
  · intro hgprov
    have hcf := gProvable_folkCutFreeProvable seq hgprov
    obtain ⟨t, _⟩ := hcf
    exact ⟨t⟩

-- ===================================================================
-- Theorem 6.2.1: concrete tree converters
-- ===================================================================
/-- Theorem 6.2.1 (LK → G): Selects a G-proof tree from an LK-proof tree
of the same sequent over a language without equality. The end sequent
satisfies the §6.1 sequent-level free/bound convention (E-CUTFB).
The selection uses soundness, completeness of G search, and classical choice. -/
@[blueprint "chap6__theorem_6_2_1" (main := true)]
noncomputable def convert_folk_to_g {L : Language} [Countable (Term L)]
    (hL : L.withoutEquality) {seq : Sequent L} (hCross : crossNoFreeBound seq)
    (t : FOLKProofTree seq) : GProofTreeExt seq := by
  have hfolk : folkProvable seq := ⟨t⟩
  have hg : sequentProvableExt seq :=
    (folk_g_equivalence hL seq hCross).mp hfolk
  exact Classical.choice hg

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The tree computed by the G-to-LK conversion is cut-free. -/
theorem convert_g_to_folkCutFree_isCutFree {L : Language}
    [DecidableEq L.predSymbols] [DecidableEq L.funSymbols] [DecidableEq L.constSymbols]
    {seq : Sequent L} (t : GProofTreeExt seq) :
    (convert_g_to_folkCutFree t).isCutFree := by
  exact (convert_g_to_folkCutFree.convert t).property

/-- Theorem 6.2.1 (companion spec): The effective G → LK conversion over
a language without equality produces a cut-free proof of the same sequent. -/
@[blueprint "chap6__theorem_6_2_1" (main := true)]
theorem theorem_6_2_1_spec {L : Language}
    [DecidableEq L.predSymbols] [DecidableEq L.funSymbols] [DecidableEq L.constSymbols]
    (_hL : L.withoutEquality) :
    ∀ (seq : Sequent L) (t : GProofTreeExt seq),
      (convert_g_to_folkCutFree t).isCutFree 

end LCS.CutElim.LK
end
