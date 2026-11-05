import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.CutElim.CompletenessBridge
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.LKe.Equivalence.AtomicLeaves
import LCS.CutElim.LKe.Equivalence.ContextPermutation
import LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
import LCS.CutElim.LKe.Equivalence.ImplicationPermutation
import LCS.CutElim.LKe.Equivalence.Normalization
import LCS.CutElim.LKe.Equivalence.AtomicTranslation
import Attach
import LCS.CutElim.LKe.Equivalence.EqualityTranslation.ProofsStamp

section
namespace LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality.Completeness
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.CompletenessBridge
open LCS.FirstOrder.Equality

namespace geqProof_to_lkeNoEssentialCuts

  -- ATTACH-BLOCKER: dependency: retained front declaration references this helper
noncomputable def lkeAtomic_contractLeft_head {L : Language}
      (A : FormulaN L) (Γ Δ : List (FormulaN L))
      (h : LKeAtomicProofTree (Sequent.mk (A :: A :: Γ) Δ)) :
      LKeAtomicProofTree (Sequent.mk (A :: Γ) Δ) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.contractLeft A Γ Δ) t, hcf⟩


  -- ATTACH-BLOCKER: dependency: retained front declaration references this helper
noncomputable def lkeAtomic_contractRight_end {L : Language}
      (A : FormulaN L) (Γ Δ : List (FormulaN L))
      (h : LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [A, A]))) :
      LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [A])) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.contractRight A Γ Δ) t, hcf⟩


  -- ATTACH-BLOCKER: dependency: retained front declaration references this helper
noncomputable def lkeAtomic_exchangeLeft_adj {L : Language}
      (Γ : List (FormulaN L)) (A B : FormulaN L)
      (Δ Λ : List (FormulaN L))
      (h : LKeAtomicProofTree (Sequent.mk (Γ ++ [A, B] ++ Δ) Λ)) :
      LKeAtomicProofTree (Sequent.mk (Γ ++ [B, A] ++ Δ) Λ) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.exchangeLeft Γ A B Δ Λ) t, hcf⟩


  -- ATTACH-BLOCKER: dependency: retained front declaration references this helper
noncomputable def lkeAtomic_exchangeRight_adj {L : Language}
      (Γ Δ : List (FormulaN L)) (A B : FormulaN L)
      (Λ : List (FormulaN L))
      (h : LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [A, B] ++ Λ))) :
      LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [B, A] ++ Λ)) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.exchangeRight Γ Δ A B Λ) t, hcf⟩


  -- Equality transport for LKeAtomicProofTree
  -- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
noncomputable def lkeAtomic_of_eq {L : Language} {s1 s2 : Sequent L}
      (heq : s1 = s2) (h : LKeAtomicProofTree s1) :
      LKeAtomicProofTree s2 := heq ▸ h


  -- Float an element from inside a left list to the front
  -- ATTACH-BLOCKER: termination suffix
noncomputable def lkeAtomic_floatLeftPast {L : Language}
      (pre mid post : List (FormulaN L)) (Λ : List (FormulaN L))
      (A : FormulaN L)
      (h : LKeAtomicProofTree (Sequent.mk (pre ++ mid ++ [A] ++ post) Λ)) :
      LKeAtomicProofTree (Sequent.mk (pre ++ [A] ++ mid ++ post) Λ) := by
    cases mid with
    | nil => exact lkeAtomic_of_eq (by simp) h
    | cons B rest =>
      have ih := fun pre h => lkeAtomic_floatLeftPast pre rest post Λ A h
      have h1 : LKeAtomicProofTree
          (Sequent.mk ((pre ++ [B]) ++ rest ++ [A] ++ post) Λ) :=
        lkeAtomic_of_eq (by simp) h
      have h2 : LKeAtomicProofTree
          (Sequent.mk ((pre ++ [B]) ++ [A] ++ rest ++ post) Λ) :=
        ih (pre ++ [B]) h1
      have h3 : LKeAtomicProofTree
          (Sequent.mk (pre ++ [B, A] ++ (rest ++ post)) Λ) :=
        lkeAtomic_of_eq (by simp) h2
      have h4 := lkeAtomic_exchangeLeft_adj pre B A (rest ++ post) Λ h3
      exact lkeAtomic_of_eq (by simp) h4
  termination_by structural mid


  -- Sink an element from front past a segment
  -- ATTACH-BLOCKER: termination suffix
noncomputable def lkeAtomic_sinkLeftPast {L : Language}
      (pre mid post : List (FormulaN L)) (Λ : List (FormulaN L))
      (A : FormulaN L)
      (h : LKeAtomicProofTree (Sequent.mk (pre ++ [A] ++ mid ++ post) Λ)) :
      LKeAtomicProofTree (Sequent.mk (pre ++ mid ++ [A] ++ post) Λ) := by
    cases mid with
    | nil => exact lkeAtomic_of_eq (by simp) h
    | cons B rest =>
      have ih := fun pre h => lkeAtomic_sinkLeftPast pre rest post Λ A h
      have h1 : LKeAtomicProofTree
          (Sequent.mk (pre ++ [A, B] ++ (rest ++ post)) Λ) :=
        lkeAtomic_of_eq (by simp) h
      have h2 := lkeAtomic_exchangeLeft_adj pre A B (rest ++ post) Λ h1
      have h3 : LKeAtomicProofTree
          (Sequent.mk ((pre ++ [B]) ++ [A] ++ rest ++ post) Λ) :=
        lkeAtomic_of_eq (by simp) h2
      have h4 := ih (pre ++ [B]) h3
      exact lkeAtomic_of_eq (by simp) h4
  termination_by structural mid


  -- Float an element from inside a right list to the end
  -- ATTACH-BLOCKER: termination suffix
noncomputable def lkeAtomic_floatRightPast {L : Language}
      (pre mid post : List (FormulaN L)) (Γ : List (FormulaN L))
      (A : FormulaN L)
      (h : LKeAtomicProofTree (Sequent.mk Γ (pre ++ [A] ++ mid ++ post))) :
      LKeAtomicProofTree (Sequent.mk Γ (pre ++ mid ++ [A] ++ post)) := by
    cases mid with
    | nil => exact lkeAtomic_of_eq (by simp) h
    | cons B rest =>
      have ih := fun pre h => lkeAtomic_floatRightPast pre rest post Γ A h
      have h1 : LKeAtomicProofTree
          (Sequent.mk Γ (pre ++ [A, B] ++ (rest ++ post))) :=
        lkeAtomic_of_eq (by simp) h
      have h2 := lkeAtomic_exchangeRight_adj Γ pre A B (rest ++ post) h1
      have h3 : LKeAtomicProofTree
          (Sequent.mk Γ ((pre ++ [B]) ++ [A] ++ rest ++ post)) :=
        lkeAtomic_of_eq (by simp) h2
      have h4 := ih (pre ++ [B]) h3
      exact lkeAtomic_of_eq (by simp) h4
  termination_by structural mid


  -- Sink an element from the end past a segment
  -- ATTACH-BLOCKER: termination suffix
noncomputable def lkeAtomic_sinkRightPast {L : Language}
      (pre mid post : List (FormulaN L)) (Γ : List (FormulaN L))
      (A : FormulaN L)
      (h : LKeAtomicProofTree (Sequent.mk Γ (pre ++ mid ++ [A] ++ post))) :
      LKeAtomicProofTree (Sequent.mk Γ (pre ++ [A] ++ mid ++ post)) := by
    cases mid with
    | nil => exact lkeAtomic_of_eq (by simp) h
    | cons B rest =>
      have ih := fun pre h => lkeAtomic_sinkRightPast pre rest post Γ A h
      have h1 : LKeAtomicProofTree
          (Sequent.mk Γ ((pre ++ [B]) ++ rest ++ [A] ++ post)) :=
        lkeAtomic_of_eq (by simp) h
      have h2 : LKeAtomicProofTree
          (Sequent.mk Γ ((pre ++ [B]) ++ [A] ++ rest ++ post)) :=
        ih (pre ++ [B]) h1
      have h3 : LKeAtomicProofTree
          (Sequent.mk Γ (pre ++ [B, A] ++ (rest ++ post))) :=
        lkeAtomic_of_eq (by simp) h2
      have h4 := lkeAtomic_exchangeRight_adj Γ pre B A (rest ++ post) h3
      exact lkeAtomic_of_eq (by simp) h4
  termination_by structural mid


  -- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Split at the first occurrence, computing both list segments. -/
  -- Weaken right by prepending before current succedent
  noncomputable def lkeAtomic_shared_axiom {L : Language} [DecidableEq (FormulaN L)]
      (s : Sequent L) (h : isAxiom s) : LKeAtomicProofTree s := by
    let q := convert_g_to_folkCutFree.folkCutFree_shared_axiom s h
    exact ⟨.lk q.val, (lkeAllCutsAtomic_lk q.val).mpr
      (cutFree_implies_allCutsAtomic q.val q.property)⟩


  -- Logical rule helpers
  -- ATTACH-BLOCKER: dependency: retained front declaration references this helper
noncomputable def lkeAtomic_andLeftL_head {L : Language}
      (A B : FormulaN L) (Γ Δ : List (FormulaN L))
      (h : LKeAtomicProofTree (Sequent.mk (A :: Γ) Δ)) :
      LKeAtomicProofTree (Sequent.mk (FormulaN.conj A B :: Γ) Δ) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.andLeftL A B Γ Δ) t, hcf⟩


  -- ATTACH-BLOCKER: dependency: retained front declaration references this helper
noncomputable def lkeAtomic_andLeftR_head {L : Language}
      (A B : FormulaN L) (Γ Δ : List (FormulaN L))
      (h : LKeAtomicProofTree (Sequent.mk (B :: Γ) Δ)) :
      LKeAtomicProofTree (Sequent.mk (FormulaN.conj A B :: Γ) Δ) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.andLeftR A B Γ Δ) t, hcf⟩


  -- ATTACH-BLOCKER: dependency: retained front declaration references this helper
noncomputable def lkeAtomic_andRight_end {L : Language}
      (A B : FormulaN L) (Γ Δ : List (FormulaN L))
      (h1 : LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [A])))
      (h2 : LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [B]))) :
      LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [FormulaN.conj A B])) := by
    obtain ⟨t1, hcf1⟩ := h1
    obtain ⟨t2, hcf2⟩ := h2
    exact ⟨.twoPremise (.andRight A B Γ Δ) t1 t2, ⟨trivial, hcf1, hcf2⟩⟩


  -- ATTACH-BLOCKER: dependency: retained front declaration references this helper
noncomputable def lkeAtomic_orLeft_head {L : Language}
      (A B : FormulaN L) (Γ Δ : List (FormulaN L))
      (h1 : LKeAtomicProofTree (Sequent.mk (A :: Γ) Δ))
      (h2 : LKeAtomicProofTree (Sequent.mk (B :: Γ) Δ)) :
      LKeAtomicProofTree (Sequent.mk (FormulaN.disj A B :: Γ) Δ) := by
    obtain ⟨t1, hcf1⟩ := h1
    obtain ⟨t2, hcf2⟩ := h2
    exact ⟨.twoPremise (.orLeft A B Γ Δ) t1 t2, ⟨trivial, hcf1, hcf2⟩⟩


  -- ATTACH-BLOCKER: dependency: retained front declaration references this helper
noncomputable def lkeAtomic_orRightL_end {L : Language}
      (A B : FormulaN L) (Γ Δ : List (FormulaN L))
      (h : LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [A]))) :
      LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [FormulaN.disj A B])) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.orRightL A B Γ Δ) t, hcf⟩


  -- ATTACH-BLOCKER: dependency: retained front declaration references this helper
noncomputable def lkeAtomic_orRightR_end {L : Language}
      (A B : FormulaN L) (Γ Δ : List (FormulaN L))
      (h : LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [B]))) :
      LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [FormulaN.disj A B])) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.orRightR A B Γ Δ) t, hcf⟩


  -- ATTACH-BLOCKER: dependency: retained front declaration references this helper
noncomputable def lkeAtomic_implLeft_head {L : Language}
      (A B : FormulaN L) (Γ Δ Λ Θ : List (FormulaN L))
      (h1 : LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [A])))
      (h2 : LKeAtomicProofTree (Sequent.mk (B :: Λ) Θ)) :
      LKeAtomicProofTree (Sequent.mk (FormulaN.impl A B :: Γ ++ Λ) (Δ ++ Θ)) := by
    obtain ⟨t1, hcf1⟩ := h1
    obtain ⟨t2, hcf2⟩ := h2
    exact ⟨.twoPremise (.implLeft A B Γ Δ Λ Θ) t1 t2, ⟨trivial, hcf1, hcf2⟩⟩


  -- ATTACH-BLOCKER: dependency: retained front declaration references this helper
noncomputable def lkeAtomic_implRight_head {L : Language}
      (A B : FormulaN L) (Γ Δ : List (FormulaN L))
      (h : LKeAtomicProofTree (Sequent.mk (A :: Γ) (Δ ++ [B]))) :
      LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [FormulaN.impl A B])) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.implRight A B Γ Δ) t, hcf⟩


  -- ATTACH-BLOCKER: dependency: retained front declaration references this helper
noncomputable def lkeAtomic_negLeft_head {L : Language}
      (A : FormulaN L) (Γ Δ : List (FormulaN L))
      (h : LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [A]))) :
      LKeAtomicProofTree (Sequent.mk (FormulaN.neg A :: Γ) Δ) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.negLeft A Γ Δ) t, hcf⟩


  -- ATTACH-BLOCKER: dependency: retained front declaration references this helper
noncomputable def lkeAtomic_negRight_head {L : Language}
      (A : FormulaN L) (Γ Δ : List (FormulaN L))
      (h : LKeAtomicProofTree (Sequent.mk (A :: Γ) Δ)) :
      LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [FormulaN.neg A])) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.negRight A Γ Δ) t, hcf⟩


  -- ATTACH-BLOCKER: dependency: retained front declaration references this helper
noncomputable def lkeAtomic_allLeft_head {L : Language}
      (t_term : Term L) (x : Nat) (A : FormulaN L)
      (Γ Δ : List (FormulaN L))
      (hfree : isFreeForN t_term x A)
      (h : LKeAtomicProofTree (Sequent.mk (formulaSubstN A t_term x :: Γ) Δ)) :
      LKeAtomicProofTree (Sequent.mk (FormulaN.all x A :: Γ) Δ) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.allLeft t_term x A Γ Δ hfree) t, hcf⟩


  -- ATTACH-BLOCKER: dependency: retained front declaration references this helper
noncomputable def lkeAtomic_allRight_end {L : Language}
      (y : Nat) (x : Nat) (A : FormulaN L)
      (Γ Δ : List (FormulaN L))
      (hfresh : ∀ F ∈ (Sequent.mk Γ (Δ ++ [FormulaN.all x A])).antecedent ++
                       (Sequent.mk Γ (Δ ++ [FormulaN.all x A])).succedent,
                  y ∉ formulaFVN F)
      (hfreeFor : isFreeForN (Term.var y) x A)
      (h : LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [formulaSubstN A (Term.var y) x]))) :
      LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [FormulaN.all x A])) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.allRight y x A Γ Δ hfresh hfreeFor) t, hcf⟩


  -- ATTACH-BLOCKER: dependency: retained front declaration references this helper
noncomputable def lkeAtomic_exLeft_head {L : Language}
      (y : Nat) (x : Nat) (A : FormulaN L)
      (Γ Δ : List (FormulaN L))
      (hfresh : ∀ F ∈ (Sequent.mk (FormulaN.ex x A :: Γ) Δ).antecedent ++
                       (Sequent.mk (FormulaN.ex x A :: Γ) Δ).succedent,
                  y ∉ formulaFVN F)
      (hfreeFor : isFreeForN (Term.var y) x A)
      (h : LKeAtomicProofTree (Sequent.mk (formulaSubstN A (Term.var y) x :: Γ) Δ)) :
      LKeAtomicProofTree (Sequent.mk (FormulaN.ex x A :: Γ) Δ) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.exLeft y x A Γ Δ hfresh hfreeFor) t, hcf⟩


  -- ATTACH-BLOCKER: dependency: retained front declaration references this helper
noncomputable def lkeAtomic_exRight_end {L : Language}
      (t_term : Term L) (x : Nat) (A : FormulaN L)
      (Γ Δ : List (FormulaN L))
      (hfree : isFreeForN t_term x A)
      (h : LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [formulaSubstN A t_term x]))) :
      LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [FormulaN.ex x A])) := by
    obtain ⟨t, hcf⟩ := h
    exact ⟨.onePremise (.exRight t_term x A Γ Δ hfree) t, hcf⟩


  -- Contract left list helper
  -- ATTACH-BLOCKER: termination suffix
noncomputable def lkeAtomic_contractLeftList {L : Language}
      (pfx lst : List (FormulaN L)) (Δ : List (FormulaN L))
      (h : LKeAtomicProofTree (Sequent.mk (pfx ++ lst ++ lst) Δ)) :
      LKeAtomicProofTree (Sequent.mk (pfx ++ lst) Δ) := by
    cases lst with
    | nil => exact lkeAtomic_of_eq (by simp) h
    | cons A rest =>
      have ih := fun pfx h => lkeAtomic_contractLeftList pfx rest Δ h
      have step1 := lkeAtomic_floatLeftPast (pfx ++ [A]) rest rest Δ A
        (lkeAtomic_of_eq (by simp) h)
      have step2 := lkeAtomic_floatLeftPast [] (pfx ++ [A]) (rest ++ rest) Δ A
        (lkeAtomic_of_eq (by simp) step1)
      have step3 := lkeAtomic_floatLeftPast [A] pfx (rest ++ rest) Δ A
        (lkeAtomic_of_eq (by simp) step2)
      have step4 := lkeAtomic_contractLeft_head A (pfx ++ rest ++ rest) Δ
        (lkeAtomic_of_eq (by simp) step3)
      have step5 := lkeAtomic_sinkLeftPast [] pfx (rest ++ rest) Δ A
        (lkeAtomic_of_eq (by simp) step4)
      have step6 := ih (pfx ++ [A]) (lkeAtomic_of_eq (by simp) step5)
      exact lkeAtomic_of_eq (by simp) step6
  termination_by structural lst


  -- Contract right list helper
  -- ATTACH-BLOCKER: termination suffix
noncomputable def lkeAtomic_contractRightList {L : Language}
      (pfx lst : List (FormulaN L)) (Γ : List (FormulaN L))
      (h : LKeAtomicProofTree (Sequent.mk Γ (pfx ++ lst ++ lst))) :
      LKeAtomicProofTree (Sequent.mk Γ (pfx ++ lst)) := by
    cases lst with
    | nil => exact lkeAtomic_of_eq (by simp) h
    | cons A rest =>
      have ih := fun pfx h => lkeAtomic_contractRightList pfx rest Γ h
      have step1 := lkeAtomic_sinkRightPast (pfx ++ [A]) rest rest Γ A
        (lkeAtomic_of_eq (by simp) h)
      have step2 := lkeAtomic_floatRightPast (pfx ++ [A]) (rest ++ rest) [] Γ A
        (lkeAtomic_of_eq (by simp) step1)
      have step3 := lkeAtomic_floatRightPast pfx (rest ++ rest ++ [A]) [] Γ A
        (lkeAtomic_of_eq (by simp) step2)
      have step4 := lkeAtomic_contractRight_end A Γ (pfx ++ rest ++ rest)
        (lkeAtomic_of_eq (by simp) step3)
      have step5 := lkeAtomic_sinkRightPast pfx (rest ++ rest) [] Γ A
        (lkeAtomic_of_eq (by simp) step4)
      have step6 := ih (pfx ++ [A]) (lkeAtomic_of_eq (by simp) step5)
      exact lkeAtomic_of_eq (by simp) step6
  termination_by structural lst


  -- k-term ∀:left helper: from the §5.4.8 extended-rule premise shape
  -- (Γ ++ [A[t₁/x],...,A[tₖ/x]] ++ [∀x.A] ++ Δ ⟹ Λ) derive the conclusion
  -- shape (Γ ++ [∀x.A] ++ Δ ⟹ Λ) by induction on ts, peeling one term at a
  -- time: apply the single-term allLeft to tHead, then contract the two
  -- resulting ∀x.A's using the structural helpers.
  -- ATTACH-BLOCKER: termination suffix
noncomputable def lkeAtomic_allLeftN {L : Language}
      (ts : List (Term L)) (Γ Δ Λ : List (FormulaN L))
      (x : Nat) (A : FormulaN L)
      (hne : ts ≠ [])
      (hfree : ∀ t ∈ ts, isFreeForN t x A)
      (h : LKeAtomicProofTree
        (Sequent.mk (Γ ++ ts.map (fun t => formulaSubstN A t x) ++
                     [FormulaN.all x A] ++ Δ) Λ)) :
      LKeAtomicProofTree (Sequent.mk (Γ ++ [FormulaN.all x A] ++ Δ) Λ) := by
    cases ts with
    | nil => exact absurd rfl hne
    | cons tHead rest =>
      have ih := fun {Γ} hne hfree h => lkeAtomic_allLeftN rest Γ Δ Λ x A hne hfree h
      have htFree : isFreeForN tHead x A := hfree tHead List.mem_cons_self
      have s1 : LKeAtomicProofTree
          (Sequent.mk ([formulaSubstN A tHead x] ++ Γ ++
            rest.map (fun t => formulaSubstN A t x) ++
            [FormulaN.all x A] ++ Δ) Λ) :=
        lkeAtomic_of_eq (by simp [List.cons_append])
          (lkeAtomic_floatLeftPast [] Γ
            (rest.map (fun t => formulaSubstN A t x) ++
              [FormulaN.all x A] ++ Δ) Λ (formulaSubstN A tHead x)
            (lkeAtomic_of_eq (by simp) h))
      have s2 : LKeAtomicProofTree
          (Sequent.mk (FormulaN.all x A :: (Γ ++
            rest.map (fun t => formulaSubstN A t x) ++
            [FormulaN.all x A] ++ Δ)) Λ) :=
        lkeAtomic_allLeft_head tHead x A
          (Γ ++ rest.map (fun t => formulaSubstN A t x) ++
            [FormulaN.all x A] ++ Δ) Λ htFree
          (lkeAtomic_of_eq (by simp) s1)
      have s3 : LKeAtomicProofTree
          (Sequent.mk ([FormulaN.all x A] ++ [FormulaN.all x A] ++
            (Γ ++ rest.map (fun t => formulaSubstN A t x)) ++ Δ) Λ) :=
        lkeAtomic_of_eq (by simp)
          (lkeAtomic_floatLeftPast [FormulaN.all x A]
            (Γ ++ rest.map (fun t => formulaSubstN A t x)) Δ Λ
            (FormulaN.all x A)
            (lkeAtomic_of_eq (by simp) s2))
      have s4 : LKeAtomicProofTree
          (Sequent.mk (FormulaN.all x A ::
            (Γ ++ rest.map (fun t => formulaSubstN A t x) ++ Δ)) Λ) :=
        lkeAtomic_contractLeft_head (FormulaN.all x A)
          (Γ ++ rest.map (fun t => formulaSubstN A t x) ++ Δ) Λ
          (lkeAtomic_of_eq (by simp) s3)
      have s5 : LKeAtomicProofTree
          (Sequent.mk (Γ ++ rest.map (fun t => formulaSubstN A t x) ++
            [FormulaN.all x A] ++ Δ) Λ) :=
        lkeAtomic_of_eq (by simp)
          (lkeAtomic_sinkLeftPast []
            (Γ ++ rest.map (fun t => formulaSubstN A t x)) Δ Λ
            (FormulaN.all x A) (lkeAtomic_of_eq (by simp) s4))
      letI : Decidable (rest = []) := decidable_of_iff (rest.length = 0) (by simp)
      by_cases hrest : rest = []
      · subst hrest
        exact lkeAtomic_of_eq (by simp) s5
      · exact ih (Γ := Γ) hrest
          (fun t' ht' => hfree t' (List.mem_cons_of_mem _ ht')) s5
  termination_by structural ts


  -- k-term ∃:right helper: dual of `lkeAtomic_allLeftN` on the succedent.
  -- ATTACH-BLOCKER: termination suffix
noncomputable def lkeAtomic_exRightN {L : Language}
      (ts : List (Term L)) (Γ Δ Λ : List (FormulaN L))
      (x : Nat) (A : FormulaN L)
      (hne : ts ≠ [])
      (hfree : ∀ t ∈ ts, isFreeForN t x A)
      (h : LKeAtomicProofTree
        (Sequent.mk Γ (Δ ++ ts.map (fun t => formulaSubstN A t x) ++
                     [FormulaN.ex x A] ++ Λ))) :
      LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [FormulaN.ex x A] ++ Λ)) := by
    cases ts with
    | nil => exact absurd rfl hne
    | cons tHead rest =>
      have ih := fun {Δ} hne hfree h => lkeAtomic_exRightN rest Γ Δ Λ x A hne hfree h
      have htFree : isFreeForN tHead x A := hfree tHead List.mem_cons_self
      have s1 : LKeAtomicProofTree
          (Sequent.mk Γ ((Δ ++ rest.map (fun t => formulaSubstN A t x) ++
            [FormulaN.ex x A] ++ Λ) ++ [formulaSubstN A tHead x])) :=
        lkeAtomic_of_eq (by simp)
          (lkeAtomic_floatRightPast Δ
            (rest.map (fun t => formulaSubstN A t x) ++
              [FormulaN.ex x A] ++ Λ) [] Γ (formulaSubstN A tHead x)
            (lkeAtomic_of_eq (by simp) h))
      have s2 : LKeAtomicProofTree
          (Sequent.mk Γ ((Δ ++ rest.map (fun t => formulaSubstN A t x) ++
            [FormulaN.ex x A] ++ Λ) ++ [FormulaN.ex x A])) :=
        lkeAtomic_exRight_end tHead x A Γ
          (Δ ++ rest.map (fun t => formulaSubstN A t x) ++
            [FormulaN.ex x A] ++ Λ) htFree s1
      have s3 : LKeAtomicProofTree
          (Sequent.mk Γ
            (Δ ++ rest.map (fun t => formulaSubstN A t x) ++ Λ ++
              [FormulaN.ex x A] ++ [FormulaN.ex x A])) :=
        lkeAtomic_of_eq (by simp)
          (lkeAtomic_floatRightPast
            (Δ ++ rest.map (fun t => formulaSubstN A t x)) Λ
            [FormulaN.ex x A] Γ (FormulaN.ex x A)
            (lkeAtomic_of_eq (by simp) s2))
      have s4 : LKeAtomicProofTree
          (Sequent.mk Γ
            (Δ ++ rest.map (fun t => formulaSubstN A t x) ++ Λ ++
              [FormulaN.ex x A])) :=
        lkeAtomic_contractRight_end (FormulaN.ex x A) Γ
          (Δ ++ rest.map (fun t => formulaSubstN A t x) ++ Λ)
          (lkeAtomic_of_eq (by simp) s3)
      have s5 : LKeAtomicProofTree
          (Sequent.mk Γ
            (Δ ++ rest.map (fun t => formulaSubstN A t x) ++
              [FormulaN.ex x A] ++ Λ)) :=
        lkeAtomic_of_eq (by simp)
          (lkeAtomic_sinkRightPast
            (Δ ++ rest.map (fun t => formulaSubstN A t x)) Λ []
            Γ (FormulaN.ex x A) (lkeAtomic_of_eq (by simp) s4))
      letI : Decidable (rest = []) := decidable_of_iff (rest.length = 0) (by simp)
      by_cases hrest : rest = []
      · subst hrest
        exact lkeAtomic_of_eq (by simp) s5
      · exact ih (Δ := Δ) hrest
          (fun t' ht' => hfree t' (List.mem_cons_of_mem _ ht')) s5
  termination_by structural ts


  -- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Discharge one equality-axiom instance while preserving atomic cuts. -/
  noncomputable def removeAxiom {L : Language} (hL : L.hasEquality = true)
      (A : FormulaN L) (hA : isEqAxiomInstance hL A)
      (Γ Δ : List (FormulaN L))
      (premise : LKeAtomicProofTree (Sequent.mk (Γ ++ [A]) Δ)) :
      LKeAtomicProofTree (Sequent.mk Γ Δ) := by
    -- REPAIR(T6-74): proof pending
    sorry


  -- ATTACH-BLOCKER: termination suffix
/-- Discharge the appended equality axioms, from right to left. -/
  noncomputable def removeAxioms {L : Language} (hL : L.hasEquality = true)
      (axioms : List (FormulaN L))
      (haxioms : ∀ A ∈ axioms, isEqAxiomInstance hL A)
      (Γ Δ : List (FormulaN L))
      (premise : LKeAtomicProofTree (Sequent.mk (Γ ++ axioms) Δ)) :
      LKeAtomicProofTree (Sequent.mk Γ Δ) := by
    cases axioms with
    | nil => exact lkeAtomic_of_eq (by simp) premise
    | cons A rest =>
      let q := removeAxioms hL rest
        (fun B hB => haxioms B (List.mem_cons_of_mem A hB)) (Γ ++ [A]) Δ
        (lkeAtomic_of_eq (by simp [List.append_assoc]) premise)
      exact removeAxiom hL A (haxioms A List.mem_cons_self) Γ Δ q
  termination_by structural axioms


  -- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
noncomputable def convertOne {L : Language} {prem conc : Sequent L}
      (rule : GentzenStep1Ext prem conc) (ih : LKeAtomicProofTree prem) :
      LKeAtomicProofTree conc := by
    cases rule with
    | conjLeft Γ Δ Λ A B =>
      have s1 : LKeAtomicProofTree (Sequent.mk ([] ++ Γ ++ [A] ++ ([B] ++ Δ)) Λ) := lkeAtomic_of_eq (by simp) ih
      have s2 := lkeAtomic_floatLeftPast [] Γ ([B] ++ Δ) Λ A s1
      have s3 : LKeAtomicProofTree (Sequent.mk (A :: (Γ ++ [B] ++ Δ)) Λ) := lkeAtomic_of_eq (by simp) s2
      have s4 := lkeAtomic_andLeftL_head A B (Γ ++ [B] ++ Δ) Λ s3
      have s5 : LKeAtomicProofTree (Sequent.mk (FormulaN.conj A B :: Γ ++ [B] ++ Δ) Λ) := s4
      have s6 := lkeAtomic_floatLeftPast [] (FormulaN.conj A B :: Γ) Δ Λ B s5
      have s7 : LKeAtomicProofTree (Sequent.mk (B :: (FormulaN.conj A B :: Γ ++ Δ)) Λ) :=
        lkeAtomic_of_eq (by simp) s6
      have s8 := lkeAtomic_andLeftR_head A B (FormulaN.conj A B :: Γ ++ Δ) Λ s7
      have s9 : LKeAtomicProofTree (Sequent.mk (FormulaN.conj A B :: FormulaN.conj A B :: Γ ++ Δ) Λ) := s8
      have s10 := lkeAtomic_contractLeft_head (FormulaN.conj A B) (Γ ++ Δ) Λ s9
      have s11 : LKeAtomicProofTree (Sequent.mk (FormulaN.conj A B :: Γ ++ Δ) Λ) := s10
      have s12 := lkeAtomic_sinkLeftPast [] Γ Δ Λ (FormulaN.conj A B) (lkeAtomic_of_eq (by simp) s11)
      exact lkeAtomic_of_eq (by simp) s12
    | disjRight Γ Δ Λ A B =>
      have i1 : LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [A] ++ ([B] ++ Λ) ++ [])) := lkeAtomic_of_eq (by simp) ih
      have s1 : LKeAtomicProofTree (Sequent.mk Γ ((Δ ++ [B] ++ Λ) ++ [A])) := lkeAtomic_of_eq (by simp)
          (lkeAtomic_floatRightPast Δ ([B] ++ Λ) [] Γ A i1)
      have s2 := lkeAtomic_orRightL_end A B Γ (Δ ++ [B] ++ Λ) s1
      have s3 : LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [B] ++ (Λ ++ [FormulaN.disj A B]) ++ [])) :=
        lkeAtomic_of_eq (by simp) s2
      have s4 : LKeAtomicProofTree (Sequent.mk Γ ((Δ ++ Λ ++ [FormulaN.disj A B]) ++ [B])) :=
        lkeAtomic_of_eq (by simp) (lkeAtomic_floatRightPast Δ (Λ ++ [FormulaN.disj A B]) [] Γ B s3)
      have s5 := lkeAtomic_orRightR_end A B Γ (Δ ++ Λ ++ [FormulaN.disj A B]) s4
      have s6 : LKeAtomicProofTree (Sequent.mk Γ ((Δ ++ Λ) ++ [FormulaN.disj A B, FormulaN.disj A B])) :=
        lkeAtomic_of_eq (by simp) s5
      have s7 := lkeAtomic_contractRight_end (FormulaN.disj A B) Γ (Δ ++ Λ) s6
      have s8 : LKeAtomicProofTree (Sequent.mk Γ (Δ ++ Λ ++ [FormulaN.disj A B] ++ [])) :=
        lkeAtomic_of_eq (by simp) s7
      exact lkeAtomic_of_eq (by simp) (lkeAtomic_sinkRightPast Δ Λ [] Γ (FormulaN.disj A B) s8)
    | implRight Γ Δ Λ A B =>
      have i1 : LKeAtomicProofTree (Sequent.mk ([A] ++ Γ) ([] ++ [B] ++ (Δ ++ Λ) ++ [])) :=
        lkeAtomic_of_eq (by simp) ih
      have s1 : LKeAtomicProofTree (Sequent.mk (A :: Γ) ((Δ ++ Λ) ++ [B])) := lkeAtomic_of_eq (by simp)
          (lkeAtomic_floatRightPast [] (Δ ++ Λ) [] ([A] ++ Γ) B i1)
      have s2 := lkeAtomic_implRight_head A B Γ (Δ ++ Λ) s1
      have s3 : LKeAtomicProofTree (Sequent.mk Γ (Δ ++ Λ ++ [FormulaN.impl A B] ++ [])) :=
        lkeAtomic_of_eq (by simp) s2
      exact lkeAtomic_of_eq (by simp) (lkeAtomic_sinkRightPast Δ Λ [] Γ (FormulaN.impl A B) s3)
    | negLeft Γ Δ Λ A =>
      have i1 : LKeAtomicProofTree (Sequent.mk (Γ ++ Δ) (Λ ++ [A])) := lkeAtomic_of_eq (by simp)
          (lkeAtomic_floatRightPast [] Λ [] (Γ ++ Δ) A (lkeAtomic_of_eq (by simp) ih))
      have s1 := lkeAtomic_negLeft_head A (Γ ++ Δ) Λ i1
      have s2 : LKeAtomicProofTree (Sequent.mk (FormulaN.neg A :: (Γ ++ Δ)) Λ) := s1
      exact lkeAtomic_of_eq (by simp) (lkeAtomic_sinkLeftPast [] Γ Δ Λ (FormulaN.neg A)
          (lkeAtomic_of_eq (by simp) s2))
    | negRight Γ Δ Λ A =>
      have i1 : LKeAtomicProofTree (Sequent.mk (A :: Γ) (Δ ++ Λ)) := lkeAtomic_of_eq (by simp) ih
      have s1 := lkeAtomic_negRight_head A Γ (Δ ++ Λ) i1
      have s2 : LKeAtomicProofTree (Sequent.mk Γ (Δ ++ Λ ++ [FormulaN.neg A] ++ [])) :=
        lkeAtomic_of_eq (by simp) s1
      exact lkeAtomic_of_eq (by simp) (lkeAtomic_sinkRightPast Δ Λ [] Γ (FormulaN.neg A) s2)
    | allLeft ts Γ Δ Λ x A hne hfree =>
      exact lkeAtomic_allLeftN ts Γ Δ Λ x A hne hfree ih
    | allRight y_eig Γ Δ Λ x A hfresh hfreeFor =>
      have s0 := lkeAtomic_floatRightPast Δ Λ [] Γ (formulaSubstN A (Term.var y_eig) x)
        (lkeAtomic_of_eq (by simp) ih)
      have s1 : LKeAtomicProofTree (Sequent.mk Γ ((Δ ++ Λ) ++ [formulaSubstN A (Term.var y_eig) x])) :=
        lkeAtomic_of_eq (by simp) s0
      have hfr : ∀ F ∈ (Sequent.mk Γ ((Δ ++ Λ) ++ [FormulaN.all x A])).antecedent ++ (Sequent.mk Γ ((Δ ++ Λ) ++
                [FormulaN.all x A])).succedent, y_eig ∉ formulaFVN F := by
        intro F hF; apply hfresh F
        simp at hF ⊢
        rcases hF with h1 | h2 | h3 | h4 <;> simp_all
      have s2 := lkeAtomic_allRight_end y_eig x A Γ (Δ ++ Λ) hfr hfreeFor s1
      have s3 : LKeAtomicProofTree (Sequent.mk Γ (Δ ++ Λ ++ [FormulaN.all x A] ++ [])) :=
        lkeAtomic_of_eq (by simp) s2
      exact lkeAtomic_of_eq (by simp) (lkeAtomic_sinkRightPast Δ Λ [] Γ (FormulaN.all x A) s3)
    | exLeft y_eig Γ Δ Λ x A hfresh hfreeFor =>
      have s0 := lkeAtomic_floatLeftPast [] Γ Δ Λ (formulaSubstN A (Term.var y_eig) x) ih
      have s1 : LKeAtomicProofTree (Sequent.mk (formulaSubstN A (Term.var y_eig) x :: (Γ ++ Δ)) Λ) :=
        lkeAtomic_of_eq (by simp) s0
      have hfr : ∀ F ∈ (Sequent.mk (FormulaN.ex x A :: Γ ++ Δ) Λ).antecedent ++
                  (Sequent.mk (FormulaN.ex x A :: Γ ++ Δ) Λ).succedent,
                 y_eig ∉ formulaFVN F := by
        intro F hF; apply hfresh F
        simp at hF ⊢
        rcases hF with h1 | h2 | h3 | h4 <;> simp_all
      have s2 := lkeAtomic_exLeft_head y_eig x A (Γ ++ Δ) Λ hfr hfreeFor s1
      have s3 : LKeAtomicProofTree (Sequent.mk (FormulaN.ex x A :: (Γ ++ Δ)) Λ) := s2
      exact lkeAtomic_of_eq (by simp) (lkeAtomic_sinkLeftPast [] Γ Δ Λ (FormulaN.ex x A)
          (lkeAtomic_of_eq (by simp) s3))
    | exRight ts Γ Δ Λ x A hne hfree =>
      exact lkeAtomic_exRightN ts Γ Δ Λ x A hne hfree ih

  -- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
noncomputable def convertTwo {L : Language} {prem₁ prem₂ conc : Sequent L}
      (rule : GentzenStep2Ext prem₁ prem₂ conc)
      (ih1 : LKeAtomicProofTree prem₁) (ih2 : LKeAtomicProofTree prem₂) :
      LKeAtomicProofTree conc := by
    cases rule with
    | conjRight Γ Δ Λ A B =>
      have ia : LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [A] ++ Λ ++ [])) := lkeAtomic_of_eq (by simp) ih1
      have ib : LKeAtomicProofTree (Sequent.mk Γ (Δ ++ [B] ++ Λ ++ [])) := lkeAtomic_of_eq (by simp) ih2
      have sa : LKeAtomicProofTree (Sequent.mk Γ ((Δ ++ Λ) ++ [A])) := lkeAtomic_of_eq (by simp)
          (lkeAtomic_floatRightPast Δ Λ [] Γ A ia)
      have sb : LKeAtomicProofTree (Sequent.mk Γ ((Δ ++ Λ) ++ [B])) := lkeAtomic_of_eq (by simp)
          (lkeAtomic_floatRightPast Δ Λ [] Γ B ib)
      have s1 := lkeAtomic_andRight_end A B Γ (Δ ++ Λ) sa sb
      have s2 : LKeAtomicProofTree (Sequent.mk Γ (Δ ++ Λ ++ [FormulaN.conj A B] ++ [])) :=
        lkeAtomic_of_eq (by simp) s1
      have s3 := lkeAtomic_sinkRightPast Δ Λ [] Γ (FormulaN.conj A B) s2
      exact lkeAtomic_of_eq (by simp) s3
    | disjLeft Γ Δ Λ A B =>
      have sa : LKeAtomicProofTree (Sequent.mk (A :: (Γ ++ Δ)) Λ) := lkeAtomic_of_eq (by simp)
          (lkeAtomic_floatLeftPast [] Γ Δ Λ A ih1)
      have sb : LKeAtomicProofTree (Sequent.mk (B :: (Γ ++ Δ)) Λ) := lkeAtomic_of_eq (by simp)
          (lkeAtomic_floatLeftPast [] Γ Δ Λ B ih2)
      have s1 := lkeAtomic_orLeft_head A B (Γ ++ Δ) Λ sa sb
      have s2 : LKeAtomicProofTree (Sequent.mk (FormulaN.disj A B :: (Γ ++ Δ)) Λ) := s1
      exact lkeAtomic_of_eq (by simp) (lkeAtomic_sinkLeftPast [] Γ Δ Λ (FormulaN.disj A B)
          (lkeAtomic_of_eq (by simp) s2))
    | implLeft Γ Δ Λ A B =>
      have i1 : LKeAtomicProofTree (Sequent.mk (Γ ++ Δ) (Λ ++ [A])) := lkeAtomic_of_eq (by simp)
          (lkeAtomic_floatRightPast [] Λ [] (Γ ++ Δ) A (lkeAtomic_of_eq (by simp) ih1))
      have s1 := lkeAtomic_implLeft_head A B (Γ ++ Δ) Λ (Γ ++ Δ) Λ i1 ih2
      have s2 : LKeAtomicProofTree (Sequent.mk ([FormulaN.impl A B] ++ (Γ ++ Δ) ++ (Γ ++ Δ)) (Λ ++ Λ)) :=
        lkeAtomic_of_eq (by simp) s1
      have s3 := lkeAtomic_contractLeftList [FormulaN.impl A B] (Γ ++ Δ) (Λ ++ Λ) s2
      have s4 : LKeAtomicProofTree (Sequent.mk (FormulaN.impl A B :: (Γ ++ Δ)) ([] ++ Λ ++ Λ)) :=
        lkeAtomic_of_eq (by simp) s3
      have s5 := lkeAtomic_contractRightList [] Λ (FormulaN.impl A B :: Γ ++ Δ) s4
      have s6 : LKeAtomicProofTree (Sequent.mk (FormulaN.impl A B :: (Γ ++ Δ)) Λ) :=
        lkeAtomic_of_eq (by simp) s5
      exact lkeAtomic_of_eq (by simp) (lkeAtomic_sinkLeftPast [] Γ Δ Λ (FormulaN.impl A B)
          (lkeAtomic_of_eq (by simp) s6))

end geqProof_to_lkeNoEssentialCuts

end LCS.CutElim.LKe.Equivalence
end

section
namespace LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality.Completeness
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.CompletenessBridge
open LCS.FirstOrder.Equality

/-- Theorem 6.3.1: Translate a G= proof by structural recursion to an LK_e
proof of the same sequent. G rules use exchange, weakening, contraction and
logical rules; equality rules use equality axioms and atomic cuts. Decidable
symbols support the axiom-leaf construction. The atomic-cut guarantee is
`geqProof_to_lkeNoEssentialCuts_allCutsAtomic`. -/
@[blueprint "chap6__theorem_6_3_1"]
noncomputable def geqProof_to_lkeNoEssentialCuts {L : Language}
    [DecidableEq L.predSymbols] [DecidableEq L.funSymbols] [DecidableEq L.constSymbols]
    {hL : L.hasEquality = true} {s : Sequent L} (t : GEqProofTree hL s) :
    LKeProofTree s :=
  (convert t).val
where
  /-- Recursively translate G= rules, preserving the conclusion and atomic cuts. -/
  convert {L : Language}
      [DecidableEq L.predSymbols] [DecidableEq L.funSymbols] [DecidableEq L.constSymbols]
      {hL : L.hasEquality = true} {s : Sequent L} (t : GEqProofTree hL s) :
      LKeAtomicProofTree s := by
    cases t with
    | base g =>
      let q := convert_g_to_folkCutFree.convert g
      exact ⟨.lk q.val, (lkeAllCutsAtomic_lk q.val).mpr
        (cutFree_implies_allCutsAtomic q.val q.property)⟩
    | axiom_ s hax =>
      letI : DecidableEq (FormulaN L) := FormulaN.decEqOfSymbols
      exact geqProof_to_lkeNoEssentialCuts.lkeAtomic_shared_axiom s hax
    | onePremise rule sub =>
      exact geqProof_to_lkeNoEssentialCuts.convertOne rule (convert sub)
    | twoPremise rule sub1 sub2 =>
      exact geqProof_to_lkeNoEssentialCuts.convertTwo rule (convert sub1) (convert sub2)
    | eqRefl term Γ Δ sub =>
      let q := convert sub
      let r := geqProof_to_lkeNoEssentialCuts.lkeAtomic_floatLeftPast [] Γ [] Δ (FormulaN.eq_ hL term term)
        (geqProof_to_lkeNoEssentialCuts.lkeAtomic_of_eq (by simp) q)
      let u : LKeAtomicProofTree (Sequent.mk ([FormulaN.eq_ hL term term] ++ Γ) Δ) :=
        geqProof_to_lkeNoEssentialCuts.lkeAtomic_of_eq (by simp) r
      exact ⟨geqRefl_to_lkeAtomicCut hL term Γ Δ u.val,
        (geqRefl_to_lkeAtomicCut_allCutsAtomic hL term Γ Δ u.val).mpr u.property⟩
    | eqFuncCong f ss ts Γ Δ sub =>
      let q := convert sub
      exact ⟨geqFuncCong_to_lkeAtomicCuts hL f ss ts Γ Δ q.val,
        geqFuncCong_to_lkeAtomicCuts_allCutsAtomic hL f ss ts Γ Δ q.val q.property⟩
    | eqPredCong P ss ts Γ Δ sub =>
      let q := convert sub
      exact ⟨geqPredCong_to_lkeAtomicCuts hL P ss ts Γ Δ q.val,
        geqPredCong_to_lkeAtomicCuts_allCutsAtomic hL P ss ts Γ Δ q.val q.property⟩
    | eqGeneral axioms _hne haxioms Γ Δ sub =>
      exact geqProof_to_lkeNoEssentialCuts.removeAxioms hL axioms haxioms Γ Δ (convert sub)
  termination_by structural t



/-- Every cut introduced by the G= translation is atomic. -/
@[blueprint "chap6__theorem_6_3_1" (main := true)]
theorem geqProof_to_lkeNoEssentialCuts_allCutsAtomic {L : Language}
    [DecidableEq L.predSymbols] [DecidableEq L.funSymbols] [DecidableEq L.constSymbols]
    {hL : L.hasEquality = true} {s : Sequent L} (t : GEqProofTree hL s) :
    lkeAllCutsAtomic (geqProof_to_lkeNoEssentialCuts t) 

-- Helper: equality axiom sequents are valid
-- retained: used by LCS.CutElim.Interpolation.Equality.Support, LCS.CutElim.LKe.Equivalence.Validity
theorem equalityAxiomValid {L : Language} (hL : L.hasEquality = true)
    (ax : LKeEqualityAxiom L) :
    sequentValid (ax.toSequent hL) := by
-- BEGIN PROOF
  cases ax with
  | refl t =>
    intro M s _
    exact ⟨FormulaN.eq_ hL t t, List.Mem.head _, eqReflValid hL t M s⟩
  | funcCong f ss ts =>
    intro M s hant
    refine ⟨FormulaN.eq_ hL (Term.func f ss) (Term.func f ts), List.Mem.head _, ?_⟩
    simp only [formulaEvalN, termEval]
    congr 1; funext i
    have := hant (FormulaN.eq_ hL (ss i) (ts i)) (by
      simp only [LKeEqualityAxiom.toSequent, List.mem_map]
      exact ⟨i, List.mem_finRange i, rfl⟩)
    simp only [formulaEvalN] at this; exact this
  | predCong P ss ts =>
    intro M s hant
    refine ⟨FormulaN.predN P ts, List.Mem.head _, ?_⟩
    simp only [formulaEvalN]
    have hPss : formulaEvalN M (FormulaN.predN P ss) s :=
      hant (FormulaN.predN P ss) (by
        simp only [LKeEqualityAxiom.toSequent]
        exact List.mem_append_right _ (List.Mem.head _))
    simp only [formulaEvalN] at hPss
    have heqs : ∀ i, termEval M s (ss i) = termEval M s (ts i) := by
      intro i
      have := hant (FormulaN.eq_ hL (ss i) (ts i)) (by
        simp only [LKeEqualityAxiom.toSequent]
        apply List.mem_append_left
        simp only [List.mem_map]
        exact ⟨i, List.mem_finRange i, rfl⟩)
      simp only [formulaEvalN] at this; exact this
    have : (fun i => termEval M s (ts i)) = (fun i => termEval M s (ss i)) :=
      funext (fun i => (heqs i).symm)
    rw [this]; exact hPss
  | eqCong s1 s2 t1 t2 =>
    intro M s hant
    refine ⟨FormulaN.eq_ hL t1 t2, List.Mem.head _, ?_⟩
    have h1 := hant (FormulaN.eq_ hL s1 t1) (by
      simp [LKeEqualityAxiom.toSequent])
    have h2 := hant (FormulaN.eq_ hL s2 t2) (by
      simp [LKeEqualityAxiom.toSequent])
    have h3 := hant (FormulaN.eq_ hL s1 s2) (by
      simp [LKeEqualityAxiom.toSequent])
    simp only [formulaEvalN] at h1 h2 h3 ⊢
    rw [← h1, h3, h2]

-- Helper: LKe soundness -- every LKe tree's conclusion is valid
-- retained: used by LCS.CutElim.Interpolation.Equality.Support, LCS.CutElim.LKe.Equivalence.Validity
theorem lkeProofTree_valid {L : Language} {s : Sequent L}
    (T : LKeProofTree s) :
    sequentValid s := by
-- BEGIN PROOF
  induction T with
  | axiom_ s hAx =>
    exact lemma_6_2_1_axioms_valid s hAx
  | eqAxiom hL ax =>
    exact equalityAxiomValid hL ax
  | onePremise rule _ ih =>
    exact lemma_6_2_1_rules1_preserve_validity rule ih
  | twoPremise rule _ _ ih1 ih2 =>
    exact lemma_6_2_1_rules2_preserve_validity rule ih1 ih2

-- Soundness at the lkeProvable level
-- retained: used by LCS.CutElim.Interpolation.Equality.Axioms, LCS.CutElim.LKe.Equivalence.Validity, LCS.Herbrand.HerbrandTheorem.Part2
theorem lkeProvable_valid {L : Language}
    (s : Sequent L) (h : lkeProvable s) :
    sequentValid s := by
-- BEGIN PROOF
  obtain ⟨T⟩ := h
  exact lkeProofTree_valid T

-- ===================================================================
-- Semantic bridge infrastructure: finite-support term enumeration
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Diagonal successor on pairs of naturals. -/
def validBridgePairStep : Nat × Nat → Nat × Nat
  | (a, 0) => (0, a + 1)
  | (a, b + 1) => (a + 1, b)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Diagonal enumeration of pairs of naturals. -/
def validBridgeUnpair : Nat → Nat × Nat
  | 0 => (0, 0)
  | n + 1 => validBridgePairStep (validBridgeUnpair n)

-- ATTACH-BLOCKER: termination suffix
/-- A right inverse to `validBridgeUnpair`.  The recursion follows the
same diagonal traversal, but its well-founded measure avoids any use of
number-theoretic pairing infrastructure. -/
def validBridgePair : Nat → Nat → Nat
  | 0, 0 => 0
  | 0, b + 1 => validBridgePair b 0 + 1
  | a + 1, b => validBridgePair a (b + 1) + 1
termination_by a b => (a + b, a)
decreasing_by all_goals omega

-- ATTACH-BLOCKER: termination suffix
theorem validBridgeUnpair_pair : ∀ a b,
    validBridgeUnpair (validBridgePair a b) = (a, b)
  | 0, 0 => by simp [validBridgePair, validBridgeUnpair]
  | 0, b + 1 => by
      rw [validBridgePair, validBridgeUnpair]
      simp [validBridgeUnpair_pair b 0, validBridgePairStep]
  | a + 1, b => by
      rw [validBridgePair, validBridgeUnpair]
      simp [validBridgeUnpair_pair a (b + 1), validBridgePairStep]
termination_by a b => (a + b, a)
decreasing_by all_goals omega

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem validBridgePair_injective {a b c d : Nat}
    (h : validBridgePair a b = validBridgePair c d) :
    a = c ∧ b = d := by
  have hu := congrArg validBridgeUnpair h
  simpa [validBridgeUnpair_pair] using hu

-- ATTACH-BLOCKER: mutual
mutual
  /-- Unranked raw terms used only to enumerate the terms of a finite
  support language. -/
  inductive ValidBridgeRawTerm : Type where
    | var : Nat → ValidBridgeRawTerm
    | const : Nat → ValidBridgeRawTerm
    | func : Nat → ValidBridgeRawTerms → ValidBridgeRawTerm

  /-- Strictly-positive lists for `ValidBridgeRawTerm`. -/
  inductive ValidBridgeRawTerms : Type where
    | nil : ValidBridgeRawTerms
    | cons : ValidBridgeRawTerm → ValidBridgeRawTerms → ValidBridgeRawTerms
end

-- ATTACH-BLOCKER: mutual
mutual
  def validBridgeRawTermCode : ValidBridgeRawTerm → Nat
    | .var n => validBridgePair 0 n
    | .const n => validBridgePair 1 n
    | .func n ts =>
        validBridgePair 2 (validBridgePair n (validBridgeRawTermsCode ts))

  def validBridgeRawTermsCode : ValidBridgeRawTerms → Nat
    | .nil => 0
    | .cons t ts =>
        validBridgePair (validBridgeRawTermCode t)
          (validBridgeRawTermsCode ts) + 1
end

-- ATTACH-BLOCKER: mutual
mutual
  theorem validBridgeRawTermCode_injective :
      Function.Injective validBridgeRawTermCode
    | .var a, .var b, h => by
        have hp := validBridgePair_injective h
        exact congrArg ValidBridgeRawTerm.var hp.2
    | .var a, .const b, h => by
        have hp := validBridgePair_injective h
        omega
    | .var a, .func b bs, h => by
        have hp := validBridgePair_injective h
        omega
    | .const a, .var b, h => by
        have hp := validBridgePair_injective h
        omega
    | .const a, .const b, h => by
        have hp := validBridgePair_injective h
        exact congrArg ValidBridgeRawTerm.const hp.2
    | .const a, .func b bs, h => by
        have hp := validBridgePair_injective h
        omega
    | .func a as, .var b, h => by
        have hp := validBridgePair_injective h
        omega
    | .func a as, .const b, h => by
        have hp := validBridgePair_injective h
        omega
    | .func a as, .func b bs, h => by
        have hp := validBridgePair_injective h
        have hp' := validBridgePair_injective hp.2
        have hab : a = b := hp'.1
        have has : as = bs :=
          validBridgeRawTermsCode_injective hp'.2
        cases hab
        cases has
        rfl

  theorem validBridgeRawTermsCode_injective :
      Function.Injective validBridgeRawTermsCode
    | .nil, .nil, _ => rfl
    | .nil, .cons b bs, h => by
        simp only [validBridgeRawTermsCode] at h
        omega
    | .cons a as, .nil, h => by
        simp only [validBridgeRawTermsCode] at h
        omega
    | .cons a as, .cons b bs, h => by
        simp only [validBridgeRawTermsCode] at h
        have hp0 :
            validBridgePair (validBridgeRawTermCode a)
                (validBridgeRawTermsCode as) =
              validBridgePair (validBridgeRawTermCode b)
                (validBridgeRawTermsCode bs) := by
          omega
        have hp := validBridgePair_injective hp0
        have hab : a = b := validBridgeRawTermCode_injective hp.1
        have has : as = bs := validBridgeRawTermsCode_injective hp.2
        cases hab
        cases has
        rfl
end

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
noncomputable def validBridgeRawEnumerate (n : Nat) :
    ValidBridgeRawTerm := by
  classical
  exact if h : ∃ t, validBridgeRawTermCode t = n then
      Classical.choose h
    else
      .var 0

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem validBridgeRawEnumerate_surjective :
    Function.Surjective validBridgeRawEnumerate := by
  intro t
  refine ⟨validBridgeRawTermCode t, ?_⟩
  unfold validBridgeRawEnumerate
  split
  · rename_i h
    apply validBridgeRawTermCode_injective
    exact Classical.choose_spec h
  · rename_i h
    exact (h ⟨t, rfl⟩).elim

-- ATTACH-BLOCKER: unsupported untagged instance
noncomputable instance validBridgeCountableRawTerm :
    Countable ValidBridgeRawTerm where
  enumerate := validBridgeRawEnumerate
  enumerate_surj := validBridgeRawEnumerate_surjective

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
def ValidBridgeRawTerms.ofList :
    List ValidBridgeRawTerm → ValidBridgeRawTerms
  | [] => .nil
  | t :: ts => .cons t (ValidBridgeRawTerms.ofList ts)

-- ATTACH-BLOCKER: mutual
mutual
  /-- Interpret raw terms using two finite symbol lists.  Invalid raw
  symbol indices harmlessly decode as `x₀`; surjectivity only uses valid
  indices. -/
  def validBridgeRawToTerm {L : Language}
      (fs : List L.funSymbols) (cs : List L.constSymbols) :
      ValidBridgeRawTerm → Term L
    | .var n => .var n
    | .const n =>
        match cs[n]? with
        | some c => .const c
        | none => .var 0
    | .func n ts =>
        match fs[n]? with
        | some f =>
            .func f (fun i =>
              (validBridgeRawTermsToList fs cs ts)[i.val]?.getD (.var 0))
        | none => .var 0

  def validBridgeRawTermsToList {L : Language}
      (fs : List L.funSymbols) (cs : List L.constSymbols) :
      ValidBridgeRawTerms → List (Term L)
    | .nil => []
    | .cons t ts =>
        validBridgeRawToTerm fs cs t ::
          validBridgeRawTermsToList fs cs ts
end

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem validBridgeRawTermsToList_ofList {L : Language}
    (fs : List L.funSymbols) (cs : List L.constSymbols)
    (ts : List ValidBridgeRawTerm) :
    validBridgeRawTermsToList fs cs (ValidBridgeRawTerms.ofList ts) =
      ts.map (validBridgeRawToTerm fs cs) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp [ValidBridgeRawTerms.ofList, validBridgeRawTermsToList, ih]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem validBridgeRawToTerm_surjective {L : Language}
    (fs : List L.funSymbols) (cs : List L.constSymbols)
    (hfs : ∀ f : L.funSymbols, f ∈ fs)
    (hcs : ∀ c : L.constSymbols, c ∈ cs) :
    Function.Surjective (validBridgeRawToTerm fs cs) := by
  intro t
  induction t with
  | var n =>
      exact ⟨.var n, rfl⟩
  | const c =>
      obtain ⟨n, hn⟩ := (List.mem_iff_getElem?).mp (hcs c)
      refine ⟨.const n, ?_⟩
      simp [validBridgeRawToTerm, hn]
  | func f ts ih =>
      obtain ⟨n, hn⟩ := (List.mem_iff_getElem?).mp (hfs f)
      let rawArgs : Fin (L.funArity f) → ValidBridgeRawTerm :=
        fun i => Classical.choose (ih i)
      let rawList : List ValidBridgeRawTerm := List.ofFn rawArgs
      refine ⟨.func n (ValidBridgeRawTerms.ofList rawList), ?_⟩
      simp only [validBridgeRawToTerm, hn, rawList,
        validBridgeRawTermsToList_ofList, List.map_ofFn]
      congr 1
      funext i
      have hspec :
          validBridgeRawToTerm fs cs (rawArgs i) = ts i :=
        Classical.choose_spec (ih i)
      have hget :
          (List.ofFn (fun j => validBridgeRawToTerm fs cs (rawArgs j)))[i.val]? =
            some (validBridgeRawToTerm fs cs (rawArgs i)) := by
        apply List.getElem?_eq_some_iff.mpr
        refine ⟨by simp, ?_⟩
        simp
      simp [hget, hspec]

-- ATTACH-BLOCKER: unsupported helper attributes
@[reducible]
noncomputable def validBridgeTermCountable (L : Language)
    (fs : List L.funSymbols) (cs : List L.constSymbols)
    (hfs : ∀ f : L.funSymbols, f ∈ fs)
    (hcs : ∀ c : L.constSymbols, c ∈ cs) :
    Countable (Term L) :=
  Countable.ofSurjection (validBridgeRawToTerm fs cs)
    (validBridgeRawToTerm_surjective fs cs hfs hcs)

-- ===================================================================
-- Semantic bridge infrastructure: finite-support language
-- ===================================================================

-- retained: used by LCS.CutElim.Interpolation.Equality.Support, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeTermFunOccurs {L : Language} (f : L.funSymbols) :
    Term L → Prop
  | .var _ => False
  | .const _ => False
  | .func g ts => f = g ∨ ∃ i, validBridgeTermFunOccurs f (ts i)

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity
def validBridgeTermConstOccurs {L : Language} (c : L.constSymbols) :
    Term L → Prop
  | .var _ => False
  | .const d => c = d
  | .func _ ts => ∃ i, validBridgeTermConstOccurs c (ts i)

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.Interpolation.Equality.Support, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeFormulaFunOccurs {L : Language} (f : L.funSymbols) :
    FormulaN L → Prop
  | .predN _ ts => ∃ i, validBridgeTermFunOccurs f (ts i)
  | .eq_ _ t₁ t₂ =>
      validBridgeTermFunOccurs f t₁ ∨ validBridgeTermFunOccurs f t₂
  | .neg A => validBridgeFormulaFunOccurs f A
  | .conj A B | .disj A B | .impl A B =>
      validBridgeFormulaFunOccurs f A ∨ validBridgeFormulaFunOccurs f B
  | .all _ A | .ex _ A => validBridgeFormulaFunOccurs f A

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeFormulaConstOccurs {L : Language} (c : L.constSymbols) :
    FormulaN L → Prop
  | .predN _ ts => ∃ i, validBridgeTermConstOccurs c (ts i)
  | .eq_ _ t₁ t₂ =>
      validBridgeTermConstOccurs c t₁ ∨ validBridgeTermConstOccurs c t₂
  | .neg A => validBridgeFormulaConstOccurs c A
  | .conj A B | .disj A B | .impl A B =>
      validBridgeFormulaConstOccurs c A ∨ validBridgeFormulaConstOccurs c B
  | .all _ A | .ex _ A => validBridgeFormulaConstOccurs c A

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.Interpolation.Equality.Support, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeFormulaPredOccurs {L : Language} (P : L.predSymbols) :
    FormulaN L → Prop
  | .predN Q _ => P = Q
  | .eq_ _ _ _ => False
  | .neg A => validBridgeFormulaPredOccurs P A
  | .conj A B | .disj A B | .impl A B =>
      validBridgeFormulaPredOccurs P A ∨ validBridgeFormulaPredOccurs P B
  | .all _ A | .ex _ A => validBridgeFormulaPredOccurs P A

-- retained: used by LCS.CutElim.Interpolation.Equality.Support
def validBridgeTermFunSymbols {L : Language} : Term L → List L.funSymbols
  | .var _ => []
  | .const _ => []
  | .func f ts =>
      f :: (List.ofFn (fun i => validBridgeTermFunSymbols (ts i))).flatten

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeTermConstSymbols {L : Language} :
    Term L → List L.constSymbols
  | .var _ => []
  | .const c => [c]
  | .func _ ts =>
      (List.ofFn (fun i => validBridgeTermConstSymbols (ts i))).flatten

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.Interpolation.Equality.Support, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeFormulaFunSymbols {L : Language} :
    FormulaN L → List L.funSymbols
  | .predN _ ts =>
      (List.ofFn (fun i => validBridgeTermFunSymbols (ts i))).flatten
  | .eq_ _ t₁ t₂ =>
      validBridgeTermFunSymbols t₁ ++ validBridgeTermFunSymbols t₂
  | .neg A => validBridgeFormulaFunSymbols A
  | .conj A B | .disj A B | .impl A B =>
      validBridgeFormulaFunSymbols A ++ validBridgeFormulaFunSymbols B
  | .all _ A | .ex _ A => validBridgeFormulaFunSymbols A

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeFormulaConstSymbols {L : Language} :
    FormulaN L → List L.constSymbols
  | .predN _ ts =>
      (List.ofFn (fun i => validBridgeTermConstSymbols (ts i))).flatten
  | .eq_ _ t₁ t₂ =>
      validBridgeTermConstSymbols t₁ ++ validBridgeTermConstSymbols t₂
  | .neg A => validBridgeFormulaConstSymbols A
  | .conj A B | .disj A B | .impl A B =>
      validBridgeFormulaConstSymbols A ++ validBridgeFormulaConstSymbols B
  | .all _ A | .ex _ A => validBridgeFormulaConstSymbols A

-- retained: used by LCS.CutElim.Interpolation.Equality.Support, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeFormulaPredSymbols {L : Language} :
    FormulaN L → List L.predSymbols
  | .predN P _ => [P]
  | .eq_ _ _ _ => []
  | .neg A => validBridgeFormulaPredSymbols A
  | .conj A B | .disj A B | .impl A B =>
      validBridgeFormulaPredSymbols A ++ validBridgeFormulaPredSymbols B
  | .all _ A | .ex _ A => validBridgeFormulaPredSymbols A

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity
theorem validBridge_mem_flatten_ofFn {α : Type} {n : Nat}
    (xs : Fin n → List α) (i : Fin n) {a : α} (ha : a ∈ xs i) :
    a ∈ (List.ofFn xs).flatten := by
  apply List.mem_flatten.mpr
  exact ⟨xs i, by simp, ha⟩

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity
theorem validBridgeTermFunOccurs_mem {L : Language}
    {f : L.funSymbols} {t : Term L}
    (h : validBridgeTermFunOccurs f t) :
    f ∈ validBridgeTermFunSymbols t := by
  induction t with
  | var _ => exact h.elim
  | const _ => exact h.elim
  | func g ts ih =>
      simp only [validBridgeTermFunOccurs] at h
      simp only [validBridgeTermFunSymbols, List.mem_cons]
      rcases h with rfl | ⟨i, hi⟩
      · exact Or.inl rfl
      · exact Or.inr (validBridge_mem_flatten_ofFn
          (fun j => validBridgeTermFunSymbols (ts j)) i (ih i hi))

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity
theorem validBridgeTermConstOccurs_mem {L : Language}
    {c : L.constSymbols} {t : Term L}
    (h : validBridgeTermConstOccurs c t) :
    c ∈ validBridgeTermConstSymbols t := by
  induction t with
  | var _ => exact h.elim
  | const d =>
      simpa [validBridgeTermConstOccurs, validBridgeTermConstSymbols] using h
  | func f ts ih =>
      simp only [validBridgeTermConstOccurs] at h
      obtain ⟨i, hi⟩ := h
      exact validBridge_mem_flatten_ofFn
        (fun j => validBridgeTermConstSymbols (ts j)) i (ih i hi)

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity
theorem validBridgeFormulaFunOccurs_mem {L : Language}
    {f : L.funSymbols} {A : FormulaN L}
    (h : validBridgeFormulaFunOccurs f A) :
    f ∈ validBridgeFormulaFunSymbols A := by
  induction A with
  | predN P ts =>
      obtain ⟨i, hi⟩ := h
      exact validBridge_mem_flatten_ofFn
        (fun j => validBridgeTermFunSymbols (ts j)) i
        (validBridgeTermFunOccurs_mem hi)
  | eq_ hL t₁ t₂ =>
      rcases h with h | h
      · exact List.mem_append_left _ (validBridgeTermFunOccurs_mem h)
      · exact List.mem_append_right _ (validBridgeTermFunOccurs_mem h)
  | neg A ih => exact ih h
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      rcases h with h | h
      · exact List.mem_append_left _ (ihA h)
      · exact List.mem_append_right _ (ihB h)
  | all x A ih | ex x A ih => exact ih h

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity
theorem validBridgeFormulaConstOccurs_mem {L : Language}
    {c : L.constSymbols} {A : FormulaN L}
    (h : validBridgeFormulaConstOccurs c A) :
    c ∈ validBridgeFormulaConstSymbols A := by
  induction A with
  | predN P ts =>
      obtain ⟨i, hi⟩ := h
      exact validBridge_mem_flatten_ofFn
        (fun j => validBridgeTermConstSymbols (ts j)) i
        (validBridgeTermConstOccurs_mem hi)
  | eq_ hL t₁ t₂ =>
      rcases h with h | h
      · exact List.mem_append_left _ (validBridgeTermConstOccurs_mem h)
      · exact List.mem_append_right _ (validBridgeTermConstOccurs_mem h)
  | neg A ih => exact ih h
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      rcases h with h | h
      · exact List.mem_append_left _ (ihA h)
      · exact List.mem_append_right _ (ihB h)
  | all x A ih | ex x A ih => exact ih h

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity
theorem validBridgeFormulaPredOccurs_mem {L : Language}
    {P : L.predSymbols} {A : FormulaN L}
    (h : validBridgeFormulaPredOccurs P A) :
    P ∈ validBridgeFormulaPredSymbols A := by
  induction A with
  | predN Q ts =>
      simpa [validBridgeFormulaPredOccurs, validBridgeFormulaPredSymbols] using h
  | eq_ hL t₁ t₂ => exact h.elim
  | neg A ih => exact ih h
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      rcases h with h | h
      · exact List.mem_append_left _ (ihA h)
      · exact List.mem_append_right _ (ihB h)
  | all x A ih | ex x A ih => exact ih h

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.Interpolation.Equality.Support, LCS.CutElim.LKe.Equivalence.Validity
/-- The sublanguage consisting exactly of the symbols occurring in a
single formula. -/
def ValidBridgeSupportLanguage {L : Language} (F : FormulaN L) :
    Language where
  funSymbols := {f // f ∈ validBridgeFormulaFunSymbols F}
  funArity := fun f => L.funArity f.1
  constSymbols := {c // c ∈ validBridgeFormulaConstSymbols F}
  predSymbols := {P // P ∈ validBridgeFormulaPredSymbols F}
  predArity := fun P => L.predArity P.1
  hasEquality := L.hasEquality

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity
def validBridgeRestrictTerm {L : Language} (F : FormulaN L) :
    (t : Term L) →
    (∀ f, validBridgeTermFunOccurs f t →
      validBridgeFormulaFunOccurs f F) →
    (∀ c, validBridgeTermConstOccurs c t →
      validBridgeFormulaConstOccurs c F) →
    Term (ValidBridgeSupportLanguage F)
  | .var n, _, _ => .var n
  | .const c, _, hc =>
      .const ⟨c, validBridgeFormulaConstOccurs_mem
        (hc c (by simp [validBridgeTermConstOccurs]))⟩
  | .func f ts, hf, hc =>
      .func
        ⟨f, validBridgeFormulaFunOccurs_mem
          (hf f (Or.inl rfl))⟩
        (fun i => validBridgeRestrictTerm F (ts i)
          (fun g hg => hf g (Or.inr ⟨i, hg⟩))
          (fun c hc' => hc c ⟨i, hc'⟩))

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeRestrictFormula {L : Language} (F : FormulaN L) :
    (A : FormulaN L) →
    (∀ f, validBridgeFormulaFunOccurs f A →
      validBridgeFormulaFunOccurs f F) →
    (∀ c, validBridgeFormulaConstOccurs c A →
      validBridgeFormulaConstOccurs c F) →
    (∀ P, validBridgeFormulaPredOccurs P A →
      validBridgeFormulaPredOccurs P F) →
    FormulaN (ValidBridgeSupportLanguage F)
  | .predN P ts, hf, hc, hp =>
      .predN
        ⟨P, validBridgeFormulaPredOccurs_mem
          (hp P (by simp [validBridgeFormulaPredOccurs]))⟩
        (fun i => validBridgeRestrictTerm F (ts i)
          (fun f h => hf f ⟨i, h⟩)
          (fun c h => hc c ⟨i, h⟩))
  | .eq_ hL t₁ t₂, hf, hc, _ =>
      .eq_ hL
        (validBridgeRestrictTerm F t₁
          (fun f h => hf f (Or.inl h))
          (fun c h => hc c (Or.inl h)))
        (validBridgeRestrictTerm F t₂
          (fun f h => hf f (Or.inr h))
          (fun c h => hc c (Or.inr h)))
  | .neg A, hf, hc, hp =>
      .neg (validBridgeRestrictFormula F A hf hc hp)
  | .conj A B, hf, hc, hp =>
      .conj
        (validBridgeRestrictFormula F A
          (fun f h => hf f (Or.inl h))
          (fun c h => hc c (Or.inl h))
          (fun P h => hp P (Or.inl h)))
        (validBridgeRestrictFormula F B
          (fun f h => hf f (Or.inr h))
          (fun c h => hc c (Or.inr h))
          (fun P h => hp P (Or.inr h)))
  | .disj A B, hf, hc, hp =>
      .disj
        (validBridgeRestrictFormula F A
          (fun f h => hf f (Or.inl h))
          (fun c h => hc c (Or.inl h))
          (fun P h => hp P (Or.inl h)))
        (validBridgeRestrictFormula F B
          (fun f h => hf f (Or.inr h))
          (fun c h => hc c (Or.inr h))
          (fun P h => hp P (Or.inr h)))
  | .impl A B, hf, hc, hp =>
      .impl
        (validBridgeRestrictFormula F A
          (fun f h => hf f (Or.inl h))
          (fun c h => hc c (Or.inl h))
          (fun P h => hp P (Or.inl h)))
        (validBridgeRestrictFormula F B
          (fun f h => hf f (Or.inr h))
          (fun c h => hc c (Or.inr h))
          (fun P h => hp P (Or.inr h)))
  | .all x A, hf, hc, hp =>
      .all x (validBridgeRestrictFormula F A hf hc hp)
  | .ex x A, hf, hc, hp =>
      .ex x (validBridgeRestrictFormula F A hf hc hp)

-- retained: used by LCS.CutElim.Interpolation.Equality.Support, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeRestrictSelf {L : Language} (F : FormulaN L) :
    FormulaN (ValidBridgeSupportLanguage F) :=
  validBridgeRestrictFormula F F
    (fun _ h => h) (fun _ h => h) (fun _ h => h)

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity
def validBridgeLiftTerm {L : Language} (F : FormulaN L) :
    Term (ValidBridgeSupportLanguage F) → Term L
  | .var n => .var n
  | .const c => .const c.1
  | .func f ts => .func f.1 (fun i => validBridgeLiftTerm F (ts i))

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.Interpolation.Equality.Support, LCS.CutElim.LKe.Equivalence.Validity
def validBridgeLiftFormula {L : Language} (F : FormulaN L) :
    FormulaN (ValidBridgeSupportLanguage F) → FormulaN L
  | .predN P ts =>
      .predN P.1 (fun i => validBridgeLiftTerm F (ts i))
  | .eq_ hL t₁ t₂ =>
      .eq_ hL (validBridgeLiftTerm F t₁) (validBridgeLiftTerm F t₂)
  | .neg A => .neg (validBridgeLiftFormula F A)
  | .conj A B =>
      .conj (validBridgeLiftFormula F A) (validBridgeLiftFormula F B)
  | .disj A B =>
      .disj (validBridgeLiftFormula F A) (validBridgeLiftFormula F B)
  | .impl A B =>
      .impl (validBridgeLiftFormula F A) (validBridgeLiftFormula F B)
  | .all x A => .all x (validBridgeLiftFormula F A)
  | .ex x A => .ex x (validBridgeLiftFormula F A)

end LCS.CutElim.LKe.Equivalence
end

