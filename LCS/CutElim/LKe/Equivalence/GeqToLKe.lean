import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.CutElim.CompletenessBridge
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.LKe.Equivalence.AtomicCuts
import LCS.CutElim.LKe.Equivalence.EqualityRules
import Attach
import LCS.CutElim.LKe.Equivalence.GeqToLKe.ProofsStamp

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

end LCS.CutElim.LKe.Equivalence
end
