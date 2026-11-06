import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.CutElim.CompletenessBridge
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Semantics.Subformulae
import Attach
import LCS.CutElim.LKe.Equivalence.AtomicLeaves.ProofsStamp

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

/-- Lemma 6.3.1 (required def): A formula is quantified if it is of the form
FormulaN.all x B or FormulaN.ex x B for some variable x and formula B. -/
@[blueprint "chap6__lemma_6_3_1"]
def isQuantified {L : Language} : FormulaN L → Prop
  | .all _ _ => True
  | .ex _ _ => True
  | _ => False

-- ===================================================================
-- Lemma 6.3.1 (required def): isAtomicOrQuantified
-- ===================================================================
/-- Lemma 6.3.1 (required def): A formula is atomic-or-quantified if it is
atomic (via FormulaN.isAtomic) or is of the form FormulaN.all x B or
FormulaN.ex x B. -/
@[blueprint "chap6__lemma_6_3_1"]
def isAtomicOrQuantified {L : Language}
    (A : FormulaN L) : Prop :=
  A.isAtomic ∨ isQuantified A

-- ===================================================================
-- Lemma 6.3.1 (required def): formulaWeight
-- ===================================================================
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 6.3.1 (required def): The number of logical connectives
(conj, disj, neg, impl) in a non-atomic, non-quantified formula.
Returns 0 for atomic formulae and for quantified formulae
(all x B, ex x B). For conj A B: 1 + weight A + weight B. Similarly
for disj, impl. For neg A: 1 + weight A. -/
def formulaWeight {L : Language} : FormulaN L → Nat
  | .predN _ _ => 0
  | .eq_ _ _ _ => 0
  | .conj A B => 1 + formulaWeight A + formulaWeight B
  | .disj A B => 1 + formulaWeight A + formulaWeight B
  | .impl A B => 1 + formulaWeight A + formulaWeight B
  | .neg A => 1 + formulaWeight A
  | .all _ _ => 0
  | .ex _ _ => 0

-- ===================================================================
-- Lemma 6.3.1 (required def): sequentWeight
-- ===================================================================
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 6.3.1 (required def): The sum of formulaWeight over all
formulae in both the antecedent and succedent of the sequent. -/
def sequentWeight {L : Language} (s : Sequent L) : Nat :=
  (s.antecedent.map formulaWeight).foldl (· + ·) 0 +
  (s.succedent.map formulaWeight).foldl (· + ·) 0

-- ===================================================================
-- Lemma 6.3.1 (required def): gProofTreeLeafSequents
-- ===================================================================
/-- Lemma 6.3.1 (required def): Returns the list of leaf (axiom)
sequents of a G proof tree under the §5.4.8 standing assumption.
With indexed trees, axiom leaves carry their sequent as a type index,
one-premise rules have one subtree, and two-premise rules have two. -/
@[blueprint "chap6__lemma_6_3_1"]
def gProofTreeLeafSequents {L : Language} :
    {s : Sequent L} → GProofTreeExt s → List (Sequent L)
  | _, .axiom_ s _ => [s]
  | _, .onePremise _ t => gProofTreeLeafSequents t
  | _, .twoPremise _ t1 t2 =>
    gProofTreeLeafSequents t1 ++ gProofTreeLeafSequents t2

-- ===================================================================
-- Lemma 6.3.1 (required def): geqLeafSequents
-- ===================================================================
/-- Lemma 6.3.1 (required def): Returns the list of leaf (axiom)
sequents of a G= proof tree by recursive traversal: for axioms
returns the singleton, for rule applications collects from all
subtrees. -/
@[blueprint "chap6__lemma_6_3_1"]
def geqLeafSequents {L : Language} {hL : L.hasEquality = true} :
    {s : Sequent L} → GEqProofTree hL s → List (Sequent L)
  | _, .base g => gProofTreeLeafSequents g
  | _, .axiom_ s _ => [s]
  | _, .onePremise _ sub => geqLeafSequents sub
  | _, .twoPremise _ sub1 sub2 =>
    geqLeafSequents sub1 ++ geqLeafSequents sub2
  | _, .eqRefl _ _ _ sub => geqLeafSequents sub
  | _, .eqFuncCong _ _ _ _ _ sub => geqLeafSequents sub
  | _, .eqPredCong _ _ _ _ _ sub => geqLeafSequents sub
  | _, .eqGeneral _ _ _ _ _ sub => geqLeafSequents sub

-- ===================================================================
-- Lemma 6.3.1 (required def): geqTreeWeight
-- ===================================================================
-- ===================================================================
-- Lemma 6.3.1 (required def): seqAllAtomicOrQuantified
-- ===================================================================
/-- Lemma 6.3.1 (required def): All formulae in the antecedent and
succedent are atomic or quantified (via isAtomicOrQuantified). -/
@[blueprint "chap6__lemma_6_3_1"]
def seqAllAtomicOrQuantified {L : Language}
    (s : Sequent L) : Prop :=
  (∀ A ∈ s.antecedent, isAtomicOrQuantified A) ∧
  (∀ A ∈ s.succedent, isAtomicOrQuantified A)

-- ===================================================================
-- Lemma 6.3.1 (helper): formulaWeight 0 implies atomic or quantified
-- ===================================================================
-- ===================================================================
-- Lemma 6.3.1 (helpers): foldl arithmetic
-- ===================================================================
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem perm_foldl_add_acc {xs : List Nat} {n : Nat} :
    xs.foldl (· + ·) n = n + xs.foldl (· + ·) 0 := by
  induction xs generalizing n with
  | nil => simp [List.foldl]
  | cons a as ih => simp [List.foldl]; rw [ih (n := n + a), ih (n := a)]; omega

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem perm_mem_split {α : Type} (A : α) (xs : List α) (h : A ∈ xs) :
    ∃ L₁ L₂ : List α, xs = L₁ ++ [A] ++ L₂ := by
-- BEGIN PROOF
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    cases h with
    | head => exact ⟨[], xs, by simp⟩
    | tail _ h' =>
      obtain ⟨L₁, L₂, hL⟩ := ih h'
      exact ⟨x :: L₁, L₂, by simp [hL]⟩

-- Recursive sum for simpler omega proofs
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
def perm_listWeightSum {L : Language} : List (FormulaN L) → Nat
  | [] => 0
  | A :: rest => formulaWeight A + perm_listWeightSum rest

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem perm_listWeightSum_eq {L : Language} (xs : List (FormulaN L)) :
    perm_listWeightSum xs = (xs.map formulaWeight).foldl (· + ·) 0 := by
-- BEGIN PROOF
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp [perm_listWeightSum, List.map]; rw [ih]
    rw [show (List.map formulaWeight as).foldl (· + ·) (formulaWeight a) =
      formulaWeight a + (List.map formulaWeight as).foldl (· + ·) 0 from perm_foldl_add_acc]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem perm_listWeightSum_append {L : Language}
    (xs ys : List (FormulaN L)) :
    perm_listWeightSum (xs ++ ys) =
    perm_listWeightSum xs + perm_listWeightSum ys := by
-- BEGIN PROOF
  induction xs with
  | nil => simp [perm_listWeightSum]
  | cons a as ih => simp [perm_listWeightSum, ih]; omega

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem perm_seqWeight_eq {L : Language}
    (ante succ : List (FormulaN L)) :
    sequentWeight (Sequent.mk ante succ) =
    perm_listWeightSum ante + perm_listWeightSum succ := by
-- BEGIN PROOF
  simp [sequentWeight, perm_listWeightSum_eq]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem perm_map_foldl_split {L : Language} (Γ₁ Γ₂ : List (FormulaN L))
    (A : FormulaN L) :
    ((Γ₁ ++ [A] ++ Γ₂).map formulaWeight).foldl (· + ·) 0 =
    (Γ₁.map formulaWeight).foldl (· + ·) 0 + formulaWeight A +
    (Γ₂.map formulaWeight).foldl (· + ·) 0 := by
-- BEGIN PROOF
  rw [show Γ₁ ++ [A] ++ Γ₂ = Γ₁ ++ ([A] ++ Γ₂) from by simp]
  rw [List.map_append, List.foldl_append,
      show List.map formulaWeight ([A] ++ Γ₂) =
        formulaWeight A :: Γ₂.map formulaWeight from by simp]
  simp only [List.foldl]; rw [perm_foldl_add_acc]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem perm_map_foldl_split2 {L : Language} (Γ₁ Γ₂ : List (FormulaN L))
    (A B : FormulaN L) :
    ((Γ₁ ++ [A, B] ++ Γ₂).map formulaWeight).foldl (· + ·) 0 =
    (Γ₁.map formulaWeight).foldl (· + ·) 0 + formulaWeight A +
    formulaWeight B +
    (Γ₂.map formulaWeight).foldl (· + ·) 0 := by
  rw [show Γ₁ ++ [A, B] ++ Γ₂ = Γ₁ ++ ([A, B] ++ Γ₂) from by simp]
  rw [List.map_append, List.foldl_append,
      show List.map formulaWeight ([A, B] ++ Γ₂) =
        formulaWeight A :: formulaWeight B :: Γ₂.map formulaWeight
        from by simp]
  simp only [List.foldl]
  rw [perm_foldl_add_acc (n := _ + _), perm_foldl_add_acc]

-- ===================================================================
-- Lemma 6.3.1 (helpers): isAxiom preservation for both-sides leaves
-- ===================================================================
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem perm_conj_both_leaf1_ax {L : Language}
    (A B : FormulaN L) (Γ₁ Γ₂ Δ₁ Δ₂ : List (FormulaN L)) :
    isAxiom (Sequent.mk (Γ₁ ++ [A, B] ++ Γ₂) (Δ₁ ++ [A] ++ Δ₂)) :=
-- BEGIN PROOF
  ⟨A, by simp [List.mem_append], by simp [List.mem_append]⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem perm_conj_both_leaf2_ax {L : Language}
    (A B : FormulaN L) (Γ₁ Γ₂ Δ₁ Δ₂ : List (FormulaN L)) :
    isAxiom (Sequent.mk (Γ₁ ++ [A, B] ++ Γ₂) (Δ₁ ++ [B] ++ Δ₂)) :=
-- BEGIN PROOF
  ⟨B, by simp [List.mem_append], by simp [List.mem_append]⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem perm_disj_both_leaf1_ax {L : Language}
    (A B : FormulaN L) (Γ₁ Γ₂ Δ₁ Δ₂ : List (FormulaN L)) :
    isAxiom (Sequent.mk (Γ₁ ++ [A] ++ Γ₂) (Δ₁ ++ [A, B] ++ Δ₂)) :=
-- BEGIN PROOF
  ⟨A, by simp [List.mem_append], by simp [List.mem_append]⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem perm_disj_both_leaf2_ax {L : Language}
    (A B : FormulaN L) (Γ₁ Γ₂ Δ₁ Δ₂ : List (FormulaN L)) :
    isAxiom (Sequent.mk (Γ₁ ++ [B] ++ Γ₂) (Δ₁ ++ [A, B] ++ Δ₂)) :=
-- BEGIN PROOF
  ⟨B, by simp [List.mem_append], by simp [List.mem_append]⟩

-- ===================================================================
-- Lemma 6.3.1 (helpers): weight decrease for both-sides decomp
-- ===================================================================
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem perm_conj_both_weight_leaf1 {L : Language}
    (A B : FormulaN L) (Γ₁ Γ₂ Δ₁ Δ₂ : List (FormulaN L)) :
    sequentWeight (Sequent.mk (Γ₁ ++ [A, B] ++ Γ₂) (Δ₁ ++ [A] ++ Δ₂)) <
    sequentWeight (Sequent.mk (Γ₁ ++ [FormulaN.conj A B] ++ Γ₂)
      (Δ₁ ++ [FormulaN.conj A B] ++ Δ₂)) := by
-- BEGIN PROOF
  simp only [sequentWeight]
  rw [perm_map_foldl_split Γ₁ Γ₂ (FormulaN.conj A B)]
  rw [perm_map_foldl_split Δ₁ Δ₂ (FormulaN.conj A B)]
  rw [perm_map_foldl_split2 Γ₁ Γ₂ A B, perm_map_foldl_split Δ₁ Δ₂ A]
  simp [formulaWeight]; omega

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem perm_conj_both_weight_leaf2 {L : Language}
    (A B : FormulaN L) (Γ₁ Γ₂ Δ₁ Δ₂ : List (FormulaN L)) :
    sequentWeight (Sequent.mk (Γ₁ ++ [A, B] ++ Γ₂) (Δ₁ ++ [B] ++ Δ₂)) <
    sequentWeight (Sequent.mk (Γ₁ ++ [FormulaN.conj A B] ++ Γ₂)
      (Δ₁ ++ [FormulaN.conj A B] ++ Δ₂)) := by
-- BEGIN PROOF
  simp only [sequentWeight]
  rw [perm_map_foldl_split Γ₁ Γ₂ (FormulaN.conj A B),
      perm_map_foldl_split Δ₁ Δ₂ (FormulaN.conj A B),
      perm_map_foldl_split2 Γ₁ Γ₂ A B, perm_map_foldl_split Δ₁ Δ₂ B]
  simp [formulaWeight]; omega

section
-- ATTACH-BLOCKER: variable
variable
    (L : Language) (n : Nat) (ihS : ∀ (s' : Sequent L), sequentWeight s' < n → isAxiom s' → ∃ (g :
      GProofTreeExt s'), ∀ (l : Sequent L), l ∈ gProofTreeLeafSequents g → seqAllAtomicOrQuantified l)
-- ATTACH-BLOCKER: unknown command Lean.Parser.Command.include
include ihS

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem axiom_atomic_left_neg
    (Δ : List (FormulaN L)) (P : FormulaN L) (Γ₁ Γ₂ : List (FormulaN L)) (hPctx : P ∈ Γ₁ ++ Γ₂) (A : FormulaN
      L) (hweight : sequentWeight (Sequent.mk (Γ₁ ++ [A.neg] ++ Γ₂) (Δ)) = n) (hPΔ : P ∈ (Δ))
    : ∃ (g : GProofTreeExt (Sequent.mk (Γ₁ ++ [A.neg] ++ Γ₂) (Δ))), ∀ (s' : Sequent L), s' ∈
      gProofTreeLeafSequents g → seqAllAtomicOrQuantified s' := by
  have hpax : isAxiom (Sequent.mk (Γ₁ ++ Γ₂) ([A] ++ Δ)) := ⟨P, hPctx, List.mem_append_right [A] hPΔ⟩
  have hlt : sequentWeight (Sequent.mk (Γ₁ ++ Γ₂) ([A] ++ Δ)) < n := by
    rw [← hweight]
    simp [perm_seqWeight_eq, perm_listWeightSum_append, perm_listWeightSum, formulaWeight]
    omega
  obtain ⟨g, hg⟩ := ihS _ hlt hpax
  refine ⟨.onePremise (.negLeft Γ₁ Γ₂ Δ A) g, ?_⟩
  simpa [gProofTreeLeafSequents] using hg

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem axiom_atomic_left_conj
    (Δ : List (FormulaN L)) (P : FormulaN L) (mem_insert_middle : ∀ (X : FormulaN L) (xs mid ys : List
      (FormulaN L)), X ∈ xs ++ ys → X ∈ xs ++ mid ++ ys) (Γ₁ Γ₂ : List (FormulaN L)) (hPctx : P ∈ Γ₁ ++ Γ₂) (A
      B : FormulaN L) (hweight : sequentWeight (Sequent.mk (Γ₁ ++ [A.conj B] ++ Γ₂) (Δ)) = n) (hPΔ : P ∈ (Δ))
    : ∃ (g : GProofTreeExt (Sequent.mk (Γ₁ ++ [A.conj B] ++ Γ₂) (Δ))), ∀ (s' : Sequent L), s' ∈
      gProofTreeLeafSequents g → seqAllAtomicOrQuantified s' := by
  have hpax : isAxiom (Sequent.mk (Γ₁ ++ [A, B] ++ Γ₂) Δ) := by
    exact ⟨P, mem_insert_middle P Γ₁ [A, B] Γ₂ hPctx, hPΔ⟩
  have hlt : sequentWeight (Sequent.mk (Γ₁ ++ [A, B] ++ Γ₂) Δ) < n := by
    rw [← hweight]
    simp [perm_seqWeight_eq, perm_listWeightSum_append, perm_listWeightSum, formulaWeight]
    omega
  obtain ⟨g, hg⟩ := ihS _ hlt hpax
  refine ⟨.onePremise (.conjLeft Γ₁ Γ₂ Δ A B) g, ?_⟩
  simpa [gProofTreeLeafSequents] using hg

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem axiom_atomic_left_disj
    (Δ : List (FormulaN L)) (P : FormulaN L) (mem_insert_middle : ∀ (X : FormulaN L) (xs mid ys : List
      (FormulaN L)), X ∈ xs ++ ys → X ∈ xs ++ mid ++ ys) (Γ₁ Γ₂ : List (FormulaN L)) (hPctx : P ∈ Γ₁ ++ Γ₂) (A
      B : FormulaN L) (hweight : sequentWeight (Sequent.mk (Γ₁ ++ [A.disj B] ++ Γ₂) (Δ)) = n) (hPΔ : P ∈ (Δ))
    : ∃ (g : GProofTreeExt (Sequent.mk (Γ₁ ++ [A.disj B] ++ Γ₂) (Δ))), ∀ (s' : Sequent L), s' ∈
      gProofTreeLeafSequents g → seqAllAtomicOrQuantified s' := by
  have hpax₁ : isAxiom (Sequent.mk (Γ₁ ++ [A] ++ Γ₂) Δ) := by
    exact ⟨P, mem_insert_middle P Γ₁ [A] Γ₂ hPctx, hPΔ⟩
  have hpax₂ : isAxiom (Sequent.mk (Γ₁ ++ [B] ++ Γ₂) Δ) := by
    exact ⟨P, mem_insert_middle P Γ₁ [B] Γ₂ hPctx, hPΔ⟩
  have hlt₁ : sequentWeight (Sequent.mk (Γ₁ ++ [A] ++ Γ₂) Δ) < n := by
    rw [← hweight]
    simp [perm_seqWeight_eq, perm_listWeightSum_append, perm_listWeightSum, formulaWeight]
    omega
  have hlt₂ : sequentWeight (Sequent.mk (Γ₁ ++ [B] ++ Γ₂) Δ) < n := by
    rw [← hweight]
    simp [perm_seqWeight_eq, perm_listWeightSum_append, perm_listWeightSum, formulaWeight]
    omega
  obtain ⟨g₁, hg₁⟩ := ihS _ hlt₁ hpax₁
  obtain ⟨g₂, hg₂⟩ := ihS _ hlt₂ hpax₂
  refine ⟨.twoPremise (.disjLeft Γ₁ Γ₂ Δ A B) g₁ g₂, ?_⟩
  intro l hl
  simp only [gProofTreeLeafSequents, List.mem_append] at hl
  exact hl.elim (hg₁ l) (hg₂ l)

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem axiom_atomic_left_impl
    (Δ : List (FormulaN L)) (P : FormulaN L) (Γ₁ Γ₂ : List (FormulaN L)) (hPctx : P ∈ Γ₁ ++ Γ₂) (A B :
      FormulaN L) (hweight : sequentWeight (Sequent.mk (Γ₁ ++ [A.impl B] ++ Γ₂) (Δ)) = n) (hPΔ : P ∈ (Δ))
    : ∃ (g : GProofTreeExt (Sequent.mk (Γ₁ ++ [A.impl B] ++ Γ₂) (Δ))), ∀ (s' : Sequent L), s' ∈
      gProofTreeLeafSequents g → seqAllAtomicOrQuantified s' := by
  have hpax₁ : isAxiom (Sequent.mk (Γ₁ ++ Γ₂) ([A] ++ Δ)) := ⟨P, hPctx, List.mem_append_right [A] hPΔ⟩
  have hpax₂ : isAxiom (Sequent.mk ([B] ++ Γ₁ ++ Γ₂) Δ) := by
    refine ⟨P, ?_, hPΔ⟩
    simpa only [List.append_assoc] using (List.mem_append_right [B] hPctx)
  have hlt₁ : sequentWeight (Sequent.mk (Γ₁ ++ Γ₂) ([A] ++ Δ)) < n := by
    rw [← hweight]
    simp [perm_seqWeight_eq, perm_listWeightSum_append, perm_listWeightSum, formulaWeight]
    omega
  have hlt₂ : sequentWeight (Sequent.mk ([B] ++ Γ₁ ++ Γ₂) Δ) < n := by
    rw [← hweight]
    simp [perm_seqWeight_eq, perm_listWeightSum_append, perm_listWeightSum, formulaWeight]
    omega
  obtain ⟨g₁, hg₁⟩ := ihS _ hlt₁ hpax₁
  obtain ⟨g₂, hg₂⟩ := ihS _ hlt₂ hpax₂
  refine ⟨.twoPremise (.implLeft Γ₁ Γ₂ Δ A B) g₁ g₂, ?_⟩
  intro l hl
  simp only [gProofTreeLeafSequents, List.mem_append] at hl
  exact hl.elim (hg₁ l) (hg₂ l)

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem axiom_atomic_right_neg
    (Γ : List (FormulaN L)) (P : FormulaN L) (Δ₁ Δ₂ : List (FormulaN L)) (hPctx : P ∈ Δ₁ ++ Δ₂) (A : FormulaN
      L) (hweight : sequentWeight (Sequent.mk (Γ) (Δ₁ ++ [A.neg] ++ Δ₂)) = n) (hPΓ : P ∈ (Γ))
    : ∃ (g : GProofTreeExt (Sequent.mk (Γ) (Δ₁ ++ [A.neg] ++ Δ₂))), ∀ (s' : Sequent L), s' ∈
      gProofTreeLeafSequents g → seqAllAtomicOrQuantified s' := by
  have hpax : isAxiom (Sequent.mk ([A] ++ Γ) (Δ₁ ++ Δ₂)) := by
    refine ⟨P, ?_, hPctx⟩
    exact List.mem_append_right [A] hPΓ
  have hlt : sequentWeight (Sequent.mk ([A] ++ Γ) (Δ₁ ++ Δ₂)) < n := by
    rw [← hweight]
    simp [perm_seqWeight_eq, perm_listWeightSum_append, perm_listWeightSum, formulaWeight]
    omega
  obtain ⟨g, hg⟩ := ihS _ hlt hpax
  refine ⟨.onePremise (.negRight Γ Δ₁ Δ₂ A) g, ?_⟩
  simpa [gProofTreeLeafSequents] using hg

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem axiom_atomic_right_conj
    (Γ : List (FormulaN L)) (P : FormulaN L) (mem_insert_middle : ∀ (X : FormulaN L) (xs mid ys : List
      (FormulaN L)), X ∈ xs ++ ys → X ∈ xs ++ mid ++ ys) (Δ₁ Δ₂ : List (FormulaN L)) (hPctx : P ∈ Δ₁ ++ Δ₂) (A
      B : FormulaN L) (hweight : sequentWeight (Sequent.mk (Γ) (Δ₁ ++ [A.conj B] ++ Δ₂)) = n) (hPΓ : P ∈ (Γ))
    : ∃ (g : GProofTreeExt (Sequent.mk (Γ) (Δ₁ ++ [A.conj B] ++ Δ₂))), ∀ (s' : Sequent L), s' ∈
      gProofTreeLeafSequents g → seqAllAtomicOrQuantified s' := by
  have hpax₁ : isAxiom (Sequent.mk Γ (Δ₁ ++ [A] ++ Δ₂)) := by
    exact ⟨P, hPΓ, mem_insert_middle P Δ₁ [A] Δ₂ hPctx⟩
  have hpax₂ : isAxiom (Sequent.mk Γ (Δ₁ ++ [B] ++ Δ₂)) := by
    exact ⟨P, hPΓ, mem_insert_middle P Δ₁ [B] Δ₂ hPctx⟩
  have hlt₁ : sequentWeight (Sequent.mk Γ (Δ₁ ++ [A] ++ Δ₂)) < n := by
    rw [← hweight]
    simp [perm_seqWeight_eq, perm_listWeightSum_append, perm_listWeightSum, formulaWeight]
    omega
  have hlt₂ : sequentWeight (Sequent.mk Γ (Δ₁ ++ [B] ++ Δ₂)) < n := by
    rw [← hweight]
    simp [perm_seqWeight_eq, perm_listWeightSum_append, perm_listWeightSum, formulaWeight]
    omega
  obtain ⟨g₁, hg₁⟩ := ihS _ hlt₁ hpax₁
  obtain ⟨g₂, hg₂⟩ := ihS _ hlt₂ hpax₂
  refine ⟨.twoPremise (.conjRight Γ Δ₁ Δ₂ A B) g₁ g₂, ?_⟩
  intro l hl
  simp only [gProofTreeLeafSequents, List.mem_append] at hl
  exact hl.elim (hg₁ l) (hg₂ l)

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem axiom_atomic_right_disj
    (Γ : List (FormulaN L)) (P : FormulaN L) (mem_insert_middle : ∀ (X : FormulaN L) (xs mid ys : List
      (FormulaN L)), X ∈ xs ++ ys → X ∈ xs ++ mid ++ ys) (Δ₁ Δ₂ : List (FormulaN L)) (hPctx : P ∈ Δ₁ ++ Δ₂) (A
      B : FormulaN L) (hweight : sequentWeight (Sequent.mk (Γ) (Δ₁ ++ [A.disj B] ++ Δ₂)) = n) (hPΓ : P ∈ (Γ))
    : ∃ (g : GProofTreeExt (Sequent.mk (Γ) (Δ₁ ++ [A.disj B] ++ Δ₂))), ∀ (s' : Sequent L), s' ∈
      gProofTreeLeafSequents g → seqAllAtomicOrQuantified s' := by
  have hpax : isAxiom (Sequent.mk Γ (Δ₁ ++ [A, B] ++ Δ₂)) := by
    exact ⟨P, hPΓ, mem_insert_middle P Δ₁ [A, B] Δ₂ hPctx⟩
  have hlt : sequentWeight (Sequent.mk Γ (Δ₁ ++ [A, B] ++ Δ₂)) < n := by
    rw [← hweight]
    simp [perm_seqWeight_eq, perm_listWeightSum_append, perm_listWeightSum, formulaWeight]
    omega
  obtain ⟨g, hg⟩ := ihS _ hlt hpax
  refine ⟨.onePremise (.disjRight Γ Δ₁ Δ₂ A B) g, ?_⟩
  simpa [gProofTreeLeafSequents] using hg

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem axiom_atomic_right_impl
    (Γ : List (FormulaN L)) (P : FormulaN L) (Δ₁ Δ₂ : List (FormulaN L)) (hPctx : P ∈ Δ₁ ++ Δ₂) (A B :
      FormulaN L) (hweight : sequentWeight (Sequent.mk (Γ) (Δ₁ ++ [A.impl B] ++ Δ₂)) = n) (hPΓ : P ∈ (Γ))
    : ∃ (g : GProofTreeExt (Sequent.mk (Γ) (Δ₁ ++ [A.impl B] ++ Δ₂))), ∀ (s' : Sequent L), s' ∈
      gProofTreeLeafSequents g → seqAllAtomicOrQuantified s' := by
  have hpax : isAxiom (Sequent.mk ([A] ++ Γ) ([B] ++ Δ₁ ++ Δ₂)) := by
    refine ⟨P, ?_, ?_⟩
    · exact List.mem_append_right [A] hPΓ
    · simpa [List.append_assoc] using List.mem_append_right [B] hPctx
  have hlt : sequentWeight (Sequent.mk ([A] ++ Γ) ([B] ++ Δ₁ ++ Δ₂)) < n := by
    rw [← hweight]
    simp [perm_seqWeight_eq, perm_listWeightSum_append, perm_listWeightSum, formulaWeight]
    omega
  obtain ⟨g, hg⟩ := ihS _ hlt hpax
  refine ⟨.onePremise (.implRight Γ Δ₁ Δ₂ A B) g, ?_⟩
  simpa [gProofTreeLeafSequents] using hg

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem axiom_atomic_both_conj
    (Γ₁ Γ₂ Δ₁ Δ₂ : List (FormulaN L)) (A B : FormulaN L) (hweight : sequentWeight (Sequent.mk (Γ₁ ++ [A.conj
      B] ++ Γ₂) (Δ₁ ++ [A.conj B] ++ Δ₂)) = n)
    : ∃ (g : GProofTreeExt (Sequent.mk (Γ₁ ++ [A.conj B] ++ Γ₂) (Δ₁ ++ [A.conj B] ++ Δ₂))), ∀ (s' : Sequent
      L), s' ∈ gProofTreeLeafSequents g → seqAllAtomicOrQuantified s' := by
  have hlt₁ : sequentWeight (Sequent.mk (Γ₁ ++ [A, B] ++ Γ₂) (Δ₁ ++ [A] ++ Δ₂)) < n := by
    rw [← hweight]
    exact perm_conj_both_weight_leaf1 A B Γ₁ Γ₂ Δ₁ Δ₂
  have hlt₂ : sequentWeight (Sequent.mk (Γ₁ ++ [A, B] ++ Γ₂) (Δ₁ ++ [B] ++ Δ₂)) < n := by
    rw [← hweight]
    exact perm_conj_both_weight_leaf2 A B Γ₁ Γ₂ Δ₁ Δ₂
  obtain ⟨g₁, hg₁⟩ := ihS _ hlt₁ (perm_conj_both_leaf1_ax A B Γ₁ Γ₂ Δ₁ Δ₂)
  obtain ⟨g₂, hg₂⟩ := ihS _ hlt₂ (perm_conj_both_leaf2_ax A B Γ₁ Γ₂ Δ₁ Δ₂)
  refine ⟨.onePremise (.conjLeft Γ₁ Γ₂ (Δ₁ ++ [FormulaN.conj A B] ++ Δ₂) A B) (.twoPremise
      (.conjRight (Γ₁ ++ [A, B] ++ Γ₂) Δ₁ Δ₂ A B)
      g₁ g₂), ?_⟩
  intro l hl
  simp only [gProofTreeLeafSequents, List.mem_append] at hl
  exact hl.elim (hg₁ l) (hg₂ l)

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem axiom_atomic_both_disj
    (Γ₁ Γ₂ Δ₁ Δ₂ : List (FormulaN L)) (A B : FormulaN L) (hweight : sequentWeight (Sequent.mk (Γ₁ ++ [A.disj
      B] ++ Γ₂) (Δ₁ ++ [A.disj B] ++ Δ₂)) = n)
    : ∃ (g : GProofTreeExt (Sequent.mk (Γ₁ ++ [A.disj B] ++ Γ₂) (Δ₁ ++ [A.disj B] ++ Δ₂))), ∀ (s' : Sequent
      L), s' ∈ gProofTreeLeafSequents g → seqAllAtomicOrQuantified s' := by
  have hlt₁ : sequentWeight (Sequent.mk (Γ₁ ++ [A] ++ Γ₂) (Δ₁ ++ [A, B] ++ Δ₂)) < n := by
    rw [← hweight]
    simp [perm_seqWeight_eq, perm_listWeightSum_append, perm_listWeightSum, formulaWeight]
    omega
  have hlt₂ : sequentWeight (Sequent.mk (Γ₁ ++ [B] ++ Γ₂) (Δ₁ ++ [A, B] ++ Δ₂)) < n := by
    rw [← hweight]
    simp [perm_seqWeight_eq, perm_listWeightSum_append, perm_listWeightSum, formulaWeight]
    omega
  obtain ⟨g₁, hg₁⟩ := ihS _ hlt₁ (perm_disj_both_leaf1_ax A B Γ₁ Γ₂ Δ₁ Δ₂)
  obtain ⟨g₂, hg₂⟩ := ihS _ hlt₂ (perm_disj_both_leaf2_ax A B Γ₁ Γ₂ Δ₁ Δ₂)
  refine ⟨.onePremise (.disjRight (Γ₁ ++ [FormulaN.disj A B] ++ Γ₂) Δ₁ Δ₂ A B) (.twoPremise
      (.disjLeft Γ₁ Γ₂ (Δ₁ ++ [A, B] ++ Δ₂) A B)
      g₁ g₂), ?_⟩
  intro l hl
  simp only [gProofTreeLeafSequents, List.mem_append] at hl
  exact hl.elim (hg₁ l) (hg₂ l)

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem axiom_atomic_both_neg
    (leafProperty_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (g : GProofTreeExt s₁), (∀ (l : Sequent
      L), l ∈ gProofTreeLeafSequents g → seqAllAtomicOrQuantified l) → ∀ (l : Sequent L), l ∈
      gProofTreeLeafSequents (heq ▸ g) → seqAllAtomicOrQuantified l) (Γ₁ Γ₂ Δ₁ Δ₂ : List (FormulaN L)) (A :
      FormulaN L) (hweight : sequentWeight (Sequent.mk (Γ₁ ++ [A.neg] ++ Γ₂) (Δ₁ ++ [A.neg] ++ Δ₂)) = n)
    : ∃ (g : GProofTreeExt (Sequent.mk (Γ₁ ++ [A.neg] ++ Γ₂) (Δ₁ ++ [A.neg] ++ Δ₂))), ∀ (s' : Sequent L), s' ∈
      gProofTreeLeafSequents g → seqAllAtomicOrQuantified s' := by
  have hlt : sequentWeight (Sequent.mk ([A] ++ Γ₁ ++ Γ₂) ([A] ++ Δ₁ ++ Δ₂)) < n := by
    rw [← hweight]
    simp [perm_seqWeight_eq, perm_listWeightSum_append, perm_listWeightSum, formulaWeight]
    omega
  obtain ⟨g, hg⟩ := ihS _ hlt (by exact ⟨A, by simp, by simp⟩)
  let rawMid : GProofTreeExt (Sequent.mk (([A] ++ Γ₁) ++ [FormulaN.neg A] ++ Γ₂) (Δ₁ ++ Δ₂)) :=
    GProofTreeExt.onePremise (GentzenStep1Ext.negLeft ([A] ++ Γ₁) Γ₂ (Δ₁ ++ Δ₂) A) g
  have hmid : (Sequent.mk (([A] ++ Γ₁) ++ [FormulaN.neg A] ++ Γ₂) (Δ₁ ++ Δ₂)) = Sequent.mk
        ([A] ++ (Γ₁ ++ [FormulaN.neg A] ++ Γ₂))
        (Δ₁ ++ Δ₂) := by
    simp [List.append_assoc]
  let gmid : GProofTreeExt (Sequent.mk ([A] ++ (Γ₁ ++ [FormulaN.neg A] ++ Γ₂)) (Δ₁ ++ Δ₂)) := hmid ▸ rawMid
  have hrawMid : ∀ l ∈ gProofTreeLeafSequents rawMid, seqAllAtomicOrQuantified l := by
    simpa [rawMid, gProofTreeLeafSequents] using hg
  have hgmid : ∀ l ∈ gProofTreeLeafSequents gmid, seqAllAtomicOrQuantified l := by
    exact leafProperty_transport hmid rawMid hrawMid
  refine ⟨.onePremise (.negRight (Γ₁ ++ [FormulaN.neg A] ++ Γ₂) Δ₁ Δ₂ A) gmid, ?_⟩
  simpa [gProofTreeLeafSequents] using hgmid

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem axiom_atomic_both_impl
    (Γ₁ Γ₂ Δ₁ Δ₂ : List (FormulaN L)) (A B : FormulaN L) (hweight : sequentWeight (Sequent.mk (Γ₁ ++ [A.impl
      B] ++ Γ₂) (Δ₁ ++ [A.impl B] ++ Δ₂)) = n)
    : ∃ (g : GProofTreeExt (Sequent.mk (Γ₁ ++ [A.impl B] ++ Γ₂) (Δ₁ ++ [A.impl B] ++ Δ₂))), ∀ (s' : Sequent
      L), s' ∈ gProofTreeLeafSequents g → seqAllAtomicOrQuantified s' := by
  have hlt₁ : sequentWeight (Sequent.mk ([A] ++ Γ₁ ++ Γ₂) ([B, A] ++ Δ₁ ++ Δ₂)) < n := by
    rw [← hweight]
    simp [perm_seqWeight_eq, perm_listWeightSum_append, perm_listWeightSum, formulaWeight]
    omega
  have hlt₂ : sequentWeight (Sequent.mk ([A, B] ++ Γ₁ ++ Γ₂) ([B] ++ Δ₁ ++ Δ₂)) < n := by
    rw [← hweight]
    simp [perm_seqWeight_eq, perm_listWeightSum_append, perm_listWeightSum, formulaWeight]
    omega
  obtain ⟨g₁, hg₁⟩ := ihS _ hlt₁ (by exact ⟨A, by simp, by simp⟩)
  obtain ⟨g₂, hg₂⟩ := ihS _ hlt₂ (by exact ⟨B, by simp, by simp⟩)
  let branch₁ : GProofTreeExt (Sequent.mk (Γ₁ ++ Γ₂) ([A] ++ (Δ₁ ++ [FormulaN.impl A B] ++ Δ₂))) :=
    .onePremise (.implRight (Γ₁ ++ Γ₂) ([A] ++ Δ₁) Δ₂ A B) g₁
  let branch₂ : GProofTreeExt (Sequent.mk ([B] ++ Γ₁ ++ Γ₂) (Δ₁ ++ [FormulaN.impl A B] ++ Δ₂)) :=
    .onePremise (.implRight ([B] ++ Γ₁ ++ Γ₂) Δ₁ Δ₂ A B) g₂
  refine ⟨.twoPremise (.implLeft Γ₁ Γ₂ (Δ₁ ++ [FormulaN.impl A B] ++ Δ₂) A B) branch₁ branch₂, ?_⟩
  intro l hl
  simp only [gProofTreeLeafSequents, List.mem_append] at hl
  rcases hl with hl | hl
  · exact hg₁ l hl
  · exact hg₂ l hl

end

-- ===================================================================
-- Lemma 6.3.1: permutation_lemma_geq
-- ===================================================================
/-- Lemma 6.3.1: Given a G=-proof T, there is a G=-proof T' such
that all leaf sequents of T' contain either atomic formulae or
quantified formulae (formulae of the form forall x B or
exists x B). The proof proceeds by induction on the structure of
the proof tree. -/
@[blueprint "chap6__lemma_6_3_1" (main := true)]
theorem permutation_lemma_geq {L : Language} {hL : L.hasEquality = true}
    {s : Sequent L}
    (T : GEqProofTree hL s) :
    ∃ T' : GEqProofTree hL s,
      ∀ s' ∈ geqLeafSequents T', seqAllAtomicOrQuantified s' 

end LCS.CutElim.LKe.Equivalence
end
