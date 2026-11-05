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

-- ===================================================================
-- Lemma 6.3.2 (required def): gProofTreeDepth
-- ===================================================================

/-- Lemma 6.3.2 (required def): The depth (height) of a G proof
tree: 0 for axiom leaves, 1 + max of subtree depths for rule
applications. -/
@[blueprint "chap6__lemma_6_3_2"]
def gProofTreeDepth {L : Language} :
    {s : Sequent L} → GProofTreeExt s → Nat
  | _, .axiom_ _ _ => 0
  | _, .onePremise _ t => 1 + gProofTreeDepth t
  | _, .twoPremise _ t1 t2 =>
    1 + max (gProofTreeDepth t1) (gProofTreeDepth t2)

-- ===================================================================
-- Lemma 6.3.2 (required def): geqDepth
-- ===================================================================

/-- Lemma 6.3.2 (required def): The depth (height) of a G= proof
tree: 0 for axiom leaves, 1 + max of subtree depths for rule
applications. -/
@[blueprint "chap6__lemma_6_3_2"]
def geqDepth {L : Language} {hL : L.hasEquality = true} :
    {s : Sequent L} → GEqProofTree hL s → Nat
  | _, .base g => gProofTreeDepth g
  | _, .axiom_ _ _ => 0
  | _, .onePremise _ sub => 1 + geqDepth sub
  | _, .twoPremise _ sub1 sub2 =>
    1 + max (geqDepth sub1) (geqDepth sub2)
  | _, .eqRefl _ _ _ sub => 1 + geqDepth sub
  | _, .eqFuncCong _ _ _ _ _ sub => 1 + geqDepth sub
  | _, .eqPredCong _ _ _ _ _ sub => 1 + geqDepth sub
  | _, .eqGeneral _ _ _ _ _ sub => 1 + geqDepth sub

-- ===================================================================
-- Lemma 6.3.2 (internal helper): depth-preserving context permutation
-- ===================================================================

-- ATTACH-BLOCKER: private declaration
/-- Removing equally marked occurrences from two permuted lists leaves
permuted remainders.  The occurrences are positional: this remains valid
when the marked value occurs more than once. -/
private theorem geqPerm_cancelMarked {α : Type} {P Q R S : List α} {X : α}
    (h : (P ++ [X] ++ Q).Perm (R ++ [X] ++ S)) :
    (P ++ Q).Perm (R ++ S) := by
  have moveFront :
      ∀ (U V : List α),
        (X :: (U ++ V)).Perm (U ++ [X] ++ V) := by
    intro U V
    have hmove :
        (([X] ++ U) ++ V).Perm ((U ++ [X]) ++ V) :=
      List.Perm.append_right V List.perm_append_comm
    simpa [List.append_assoc] using hmove
  exact List.Perm.cons_inv
    ((moveFront P Q).trans (h.trans (moveFront R S).symm))

-- ATTACH-BLOCKER: private declaration
/-- Inserting the same formula block at arbitrary splits preserves a
permutation of the surrounding contexts. -/
private theorem geqPerm_insertBlock {α : Type} {P Q R S : List α}
    (block : List α) (h : (P ++ Q).Perm (R ++ S)) :
    (P ++ block ++ Q).Perm (R ++ block ++ S) := by
  have moveFront :
      ∀ (U V : List α),
        (U ++ block ++ V).Perm (block ++ (U ++ V)) := by
    intro U V
    have hmove :
        ((U ++ block) ++ V).Perm ((block ++ U) ++ V) :=
      List.Perm.append_right V List.perm_append_comm
    simpa [List.append_assoc] using hmove
  exact (moveFront P Q).trans
    ((List.Perm.append_left block h).trans (moveFront R S).symm)

-- retained: used by LCS.CutElim.LKe.Equivalence.ContextPermutation
/-- Atomic-or-quantified sequents are invariant under independent
permutations of their antecedent and succedent. -/
theorem seqAllAtomicOrQuantified_perm {L : Language}
    {Γ Δ Γ' Δ' : List (FormulaN L)}
    (hΓ : Γ.Perm Γ') (hΔ : Δ.Perm Δ')
    (h : seqAllAtomicOrQuantified (Sequent.mk Γ Δ)) :
    seqAllAtomicOrQuantified (Sequent.mk Γ' Δ') := by
  constructor
  · intro F hF
    exact h.1 F (hΓ.mem_iff.mpr hF)
  · intro F hF
    exact h.2 F (hΔ.mem_iff.mpr hF)

-- retained: used by LCS.CutElim.LKe.Equivalence.ContextPermutation
theorem geqPermuteContexts_base
    (L : Language) (hL : L.hasEquality = true) (permAxiom : ∀ (s₀ : Sequent L), isAxiom s₀ → ∀ (Γ₀ Δ₀ : List
      (FormulaN L)), s₀.antecedent.Perm Γ₀ → s₀.succedent.Perm Δ₀ → seqAllAtomicOrQuantified s₀ → ∃ (p :
      GEqProofTree hL (Sequent.mk (Γ₀) (Δ₀))), geqDepth p = 0 ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p →
      seqAllAtomicOrQuantified s') (n : Nat) (s : Sequent L) (Γ' Δ' : List (FormulaN L)) (hΓ :
      s.antecedent.Perm Γ') (hΔ : s.succedent.Perm Δ') (permOne : ∀ {prem conc : Sequent L} (rule :
      GentzenStep1Ext prem conc) (sub : GEqProofTree hL prem), geqDepth sub < n → conc.antecedent.Perm Γ' →
      conc.succedent.Perm Δ' → (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified s') →
      ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth sub ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s') (permTwo : ∀ {prem1 prem2 conc : Sequent L} (rule :
      GentzenStep2Ext prem1 prem2 conc) (sub1 : GEqProofTree hL prem1) (sub2 : GEqProofTree hL prem2),
      geqDepth sub1 < n → geqDepth sub2 < n → conc.antecedent.Perm Γ' → conc.succedent.Perm Δ' → (∀ (s' :
      Sequent L), s' ∈ geqLeafSequents sub1 → seqAllAtomicOrQuantified s') → (∀ (s' : Sequent L), s' ∈
      geqLeafSequents sub2 → seqAllAtomicOrQuantified s') → ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))),
      geqDepth p = 1 + max (geqDepth sub1) (geqDepth sub2) ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p →
      seqAllAtomicOrQuantified s') (g : GProofTreeExt s) (hdepth : geqDepth (GEqProofTree.base (hL := hL) g) =
      n) (hleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents (GEqProofTree.base (hL := hL) g) →
      seqAllAtomicOrQuantified s')
    : ∃ (T' : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth T' = geqDepth (GEqProofTree.base (hL := hL) g)
      ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents T' → seqAllAtomicOrQuantified s' := by
  cases g with
  | axiom_ _ hAx =>
    obtain ⟨p, hpd, hpl⟩ := permAxiom s hAx Γ' Δ' hΓ hΔ (hleaf s (by
          simp [geqLeafSequents, gProofTreeLeafSequents]))
    exact ⟨p, by
      simpa [geqDepth, gProofTreeDepth] using hpd, hpl⟩
  | onePremise rule sub =>
    obtain ⟨p, hpd, hpl⟩ := permOne rule (.base sub) (by
        simp only [geqDepth, gProofTreeDepth] at hdepth ⊢
        omega) hΓ hΔ (by
          intro s' hs'
          exact hleaf s' (by
            simpa [geqLeafSequents, gProofTreeLeafSequents] using hs'))
    exact ⟨p, by
      simpa [geqDepth, gProofTreeDepth] using hpd, hpl⟩
  | twoPremise rule sub1 sub2 =>
    obtain ⟨p, hpd, hpl⟩ := permTwo rule (.base sub1) (.base sub2) (by
        simp only [geqDepth, gProofTreeDepth] at hdepth ⊢
        omega) (by
        simp only [geqDepth, gProofTreeDepth] at hdepth ⊢
        omega) hΓ hΔ (by
          intro s' hs'
          exact hleaf s' (by
            simp only [geqLeafSequents, gProofTreeLeafSequents, List.mem_append]
            exact Or.inl hs')) (by
          intro s' hs'
          exact hleaf s' (by
            simp only [geqLeafSequents, gProofTreeLeafSequents, List.mem_append]
            exact Or.inr hs'))
    exact ⟨p, by
      simpa [geqDepth, gProofTreeDepth] using hpd, hpl⟩

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
section
-- ATTACH-BLOCKER: variable
variable
    (L : Language) (hL : L.hasEquality = true) (n : Nat) (ih : ∀ (m : Nat), m < n → ∀ {s : Sequent L} (T :
      GEqProofTree hL s), geqDepth T = m → ∀ (Γ' Δ' : List (FormulaN L)), s.antecedent.Perm Γ' →
      s.succedent.Perm Δ' → (∀ (s' : Sequent L), s' ∈ geqLeafSequents T → seqAllAtomicOrQuantified s') → ∃ (T'
      : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth T' = geqDepth T ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents T' → seqAllAtomicOrQuantified s')
-- ATTACH-BLOCKER: unknown command Lean.Parser.Command.include
include ih

-- ATTACH-BLOCKER: private declaration
private theorem geqPermuteContexts_conjLeft
    (Γ' Δ' Γr Δr Λr : List (FormulaN L)) (X Y : FormulaN L) (sub : GEqProofTree hL (Sequent.mk (Γr ++ [X, Y]
      ++ Δr) (Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') (hΓc : (Γr ++ [X.conj Y] ++ Δr).Perm Γ') (hΔc : (Λr).Perm Δ')
    : ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth sub ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  have hmem : FormulaN.conj X Y ∈ Γ' := hΓc.mem_iff.mp (by simp)
  obtain ⟨Γt, Δt, hsplit⟩ := perm_mem_split (FormulaN.conj X Y) Γ' hmem
  subst Γ'
  have hrest := geqPerm_cancelMarked hΓc
  have hprem := geqPerm_insertBlock ([X, Y] : List (FormulaN L)) hrest
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) hsubdepth sub rfl (Γt ++ [X, Y] ++ Δt) Δ' hprem hΔc hsubleaf
  refine ⟨.onePremise (.conjLeft Γt Δt Δ' X Y) q, ?_, ?_⟩
  · simp only [geqDepth]
    omega
  · simpa [geqLeafSequents] using hql

-- ATTACH-BLOCKER: private declaration
private theorem geqPermuteContexts_disjRight
    (Γ' Δ' Γr Δr Λr : List (FormulaN L)) (X Y : FormulaN L) (sub : GEqProofTree hL (Sequent.mk (Γr) (Δr ++ [X,
      Y] ++ Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') (hΓc : (Γr).Perm Γ') (hΔc : (Δr ++ [X.disj Y] ++ Λr).Perm Δ')
    : ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth sub ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  have hmem : FormulaN.disj X Y ∈ Δ' := hΔc.mem_iff.mp (by simp)
  obtain ⟨Δt, Λt, hsplit⟩ := perm_mem_split (FormulaN.disj X Y) Δ' hmem
  subst Δ'
  have hrest := geqPerm_cancelMarked hΔc
  have hprem := geqPerm_insertBlock ([X, Y] : List (FormulaN L)) hrest
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) hsubdepth sub rfl Γ' (Δt ++ [X, Y] ++ Λt) hΓc hprem hsubleaf
  refine ⟨.onePremise (.disjRight Γ' Δt Λt X Y) q, ?_, ?_⟩
  · simp only [geqDepth]
    omega
  · simpa [geqLeafSequents] using hql

-- ATTACH-BLOCKER: private declaration
private theorem geqPermuteContexts_implRight
    (Γ' Δ' Γr Δr Λr : List (FormulaN L)) (X Y : FormulaN L) (sub : GEqProofTree hL (Sequent.mk ([X] ++ Γr)
      ([Y] ++ Δr ++ Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents
      sub → seqAllAtomicOrQuantified s') (hΓc : (Γr).Perm Γ') (hΔc : (Δr ++ [X.impl Y] ++ Λr).Perm Δ')
    : ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth sub ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  have hmem : FormulaN.impl X Y ∈ Δ' := hΔc.mem_iff.mp (by simp)
  obtain ⟨Δt, Λt, hsplit⟩ := perm_mem_split (FormulaN.impl X Y) Δ' hmem
  subst Δ'
  have hrest := geqPerm_cancelMarked hΔc
  have hpremAnt : ([X] ++ Γr).Perm ([X] ++ Γ') := List.Perm.append_left [X] hΓc
  have hpremSuc : ([Y] ++ Δr ++ Λr).Perm ([Y] ++ Δt ++ Λt) := by
    simpa [List.append_assoc] using List.Perm.append_left [Y] hrest
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) hsubdepth sub rfl ([X] ++ Γ') ([Y] ++ Δt ++ Λt)
      hpremAnt hpremSuc hsubleaf
  refine ⟨.onePremise (.implRight Γ' Δt Λt X Y) q, ?_, ?_⟩
  · simp only [geqDepth]
    omega
  · simpa [geqLeafSequents] using hql

-- ATTACH-BLOCKER: private declaration
private theorem geqPermuteContexts_negLeft
    (Γ' Δ' Γr Δr Λr : List (FormulaN L)) (X : FormulaN L) (sub : GEqProofTree hL (Sequent.mk (Γr ++ Δr) ([X]
      ++ Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') (hΓc : (Γr ++ [X.neg] ++ Δr).Perm Γ') (hΔc : (Λr).Perm Δ')
    : ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth sub ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  have hmem : FormulaN.neg X ∈ Γ' := hΓc.mem_iff.mp (by simp)
  obtain ⟨Γt, Δt, hsplit⟩ := perm_mem_split (FormulaN.neg X) Γ' hmem
  subst Γ'
  have hpremAnt := geqPerm_cancelMarked hΓc
  have hpremSuc : ([X] ++ Λr).Perm ([X] ++ Δ') := List.Perm.append_left [X] hΔc
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) hsubdepth sub rfl (Γt ++ Δt) ([X] ++ Δ')
      hpremAnt hpremSuc hsubleaf
  refine ⟨.onePremise (.negLeft Γt Δt Δ' X) q, ?_, ?_⟩
  · simp only [geqDepth]
    omega
  · simpa [geqLeafSequents] using hql

-- ATTACH-BLOCKER: private declaration
private theorem geqPermuteContexts_negRight
    (Γ' Δ' Γr Δr Λr : List (FormulaN L)) (X : FormulaN L) (sub : GEqProofTree hL (Sequent.mk ([X] ++ Γr) (Δr
      ++ Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') (hΓc : (Γr).Perm Γ') (hΔc : (Δr ++ [X.neg] ++ Λr).Perm Δ')
    : ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth sub ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  have hmem : FormulaN.neg X ∈ Δ' := hΔc.mem_iff.mp (by simp)
  obtain ⟨Δt, Λt, hsplit⟩ := perm_mem_split (FormulaN.neg X) Δ' hmem
  subst Δ'
  have hpremAnt : ([X] ++ Γr).Perm ([X] ++ Γ') := List.Perm.append_left [X] hΓc
  have hpremSuc := geqPerm_cancelMarked hΔc
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) hsubdepth sub rfl ([X] ++ Γ') (Δt ++ Λt)
      hpremAnt hpremSuc hsubleaf
  refine ⟨.onePremise (.negRight Γ' Δt Λt X) q, ?_, ?_⟩
  · simp only [geqDepth]
    omega
  · simpa [geqLeafSequents] using hql

-- ATTACH-BLOCKER: private declaration
private theorem geqPermuteContexts_allLeft
    (Γ' Δ' : List (FormulaN L)) (ts : List (Term L)) (Γr Δr Λr : List (FormulaN L)) (x : Nat) (X : FormulaN L)
      (hne : ts ≠ []) (hfree : ∀ (t : Term L), t ∈ ts → isFreeForN t x X) (sub : GEqProofTree hL (Sequent.mk
      (Γr ++ List.map (fun (t : Term L) => formulaSubstN X t x) ts ++ [FormulaN.all x X] ++ Δr) (Λr)))
      (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') (hΓc : (Γr ++ [FormulaN.all x X] ++ Δr).Perm Γ') (hΔc : (Λr).Perm Δ')
    : ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth sub ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  have hmem : FormulaN.all x X ∈ Γ' := hΓc.mem_iff.mp (by simp)
  obtain ⟨Γt, Δt, hsplit⟩ := perm_mem_split (FormulaN.all x X) Γ' hmem
  subst Γ'
  have hrest := geqPerm_cancelMarked hΓc
  have hprem : (Γr ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++ [FormulaN.all x X] ++ Δr).Perm
        (Γt ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++ [FormulaN.all x X] ++ Δt) := by
    simpa [List.append_assoc] using (geqPerm_insertBlock
        (ts.map (fun t => Substitution.formulaSubstN X t x) ++ [FormulaN.all x X]) hrest)
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) hsubdepth sub rfl
      (Γt ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++ [FormulaN.all x X] ++ Δt)
      Δ' hprem hΔc hsubleaf
  refine ⟨.onePremise (.allLeft ts Γt Δt Δ' x X hne hfree) q, ?_, ?_⟩
  · simp only [geqDepth]
    omega
  · simpa [geqLeafSequents] using hql

-- ATTACH-BLOCKER: private declaration
private theorem geqPermuteContexts_allRight
    (permFresh : ∀ (y : Nat) {Γ Δ Γ' Δ' : List (FormulaN L)}, Γ.Perm Γ' → Δ.Perm Δ' → (∀ (F : FormulaN L), F ∈
      Γ ++ Δ → ¬y ∈ formulaFVN F) → ∀ (F : FormulaN L), F ∈ Γ' ++ Δ' → ¬y ∈ formulaFVN F) (Γ' Δ' : List
      (FormulaN L)) (y : Nat) (Γr Δr Λr : List (FormulaN L)) (x : Nat) (X : FormulaN L) (hfresh : ∀ (F :
      FormulaN L), F ∈ (Γr) ++ (Δr ++ [FormulaN.all x X] ++ Λr) → ¬y ∈ formulaFVN F) (hfree : isFreeForN
      (Term.var y) x X) (sub : GEqProofTree hL (Sequent.mk (Γr) (Δr ++ [formulaSubstN X (Term.var y) x] ++
      Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') (hΓc : (Γr).Perm Γ') (hΔc : (Δr ++ [FormulaN.all x X] ++ Λr).Perm Δ')
    : ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth sub ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  have hmem : FormulaN.all x X ∈ Δ' := hΔc.mem_iff.mp (by simp)
  obtain ⟨Δt, Λt, hsplit⟩ := perm_mem_split (FormulaN.all x X) Δ' hmem
  subst Δ'
  have hrest := geqPerm_cancelMarked hΔc
  have hprem := geqPerm_insertBlock ([Substitution.formulaSubstN X (Term.var y) x] : List (FormulaN L)) hrest
  have hfresh' : ∀ F ∈ Γ' ++ (Δt ++ [FormulaN.all x X] ++ Λt), y ∉ Variables.formulaFVN F :=
    permFresh y hΓc hΔc hfresh
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) hsubdepth sub rfl Γ'
      (Δt ++ [Substitution.formulaSubstN X (Term.var y) x] ++ Λt)
      hΓc hprem hsubleaf
  refine ⟨.onePremise (.allRight y Γ' Δt Λt x X hfresh' hfree) q, ?_, ?_⟩
  · simp only [geqDepth]
    omega
  · simpa [geqLeafSequents] using hql

-- ATTACH-BLOCKER: private declaration
private theorem geqPermuteContexts_exLeft
    (permFresh : ∀ (y : Nat) {Γ Δ Γ' Δ' : List (FormulaN L)}, Γ.Perm Γ' → Δ.Perm Δ' → (∀ (F : FormulaN L), F ∈
      Γ ++ Δ → ¬y ∈ formulaFVN F) → ∀ (F : FormulaN L), F ∈ Γ' ++ Δ' → ¬y ∈ formulaFVN F) (Γ' Δ' : List
      (FormulaN L)) (y : Nat) (Γr Δr Λr : List (FormulaN L)) (x : Nat) (X : FormulaN L) (hfresh : ∀ (F :
      FormulaN L), F ∈ (Γr ++ [FormulaN.ex x X] ++ Δr) ++ (Λr) → ¬y ∈ formulaFVN F) (hfree : isFreeForN
      (Term.var y) x X) (sub : GEqProofTree hL (Sequent.mk (Γr ++ [formulaSubstN X (Term.var y) x] ++ Δr)
      (Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') (hΓc : (Γr ++ [FormulaN.ex x X] ++ Δr).Perm Γ') (hΔc : (Λr).Perm Δ')
    : ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth sub ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  have hmem : FormulaN.ex x X ∈ Γ' := hΓc.mem_iff.mp (by simp)
  obtain ⟨Γt, Δt, hsplit⟩ := perm_mem_split (FormulaN.ex x X) Γ' hmem
  subst Γ'
  have hrest := geqPerm_cancelMarked hΓc
  have hprem := geqPerm_insertBlock ([Substitution.formulaSubstN X (Term.var y) x] : List (FormulaN L)) hrest
  have hfresh' : ∀ F ∈ (Γt ++ [FormulaN.ex x X] ++ Δt) ++ Δ', y ∉ Variables.formulaFVN F :=
    permFresh y hΓc hΔc hfresh
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) hsubdepth sub rfl
      (Γt ++ [Substitution.formulaSubstN X (Term.var y) x] ++ Δt)
      Δ' hprem hΔc hsubleaf
  refine ⟨.onePremise (.exLeft y Γt Δt Δ' x X hfresh' hfree) q, ?_, ?_⟩
  · simp only [geqDepth]
    omega
  · simpa [geqLeafSequents] using hql

-- ATTACH-BLOCKER: private declaration
private theorem geqPermuteContexts_exRight
    (Γ' Δ' : List (FormulaN L)) (ts : List (Term L)) (Γr Δr Λr : List (FormulaN L)) (x : Nat) (X : FormulaN L)
      (hne : ts ≠ []) (hfree : ∀ (t : Term L), t ∈ ts → isFreeForN t x X) (sub : GEqProofTree hL (Sequent.mk
      (Γr) (Δr ++ List.map (fun (t : Term L) => formulaSubstN X t x) ts ++ [FormulaN.ex x X] ++ Λr)))
      (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') (hΓc : (Γr).Perm Γ') (hΔc : (Δr ++ [FormulaN.ex x X] ++ Λr).Perm Δ')
    : ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth sub ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  have hmem : FormulaN.ex x X ∈ Δ' := hΔc.mem_iff.mp (by simp)
  obtain ⟨Δt, Λt, hsplit⟩ := perm_mem_split (FormulaN.ex x X) Δ' hmem
  subst Δ'
  have hrest := geqPerm_cancelMarked hΔc
  have hprem : (Δr ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++ [FormulaN.ex x X] ++ Λr).Perm
        (Δt ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++ [FormulaN.ex x X] ++ Λt) := by
    simpa [List.append_assoc] using (geqPerm_insertBlock
        (ts.map (fun t => Substitution.formulaSubstN X t x) ++ [FormulaN.ex x X]) hrest)
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) hsubdepth sub rfl Γ'
      (Δt ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++ [FormulaN.ex x X] ++ Λt)
      hΓc hprem hsubleaf
  refine ⟨.onePremise (.exRight ts Γ' Δt Λt x X hne hfree) q, ?_, ?_⟩
  · simp only [geqDepth]
    omega
  · simpa [geqLeafSequents] using hql

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqPermuteContexts_permOne
    (permFresh : ∀ (y : Nat) {Γ Δ Γ' Δ' : List (FormulaN L)}, Γ.Perm Γ' → Δ.Perm Δ' → (∀ (F : FormulaN L), F ∈
      Γ ++ Δ → ¬y ∈ formulaFVN F) → ∀ (F : FormulaN L), F ∈ Γ' ++ Δ' → ¬y ∈ formulaFVN F) (Γ' Δ' : List
      (FormulaN L))
    : ∀ {prem conc : Sequent L} (rule : GentzenStep1Ext prem conc) (sub : GEqProofTree hL prem), geqDepth sub
      < n → conc.antecedent.Perm Γ' → conc.succedent.Perm Δ' → (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') → ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth
      sub ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  intro prem conc rule sub hsubdepth hΓc hΔc hsubleaf
  cases rule with
  | conjLeft Γr Δr Λr X Y =>
    exact geqPermuteContexts_conjLeft L hL n ih Γ' Δ' _ _ _ X Y sub hsubdepth hsubleaf hΓc hΔc
  | disjRight Γr Δr Λr X Y =>
    exact geqPermuteContexts_disjRight L hL n ih Γ' Δ' _ _ _ X Y sub hsubdepth hsubleaf hΓc hΔc
  | implRight Γr Δr Λr X Y =>
    exact geqPermuteContexts_implRight L hL n ih Γ' Δ' Γr Δr Λr X Y sub hsubdepth hsubleaf hΓc hΔc
  | negLeft Γr Δr Λr X =>
    exact geqPermuteContexts_negLeft L hL n ih Γ' Δ' _ _ Λr X sub hsubdepth hsubleaf hΓc hΔc
  | negRight Γr Δr Λr X =>
    exact geqPermuteContexts_negRight L hL n ih Γ' Δ' Γr _ _ X sub hsubdepth hsubleaf hΓc hΔc
  | allLeft ts Γr Δr Λr x X hne hfree =>
    exact geqPermuteContexts_allLeft L hL n ih Γ' Δ' ts Γr Δr _ x X hne hfree sub hsubdepth hsubleaf hΓc hΔc
  | allRight y Γr Δr Λr x X hfresh hfree =>
    exact geqPermuteContexts_allRight L hL n ih permFresh Γ' Δ' y _ _ _ x X hfresh hfree sub hsubdepth hsubleaf hΓc hΔc
  | exLeft y Γr Δr Λr x X hfresh hfree =>
    exact geqPermuteContexts_exLeft L hL n ih permFresh Γ' Δ' y _ _ _ x X hfresh hfree sub hsubdepth hsubleaf hΓc hΔc
  | exRight ts Γr Δr Λr x X hne hfree =>
    exact geqPermuteContexts_exRight L hL n ih Γ' Δ' ts _ Δr Λr x X hne hfree sub hsubdepth hsubleaf hΓc hΔc

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqPermuteContexts_permTwo
    (Γ' Δ' : List (FormulaN L))
    : ∀ {prem1 prem2 conc : Sequent L} (rule : GentzenStep2Ext prem1 prem2 conc) (sub1 : GEqProofTree hL
      prem1) (sub2 : GEqProofTree hL prem2), geqDepth sub1 < n → geqDepth sub2 < n → conc.antecedent.Perm Γ' →
      conc.succedent.Perm Δ' → (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub1 → seqAllAtomicOrQuantified s') →
      (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub2 → seqAllAtomicOrQuantified s') → ∃ (p : GEqProofTree hL
      (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + max (geqDepth sub1) (geqDepth sub2) ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  intro prem1 prem2 conc rule sub1 sub2 hsub1depth hsub2depth hΓc hΔc hsub1leaf hsub2leaf
  cases rule with
  | conjRight Γr Δr Λr X Y =>
    have hmem : FormulaN.conj X Y ∈ Δ' := hΔc.mem_iff.mp (by simp)
    obtain ⟨Δt, Λt, hsplit⟩ := perm_mem_split (FormulaN.conj X Y) Δ' hmem
    subst Δ'
    have hrest := geqPerm_cancelMarked hΔc
    have hprem1 := geqPerm_insertBlock ([X] : List (FormulaN L)) hrest
    have hprem2 := geqPerm_insertBlock ([Y] : List (FormulaN L)) hrest
    obtain ⟨q1, hq1d, hq1l⟩ := ih (geqDepth sub1) hsub1depth sub1 rfl Γ'
        (Δt ++ [X] ++ Λt) hΓc hprem1 hsub1leaf
    obtain ⟨q2, hq2d, hq2l⟩ := ih (geqDepth sub2) hsub2depth sub2 rfl Γ'
        (Δt ++ [Y] ++ Λt) hΓc hprem2 hsub2leaf
    refine ⟨.twoPremise (.conjRight Γ' Δt Λt X Y) q1 q2, ?_, ?_⟩
    · simp only [geqDepth]
      omega
    · intro s' hs'
      simp only [geqLeafSequents, List.mem_append] at hs'
      exact hs'.elim (hq1l s') (hq2l s')
  | disjLeft Γr Δr Λr X Y =>
    have hmem : FormulaN.disj X Y ∈ Γ' := hΓc.mem_iff.mp (by simp)
    obtain ⟨Γt, Δt, hsplit⟩ := perm_mem_split (FormulaN.disj X Y) Γ' hmem
    subst Γ'
    have hrest := geqPerm_cancelMarked hΓc
    have hprem1 := geqPerm_insertBlock ([X] : List (FormulaN L)) hrest
    have hprem2 := geqPerm_insertBlock ([Y] : List (FormulaN L)) hrest
    obtain ⟨q1, hq1d, hq1l⟩ := ih (geqDepth sub1) hsub1depth sub1 rfl
        (Γt ++ [X] ++ Δt) Δ' hprem1 hΔc hsub1leaf
    obtain ⟨q2, hq2d, hq2l⟩ := ih (geqDepth sub2) hsub2depth sub2 rfl
        (Γt ++ [Y] ++ Δt) Δ' hprem2 hΔc hsub2leaf
    refine ⟨.twoPremise (.disjLeft Γt Δt Δ' X Y) q1 q2, ?_, ?_⟩
    · simp only [geqDepth]
      omega
    · intro s' hs'
      simp only [geqLeafSequents, List.mem_append] at hs'
      exact hs'.elim (hq1l s') (hq2l s')
  | implLeft Γr Δr Λr X Y =>
    have hmem : FormulaN.impl X Y ∈ Γ' := hΓc.mem_iff.mp (by simp)
    obtain ⟨Γt, Δt, hsplit⟩ := perm_mem_split (FormulaN.impl X Y) Γ' hmem
    subst Γ'
    have hrest := geqPerm_cancelMarked hΓc
    have hprem1suc : ([X] ++ Λr).Perm ([X] ++ Δ') := List.Perm.append_left [X] hΔc
    have hprem2ant : ([Y] ++ Γr ++ Δr).Perm ([Y] ++ (Γt ++ Δt)) := by
      simpa [List.append_assoc] using (List.Perm.append_left [Y] hrest)
    obtain ⟨q1, hq1d, hq1l⟩ := ih (geqDepth sub1) hsub1depth sub1 rfl (Γt ++ Δt) ([X] ++ Δ')
        hrest hprem1suc hsub1leaf
    obtain ⟨q2, hq2d, hq2l⟩ := ih (geqDepth sub2) hsub2depth sub2 rfl ([Y] ++ Γt ++ Δt) Δ'
        hprem2ant hΔc hsub2leaf
    refine ⟨.twoPremise (.implLeft Γt Δt Δ' X Y) q1 q2, ?_, ?_⟩
    · simp only [geqDepth]
      omega
    · intro s' hs'
      simp only [geqLeafSequents, List.mem_append] at hs'
      exact hs'.elim (hq1l s') (hq2l s')

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqPermuteContexts_eqRefl
    (Γ' Δ' : List (FormulaN L)) (t : Term L) (Γr Δr : List (FormulaN L)) (sub : GEqProofTree hL (Sequent.mk
      (Γr ++ [FormulaN.eq_ hL t t]) (Δr))) (hΓ : (Γr).Perm Γ') (hΔ : (Δr).Perm Δ') (hdepth : geqDepth
      (GEqProofTree.eqRefl t Γr Δr sub) = n) (hleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents
      (GEqProofTree.eqRefl t Γr Δr sub) → seqAllAtomicOrQuantified s')
    : ∃ (T' : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth T' = geqDepth (GEqProofTree.eqRefl t Γr Δr
      sub) ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents T' → seqAllAtomicOrQuantified s' := by
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) (by
      simp only [geqDepth] at hdepth
      omega) sub rfl
      (Γ' ++ [FormulaN.eq_ hL t t]) Δ'
      (List.Perm.append_right [FormulaN.eq_ hL t t] hΓ) hΔ (by
        simpa [geqLeafSequents] using hleaf)
  let p : GEqProofTree hL (Sequent.mk Γ' Δ') := .eqRefl t Γ' Δ' q
  refine ⟨p, ?_, ?_⟩
  · change 1 + geqDepth q = 1 + geqDepth sub
    rw [hqd]
  · simpa [p, geqLeafSequents] using hql

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqPermuteContexts_eqFuncCong
    (Γ' Δ' : List (FormulaN L)) (f : L.funSymbols) (ss ts : Fin (L.funArity f) → Term L) (Γr Δr : List
      (FormulaN L)) (sub : GEqProofTree hL (Sequent.mk (Γr ++ [eqCongruenceImplFunc L hL f ss ts]) (Δr))) (hΓ
      : (Γr).Perm Γ') (hΔ : (Δr).Perm Δ') (hdepth : geqDepth (GEqProofTree.eqFuncCong f ss ts Γr Δr sub) = n)
      (hleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents (GEqProofTree.eqFuncCong f ss ts Γr Δr sub) →
      seqAllAtomicOrQuantified s')
    : ∃ (T' : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth T' = geqDepth (GEqProofTree.eqFuncCong f ss ts
      Γr Δr sub) ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents T' → seqAllAtomicOrQuantified s' := by
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) (by
      simp only [geqDepth] at hdepth
      omega) sub rfl
      (Γ' ++ [eqCongruenceImplFunc L hL f ss ts]) Δ'
      (List.Perm.append_right [eqCongruenceImplFunc L hL f ss ts] hΓ) hΔ (by
        simpa [geqLeafSequents] using hleaf)
  let p : GEqProofTree hL (Sequent.mk Γ' Δ') := .eqFuncCong f ss ts Γ' Δ' q
  refine ⟨p, ?_, ?_⟩
  · change 1 + geqDepth q = 1 + geqDepth sub
    rw [hqd]
  · simpa [p, geqLeafSequents] using hql

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqPermuteContexts_eqPredCong
    (Γ' Δ' : List (FormulaN L)) (P : L.predSymbols) (ss ts : Fin (L.predArity P) →
      Term L) (Γr Δr : List (FormulaN L)) (sub : GEqProofTree hL (Sequent.mk (Γr ++ [eqCongruenceImplPred L hL
      P ss ts]) (Δr))) (hΓ : (Γr).Perm Γ') (hΔ : (Δr).Perm Δ') (hdepth : geqDepth (GEqProofTree.eqPredCong P ss ts Γr Δr sub) = n) (hleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents (GEqProofTree.eqPredCong P
      ss ts Γr Δr sub) → seqAllAtomicOrQuantified s')
    : ∃ (T' : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth T' = geqDepth (GEqProofTree.eqPredCong P ss
      ts Γr Δr sub) ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents T' → seqAllAtomicOrQuantified s' := by
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) (by
      simp only [geqDepth] at hdepth
      omega) sub rfl
      (Γ' ++ [eqCongruenceImplPred L hL P ss ts]) Δ'
      (List.Perm.append_right [eqCongruenceImplPred L hL P ss ts] hΓ) hΔ (by
        simpa [geqLeafSequents] using hleaf)
  let p : GEqProofTree hL (Sequent.mk Γ' Δ') := .eqPredCong P ss ts Γ' Δ' q
  refine ⟨p, ?_, ?_⟩
  · change 1 + geqDepth q = 1 + geqDepth sub
    rw [hqd]
  · simpa [p, geqLeafSequents] using hql

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqPermuteContexts_eqGeneral
    (Γ' Δ' axioms : List (FormulaN L)) (hne : axioms ≠ []) (haxioms : ∀ (A : FormulaN L), A ∈ axioms →
      isEqAxiomInstance hL A) (Γr Δr : List (FormulaN L)) (sub : GEqProofTree hL (Sequent.mk (Γr ++ axioms)
      (Δr))) (hΓ : (Γr).Perm Γ') (hΔ : (Δr).Perm Δ') (hdepth : geqDepth (GEqProofTree.eqGeneral axioms hne
      haxioms Γr Δr sub) = n) (hleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents (GEqProofTree.eqGeneral axioms
      hne haxioms Γr Δr sub) → seqAllAtomicOrQuantified s')
    : ∃ (T' : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth T' = geqDepth (GEqProofTree.eqGeneral axioms
      hne haxioms Γr Δr sub) ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents T' → seqAllAtomicOrQuantified s' := by
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) (by
      simp only [geqDepth] at hdepth
      omega) sub rfl
      (Γ' ++ axioms) Δ'
      (List.Perm.append_right axioms hΓ) hΔ (by
        simpa [geqLeafSequents] using hleaf)
  let p : GEqProofTree hL (Sequent.mk Γ' Δ') := .eqGeneral axioms hne haxioms Γ' Δ' q
  refine ⟨p, ?_, ?_⟩
  · change 1 + geqDepth q = 1 + geqDepth sub
    rw [hqd]
  · simpa [p, geqLeafSequents] using hql

end
end LCS.CutElim.LKe.Equivalence
end

