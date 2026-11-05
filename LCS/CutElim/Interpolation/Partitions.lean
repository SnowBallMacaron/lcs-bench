import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import Attach
import LCS.CutElim.Interpolation.Partitions.ProofsStamp

section
namespace LCS.CutElim.Interpolation
open Classical
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen.Hintikka
namespace List

/-- Lemma 6.5.2 (required type): Two lists l1 and l2 form an
interleaving of a list l if l can be obtained by interleaving the
elements of l1 and l2 while preserving the relative order within
each list. Used in `SequentPartition` to express that the antecedent
(resp. succedent) is the union of two disjoint subsequences. -/
@[blueprint "chap6__lemma_6_5_2"]
inductive Interleaving {α : Type} :
    List α → List α → List α → Prop where
  /-- The empty list is an interleaving of two empty lists -/
  | nil : List.Interleaving [] [] []
  /-- Prepending an element from the first list -/
  | left (a : α) {l1 l2 l : List α} :
    List.Interleaving l1 l2 l →
    List.Interleaving (a :: l1) l2 (a :: l)
  /-- Prepending an element from the second list -/
  | right (a : α) {l1 l2 l : List α} :
    List.Interleaving l1 l2 l →
    List.Interleaving l1 (a :: l2) (a :: l)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- If an interleaving of l1 and l2 gives [], then l1 = [] and l2 = []. -/
theorem Interleaving.nil_iff {α : Type} {l1 l2 : List α}
    (h : List.Interleaving l1 l2 []) : l1 = [] ∧ l2 = [] := by
-- BEGIN PROOF
  cases h with
  | nil => exact ⟨rfl, rfl⟩

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- If an interleaving of l1 and l2 gives [a], then either l1 = [a] ∧ l2 = []
or l1 = [] ∧ l2 = [a]. -/
theorem Interleaving.singleton_iff {α : Type} {l1 l2 : List α} {a : α}
    (h : List.Interleaving l1 l2 [a]) :
    (l1 = [a] ∧ l2 = []) ∨ (l1 = [] ∧ l2 = [a]) := by
-- BEGIN PROOF
  cases h with
  | left a' h' =>
    left
    have := h'.nil_iff
    exact ⟨by rw [this.1], this.2⟩
  | right a' h' =>
    right
    have := h'.nil_iff
    exact ⟨this.1, by rw [this.2]⟩

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- If l is an interleaving of l1 and l2, then every element of l
is in l1 or l2. -/
theorem Interleaving.mem_or {α : Type} {l1 l2 l : List α} {a : α}
    (h : List.Interleaving l1 l2 l) (ha : a ∈ l) :
    a ∈ l1 ∨ a ∈ l2 := by
-- BEGIN PROOF
  induction h with
  | nil => simp at ha
  | left x _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact Or.inl (List.Mem.head _)
    · rcases ih ha' with h1 | h2
      · exact Or.inl (List.Mem.tail _ h1)
      · exact Or.inr h2
  | right x _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact Or.inr (List.Mem.head _)
    · rcases ih ha' with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (List.Mem.tail _ h2)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Inversion: if the interleaving of l1, l2 starts with a, then either
l1 starts with a or l2 starts with a. -/
theorem Interleaving.cons_inv {α : Type} {l1 l2 l : List α} {a : α}
    (h : List.Interleaving l1 l2 (a :: l)) :
    (∃ l1', l1 = a :: l1' ∧ List.Interleaving l1' l2 l) ∨
    (∃ l2', l2 = a :: l2' ∧ List.Interleaving l1 l2' l) := by
-- BEGIN PROOF
  cases h with
  | left a' h' => exact Or.inl ⟨_, rfl, h'⟩
  | right a' h' => exact Or.inr ⟨_, rfl, h'⟩

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- If l1, l2 interleave to l, then every element of l1 is in l. -/
theorem Interleaving.mem_left {α : Type} {l1 l2 l : List α} {a : α}
    (h : List.Interleaving l1 l2 l) (ha : a ∈ l1) : a ∈ l := by
-- BEGIN PROOF
  induction h with
  | nil => simp at ha
  | left x _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact List.Mem.head _
    · exact List.Mem.tail _ (ih ha')
  | right x _ ih => exact List.Mem.tail _ (ih ha)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- If l1, l2 interleave to l, then every element of l2 is in l. -/
theorem Interleaving.mem_right {α : Type} {l1 l2 l : List α} {a : α}
    (h : List.Interleaving l1 l2 l) (ha : a ∈ l2) : a ∈ l := by
-- BEGIN PROOF
  induction h with
  | nil => simp at ha
  | left x _ ih => exact List.Mem.tail _ (ih ha)
  | right x _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact List.Mem.head _
    · exact List.Mem.tail _ (ih ha')

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The identity interleaving: l is an interleaving of [] and l. -/
theorem Interleaving.nil_left {α : Type} :
    ∀ (l : List α), List.Interleaving [] l l
  | [] => .nil
  | a :: rest => .right a (Interleaving.nil_left rest)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The identity interleaving: l is an interleaving of l and []. -/
theorem Interleaving.nil_right {α : Type} :
    ∀ (l : List α), List.Interleaving l [] l
  | [] => .nil
  | a :: rest => .left a (Interleaving.nil_right rest)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Append to combined list: if Interleaving l1 l2 l, then
Interleaving l1 (l2 ++ l') (l ++ l') when we also interleave l' into l2. -/
theorem Interleaving.append_right {α : Type} {l1 l2 l : List α}
    (h : List.Interleaving l1 l2 l) (l' : List α) :
    List.Interleaving l1 (l2 ++ l') (l ++ l') := by
-- BEGIN PROOF
  induction h with
  | nil => simp; exact Interleaving.nil_left l'
  | left a _ ih => exact .left a ih
  | right a _ ih => exact .right a ih

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Append to combined list on the left side. -/
theorem Interleaving.append_left {α : Type} {l1 l2 l : List α}
    (h : List.Interleaving l1 l2 l) (l' : List α) :
    List.Interleaving (l1 ++ l') l2 (l ++ l') := by
-- BEGIN PROOF
  induction h with
  | nil => simp; exact Interleaving.nil_right l'
  | left a _ ih => exact .left a ih
  | right a _ ih => exact .right a ih

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Splitting an interleaving over an append: if Interleaving l1 l2 (a ++ b),
then l1 and l2 each split into sub-lists l1a++l1b and l2a++l2b that
interleave a and b respectively. -/
theorem Interleaving.append_split {α : Type} {l1 l2 : List α}
    {a b : List α}
    (h : List.Interleaving l1 l2 (a ++ b)) :
    ∃ l1a l1b l2a l2b,
      l1 = l1a ++ l1b ∧ l2 = l2a ++ l2b ∧
      List.Interleaving l1a l2a a ∧ List.Interleaving l1b l2b b := by
-- BEGIN PROOF
  induction a generalizing l1 l2 with
  | nil =>
    simp at h
    exact ⟨[], l1, [], l2, rfl, rfl, .nil, h⟩
  | cons x xs ih =>
    simp only [List.cons_append] at h
    rcases h.cons_inv with ⟨l1', hl1, hint⟩ | ⟨l2', hl2, hint⟩
    · obtain ⟨l1a, l1b, l2a, l2b, h1, h2, ha, hb⟩ := ih hint
      exact ⟨x :: l1a, l1b, l2a, l2b, by rw [hl1, h1]; simp, h2, .left x ha, hb⟩
    · obtain ⟨l1a, l1b, l2a, l2b, h1, h2, ha, hb⟩ := ih hint
      exact ⟨l1a, l1b, x :: l2a, l2b, h1, by rw [hl2, h2]; simp, .right x ha, hb⟩

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Inversion for appending a single element: if Interleaving l1 l2 (l ++ [a]),
then either l1 ends with a or l2 ends with a. -/
theorem Interleaving.append_single_inv {α : Type} {l1 l2 l : List α} {a : α}
    (h : List.Interleaving l1 l2 (l ++ [a])) :
    (∃ l1', l1 = l1' ++ [a] ∧ List.Interleaving l1' l2 l) ∨
    (∃ l2', l2 = l2' ++ [a] ∧ List.Interleaving l1 l2' l) := by
-- BEGIN PROOF
  induction l generalizing l1 l2 with
  | nil =>
    simp at h
    rcases h.singleton_iff with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨[], by simp [h1], by rw [h2]; exact .nil⟩
    · exact Or.inr ⟨[], by simp [h2], by rw [h1]; exact .nil⟩
  | cons x xs ih =>
    rcases h.cons_inv with ⟨l1', hl1, hint⟩ | ⟨l2', hl2, hint⟩
    · rcases ih hint with ⟨l1'', hl1'', hint'⟩ | ⟨l2'', hl2'', hint'⟩
      · exact Or.inl ⟨x :: l1'', by rw [hl1, hl1'']; simp, .left x hint'⟩
      · exact Or.inr ⟨l2'', hl2'', by rw [hl1]; exact .left x hint'⟩
    · rcases ih hint with ⟨l1'', hl1'', hint'⟩ | ⟨l2'', hl2'', hint'⟩
      · exact Or.inl ⟨l1'', hl1'', by rw [hl2]; exact .right x hint'⟩
      · exact Or.inr ⟨x :: l2'', by rw [hl2, hl2'']; simp, .right x hint'⟩

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Swap two adjacent elements in the combined list.
Given Interleaving l1 l2 (pre ++ [a, b] ++ suf), produce
Interleaving l1' l2' (pre ++ [b, a] ++ suf) where l1' and l2'
have the same members as l1 and l2 respectively. -/
theorem Interleaving.swap_mid {α : Type}
    {l1 l2 : List α} {pre : List α} {a b : α} {suf : List α}
    (h : List.Interleaving l1 l2 (pre ++ [a, b] ++ suf)) :
    ∃ l1' l2', List.Interleaving l1' l2' (pre ++ [b, a] ++ suf) ∧
    (∀ x, x ∈ l1' → x ∈ l1) ∧ (∀ x, x ∈ l2' → x ∈ l2) ∧
    (∀ x, x ∈ l1 → x ∈ l1') ∧ (∀ x, x ∈ l2 → x ∈ l2') := by
-- BEGIN PROOF
  induction pre generalizing l1 l2 with
  | nil =>
    simp only [List.nil_append] at h ⊢
    rcases h.cons_inv with ⟨la, hla, ha⟩ | ⟨la, hla, ha⟩
    · rcases ha.cons_inv with ⟨lb, hlb, hb⟩ | ⟨lb, hlb, hb⟩
      · -- both a,b in l1
        refine ⟨b :: a :: lb, l2, .left b (.left a hb), ?_, fun x hx => hx, ?_, fun x hx => hx⟩
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · subst hla; subst hlb; exact List.Mem.tail _ (List.Mem.head _)
          · subst hla; exact List.Mem.head _
          · subst hla; subst hlb; exact List.Mem.tail _ (List.Mem.tail _ hx)
        · intro x hx
          subst hla
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inr (Or.inl rfl)
          · subst hlb; simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact Or.inl rfl
            · exact Or.inr (Or.inr hx)
      · -- a in l1, b in l2
        subst hla; subst hlb
        exact ⟨a :: la, b :: lb, .right b (.left a hb),
          fun x hx => hx, fun x hx => hx, fun x hx => hx, fun x hx => hx⟩
    · rcases ha.cons_inv with ⟨lb, hlb, hb⟩ | ⟨lb, hlb, hb⟩
      · -- a in l2, b in l1
        subst hlb; subst hla
        exact ⟨b :: lb, a :: la, .left b (.right a hb),
          fun x hx => hx, fun x hx => hx, fun x hx => hx, fun x hx => hx⟩
      · -- both a,b in l2
        refine ⟨l1, b :: a :: lb, .right b (.right a hb), fun x hx => hx, ?_, fun x hx => hx, ?_⟩
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · subst hla; subst hlb; exact List.Mem.tail _ (List.Mem.head _)
          · subst hla; exact List.Mem.head _
          · subst hla; subst hlb; exact List.Mem.tail _ (List.Mem.tail _ hx)
        · intro x hx
          subst hla
          simp only [List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inr (Or.inl rfl)
          · subst hlb; simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact Or.inl rfl
            · exact Or.inr (Or.inr hx)
  | cons x xs ih =>
    simp only [List.cons_append] at h ⊢
    rcases h.cons_inv with ⟨l1', hl1, hint⟩ | ⟨l2', hl2, hint⟩
    · obtain ⟨l1'', l2'', hint', hm1, hm2, hm1', hm2'⟩ := ih hint
      refine ⟨x :: l1'', l2'', .left x hint', ?_, hm2, ?_, hm2'⟩
      · intro y hy; subst hl1; simp only [List.mem_cons] at hy ⊢
        rcases hy with rfl | hy'
        · exact Or.inl rfl
        · exact Or.inr (hm1 y hy')
      · intro y hy; subst hl1; simp only [List.mem_cons] at hy ⊢
        rcases hy with rfl | hy'
        · exact Or.inl rfl
        · exact Or.inr (hm1' y hy')
    · obtain ⟨l1'', l2'', hint', hm1, hm2, hm1', hm2'⟩ := ih hint
      refine ⟨l1'', x :: l2'', .right x hint', hm1, ?_, hm1', ?_⟩
      · intro y hy; subst hl2; simp only [List.mem_cons] at hy ⊢
        rcases hy with rfl | hy'
        · exact Or.inl rfl
        · exact Or.inr (hm2 y hy')
      · intro y hy; subst hl2; simp only [List.mem_cons] at hy ⊢
        rcases hy with rfl | hy'
        · exact Or.inl rfl
        · exact Or.inr (hm2' y hy')

end List
end LCS.CutElim.Interpolation
end

section
namespace LCS.CutElim.Interpolation
open Classical
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen.Hintikka

/-- The designated falsum constant ⊥ for LK⊥ and LKₑ,⊥, encoded as a
nullary predicate symbol applied to the empty term vector. -/
@[blueprint "chap6__lemma_6_5_4"]
def botFormula {L : Language} (botP : L.predSymbols) (hArity : L.predArity botP = 0) : FormulaN L :=
  FormulaN.predN botP (hArity ▸ Fin.elim0)

-- ===================================================================
-- Lemma 6.5.2 (required def): formulaPredSymbolsN
-- ===================================================================

/-- Lemma 6.5.2 (required): The set of predicate symbols occurring in
a formula, extracted as the third component of formulaPredSymbolsN. -/
@[blueprint "chap6__lemma_6_5_2"]
def formulaPredSymbolsN {L : Language} : FormulaN L → Set L.predSymbols
  | .predN P _ => fun Q => Q = P
  | .eq_ _ _ _ => ∅
  | .neg A => formulaPredSymbolsN A
  | .conj A B => formulaPredSymbolsN A ∪ formulaPredSymbolsN B
  | .disj A B => formulaPredSymbolsN A ∪ formulaPredSymbolsN B
  | .impl A B => formulaPredSymbolsN A ∪ formulaPredSymbolsN B
  | .all _ A => formulaPredSymbolsN A
  | .ex _ A => formulaPredSymbolsN A

-- ===================================================================
-- Lemma 6.5.2 (required def): formulaConstSymbolsN
-- ===================================================================

/-- Lemma 6.5.2 (required def): The set of constant symbols
occurring in a term, recursing through subterms. -/
@[blueprint "chap6__lemma_6_5_2"]
def termConstSymbols {L : Language} : Term L → Set L.constSymbols
  | .var _ => ∅
  | .const c => fun d => d = c
  | .func _ ts => fun c => ∃ i, termConstSymbols (ts i) c

/-- Lemma 6.5.2 (required def): The set of constant symbols
occurring in a formula, recursing through subformulae and
subterms. -/
@[blueprint "chap6__lemma_6_5_2"]
def formulaConstSymbolsN {L : Language} : FormulaN L → Set L.constSymbols
  | .predN _ ts => fun c => ∃ i, termConstSymbols (ts i) c
  | .eq_ _ t1 t2 => termConstSymbols t1 ∪ termConstSymbols t2
  | .neg A => formulaConstSymbolsN A
  | .conj A B => formulaConstSymbolsN A ∪ formulaConstSymbolsN B
  | .disj A B => formulaConstSymbolsN A ∪ formulaConstSymbolsN B
  | .impl A B => formulaConstSymbolsN A ∪ formulaConstSymbolsN B
  | .all _ A => formulaConstSymbolsN A
  | .ex _ A => formulaConstSymbolsN A

/-- Predicate symbols occurring in a formula, with `none` denoting equality
and `some P` denoting an ordinary predicate symbol. -/
@[blueprint "chap6__theorem_6_5_1"]
def formulaPredSymbolsWithEqN {L : Language} : FormulaN L → Set (Option L.predSymbols)
  | .predN P _ => fun Q => Q = some P
  | .eq_ _ _ _ => fun Q => Q = none
  | .neg A => formulaPredSymbolsWithEqN A
  | .conj A B => formulaPredSymbolsWithEqN A ∪ formulaPredSymbolsWithEqN B
  | .disj A B => formulaPredSymbolsWithEqN A ∪ formulaPredSymbolsWithEqN B
  | .impl A B => formulaPredSymbolsWithEqN A ∪ formulaPredSymbolsWithEqN B
  | .all _ A => formulaPredSymbolsWithEqN A
  | .ex _ A => formulaPredSymbolsWithEqN A

/-- A validity interpolant of A ⊃ B has both implications valid, and its
free variables, predicates (including equality), and constants common to A and B. -/
@[blueprint "chap6__theorem_6_5_1"]
def IsValidInterpolant {L : Language} (A B I : FormulaN L) : Prop :=
  universallyValidN (A.impl I) ∧ universallyValidN (I.impl B) ∧
  (formulaFVN I ⊆ formulaFVN A ∩ formulaFVN B) ∧
  (formulaPredSymbolsWithEqN I ⊆ formulaPredSymbolsWithEqN A ∩
    formulaPredSymbolsWithEqN B) ∧
  (formulaConstSymbolsN I ⊆ formulaConstSymbolsN A ∩ formulaConstSymbolsN B)

/-- A validity interpolant with equality exempt from the common-predicate
condition, as in the equality witness of §6.5.1. -/
@[blueprint "chap6__theorem_6_5_1"]
def IsValidInterpolantEq {L : Language} (A B I : FormulaN L) : Prop :=
  universallyValidN (A.impl I) ∧ universallyValidN (I.impl B) ∧
  (formulaFVN I ⊆ formulaFVN A ∩ formulaFVN B) ∧
  (formulaPredSymbolsN I ⊆ formulaPredSymbolsN A ∩ formulaPredSymbolsN B) ∧
  (formulaConstSymbolsN I ⊆ formulaConstSymbolsN A ∩ formulaConstSymbolsN B)

/-- Validity with a designated nullary symbol interpreted as the genuine
logical constant ⊥: every structure in the quantification makes it false. -/
@[blueprint "chap6__theorem_6_5_1"]
def universallyValidBotN {L : Language} (botP : L.predSymbols)
    (hBot : L.predArity botP = 0) (A : FormulaN L) : Prop :=
  ∀ M : Structure L, (∀ s, ¬ formulaEvalN M (botFormula botP hBot) s) → validInN M A

/-- A validity interpolant in a language with a genuine falsum constant.
The designated nullary symbol is exempt from the common-predicate condition;
equality is counted, and validity fixes the designated symbol to false. -/
@[blueprint "chap6__theorem_6_5_1"]
def IsValidInterpolantBot {L : Language} (botP : L.predSymbols)
    (hBot : L.predArity botP = 0) (A B I : FormulaN L) : Prop :=
  universallyValidBotN botP hBot (A.impl I) ∧
  universallyValidBotN botP hBot (I.impl B) ∧
  (formulaFVN I ⊆ formulaFVN A ∩ formulaFVN B) ∧
  (∀ R, R ∈ formulaPredSymbolsWithEqN I → R ≠ some botP →
    R ∈ formulaPredSymbolsWithEqN A ∩ formulaPredSymbolsWithEqN B) ∧
  (formulaConstSymbolsN I ⊆ formulaConstSymbolsN A ∩ formulaConstSymbolsN B)

/-- Without equality or a falsum constant, the valid implication
(P ⊃ P) ⊃ (Q ⊃ Q), for distinct nullary predicates, has no validity interpolant. -/
@[attach_debt, blueprint "chap6__theorem_6_5_1"]
theorem interpolant_language_dependence {L : Language} (hL : L.withoutEquality)
    (P Q : L.predSymbols) (hPQ : P ≠ Q)
    (hP : L.predArity P = 0) (hQ : L.predArity Q = 0) :
    let p := FormulaN.predN P (hP ▸ Fin.elim0)
    let q := FormulaN.predN Q (hQ ▸ Fin.elim0)
    universallyValidN ((p.impl p).impl (q.impl q)) ∧
      ¬ ∃ I, IsValidInterpolant (p.impl p) (q.impl q) I 

/-- With equality exempt from the common-predicate condition,
∀x(x ≐ x) interpolates (P ⊃ P) ⊃ (Q ⊃ Q). -/
@[blueprint "chap6__theorem_6_5_1"]
theorem interpolant_equality_witness {L : Language} (hEq : L.hasEquality = true)
    (P Q : L.predSymbols) (hP : L.predArity P = 0) (hQ : L.predArity Q = 0)
    (x : Nat) :
    let p := FormulaN.predN P (hP ▸ Fin.elim0)
    let q := FormulaN.predN Q (hQ ▸ Fin.elim0)
    IsValidInterpolantEq (p.impl p) (q.impl q)
      (.all x (.eq_ hEq (.var x) (.var x))) 

/-- With a genuine falsum constant exempt from predicate occurrences,
¬⊥ interpolates (P ⊃ P) ⊃ (Q ⊃ Q). -/
@[blueprint "chap6__theorem_6_5_1"]
theorem interpolant_true_witness {L : Language} (botP : L.predSymbols)
    (hBot : L.predArity botP = 0) (P Q : L.predSymbols)
    (hP : L.predArity P = 0) (hQ : L.predArity Q = 0) :
    let p := FormulaN.predN P (hP ▸ Fin.elim0)
    let q := FormulaN.predN Q (hQ ▸ Fin.elim0)
    IsValidInterpolantBot botP hBot (p.impl p) (q.impl q)
      (.neg (botFormula botP hBot)) 

-- ===================================================================
-- Lemma 6.5.2 (required def): listFormulaPredSymbols
-- ===================================================================

/-- Lemma 6.5.2 (required def): The set of predicate symbols
occurring in a list of formulae. Used in `IsInterpolant` to express
that the interpolant's predicate symbols appear in both sides of the
partition. -/
@[blueprint "chap6__lemma_6_5_2"]
def listFormulaPredSymbols {L : Language}
    (fs : List (FormulaN L)) : Set L.predSymbols :=
  fun P => ∃ A ∈ fs, formulaPredSymbolsN A P

-- ===================================================================
-- Lemma 6.5.2 (helper def): listFormulaConstSymbols
-- ===================================================================

/-- Lemma 6.5.2 (required def): The set of constant symbols
occurring in a list of formulae. Used in `IsInterpolant` to express
that the interpolant's constant symbols appear in both sides of the
partition. -/
@[blueprint "chap6__lemma_6_5_2"]
def listFormulaConstSymbols {L : Language}
    (fs : List (FormulaN L)) : Set L.constSymbols :=
  fun c => ∃ A ∈ fs, formulaConstSymbolsN A c

-- ===================================================================
-- Lemma 6.5.2 (helper def): listFormulaFV
-- ===================================================================

/-- Lemma 6.5.2 (required def): The set of free variables occurring
in a list of formulae. Used in `IsInterpolant` to express that the
interpolant's free variables appear in both sides of the
partition. -/
@[blueprint "chap6__lemma_6_5_2"]
def listFormulaFV {L : Language}
    (fs : List (FormulaN L)) : Set Nat :=
  fun v => ∃ A ∈ fs, formulaFVN A v

-- ===================================================================
-- Lemma 6.5.4 (shared definition): isLKBotAxiom
-- ===================================================================

/-- An LK⊥ axiom over a language with or without equality is either
an ordinary LK axiom or the falsum axiom ⊥ →. -/
@[blueprint "chap6__lemma_6_5_4"]
def isLKBotAxiom {L : Language} (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) (s : Sequent L) : Prop :=
  isFOLKAxiom s ∨ (s.antecedent = [botFormula botP hBotArity] ∧ s.succedent = [])

-- ===================================================================
-- Lemma 6.5.4 (shared definition): FOLKBotProofTree (indexed)
-- ===================================================================

/-- LK⊥ proof trees over a language with or without equality, indexed
by conclusion sequent. The leaves are ordinary LK axioms or ⊥ →.
These trees also serve the equality interpolation construction. -/
@[blueprint "chap6__lemma_6_5_4"]
inductive FOLKBotProofTree {L : Language} (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) : Sequent L → Type where
  | axiom_ (s : Sequent L) (h : isLKBotAxiom botP hBotArity s) : FOLKBotProofTree botP hBotArity s
  | onePremise {prem conc : Sequent L} (rule : FOLKStep1 prem conc) (t : FOLKBotProofTree botP hBotArity prem) : FOLKBotProofTree botP hBotArity conc
  | twoPremise {prem1 prem2 conc : Sequent L} (rule : FOLKStep2 prem1 prem2 conc) (t1 : FOLKBotProofTree botP hBotArity prem1) (t2 : FOLKBotProofTree botP hBotArity prem2) : FOLKBotProofTree botP hBotArity conc

end LCS.CutElim.Interpolation
end

section
namespace LCS.CutElim.Interpolation
open Classical
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen.Hintikka
namespace FOLKBotProofTree
-- ATTACH-BLOCKER: variable
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Lemma 6.5.2 (companion): Returns the sequent labeling the root
of the LK_bot proof tree. -/
def conclusion {s : Sequent L} (_ : FOLKBotProofTree botP hBotArity s) : Sequent L := s

-- ATTACH-BLOCKER: section variables: helper requires front context
@[simp]
theorem conclusion_eq {s : Sequent L} (t : FOLKBotProofTree botP hBotArity s) : t.conclusion = s := rfl

-- ===================================================================
-- Lemma 6.5.4 (shared definition): FOLKBotProofTree.isCutFree
-- ===================================================================

/-- An LK⊥ proof tree is cut-free iff every rule in it is cut-free.
This predicate applies to languages with or without equality. -/
@[blueprint "chap6__lemma_6_5_4"]
def isCutFree : {s : Sequent L} → FOLKBotProofTree botP hBotArity s → Prop
  | _, .axiom_ _ _ => True
  | _, .onePremise _ t => t.isCutFree
  | _, .twoPremise r t1 t2 =>
    (match r with | .cut .. => False | _ => True) ∧ t1.isCutFree ∧ t2.isCutFree

end FOLKBotProofTree
end LCS.CutElim.Interpolation
end

section
namespace LCS.CutElim.Interpolation
open Classical
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen.Hintikka

/-- A sequent is LK⊥-provable if it has an LK⊥ proof tree, over a
language with or without equality. -/
@[blueprint "chap6__lemma_6_5_4"]
def lkBotProvable {L : Language} (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) (s : Sequent L) : Prop :=
  Nonempty (FOLKBotProofTree botP hBotArity s)

-- ===================================================================
-- Lemma 6.5.2: LK⊥ over a language without equality
-- ===================================================================

/-- The falsum constant ⊥ over a language without equality. -/
@[blueprint "chap6__lemma_6_5_2"]
abbrev botFormulaNoEq {L : Language} (_hL : L.withoutEquality)
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) : FormulaN L :=
  botFormula botP hBotArity

/-- LK⊥ axioms over a language without equality. -/
@[blueprint "chap6__lemma_6_5_2"]
abbrev isLKBotAxiomNoEq {L : Language} (_hL : L.withoutEquality)
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) (s : Sequent L) : Prop :=
  isLKBotAxiom botP hBotArity s

/-- Indexed LK⊥ proof trees over a language without equality. -/
@[blueprint "chap6__lemma_6_5_2"]
abbrev FOLKBotProofTreeNoEq {L : Language} (_hL : L.withoutEquality)
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) : Sequent L → Type :=
  FOLKBotProofTree botP hBotArity

/-- Cut-freeness of an LK⊥ proof tree over a language without equality. -/
@[blueprint "chap6__lemma_6_5_2"]
abbrev FOLKBotProofTreeNoEq.isCutFree {L : Language} (hL : L.withoutEquality)
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0} {s : Sequent L}
    (t : FOLKBotProofTreeNoEq hL botP hBotArity s) : Prop :=
  FOLKBotProofTree.isCutFree t

/-- LK⊥ provability over a language without equality. -/
@[blueprint "chap6__lemma_6_5_2"]
abbrev lkBotProvableNoEq {L : Language} (_hL : L.withoutEquality)
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) (s : Sequent L) : Prop :=
  lkBotProvable botP hBotArity s

/-- Cut elimination for LK⊥ over a language without equality: under the
§6.1 end-sequent convention that no variable occurs both free and bound
anywhere in the sequent, provability is equivalent to the existence of a
cut-free LK⊥ proof of the same sequent. -/
@[attach_debt, blueprint "chap6__lemma_6_5_2"]
theorem lkBot_cut_elimination {L : Language} [Countable (Term L)]
    (hL : L.withoutEquality) (botP : L.predSymbols)
    (hBotArity : L.predArity botP = 0) (s : Sequent L)
    (hCross : crossNoFreeBound s) :
    lkBotProvable botP hBotArity s ↔
      ∃ t : FOLKBotProofTree botP hBotArity s, t.isCutFree 

-- ===================================================================
-- Helper: folkToBot — convert FOLK proof tree to FOLKBot proof tree
-- ===================================================================

-- retained: used by LCS.CutElim.Interpolation.KeyLemma
/-- Convert an indexed LK proof tree to an indexed LKbot proof tree. Every LK axiom
(identity: [A] -> [A]) is also an LKbot axiom (via the left disjunct
of isLKBotAxiom). -/
def folkToBot {L : Language} (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) {s : Sequent L} :
    LCS.CutElim.LK.FOLKProofTree s → FOLKBotProofTree botP hBotArity s
  | .axiom_ s h => .axiom_ s (Or.inl h)
  | .onePremise rule t => .onePremise rule (folkToBot botP hBotArity t)
  | .twoPremise rule t1 t2 => .twoPremise rule (folkToBot botP hBotArity t1) (folkToBot botP hBotArity t2)



-- retained: used by LCS.CutElim.Interpolation.KeyLemma
/-- folkToBot preserves cut-freeness: if an LK proof tree is
cut-free, then the corresponding LKbot proof tree is also cut-free. -/
theorem folkToBot_isCutFree {L : Language} (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) {s : Sequent L}
    (T : LCS.CutElim.LK.FOLKProofTree s) (hcf : T.isCutFree) :
    (folkToBot botP hBotArity T).isCutFree := by
-- BEGIN PROOF
  induction T with
  | axiom_ s h => trivial
  | onePremise rule t ih =>
    simp only [folkToBot, FOLKBotProofTree.isCutFree]
    exact ih (by simp only [LCS.CutElim.LK.FOLKProofTree.isCutFree] at hcf; exact hcf)
  | twoPremise rule t1 t2 ih1 ih2 =>
    simp only [folkToBot, FOLKBotProofTree.isCutFree]
    constructor
    · cases rule <;> simp only [LCS.CutElim.LK.FOLKProofTree.isCutFree] at hcf ⊢ <;> exact hcf.1
    · exact ⟨ih1 (by simp only [LCS.CutElim.LK.FOLKProofTree.isCutFree] at hcf; exact hcf.2.1),
             ih2 (by simp only [LCS.CutElim.LK.FOLKProofTree.isCutFree] at hcf; exact hcf.2.2)⟩

-- retained: used by LCS.CutElim.Interpolation.KeyLemma
/-- LK-provability implies LKbot-provability. -/
theorem folkProvable_to_lkBotProvable {L : Language}
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (s : Sequent L) (h : folkProvable s) : lkBotProvable botP hBotArity s := by
  obtain ⟨t⟩ := h; exact ⟨folkToBot botP hBotArity t⟩

-- retained: used by LCS.CutElim.Interpolation.KeyLemma
/-- Lemma 6.5.2 (required helper): Cut-free LK-provability implies
cut-free LKbot proof tree existence. Used by
`interpolation_key_lemma_witness_cutFree` to convert the cut-free provability
hypothesis into a concrete cut-free LKbot proof tree for the
inductive argument. -/
theorem folkCutFreeProvable_to_lkBotCutFree {L : Language}
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (s : Sequent L) (h : folkCutFreeProvable s) :
    ∃ (t : FOLKBotProofTree botP hBotArity s), t.isCutFree :=
-- BEGIN PROOF
by
  obtain ⟨t, hcf⟩ := h
  exact ⟨folkToBot botP hBotArity t, folkToBot_isCutFree botP hBotArity t hcf⟩

-- ===================================================================
-- Lemma 6.5.2 (required structure): SequentPartition
-- ===================================================================

/-- Lemma 6.5.2 (required): A partition of a sequent Gamma -> Delta
is a quadruple <Gamma_1, Delta_1, Gamma_2, Delta_2> where
(Gamma_1, Gamma_2) are disjoint subsequences of Gamma whose
interleaving gives Gamma, and similarly (Delta_1, Delta_2) are
disjoint subsequences of Delta whose interleaving gives Delta. -/
@[blueprint "chap6__lemma_6_5_2"]
structure SequentPartition {L : Language} (s : Sequent L) where
  /-- The first partition of the antecedent -/
  gamma1 : List (FormulaN L)
  /-- The first partition of the succedent -/
  delta1 : List (FormulaN L)
  /-- The second partition of the antecedent -/
  gamma2 : List (FormulaN L)
  /-- The second partition of the succedent -/
  delta2 : List (FormulaN L)
  /-- The antecedent is an interleaving of gamma1 and gamma2 -/
  gamma_partition :
    List.Interleaving gamma1 gamma2 s.antecedent
  /-- The succedent is an interleaving of delta1 and delta2 -/
  delta_partition :
    List.Interleaving delta1 delta2 s.succedent

-- ===================================================================

-- ===================================================================
-- Lemma 6.5.2 (required structure): IsInterpolant
-- ===================================================================

/-- Lemma 6.5.2 (required): A formula C is an interpolant of a
partition <Gamma_1, Delta_1, Gamma_2, Delta_2> of a sequent if:
(i) Gamma_1 -> Delta_1, C and C, Gamma_2 -> Delta_2 are
LK_bot-provable, and (ii) all predicate symbols (except falsum),
constant symbols, and free variables in C occur both in
Gamma_1 union Delta_1 and in Gamma_2 union Delta_2. -/
@[blueprint "chap6__lemma_6_5_2"]
structure IsInterpolant {L : Language} (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) {s : Sequent L}
    (p : SequentPartition s) (C : FormulaN L) : Prop where
  /-- Gamma_1 -> Delta_1, C is LK_bot-provable -/
  left_provable :
    lkBotProvable botP hBotArity
      { antecedent := p.gamma1
        succedent := p.delta1 ++ [C] }
  /-- C, Gamma_2 -> Delta_2 is LK_bot-provable -/
  right_provable :
    lkBotProvable botP hBotArity
      { antecedent := [C] ++ p.gamma2
        succedent := p.delta2 }
  /-- All predicate symbols in C EXCEPT ⊥ occur in both sides of the
      partition. Textbook Lem 6.5.2(ii) explicitly excludes ⊥: "all
      predicate symbols (except for ⊥)". Without this exception the
      axiom case C = ⊥ would fail its own pred_common obligation. -/
  pred_common : ∀ P, P ∈ formulaPredSymbolsN C → P ≠ botP →
    P ∈ listFormulaPredSymbols (p.gamma1 ++ p.delta1) ∧
    P ∈ listFormulaPredSymbols (p.gamma2 ++ p.delta2)
  /-- All constant symbols in C occur in both sides of the
      partition -/
  const_common :
    formulaConstSymbolsN C ⊆
      listFormulaConstSymbols (p.gamma1 ++ p.delta1) ∩
      listFormulaConstSymbols (p.gamma2 ++ p.delta2)
  /-- All free variables in C occur in both sides of the
      partition -/
  fv_common :
    formulaFVN C ⊆
      listFormulaFV (p.gamma1 ++ p.delta1) ∩
      listFormulaFV (p.gamma2 ++ p.delta2)
  /-- If all partition formulas have no eq_, the interpolant has no eq_ -/
  no_eq : (∀ A ∈ p.gamma1 ++ p.delta1 ++ p.gamma2 ++ p.delta2, formulaNoEq A) →
    formulaNoEq C

-- ===================================================================
-- Theorem 6.5.1 (required structure): IsImplicationInterpolant
-- ===================================================================

/-- Theorem 6.5.1 (required): A formula C is an interpolant of an
implication A implies B if: (1) A implies C is LK-provable
(i.e., [A] -> [C] is provable), (2) C implies B is LK-provable
(i.e., [C] -> [B] is provable), and (3) all predicate symbols,
constant symbols, and free variables in C occur in both A and B. -/
@[blueprint "chap6__theorem_6_5_1"]
structure IsImplicationInterpolant {L : Language}
    (A B C : FormulaN L) : Prop where
  /-- A implies C is LK-provable -/
  left_provable :
    folkProvable { antecedent := [A], succedent := [C] }
  /-- C implies B is LK-provable -/
  right_provable :
    folkProvable { antecedent := [C], succedent := [B] }
  /-- All predicate symbols in C occur in both A and B -/
  pred_common :
    formulaPredSymbolsN C ⊆
      formulaPredSymbolsN A ∩ formulaPredSymbolsN B
  /-- All constant symbols in C occur in both A and B -/
  const_common :
    formulaConstSymbolsN C ⊆
      formulaConstSymbolsN A ∩ formulaConstSymbolsN B
  /-- All free variables in C occur in both A and B -/
  fv_common :
    formulaFVN C ⊆ formulaFVN A ∩ formulaFVN B

-- ===================================================================
-- Example 6.5.1 (companion type): InterpExPred
-- ===================================================================

/-- Example 6.5.1 (companion type): Predicate symbols for the
interpolation example: P (unary), Q (unary), S (unary). -/
@[blueprint "chap6__example_6_5_1"]
inductive InterpExPred : Type where
  | P : InterpExPred
  | Q : InterpExPred
  | S_ : InterpExPred

-- ===================================================================
-- Example 6.5.1 (companion type): InterpExConst
-- ===================================================================

/-- Example 6.5.1 (companion type): Constant symbols for the
interpolation example: a and b. -/
@[blueprint "chap6__example_6_5_1"]
inductive InterpExConst : Type where
  | a : InterpExConst
  | b : InterpExConst

-- ===================================================================
-- Example 6.5.1 (companion def): interpExLanguage
-- ===================================================================

/-- Example 6.5.1 (companion): The first-order language with unary
predicate symbols P, Q, S (each of arity 1), constant symbols a and b,
no function symbols, and no equality. -/
@[blueprint "chap6__example_6_5_1"]
def interpExLanguage : Language where
  funSymbols := Empty
  funArity := fun e => e.elim
  constSymbols := InterpExConst
  predSymbols := InterpExPred
  predArity := fun | .P => 1 | .Q => 1 | .S_ => 1
  hasEquality := false

-- ===================================================================
-- Example 6.5.1 (companion def): interpExAntecedent
-- ===================================================================

/-- Example 6.5.1 (companion): The formula A = P(a) /\ forall x Q(x),
the antecedent of the example implication. Variable x is encoded as
variable 0. -/
@[blueprint "chap6__example_6_5_1"]
def interpExAntecedent : FormulaN interpExLanguage :=
  .conj (.predN InterpExPred.P (fun _ => Term.const InterpExConst.a))
        (.all 0 (.predN InterpExPred.Q (fun _ => Term.var 0)))
-- ===================================================================
-- Example 6.5.1 (companion def): interpExConsequent
-- ===================================================================

/-- Example 6.5.1 (companion): The formula B = forall y S(y) \/ Q(b),
the consequent of the example implication. Variable y is encoded as
variable 1. -/
@[blueprint "chap6__example_6_5_1"]
def interpExConsequent : FormulaN interpExLanguage :=
  .disj (.all 1 (.predN InterpExPred.S_ (fun _ => Term.var 1)))
        (.predN InterpExPred.Q (fun _ => Term.const InterpExConst.b))
-- ===================================================================
-- Example 6.5.1 (companion def): interpExInterpolant
-- ===================================================================

/-- Example 6.5.1 (companion): The formula C = forall x Q(x), the
interpolant of the example implication. Q is the common predicate
symbol between A and B. -/
@[blueprint "chap6__example_6_5_1"]
def interpExInterpolant : FormulaN interpExLanguage :=
  .all 0 (.predN InterpExPred.Q (fun _ => Term.var 0))
-- ===================================================================
-- Example 6.5.1: interpolation_example
-- ===================================================================


/-- Example 6.5.1: ∀x Q(x) is an interpolant of
(P(a) ∧ ∀x Q(x)) ⊃ (∀y S(y) ∨ Q(b)). -/
@[blueprint "chap6__example_6_5_1" (main := true)]
theorem interpolation_example_spec : IsImplicationInterpolant
    interpExAntecedent interpExConsequent interpExInterpolant 

-- ===================================================================
-- Lemma 6.5.1: Variable and constant substitution in LK proof trees
-- ===================================================================

-- ===================================================================
-- Substitution infrastructure
-- ===================================================================

/-- Lemma 6.5.1 (required def): Apply variable substitution `[z/y]`
pointwise to every formula in the antecedent and succedent of a
sequent. -/
@[blueprint "chap6__lemma_6_5_1"]
def sequentSubstVar {L : Language}
    (s : Sequent L) (z y : Nat) : Sequent L :=
  { antecedent := s.antecedent.map (fun A => formulaSubstN A (.var z) y)
    succedent := s.succedent.map (fun A => formulaSubstN A (.var z) y) }

/-- Lemma 6.5.1 (required def): Replace every occurrence of the
constant symbol `c` in a term by the variable `z`. -/
@[blueprint "chap6__lemma_6_5_1"]
noncomputable def termSubstConst {L : Language}
    (t : Term L) (z : Nat) (c : L.constSymbols) : Term L :=
  match t with
  | .var x => .var x
  | .const c' => if c' = c then .var z else .const c'
  | .func f ts => .func f (fun i => termSubstConst (ts i) z c)

/-- Lemma 6.5.1 (required def): Replace every occurrence of the
constant symbol `c` in a formula by the variable `z`, recursing
through subformulae and subterms. -/
@[blueprint "chap6__lemma_6_5_1"]
noncomputable def formulaSubstConst {L : Language}
    (A : FormulaN L) (z : Nat) (c : L.constSymbols) : FormulaN L :=
  match A with
  | .predN P ts => .predN P (fun i => termSubstConst (ts i) z c)
  | .eq_ hL t1 t2 => .eq_ hL (termSubstConst t1 z c) (termSubstConst t2 z c)
  | .conj A B => .conj (formulaSubstConst A z c) (formulaSubstConst B z c)
  | .disj A B => .disj (formulaSubstConst A z c) (formulaSubstConst B z c)
  | .impl A B => .impl (formulaSubstConst A z c) (formulaSubstConst B z c)
  | .neg A => .neg (formulaSubstConst A z c)
  | .all x A => .all x (formulaSubstConst A z c)
  | .ex x A => .ex x (formulaSubstConst A z c)

-- retained: used by LCS.CutElim.Interpolation.InterpolantRepair
theorem formulaSubstConst_noEq {L : Language}
    (A : FormulaN L) (z : Nat) (c : L.constSymbols) (h : formulaNoEq A) :
    formulaNoEq (formulaSubstConst A z c) := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => exact trivial
  | eq_ _ _ _ => exact absurd h id
  | conj A B ihA ihB => simp [formulaSubstConst, formulaNoEq] at h ⊢; exact ⟨ihA h.1, ihB h.2⟩
  | disj A B ihA ihB => simp [formulaSubstConst, formulaNoEq] at h ⊢; exact ⟨ihA h.1, ihB h.2⟩
  | impl A B ihA ihB => simp [formulaSubstConst, formulaNoEq] at h ⊢; exact ⟨ihA h.1, ihB h.2⟩
  | neg A ih => simp [formulaSubstConst, formulaNoEq] at h ⊢; exact ih h
  | all _ A ih => simp [formulaSubstConst, formulaNoEq] at h ⊢; exact ih h
  | ex _ A ih => simp [formulaSubstConst, formulaNoEq] at h ⊢; exact ih h

/-- Lemma 6.5.1 (required def): Apply constant-for-variable
substitution `[z/c]` pointwise to every formula in the antecedent
and succedent of a sequent. -/
@[blueprint "chap6__lemma_6_5_1"]
noncomputable def sequentSubstConst {L : Language}
    (s : Sequent L) (z : Nat) (c : L.constSymbols) : Sequent L :=
  { antecedent := s.antecedent.map (fun A => formulaSubstConst A z c)
    succedent := s.succedent.map (fun A => formulaSubstConst A z c) }

end LCS.CutElim.Interpolation
end

section
namespace LCS.CutElim.Interpolation
open Classical
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen.Hintikka
section
-- ATTACH-BLOCKER: variable
variable (L : Language) (z : Nat) (c : L.constSymbols)

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem folkConst_termComm
    (u : Term L) (t : Term L) (x : Nat) (hzx : z ≠ x)
    : termSubstConst (termSubst u t x) z c = termSubst (termSubstConst u z c) (termSubstConst t z c) x := by
  induction u with
  | var v =>
    simp only [termSubst]
    by_cases hvx : v = x <;> simp_all [termSubstConst, termSubst]
  | const d =>
    simp only [termSubst, termSubstConst]
    by_cases hdc : d = c
    · subst hdc
      simp [termSubst, hzx]
    · simp [termSubst, hdc]
  | func f ts ih =>
    simp only [termSubst, termSubstConst]
    congr 1
    ext i
    exact ih i

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem folkConst_formulaComm
    (termComm : ∀ (u t : Term L) (x : Nat), z ≠ x → termSubstConst (termSubst u t x) z c = termSubst
      (termSubstConst u z c) (termSubstConst t z c) x) (A : FormulaN L) (t : Term L) (x : Nat) (hzx : z ≠ x)
    : formulaSubstConst (formulaSubstN A t x) z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t
      z c) x := by
  induction A with
  | predN P ts =>
    simp [formulaSubstN, formulaSubstConst]
    congr 1
    ext i
    exact termComm _ _ _ hzx
  | eq_ _ t₁ t₂ =>
    simp [formulaSubstN, formulaSubstConst, termComm t₁ t x hzx, termComm t₂ t x hzx]
  | conj A B ihA ihB =>
    simp [formulaSubstN, formulaSubstConst, ihA, ihB]
  | disj A B ihA ihB =>
    simp [formulaSubstN, formulaSubstConst, ihA, ihB]
  | impl A B ihA ihB =>
    simp [formulaSubstN, formulaSubstConst, ihA, ihB]
  | neg A ih =>
    simp [formulaSubstN, formulaSubstConst, ih]
  | all w A ih =>
    simp [formulaSubstN, formulaSubstConst]
    split <;> simp [formulaSubstConst, ih]
  | ex w A ih =>
    simp [formulaSubstN, formulaSubstConst]
    split <;> simp [formulaSubstConst, ih]

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem folkConst_termFreshAfterConst
    (t : Term L) (v : Nat) (hvz : v ≠ z) (h : ¬v ∈ termFV t)
    : ¬v ∈ termFV (termSubstConst t z c) := by
  induction t with
  | var w => exact h
  | const d =>
    simp only [termSubstConst]
    split
    · simp [termFV]
      exact hvz
    · exact fun hm => h hm
  | func f ts ih =>
    simp only [termSubstConst, termFV] at h ⊢
    intro ⟨i, hi⟩
    exact h ⟨i, (ih i (fun hc => h ⟨i, hc⟩)).elim hi⟩

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem folkConst_freeAfterConst
    (termFreshAfterConst : ∀ (t : Term L) (v : Nat), v ≠ z → ¬v ∈ termFV t → ¬v ∈ termFV (termSubstConst t z
      c)) (A : FormulaN L) (t : Term L) (x : Nat) (hfree : isFreeForN t x A) (hNoZ : ¬z ∈ formulaBVN A)
    : isFreeForN (termSubstConst t z c) x (formulaSubstConst A z c) := by
  induction A with
  | predN P ts => trivial
  | eq_ _ t₁ t₂ => trivial
  | conj A B ihA ihB =>
    exact ⟨ihA hfree.1 (fun h => hNoZ (Or.inl h)), ihB hfree.2 (fun h => hNoZ (Or.inr h))⟩
  | disj A B ihA ihB =>
    exact ⟨ihA hfree.1 (fun h => hNoZ (Or.inl h)), ihB hfree.2 (fun h => hNoZ (Or.inr h))⟩
  | impl A B ihA ihB =>
    exact ⟨ihA hfree.1 (fun h => hNoZ (Or.inl h)), ihB hfree.2 (fun h => hNoZ (Or.inr h))⟩
  | neg A ih =>
    exact ih hfree hNoZ
  | all w A ih =>
    simp only [formulaSubstConst, isFreeForN]
    simp only [isFreeForN] at hfree
    rcases hfree with hxw | ⟨hwtv, hff⟩
    · left
      exact hxw
    · have hzw : z ≠ w := fun h => hNoZ (Or.inr (h ▸ rfl))
      right
      exact ⟨termFreshAfterConst t w (Ne.symm hzw) hwtv, ih hff (fun h => hNoZ (Or.inl h))⟩
  | ex w A ih =>
    simp only [formulaSubstConst, isFreeForN]
    simp only [isFreeForN] at hfree
    rcases hfree with hxw | ⟨hwtv, hff⟩
    · left
      exact hxw
    · have hzw : z ≠ w := fun h => hNoZ (Or.inr (h ▸ rfl))
      right
      exact ⟨termFreshAfterConst t w (Ne.symm hzw) hwtv, ih hff (fun h => hNoZ (Or.inl h))⟩

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem folkConst_formulaFreshAfterConst
    (termFreshAfterConst : ∀ (t : Term L) (v : Nat), v ≠ z → ¬v ∈ termFV t → ¬v ∈ termFV (termSubstConst t z
      c)) (A : FormulaN L) (v : Nat) (hvz : v ≠ z) (h : ¬v ∈ formulaFVN A)
    : ¬v ∈ formulaFVN (formulaSubstConst A z c) := by
  induction A with
  | predN P ts =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro ⟨i, hi⟩
    exact h ⟨i, (termFreshAfterConst (ts i) v hvz (fun hm => h ⟨i, hm⟩)).elim hi⟩
  | eq_ _ t₁ t₂ =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro hm
    rcases hm with h₁ | h₂
    · exact (termFreshAfterConst t₁ v hvz (fun hm => h (Or.inl hm))).elim h₁
    · exact (termFreshAfterConst t₂ v hvz (fun hm => h (Or.inr hm))).elim h₂
  | conj A B ihA ihB =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro hm
    rcases hm with hA | hB
    · exact ihA (fun hm => h (Or.inl hm)) hA
    · exact ihB (fun hm => h (Or.inr hm)) hB
  | disj A B ihA ihB =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro hm
    rcases hm with hA | hB
    · exact ihA (fun hm => h (Or.inl hm)) hA
    · exact ihB (fun hm => h (Or.inr hm)) hB
  | impl A B ihA ihB =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro hm
    rcases hm with hA | hB
    · exact ihA (fun hm => h (Or.inl hm)) hA
    · exact ihB (fun hm => h (Or.inr hm)) hB
  | neg A ih =>
    simp only [formulaSubstConst, formulaFVN]
    exact ih h
  | all w A ih =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro ⟨hm, hne⟩
    exact ih (fun hm' => h ⟨hm', hne⟩) hm
  | ex w A ih =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro ⟨hm, hne⟩
    exact ih (fun hm' => h ⟨hm', hne⟩) hm

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem folkConst_sequentFreshAfterConst
    (formulaFreshAfterConst : ∀ (A : FormulaN L) (v : Nat), v ≠ z → ¬v ∈ formulaFVN A → ¬v ∈ formulaFVN
      (formulaSubstConst A z c)) (q : Sequent L) (e : Nat) (he : ∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) (hez : e ≠ z)
    : ∀ (F : FormulaN L), F ∈ (sequentSubstConst q z c).antecedent ++ (sequentSubstConst q z c).succedent → ¬e
      ∈ formulaFVN F := by
  intro F hF
  change F ∈ q.antecedent.map (fun A => formulaSubstConst A z c) ++
      q.succedent.map (fun A => formulaSubstConst A z c) at hF
  rcases List.mem_append.mp hF with hF | hF
  · rcases List.mem_map.mp hF with ⟨G, hG, rfl⟩
    have hmem : G ∈ q.antecedent ++ q.succedent := List.mem_append.mpr (Or.inl hG)
    exact formulaFreshAfterConst G e hez (he G hmem)
  · rcases List.mem_map.mp hF with ⟨G, hG, rfl⟩
    have hmem : G ∈ q.antecedent ++ q.succedent := List.mem_append.mpr (Or.inr hG)
    exact formulaFreshAfterConst G e hez (he G hmem)

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def folkConst_allLeft
    (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat), z ≠ x → formulaSubstConst (formulaSubstN A t x)
      z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A :
      FormulaN L) (t : Term L) (x : Nat), isFreeForN t x A → ¬z ∈ formulaBVN A → isFreeForN (termSubstConst t
      z c) x (formulaSubstConst A z c)) (t₀ : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ :
      List (FormulaN L)) (hfree : isFreeForN t₀ x A) (transformedTree : FOLKProofTree (sequentSubstConst
      (Sequent.mk (formulaSubstN A t₀ x :: Γ) (Δ)) z c)) (hRuleNO : (FOLKStep1.allLeft t₀ x A Γ Δ
      hfree).varNotOccurs z)
    : FOLKProofTree (sequentSubstConst (Sequent.mk (FormulaN.all x A :: Γ) (Δ)) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (termSubstConst t₀ z c) x (formulaSubstConst A z c) :=
    freeAfterConst A t₀ x hfree hNoZ
  have sub : FOLKProofTree (Sequent.mk (formulaSubstN (formulaSubstConst A z c) (termSubstConst t₀ z c) x ::
            Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))) := by
    simpa [sequentSubstConst, formulaComm A t₀ x hzx] using transformedTree
  simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise (FOLKStep1.allLeft
        (termSubstConst t₀ z c) x
        (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c)) hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def folkConst_allRight
    (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat), z ≠ x → formulaSubstConst (formulaSubstN A t x)
      z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A :
      FormulaN L) (t : Term L) (x : Nat), isFreeForN t x A → ¬z ∈ formulaBVN A → isFreeForN (termSubstConst t
      z c) x (formulaSubstConst A z c)) (sequentFreshAfterConst : ∀ (q : Sequent L) (e : Nat), (∀ (F :
      FormulaN L), F ∈ q.antecedent ++ q.succedent → ¬e ∈ formulaFVN F) → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstConst q z c).antecedent ++ (sequentSubstConst q z c).succedent → ¬e ∈ formulaFVN F) (e :
      Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfresh : ∀ (F :
      FormulaN L), F ∈ (Γ) ++ (Δ ++ [FormulaN.all x A]) → ¬e ∈ formulaFVN F) (hfree : isFreeForN (Term.var e)
      x A) (transformedTree : FOLKProofTree (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [formulaSubstN A
      (Term.var e) x])) z c)) (hRuleNO : (FOLKStep1.allRight e x A Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKProofTree (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [FormulaN.all x A])) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hze : z ≠ e := hRuleNO.2.2.1
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (.var e) x (formulaSubstConst A z c) := by
    simpa [termSubstConst] using freeAfterConst A (.var e) x hfree hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (Γ.map (fun G => formulaSubstConst G z c))
            (Δ.map (fun G => formulaSubstConst G z c) ++
              [FormulaN.all x (formulaSubstConst A z c)])).antecedent ++
          (Sequent.mk (Γ.map (fun G => formulaSubstConst G z c)) (Δ.map (fun G => formulaSubstConst G z c) ++
              [FormulaN.all x (formulaSubstConst A z c)])).succedent,
        e ∉ formulaFVN F := by
    simpa [sequentSubstConst, formulaSubstConst] using sequentFreshAfterConst
        (Sequent.mk Γ (Δ ++ [FormulaN.all x A])) e hfresh
        (Ne.symm hze)
  have sub : FOLKProofTree (Sequent.mk (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c) ++
            [formulaSubstN (formulaSubstConst A z c) (.var e) x])) := by
    simpa [sequentSubstConst, formulaComm A (.var e) x hzx, termSubstConst] using transformedTree
  simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise (FOLKStep1.allRight e x
        (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c))
        hfresh' hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def folkConst_exLeft
    (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat), z ≠ x → formulaSubstConst (formulaSubstN A t x)
      z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A :
      FormulaN L) (t : Term L) (x : Nat), isFreeForN t x A → ¬z ∈ formulaBVN A → isFreeForN (termSubstConst t
      z c) x (formulaSubstConst A z c)) (sequentFreshAfterConst : ∀ (q : Sequent L) (e : Nat), (∀ (F :
      FormulaN L), F ∈ q.antecedent ++ q.succedent → ¬e ∈ formulaFVN F) → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstConst q z c).antecedent ++ (sequentSubstConst q z c).succedent → ¬e ∈ formulaFVN F) (e :
      Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfresh : ∀ (F :
      FormulaN L), F ∈ (FormulaN.ex x A :: Γ) ++ (Δ) → ¬e ∈ formulaFVN F) (hfree : isFreeForN (Term.var e) x
      A) (transformedTree : FOLKProofTree (sequentSubstConst (Sequent.mk (formulaSubstN A (Term.var e) x :: Γ)
      (Δ)) z c)) (hRuleNO : (FOLKStep1.exLeft e x A Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKProofTree (sequentSubstConst (Sequent.mk (FormulaN.ex x A :: Γ) (Δ)) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hze : z ≠ e := hRuleNO.2.2.1
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (.var e) x (formulaSubstConst A z c) := by
    simpa [termSubstConst] using freeAfterConst A (.var e) x hfree hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (FormulaN.ex x (formulaSubstConst A z c) ::
              Γ.map (fun G => formulaSubstConst G z c))
            (Δ.map (fun G => formulaSubstConst G z c))).antecedent ++
          (Sequent.mk (FormulaN.ex x (formulaSubstConst A z c) :: Γ.map (fun G => formulaSubstConst G z c))
            (Δ.map (fun G => formulaSubstConst G z c))).succedent,
        e ∉ formulaFVN F := by
    simpa [sequentSubstConst, formulaSubstConst] using sequentFreshAfterConst
        (Sequent.mk (FormulaN.ex x A :: Γ) Δ) e hfresh
        (Ne.symm hze)
  have sub : FOLKProofTree (Sequent.mk (formulaSubstN (formulaSubstConst A z c) (.var e) x ::
            Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))) := by
    simpa [sequentSubstConst, formulaComm A (.var e) x hzx, termSubstConst] using transformedTree
  simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise (FOLKStep1.exLeft e x
        (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c))
        hfresh' hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def folkConst_exRight
    (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat), z ≠ x → formulaSubstConst (formulaSubstN A t x)
      z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A :
      FormulaN L) (t : Term L) (x : Nat), isFreeForN t x A → ¬z ∈ formulaBVN A → isFreeForN (termSubstConst t
      z c) x (formulaSubstConst A z c)) (t₀ : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ :
      List (FormulaN L)) (hfree : isFreeForN t₀ x A) (transformedTree : FOLKProofTree (sequentSubstConst
      (Sequent.mk (Γ) (Δ ++ [formulaSubstN A t₀ x])) z c)) (hRuleNO : (FOLKStep1.exRight t₀ x A Γ Δ
      hfree).varNotOccurs z)
    : FOLKProofTree (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [FormulaN.ex x A])) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (termSubstConst t₀ z c) x (formulaSubstConst A z c) :=
    freeAfterConst A t₀ x hfree hNoZ
  have sub : FOLKProofTree (Sequent.mk (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c) ++ [formulaSubstN (formulaSubstConst A z c)
              (termSubstConst t₀ z c) x])) := by
    simpa [sequentSubstConst, formulaComm A t₀ x hzx] using transformedTree
  simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise (FOLKStep1.exRight
        (termSubstConst t₀ z c) x
        (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c)) hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def folkConst_oneRule
    (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat), z ≠ x → formulaSubstConst (formulaSubstN A t x)
      z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A :
      FormulaN L) (t : Term L) (x : Nat), isFreeForN t x A → ¬z ∈ formulaBVN A → isFreeForN (termSubstConst t
      z c) x (formulaSubstConst A z c)) (sequentFreshAfterConst : ∀ (q : Sequent L) (e : Nat), (∀ (F :
      FormulaN L), F ∈ q.antecedent ++ q.succedent → ¬e ∈ formulaFVN F) → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstConst q z c).antecedent ++ (sequentSubstConst q z c).succedent → ¬e ∈ formulaFVN F) (q :
      Sequent L) (prem : Sequent L) (rule : FOLKStep1 prem q) (hRuleNO : rule.varNotOccurs z) (transformedTree
      : FOLKProofTree (sequentSubstConst prem z c))
    : FOLKProofTree (sequentSubstConst q z c) := by
  cases rule with
  | weakenLeft A Γ Δ =>
    simpa [sequentSubstConst] using FOLKProofTree.onePremise (FOLKStep1.weakenLeft (formulaSubstConst A z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | weakenRight A Γ Δ =>
    simpa [sequentSubstConst] using FOLKProofTree.onePremise (FOLKStep1.weakenRight (formulaSubstConst A z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | contractLeft A Γ Δ =>
    simpa [sequentSubstConst] using FOLKProofTree.onePremise (FOLKStep1.contractLeft (formulaSubstConst A z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | contractRight A Γ Δ =>
    simpa [sequentSubstConst] using FOLKProofTree.onePremise
        (FOLKStep1.contractRight (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | exchangeLeft Γ A B Δ Λ =>
    simpa [sequentSubstConst] using FOLKProofTree.onePremise (FOLKStep1.exchangeLeft
          (Γ.map (fun F => formulaSubstConst F z c))
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Δ.map (fun F => formulaSubstConst F z c))
          (Λ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | exchangeRight Γ Δ A B Λ =>
    simpa [sequentSubstConst] using FOLKProofTree.onePremise (FOLKStep1.exchangeRight
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Λ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | andLeftL A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise (FOLKStep1.andLeftL
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | andLeftR A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise (FOLKStep1.andLeftR
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | orRightL A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise (FOLKStep1.orRightL
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | orRightR A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise (FOLKStep1.orRightR
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | implRight A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise (FOLKStep1.implRight
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | negLeft A Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise
        (FOLKStep1.negLeft (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | negRight A Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.onePremise
        (FOLKStep1.negRight (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | allLeft t₀ x A Γ Δ hfree =>
    exact folkConst_allLeft L z c formulaComm freeAfterConst t₀ x A Γ Δ hfree transformedTree hRuleNO
  | allRight e x A Γ Δ hfresh hfree =>
    exact folkConst_allRight L z c formulaComm freeAfterConst sequentFreshAfterConst e x A Γ Δ hfresh hfree transformedTree hRuleNO
  | exLeft e x A Γ Δ hfresh hfree =>
    exact folkConst_exLeft L z c formulaComm freeAfterConst sequentFreshAfterConst e x A Γ Δ hfresh hfree transformedTree hRuleNO
  | exRight t₀ x A Γ Δ hfree =>
    exact folkConst_exRight L z c formulaComm freeAfterConst t₀ x A Γ Δ hfree transformedTree hRuleNO

-- ATTACH-BLOCKER: section variables: helper requires front context
noncomputable def folkConst_twoRule
    (q : Sequent L) (prem1 : Sequent L) (prem2 : Sequent L) (rule : FOLKStep2 prem1 prem2 q) (transformedTree₁
      : FOLKProofTree (sequentSubstConst prem1 z c)) (transformedTree₂ : FOLKProofTree (sequentSubstConst
      prem2 z c))
    : FOLKProofTree (sequentSubstConst q z c) := by
  cases rule with
  | cut A Γ Δ Λ Θ =>
    simpa [sequentSubstConst] using FOLKProofTree.twoPremise (FOLKStep2.cut (formulaSubstConst A z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
          (Λ.map (fun F => formulaSubstConst F z c))
          (Θ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree₁)
        (by simpa [sequentSubstConst] using transformedTree₂)
  | andRight A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.twoPremise (FOLKStep2.andRight
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree₁)
        (by simpa [sequentSubstConst] using transformedTree₂)
  | orLeft A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.twoPremise (FOLKStep2.orLeft
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree₁)
        (by simpa [sequentSubstConst] using transformedTree₂)
  | implLeft A B Γ Δ Λ Θ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKProofTree.twoPremise (FOLKStep2.implLeft
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
          (Λ.map (fun F => formulaSubstConst F z c))
          (Θ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree₁)
        (by simpa [sequentSubstConst] using transformedTree₂)

end
end LCS.CutElim.Interpolation
end

