import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import LCS.Propositional.Systems.G.Search
import LCS.Propositional.Systems.G.Search.Fairness
import Attach
import LCS.Propositional.Infinite.Sequents
import LCS.Propositional.Infinite.SearchTrees.ProofsStamp

/-! # Systematic trees of the infinite search (Definition 3.5.1)

The finite stages of the systematic deduction tree built by search:
nodes labelled by finite sequents, context-extension edges, leaf
substitution (dosubstitution), tree addresses and their basic lemmas.
-/
section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

/-- Append the two current heads to a finite label. -/
@[blueprint "chap3__definition_3_5_1"]
def extendSeq (s : Sequent)
    (newAnt newSuc : Option PropFormulaNormalized) : Sequent :=
  Sequent.mk (s.antecedent ++ newAnt.toList) (s.succedent ++ newSuc.toList)

/-- Finite stages of the systematic infinite search. Context introductions
are genuine edges; they are not Gentzen inferences or changes to old labels. -/
@[blueprint "chap3__definition_3_5_1"]
inductive InfDeductionTree : Sequent → Type where
  | leaf (s : Sequent) : InfDeductionTree s
  | onePremise {s p : Sequent} : GentzenStep1 p s →
      InfDeductionTree p → InfDeductionTree s
  | twoPremise {s p q : Sequent} : GentzenStep2 p q s →
      InfDeductionTree p → InfDeductionTree q → InfDeductionTree s
  | extend {s : Sequent} (newAnt newSuc : Option PropFormulaNormalized) :
      InfDeductionTree (extendSeq s newAnt newSuc) → InfDeductionTree s

namespace InfDeductionTree

@[blueprint "chap3__definition_3_5_1"]
def leaves : {s : Sequent} → InfDeductionTree s → List Sequent
  | _, .leaf s => [s]
  | _, .onePremise _ t => t.leaves
  | _, .twoPremise _ l r => l.leaves ++ r.leaves
  | _, .extend _ _ t => t.leaves

/-- Embed a finite Gentzen tree while keeping every label and rule. -/
@[blueprint "chap3__definition_3_5_1"]
def ofDeductionTree : {s : Sequent} → DeductionTree s → InfDeductionTree s
  | _, .leaf s => .leaf s
  | _, .onePremise rule t => .onePremise rule (ofDeductionTree t)
  | _, .twoPremise rule l r => .twoPremise rule (ofDeductionTree l) (ofDeductionTree r)

/-- Simultaneous substitution at the original leaves, in address order. -/
@[blueprint "chap3__definition_3_5_1"]
def bindLeaves (f : (s : Sequent) → InfDeductionTree s) :
    {s : Sequent} → InfDeductionTree s → InfDeductionTree s
  | _, .leaf s => f s
  | _, .onePremise rule t => .onePremise rule (bindLeaves f t)
  | _, .twoPremise rule l r => .twoPremise rule (bindLeaves f l) (bindLeaves f r)
  | _, .extend a b t => .extend a b (bindLeaves f t)

/-- Tree addresses use child 0 for a unary edge and children 0,1 for a fork. -/
@[blueprint "chap3__definition_3_5_1"]
def labelAt : {s : Sequent} → InfDeductionTree s → List Nat → Option Sequent
  | s, _, [] => some s
  | _, .leaf _, _ :: _ => none
  | _, .onePremise _ t, 0 :: p => t.labelAt p
  | _, .onePremise _ _, (_ + 1) :: _ => none
  | _, .twoPremise _ l _, 0 :: p => l.labelAt p
  | _, .twoPremise _ _ r, 1 :: p => r.labelAt p
  | _, .twoPremise _ _ _, (_ + 2) :: _ => none
  | _, .extend _ _ t, 0 :: p => t.labelAt p
  | _, .extend _ _ _, (_ + 1) :: _ => none

@[simp] theorem leaves_bindLeaves (f : (s : Sequent) → InfDeductionTree s)
    {s : Sequent} (t : InfDeductionTree s) :
    (bindLeaves f t).leaves = t.leaves.flatMap (fun s => (f s).leaves) := by
  induction t with
  | leaf => simp [bindLeaves, leaves]
  | onePremise _ _ ih => exact ih
  | twoPremise _ _ _ ih₁ ih₂ => simp [bindLeaves, leaves, ih₁, ih₂, List.flatMap_append]
  | extend _ _ _ ih => exact ih

/-- Grafting below leaves preserves every existing node and its address. -/
theorem labelAt_bindLeaves_preserves (f : (s : Sequent) → InfDeductionTree s)
    {s : Sequent} (t : InfDeductionTree s) (p : List Nat) (label : Sequent)
    (h : t.labelAt p = some label) :
    (t.bindLeaves f).labelAt p = some label := by
  induction t generalizing p with
  | leaf s =>
    cases p with
    | nil => simpa [labelAt, bindLeaves] using h
    | cons => simp [labelAt] at h
  | onePremise rule t ih =>
    cases p with
    | nil => exact h
    | cons i p =>
      cases i with
      | zero => exact ih p h
      | succ => simp [labelAt] at h
  | twoPremise rule l r ih₁ ih₂ =>
    cases p with
    | nil => exact h
    | cons i p =>
      cases i with
      | zero => exact ih₁ p h
      | succ i =>
        cases i with
        | zero => exact ih₂ p h
        | succ => simp [labelAt] at h
  | extend a b t ih =>
    cases p with
    | nil => exact h
    | cons i p =>
      cases i with
      | zero => exact ih p h
      | succ => simp [labelAt] at h

end InfDeductionTree

/-- Immediate directed steps on a search branch. -/
inductive InfBranchStep : Sequent → Sequent → Type where
  | onePremise {s p} : GentzenStep1 p s → InfBranchStep s p
  | leftPremise {s p q} : GentzenStep2 p q s → InfBranchStep s p
  | rightPremise {s p q} : GentzenStep2 p q s → InfBranchStep s q
  | extend (s) (a b) : InfBranchStep s (extendSeq s a b)
  | idle (s) : InfBranchStep s s

/-- Every actual parent-child edge carries its structural branch step. -/
theorem InfDeductionTree.branchStep_of_labels {root : Sequent}
    (tree : InfDeductionTree root) (p : List Nat) (i : Nat) {s c : Sequent}
    (hs : tree.labelAt p = some s) (hc : tree.labelAt (p ++ [i]) = some c) :
    Nonempty (InfBranchStep s c) := by
  induction tree generalizing p with
  | leaf root =>
    cases p <;> simp [InfDeductionTree.labelAt] at hs hc
  | onePremise rule t ih =>
    cases p with
    | nil =>
      simp only [InfDeductionTree.labelAt, Option.some.injEq] at hs
      subst s
      cases i with
      | zero =>
        simp only [List.nil_append, InfDeductionTree.labelAt, Option.some.injEq] at hc
        subst c
        exact ⟨.onePremise rule⟩
      | succ => simp [InfDeductionTree.labelAt] at hc
    | cons j p =>
      cases j with
      | zero => exact ih p hs hc
      | succ => simp [InfDeductionTree.labelAt] at hs
  | twoPremise rule l r ih₁ ih₂ =>
    cases p with
    | nil =>
      simp only [InfDeductionTree.labelAt, Option.some.injEq] at hs
      subst s
      cases i with
      | zero =>
        simp only [List.nil_append, InfDeductionTree.labelAt, Option.some.injEq] at hc
        subst c
        exact ⟨.leftPremise rule⟩
      | succ i =>
        cases i with
        | zero =>
          simp only [List.nil_append, InfDeductionTree.labelAt, Option.some.injEq] at hc
          subst c
          exact ⟨.rightPremise rule⟩
        | succ => simp [InfDeductionTree.labelAt] at hc
    | cons j p =>
      cases j with
      | zero => exact ih₁ p hs hc
      | succ j =>
        cases j with
        | zero => exact ih₂ p hs hc
        | succ => simp [InfDeductionTree.labelAt] at hs
  | extend a b t ih =>
    cases p with
    | nil =>
      simp only [InfDeductionTree.labelAt, Option.some.injEq] at hs
      subst s
      cases i with
      | zero =>
        simp only [List.nil_append, InfDeductionTree.labelAt, Option.some.injEq] at hc
        subst c
        exact ⟨.extend _ a b⟩
      | succ => simp [InfDeductionTree.labelAt] at hc
    | cons j p =>
      cases j with
      | zero => exact ih p hs hc
      | succ => simp [InfDeductionTree.labelAt] at hs

namespace InfDeductionTree

/-- The label at an address only when that address is a leaf. -/
def leafAt : {s : Sequent} → InfDeductionTree s → List Nat → Option Sequent
  | s, .leaf _, [] => some s
  | _, .leaf _, _ :: _ => none
  | _, .onePremise _ _, [] => none
  | _, .onePremise _ t, 0 :: p => t.leafAt p
  | _, .onePremise _ _, (_ + 1) :: _ => none
  | _, .twoPremise _ _ _, [] => none
  | _, .twoPremise _ l _, 0 :: p => l.leafAt p
  | _, .twoPremise _ _ r, 1 :: p => r.leafAt p
  | _, .twoPremise _ _ _, (_ + 2) :: _ => none
  | _, .extend _ _ _, [] => none
  | _, .extend _ _ t, 0 :: p => t.leafAt p
  | _, .extend _ _ _, (_ + 1) :: _ => none

theorem labelAt_of_leafAt {s label : Sequent} (t : InfDeductionTree s)
    (p : List Nat) (h : t.leafAt p = some label) : t.labelAt p = some label := by
  induction t generalizing p with
  | leaf => cases p <;> simp_all [leafAt, labelAt]
  | onePremise r t ih =>
    cases p with
    | nil => simp [leafAt] at h
    | cons i p =>
      cases i with
      | zero => exact ih p h
      | succ => simp [leafAt] at h
  | twoPremise r l t ih₁ ih₂ =>
    cases p with
    | nil => simp [leafAt] at h
    | cons i p =>
      cases i with
      | zero => exact ih₁ p h
      | succ i =>
        cases i with
        | zero => exact ih₂ p h
        | succ => simp [leafAt] at h
  | extend a b t ih =>
    cases p with
    | nil => simp [leafAt] at h
    | cons i p =>
      cases i with
      | zero => exact ih p h
      | succ => simp [leafAt] at h

def height : {s : Sequent} → InfDeductionTree s → Nat
  | _, .leaf _ => 0
  | _, .onePremise _ t => t.height + 1
  | _, .twoPremise _ l r => max l.height r.height + 1
  | _, .extend _ _ t => t.height + 1

theorem labelAt_length_le_height {s label : Sequent} (t : InfDeductionTree s)
    (p : List Nat) (h : t.labelAt p = some label) : p.length ≤ t.height := by
  induction t generalizing p with
  | leaf => cases p <;> simp_all [labelAt, height]
  | onePremise rule t ih =>
    cases p with
    | nil => simp
    | cons i p =>
      cases i with
      | zero => exact Nat.succ_le_succ (ih p h)
      | succ => simp [labelAt] at h
  | twoPremise rule l r ih₁ ih₂ =>
    cases p with
    | nil => simp
    | cons i p =>
      cases i with
      | zero =>
        have := ih₁ p h
        simp only [List.length_cons, height]
        omega
      | succ i =>
        cases i with
        | zero =>
          have := ih₂ p h
          simp only [List.length_cons, height]
          omega
        | succ => simp [labelAt] at h
  | extend a b t ih =>
    cases p with
    | nil => simp
    | cons i p =>
      cases i with
      | zero => exact Nat.succ_le_succ (ih p h)
      | succ => simp [labelAt] at h

/-- Extension retains every existing edge and adds nodes only below leaves. -/
inductive Extension : {s t : Sequent} → InfDeductionTree s → InfDeductionTree t → Prop where
  | leaf {s} (t : InfDeductionTree s) : Extension (.leaf s) t
  | one {s p} (rule : GentzenStep1 p s) {a b : InfDeductionTree p} :
      Extension a b → Extension (.onePremise rule a) (.onePremise rule b)
  | two {s p q} (rule : GentzenStep2 p q s)
      {a b : InfDeductionTree p} {c d : InfDeductionTree q} :
      Extension a b → Extension c d → Extension (.twoPremise rule a c) (.twoPremise rule b d)
  | intro {s} (a b) {t u : InfDeductionTree (extendSeq s a b)} :
      Extension t u → Extension (.extend a b t) (.extend a b u)

theorem Extension.refl {s} (t : InfDeductionTree s) : Extension t t := by
  induction t with
  | leaf => exact .leaf _
  | onePremise r _ ih => exact .one r ih
  | twoPremise r _ _ ih₁ ih₂ => exact .two r ih₁ ih₂
  | extend a b _ ih => exact .intro a b ih

theorem Extension.trans {s t u} {a : InfDeductionTree s} {b : InfDeductionTree t}
    {c : InfDeductionTree u} (h₁ : Extension a b) (h₂ : Extension b c) : Extension a c := by
  induction h₁ generalizing u with
  | leaf => cases h₂ <;> exact .leaf _
  | one r h ih => cases h₂ with | one _ h₂ => exact .one r (ih h₂)
  | two r h₁ h₂ ih₁ ih₂ =>
    cases ‹Extension (.twoPremise r _ _) c› with
    | two _ ha hb => exact .two r (ih₁ ha) (ih₂ hb)
  | intro a b h ih => cases h₂ with | intro _ _ h₂ => exact .intro a b (ih h₂)

theorem extension_bindLeaves (f : (s : Sequent) → InfDeductionTree s)
    {s} (t : InfDeductionTree s) : Extension t (t.bindLeaves f) := by
  induction t with
  | leaf => exact .leaf _
  | onePremise r _ ih => exact .one r ih
  | twoPremise r _ _ ih₁ ih₂ => exact .two r ih₁ ih₂
  | extend a b _ ih => exact .intro a b ih

/-- A new node is either an old node or lies below an old leaf. -/
theorem Extension.node_or_leaf_prefix {s t} {a : InfDeductionTree s}
    {b : InfDeductionTree t} (h : Extension a b) (p : List Nat) (label : Sequent)
    (hp : b.labelAt p = some label) :
    a.labelAt p = some label ∨
      ∃ q suffix leaf, p = q ++ suffix ∧ a.leafAt q = some leaf := by
  induction h generalizing p with
  | leaf => exact Or.inr ⟨[], p, _, rfl, rfl⟩
  | one rule h ih =>
    cases p with
    | nil => exact Or.inl hp
    | cons i p =>
      cases i with
      | zero =>
        rcases ih p hp with hold | ⟨q, suffix, leaf, rfl, hleaf⟩
        · exact Or.inl hold
        · exact Or.inr ⟨0 :: q, suffix, leaf, rfl, hleaf⟩
      | succ => simp [labelAt] at hp
  | two rule h₁ h₂ ih₁ ih₂ =>
    cases p with
    | nil => exact Or.inl hp
    | cons i p =>
      cases i with
      | zero =>
        rcases ih₁ p hp with hold | ⟨q, suffix, leaf, rfl, hleaf⟩
        · exact Or.inl hold
        · exact Or.inr ⟨0 :: q, suffix, leaf, rfl, hleaf⟩
      | succ i =>
        cases i with
        | zero =>
          rcases ih₂ p hp with hold | ⟨q, suffix, leaf, rfl, hleaf⟩
          · exact Or.inl hold
          · exact Or.inr ⟨1 :: q, suffix, leaf, rfl, hleaf⟩
        | succ => simp [labelAt] at hp
  | intro a b h ih =>
    cases p with
    | nil => exact Or.inl hp
    | cons i p =>
      cases i with
      | zero =>
        rcases ih p hp with hold | ⟨q, suffix, leaf, rfl, hleaf⟩
        · exact Or.inl hold
        · exact Or.inr ⟨0 :: q, suffix, leaf, rfl, hleaf⟩
      | succ => simp [labelAt] at hp

/-- Every internal search-tree node is nonaxiomatic. -/
def AllInnerOpen : {s : Sequent} → InfDeductionTree s → Prop
  | _, .leaf _ => True
  | s, .onePremise _ t => ¬ isAxiom s ∧ t.AllInnerOpen
  | s, .twoPremise _ l r => ¬ isAxiom s ∧ l.AllInnerOpen ∧ r.AllInnerOpen
  | s, .extend _ _ t => ¬ isAxiom s ∧ t.AllInnerOpen

theorem allInnerOpen_ofDeductionTree {s} (t : DeductionTree s)
    (h : Search.AllInnerOpen t) : (ofDeductionTree t).AllInnerOpen := by
  induction t with
  | leaf => trivial
  | onePremise r t ih => exact ⟨h.1, ih h.2⟩
  | twoPremise r l t ih₁ ih₂ => exact ⟨h.1, ih₁ h.2.1, ih₂ h.2.2⟩

theorem allInnerOpen_bindLeaves (f : (s : Sequent) → InfDeductionTree s)
    (hf : ∀ s, (f s).AllInnerOpen) {s} (t : InfDeductionTree s)
    (h : t.AllInnerOpen) : (t.bindLeaves f).AllInnerOpen := by
  induction t with
  | leaf s => exact hf s
  | onePremise r t ih => exact ⟨h.1, ih h.2⟩
  | twoPremise r l t ih₁ ih₂ => exact ⟨h.1, ih₁ h.2.1, ih₂ h.2.2⟩
  | extend a b t ih => exact ⟨h.1, ih h.2⟩

theorem leafAt_of_axiom {s label : Sequent} (t : InfDeductionTree s)
    (h : t.AllInnerOpen) (p : List Nat) (hp : t.labelAt p = some label)
    (ha : isAxiom label) : t.leafAt p = some label := by
  induction t generalizing p with
  | leaf => cases p <;> simp_all [labelAt, leafAt]
  | onePremise r t ih =>
    cases p with
    | nil => exact False.elim (h.1 ((Option.some.inj hp) ▸ ha))
    | cons i p =>
      cases i with
      | zero => exact ih h.2 p hp
      | succ => simp [labelAt] at hp
  | twoPremise r l t ih₁ ih₂ =>
    cases p with
    | nil => exact False.elim (h.1 ((Option.some.inj hp) ▸ ha))
    | cons i p =>
      cases i with
      | zero => exact ih₁ h.2.1 p hp
      | succ i =>
        cases i with
        | zero => exact ih₂ h.2.2 p hp
        | succ => simp [labelAt] at hp
  | extend a b t ih =>
    cases p with
    | nil => exact False.elim (h.1 ((Option.some.inj hp) ▸ ha))
    | cons i p =>
      cases i with
      | zero => exact ih h.2 p hp
      | succ => simp [labelAt] at hp

theorem leafAt_bindLeaves_of_fixed (f : (s : Sequent) → InfDeductionTree s)
    {s label : Sequent} (t : InfDeductionTree s) (p : List Nat)
    (hp : t.leafAt p = some label) (hf : f label = .leaf label) :
    (t.bindLeaves f).leafAt p = some label := by
  induction t generalizing p with
  | leaf s =>
    cases p with
    | nil =>
      simp only [leafAt, Option.some.injEq] at hp
      subst label
      simp [bindLeaves, hf, leafAt]
    | cons => simp [leafAt] at hp
  | onePremise r t ih =>
    cases p with
    | nil => simp [leafAt] at hp
    | cons i p =>
      cases i with
      | zero => exact ih p hp
      | succ => simp [leafAt] at hp
  | twoPremise r l t ih₁ ih₂ =>
    cases p with
    | nil => simp [leafAt] at hp
    | cons i p =>
      cases i with
      | zero => exact ih₁ p hp
      | succ i =>
        cases i with
        | zero => exact ih₂ p hp
        | succ => simp [leafAt] at hp
  | extend a b t ih =>
    cases p with
    | nil => simp [leafAt] at hp
    | cons i p =>
      cases i with
      | zero => exact ih p hp
      | succ => simp [leafAt] at hp

theorem labelAt_child_of_leafAt {s label : Sequent} (t : InfDeductionTree s)
    (p : List Nat) (i : Nat) (hp : t.leafAt p = some label) :
    t.labelAt (p ++ [i]) = none := by
  induction t generalizing p with
  | leaf => cases p <;> simp_all [leafAt, labelAt]
  | onePremise r t ih =>
    cases p with
    | nil => simp [leafAt] at hp
    | cons j p =>
      cases j with
      | zero => exact ih p hp
      | succ => simp [leafAt] at hp
  | twoPremise r l t ih₁ ih₂ =>
    cases p with
    | nil => simp [leafAt] at hp
    | cons j p =>
      cases j with
      | zero => exact ih₁ p hp
      | succ j =>
        cases j with
        | zero => exact ih₂ p hp
        | succ => simp [leafAt] at hp
  | extend a b t ih =>
    cases p with
    | nil => simp [leafAt] at hp
    | cons j p =>
      cases j with
      | zero => exact ih p hp
      | succ => simp [leafAt] at hp

/-- Lookup below an old leaf is exactly lookup in that leaf's replacement. -/
theorem labelAt_bindLeaves_below_leaf (f : (s : Sequent) → InfDeductionTree s)
    {s label : Sequent} (t : InfDeductionTree s) (p suffix : List Nat)
    (hp : t.leafAt p = some label) :
    (t.bindLeaves f).labelAt (p ++ suffix) = (f label).labelAt suffix := by
  induction t generalizing p with
  | leaf s =>
    cases p with
    | nil => simp only [leafAt, Option.some.injEq] at hp; subst label; rfl
    | cons => simp [leafAt] at hp
  | onePremise r t ih =>
    cases p with
    | nil => simp [leafAt] at hp
    | cons i p =>
      cases i with
      | zero => exact ih p hp
      | succ => simp [leafAt] at hp
  | twoPremise r l t ih₁ ih₂ =>
    cases p with
    | nil => simp [leafAt] at hp
    | cons i p =>
      cases i with
      | zero => exact ih₁ p hp
      | succ i =>
        cases i with
        | zero => exact ih₂ p hp
        | succ => simp [leafAt] at hp
  | extend a b t ih =>
    cases p with
    | nil => simp [leafAt] at hp
    | cons i p =>
      cases i with
      | zero => exact ih p hp
      | succ => simp [leafAt] at hp

theorem leafAt_bindLeaves_below_leaf (f : (s : Sequent) → InfDeductionTree s)
    {s label : Sequent} (t : InfDeductionTree s) (p suffix : List Nat)
    (hp : t.leafAt p = some label) :
    (t.bindLeaves f).leafAt (p ++ suffix) = (f label).leafAt suffix := by
  induction t generalizing p with
  | leaf s =>
    cases p with
    | nil => simp only [leafAt, Option.some.injEq] at hp; subst label; rfl
    | cons => simp [leafAt] at hp
  | onePremise r t ih =>
    cases p with
    | nil => simp [leafAt] at hp
    | cons i p =>
      cases i with
      | zero => exact ih p hp
      | succ => simp [leafAt] at hp
  | twoPremise r l t ih₁ ih₂ =>
    cases p with
    | nil => simp [leafAt] at hp
    | cons i p =>
      cases i with
      | zero => exact ih₁ p hp
      | succ i =>
        cases i with
        | zero => exact ih₂ p hp
        | succ => simp [leafAt] at hp
  | extend a b t ih =>
    cases p with
    | nil => simp [leafAt] at hp
    | cons i p =>
      cases i with
      | zero => exact ih p hp
      | succ => simp [leafAt] at hp

/-- Each new leaf lies below one precise old leaf occurrence. -/
theorem leafAt_bindLeaves_decompose (f : (s : Sequent) → InfDeductionTree s)
    {s label : Sequent} (t : InfDeductionTree s) (p : List Nat)
    (hp : (t.bindLeaves f).leafAt p = some label) :
    ∃ q suffix leaf, p = q ++ suffix ∧ t.leafAt q = some leaf ∧
      (f leaf).leafAt suffix = some label := by
  induction t generalizing p with
  | leaf s => exact ⟨[], p, s, rfl, rfl, hp⟩
  | onePremise r t ih =>
    cases p with
    | nil => simp [bindLeaves, leafAt] at hp
    | cons i p =>
      cases i with
      | zero =>
        obtain ⟨q, suffix, leaf, rfl, hq, hf⟩ := ih p hp
        exact ⟨0 :: q, suffix, leaf, rfl, hq, hf⟩
      | succ => simp [bindLeaves, leafAt] at hp
  | twoPremise r l t ih₁ ih₂ =>
    cases p with
    | nil => simp [bindLeaves, leafAt] at hp
    | cons i p =>
      cases i with
      | zero =>
        obtain ⟨q, suffix, leaf, rfl, hq, hf⟩ := ih₁ p hp
        exact ⟨0 :: q, suffix, leaf, rfl, hq, hf⟩
      | succ i =>
        cases i with
        | zero =>
          obtain ⟨q, suffix, leaf, rfl, hq, hf⟩ := ih₂ p hp
          exact ⟨1 :: q, suffix, leaf, rfl, hq, hf⟩
        | succ => simp [bindLeaves, leafAt] at hp
  | extend a b t ih =>
    cases p with
    | nil => simp [bindLeaves, leafAt] at hp
    | cons i p =>
      cases i with
      | zero =>
        obtain ⟨q, suffix, leaf, rfl, hq, hf⟩ := ih p hp
        exact ⟨0 :: q, suffix, leaf, rfl, hq, hf⟩
      | succ => simp [bindLeaves, leafAt] at hp

/-- No proper descendant address can lie below a leaf. -/
theorem leafAt_descendant_eq {s leaf label : Sequent} (t : InfDeductionTree s)
    (p suffix : List Nat) (hp : t.leafAt p = some leaf)
    (hq : t.labelAt (p ++ suffix) = some label) : suffix = [] := by
  induction t generalizing p with
  | leaf s =>
    cases p with
    | nil => cases suffix <;> simp_all [labelAt]
    | cons => simp [leafAt] at hp
  | onePremise r t ih =>
    cases p with
    | nil => simp [leafAt] at hp
    | cons i p =>
      cases i with
      | zero => exact ih p hp hq
      | succ => simp [leafAt] at hp
  | twoPremise r l t ih₁ ih₂ =>
    cases p with
    | nil => simp [leafAt] at hp
    | cons i p =>
      cases i with
      | zero => exact ih₁ p hp hq
      | succ i =>
        cases i with
        | zero => exact ih₂ p hp hq
        | succ => simp [leafAt] at hp
  | extend a b t ih =>
    cases p with
    | nil => simp [leafAt] at hp
    | cons i p =>
      cases i with
      | zero => exact ih p hp hq
      | succ => simp [leafAt] at hp

/-- Every listed leaf has an actual address. -/
theorem leafAt_of_mem_leaves {s leaf : Sequent} (t : InfDeductionTree s)
    (h : leaf ∈ t.leaves) : ∃ p, t.leafAt p = some leaf := by
  induction t with
  | leaf s =>
    simp only [leaves, List.mem_singleton] at h
    subst leaf
    exact ⟨[], rfl⟩
  | onePremise rule t ih =>
    obtain ⟨p, hp⟩ := ih h
    exact ⟨0 :: p, hp⟩
  | twoPremise rule l r ih₁ ih₂ =>
    rcases List.mem_append.mp h with h | h
    · obtain ⟨p, hp⟩ := ih₁ h; exact ⟨0 :: p, hp⟩
    · obtain ⟨p, hp⟩ := ih₂ h; exact ⟨1 :: p, hp⟩
  | extend a b t ih =>
    obtain ⟨p, hp⟩ := ih h
    exact ⟨0 :: p, hp⟩

/-- A node's immediate predecessor is present and the edge is binary. -/
theorem labelAt_parent {s label : Sequent} (t : InfDeductionTree s)
    (p : List Nat) (i : Nat) (hp : t.labelAt (p ++ [i]) = some label) :
    (∃ parent, t.labelAt p = some parent) ∧ (i = 0 ∨ i = 1) := by
  induction t generalizing p with
  | leaf => cases p <;> simp [labelAt] at hp
  | @onePremise s c rule t ih =>
    cases p with
    | nil =>
      cases i with
      | zero => exact ⟨⟨s, rfl⟩, Or.inl rfl⟩
      | succ => simp [labelAt] at hp
    | cons j p =>
      cases j with
      | zero => exact ih p hp
      | succ => simp [labelAt] at hp
  | @twoPremise s c d rule l r ih₁ ih₂ =>
    cases p with
    | nil =>
      cases i with
      | zero => exact ⟨⟨s, rfl⟩, Or.inl rfl⟩
      | succ i =>
        cases i with
        | zero => exact ⟨⟨s, rfl⟩, Or.inr rfl⟩
        | succ => simp [labelAt] at hp
    | cons j p =>
      cases j with
      | zero => exact ih₁ p hp
      | succ j =>
        cases j with
        | zero => exact ih₂ p hp
        | succ => simp [labelAt] at hp
  | @extend s a b t ih =>
    cases p with
    | nil =>
      cases i with
      | zero => exact ⟨⟨s, rfl⟩, Or.inl rfl⟩
      | succ => simp [labelAt] at hp
    | cons j p =>
      cases j with
      | zero => exact ih p hp
      | succ => simp [labelAt] at hp

/-- An addressed leaf occurs in the tree's leaf list. -/
theorem mem_leaves_of_leafAt {s leaf : Sequent} (t : InfDeductionTree s)
    (p : List Nat) (h : t.leafAt p = some leaf) : leaf ∈ t.leaves := by
  induction t generalizing p with
  | leaf => cases p <;> simp_all [leafAt, leaves]
  | onePremise r t ih =>
    cases p with
    | nil => simp [leafAt] at h
    | cons i p =>
      cases i with
      | zero => exact ih p h
      | succ => simp [leafAt] at h
  | twoPremise r l t ih₁ ih₂ =>
    cases p with
    | nil => simp [leafAt] at h
    | cons i p =>
      cases i with
      | zero => exact List.mem_append_left _ (ih₁ p h)
      | succ i =>
        cases i with
        | zero => exact List.mem_append_right _ (ih₂ p h)
        | succ => simp [leafAt] at h
  | extend a b t ih =>
    cases p with
    | nil => simp [leafAt] at h
    | cons i p =>
      cases i with
      | zero => exact ih p h
      | succ => simp [leafAt] at h

end InfDeductionTree
end LCS.Propositional.Infinite
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

@[simp] theorem InfDeductionTree.ofDeductionTree_cast {s t : Sequent} (h : s = t)
    (tree : DeductionTree s) :
    ofDeductionTree (h ▸ tree) = h ▸ ofDeductionTree tree := by
  subst h
  rfl

@[simp] theorem InfDeductionTree.bindLeaves_cast (f : (s : Sequent) → InfDeductionTree s)
    {s t : Sequent} (h : s = t) (tree : InfDeductionTree s) :
    bindLeaves f (h ▸ tree) = h ▸ bindLeaves f tree := by
  subst h
  rfl

@[simp] theorem InfDeductionTree.labelAt_cast {s t : Sequent} (h : s = t)
    (tree : InfDeductionTree s) (p : List Nat) :
    (h ▸ tree : InfDeductionTree t).labelAt p = tree.labelAt p := by
  subst h
  rfl

@[simp] theorem InfDeductionTree.leafAt_cast {s t : Sequent} (h : s = t)
    (tree : InfDeductionTree s) (p : List Nat) :
    (h ▸ tree : InfDeductionTree t).leafAt p = tree.leafAt p := by
  subst h
  rfl

end LCS.Propositional.Infinite
end
