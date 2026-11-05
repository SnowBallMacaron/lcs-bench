/-!
# Utility definitions for LCS formalization

This file contains basic utility definitions used throughout the LCS formalization,
particularly set-theoretic primitives that are not directly in Lean 4 core.
-/

universe u

/-- Set type as a function to Prop -/
abbrev Set (α : Type u) := α → Prop

/-- Membership instance for sets: a ∈ s ↔ s a
    Note: In Lean 4 stable, Membership.mem takes container first, then element. -/
instance {α : Type u} : Membership α (Set α) where
  mem (s : Set α) (a : α) := s a

namespace Set

/-- Empty set -/
def empty {α : Type u} : Set α := fun _ => False

end Set

namespace Set

/-- Set union -/
def union {α : Type u} (s t : Set α) : Set α := fun x => s x ∨ t x

end Set

namespace Set

/-- Set intersection -/
def inter {α : Type u} (s t : Set α) : Set α := fun x => s x ∧ t x

end Set

namespace Set

/-- Subset relation -/
def subset {α : Type u} (s t : Set α) : Prop := ∀ x, s x → t x

end Set

/-- Notation for subset -/
infixl:50 " ⊆ " => Set.subset

/-- Notation for union -/
infixl:65 " ∪ " => Set.union

/-- Notation for intersection -/
infixl:70 " ∩ " => Set.inter

/-- Notation for empty set -/
notation "∅" => Set.empty

namespace Set

/-- Singleton set -/
def singleton {α : Type u} (a : α) [DecidableEq α] : Set α :=
  fun x => x = a

end Set

namespace Set

/-- Set difference -/
def diff {α : Type u} (s t : Set α) : Set α :=
  fun x => s x ∧ ¬ t x

end Set

/-- Notation for set difference -/
infixl:65 " \\ " => Set.diff

namespace Set

/-- Indexed union: ⋃ over an index type -/
def iUnion {α : Type u} {ι : Type} (f : ι → Set α) : Set α :=
  fun x => ∃ i, f i x

end Set

namespace Set

/-- A set is finite if there exists a list containing exactly its members -/
def Finite {α : Type u} (s : Set α) : Prop :=
  ∃ (l : List α), ∀ a, s a ↔ a ∈ l

/-- The empty set is finite -/
theorem Finite.empty {α : Type u} : Finite (Set.empty : Set α) :=
-- BEGIN PROOF
  ⟨[], fun _ => ⟨False.elim, fun h => by simp at h⟩⟩

/-- A finite union of two finite sets is finite -/
theorem Finite.union {α : Type u} {s t : Set α}
    (hs : Finite s) (ht : Finite t) : Finite (s ∪ t) := by
-- BEGIN PROOF
  obtain ⟨ls, hls⟩ := hs
  obtain ⟨lt, hlt⟩ := ht
  exact ⟨ls ++ lt, fun a => by
    simp only [Set.union]
    constructor
    · intro h
      rcases h with h | h
      · exact List.mem_append.mpr (Or.inl ((hls a).mp h))
      · exact List.mem_append.mpr (Or.inr ((hlt a).mp h))
    · intro h
      rcases List.mem_append.mp h with h | h
      · exact Or.inl ((hls a).mpr h)
      · exact Or.inr ((hlt a).mpr h)⟩

/-- A subset of a finite set is finite (weaker formulation: there exists
    a list containing all elements of t, though it may contain extras) -/
theorem Finite.subset {α : Type u} {s t : Set α}
    (hs : Finite s) (hts : t ⊆ s) : Finite t := by
-- BEGIN PROOF
  -- With the biconditional definition, we need classical logic to filter.
  -- Instead, we weaken: show ¬Finite t → ¬Finite s by contrapositive is
  -- the approach used in pigeonhole below. Here we provide a direct proof
  -- using classical decidability.
  obtain ⟨l, hl⟩ := hs
  -- Use classical logic: for each element in l, either t holds or not
  have : ∀ (a : α), t a → a ∈ l := fun a ha => (hl a).mp (hts a ha)
  -- We need a sublist of l containing exactly the elements satisfying t.
  -- Use classical filtering.
  classical
  exact ⟨l.filter (fun a => decide (t a)), fun a => by
    simp only [List.mem_filter]
    constructor
    · intro ha
      exact ⟨(hl a).mp (hts a ha), by simp [ha]⟩
    · intro ⟨_, hd⟩
      simp [decide_eq_true_eq] at hd
      exact hd⟩

/-- The union of a list-indexed family of finite sets is finite -/
theorem finite_list_union {α : Type u} {β : Type} (l : List β) (f : β → Set α)
    (hf : ∀ b ∈ l, Finite (f b)) : Finite (fun x => ∃ b ∈ l, f b x) := by
-- BEGIN PROOF
  induction l with
  | nil =>
    have : (fun x => ∃ b ∈ ([] : List β), f b x) = Set.empty := by
      funext x
      simp only [Set.empty]
      apply propext
      constructor
      · intro ⟨_, hb, _⟩; simp at hb
      · intro h; exact False.elim h
    rw [this]
    exact Finite.empty
  | cons b bs ih =>
    have hfbs : ∀ b' ∈ bs, Finite (f b') := fun b' hb' =>
      hf b' (List.mem_cons.mpr (Or.inr hb'))
    have ih' := ih hfbs
    have hfb := hf b (List.mem_cons.mpr (Or.inl rfl))
    have heq : (fun x => ∃ b' ∈ b :: bs, f b' x) =
               Set.union (f b) (fun x => ∃ b' ∈ bs, f b' x) := by
      funext x
      simp only [Set.union]
      apply propext
      constructor
      · intro ⟨b', hb', hfx⟩
        rcases List.mem_cons.mp hb' with rfl | hbs
        · exact Or.inl hfx
        · exact Or.inr ⟨b', hbs, hfx⟩
      · intro h
        rcases h with hfx | ⟨b', hbs, hfx⟩
        · exact ⟨b, List.mem_cons.mpr (Or.inl rfl), hfx⟩
        · exact ⟨b', List.mem_cons.mpr (Or.inr hbs), hfx⟩
    rw [heq]
    exact Finite.union hfb ih'

/-- Pigeonhole principle for lists: if a non-finite set s is covered by
    sets f(b) for b in a finite list l, then some f(b) is non-finite -/
theorem pigeonhole_list {α : Type u} {β : Type} (s : Set α) (l : List β) (f : β → Set α)
    (hs : ¬ Finite s)
    (hcover : ∀ x, s x → ∃ b ∈ l, f b x) :
    ∃ b ∈ l, ¬ Finite (f b) :=
-- BEGIN PROOF
  Classical.byContradiction fun hall => by
    -- hall : ¬ ∃ b, b ∈ l ∧ ¬ Finite (f b)
    -- This means all f b for b ∈ l are finite
    have hall' : ∀ b ∈ l, Finite (f b) := fun b hb =>
      Classical.byContradiction fun hnf => hall ⟨b, hb, hnf⟩
    -- All f b are finite, so their union is finite
    have hunion := finite_list_union l f hall'
    -- s is a subset of the union
    have hsub : s ⊆ (fun x => ∃ b ∈ l, f b x) := fun x hx => hcover x hx
    -- So s is finite
    exact hs (Finite.subset hunion hsub)

end Set

-- ============================================================================
-- Multiset: Quotient-based multiset (Mathlib pattern, no Mathlib dependency)
-- ============================================================================

namespace LCS

def Multiset (α : Type) : Type := Quotient (List.isSetoid α)

namespace Multiset
variable {α β : Type}

def ofList (l : List α) : Multiset α := Quotient.mk _ l
instance : Coe (List α) (Multiset α) := ⟨ofList⟩
def nil : Multiset α := ofList []
instance : EmptyCollection (Multiset α) := ⟨nil⟩

def cons (a : α) (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => ofList (a :: l)) fun _ _ p => Quot.sound (p.cons a)

protected def add (s₁ s₂ : Multiset α) : Multiset α :=
  Quotient.liftOn₂ s₁ s₂ (fun l₁ l₂ => ofList (l₁ ++ l₂))
    fun _ _ _ _ p₁ p₂ => Quot.sound (p₁.append p₂)
instance : Add (Multiset α) := ⟨Multiset.add⟩

def Nodup (s : Multiset α) : Prop :=
  Quot.liftOn s List.Nodup fun _ _ p => propext p.nodup_iff

def Mem (a : α) (s : Multiset α) : Prop :=
  Quot.liftOn s (fun l => a ∈ l) fun _ _ p => propext p.mem_iff
instance : Membership α (Multiset α) where mem s a := Mem a s

def map (f : α → β) (s : Multiset α) : Multiset β :=
  Quot.liftOn s (fun l => ofList (l.map f)) fun _ _ p => Quot.sound (p.map f)

def card : Multiset α → Nat := Quot.lift List.length fun _ _ => List.Perm.length_eq

instance [DecidableEq α] (a : α) (s : Multiset α) : Decidable (a ∈ s) :=
  Quotient.recOnSubsingleton s (fun l => show Decidable (a ∈ l) from inferInstance)

theorem ind {p : Multiset α → Prop} (h : ∀ l : List α, p (ofList l)) : ∀ s, p s :=
-- BEGIN PROOF
  Quot.ind h

/-- Bool-valued universal quantifier over a Multiset. -/
def all (p : α → Bool) (s : Multiset α) : Bool :=
  Quot.liftOn s (fun l => l.all p) (fun _ _ hp => by
    induction hp with
    | nil => rfl
    | cons a _ ih => simp [List.all_cons, ih]
    | swap a b l => simp [List.all_cons]; cases p a <;> cases p b <;> simp
    | trans _ _ ih1 ih2 => rw [ih1, ih2])

theorem all_eq_true {p : α → Bool} {s : Multiset α} :
    s.all p = true ↔ ∀ a ∈ s, p a = true := by
-- BEGIN PROOF
  induction s using Quotient.inductionOn with
  | _ l =>
    constructor
    · intro h a ha; exact List.all_eq_true.mp h a ha
    · intro h; exact List.all_eq_true.mpr (fun a ha => h a ha)

/-- Bool-valued existential quantifier over a Multiset. -/
def any (p : α → Bool) (s : Multiset α) : Bool :=
  Quot.liftOn s (fun l => l.any p) (fun _ _ hp => by
    induction hp with
    | nil => rfl
    | cons a _ ih => simp [List.any_cons, ih]
    | swap a b l => simp [List.any_cons]; cases p a <;> cases p b <;> simp
    | trans _ _ ih1 ih2 => rw [ih1, ih2])

theorem any_eq_true {p : α → Bool} {s : Multiset α} :
    s.any p = true ↔ ∃ a ∈ s, p a = true := by
-- BEGIN PROOF
  induction s using Quotient.inductionOn with
  | _ l =>
    constructor
    · intro h
      have := List.any_eq_true.mp h
      obtain ⟨a, ha, hp⟩ := this
      exact ⟨a, ha, hp⟩
    · intro ⟨a, ha, hp⟩
      exact List.any_eq_true.mpr ⟨a, ha, hp⟩

end Multiset

-- ============================================================================
-- Helper: nodup lists with same members are permutations
-- ============================================================================

theorem list_perm_of_nodup_of_mem_iff [DecidableEq α] {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) :
    l₁.Perm l₂ := by
-- BEGIN PROOF
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => exact List.Perm.nil
    | cons b t =>
      exact absurd ((h b).mpr List.mem_cons_self) (List.not_mem_nil)
  | cons a t ih =>
    have ha₂ : a ∈ l₂ := (h a).mp List.mem_cons_self
    have hp := List.perm_cons_erase ha₂
    apply List.Perm.trans _ hp.symm
    apply List.Perm.cons
    have hnd_at := List.nodup_cons.mp h₁
    have hnd_ae := hp.nodup_iff.mp h₂
    have hnd_e := (List.nodup_cons.mp hnd_ae).2
    exact ih hnd_at.2 hnd_e fun x => ⟨
      fun hx => by
        have hxa : x ≠ a := fun heq => by subst heq; exact hnd_at.1 hx
        exact (List.mem_erase_of_ne hxa).mpr ((h x).mp (List.mem_cons.mpr (Or.inr hx))),
      fun hx => by
        have hxa : x ≠ a := fun heq => by subst heq; exact (List.nodup_cons.mp hnd_ae).1 hx
        have := (h x).mpr (List.mem_of_mem_erase hx)
        exact (List.mem_cons.mp this).elim (fun heq => absurd heq hxa) id⟩

-- ============================================================================
-- Finset: Quotient-based finite set (Mathlib pattern, no Mathlib dependency)
-- ============================================================================

structure Finset (α : Type) where
  val : Multiset α
  nodup : val.Nodup

namespace Finset
variable {α β : Type}

-- Empty
def empty : Finset α := ⟨∅, List.nodup_nil⟩
instance : EmptyCollection (Finset α) := ⟨empty⟩

-- Singleton
def singleton (a : α) : Finset α :=
  ⟨Multiset.ofList [a], List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩
instance : Singleton α (Finset α) := ⟨singleton⟩

-- Membership
def Mem (a : α) (s : Finset α) : Prop := a ∈ s.val
instance : Membership α (Finset α) where mem s a := Finset.Mem a s

instance [DecidableEq α] (a : α) (s : Finset α) : Decidable (a ∈ s) :=
  inferInstanceAs (Decidable (a ∈ s.val))

-- Insert (idempotent: inserts only if not already present)
def insert [DecidableEq α] (a : α) (s : Finset α) : Finset α := by
  refine ⟨Quot.liftOn s.val
    (fun l => Multiset.ofList (if a ∈ l then l else a :: l))
    (fun l₁ l₂ hp => Quot.sound (by
      by_cases h₁ : a ∈ l₁
      · have h₂ := hp.mem_iff.mp h₁; simp [h₁, h₂]; exact hp
      · have h₂ : a ∉ l₂ := fun h => h₁ (hp.mem_iff.mpr h)
        simp [h₁, h₂]; exact hp.cons a)), ?_⟩
  cases s with | mk v nd =>
  induction v using Quot.ind with
  | mk l =>
    show (if a ∈ l then l else a :: l).Nodup
    split
    · exact nd
    · next h => exact List.nodup_cons.mpr ⟨h, nd⟩
instance [DecidableEq α] : Insert α (Finset α) := ⟨insert⟩

theorem mem_insert [DecidableEq α] {a b : α} {s : Finset α} :
    a ∈ insert b s ↔ a = b ∨ a ∈ s := by
-- BEGIN PROOF
  cases s with | mk v nd =>
  revert nd
  induction v using Quot.ind with
  | mk l =>
    intro nd
    change a ∈ (insert b ⟨Multiset.ofList l, nd⟩).val ↔
           a = b ∨ a ∈ (Multiset.ofList l : Multiset α)
    show a ∈ (if b ∈ l then l else b :: l) ↔ a = b ∨ a ∈ l
    split
    · next h => exact ⟨fun ha => Or.inr ha, fun h2 => h2.elim (fun heq => heq ▸ h) id⟩
    · next h => exact ⟨fun ha => (List.mem_cons.mp ha).elim Or.inl Or.inr,
                        fun h2 => List.mem_cons.mpr (h2.elim Or.inl Or.inr)⟩

theorem not_mem_empty {a : α} : ¬(a ∈ (∅ : Finset α)) := nofun

-- Card
def card (s : Finset α) : Nat := s.val.card

-- Subset
def Subset (s t : Finset α) : Prop := ∀ a, a ∈ s → a ∈ t
instance : HasSubset (Finset α) := ⟨Subset⟩

-- Extensionality: the critical theorem making Finset usable as a type index.
-- Two Finset with the same membership are equal.
-- Proof: lift to List level via Quotient.inductionOn₂, then use the
-- list_perm_of_nodup_of_mem_iff lemma to obtain a permutation proof,
-- which is exactly Quotient.sound for the permutation setoid.
theorem ext [DecidableEq α] {s₁ s₂ : Finset α}
    (h : ∀ a, a ∈ s₁ ↔ a ∈ s₂) : s₁ = s₂ := by
-- BEGIN PROOF
  cases s₁ with | mk v₁ nd₁ =>
  cases s₂ with | mk v₂ nd₂ =>
  simp only [Finset.mk.injEq]
  revert nd₁ nd₂ h
  exact Quotient.inductionOn₂ v₁ v₂ (fun l₁ l₂ nd₁ nd₂ h =>
    Quotient.sound (list_perm_of_nodup_of_mem_iff nd₁ nd₂ h))

-- Filter
def filter (p : α → Bool) (s : Finset α) : Finset α := by
  refine ⟨Quot.liftOn s.val
    (fun l => Multiset.ofList (l.filter p))
    (fun _ _ hp => Quot.sound (hp.filter p)), ?_⟩
  cases s with | mk v nd =>
  induction v using Quot.ind with
  | mk l => exact nd.filter p

theorem mem_filter {p : α → Bool} {a : α} {s : Finset α} :
    a ∈ filter p s ↔ a ∈ s ∧ p a = true := by
-- BEGIN PROOF
  cases s with | mk v nd =>
  revert nd
  induction v using Quot.ind with
  | mk l =>
    intro nd
    show a ∈ l.filter p ↔ a ∈ l ∧ p a = true
    exact List.mem_filter

-- Erase
def erase [DecidableEq α] (s : Finset α) (a : α) : Finset α := by
  refine ⟨Quot.liftOn s.val
    (fun l => Multiset.ofList (l.erase a))
    (fun _ _ hp => Quot.sound (hp.erase a)), ?_⟩
  cases s with | mk v nd =>
  induction v using Quot.ind with
  | mk l => exact nd.erase a

-- Membership in foldl insert: the key helper for union and ofList.
theorem mem_foldl_insert [DecidableEq α] {a : α} {s : Finset α} {l : List α} :
    a ∈ l.foldl (fun acc x => Insert.insert x acc) s ↔ a ∈ s ∨ a ∈ l := by
-- BEGIN PROOF
  induction l generalizing s with
  | nil => simp only [List.foldl, List.not_mem_nil, or_false]
  | cons x xs ih =>
    simp only [List.foldl]
    rw [ih]
    constructor
    · intro h; cases h with
      | inl h => cases mem_insert.mp h with
        | inl h => exact Or.inr (List.mem_cons.mpr (Or.inl h))
        | inr h => exact Or.inl h
      | inr h => exact Or.inr (List.mem_cons.mpr (Or.inr h))
    · intro h; cases h with
      | inl h => exact Or.inl (mem_insert.mpr (Or.inr h))
      | inr h => cases List.mem_cons.mp h with
        | inl h => exact Or.inl (mem_insert.mpr (Or.inl h))
        | inr h => exact Or.inr h

-- Convert a list to a Finset by inserting each element (deduplication).
def ofList [DecidableEq α] (l : List α) : Finset α :=
  l.foldl (fun acc a => Insert.insert a acc) ∅

theorem mem_ofList [DecidableEq α] {a : α} {l : List α} :
    a ∈ ofList l ↔ a ∈ l := by
-- BEGIN PROOF
  show a ∈ l.foldl (fun acc x => Insert.insert x acc) (∅ : Finset α) ↔ a ∈ l
  rw [mem_foldl_insert]
  exact ⟨fun h => h.elim (fun h => absurd h not_mem_empty) id, Or.inr⟩

-- Union: fold insert over the second set's elements.
-- Congruence follows from ext + mem_foldl_insert + Perm.mem_iff.
def union [DecidableEq α] (s t : Finset α) : Finset α :=
  Quot.liftOn t.val
    (fun l => l.foldl (fun acc x => Insert.insert x acc) s)
    (fun _ _ hp => ext fun a => by
      rw [mem_foldl_insert, mem_foldl_insert]
      exact or_congr_right hp.mem_iff)
instance [DecidableEq α] : Union (Finset α) := ⟨union⟩

theorem mem_union [DecidableEq α] {a : α} {s t : Finset α} :
    a ∈ union s t ↔ a ∈ s ∨ a ∈ t := by
-- BEGIN PROOF
  cases t with | mk v nd =>
  revert nd
  induction v using Quot.ind with
  | mk l =>
    intro nd
    exact mem_foldl_insert

-- Image: map then deduplicate via ofList.
-- Congruence follows from ext + mem_ofList + Perm.mem_iff on mapped lists.
def image [DecidableEq β] (f : α → β) (s : Finset α) : Finset β :=
  Quot.liftOn s.val
    (fun l => ofList (l.map f))
    (fun _ _ hp => ext fun b => by
      rw [mem_ofList, mem_ofList]
      simp only [List.mem_map]
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ⟨a, hp.mem_iff.mp ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩; exact ⟨a, hp.mem_iff.mpr ha, rfl⟩)

theorem mem_image [DecidableEq β] {b : β} {f : α → β} {s : Finset α} :
    b ∈ image f s ↔ ∃ a ∈ s, f a = b := by
-- BEGIN PROOF
  cases s with | mk v nd =>
  revert nd
  induction v using Quot.ind with
  | mk l =>
    intro nd
    -- Goal: b ∈ ofList (l.map f) ↔ ∃ a ∈ ⟨Multiset.ofList l, nd⟩, f a = b
    -- LHS: b ∈ l.map f (via mem_ofList)
    -- RHS: ∃ a, a ∈ l ∧ f a = b (Finset mem reduces to list mem)
    constructor
    · intro h
      obtain ⟨a, ha, rfl⟩ := (mem_ofList (l := l.map f)).mp h |> List.mem_map.mp
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact (mem_ofList (l := l.map f)).mpr (List.mem_map.mpr ⟨a, ha, rfl⟩)

@[simp]
theorem mem_empty {α : Type} (a : α) : a ∈ (∅ : LCS.Finset α) ↔ False :=
-- BEGIN PROOF
  ⟨fun h => LCS.Finset.not_mem_empty h, fun h => h.elim⟩

@[simp]
theorem mem_singleton {α : Type} (a b : α) :
    a ∈ (LCS.Finset.singleton b : LCS.Finset α) ↔ a = b := by
-- BEGIN PROOF
  show a ∈ ([b] : List α) ↔ a = b
  exact List.mem_singleton

@[simp]
theorem mem_erase {α : Type} [DecidableEq α] (a x : α) (s : LCS.Finset α) :
    x ∈ s.erase a ↔ x ∈ s ∧ x ≠ a := by
-- BEGIN PROOF
  cases s with | mk v nd =>
  revert nd
  induction v using LCS.Multiset.ind with
  | _ l =>
    intro hnd
    show x ∈ (l.erase a) ↔ x ∈ l ∧ x ≠ a
    constructor
    · intro h
      refine ⟨List.mem_of_mem_erase h, ?_⟩
      intro heq
      subst heq
      have : ¬ x ∈ l.erase x := by
        intro hxe
        have hp : l.Perm (x :: l.erase x) := List.perm_cons_erase (List.mem_of_mem_erase hxe)
        have hnd2 : (x :: l.erase x).Nodup := hp.nodup_iff.mp hnd
        exact (List.nodup_cons.mp hnd2).1 hxe
      exact this h
    · intro ⟨hm, hne⟩
      exact (List.mem_erase_of_ne hne).mpr hm

/-- Explicit-argument wrapper for `LCS.Finset.mem_union`. The upstream lemma
    takes membership args implicitly, but the Ch4 proofs use the
    convention of explicit positional args. -/
@[simp]
theorem mem_union_exp {α : Type} [DecidableEq α] (a : α) (s t : LCS.Finset α) :
    a ∈ LCS.Finset.union s t ↔ a ∈ s ∨ a ∈ t :=
-- BEGIN PROOF
  LCS.Finset.mem_union

/-- Explicit-argument wrapper for `LCS.Finset.mem_ofList`. -/
@[simp]
theorem mem_ofList_exp {α : Type} [DecidableEq α] (a : α) (l : List α) :
    a ∈ (LCS.Finset.ofList l : LCS.Finset α) ↔ a ∈ l :=
-- BEGIN PROOF
  LCS.Finset.mem_ofList

/-- Explicit-argument wrapper for `LCS.Finset.mem_insert`, matching the
    arg convention `(inserted, queried, set)`. -/
@[simp]
theorem mem_insert_exp {α : Type} [DecidableEq α] (a x : α) (s : LCS.Finset α) :
    x ∈ LCS.Finset.insert a s ↔ x = a ∨ x ∈ s :=
-- BEGIN PROOF
  LCS.Finset.mem_insert

/-- Explicit-argument wrapper for `LCS.Finset.mem_image`. -/
@[simp]
theorem mem_image_exp {α β : Type} [DecidableEq β] (b : β) (f : α → β)
    (s : LCS.Finset α) :
    b ∈ LCS.Finset.image f s ↔ ∃ a ∈ s, f a = b :=
-- BEGIN PROOF
  LCS.Finset.mem_image

/-- Explicit-argument wrapper for `LCS.Finset.mem_filter`. -/
@[simp]
theorem mem_filter_exp {α : Type} (p : α → Bool) (a : α) (s : LCS.Finset α) :
    a ∈ LCS.Finset.filter p s ↔ a ∈ s ∧ p a = true :=
-- BEGIN PROOF
  LCS.Finset.mem_filter

-- A noncomputable `toList` for LCS.Finset, returning SOME list of members.
-- LCS.Finset's `.val : Multiset α` needs a choice to extract a list
-- witness; we use `Classical.choose` here.

theorem exists_list {α : Type} (s : LCS.Finset α) :
    ∃ l : List α, LCS.Multiset.ofList l = s.val := by
-- BEGIN PROOF
  induction s.val using LCS.Multiset.ind with
  | _ l => exact ⟨l, rfl⟩

noncomputable def toList {α : Type} (s : LCS.Finset α) : List α :=
  Classical.choose s.exists_list

theorem toList_ofList_eq {α : Type} (s : LCS.Finset α) :
    LCS.Multiset.ofList s.toList = s.val :=
-- BEGIN PROOF
  Classical.choose_spec s.exists_list

theorem mem_toList {α : Type} (s : LCS.Finset α) (a : α) :
    a ∈ s.toList ↔ a ∈ s := by
-- BEGIN PROOF
  have h : LCS.Multiset.ofList s.toList = s.val := LCS.Finset.toList_ofList_eq s
  constructor
  · intro (ha : a ∈ s.toList)
    show a ∈ s.val
    rw [← h]
    exact ha
  · intro ha
    show a ∈ s.toList
    have : a ∈ s.val := ha
    rw [← h] at this
    exact this

theorem union_eq_right [DecidableEq α] {S T : Finset α}
    (h : LCS.Finset.Subset S T) : LCS.Finset.union S T = T := by
  apply LCS.Finset.ext
  intro C
  simp only [LCS.Finset.mem_union]
  exact ⟨fun hc => hc.elim (h C) id, Or.inr⟩

theorem union_comm [DecidableEq α] (S T : Finset α) :
    LCS.Finset.union S T = LCS.Finset.union T S := by
  apply LCS.Finset.ext
  intro C
  simp [or_comm]

theorem nonempty_of_ne_empty [DecidableEq α] (S : Finset α) (h : S ≠ LCS.Finset.empty) :
    ∃ C, C ∈ S := by
  apply Classical.byContradiction
  intro hNo
  apply h
  apply LCS.Finset.ext
  intro C
  constructor
  · intro hC
    exact (hNo ⟨C, hC⟩).elim
  · exact fun hC => (LCS.Finset.not_mem_empty hC).elim

end Finset

end LCS

-- Computable DecidableEq for Multiset and LCS.Finset, needed for `by_cases`
-- on Finset equality (used in `all_singletons_exact_pair_proof`).

instance instDecidableEqMultiset {α : Type} [DecidableEq α] :
    DecidableEq (LCS.Multiset α) :=
  fun s t => Quotient.recOnSubsingleton₂ s t
    (fun l1 l2 =>
      if h : l1.Perm l2 then isTrue (Quot.sound h)
      else isFalse (fun heq => h (Quotient.exact heq)))

instance instDecidableEqLCSFinset {α : Type} [DecidableEq α] :
    DecidableEq (LCS.Finset α) := by
  intro s t
  cases s; cases t
  simp [LCS.Finset.mk.injEq]
  exact inferInstance

-- ============================================================================
-- Tree domains and labeled trees (Chapter 2, Definitions 2.2.1–2.2.6)
-- ============================================================================

namespace LCS

/-- Definition 2.2.1: Tree addresses are finite sequences of natural numbers.
    The textbook uses strings over N₊ (positive integers). We use List Nat
    with 0-indexing (child 0 is the first child). The empty list [] is the
    root address. -/
abbrev TreeAddr := List Nat

/-- Definition 2.2.1: A tree domain is a nonempty set of tree addresses
    satisfying prefix closure and left-sibling closure. -/
structure TreeDomain where
  /-- The set of valid addresses -/
  dom : Set TreeAddr
  /-- The root (empty address) is always in the domain -/
  root_mem : [] ∈ dom
  /-- Prefix closure: if u ++ v ∈ D then u ∈ D -/
  prefix_closed : ∀ u v, (u ++ v) ∈ dom → u ∈ dom
  /-- Left-sibling closure: if u ++ [i+1] ∈ D then u ++ [i] ∈ D -/
  left_sibling_closed : ∀ u i, (u ++ [i + 1]) ∈ dom → (u ++ [i]) ∈ dom

/-- Definition 2.2.2: A labeled tree (Sigma-tree) is a tree domain together
    with a labeling function from valid addresses to labels. -/
structure LabeledTree (Label : Type) where
  /-- The underlying tree domain -/
  domain : TreeDomain
  /-- Label at each valid address -/
  label : (a : TreeAddr) → a ∈ domain.dom → Label

namespace TreeDomain

/-- The root address is always a valid address (direct consequence of root_mem). -/
theorem root_in_dom (d : TreeDomain) : ([] : TreeAddr) ∈ d.dom :=
-- BEGIN PROOF
  d.root_mem

/-- If u ++ [i] is in the domain, then u is in the domain. -/
theorem parent_mem (d : TreeDomain) (u : TreeAddr) (i : Nat)
    (h : (u ++ [i]) ∈ d.dom) : u ∈ d.dom :=
-- BEGIN PROOF
  d.prefix_closed u [i] h

/-- Left-sibling closure iterated: if u ++ [i] ∈ D and j ≤ i,
    then u ++ [j] ∈ D. -/
theorem sibling_mem (d : TreeDomain) (u : TreeAddr) (i j : Nat)
    (hij : j ≤ i) (h : (u ++ [i]) ∈ d.dom) : (u ++ [j]) ∈ d.dom := by
-- BEGIN PROOF
  induction i with
  | zero =>
    have : j = 0 := Nat.le_zero.mp hij
    rw [this]; exact h
  | succ n ih =>
    cases Nat.eq_or_lt_of_le hij with
    | inl heq => rw [heq]; exact h
    | inr hlt =>
      have hle : j ≤ n := Nat.lt_succ_iff.mp hlt
      exact ih hle (d.left_sibling_closed u n h)

end TreeDomain

namespace LabeledTree

variable {Label : Type}

/-- The root of a tree is the empty address. -/
def root : TreeAddr := []

/-- A node is a leaf if it has no children (child 0 is not in the domain). -/
def isLeaf (t : LabeledTree Label) (u : TreeAddr) (_hu : u ∈ t.domain.dom) : Prop :=
  ¬ ((u ++ [0]) ∈ t.domain.dom)

/-- Definition 2.2.4: The subtree of t rooted at address u.
    The domain is {v | u ++ v ∈ dom(t)} and the label at v is t's label
    at u ++ v. -/
def subtree (t : LabeledTree Label) (u : TreeAddr) (hu : u ∈ t.domain.dom) :
    LabeledTree Label where
  domain := {
    dom := fun v => (u ++ v) ∈ t.domain.dom
    root_mem := by
      show (u ++ []) ∈ t.domain.dom
      simp [hu]
    prefix_closed := fun v w (h : u ++ (v ++ w) ∈ t.domain.dom) => by
      show (u ++ v) ∈ t.domain.dom
      have hmem : (u ++ v) ++ w ∈ t.domain.dom := by
        rw [List.append_assoc]; exact h
      exact t.domain.prefix_closed (u ++ v) w hmem
    left_sibling_closed := fun v i (h : u ++ (v ++ [i + 1]) ∈ t.domain.dom) => by
      show u ++ (v ++ [i]) ∈ t.domain.dom
      have h2 : (u ++ v) ++ [i + 1] ∈ t.domain.dom := by
        rw [List.append_assoc]; exact h
      have h3 := t.domain.left_sibling_closed (u ++ v) i h2
      rw [List.append_assoc] at h3
      exact h3
  }
  label := fun a ha => t.label (u ++ a) ha

/-- Definition 2.2.5: Tree replacement — replace the subtree at address u
    in t₁ with tree t₂. The domain consists of addresses in t₁ that are
    not strictly below u, plus addresses u ++ v where v is in t₂'s domain.
    Labels come from t₁ outside u and from t₂ below u. -/
noncomputable def replacement (t₁ : LabeledTree Label) (u : TreeAddr)
    (_hu : u ∈ t₁.domain.dom) (t₂ : LabeledTree Label) :
    LabeledTree Label where
  domain := {
    dom := fun w =>
      -- Either w is in t₁ and not strictly below u ...
      (w ∈ t₁.domain.dom ∧ ¬ ∃ v, v ≠ [] ∧ w = u ++ v) ∨
      -- ... or w = u ++ v for some v in t₂'s domain
      (∃ v, v ∈ t₂.domain.dom ∧ w = u ++ v)
    root_mem := by
      by_cases h : u = []
      · right; exact ⟨[], t₂.domain.root_mem, by simp [h]⟩
      · left; exact ⟨t₁.domain.root_mem, fun ⟨v, _, heq⟩ => by
          cases v with
          | nil => simp at heq; exact h heq
          | cons hd tl => simp at heq⟩
    prefix_closed := fun w₁ w₂ hw => by
      -- hw : (w₁ ++ w₂) ∈ dom
      -- append_eq_append_iff on (ws ++ xs = ys ++ zs) gives:
      --   Left:  ∃ as, ys = ws ++ as ∧ xs = as ++ zs  (ws prefix of ys)
      --   Right: ∃ bs, ws = ys ++ bs ∧ zs = bs ++ xs  (ys prefix of ws)
      rcases hw with ⟨h_t1, h_not_below⟩ | ⟨v, hv, heq⟩
      · -- Case 1: w₁ ++ w₂ ∈ t₁.domain.dom and not strictly below u
        left
        exact ⟨t₁.domain.prefix_closed w₁ w₂ h_t1, fun ⟨v', hv'_ne, hv'_eq⟩ => by
          apply h_not_below
          exact ⟨v' ++ w₂, by intro h; exact hv'_ne (List.append_eq_nil_iff.mp h).1,
                 by rw [hv'_eq, List.append_assoc]⟩⟩
      · -- Case 2: w₁ ++ w₂ = u ++ v for some v ∈ t₂.domain.dom
        rcases List.append_eq_append_iff.mp heq with ⟨as, h_u_eq, _⟩ | ⟨bs, hw₁_eq, hv_eq⟩
        · -- w₁ is prefix of u: u = w₁ ++ as
          left
          exact ⟨t₁.domain.prefix_closed w₁ as (h_u_eq ▸ _hu), fun ⟨v', hv'_ne, hv'_eq⟩ => by
            have h : w₁ ++ (as ++ v') = w₁ := by
              rw [← List.append_assoc, ← h_u_eq]; exact hv'_eq.symm
            have h2 : as ++ v' = [] :=
              List.append_cancel_left (by rw [h, List.append_nil])
            exact hv'_ne (List.append_eq_nil_iff.mp h2).2⟩
        · -- u is prefix of w₁: w₁ = u ++ bs, v = bs ++ w₂
          right
          exact ⟨bs, t₂.domain.prefix_closed bs w₂ (hv_eq ▸ hv), hw₁_eq⟩
    left_sibling_closed := fun w i hw => by
      -- hw : (w ++ [i + 1]) ∈ dom
      rcases hw with ⟨h_t1, h_not_below⟩ | ⟨v, hv, heq⟩
      · -- Case 1: w ++ [i+1] ∈ t₁.domain.dom and not strictly below u
        left
        exact ⟨t₁.domain.left_sibling_closed w i h_t1, fun ⟨v', hv'_ne, hv'_eq⟩ => by
          -- From hv'_eq : w ++ [i] = u ++ v', use append_eq_append_iff
          rcases List.append_eq_append_iff.mp hv'_eq with ⟨as, h_u_eq, h_tail⟩ | ⟨bs, hw_eq, _⟩
          · -- w is prefix of u: u = w ++ as, [i] = as ++ v'
            -- Since as ++ v' = [i] and v' ≠ [], as must be [] and v' = [i]
            have has_nil : as = [] := by
              cases as with
              | nil => rfl
              | cons hd tl =>
                simp [List.cons_append] at h_tail
                cases tl with
                | nil =>
                  simp at h_tail
                  exact absurd h_tail.2 hv'_ne
                | cons _ _ => simp at h_tail
            -- So u = w, and w ++ [i+1] = u ++ [i+1] with [i+1] ≠ []
            rw [has_nil, List.append_nil] at h_u_eq
            apply h_not_below
            exact ⟨[i + 1], by simp, by rw [h_u_eq]⟩
          · -- u is prefix of w: w = u ++ bs
            apply h_not_below
            exact ⟨bs ++ [i + 1],
                   by intro h; exact List.cons_ne_nil _ _ (List.append_eq_nil_iff.mp h).2,
                   by rw [hw_eq, List.append_assoc]⟩⟩
      · -- Case 2: w ++ [i+1] = u ++ v for some v ∈ t₂.domain.dom
        rcases List.append_eq_append_iff.mp heq with ⟨as, h_u_eq, h_tail⟩ | ⟨bs, hw_eq, hv_eq⟩
        · -- w is prefix of u: u = w ++ as, [i+1] = as ++ v
          cases as with
          | nil =>
            -- as = [], so u = w, [i+1] = v
            simp at h_tail h_u_eq
            -- h_tail : [i + 1] = v, h_u_eq : u = w
            right
            exact ⟨[i], t₂.domain.left_sibling_closed [] i (by simp; rw [h_tail]; exact hv),
                   by rw [h_u_eq]⟩
          | cons hd tl =>
            simp [List.cons_append] at h_tail
            -- h_tail : i + 1 = hd ∧ tl = [] ∧ v = []
            left
            constructor
            · -- w ∈ t₁ via left_sibling_closed on u ∈ t₁
              rw [h_tail.2.1] at h_u_eq
              rw [← h_tail.1] at h_u_eq
              -- u = w ++ [i + 1], so w ++ [i + 1] ∈ t₁
              have hu_t1 : (w ++ [i + 1]) ∈ t₁.domain.dom := h_u_eq ▸ _hu
              exact t₁.domain.left_sibling_closed w i hu_t1
            · intro ⟨v', hv'_ne, hv'_eq⟩
              -- w ++ [i] = u ++ v' and u = w ++ (hd :: tl)
              -- So w ++ [i] = w ++ (hd :: tl) ++ v'
              rw [h_u_eq, List.append_assoc] at hv'_eq
              have h_eq := List.append_cancel_left hv'_eq
              -- [i] = (hd :: tl) ++ v', impossible since v' ≠ [] and tl might not be []
              -- After simp, tl = [], so [i] = [hd] ++ v' = hd :: v'
              rw [h_tail.2.1] at h_eq
              simp at h_eq
              exact hv'_ne h_eq.2
        · -- u is prefix of w: w = u ++ bs, v = bs ++ [i+1]
          right
          exact ⟨bs ++ [i], t₂.domain.left_sibling_closed bs i (hv_eq ▸ hv),
                 by rw [hw_eq, List.append_assoc]⟩
  }
  label := fun a ha => by
    classical
    exact if h : ∃ v, v ∈ t₂.domain.dom ∧ a = u ++ v then
      t₂.label h.choose h.choose_spec.1
    else
      have hdom : a ∈ t₁.domain.dom := by
        rcases ha with ⟨hdom, _⟩ | ⟨v, hv, heq⟩
        · exact hdom
        · exact absurd ⟨v, hv, heq⟩ h
      t₁.label a hdom

/-- Definition 2.2.6: A ranked alphabet has a rank function assigning
    a natural number (arity) to each symbol. -/
structure RankedAlphabet (Label : Type) where
  /-- The rank (arity) function -/
  rank : Label → Nat

/-- Definition 2.2.6: A ranked tree is a labeled tree where the outdegree
    of each node equals the rank of its label. -/
structure RankedTree (Label : Type) extends LabeledTree Label where
  /-- The ranked alphabet -/
  alphabet : RankedAlphabet Label
  /-- For every node u, its number of children equals the rank of its label -/
  rank_consistent : ∀ (a : TreeAddr) (ha : a ∈ toLabeledTree.domain.dom),
    (∀ j, j < alphabet.rank (toLabeledTree.label a ha) →
      (a ++ [j]) ∈ toLabeledTree.domain.dom) ∧
    (¬ (a ++ [alphabet.rank (toLabeledTree.label a ha)]) ∈ toLabeledTree.domain.dom)

end LabeledTree

-- ============================================================================
-- Koenig's Lemma (general tree theory)
-- ============================================================================

namespace TreeDomain

/-- A tree domain is finitely branching if every node has only finitely
    many children: for each u in the domain, there exists a bound n such
    that u ++ [i] is not in the domain for any i >= n. -/
def FinitelyBranching (d : TreeDomain) : Prop :=
  ∀ u, u ∈ d.dom → ∃ n, ∀ i, i ≥ n → ¬ ((u ++ [i]) ∈ d.dom)

/-- A tree domain is finite if there are only finitely many addresses
    in the domain (witnessed by a bounding list). -/
def IsFinite (d : TreeDomain) : Prop :=
  Set.Finite d.dom

/-- A tree domain has infinitely many nodes if for every n, there exists
    a node at depth >= n. -/
def IsInfinite (d : TreeDomain) : Prop :=
  ∀ n : Nat, ∃ u, u ∈ d.dom ∧ u.length ≥ n

/-- An infinite path through a tree domain is a function f : Nat -> Nat
    such that every finite prefix [f 0, f 1, ..., f (n-1)] is in the
    domain. -/
def HasInfinitePath (d : TreeDomain) : Prop :=
  ∃ f : Nat → Nat, ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ d.dom

/-- If a tree domain has infinitely many nodes, it has a node at
    every depth. This is a consequence of prefix closure. -/
theorem infinite_has_all_depths (d : TreeDomain)
    (hInf : d.IsInfinite) : ∀ n, ∃ u, u ∈ d.dom ∧ u.length = n := by
-- BEGIN PROOF
  intro n
  obtain ⟨u, hu, hlen⟩ := hInf n
  exact ⟨u.take n,
    d.prefix_closed (u.take n) (u.drop n) (by rw [List.take_append_drop]; exact hu),
    by rw [List.length_take]; omega⟩

-- Fin/List.ofFn helpers for Koenig's lemma

theorem castSucc_succ_eq_succ_castSucc {n : Nat} (i : Fin n) :
    i.castSucc.succ = i.succ.castSucc := by
-- BEGIN PROOF
  ext; simp [Fin.castSucc, Fin.succ]

theorem castSucc_zero_eq {n : Nat} :
    (0 : Fin (n + 1)).castSucc = (0 : Fin (n + 2)) := by
-- BEGIN PROOF
  ext; simp [Fin.castSucc]

theorem last_succ_eq {n : Nat} :
    (Fin.last n).succ = Fin.last (n + 1) := by
-- BEGIN PROOF
  ext; simp [Fin.last, Fin.succ]

/-- List.ofFn snoc decomposition: List.ofFn f for Fin (n+1) equals
    List.ofFn of the first n values appended with the last value. -/
theorem list_ofFn_snoc {α : Type} (n : Nat) (f : Fin (n + 1) → α) :
    List.ofFn f = List.ofFn (fun i : Fin n => f i.castSucc) ++ [f (Fin.last n)] := by
-- BEGIN PROOF
  induction n with
  | zero => simp [List.ofFn_succ, List.ofFn_zero, Fin.last, Fin.castSucc]
  | succ m ih =>
    rw [List.ofFn_succ, ih (fun i => f i.succ),
        List.ofFn_succ (f := fun i : Fin (m + 1) => f i.castSucc),
        castSucc_zero_eq, last_succ_eq, List.cons_append,
        show (fun i : Fin m => f i.castSucc.succ) =
             (fun i : Fin m => f i.succ.castSucc) from
          funext (fun i => congrArg f (castSucc_succ_eq_succ_castSucc i))]

/-- The set of all nodes that are "at or below" a given node u: i.e.,
    all w in the domain such that w = u ++ v for some v. -/
def nodesBelow (d : TreeDomain) (u : TreeAddr) : Set TreeAddr :=
  fun w => ∃ v, w = u ++ v ∧ d.dom w

/-- nodesBelow [] equals d.dom -/
theorem nodesBelow_root (d : TreeDomain) :
    ∀ w, d.nodesBelow [] w ↔ d.dom w := by
-- BEGIN PROOF
  intro w; simp [nodesBelow]

/-- Every node below u either equals u or goes through some child. -/
theorem nodesBelow_decompose (d : TreeDomain) (u : TreeAddr)
    (w : TreeAddr) (hw : d.nodesBelow u w) :
    w = u ∨ ∃ i v, w = u ++ (i :: v) ∧ d.dom w := by
-- BEGIN PROOF
  obtain ⟨v, rfl, hm⟩ := hw
  cases v with
  | nil => left; simp
  | cons i vs => right; exact ⟨i, vs, rfl, hm⟩

/-- nodesBelow (u ++ [i]) is a subset of nodesBelow u. -/
theorem nodesBelow_child_sub (d : TreeDomain) (u : TreeAddr) (i : Nat) :
    d.nodesBelow (u ++ [i]) ⊆ d.nodesBelow u := by
-- BEGIN PROOF
  intro w ⟨v, hweq, hm⟩
  exact ⟨i :: v, by rw [hweq]; simp [List.append_assoc], hm⟩

/-- A finite set of tree addresses has a maximum length. -/
theorem finite_has_max_length (l : List TreeAddr) :
    ∃ N : Nat, ∀ w ∈ l, w.length ≤ N := by
-- BEGIN PROOF
  induction l with
  | nil => exact ⟨0, fun _ h => absurd h (List.not_mem_nil)⟩
  | cons x xs ih =>
    obtain ⟨N', hN'⟩ := ih
    exact ⟨max x.length N', fun w hw => by
      cases List.mem_cons.mp hw with
      | inl heq => rw [heq]; exact Nat.le_max_left _ _
      | inr hxs => exact Nat.le_trans (hN' w hxs) (Nat.le_max_right _ _)⟩

/-- If a set of tree addresses is finite, then there is a bound on the
    length of addresses in the set: the tree is not IsInfinite. -/
theorem finite_not_infinite (d : TreeDomain)
    (hFin : Set.Finite d.dom) : ¬ d.IsInfinite := by
-- BEGIN PROOF
  intro hInf
  obtain ⟨l, hl⟩ := hFin
  obtain ⟨N, hN⟩ := finite_has_max_length l
  obtain ⟨u, hu, hlen⟩ := hInf (N + 1)
  have := hN u ((hl u).mp hu)
  omega

/-- If a finitely branching node has infinitely many nodes below it,
    then some child also has infinitely many nodes below it. This is
    the pigeonhole step at the core of Koenig's lemma.

    Proof: Suppose u has at most n children (i.e., u ++ [i] not in domain
    for i >= n). Each node below u either equals u itself or goes through
    some child u ++ [i] with i < n. If every such child had finitely many
    descendants, the union (a finite union of finite sets plus {u}) would
    be finite, contradicting the assumption that nodesBelow u is infinite.
    So some child must have infinitely many descendants. -/
theorem pigeonhole_child (d : TreeDomain) (u : TreeAddr)
    (hu : d.dom u) (hFB : d.FinitelyBranching)
    (hInf : ¬ Set.Finite (d.nodesBelow u)) :
    ∃ i, d.dom (u ++ [i]) ∧
      ¬ Set.Finite (d.nodesBelow (u ++ [i])) :=
-- BEGIN PROOF
  Classical.byContradiction fun hall => by
    -- hall : ¬ ∃ i, d.dom (u ++ [i]) ∧ ¬ Set.Finite (d.nodesBelow (u ++ [i]))
    -- u has only finitely many children (bound n)
    obtain ⟨n, hn⟩ := hFB u hu
    -- Every child that exists has finite nodesBelow
    have hallFin : ∀ i, d.dom (u ++ [i]) →
        Set.Finite (d.nodesBelow (u ++ [i])) :=
      fun i hi => Classical.byContradiction fun hinf => hall ⟨i, hi, hinf⟩
    -- nodesBelow (u ++ [i]) is empty (thus finite) when u ++ [i] not in dom
    have hAllFin : ∀ i, Set.Finite (d.nodesBelow (u ++ [i])) := by
      intro i
      by_cases hi : d.dom (u ++ [i])
      · exact hallFin i hi
      · -- nodesBelow is empty: every element w = (u++[i])++v requires u++[i] in dom
        apply Set.Finite.subset Set.Finite.empty
        intro w ⟨v, hweq, hdom⟩
        -- w = (u ++ [i]) ++ v and w ∈ dom, so u ++ [i] ∈ dom by prefix closure
        exact absurd (d.prefix_closed (u ++ [i]) v (by
          have : w = (u ++ [i]) ++ v := by rw [hweq, List.append_assoc]
          rw [← this]; exact hdom)) hi
    -- nodesBelow u decomposes: every w is u or goes through some child i < n
    apply hInf
    -- Every node below u either equals u or is below some child
    have hcover : d.nodesBelow u ⊆ Set.union (fun w => w = u)
        (fun w => ∃ i, i < n ∧ d.nodesBelow (u ++ [i]) w) := by
      intro w ⟨v, hweq, hdom⟩
      cases v with
      | nil => left; simpa using hweq
      | cons i vs =>
        right
        have hi_dom : d.dom (u ++ [i]) := by
          apply d.prefix_closed (u ++ [i]) vs
          have : w = (u ++ [i]) ++ vs := by
            rw [hweq]; simp [List.append_assoc]
          rw [← this]; exact hdom
        have hin : i < n := Classical.byContradiction fun h =>
          hn i (Nat.not_lt.mp h) hi_dom
        refine ⟨i, hin, vs, ?_, hdom⟩
        rw [hweq]; simp [List.append_assoc]
    apply Set.Finite.subset _ hcover
    apply Set.Finite.union
    · exact ⟨[u], fun a => by constructor <;> (intro h; simp_all)⟩
    · -- Finite union of nodesBelow (u ++ [i]) for i < n
      suffices ∀ k, Set.Finite
          (fun w => ∃ i, i < k ∧ d.nodesBelow (u ++ [i]) w) from this n
      intro k
      induction k with
      | zero =>
        apply Set.Finite.subset Set.Finite.empty
        intro w ⟨_, hi, _⟩; omega
      | succ m ihm =>
        -- (exists i < m+1, P i) = (exists i < m, P i) or P m
        apply Set.Finite.subset (Set.Finite.union ihm (hAllFin m))
        intro w ⟨i, hi, hc⟩
        simp only [Set.union]
        cases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with
        | inl heq => right; rw [← heq]; exact hc
        | inr hlt => left; exact ⟨i, hlt, hc⟩

/-- If a tree domain is not finite, it is infinite (has nodes at every
    depth). For a finitely branching tree, not IsFinite implies IsInfinite.

    Proof sketch: If not IsInfinite, there is a depth bound n such that
    all nodes have length < n. In a finitely branching tree with bounded
    depth, the number of nodes is finite (each level has finitely many
    nodes, and there are at most n levels). This contradicts not IsFinite.

    The converse (IsInfinite implies not IsFinite) follows from
    finite_not_infinite. -/
theorem not_finite_is_infinite (d : TreeDomain)
    (hFB : d.FinitelyBranching) (hNotFin : ¬ d.IsFinite) :
    d.IsInfinite :=
-- BEGIN PROOF
  -- We prove the contrapositive: ¬ IsInfinite → IsFinite (using finite branching).
  -- Then ¬ IsFinite → ¬ ¬ IsInfinite, and by classical DN elimination, IsInfinite.
  -- This is proved by iterating pigeonhole_child: if the tree is not finite but
  -- has bounded depth N, we get a contradiction by finding nodes of increasing
  -- length, each with infinite descendants, until we exceed the depth bound.
  Classical.byContradiction fun hNotInf => by
    -- We have ¬ IsFinite and ¬ IsInfinite. Derive contradiction (prove False).
    -- From ¬ IsInfinite: there exists N such that no node has length >= N.
    have hBound : ∃ N, ∀ u, d.dom u → u.length < N := by
      -- ¬ (∀ n, ∃ u, d.dom u ∧ u.length ≥ n) means ∃ n, ∀ u, d.dom u → u.length < n
      exact Classical.byContradiction fun h => hNotInf (fun n =>
        Classical.byContradiction fun hne =>
          h ⟨n, fun u hu => Classical.byContradiction fun hlt =>
            hne ⟨u, hu, Nat.not_lt.mp hlt⟩⟩)
    obtain ⟨N, hN⟩ := hBound
    -- Key: nodesBelow [] is not finite (it equals dom which is not finite)
    have hDomNotFin : ¬ Set.Finite (d.nodesBelow []) :=
      fun hfin => hNotFin (Set.Finite.subset hfin
        (fun w hw => (nodesBelow_root d w).mpr hw))
    -- By iterating pigeonhole_child N times from root [], we get a node
    -- of length N with infinite nodesBelow. But all nodes have length < N.
    -- Use Nat induction on the remaining depth budget (N - k).
    suffices ∀ budget k, budget = N - k → k ≤ N →
        ∀ u, u.length = k → d.dom u →
        ¬ Set.Finite (d.nodesBelow u) → False from
      this N 0 (by omega) (Nat.zero_le N) [] rfl d.root_mem hDomNotFin
    intro budget
    induction budget with
    | zero =>
      -- Budget = 0, so k = N. Node has length N but all nodes have length < N.
      intro k hbudget hkN u hulen hudom _
      have := hN u hudom; omega
    | succ m ih =>
      -- Budget = m + 1, so k < N. Pigeonhole gives a child with infinite
      -- descendants, consuming one unit of budget.
      intro k hbudget hkN u hulen hudom huinf
      obtain ⟨i, hi, hinf⟩ := pigeonhole_child d u hudom hFB huinf
      have hlen : (u ++ [i]).length = k + 1 := by simp [hulen]
      have hkN' : k + 1 ≤ N := by have := hN (u ++ [i]) hi; omega
      exact ih (k + 1) (by omega) hkN' (u ++ [i]) hlen hi hinf

/-- Koenig's Lemma: A finitely branching tree domain with infinitely
    many nodes has an infinite path.

    This is a fundamental result in combinatorics and logic, used in
    completeness proofs for search procedures in first-order logic
    (Gallier, Chapter 5, Theorem 5.4.1).

    Proof: By dependent choice (Classical.choice) and the pigeonhole
    principle. We build the path f(0), f(1), ... inductively. At each
    step we have a node u with infinitely many nodes below it. Since u
    is finitely branching, the pigeonhole principle gives a child
    u ++ [f(k)] that also has infinitely many nodes below it. Iterating
    produces the infinite path.

    The key auxiliary lemma is pigeonhole_child: if a finitely branching
    node has infinitely many descendants, at least one child does too. -/
noncomputable def konig_lemma (d : TreeDomain)
    (hFB : d.FinitelyBranching)
    (hInf : d.IsInfinite) :
    d.HasInfinitePath := by
  -- The root has infinitely many nodes below it
  have hRootInf : ¬ Set.Finite (d.nodesBelow []) :=
    fun hfin => finite_not_infinite d
      (Set.Finite.subset hfin (fun w hw => (nodesBelow_root d w).mpr hw))
      hInf
  -- Build the path by dependent choice via the pigeonhole principle.
  -- State type: a node u ∈ dom with infinite nodesBelow
  let State := { u : TreeAddr // d.dom u ∧ ¬ Set.Finite (d.nodesBelow u) }
  -- Initial state: root []
  let s0 : State := ⟨[], d.root_mem, hRootInf⟩
  -- Step function: given a state, produce the child index and next state.
  -- Uses Classical.choice to extract from the existential.
  let stepIdx : State → Nat := fun ⟨u, hu, hinf⟩ =>
    (pigeonhole_child d u hu hFB hinf).choose
  let stepNext : State → State := fun ⟨u, hu, hinf⟩ =>
    let i := (pigeonhole_child d u hu hFB hinf).choose
    ⟨u ++ [i],
     (pigeonhole_child d u hu hFB hinf).choose_spec.1,
     (pigeonhole_child d u hu hFB hinf).choose_spec.2⟩
  -- Key property: stepNext s has value = s.val ++ [stepIdx s]
  have hstep_val : ∀ s : State, (stepNext s).val = s.val ++ [stepIdx s] := by
    intro ⟨u, hu, hinf⟩; rfl
  -- Build the sequence of states via Nat.rec
  let stateSeq : Nat → State := fun n =>
    Nat.rec s0 (fun _ s => stepNext s) n
  -- The path function: child index at each step
  let f : Nat → Nat := fun n => stepIdx (stateSeq n)
  -- Key invariant: stateSeq n has value = prefix of path of length n
  -- Specifically: (stateSeq n).val = list of first n values of f
  -- We prove this by showing the recurrence:
  -- (stateSeq 0).val = []
  -- (stateSeq (n+1)).val = (stateSeq n).val ++ [f n]
  have hseq_zero : (stateSeq 0).val = [] := rfl
  have hseq_succ : ∀ n, (stateSeq (n + 1)).val = (stateSeq n).val ++ [f n] := by
    intro n
    -- stateSeq (n+1) = stepNext (stateSeq n)
    -- stepNext s has value s.val ++ [stepIdx s] = s.val ++ [f n]
    exact hstep_val (stateSeq n)
  -- Now show (stateSeq n).val = List.ofFn (fun i : Fin n => f i)
  -- by induction on n, using hseq_zero and hseq_succ.
  -- Instead of fighting List.ofFn, we use an alternative formulation:
  -- Every prefix of the path is in the domain, where we represent the
  -- prefix directly as (stateSeq n).val.
  -- The HasInfinitePath definition uses List.ofFn, so we need the
  -- equality (stateSeq n).val = List.ofFn (fun i : Fin n => f i).
  -- This is provable by induction, using the recurrence above plus the
  -- fact that List.ofFn for Fin (n+1) = List.ofFn for Fin n ++ [f n].
  -- The List.ofFn decomposition for Fin (n+1) is:
  -- List.ofFn g = (List.ofFn (fun i : Fin n => g i.castSucc)) ++ [g (Fin.last n)]
  -- This is available as List.ofFn_succ' in recent Lean/Mathlib.
  -- Without Mathlib, we prove the correspondence differently.
  -- Actually, let's just use a custom infinite path definition that avoids List.ofFn.
  -- HasInfinitePath says: ∃ f, ∀ n, List.ofFn (fun i : Fin n => f i) ∈ d.dom
  -- We have: ∀ n, (stateSeq n).val ∈ d.dom (from the state invariant)
  -- We need: (stateSeq n).val = List.ofFn (fun i : Fin n => f i)
  -- Let's prove this and be done.
  refine ⟨f, ?_⟩
  intro n
  -- Show: List.ofFn (fun i : Fin n => f i) ∈ d.dom
  -- It suffices to show: List.ofFn (fun i : Fin n => f i) = (stateSeq n).val
  -- since (stateSeq n).val ∈ d.dom by the state invariant.
  suffices heq : (stateSeq n).val = List.ofFn (fun i : Fin n => f i) from
    heq ▸ (stateSeq n).property.1
  -- Prove by induction on n
  induction n with
  | zero =>
    simp [List.ofFn, hseq_zero]
  | succ k ih =>
    rw [hseq_succ]
    -- Need: (stateSeq k).val ++ [f k] = List.ofFn (fun i : Fin (k+1) => f i)
    -- ih : (stateSeq k).val = List.ofFn (fun i : Fin k => f i)
    rw [ih]
    -- Need: List.ofFn (fun i : Fin k => f i) ++ [f k] = List.ofFn (fun i : Fin (k+1) => f i)
    -- By list_ofFn_snoc:
    -- List.ofFn g = List.ofFn (g . castSucc) ++ [g (Fin.last k)]
    -- where g = fun i : Fin (k+1) => f i.
    -- So RHS = List.ofFn (fun i : Fin k => f i.castSucc) ++ [f (Fin.last k)]
    -- = List.ofFn (fun i : Fin k => f i) ++ [f k]
    -- since i.castSucc.val = i.val and (Fin.last k).val = k.
    -- List.ofFn (fun i : Fin (k+1) => f i)
    -- = List.ofFn (fun i : Fin k => f i.castSucc) ++ [f (Fin.last k)]
    -- = List.ofFn (fun i : Fin k => f i) ++ [f k]
    have hsnoc := list_ofFn_snoc k (fun i : Fin (k + 1) => f ↑i)
    -- hsnoc: List.ofFn (fun i => f i) = ofFn (fun i => f i.castSucc) ++ [f (last k)]
    -- We need: ofFn (fun i => f i) ++ [f k] = ofFn (fun i => f i.castSucc) ++ [f (last k)]
    -- i.e., the same thing but with coercion cleanup on both sides.
    -- castSucc.val = val for Fin k, and (Fin.last k).val = k.
    have h1 : (fun i : Fin k => f (↑(i.castSucc) : Nat)) = (fun i : Fin k => f ↑i) :=
      funext (fun ⟨i, _⟩ => by simp [Fin.castSucc])
    have h2 : f ↑(Fin.last k) = f k := by simp [Fin.last]
    rw [h1, h2] at hsnoc
    exact hsnoc.symm

/-- Koenig's Lemma (contrapositive form): If a finitely branching tree
    domain has no infinite path, then the tree domain is finite.

    This form is often more directly useful in completeness proofs:
    if every branch of the search tree terminates, the tree is finite. -/
theorem konig_contrapositive (d : TreeDomain)
    (hFB : d.FinitelyBranching)
    (hNoPath : ¬ d.HasInfinitePath) :
    d.IsFinite :=
-- BEGIN PROOF
  -- Contrapositive of konig_lemma: if not finite, then infinite (by
  -- not_finite_is_infinite), then has infinite path (by konig_lemma),
  -- contradicting hNoPath.
  Classical.byContradiction fun hNotFin =>
    hNoPath (konig_lemma d hFB (not_finite_is_infinite d hFB hNotFin))

end TreeDomain

end LCS

-- ============================================================================
-- Countable types (enumeration infrastructure for Lindenbaum's lemma)
-- ============================================================================

/-- A type is countable if there exists a surjection from Nat onto it.
    This is the standard notion needed for Lindenbaum's lemma: we
    enumerate all formulae to build a maximal consistent extension. -/
class Countable (α : Type) where
  /-- A surjective enumeration function -/
  enumerate : Nat → α
  /-- The enumeration is surjective: every element is hit -/
  enumerate_surj : Function.Surjective enumerate

/-- At most countable: there is an injection into `Nat`. Unlike `Countable`
(a surjective enumeration), this admits the empty type (Definition 5.2.1:
symbol sets are "countable, possibly empty"). -/
class AtMostCountable (α : Type) : Prop where
  exists_injective : ∃ f : α → Nat, Function.Injective f

/-- A surjective enumeration gives an injection by choosing an index for each element. -/
instance Countable.instAtMostCountable [Countable α] : AtMostCountable α where
  exists_injective := by
    classical
    refine ⟨fun a => Classical.choose (Countable.enumerate_surj a), ?_⟩
    intro a b h
    have ha := Classical.choose_spec (Countable.enumerate_surj a)
    have hb := Classical.choose_spec (Countable.enumerate_surj b)
    exact ha.symm.trans ((congrArg Countable.enumerate h).trans hb)

namespace Countable

/-- A nonempty type admitting an injection into `Nat` has a surjective enumeration. -/
noncomputable def ofAtMostCountable [AtMostCountable α] [Nonempty α] : Countable α := by
  classical
  let f := Classical.choose (AtMostCountable.exists_injective (α := α))
  have hf := Classical.choose_spec (AtMostCountable.exists_injective (α := α))
  exact {
    enumerate := fun n => if h : ∃ a, f a = n then Classical.choose h
      else Classical.choice ‹Nonempty α›
    enumerate_surj := fun a => by
      refine ⟨f a, ?_⟩
      dsimp
      rw [dif_pos (show ∃ b, f b = f a from ⟨a, rfl⟩)]
      exact hf (Classical.choose_spec (show ∃ b, f b = f a from ⟨a, rfl⟩)) }

/-- Nat is countable (identity enumeration). -/
instance instCountableNat : Countable Nat where
  enumerate := id
  enumerate_surj := fun n => ⟨n, rfl⟩

/-- Sum of two countable types is countable.
    Evens map to the left summand, odds to the right. -/
noncomputable instance instCountableSum [Countable α] [Countable β] :
    Countable (α ⊕ β) where
  enumerate := fun n =>
    if n % 2 = 0 then Sum.inl (Countable.enumerate (n / 2))
    else Sum.inr (Countable.enumerate (n / 2))
  enumerate_surj := fun
    | Sum.inl a => by
      obtain ⟨na, rfl⟩ := Countable.enumerate_surj a
      exact ⟨2 * na, by simp [Nat.mul_mod_right]⟩
    | Sum.inr b => by
      obtain ⟨nb, rfl⟩ := Countable.enumerate_surj b
      refine ⟨2 * nb + 1, ?_⟩
      show (if (2 * nb + 1) % 2 = 0 then _ else _) = _
      have h1 : ¬ ((2 * nb + 1) % 2 = 0) := by omega
      rw [if_neg h1]
      show Sum.inr (Countable.enumerate ((2 * nb + 1) / 2)) = Sum.inr (Countable.enumerate nb)
      have h2 : (2 * nb + 1) / 2 = nb := by omega
      rw [h2]

/-- If there is a surjection from a countable type onto β, then β is countable. -/
@[reducible]
noncomputable def ofSurjection [Countable α] (f : α → β)
    (hf : Function.Surjective f) : Countable β where
  enumerate := fun n => f (Countable.enumerate n)
  enumerate_surj := fun b => by
    obtain ⟨a, rfl⟩ := hf b
    obtain ⟨n, rfl⟩ := Countable.enumerate_surj a
    exact ⟨n, rfl⟩

end Countable
