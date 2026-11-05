import LCS.Item
import LCS.Util
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Semantics.Equivalence
import LCS.FirstOrder.SemanticsN.Substitution
import LCS.Herbrand.PrenexForm.Part1
import Attach
import LCS.Herbrand.PrenexForm.Part2.ProofsStamp

section
namespace LCS.Herbrand.PrenexForm
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Equivalence
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN.Substitution



-- ===================================================================
-- Theorem 7.2.1: Prenex normal form existence
-- ===================================================================

/-- Theorem 7.2.1: For every formula A, a prenex formula B can be constructed such that A equiv B is valid (A and B are logically equivalent). The constructive witness is toPrenex A. This is the main theorem stating that toPrenex produces a prenex formula and that it is equivalent to the input. -/
@[blueprint "chap7__theorem_7_2_1" (main := true)]
theorem prenex_normal_form_exists {L : Language}
    (A : FormulaN L) :
    ∃ B : FormulaN L,
      isPrenex B ∧ foLogEquivN A B 





-- ===================================================================
-- Theorem 7.2.1 (infrastructure): Prenex helper semantic lemmas
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Pulling quantifiers from a prefix past the right conjunct, when the
    prefix variables are not free in the left conjunct M. -/
theorem toPrenexHelper_conj_right {L : Language}
    (prefix_ : List (QuantifierKind × Nat)) (M body : FormulaN L)
    (hfresh : ∀ p ∈ prefix_, ¬ Membership.mem (formulaFVN M) p.2) :
    foLogEquivN
      (toPrenexHelper prefix_ (FormulaN.conj M body))
      (FormulaN.conj M (toPrenexHelper prefix_ body)) := by
-- BEGIN PROOF
  induction prefix_ with
  | nil => simp [toPrenexHelper]; exact foLogEquivN_refl _
  | cons q rest ih =>
    have hfreshQ := hfresh q (List.Mem.head rest)
    have hfreshRest : ∀ p ∈ rest, ¬ Membership.mem (formulaFVN M) p.2 :=
      fun p hp => hfresh p (List.Mem.tail q hp)
    match q with
    | (QuantifierKind.universal, x) =>
      simp only [toPrenexHelper]
      exact foLogEquivN_trans
        (foLogEquivN_all x (ih hfreshRest))
        (foLogEquivN_symm (prenex_conj_right_all x M
          (toPrenexHelper rest body) hfreshQ))
    | (QuantifierKind.existential, x) =>
      simp only [toPrenexHelper]
      exact foLogEquivN_trans
        (foLogEquivN_ex x (ih hfreshRest))
        (foLogEquivN_symm (prenex_conj_right_ex x M
          (toPrenexHelper rest body) hfreshQ))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Pulling quantifiers from a prefix past the left conjunct, when the
    prefix variables are not free in the right conjunct M. -/
theorem toPrenexHelper_conj_left {L : Language}
    (prefix_ : List (QuantifierKind × Nat)) (body M : FormulaN L)
    (hfresh : ∀ p ∈ prefix_, ¬ Membership.mem (formulaFVN M) p.2) :
    foLogEquivN
      (toPrenexHelper prefix_ (FormulaN.conj body M))
      (FormulaN.conj (toPrenexHelper prefix_ body) M) := by
-- BEGIN PROOF
  induction prefix_ with
  | nil => simp [toPrenexHelper]; exact foLogEquivN_refl _
  | cons q rest ih =>
    have hfreshQ := hfresh q (List.Mem.head rest)
    have hfreshRest : ∀ p ∈ rest, ¬ Membership.mem (formulaFVN M) p.2 :=
      fun p hp => hfresh p (List.Mem.tail q hp)
    match q with
    | (QuantifierKind.universal, x) =>
      simp only [toPrenexHelper]
      exact foLogEquivN_trans
        (foLogEquivN_all x (ih hfreshRest))
        (foLogEquivN_symm (prenex_equiv_d_univ_conj x
          (toPrenexHelper rest body) M hfreshQ))
    | (QuantifierKind.existential, x) =>
      simp only [toPrenexHelper]
      exact foLogEquivN_trans
        (foLogEquivN_ex x (ih hfreshRest))
        (foLogEquivN_symm (prenex_equiv_d_ex_conj x
          (toPrenexHelper rest body) M hfreshQ))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Pulling quantifiers from a prefix past the right disjunct, when the
    prefix variables are not free in the left disjunct M. -/
theorem toPrenexHelper_disj_right {L : Language}
    (prefix_ : List (QuantifierKind × Nat)) (M body : FormulaN L)
    (hfresh : ∀ p ∈ prefix_, ¬ Membership.mem (formulaFVN M) p.2) :
    foLogEquivN
      (toPrenexHelper prefix_ (FormulaN.disj M body))
      (FormulaN.disj M (toPrenexHelper prefix_ body)) := by
-- BEGIN PROOF
  induction prefix_ with
  | nil => simp [toPrenexHelper]; exact foLogEquivN_refl _
  | cons q rest ih =>
    have hfreshQ := hfresh q (List.Mem.head rest)
    have hfreshRest : ∀ p ∈ rest, ¬ Membership.mem (formulaFVN M) p.2 :=
      fun p hp => hfresh p (List.Mem.tail q hp)
    match q with
    | (QuantifierKind.universal, x) =>
      simp only [toPrenexHelper]
      exact foLogEquivN_trans
        (foLogEquivN_all x (ih hfreshRest))
        (foLogEquivN_symm (prenex_disj_right_all x M
          (toPrenexHelper rest body) hfreshQ))
    | (QuantifierKind.existential, x) =>
      simp only [toPrenexHelper]
      exact foLogEquivN_trans
        (foLogEquivN_ex x (ih hfreshRest))
        (foLogEquivN_symm (prenex_disj_right_ex x M
          (toPrenexHelper rest body) hfreshQ))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Pulling quantifiers from a prefix past the left disjunct, when the
    prefix variables are not free in the right disjunct M. -/
theorem toPrenexHelper_disj_left {L : Language}
    (prefix_ : List (QuantifierKind × Nat)) (body M : FormulaN L)
    (hfresh : ∀ p ∈ prefix_, ¬ Membership.mem (formulaFVN M) p.2) :
    foLogEquivN
      (toPrenexHelper prefix_ (FormulaN.disj body M))
      (FormulaN.disj (toPrenexHelper prefix_ body) M) := by
-- BEGIN PROOF
  induction prefix_ with
  | nil => simp [toPrenexHelper]; exact foLogEquivN_refl _
  | cons q rest ih =>
    have hfreshQ := hfresh q (List.Mem.head rest)
    have hfreshRest : ∀ p ∈ rest, ¬ Membership.mem (formulaFVN M) p.2 :=
      fun p hp => hfresh p (List.Mem.tail q hp)
    match q with
    | (QuantifierKind.universal, x) =>
      simp only [toPrenexHelper]
      exact foLogEquivN_trans
        (foLogEquivN_all x (ih hfreshRest))
        (foLogEquivN_symm (prenex_equiv_d_univ_disj x
          (toPrenexHelper rest body) M hfreshQ))
    | (QuantifierKind.existential, x) =>
      simp only [toPrenexHelper]
      exact foLogEquivN_trans
        (foLogEquivN_ex x (ih hfreshRest))
        (foLogEquivN_symm (prenex_equiv_d_ex_disj x
          (toPrenexHelper rest body) M hfreshQ))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Dualizing the prefix and negating the body yields the negation of the
    original quantifier-wrapped formula. -/
theorem toPrenexHelper_neg_dual {L : Language}
    (prefix_ : List (QuantifierKind × Nat)) (body : FormulaN L) :
    foLogEquivN
      (toPrenexHelper (dualPrefix prefix_) (FormulaN.neg body))
      (FormulaN.neg (toPrenexHelper prefix_ body)) := by
-- BEGIN PROOF
  induction prefix_ with
  | nil => simp [toPrenexHelper, dualPrefix]; exact foLogEquivN_refl _
  | cons q rest ih =>
    match q with
    | (QuantifierKind.universal, x) =>
      simp only [dualPrefix, List.map, QuantifierKind.dual, toPrenexHelper]
      exact foLogEquivN_trans
        (foLogEquivN_ex x ih)
        (foLogEquivN_symm (prenex_equiv_c_neg_all x
          (toPrenexHelper rest body)))
    | (QuantifierKind.existential, x) =>
      simp only [dualPrefix, List.map, QuantifierKind.dual, toPrenexHelper]
      exact foLogEquivN_trans
        (foLogEquivN_all x ih)
        (foLogEquivN_symm (prenex_equiv_c_neg_ex x
          (toPrenexHelper rest body)))

-- ATTACH-BLOCKER: private declaration
private theorem toPrenexHelper_impl_right {L : Language}
    (prefix_ : List (QuantifierKind × Nat)) (M body : FormulaN L)
    (hfresh : ∀ p ∈ prefix_, ¬ Membership.mem (formulaFVN M) p.2) :
    foLogEquivN
      (toPrenexHelper prefix_ (FormulaN.impl M body))
      (FormulaN.impl M (toPrenexHelper prefix_ body)) := by
  induction prefix_ with
  | nil => exact foLogEquivN_refl _
  | cons p rest ih =>
    have hfreshQ := hfresh p (List.Mem.head rest)
    have hfreshRest : ∀ q ∈ rest,
        ¬ Membership.mem (formulaFVN M) q.2 :=
      fun q hq => hfresh q (List.Mem.tail p hq)
    rcases p with ⟨q, x⟩
    cases q
    · exact foLogEquivN_trans
        (foLogEquivN_all x (ih hfreshRest))
        (prenex_equiv_b_univ_impl_right x M
          (toPrenexHelper rest body) hfreshQ)
    · exact foLogEquivN_trans
        (foLogEquivN_ex x (ih hfreshRest))
        (prenex_equiv_b_ex_impl_right x M
          (toPrenexHelper rest body) hfreshQ)

-- ATTACH-BLOCKER: private declaration
private theorem toPrenexHelper_impl_left_dual {L : Language}
    (prefix_ : List (QuantifierKind × Nat)) (body M : FormulaN L)
    (hfresh : ∀ p ∈ prefix_, ¬ Membership.mem (formulaFVN M) p.2) :
    foLogEquivN
      (toPrenexHelper (dualPrefix prefix_) (FormulaN.impl body M))
      (FormulaN.impl (toPrenexHelper prefix_ body) M) := by
  induction prefix_ with
  | nil => exact foLogEquivN_refl _
  | cons p rest ih =>
    have hfreshQ := hfresh p (List.Mem.head rest)
    have hfreshRest : ∀ q ∈ rest,
        ¬ Membership.mem (formulaFVN M) q.2 :=
      fun q hq => hfresh q (List.Mem.tail p hq)
    rcases p with ⟨q, x⟩
    cases q
    · exact foLogEquivN_trans
        (foLogEquivN_ex x (ih hfreshRest))
        (prenex_equiv_a_ex_impl_left x
          (toPrenexHelper rest body) M hfreshQ)
    · exact foLogEquivN_trans
        (foLogEquivN_all x (ih hfreshRest))
        (prenex_equiv_a_univ_impl_left x
          (toPrenexHelper rest body) M hfreshQ)

-- ATTACH-BLOCKER: private declaration
private theorem toPrenexHelper_append {L : Language}
    (left right : List (QuantifierKind × Nat)) (body : FormulaN L) :
    toPrenexHelper (left ++ right) body =
      toPrenexHelper left (toPrenexHelper right body) := by
  induction left with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨q, x⟩
    cases q <;> simp [toPrenexHelper, ih]

-- ATTACH-BLOCKER: private declaration
private theorem toPrenexHelper_rebuild {L : Language}
    (A : FormulaN L) :
    toPrenexHelper (prenexPrefix A) (prenexMatrix A) = A := by
  induction A with
  | all x A ih => simp [prenexPrefix, prenexMatrix, toPrenexHelper, ih]
  | ex x A ih => simp [prenexPrefix, prenexMatrix, toPrenexHelper, ih]
  | _ => rfl

-- ATTACH-BLOCKER: private declaration
private theorem toPrenexHelper_equiv {L : Language}
    (prefix_ : List (QuantifierKind × Nat)) {A B : FormulaN L}
    (h : foLogEquivN A B) :
    foLogEquivN (toPrenexHelper prefix_ A)
      (toPrenexHelper prefix_ B) := by
  induction prefix_ with
  | nil => exact h
  | cons p rest ih =>
    rcases p with ⟨q, x⟩
    cases q
    · exact foLogEquivN_all x ih
    · exact foLogEquivN_ex x ih

-- ATTACH-BLOCKER: private declaration
private theorem toPrenexHelper_fv_iff {L : Language}
    (prefix_ : List (QuantifierKind × Nat)) (body : FormulaN L)
    (x : Nat) :
    x ∈ formulaFVN (toPrenexHelper prefix_ body) ↔
      x ∈ formulaFVN body ∧
        ∀ p ∈ prefix_, x ≠ p.2 := by
  induction prefix_ with
  | nil => simp [toPrenexHelper]
  | cons p rest ih =>
    rcases p with ⟨q, y⟩
    cases q
    · constructor
      · intro hx
        have hrest := ih.mp hx.1
        refine ⟨hrest.1, ?_⟩
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact hx.2
        · exact hrest.2 p hp
      · rintro ⟨hbody, hall⟩
        refine ⟨ih.mpr ⟨hbody, ?_⟩, hall _ (List.Mem.head rest)⟩
        intro p hp
        exact hall p (List.Mem.tail (QuantifierKind.universal, y) hp)
    · constructor
      · intro hx
        have hrest := ih.mp hx.1
        refine ⟨hrest.1, ?_⟩
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact hx.2
        · exact hrest.2 p hp
      · rintro ⟨hbody, hall⟩
        refine ⟨ih.mpr ⟨hbody, ?_⟩, hall _ (List.Mem.head rest)⟩
        intro p hp
        exact hall p (List.Mem.tail (QuantifierKind.existential, y) hp)

-- ATTACH-BLOCKER: private declaration
private theorem toPrenexHelper_bv_iff {L : Language}
    (prefix_ : List (QuantifierKind × Nat)) (body : FormulaN L)
    (x : Nat) :
    x ∈ formulaBVN (toPrenexHelper prefix_ body) ↔
      x ∈ formulaBVN body ∨
        ∃ p ∈ prefix_, x = p.2 := by
  induction prefix_ with
  | nil => simp [toPrenexHelper]
  | cons p rest ih =>
    rcases p with ⟨q, y⟩
    cases q
    · constructor
      · intro hx
        rcases hx with hrest | hxy
        · rcases ih.mp hrest with hbody | ⟨p, hp, hpx⟩
          · exact Or.inl hbody
          · exact Or.inr ⟨p, List.Mem.tail _ hp, hpx⟩
        · exact Or.inr ⟨(QuantifierKind.universal, y),
            List.Mem.head rest, hxy⟩
      · intro hx
        rcases hx with hbody | ⟨p, hp, hpx⟩
        · exact Or.inl (ih.mpr (Or.inl hbody))
        · simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact Or.inr hpx
          · exact Or.inl (ih.mpr (Or.inr ⟨p, hp, hpx⟩))
    · constructor
      · intro hx
        rcases hx with hrest | hxy
        · rcases ih.mp hrest with hbody | ⟨p, hp, hpx⟩
          · exact Or.inl hbody
          · exact Or.inr ⟨p, List.Mem.tail _ hp, hpx⟩
        · exact Or.inr ⟨(QuantifierKind.existential, y),
            List.Mem.head rest, hxy⟩
      · intro hx
        rcases hx with hbody | ⟨p, hp, hpx⟩
        · exact Or.inl (ih.mpr (Or.inl hbody))
        · simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact Or.inr hpx
          · exact Or.inl (ih.mpr (Or.inr ⟨p, hp, hpx⟩))

-- ATTACH-BLOCKER: private declaration
private theorem prenexPrefix_bv {L : Language} (A : FormulaN L)
    (p : QuantifierKind × Nat) (hp : p ∈ prenexPrefix A) :
    p.2 ∈ formulaBVN A := by
  induction A with
  | all x A ih =>
    simp only [prenexPrefix, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact Or.inr rfl
    · exact Or.inl (ih hp)
  | ex x A ih =>
    simp only [prenexPrefix, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact Or.inr rfl
    · exact Or.inl (ih hp)
  | _ => simp [prenexPrefix] at hp

-- ATTACH-BLOCKER: private declaration
private theorem prenexMatrix_bv {L : Language} (A : FormulaN L)
    (x : Nat) (hx : x ∈ formulaBVN (prenexMatrix A)) :
    x ∈ formulaBVN A := by
  induction A with
  | all y A ih => exact Or.inl (ih hx)
  | ex y A ih => exact Or.inl (ih hx)
  | _ => exact hx

-- ATTACH-BLOCKER: private declaration
private theorem prenexMatrix_fv_or_bv {L : Language} (A : FormulaN L)
    (x : Nat) (hx : x ∈ formulaFVN (prenexMatrix A)) :
    x ∈ formulaFVN A ∨ x ∈ formulaBVN A := by
  induction A with
  | all y A ih =>
    rcases ih hx with hfv | hbv
    · by_cases hxy : x = y
      · exact Or.inr (Or.inr hxy)
      · exact Or.inl ⟨hfv, hxy⟩
    · exact Or.inr (Or.inl hbv)
  | ex y A ih =>
    rcases ih hx with hfv | hbv
    · by_cases hxy : x = y
      · exact Or.inr (Or.inr hxy)
      · exact Or.inl ⟨hfv, hxy⟩
    · exact Or.inr (Or.inl hbv)
  | _ => exact Or.inl hx

-- ATTACH-BLOCKER: private declaration
private theorem mem_dualPrefix_of_mem
    (prefix_ : List (QuantifierKind × Nat))
    (p : QuantifierKind × Nat) (hp : p ∈ prefix_) :
    (p.1.dual, p.2) ∈ dualPrefix prefix_ := by
  exact List.mem_map_of_mem
    (f := fun q => (q.1.dual, q.2)) hp

-- ATTACH-BLOCKER: private declaration
private theorem dualPrefix_mem_source
    (prefix_ : List (QuantifierKind × Nat))
    (p : QuantifierKind × Nat) (hp : p ∈ dualPrefix prefix_) :
    ∃ q ∈ prefix_, p.2 = q.2 := by
  simp only [dualPrefix, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact ⟨q, hq, rfl⟩

-- ATTACH-BLOCKER: private declaration
private theorem prenexRebuild_fv {L : Language}
    (A : FormulaN L) (x : Nat)
    (hmatrix : x ∈ formulaFVN (prenexMatrix A))
    (hprefix : ∀ p ∈ prenexPrefix A, x ≠ p.2) :
    x ∈ formulaFVN A := by
  rw [← toPrenexHelper_rebuild A]
  exact (toPrenexHelper_fv_iff
    (prenexPrefix A) (prenexMatrix A) x).mpr
      ⟨hmatrix, hprefix⟩

-- ATTACH-BLOCKER: private declaration
private theorem toPrenexRaw_fv_subset {L : Language}
    (A : FormulaN L) :
    ∀ x, x ∈ formulaFVN (toPrenexRaw A) →
      x ∈ formulaFVN A := by
  induction A with
  | predN P ts => exact fun _ hx => hx
  | eq_ hL t₁ t₂ => exact fun _ hx => hx
  | neg A ih =>
    intro x hx
    let pA := toPrenexRaw A
    have hout := (toPrenexHelper_fv_iff
      (dualPrefix (prenexPrefix pA)) (.neg (prenexMatrix pA)) x).mp hx
    have hpA : x ∈ formulaFVN pA := by
      apply prenexRebuild_fv pA x hout.1
      intro p hp
      exact hout.2 (p.1.dual, p.2)
        (mem_dualPrefix_of_mem (prenexPrefix pA) p hp)
    exact ih x hpA
  | conj A B ihA ihB =>
    intro x hx
    let pA := toPrenexRaw A
    let pB := toPrenexRaw B
    have hout := (toPrenexHelper_fv_iff
      (prenexPrefix pA ++ prenexPrefix pB)
      (.conj (prenexMatrix pA) (prenexMatrix pB)) x).mp hx
    rcases hout.1 with hA | hB
    · exact Or.inl (ihA x (prenexRebuild_fv pA x hA
        (fun p hp => hout.2 p (by simp [hp]))))
    · exact Or.inr (ihB x (prenexRebuild_fv pB x hB
        (fun p hp => hout.2 p (by simp [hp]))))
  | disj A B ihA ihB =>
    intro x hx
    let pA := toPrenexRaw A
    let pB := toPrenexRaw B
    have hout := (toPrenexHelper_fv_iff
      (prenexPrefix pA ++ prenexPrefix pB)
      (.disj (prenexMatrix pA) (prenexMatrix pB)) x).mp hx
    rcases hout.1 with hA | hB
    · exact Or.inl (ihA x (prenexRebuild_fv pA x hA
        (fun p hp => hout.2 p (by simp [hp]))))
    · exact Or.inr (ihB x (prenexRebuild_fv pB x hB
        (fun p hp => hout.2 p (by simp [hp]))))
  | impl A B ihA ihB =>
    intro x hx
    let pA := toPrenexRaw A
    let pB := toPrenexRaw B
    have hout := (toPrenexHelper_fv_iff
      (dualPrefix (prenexPrefix pA) ++ prenexPrefix pB)
      (.impl (prenexMatrix pA) (prenexMatrix pB)) x).mp hx
    rcases hout.1 with hA | hB
    · exact Or.inl (ihA x (prenexRebuild_fv pA x hA
        (fun p hp => hout.2 (p.1.dual, p.2)
            (by
              apply List.mem_append_left
              exact mem_dualPrefix_of_mem (prenexPrefix pA) p hp))))
    · exact Or.inr (ihB x (prenexRebuild_fv pB x hB
        (fun p hp => hout.2 p (by simp [hp]))))
  | all y A ih =>
    intro x hx
    exact ⟨ih x hx.1, hx.2⟩
  | ex y A ih =>
    intro x hx
    exact ⟨ih x hx.1, hx.2⟩

-- ATTACH-BLOCKER: private declaration
private theorem toPrenexRaw_bv_subset {L : Language}
    (A : FormulaN L) :
    ∀ x, x ∈ formulaBVN (toPrenexRaw A) →
      x ∈ formulaBVN A := by
  induction A with
  | predN P ts => exact fun _ hx => hx
  | eq_ hL t₁ t₂ => exact fun _ hx => hx
  | neg A ih =>
    intro x hx
    let pA := toPrenexRaw A
    rcases (toPrenexHelper_bv_iff
      (dualPrefix (prenexPrefix pA)) (.neg (prenexMatrix pA)) x).mp hx with
      hmatrix | ⟨p, hp, hpx⟩
    · exact ih x (prenexMatrix_bv pA x hmatrix)
    · obtain ⟨q, hq, hpq⟩ :=
        dualPrefix_mem_source (prenexPrefix pA) p hp
      apply ih x
      rw [hpx, hpq]
      exact prenexPrefix_bv pA q hq
  | conj A B ihA ihB =>
    intro x hx
    let pA := toPrenexRaw A
    let pB := toPrenexRaw B
    rcases (toPrenexHelper_bv_iff
      (prenexPrefix pA ++ prenexPrefix pB)
      (.conj (prenexMatrix pA) (prenexMatrix pB)) x).mp hx with
      hmatrix | ⟨p, hp, hpx⟩
    · rcases hmatrix with hA | hB
      · exact Or.inl (ihA x (prenexMatrix_bv pA x hA))
      · exact Or.inr (ihB x (prenexMatrix_bv pB x hB))
    · rcases List.mem_append.mp hp with hpA | hpB
      · apply Or.inl
        apply ihA x
        rw [hpx]
        exact prenexPrefix_bv pA p hpA
      · apply Or.inr
        apply ihB x
        rw [hpx]
        exact prenexPrefix_bv pB p hpB
  | disj A B ihA ihB =>
    intro x hx
    let pA := toPrenexRaw A
    let pB := toPrenexRaw B
    rcases (toPrenexHelper_bv_iff
      (prenexPrefix pA ++ prenexPrefix pB)
      (.disj (prenexMatrix pA) (prenexMatrix pB)) x).mp hx with
      hmatrix | ⟨p, hp, hpx⟩
    · rcases hmatrix with hA | hB
      · exact Or.inl (ihA x (prenexMatrix_bv pA x hA))
      · exact Or.inr (ihB x (prenexMatrix_bv pB x hB))
    · rcases List.mem_append.mp hp with hpA | hpB
      · apply Or.inl
        apply ihA x
        rw [hpx]
        exact prenexPrefix_bv pA p hpA
      · apply Or.inr
        apply ihB x
        rw [hpx]
        exact prenexPrefix_bv pB p hpB
  | impl A B ihA ihB =>
    intro x hx
    let pA := toPrenexRaw A
    let pB := toPrenexRaw B
    rcases (toPrenexHelper_bv_iff
      (dualPrefix (prenexPrefix pA) ++ prenexPrefix pB)
      (.impl (prenexMatrix pA) (prenexMatrix pB)) x).mp hx with
      hmatrix | ⟨p, hp, hpx⟩
    · rcases hmatrix with hA | hB
      · exact Or.inl (ihA x (prenexMatrix_bv pA x hA))
      · exact Or.inr (ihB x (prenexMatrix_bv pB x hB))
    · rcases List.mem_append.mp hp with hpA | hpB
      · obtain ⟨q, hq, hpq⟩ :=
          dualPrefix_mem_source (prenexPrefix pA) p hpA
        apply Or.inl
        apply ihA x
        rw [hpx, hpq]
        exact prenexPrefix_bv pA q hq
      · apply Or.inr
        apply ihB x
        rw [hpx]
        exact prenexPrefix_bv pB p hpB
  | all y A ih =>
    intro x hx
    rcases hx with hx | rfl
    · exact Or.inl (ih x hx)
    · exact Or.inr rfl
  | ex y A ih =>
    intro x hx
    rcases hx with hx | rfl
    · exact Or.inl (ih x hx)
    · exact Or.inr rfl

-- ATTACH-BLOCKER: private declaration
private theorem isRectified_union_left {L : Language}
    (A B : FormulaN L)
    (hFresh : ∀ x, ¬
      ((x ∈ formulaFVN A ∨ x ∈ formulaFVN B) ∧
       (x ∈ formulaBVN A ∨ x ∈ formulaBVN B)))
    (hDistinct : distinctQuantifierBindings A) :
    isRectified A := by
  constructor
  · intro x hx
    exact hFresh x ⟨Or.inl hx.1, Or.inl hx.2⟩
  · exact hDistinct

-- ATTACH-BLOCKER: private declaration
private theorem isRectified_union_right {L : Language}
    (A B : FormulaN L)
    (hFresh : ∀ x, ¬
      ((x ∈ formulaFVN A ∨ x ∈ formulaFVN B) ∧
       (x ∈ formulaBVN A ∨ x ∈ formulaBVN B)))
    (hDistinct : distinctQuantifierBindings B) :
    isRectified B := by
  constructor
  · intro x hx
    exact hFresh x ⟨Or.inr hx.1, Or.inr hx.2⟩
  · exact hDistinct

-- ATTACH-BLOCKER: private declaration
private theorem isRectified_all_body {L : Language}
    (y : Nat) (A : FormulaN L)
    (hFresh : boundVarsFresh (.all y A))
    (hDistinct : distinctQuantifierBindings (.all y A)) :
    isRectified A := by
  constructor
  · intro x hx
    by_cases hxy : x = y
    · subst x
      exact hDistinct.2 hx.2
    · apply hFresh x
      exact ⟨⟨hx.1, hxy⟩, Or.inl hx.2⟩
  · exact hDistinct.1

-- ATTACH-BLOCKER: private declaration
private theorem isRectified_ex_body {L : Language}
    (y : Nat) (A : FormulaN L)
    (hFresh : boundVarsFresh (.ex y A))
    (hDistinct : distinctQuantifierBindings (.ex y A)) :
    isRectified A := by
  constructor
  · intro x hx
    by_cases hxy : x = y
    · subst x
      exact hDistinct.2 hx.2
    · apply hFresh x
      exact ⟨⟨hx.1, hxy⟩, Or.inl hx.2⟩
  · exact hDistinct.1

-- ATTACH-BLOCKER: private declaration
private theorem toPrenexRaw_binary_fresh {L : Language}
    (A B : FormulaN L)
    (hFresh : ∀ x, ¬
      ((x ∈ formulaFVN A ∨ x ∈ formulaFVN B) ∧
       (x ∈ formulaBVN A ∨ x ∈ formulaBVN B)))
    (hDisjoint : ∀ x, ¬
      (x ∈ formulaBVN A ∧ x ∈ formulaBVN B)) :
    (∀ p ∈ prenexPrefix (toPrenexRaw B),
      ¬ p.2 ∈ formulaFVN (prenexMatrix (toPrenexRaw A))) ∧
    (∀ p ∈ prenexPrefix (toPrenexRaw A),
      ¬ p.2 ∈ formulaFVN (toPrenexRaw B)) := by
  constructor
  · intro p hp hmatrix
    have hpB : p.2 ∈ formulaBVN B :=
      toPrenexRaw_bv_subset B p.2
        (prenexPrefix_bv (toPrenexRaw B) p hp)
    rcases prenexMatrix_fv_or_bv (toPrenexRaw A) p.2 hmatrix with
      hfv | hbv
    · exact hFresh p.2
        ⟨Or.inl (toPrenexRaw_fv_subset A p.2 hfv), Or.inr hpB⟩
    · exact hDisjoint p.2
        ⟨toPrenexRaw_bv_subset A p.2 hbv, hpB⟩
  · intro p hp hfv
    have hpA : p.2 ∈ formulaBVN A :=
      toPrenexRaw_bv_subset A p.2
        (prenexPrefix_bv (toPrenexRaw A) p hp)
    exact hFresh p.2
      ⟨Or.inr (toPrenexRaw_fv_subset B p.2 hfv), Or.inl hpA⟩

-- ATTACH-BLOCKER: private declaration
private theorem toPrenexRaw_equiv_of_rectified {L : Language}
    (A : FormulaN L) (hRect : isRectified A) :
    foLogEquivN A (toPrenexRaw A) := by
  induction A with
  | predN P ts => exact foLogEquivN_refl _
  | eq_ hL t₁ t₂ => exact foLogEquivN_refl _
  | neg A ih =>
    have hRectA : isRectified A := hRect
    have hMove := toPrenexHelper_neg_dual
      (prenexPrefix (toPrenexRaw A))
      (prenexMatrix (toPrenexRaw A))
    have hRaw :
        foLogEquivN (toPrenexRaw (.neg A))
          (.neg (toPrenexRaw A)) := by
      simpa only [toPrenexRaw, toPrenexHelper_rebuild] using hMove
    exact foLogEquivN_trans (foLogEquivN_neg (ih hRectA))
      (foLogEquivN_symm hRaw)
  | conj A B ihA ihB =>
    have hFresh : ∀ x, ¬
        ((x ∈ formulaFVN A ∨ x ∈ formulaFVN B) ∧
         (x ∈ formulaBVN A ∨ x ∈ formulaBVN B)) := hRect.1
    have hDistinct : distinctQuantifierBindings A ∧
        distinctQuantifierBindings B ∧
        ∀ x, ¬ (x ∈ formulaBVN A ∧ x ∈ formulaBVN B) :=
      hRect.2
    have hRectA := isRectified_union_left A B hFresh hDistinct.1
    have hRectB := isRectified_union_right A B hFresh hDistinct.2.1
    obtain ⟨hFreshB, hFreshA⟩ :=
      toPrenexRaw_binary_fresh A B hFresh hDistinct.2.2
    let pA := toPrenexRaw A
    let pB := toPrenexRaw B
    have hMoveB := toPrenexHelper_conj_right
      (prenexPrefix pB) (prenexMatrix pA) (prenexMatrix pB) hFreshB
    have hMoveA := toPrenexHelper_conj_left
      (prenexPrefix pA) (prenexMatrix pA) pB hFreshA
    have hCombined :
        foLogEquivN
          (toPrenexHelper (prenexPrefix pA ++ prenexPrefix pB)
            (.conj (prenexMatrix pA) (prenexMatrix pB)))
          (.conj pA pB) := by
      rw [toPrenexHelper_append]
      exact foLogEquivN_trans
        (toPrenexHelper_equiv (prenexPrefix pA) hMoveB)
        (by simpa only [toPrenexHelper_rebuild] using hMoveA)
    exact foLogEquivN_trans
      (foLogEquivN_conj (ihA hRectA) (ihB hRectB))
      (by
        simpa only [toPrenexRaw] using
          (foLogEquivN_symm hCombined))
  | disj A B ihA ihB =>
    have hFresh : ∀ x, ¬
        ((x ∈ formulaFVN A ∨ x ∈ formulaFVN B) ∧
         (x ∈ formulaBVN A ∨ x ∈ formulaBVN B)) := hRect.1
    have hDistinct : distinctQuantifierBindings A ∧
        distinctQuantifierBindings B ∧
        ∀ x, ¬ (x ∈ formulaBVN A ∧ x ∈ formulaBVN B) :=
      hRect.2
    have hRectA := isRectified_union_left A B hFresh hDistinct.1
    have hRectB := isRectified_union_right A B hFresh hDistinct.2.1
    obtain ⟨hFreshB, hFreshA⟩ :=
      toPrenexRaw_binary_fresh A B hFresh hDistinct.2.2
    let pA := toPrenexRaw A
    let pB := toPrenexRaw B
    have hMoveB := toPrenexHelper_disj_right
      (prenexPrefix pB) (prenexMatrix pA) (prenexMatrix pB) hFreshB
    have hMoveA := toPrenexHelper_disj_left
      (prenexPrefix pA) (prenexMatrix pA) pB hFreshA
    have hCombined :
        foLogEquivN
          (toPrenexHelper (prenexPrefix pA ++ prenexPrefix pB)
            (.disj (prenexMatrix pA) (prenexMatrix pB)))
          (.disj pA pB) := by
      rw [toPrenexHelper_append]
      exact foLogEquivN_trans
        (toPrenexHelper_equiv (prenexPrefix pA) hMoveB)
        (by simpa only [toPrenexHelper_rebuild] using hMoveA)
    exact foLogEquivN_trans
      (foLogEquivN_disj (ihA hRectA) (ihB hRectB))
      (by
        simpa only [toPrenexRaw] using
          (foLogEquivN_symm hCombined))
  | impl A B ihA ihB =>
    have hFresh : ∀ x, ¬
        ((x ∈ formulaFVN A ∨ x ∈ formulaFVN B) ∧
         (x ∈ formulaBVN A ∨ x ∈ formulaBVN B)) := hRect.1
    have hDistinct : distinctQuantifierBindings A ∧
        distinctQuantifierBindings B ∧
        ∀ x, ¬ (x ∈ formulaBVN A ∧ x ∈ formulaBVN B) :=
      hRect.2
    have hRectA := isRectified_union_left A B hFresh hDistinct.1
    have hRectB := isRectified_union_right A B hFresh hDistinct.2.1
    obtain ⟨hFreshB, hFreshA⟩ :=
      toPrenexRaw_binary_fresh A B hFresh hDistinct.2.2
    let pA := toPrenexRaw A
    let pB := toPrenexRaw B
    have hMoveB := toPrenexHelper_impl_right
      (prenexPrefix pB) (prenexMatrix pA) (prenexMatrix pB) hFreshB
    have hMoveA := toPrenexHelper_impl_left_dual
      (prenexPrefix pA) (prenexMatrix pA) pB hFreshA
    have hCombined :
        foLogEquivN
          (toPrenexHelper
            (dualPrefix (prenexPrefix pA) ++ prenexPrefix pB)
            (.impl (prenexMatrix pA) (prenexMatrix pB)))
          (.impl pA pB) := by
      rw [toPrenexHelper_append]
      exact foLogEquivN_trans
        (toPrenexHelper_equiv
          (dualPrefix (prenexPrefix pA)) hMoveB)
        (by simpa only [toPrenexHelper_rebuild] using hMoveA)
    exact foLogEquivN_trans
      (foLogEquivN_impl (ihA hRectA) (ihB hRectB))
      (by
        simpa only [toPrenexRaw] using
          (foLogEquivN_symm hCombined))
  | all y A ih =>
    have hRectA := isRectified_all_body y A hRect.1 hRect.2
    exact foLogEquivN_all y (ih hRectA)
  | ex y A ih =>
    have hRectA := isRectified_ex_body y A hRect.1 hRect.2
    exact foLogEquivN_ex y (ih hRectA)

-- ATTACH-BLOCKER: private declaration
private theorem rectifyAuxN_eq_rectifyAux {L : Language}
    (A : FormulaN L) (sigma : Nat → Nat) (n : Nat) :
    rectifyAuxN A sigma n = rectifyAux A sigma n := by
  induction A generalizing sigma n with
  | predN P ts => rfl
  | eq_ hL t₁ t₂ => rfl
  | neg A ih => simp [rectifyAuxN, rectifyAux, ih]
  | conj A B ihA ihB =>
    simp [rectifyAuxN, rectifyAux, ihA, ihB]
  | disj A B ihA ihB =>
    simp [rectifyAuxN, rectifyAux, ihA, ihB]
  | impl A B ihA ihB =>
    simp [rectifyAuxN, rectifyAux, ihA, ihB]
  | all y A ih => simp [rectifyAuxN, rectifyAux, ih]
  | ex y A ih => simp [rectifyAuxN, rectifyAux, ih]

-- ATTACH-BLOCKER: private declaration
private theorem rectifyN_eq_rectify {L : Language} (A : FormulaN L) :
    rectifyN A = rectify A := by
  unfold rectifyN rectify
  rw [rectifyAuxN_eq_rectifyAux]

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Theorem 7.2.1 (companion theorem): toPrenex preserves logical equivalence. This is the second conjunct of the prenex normal form theorem: the converted formula is equivalent to the original. The proof composes two steps: (1) rectify A ≡ A (by rectify_equiv), (2) toPrenexRaw (rectify A) ≡ rectify A (raw conversion on the rectified formula, where bound variables are distinct, so prefix concatenation is sound). -/
theorem toPrenex_equiv {L : Language}
    (A : FormulaN L) :
    foLogEquivN A (toPrenex A) :=
-- BEGIN PROOF
by
  have hRectify : foLogEquivN A (rectify A) := rectify_equiv A
  have hRaw : foLogEquivN (rectify A)
      (toPrenexRaw (rectify A)) :=
    toPrenexRaw_equiv_of_rectified (rectify A)
      (rectify_isRectified A)
  simpa only [toPrenex, rectifyN_eq_rectify] using
    (foLogEquivN_trans hRectify hRaw)

-- ===================================================================
-- Lemma 7.2.2: Quantifier-free DNF transformation
-- ===================================================================

/-- Lemma 7.2.2: One application of one of the following eight identities,
from left to right, at a subformula position built from ∨, ∧, ¬, and ⊃.
These are the identities by which a quantifier-free formula is transformed
into an equivalent formula in disjunctive normal form. -/
@[blueprint "chap7__lemma_7_2_2"]
inductive DNFIdentityStep {L : Language} : FormulaN L → FormulaN L → Prop where
  | impl_as_disj (A B : FormulaN L) :
      DNFIdentityStep (.impl A B) (.disj (.neg A) B)
  | double_neg (A : FormulaN L) :
      DNFIdentityStep (.neg (.neg A)) A
  | deMorgan_conj (A B : FormulaN L) :
      DNFIdentityStep (.neg (.conj A B)) (.disj (.neg A) (.neg B))
  | deMorgan_disj (A B : FormulaN L) :
      DNFIdentityStep (.neg (.disj A B)) (.conj (.neg A) (.neg B))
  | conj_distrib_left (A B C : FormulaN L) :
      DNFIdentityStep (.conj A (.disj B C)) (.disj (.conj A B) (.conj A C))
  | conj_distrib_right (A B C : FormulaN L) :
      DNFIdentityStep (.conj (.disj B C) A) (.disj (.conj B A) (.conj C A))
  | conj_assoc (A B C : FormulaN L) :
      DNFIdentityStep (.conj (.conj A B) C) (.conj A (.conj B C))
  | disj_assoc (A B C : FormulaN L) :
      DNFIdentityStep (.disj (.disj A B) C) (.disj A (.disj B C))
  | neg {A B : FormulaN L} :
      DNFIdentityStep A B → DNFIdentityStep (.neg A) (.neg B)
  | conj_left {A B : FormulaN L} (C : FormulaN L) :
      DNFIdentityStep A B → DNFIdentityStep (.conj A C) (.conj B C)
  | conj_right (A : FormulaN L) {B C : FormulaN L} :
      DNFIdentityStep B C → DNFIdentityStep (.conj A B) (.conj A C)
  | disj_left {A B : FormulaN L} (C : FormulaN L) :
      DNFIdentityStep A B → DNFIdentityStep (.disj A C) (.disj B C)
  | disj_right (A : FormulaN L) {B C : FormulaN L} :
      DNFIdentityStep B C → DNFIdentityStep (.disj A B) (.disj A C)
  | impl_left {A B : FormulaN L} (C : FormulaN L) :
      DNFIdentityStep A B → DNFIdentityStep (.impl A C) (.impl B C)
  | impl_right (A : FormulaN L) {B C : FormulaN L} :
      DNFIdentityStep B C → DNFIdentityStep (.impl A B) (.impl A C)

/-- Lemma 7.2.2: Transformation by finitely many applications of the eight
identities, allowing zero applications when the formula is already in
disjunctive normal form. -/
@[blueprint "chap7__lemma_7_2_2"]
inductive DNFIdentityRewrites {L : Language} : FormulaN L → FormulaN L → Prop where
  | refl (A : FormulaN L) : DNFIdentityRewrites A A
  | step {A B C : FormulaN L} :
      DNFIdentityStep A B → DNFIdentityRewrites B C → DNFIdentityRewrites A C

/-- Lemma 7.2.2 (companion theorem): Left distributivity of conjunction over disjunction: A and (B or C) equiv (A and B) or (A and C). This is one of the eight propositional identities used in the DNF transformation. -/
@[blueprint "chap7__lemma_7_2_2"]
theorem prenex_equiv_conj_distrib_left {L : Language}
    (A B C : FormulaN L) :
    foLogEquivN
      (FormulaN.conj A (FormulaN.disj B C))
      (FormulaN.disj (FormulaN.conj A B) (FormulaN.conj A C)) 

/-- Lemma 7.2.2 (companion theorem): Right distributivity of conjunction over disjunction: (B or C) and A equiv (B and A) or (C and A). This is one of the eight propositional identities used in the DNF transformation. -/
@[blueprint "chap7__lemma_7_2_2"]
theorem prenex_equiv_conj_distrib_right {L : Language}
    (A B C : FormulaN L) :
    foLogEquivN
      (FormulaN.conj (FormulaN.disj B C) A)
      (FormulaN.disj (FormulaN.conj B A) (FormulaN.conj C A)) 

-- ===================================================================
-- Lemma 7.2.2 (companion def): isLiteral
-- ===================================================================

/-- Lemma 7.2.2 (companion def): A formula is a literal if it is atomic or the negation of an atomic formula. Atomic formulae include n-ary predicate applications and equality. -/
@[blueprint "chap7__lemma_7_2_2"]
def isLiteral {L : Language} : FormulaN L → Prop
  | .predN _ _ => True
  | .eq_ _ _ _ => True
  | .neg (.predN _ _) => True
  | .neg (.eq_ _ _ _) => True
  | _ => False

-- ===================================================================
-- Lemma 7.2.2 (companion def): isDNF
-- ===================================================================

/-- Lemma 7.2.2 (companion def): A helper predicate: a formula is a conjunction of literals (a "clause" in DNF terminology, meaning a conjunctive clause). -/
@[blueprint "chap7__lemma_7_2_2"]
def isConjOfLiterals {L : Language} : FormulaN L → Prop
  | .conj A B => isConjOfLiterals A ∧ isConjOfLiterals B
  | A => isLiteral A

/-- Lemma 7.2.2 (companion def): A first-order formula is in disjunctive normal form if it is a disjunction of conjunctions of literals (atomic formulae or negated atomic formulae). -/
@[blueprint "chap7__lemma_7_2_2"]
def isDNF {L : Language} : FormulaN L → Prop
  | .disj A B => isDNF A ∧ isDNF B
  | A => isConjOfLiterals A

-- ===================================================================
-- Lemma 7.2.2: Quantifier-free DNF theorem
-- ===================================================================



-- Helper: conjOfLiterals → isDNF


-- Helper: disjunction of two DNFs is DNF


-- Helper: conjunction of two conjOfLiterals is conjOfLiterals


-- Helper: distributing a conjOfLiterals over a DNF produces a DNF
-- (A ∧ B) where A is conjOfLiterals and B is DNF
-- Result is equivalent and in DNF.


-- Helper: distributing two DNFs under conjunction produces a DNF


-- Helper: negation of a conjOfLiterals has a DNF equivalent


-- Helper: negation of a DNF has a DNF equivalent


/-- Lemma 7.2.2: Every quantifier-free formula A (containing the connectives
∨, ∧, ¬, ⊃) can be transformed into an equivalent formula in disjunctive
normal form, by application of the following identities. -/
@[attach_debt, blueprint "chap7__lemma_7_2_2" (main := true)]
theorem qfree_dnf_exists {L : Language}
    (A : FormulaN L) (hqf : FirstOrder.SemanticsN.isQuantifierFree A) :
    ∃ B : FormulaN L,
      isDNF B ∧ DNFIdentityRewrites A B ∧ foLogEquivN A B

-- ===================================================================
-- Lemma 7.2.2 (companions): Quantifier-free CNF existence
-- ===================================================================

/-- Lemma 7.2.2 (companion def): A nonempty binary disjunction of literals,
including a single literal. Literals are the existing predicate/equality atoms
and their direct negations; terms and free variables are unrestricted. -/
@[blueprint "chap7__lemma_7_2_2"]
def isDisjOfLiterals {L : Language} : FormulaN L → Prop
  | .disj A B => isDisjOfLiterals A ∧ isDisjOfLiterals B
  | A => isLiteral A

/-- Lemma 7.2.2 (companion def): A conjunction of disjunctions of literals,
using the standing binary FormulaN syntax. Singleton clauses and singleton
conjunctions are admitted. Empty Boolean constants are expressed by the
standing abbreviations, not by new syntax constructors. -/
@[blueprint "chap7__lemma_7_2_2"]
def isCNF {L : Language} : FormulaN L → Prop
  | .conj A B => isCNF A ∧ isCNF B
  | A => isDisjOfLiterals A





/-- Lemma 7.2.2 (companion theorem, §7.2 matrix remark): Every quantifier-free
first-order formula has a logically equivalent CNF over exactly the same atoms.
Atomic subformula equality preserves predicate arguments and equality terms,
including free variables. Together with `qfree_dnf_exists`, this gives both
independent normal-form choices. The claim is existential and specifies no
particular conversion. -/
@[attach_debt, blueprint "chap7__lemma_7_2_2"]
theorem qfree_cnf_exists {L : Language}
    (A : FormulaN L) (hqf : isQuantifierFree A) :
    ∃ B : FormulaN L, isCNF B ∧ foLogEquivN A B ∧
      ∀ P : FormulaN L, P.isAtomic = true →
        (IsSubformula P B ↔ IsSubformula P A) 

end LCS.Herbrand.PrenexForm
end
