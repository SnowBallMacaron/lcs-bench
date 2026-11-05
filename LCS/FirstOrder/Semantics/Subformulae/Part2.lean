import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.Syntax.Substitution
import LCS.FirstOrder.Syntax.Variables
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.SemanticsN
import LCS.FirstOrder.Semantics.Substitution
import LCS.Propositional.Syntax
import LCS.Propositional.Semantics
import LCS.FirstOrder.Semantics.Subformulae.Part1
import Attach
import LCS.FirstOrder.Semantics.Subformulae.Part2.ProofsStamp

section
namespace LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax
open LCS.FirstOrder.Syntax.Substitution
open LCS.FirstOrder.Syntax.Variables
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics
open LCS.FirstOrder.Semantics.Substitution (coincidenceLemma)
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics





-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 5.3.4 (companion): Apply a variable renaming to a term. -/
def termVarMap {L : Language} (sigma : Nat → Nat) : Term L → Term L
  | .var i => .var (sigma i)
  | .const c => .const c
  | .func f ts => .func f (fun j => termVarMap sigma (ts j))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 5.3.4 (companion): Update a function at a single point. -/
def funUpdate (f : Nat → Nat) (i : Nat) (v : Nat) : Nat → Nat :=
  fun x => if x = i then v else f x

/-- Lemma 5.3.4 (required helper): rectifyAux A sigma n traverses
formula A, renaming each quantifier-bound variable to a fresh counter
starting from n, using sigma to track the accumulated renaming.
Returns (rectified formula, next counter). -/
@[blueprint "chap5__lemma_5_3_4"]
def rectifyAux {L : Language} : FormulaN L → (Nat → Nat) → Nat → FormulaN L × Nat
  | .predN P ts, sigma, n => (.predN P (fun j => termVarMap sigma (ts j)), n)
  | .eq_ hL t1 t2, sigma, n => (.eq_ hL (termVarMap sigma t1) (termVarMap sigma t2), n)
  | .neg A, sigma, n => let (A', n') := rectifyAux A sigma n; (.neg A', n')
  | .conj A B, sigma, n =>
    let (A', n') := rectifyAux A sigma n
    let (B', n'') := rectifyAux B sigma n'
    (.conj A' B', n'')
  | .disj A B, sigma, n =>
    let (A', n') := rectifyAux A sigma n
    let (B', n'') := rectifyAux B sigma n'
    (.disj A' B', n'')
  | .impl A B, sigma, n =>
    let (A', n') := rectifyAux A sigma n
    let (B', n'') := rectifyAux B sigma n'
    (.impl A' B', n'')
  | .all i A, sigma, n =>
    let sigma' := funUpdate sigma i n
    let (A', n') := rectifyAux A sigma' (n + 1)
    (.all n A', n')
  | .ex i A, sigma, n =>
    let sigma' := funUpdate sigma i n
    let (A', n') := rectifyAux A sigma' (n + 1)
    (.ex n A', n')

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 5.3.4 (companion): max over a finite function. -/
def finMax (n : Nat) (f : Fin n → Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => Nat.max (f ⟨n, Nat.lt_succ_of_le (Nat.le_refl n)⟩)
    (finMax n (fun i => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ n)⟩))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 5.3.4 (companion): Maximum variable index in a term (0 if no
variables). -/
def termMaxVar {L : Language} : Term L → Nat
  | .var i => i
  | .const _ => 0
  | .func f ts => finMax (L.funArity f) (fun j => termMaxVar (ts j))

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.LKe.Equivalence.Validity, LCS.FirstOrder.Gentzen.Search.NoFunction.Contracts, LCS.Herbrand.PrenexForm.Part1
/-- Lemma 5.3.4 (companion): Maximum variable index appearing anywhere
in a formula. -/
def formulaMaxVarN {L : Language} : FormulaN L → Nat
  | .predN P ts => finMax (L.predArity P) (fun j => termMaxVar (ts j))
  | .eq_ _ t1 t2 => Nat.max (termMaxVar t1) (termMaxVar t2)
  | .neg A => formulaMaxVarN A
  | .conj A B => Nat.max (formulaMaxVarN A) (formulaMaxVarN B)
  | .disj A B => Nat.max (formulaMaxVarN A) (formulaMaxVarN B)
  | .impl A B => Nat.max (formulaMaxVarN A) (formulaMaxVarN B)
  | .all i A => Nat.max i (formulaMaxVarN A)
  | .ex i A => Nat.max i (formulaMaxVarN A)

-- retained: used by LCS.CutElim.Beth.Part2, LCS.FOResolution.ClauseForm, LCS.Herbrand.HerbrandTheorem.Part2, LCS.Herbrand.PrenexForm.Part2
/-- Lemma 5.3.4 (companion): A recursive function that produces a
rectified formula A' from A by systematically renaming bound variables
to fresh names, avoiding clashes with free variables and previously
used bound variables. -/
def rectify {L : Language} (A : FormulaN L) : FormulaN L :=
  (rectifyAux A id (formulaMaxVarN A + 1)).1

-- ===================================================================
-- Helper lemmas for rectify correctness
-- ===================================================================

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Contracts
theorem rectifyAux_counter_le {L : Language} (A : FormulaN L)
    (sigma : Nat → Nat) (n : Nat) :
    n ≤ (rectifyAux A sigma n).2 := by
-- BEGIN PROOF
  induction A generalizing sigma n with
  | predN _ _ | eq_ _ _ _ => simp [rectifyAux]
  | neg A ih => exact ih sigma n
  | conj A B ihA ihB | disj A B ihA ihB
  | impl A B ihA ihB =>
    exact Nat.le_trans (ihA sigma n) (ihB sigma _)
  | all i A ih | ex i A ih =>
    exact Nat.le_trans (Nat.le_succ n) (ih _ (n + 1))

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Contracts
theorem rectifyAux_bv_range {L : Language} (A : FormulaN L)
    (sigma : Nat → Nat) (ctr : Nat) :
    ∀ x, x ∈ formulaBVN (rectifyAux A sigma ctr).1 →
      ctr ≤ x ∧ x < (rectifyAux A sigma ctr).2 := by
-- BEGIN PROOF
  induction A generalizing sigma ctr with
  | predN _ _ =>
    intro x hx; unfold rectifyAux formulaBVN at hx; exact absurd hx id
  | eq_ _ _ _ =>
    intro x hx; unfold rectifyAux formulaBVN at hx; exact absurd hx id
  | neg A ih => exact ih sigma ctr
  | conj A B ihA ihB | disj A B ihA ihB
  | impl A B ihA ihB =>
    intro x hx; unfold rectifyAux at hx; simp only [formulaBVN] at hx
    rcases hx with hxA | hxB
    · exact ⟨(ihA sigma ctr x hxA).1,
        Nat.lt_of_lt_of_le (ihA sigma ctr x hxA).2
          (rectifyAux_counter_le B sigma _)⟩
    · exact ⟨Nat.le_trans (rectifyAux_counter_le A sigma ctr)
          (ihB sigma _ x hxB).1, (ihB sigma _ x hxB).2⟩
  | all i A ih =>
    intro x hx
    let body := (rectifyAux A (funUpdate sigma i ctr) (ctr + 1)).1
    let ctr' := (rectifyAux A (funUpdate sigma i ctr) (ctr + 1)).2
    have hx' : x ∈ formulaBVN body ∨ x = ctr := by
      change x ∈ formulaBVN (FormulaN.all ctr body) at hx
      simp only [formulaBVN] at hx; exact hx
    have goal_snd : (rectifyAux (FormulaN.all i A) sigma ctr).2 = ctr' :=
      rfl
    rw [goal_snd]
    rcases hx' with hBody | hEq
    · have := ih (funUpdate sigma i ctr) (ctr + 1) x hBody; omega
    · rw [hEq]; constructor; · omega
      · exact Nat.lt_of_lt_of_le (Nat.lt_add_one ctr)
          (rectifyAux_counter_le A _ (ctr + 1))
  | ex i A ih =>
    intro x hx
    let body := (rectifyAux A (funUpdate sigma i ctr) (ctr + 1)).1
    let ctr' := (rectifyAux A (funUpdate sigma i ctr) (ctr + 1)).2
    have hx' : x ∈ formulaBVN body ∨ x = ctr := by
      change x ∈ formulaBVN (FormulaN.ex ctr body) at hx
      simp only [formulaBVN] at hx; exact hx
    have goal_snd : (rectifyAux (FormulaN.ex i A) sigma ctr).2 = ctr' :=
      rfl
    rw [goal_snd]
    rcases hx' with hBody | hEq
    · have := ih (funUpdate sigma i ctr) (ctr + 1) x hBody; omega
    · rw [hEq]; constructor; · omega
      · exact Nat.lt_of_lt_of_le (Nat.lt_add_one ctr)
          (rectifyAux_counter_le A _ (ctr + 1))

-- retained: used by LCS.Herbrand.HerbrandTheorem.Part2, LCS.Herbrand.PrenexForm.Part2
theorem rectifyAux_dqb {L : Language} (A : FormulaN L)
    (sigma : Nat → Nat) (ctr : Nat) :
    distinctQuantifierBindings (rectifyAux A sigma ctr).1 := by
-- BEGIN PROOF
  induction A generalizing sigma ctr with
  | predN _ _ | eq_ _ _ _ => exact trivial
  | neg A ih => exact ih sigma ctr
  | conj A B ihA ihB =>
    suffices h : distinctQuantifierBindings (FormulaN.conj
        (rectifyAux A sigma ctr).1
        (rectifyAux B sigma (rectifyAux A sigma ctr).2).1) from h
    simp only [distinctQuantifierBindings]
    refine ⟨ihA sigma ctr, ihB sigma _, fun x ⟨hxA, hxB⟩ => ?_⟩
    have h1 := (rectifyAux_bv_range A sigma ctr x hxA).2
    have h2 := (rectifyAux_bv_range B sigma
      (rectifyAux A sigma ctr).2 x hxB).1
    omega
  | disj A B ihA ihB =>
    suffices h : distinctQuantifierBindings (FormulaN.disj
        (rectifyAux A sigma ctr).1
        (rectifyAux B sigma (rectifyAux A sigma ctr).2).1) from h
    simp only [distinctQuantifierBindings]
    refine ⟨ihA sigma ctr, ihB sigma _, fun x ⟨hxA, hxB⟩ => ?_⟩
    have h1 := (rectifyAux_bv_range A sigma ctr x hxA).2
    have h2 := (rectifyAux_bv_range B sigma
      (rectifyAux A sigma ctr).2 x hxB).1
    omega
  | impl A B ihA ihB =>
    suffices h : distinctQuantifierBindings (FormulaN.impl
        (rectifyAux A sigma ctr).1
        (rectifyAux B sigma (rectifyAux A sigma ctr).2).1) from h
    simp only [distinctQuantifierBindings]
    refine ⟨ihA sigma ctr, ihB sigma _, fun x ⟨hxA, hxB⟩ => ?_⟩
    have h1 := (rectifyAux_bv_range A sigma ctr x hxA).2
    have h2 := (rectifyAux_bv_range B sigma
      (rectifyAux A sigma ctr).2 x hxB).1
    omega
  | all i A ih =>
    suffices h : distinctQuantifierBindings (FormulaN.all ctr
        (rectifyAux A (funUpdate sigma i ctr) (ctr + 1)).1) from h
    simp only [distinctQuantifierBindings]
    refine ⟨ih _ _, fun hBVn => ?_⟩
    have := (rectifyAux_bv_range A (funUpdate sigma i ctr)
      (ctr + 1) ctr hBVn).1; omega
  | ex i A ih =>
    suffices h : distinctQuantifierBindings (FormulaN.ex ctr
        (rectifyAux A (funUpdate sigma i ctr) (ctr + 1)).1) from h
    simp only [distinctQuantifierBindings]
    refine ⟨ih _ _, fun hBVn => ?_⟩
    have := (rectifyAux_bv_range A (funUpdate sigma i ctr)
      (ctr + 1) ctr hBVn).1; omega

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Contracts
theorem termVarMap_fv_source {L : Language} (sigma : Nat → Nat)
    (t : Term L) :
    ∀ x, x ∈ termFV (termVarMap sigma t) →
      ∃ y, y ∈ termFV t ∧ x = sigma y := by
-- BEGIN PROOF
  induction t with
  | var k =>
    intro x hx; unfold termVarMap termFV at hx; exact ⟨k, rfl, hx⟩
  | const _ =>
    intro x hx; unfold termVarMap termFV at hx; exact absurd hx id
  | func f ts ih =>
    intro x hx; unfold termVarMap termFV at hx
    obtain ⟨j, hj⟩ := hx
    obtain ⟨y, hy, hxy⟩ := ih j x hj
    exact ⟨y, ⟨j, hy⟩, hxy⟩

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Contracts
theorem rectifyAux_fv_source {L : Language} (A : FormulaN L)
    (sigma : Nat → Nat) (ctr : Nat) :
    ∀ x, x ∈ formulaFVN (rectifyAux A sigma ctr).1 →
      ∃ y, y ∈ formulaFVN A ∧ x = sigma y := by
-- BEGIN PROOF
  induction A generalizing sigma ctr with
  | predN P ts =>
    intro x hx
    change x ∈ formulaFVN (FormulaN.predN P
      (fun j => termVarMap sigma (ts j))) at hx
    simp only [formulaFVN] at hx
    obtain ⟨j, hj⟩ := hx
    obtain ⟨y, hy, hxy⟩ := termVarMap_fv_source sigma (ts j) x hj
    exact ⟨y, ⟨j, hy⟩, hxy⟩
  | eq_ hL t1 t2 =>
    intro x hx
    change x ∈ formulaFVN (FormulaN.eq_ hL (termVarMap sigma t1)
      (termVarMap sigma t2)) at hx
    simp only [formulaFVN] at hx
    rcases hx with h1 | h2
    · obtain ⟨y, hy, hxy⟩ := termVarMap_fv_source sigma t1 x h1
      exact ⟨y, Or.inl hy, hxy⟩
    · obtain ⟨y, hy, hxy⟩ := termVarMap_fv_source sigma t2 x h2
      exact ⟨y, Or.inr hy, hxy⟩
  | neg A ih => exact ih sigma ctr
  | conj A B ihA ihB =>
    intro x hx; unfold rectifyAux at hx; simp only [formulaFVN] at hx
    rcases hx with hxA | hxB
    · obtain ⟨y, hy, hxy⟩ := ihA sigma ctr x hxA
      exact ⟨y, Or.inl hy, hxy⟩
    · obtain ⟨y, hy, hxy⟩ := ihB sigma _ x hxB
      exact ⟨y, Or.inr hy, hxy⟩
  | disj A B ihA ihB =>
    intro x hx; unfold rectifyAux at hx; simp only [formulaFVN] at hx
    rcases hx with hxA | hxB
    · obtain ⟨y, hy, hxy⟩ := ihA sigma ctr x hxA
      exact ⟨y, Or.inl hy, hxy⟩
    · obtain ⟨y, hy, hxy⟩ := ihB sigma _ x hxB
      exact ⟨y, Or.inr hy, hxy⟩
  | impl A B ihA ihB =>
    intro x hx; unfold rectifyAux at hx; simp only [formulaFVN] at hx
    rcases hx with hxA | hxB
    · obtain ⟨y, hy, hxy⟩ := ihA sigma ctr x hxA
      exact ⟨y, Or.inl hy, hxy⟩
    · obtain ⟨y, hy, hxy⟩ := ihB sigma _ x hxB
      exact ⟨y, Or.inr hy, hxy⟩
  | all i A ih =>
    intro x hx
    let sigma' := funUpdate sigma i ctr
    change x ∈ formulaFVN (FormulaN.all ctr
      (rectifyAux A sigma' (ctr + 1)).1) at hx
    simp only [formulaFVN] at hx
    obtain ⟨hFV, hNeq⟩ := hx
    obtain ⟨y, hy, hxy⟩ := ih sigma' (ctr + 1) x hFV
    by_cases hyi : y = i
    · subst hyi; simp [sigma', funUpdate] at hxy
      exact absurd hxy hNeq
    · refine ⟨y, ⟨hy, hyi⟩, ?_⟩
      simp [sigma', funUpdate, hyi] at hxy; exact hxy
  | ex i A ih =>
    intro x hx
    let sigma' := funUpdate sigma i ctr
    change x ∈ formulaFVN (FormulaN.ex ctr
      (rectifyAux A sigma' (ctr + 1)).1) at hx
    simp only [formulaFVN] at hx
    obtain ⟨hFV, hNeq⟩ := hx
    obtain ⟨y, hy, hxy⟩ := ih sigma' (ctr + 1) x hFV
    by_cases hyi : y = i
    · subst hyi; simp [sigma', funUpdate] at hxy
      exact absurd hxy hNeq
    · refine ⟨y, ⟨hy, hyi⟩, ?_⟩
      simp [sigma', funUpdate, hyi] at hxy; exact hxy

-- retained: used by LCS.Herbrand.PrenexForm.Part1
theorem finMax_ge (n : Nat) (f : Fin n → Nat) (j : Fin n) :
    f j ≤ finMax n f := by
-- BEGIN PROOF
  induction n with
  | zero => exact absurd j.isLt (Nat.not_lt_zero _)
  | succ n ih =>
    unfold finMax
    by_cases hjn : j.val = n
    · have hj : j = ⟨n, Nat.lt_succ_of_le (Nat.le_refl n)⟩ := by
        ext; exact hjn
      rw [hj]; exact Nat.le_max_left _ _
    · have hlt : j.val < n :=
        Nat.lt_of_le_of_ne (Nat.le_of_lt_succ j.isLt) hjn
      have := ih (fun i => f ⟨i.val,
        Nat.lt_of_lt_of_le i.isLt (Nat.le_succ n)⟩) ⟨j.val, hlt⟩
      exact Nat.le_trans this (Nat.le_max_right _ _)

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity, LCS.FirstOrder.Gentzen.Search.NoFunction.Contracts
theorem termFV_le_maxVar {L : Language} (t : Term L) :
    ∀ x, x ∈ termFV t → x ≤ termMaxVar t := by
-- BEGIN PROOF
  induction t with
  | var i =>
    intro x hx; unfold termFV at hx; exact Nat.le_of_eq hx
  | const _ => intro x hx; exact absurd hx id
  | func f ts ih =>
    intro x hx; unfold termFV at hx
    obtain ⟨j, hj⟩ := hx
    unfold termMaxVar
    exact Nat.le_trans (ih j x hj)
      (finMax_ge _ (fun j => termMaxVar (ts j)) j)

-- retained: used by LCS.CutElim.LKe.Equivalence.Validity, LCS.FirstOrder.Gentzen.Search.NoFunction.Contracts
theorem formulaFVN_le_maxVarN {L : Language} (A : FormulaN L) :
    ∀ x, x ∈ formulaFVN A → x ≤ formulaMaxVarN A := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    intro x hx; simp only [formulaFVN] at hx
    obtain ⟨j, hj⟩ := hx
    unfold formulaMaxVarN
    exact Nat.le_trans (termFV_le_maxVar (ts j) x hj)
      (finMax_ge _ (fun j => termMaxVar (ts j)) j)
  | eq_ _ t1 t2 =>
    intro x hx; simp only [formulaFVN] at hx
    rcases hx with h1 | h2
    · exact Nat.le_trans (termFV_le_maxVar t1 x h1)
        (Nat.le_max_left _ _)
    · exact Nat.le_trans (termFV_le_maxVar t2 x h2)
        (Nat.le_max_right _ _)
  | neg A ih => exact ih
  | conj A B ihA ihB =>
    intro x hx; simp only [formulaFVN] at hx
    rcases hx with hA | hB
    · exact Nat.le_trans (ihA x hA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB x hB) (Nat.le_max_right _ _)
  | disj A B ihA ihB =>
    intro x hx; simp only [formulaFVN] at hx
    rcases hx with hA | hB
    · exact Nat.le_trans (ihA x hA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB x hB) (Nat.le_max_right _ _)
  | impl A B ihA ihB =>
    intro x hx; simp only [formulaFVN] at hx
    rcases hx with hA | hB
    · exact Nat.le_trans (ihA x hA) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihB x hB) (Nat.le_max_right _ _)
  | all i A ih =>
    intro x hx; simp only [formulaFVN] at hx
    exact Nat.le_trans (ih x hx.1) (Nat.le_max_right _ _)
  | ex i A ih =>
    intro x hx; simp only [formulaFVN] at hx
    exact Nat.le_trans (ih x hx.1) (Nat.le_max_right _ _)

-- retained: used by LCS.Herbrand.HerbrandTheorem.Part2, LCS.Herbrand.PrenexForm.Part2
/-- Lemma 5.3.4 (companion): The output of rectify is rectified. -/
theorem rectify_isRectified {L : Language} (A : FormulaN L) :
    isRectified (rectify A) := by
-- BEGIN PROOF
  unfold isRectified rectify
  constructor
  · -- boundVarsFresh: FV ∩ BV = ∅
    intro x ⟨hFV, hBV⟩
    have hBV_ge := (rectifyAux_bv_range A id (formulaMaxVarN A + 1)
      x hBV).1
    obtain ⟨y, hyFV, hxy⟩ := rectifyAux_fv_source A id
      (formulaMaxVarN A + 1) x hFV
    -- hxy : x = id y, i.e., x = y
    have hxy' : x = y := hxy
    have hle := formulaFVN_le_maxVarN A y hyFV
    omega
  · -- distinctQuantifierBindings
    exact rectifyAux_dqb A id (formulaMaxVarN A + 1)

-- ===================================================================
-- Lemma 5.3.4: Rectification of full first-order formulae
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 5.3.4 (companion): A counter-based traversal of a full first-order formula,
renaming each quantifier to a fresh index and returning the next unused counter. -/
def rectifyAuxF {L : Language} : Formula L → (Nat → Nat) → Nat → Formula L × Nat
  | .falsum, _, n => (.falsum, n)
  | .pred0 P hP, _, n => (.pred0 P hP, n)
  | .predN P hP ts, sigma, n => (.predN P hP (fun j => termVarMap sigma (ts j)), n)
  | .eq_ hL t1 t2, sigma, n => (.eq_ hL (termVarMap sigma t1) (termVarMap sigma t2), n)
  | .neg A, sigma, n => let (A', n') := rectifyAuxF A sigma n; (.neg A', n')
  | .conj A B, sigma, n =>
    let (A', n') := rectifyAuxF A sigma n
    let (B', n'') := rectifyAuxF B sigma n'
    (.conj A' B', n'')
  | .disj A B, sigma, n =>
    let (A', n') := rectifyAuxF A sigma n
    let (B', n'') := rectifyAuxF B sigma n'
    (.disj A' B', n'')
  | .impl A B, sigma, n =>
    let (A', n') := rectifyAuxF A sigma n
    let (B', n'') := rectifyAuxF B sigma n'
    (.impl A' B', n'')
  | .equiv_ A B, sigma, n =>
    let (A', n') := rectifyAuxF A sigma n
    let (B', n'') := rectifyAuxF B sigma n'
    (.equiv_ A' B', n'')
  | .all i A, sigma, n =>
    let sigma' := funUpdate sigma i n
    let (A', n') := rectifyAuxF A sigma' (n + 1)
    (.all n A', n')
  | .ex i A, sigma, n =>
    let sigma' := funUpdate sigma i n
    let (A', n') := rectifyAuxF A sigma' (n + 1)
    (.ex n A', n')

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 5.3.4 (companion): Maximum variable index appearing in a full first-order formula,
including quantifier indices; zero for falsum and rank-zero predicates. -/
def formulaMaxVarF {L : Language} : Formula L → Nat
  | .falsum | .pred0 _ _ => 0
  | .predN P _ ts => finMax (L.predArity P) (fun j => termMaxVar (ts j))
  | .eq_ _ t1 t2 => Nat.max (termMaxVar t1) (termMaxVar t2)
  | .neg A => formulaMaxVarF A
  | .conj A B => Nat.max (formulaMaxVarF A) (formulaMaxVarF B)
  | .disj A B => Nat.max (formulaMaxVarF A) (formulaMaxVarF B)
  | .impl A B => Nat.max (formulaMaxVarF A) (formulaMaxVarF B)
  | .equiv_ A B => Nat.max (formulaMaxVarF A) (formulaMaxVarF B)
  | .all i A => Nat.max i (formulaMaxVarF A)
  | .ex i A => Nat.max i (formulaMaxVarF A)

/-- Lemma 5.3.4 (companion): Compute a rectified full first-order formula by starting fresh
quantifier indices above every variable index in the input. -/
@[blueprint "chap5__lemma_5_3_4"]
def rectifyF {L : Language} (A : Formula L) : Formula L :=
  (rectifyAuxF A id (formulaMaxVarF A + 1)).1













-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Contracts
/-- Evaluating a term after variable renaming is the same as evaluating
the original term under the composed assignment. -/
theorem termVarMap_eval {L : Language} (M : Structure L)
    (s : Assignment M) (sigma : Nat → Nat) (t : Term L) :
    termEval M s (termVarMap sigma t) =
    termEval M (fun x => s (sigma x)) t := by
-- BEGIN PROOF
  induction t with
  | var i => simp [termVarMap, termEval]
  | const c => simp [termVarMap, termEval]
  | func f ts ih =>
    simp only [termVarMap, termEval]
    congr 1; funext j; exact ih j

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Contracts
/-- Key semantic lemma for rectify: rectifyAux A sigma n evaluates
under assignment s the same as A evaluates under s composed with sigma,
provided all free variables of A are mapped by sigma to values below n
(freshness condition ensuring no capture). -/
theorem rectifyAux_eval {L : Language} (A : FormulaN L)
    (sigma : Nat → Nat) (n : Nat)
    (hFresh : ∀ x, x ∈ formulaFVN A → sigma x < n)
    (M : Structure L) (s : Assignment M) :
    formulaEvalN M (rectifyAux A sigma n).1 s ↔
    formulaEvalN M A (fun x => s (sigma x)) := by
-- BEGIN PROOF
  induction A generalizing sigma n s with
  | predN P ts =>
    simp only [rectifyAux, formulaEvalN]
    constructor <;> intro h
    · have : (fun i => termEval M s (termVarMap sigma (ts i))) =
          (fun i => termEval M (fun x => s (sigma x)) (ts i)) :=
        funext (fun j => termVarMap_eval M s sigma (ts j))
      rw [this] at h; exact h
    · have : (fun i => termEval M s (termVarMap sigma (ts i))) =
          (fun i => termEval M (fun x => s (sigma x)) (ts i)) :=
        funext (fun j => termVarMap_eval M s sigma (ts j))
      rw [this]; exact h
  | eq_ _ t1 t2 =>
    simp only [rectifyAux, formulaEvalN]
    rw [termVarMap_eval, termVarMap_eval]
  | neg A ih =>
    simp only [rectifyAux, formulaEvalN]
    exact not_congr (ih sigma n hFresh s)
  | conj A B ihA ihB =>
    simp only [rectifyAux, formulaEvalN]
    exact and_congr (ihA sigma n (fun x hx => hFresh x (Or.inl hx)) s)
      (ihB sigma _ (fun x hx => Nat.lt_of_lt_of_le
        (hFresh x (Or.inr hx)) (rectifyAux_counter_le A sigma n)) s)
  | disj A B ihA ihB =>
    simp only [rectifyAux, formulaEvalN]
    exact or_congr (ihA sigma n (fun x hx => hFresh x (Or.inl hx)) s)
      (ihB sigma _ (fun x hx => Nat.lt_of_lt_of_le
        (hFresh x (Or.inr hx)) (rectifyAux_counter_le A sigma n)) s)
  | impl A B ihA ihB =>
    simp only [rectifyAux, formulaEvalN]
    exact imp_congr (ihA sigma n (fun x hx => hFresh x (Or.inl hx)) s)
      (ihB sigma _ (fun x hx => Nat.lt_of_lt_of_le
        (hFresh x (Or.inr hx)) (rectifyAux_counter_le A sigma n)) s)
  | all i A ih =>
    simp only [rectifyAux, formulaEvalN]
    let sigma' := funUpdate sigma i n
    have hFresh' : ∀ x, x ∈ formulaFVN A → sigma' x < n + 1 := by
      intro x hx
      by_cases hxi : x = i
      · subst hxi; simp [sigma', funUpdate]
      · simp [sigma', funUpdate, hxi]
        exact Nat.lt_succ_of_lt (hFresh x ⟨hx, hxi⟩)
    constructor <;> intro h a
    · have step := (ih sigma' (n + 1) hFresh'
        (assignUpdate s n a)).mp (h a)
      exact (coincidenceLemmaN M A
        (fun x => (assignUpdate s n a) (sigma' x))
        (assignUpdate (fun x => s (sigma x)) i a)
        (fun y hy => by
          by_cases hyi : y = i
          · subst hyi; simp [assignUpdate, sigma', funUpdate]
          · have hne : sigma y ≠ n :=
              Nat.ne_of_lt (hFresh y ⟨hy, hyi⟩)
            simp [assignUpdate, sigma', funUpdate, hyi, hne]
              )).mp step
    · apply (ih sigma' (n + 1) hFresh'
        (assignUpdate s n a)).mpr
      exact (coincidenceLemmaN M A
        (assignUpdate (fun x => s (sigma x)) i a)
        (fun x => (assignUpdate s n a) (sigma' x))
        (fun y hy => by
          by_cases hyi : y = i
          · subst hyi; simp [assignUpdate, sigma', funUpdate]
          · have hne : sigma y ≠ n :=
              Nat.ne_of_lt (hFresh y ⟨hy, hyi⟩)
            simp [assignUpdate, sigma', funUpdate, hyi, hne]
              )).mp (h a)
  | ex i A ih =>
    simp only [rectifyAux, formulaEvalN]
    let sigma' := funUpdate sigma i n
    have hFresh' : ∀ x, x ∈ formulaFVN A → sigma' x < n + 1 := by
      intro x hx
      by_cases hxi : x = i
      · subst hxi; simp [sigma', funUpdate]
      · simp [sigma', funUpdate, hxi]
        exact Nat.lt_succ_of_lt (hFresh x ⟨hx, hxi⟩)
    constructor <;> intro ⟨a, ha⟩ <;> refine ⟨a, ?_⟩
    · have step := (ih sigma' (n + 1) hFresh'
        (assignUpdate s n a)).mp ha
      exact (coincidenceLemmaN M A
        (fun x => (assignUpdate s n a) (sigma' x))
        (assignUpdate (fun x => s (sigma x)) i a)
        (fun y hy => by
          by_cases hyi : y = i
          · subst hyi; simp [assignUpdate, sigma', funUpdate]
          · have hne : sigma y ≠ n :=
              Nat.ne_of_lt (hFresh y ⟨hy, hyi⟩)
            simp [assignUpdate, sigma', funUpdate, hyi, hne]
              )).mp step
    · apply (ih sigma' (n + 1) hFresh'
        (assignUpdate s n a)).mpr
      exact (coincidenceLemmaN M A
        (assignUpdate (fun x => s (sigma x)) i a)
        (fun x => (assignUpdate s n a) (sigma' x))
        (fun y hy => by
          by_cases hyi : y = i
          · subst hyi; simp [assignUpdate, sigma', funUpdate]
          · have hne : sigma y ≠ n :=
              Nat.ne_of_lt (hFresh y ⟨hy, hyi⟩)
            simp [assignUpdate, sigma', funUpdate, hyi, hne]
              )).mp ha



/-- Lemma 5.3.4(ii): Every full first-order formula is semantically
equivalent to the rectified formula computed by rectifyF. -/
@[blueprint "chap5__lemma_5_3_4" (main := true)]
theorem rectifyF_equiv {L : Language} (A : Formula L) :
    universallyValid (Formula.equiv_ A (rectifyF A)) 

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Lemma 5.3.4 (companion on normalized formulae): The output of rectify is semantically equivalent to the
input: |= A equiv rectify(A). Every formula can be rectified (bound variables renamed to avoid free variables) while preserving semantics. -/
theorem rectify_equiv {L : Language} (A : FormulaN L) :
    universallyValidN (FormulaN.conj
      (FormulaN.impl A (rectify A))
      (FormulaN.impl (rectify A) A)) := by
-- BEGIN PROOF
  intro M s
  simp only [formulaEvalN, rectify]
  have hFresh : ∀ x, x ∈ formulaFVN A → id x < formulaMaxVarN A + 1 := by
    intro x hx; simp [id]
    exact Nat.lt_succ_of_le (formulaFVN_le_maxVarN A x hx)
  constructor
  · intro h
    exact (rectifyAux_eval A id (formulaMaxVarN A + 1) hFresh M s).mpr h
  · intro h
    exact (rectifyAux_eval A id (formulaMaxVarN A + 1) hFresh M s).mp h

-- ===================================================================
-- Lemma 5.3.5: Validity of tautology instances
-- ===================================================================



/-- Lemma 5.3.5: Every full first-order formula obtained by substitution
into a tautology over L's rank-zero predicates is universally valid. -/
@[blueprint "chap5__lemma_5_3_5" (main := true)]
theorem propInstanceValid {L : Language} (A : Formula L) :
    inPROPL A → universallyValid A 





end LCS.FirstOrder.Semantics.Subformulae
end

