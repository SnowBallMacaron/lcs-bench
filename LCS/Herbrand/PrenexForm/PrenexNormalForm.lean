import LCS.Item
import LCS.Util
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Semantics.Equivalence
import LCS.FirstOrder.SemanticsN.Substitution
import LCS.Herbrand.PrenexForm.PrenexFormulas
import LCS.Herbrand.PrenexForm.Equivalences
import Attach
import LCS.Herbrand.PrenexForm.PrenexNormalForm.ProofsStamp

/-! # Herbrand.PrenexForm.PrenexNormalForm
    Chapter 7, Section 2.1: Theorem 7.2.1, for every formula A a prenex
    formula B can be constructed such that A and B are equivalent.

    The existence proof by induction on A (the negation case and the binary
    cases, where the bound variables of one prenex operand are renamed apart
    before Lemma 7.2.1 pulls the quantifiers out), and the conversion as a
    function: the formula is rectified, quantifiers are pulled out along the
    prefixes of the subformulae (dualized under negation and in antecedents of
    implications), and the result is prenex and equivalent to the input.

    Source: Logic for Computer Science, Gallier 2015
-/

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
-- Theorem 7.2.1 (infrastructure): Variable bound utilities
-- ===================================================================

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Upper bound on all variable indices occurring in a term. -/
def Term.varBound {L : Language} : Term L → Nat
  | .var i => i + 1
  | .const _ => 0
  | .func f ts => finMax (L.funArity f) (fun j => Term.varBound (ts j))

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Upper bound on all variable indices (free, bound, and in terms)
    occurring in a formula. Any variable v with v ≥ varBound A does
    not appear anywhere in A. -/
def formulaVarBound {L : Language} : FormulaN L → Nat
  | .predN _ ts => finMax _ (fun j => Term.varBound (ts j))
  | .eq_ hL t1 t2 => max (Term.varBound t1) (Term.varBound t2)
  | .neg A => formulaVarBound A
  | .conj A B => max (formulaVarBound A) (formulaVarBound B)
  | .disj A B => max (formulaVarBound A) (formulaVarBound B)
  | .impl A B => max (formulaVarBound A) (formulaVarBound B)
  | .all x A => max (x + 1) (formulaVarBound A)
  | .ex x A => max (x + 1) (formulaVarBound A)

-- retained: used by LCS.Herbrand.PrenexForm.Part2
theorem termFV_bounded {L : Language} (t : Term L) (v : Nat)
    (hv : v ≥ Term.varBound t) : ¬ Membership.mem (termFV t) v := by
-- BEGIN PROOF
  induction t with
  | var i =>
    simp [Term.varBound] at hv; intro h; subst h; omega
  | const _ => intro h; exact h
  | func f ts ih =>
    intro h; simp [termFV] at h; obtain ⟨j, hj⟩ := h
    exact ih j (Nat.le_trans (finMax_ge _ (fun j => Term.varBound (ts j)) j)
      (by simp [Term.varBound] at hv; exact hv)) hj

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Variables above the varBound of a formula are not free in that formula. -/
theorem formulaFV_bounded {L : Language} (A : FormulaN L) (v : Nat)
    (hv : v ≥ formulaVarBound A) : ¬ Membership.mem (formulaFVN A) v := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    intro h; simp [formulaFVN] at h; obtain ⟨j, hj⟩ := h
    exact termFV_bounded (ts j) v
      (Nat.le_trans (finMax_ge _ (fun j => Term.varBound (ts j)) j)
        (by simp [formulaVarBound] at hv; exact hv)) hj
  | eq_ hL t1 t2 =>
    intro h; cases h with
    | inl h1 => exact termFV_bounded t1 v (by simp [formulaVarBound] at hv; omega) h1
    | inr h2 => exact termFV_bounded t2 v (by simp [formulaVarBound] at hv; omega) h2
  | neg A ih =>
    simp [formulaVarBound] at hv; exact ih hv
  | conj A B ihA ihB =>
    intro h; cases h with
    | inl ha => exact ihA (by simp [formulaVarBound] at hv; omega) ha
    | inr hb => exact ihB (by simp [formulaVarBound] at hv; omega) hb
  | disj A B ihA ihB =>
    intro h; cases h with
    | inl ha => exact ihA (by simp [formulaVarBound] at hv; omega) ha
    | inr hb => exact ihB (by simp [formulaVarBound] at hv; omega) hb
  | impl A B ihA ihB =>
    intro h; cases h with
    | inl ha => exact ihA (by simp [formulaVarBound] at hv; omega) ha
    | inr hb => exact ihB (by simp [formulaVarBound] at hv; omega) hb
  | all x A ih =>
    intro h; exact ih (by simp [formulaVarBound] at hv; omega) h.1
  | ex x A ih =>
    intro h; exact ih (by simp [formulaVarBound] at hv; omega) h.1

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- A variable above the varBound of a formula is free-for substitution. -/
theorem isFreeFor_fresh {L : Language} (A : FormulaN L) (x y : Nat)
    (hy : y ≥ formulaVarBound A) : isFreeForN (Term.var y) x A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ | eq_ _ _ _ => simp [isFreeForN]
  | neg A ih =>
    simp [isFreeForN]; exact ih (by simp [formulaVarBound] at hy; exact hy)
  | conj A B ihA ihB =>
    simp [isFreeForN]
    exact ⟨ihA (by simp [formulaVarBound] at hy; omega),
           ihB (by simp [formulaVarBound] at hy; omega)⟩
  | disj A B ihA ihB =>
    simp [isFreeForN]
    exact ⟨ihA (by simp [formulaVarBound] at hy; omega),
           ihB (by simp [formulaVarBound] at hy; omega)⟩
  | impl A B ihA ihB =>
    simp [isFreeForN]
    exact ⟨ihA (by simp [formulaVarBound] at hy; omega),
           ihB (by simp [formulaVarBound] at hy; omega)⟩
  | all z A ih =>
    simp [isFreeForN]; right
    exact ⟨by intro heq; subst heq; simp [formulaVarBound] at hy; omega,
           ih (by simp [formulaVarBound] at hy; omega)⟩
  | ex z A ih =>
    simp [isFreeForN]; right
    exact ⟨by intro heq; subst heq; simp [formulaVarBound] at hy; omega,
           ih (by simp [formulaVarBound] at hy; omega)⟩

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Variable substitution preserves the quantifier-free property. -/
theorem subst_preserves_qf {L : Language} (A : FormulaN L) (y x : Nat)
    (hqf : FirstOrder.SemanticsN.isQuantifierFree A) :
    FirstOrder.SemanticsN.isQuantifierFree (formulaSubstN A (Term.var y) x) := by
-- BEGIN PROOF
  induction A with
  | predN _ _ | eq_ _ _ _ =>
    simp [formulaSubstN, FirstOrder.SemanticsN.isQuantifierFree]
  | neg A ih =>
    simp [formulaSubstN, FirstOrder.SemanticsN.isQuantifierFree] at *; exact ih hqf
  | conj A B ihA ihB =>
    simp [formulaSubstN, FirstOrder.SemanticsN.isQuantifierFree] at *; exact ⟨ihA hqf.1, ihB hqf.2⟩
  | disj A B ihA ihB =>
    simp [formulaSubstN, FirstOrder.SemanticsN.isQuantifierFree] at *; exact ⟨ihA hqf.1, ihB hqf.2⟩
  | impl A B ihA ihB =>
    simp [formulaSubstN, FirstOrder.SemanticsN.isQuantifierFree] at *; exact ⟨ihA hqf.1, ihB hqf.2⟩
  | all _ _ => exact absurd hqf id
  | ex _ _ => exact absurd hqf id

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Variable substitution preserves the prenex property. -/
theorem subst_preserves_prenex {L : Language} (A : FormulaN L) (y x : Nat)
    (hp : isPrenex A) :
    isPrenex (formulaSubstN A (Term.var y) x) := by
-- BEGIN PROOF
  induction A with
  | all z B ih =>
    simp [formulaSubstN]; split
    · exact hp
    · simp [isPrenex]; exact ih hp
  | ex z B ih =>
    simp [formulaSubstN]; split
    · exact hp
    · simp [isPrenex]; exact ih hp
  | _ => exact subst_preserves_qf _ y x hp

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- The number of leading quantifiers in a formula. -/
def numLeadingQ {L : Language} : FormulaN L → Nat
  | .all _ A => 1 + numLeadingQ A
  | .ex _ A => 1 + numLeadingQ A
  | _ => 0

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- A formula with positive numLeadingQ is either all or ex. -/
theorem numLeadingQ_pos {L : Language} (Q : FormulaN L)
    (h : numLeadingQ Q > 0) :
    (∃ x body, Q = .all x body) ∨ (∃ x body, Q = .ex x body) := by
-- BEGIN PROOF
  cases Q <;> simp [numLeadingQ] at h
  · exact Or.inl ⟨_, _, rfl⟩
  · exact Or.inr ⟨_, _, rfl⟩

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Variable substitution preserves the number of leading quantifiers. -/
theorem subst_preserves_numLeadingQ {L : Language}
    (A : FormulaN L) (y x : Nat) :
    numLeadingQ (formulaSubstN A (Term.var y) x) =
    numLeadingQ A := by
-- BEGIN PROOF
  induction A with
  | all z B ih =>
    simp [formulaSubstN]; split
    · rfl
    · simp [numLeadingQ]; exact ih
  | ex z B ih =>
    simp [formulaSubstN]; split
    · rfl
    · simp [numLeadingQ]; exact ih
  | _ => simp [formulaSubstN, numLeadingQ]

-- ===================================================================
-- Theorem 7.2.1 (infrastructure): Prenex combining helpers
-- ===================================================================

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Negation of a prenex formula has a prenex equivalent. -/
theorem negPrenex_equiv {L : Language} (B : FormulaN L)
    (hp : isPrenex B) :
    ∃ C : FormulaN L, isPrenex C ∧ foLogEquivN (FormulaN.neg B) C := by
-- BEGIN PROOF
  induction B with
  | all x A ih =>
    obtain ⟨C, hpC, heC⟩ := ih hp
    exact ⟨FormulaN.ex x C, hpC,
      foLogEquivN_trans (prenex_equiv_c_neg_all x A) (foLogEquivN_ex x heC)⟩
  | ex x A ih =>
    obtain ⟨C, hpC, heC⟩ := ih hp
    exact ⟨FormulaN.all x C, hpC,
      foLogEquivN_trans (prenex_equiv_c_neg_ex x A) (foLogEquivN_all x heC)⟩
  | neg A _ =>
    exact ⟨.neg (.neg A),
      by simp [isPrenex, FirstOrder.SemanticsN.isQuantifierFree] at *; exact hp,
      foLogEquivN_refl _⟩
  | conj A1 A2 _ _ =>
    exact ⟨.neg (.conj A1 A2),
      by simp [isPrenex, FirstOrder.SemanticsN.isQuantifierFree] at *; exact hp,
      foLogEquivN_refl _⟩
  | disj A1 A2 _ _ =>
    exact ⟨.neg (.disj A1 A2),
      by simp [isPrenex, FirstOrder.SemanticsN.isQuantifierFree] at *; exact hp,
      foLogEquivN_refl _⟩
  | impl A1 A2 _ _ =>
    exact ⟨.neg (.impl A1 A2),
      by simp [isPrenex, FirstOrder.SemanticsN.isQuantifierFree] at *; exact hp,
      foLogEquivN_refl _⟩
  | predN P ts => exact ⟨.neg (.predN P ts), trivial, foLogEquivN_refl _⟩
  | eq_ hL t1 t2 => exact ⟨.neg (.eq_ hL t1 t2), trivial, foLogEquivN_refl _⟩

-- retained: used by LCS.Herbrand.PrenexForm.Part2
/-- Conjunction of two prenex formulas has a prenex equivalent.
    By well-founded induction on the total number of leading quantifiers. -/
theorem conjPrenex {L : Language} (P1 P2 : FormulaN L)
    (hp1 : isPrenex P1) (hp2 : isPrenex P2) :
    ∃ C : FormulaN L, isPrenex C ∧
      foLogEquivN (FormulaN.conj P1 P2) C := by
-- BEGIN PROOF
  -- Induction on total number of leading quantifiers
  suffices h : ∀ n, ∀ Q1 Q2 : FormulaN L,
      isPrenex Q1 → isPrenex Q2 →
      numLeadingQ Q1 + numLeadingQ Q2 ≤ n →
      ∃ C, isPrenex C ∧ foLogEquivN (.conj Q1 Q2) C from
    h _ P1 P2 hp1 hp2 (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro Q1 Q2 hq1 hq2 hn
    -- Both have 0 leading quantifiers. conj of two prenex-without-quantifiers is prenex.
    have hqf1 : FirstOrder.SemanticsN.isQuantifierFree Q1 := by
      cases Q1 <;> simp [numLeadingQ] at hn <;> exact hq1
    have hqf2 : FirstOrder.SemanticsN.isQuantifierFree Q2 := by
      cases Q2 <;> simp [numLeadingQ] at hn <;> exact hq2
    exact ⟨.conj Q1 Q2, ⟨hqf1, hqf2⟩, foLogEquivN_refl _⟩
  | succ k ih =>
    intro Q1 Q2 hq1 hq2 hn
    -- Case split: if Q1 has leading quantifiers, pull from left.
    -- Otherwise, pull from Q2.
    by_cases h1 : numLeadingQ Q1 > 0
    · -- Q1 has at least one leading quantifier
      rcases numLeadingQ_pos Q1 h1 with ⟨x, body1, rfl⟩ | ⟨x, body1, rfl⟩
      · -- Q1 = all x body1
        let y := max (formulaVarBound (.all x body1)) (formulaVarBound Q2)
        have hfreeFor := isFreeFor_fresh body1 x y
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
        have hnotFree : ¬ Membership.mem (formulaFVN body1) y ∨ y = x :=
          Or.inl (formulaFV_bounded body1 y
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)))
        have hRename := prenex_equiv_f_univ_rename x y body1 hfreeFor hnotFree
        have hyFresh := formulaFV_bounded Q2 y (Nat.le_max_right _ _)
        have hPull := prenex_equiv_d_univ_conj y
          (formulaSubstN body1 (Term.var y) x) Q2 hyFresh
        have hpSub := subst_preserves_prenex body1 y x hq1
        have hBound : numLeadingQ (formulaSubstN body1 (Term.var y) x) +
            numLeadingQ Q2 ≤ k := by
          rw [subst_preserves_numLeadingQ]
          simp [numLeadingQ] at hn; omega
        obtain ⟨C, hpC, heC⟩ := ih _ _ hpSub hq2 hBound
        exact ⟨.all y C, hpC,
          foLogEquivN_trans
            (foLogEquivN_conj hRename (foLogEquivN_refl Q2))
            (foLogEquivN_trans hPull (foLogEquivN_all y heC))⟩
      · -- Q1 = ex x body1
        let y := max (formulaVarBound (.ex x body1)) (formulaVarBound Q2)
        have hfreeFor := isFreeFor_fresh body1 x y
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
        have hnotFree : ¬ Membership.mem (formulaFVN body1) y ∨ y = x :=
          Or.inl (formulaFV_bounded body1 y
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)))
        have hRename := prenex_equiv_f_ex_rename x y body1 hfreeFor hnotFree
        have hyFresh := formulaFV_bounded Q2 y (Nat.le_max_right _ _)
        have hPull := prenex_equiv_d_ex_conj y
          (formulaSubstN body1 (Term.var y) x) Q2 hyFresh
        have hpSub := subst_preserves_prenex body1 y x hq1
        have hBound : numLeadingQ (formulaSubstN body1 (Term.var y) x) +
            numLeadingQ Q2 ≤ k := by
          rw [subst_preserves_numLeadingQ]
          simp [numLeadingQ] at hn; omega
        obtain ⟨C, hpC, heC⟩ := ih _ _ hpSub hq2 hBound
        exact ⟨.ex y C, hpC,
          foLogEquivN_trans
            (foLogEquivN_conj hRename (foLogEquivN_refl Q2))
            (foLogEquivN_trans hPull (foLogEquivN_ex y heC))⟩
    · -- Q1 has no leading quantifiers (numLeadingQ Q1 = 0)
      by_cases h2 : numLeadingQ Q2 > 0
      · -- Q2 has at least one leading quantifier. Pull from right.
        rcases numLeadingQ_pos Q2 h2 with ⟨y, body2, rfl⟩ | ⟨y, body2, rfl⟩
        · -- Q2 = all y body2
          let z := max (formulaVarBound Q1) (formulaVarBound (.all y body2))
          have hfreeFor := isFreeFor_fresh body2 y z
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
          have hnotFree : ¬ Membership.mem (formulaFVN body2) z ∨ z = y :=
            Or.inl (formulaFV_bounded body2 z
              (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
          have hRename := prenex_equiv_f_univ_rename y z body2 hfreeFor hnotFree
          have hzFresh := formulaFV_bounded Q1 z (Nat.le_max_left _ _)
          have hPull := prenex_conj_right_all z Q1
            (formulaSubstN body2 (Term.var z) y) hzFresh
          have hpSub := subst_preserves_prenex body2 z y hq2
          have hBound : numLeadingQ Q1 +
              numLeadingQ (formulaSubstN body2 (Term.var z) y) ≤ k := by
            rw [subst_preserves_numLeadingQ]
            simp [numLeadingQ] at hn; omega
          obtain ⟨C, hpC, heC⟩ := ih Q1 _ hq1 hpSub hBound
          exact ⟨.all z C, hpC,
            foLogEquivN_trans
              (foLogEquivN_conj (foLogEquivN_refl Q1) hRename)
              (foLogEquivN_trans hPull (foLogEquivN_all z heC))⟩
        · -- Q2 = ex y body2
          let z := max (formulaVarBound Q1) (formulaVarBound (.ex y body2))
          have hfreeFor := isFreeFor_fresh body2 y z
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
          have hnotFree : ¬ Membership.mem (formulaFVN body2) z ∨ z = y :=
            Or.inl (formulaFV_bounded body2 z
              (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
          have hRename := prenex_equiv_f_ex_rename y z body2 hfreeFor hnotFree
          have hzFresh := formulaFV_bounded Q1 z (Nat.le_max_left _ _)
          have hPull := prenex_conj_right_ex z Q1
            (formulaSubstN body2 (Term.var z) y) hzFresh
          have hpSub := subst_preserves_prenex body2 z y hq2
          have hBound : numLeadingQ Q1 +
              numLeadingQ (formulaSubstN body2 (Term.var z) y) ≤ k := by
            rw [subst_preserves_numLeadingQ]
            simp [numLeadingQ] at hn; omega
          obtain ⟨C, hpC, heC⟩ := ih Q1 _ hq1 hpSub hBound
          exact ⟨.ex z C, hpC,
            foLogEquivN_trans
              (foLogEquivN_conj (foLogEquivN_refl Q1) hRename)
              (foLogEquivN_trans hPull (foLogEquivN_ex z heC))⟩
      · -- Both Q1 and Q2 have 0 leading quantifiers: both qf
        exact ih Q1 Q2 hq1 hq2 (by omega)

-- ===================================================================
-- Theorem 7.2.1: Prenex normal form existence
-- ===================================================================

/-- Theorem 7.2.1: For every formula A, a prenex formula B can be constructed such that A equiv B is valid (A and B are logically equivalent). The constructive witness is toPrenex A. This is the main theorem stating that toPrenex produces a prenex formula and that it is equivalent to the input. -/
@[blueprint "chap7__theorem_7_2_1" (main := true)]
theorem prenex_normal_form_exists {L : Language}
    (A : FormulaN L) :
    ∃ B : FormulaN L,
      isPrenex B ∧ foLogEquivN A B

end LCS.Herbrand.PrenexForm
