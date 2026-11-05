import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Semantics.Substitution
import LCS.Propositional.Semantics
import LCS.FirstOrder.ManySorted.Gentzen.Calculus
import Attach
import LCS.FirstOrder.ManySorted.Gentzen.Completeness.ProofsStamp

section
namespace LCS.FirstOrder.ManySorted.Gentzen
open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.Propositional.Semantics

/-- An arbitrarily indexed ordered family of many-sorted formulae.
The strict total order records positions, including repeated formulae. -/
structure MSFormulaSequence (L : MSLanguage) where
  Index : Type
  before : Index → Index → Prop
  irrefl : ∀ i, ¬ before i i
  trans : ∀ i j k, before i j → before j k → before i k
  total : ∀ i j, i = j ∨ before i j ∨ before j i
  formula : Index → MSFormula L

/-- General carrier of possibly infinite ordered sequents, shared with G=. -/
structure MSInfSequentCore (L : MSLanguage) where
  antecedent : MSFormulaSequence L
  succedent : MSFormulaSequence L

/-- All formulae of an indexed sequent belong to the six-connective domain. -/
def MSInfSequentCore.IsSixConnective {L : MSLanguage} (seq : MSInfSequentCore L) : Prop :=
  (∀ i, msIsSixConnective (seq.antecedent.formula i)) ∧
  (∀ i, msIsSixConnective (seq.succedent.formula i))

/-- Lemma 10.4.1: possibly infinite sequents of equality-free G. -/
@[blueprint "chap10__lemma_10_4_1"]
def MSInfSequent (L : MSLanguage) (_hL : L.withoutEquality) :=
  {seq : MSInfSequentCore L // seq.IsSixConnective}

/-- A finite subsequence selects distinct positions in their original order. -/
def MSFormulaSequence.IsFiniteSubsequence {L : MSLanguage}
    (a : MSFormulaSequence L) (xs : List (MSFormula L)) : Prop :=
  ∃ f : Fin xs.length → a.Index,
    (∀ i j, i < j → a.before (f i) (f j)) ∧
    ∀ i, xs.get i = a.formula (f i)

/-- A finite subsequent selects an ordered subsequence on each side. -/
def MSInfSequentCore.IsFiniteSubsequent {L : MSLanguage}
    (seq : MSInfSequentCore L) (finite : MSSequentCore L) : Prop :=
  seq.antecedent.IsFiniteSubsequence finite.antecedent ∧
  seq.succedent.IsFiniteSubsequence finite.succedent

/-- Shared-assignment validity of an arbitrary indexed sequent. -/
def msInfSequentValidCore {L : MSLanguage} (seq : MSInfSequentCore L) : Prop :=
  ∀ (M : MSStructure L) (v : MSAssignment M),
    (∀ i, msFormulaEval M (seq.antecedent.formula i) v = BoolVal.T) →
    ∃ j, msFormulaEval M (seq.succedent.formula j) v = BoolVal.T

/-- Lemma 10.4.1: validity of a possibly infinite sequent in G. -/
@[blueprint "chap10__lemma_10_4_1"]
def msInfSequentValid {L : MSLanguage} {hL : L.withoutEquality}
    (seq : MSInfSequent L hL) : Prop := msInfSequentValidCore seq.val

/-- Lemma 10.4.1: a possibly infinite sequent is G-provable when some
finite subsequent, with the original order retained, has a G-proof. -/
@[blueprint "chap10__lemma_10_4_1"]
def msInfSequentProvable {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.withoutEquality) (seq : MSInfSequent L hL) : Prop :=
  ∃ finite : MSSequentCore L,
    seq.val.IsFiniteSubsequent finite ∧ msSequentProvable hL finite

/-- Theorem 10.4.1: no sorted variable free in any end-sequent formula
occurs bound in any end-sequent formula, on either side. -/
@[blueprint "chap10__theorem_10_4_1"]
def MSInfSequent.crossNoFreeBound {L : MSLanguage} {hL : L.withoutEquality}
    (seq : MSInfSequent L hL) : Prop :=
  ∀ x : MSVar L,
    ((∃ i, x ∈ msFormulaFV (seq.val.antecedent.formula i)) ∨
      (∃ j, x ∈ msFormulaFV (seq.val.succedent.formula j))) →
    (∀ i, x ∉ msFormulaBV (seq.val.antecedent.formula i)) ∧
      (∀ j, x ∉ msFormulaBV (seq.val.succedent.formula j))

/-- Lemma 10.4.1 (companion): `msSequentValid seq ↔ ∀ M, ¬
msSequentFalsifiableIn M seq`. Validity and "not falsifiable in any
structure" coincide. Many-sorted, `BoolVal`-valued analogue of
one-sorted `sequentValid_iff_not_falsifiable`. -/
@[blueprint "chap10__lemma_10_4_1"]
theorem msSequentValid_iff_not_falsifiable {L : MSLanguage}
    (seq : MSSequentCore L) :
    msSequentValid seq ↔ ∀ M : MSStructure L, ¬ msSequentFalsifiableIn M seq

-- ===================================================================
-- BoolVal connective helper lemmas (Ch3 truth functions, T/F form)
-- ===================================================================

-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem hAnd_eq_T {a b : BoolVal} :
    hAnd a b = BoolVal.T ↔ a = BoolVal.T ∧ b = BoolVal.T := by
  cases a <;> cases b <;> simp [hAnd]

-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem hOr_eq_F {a b : BoolVal} :
    hOr a b = BoolVal.F ↔ a = BoolVal.F ∧ b = BoolVal.F := by
  cases a <;> cases b <;> simp [hOr]



-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem hImplies_eq_F {a b : BoolVal} :
    hImplies a b = BoolVal.F ↔ a = BoolVal.T ∧ b = BoolVal.F := by
  cases a <;> cases b <;> simp [hImplies]



-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem hNeg_eq_T {a : BoolVal} : hNeg a = BoolVal.T ↔ a = BoolVal.F := by
  cases a <;> simp [hNeg]

-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem hNeg_eq_F {a : BoolVal} : hNeg a = BoolVal.F ↔ a = BoolVal.T := by
  cases a <;> simp [hNeg]

-- ===================================================================
-- Quantifier evaluation helper lemmas (forallM / existsM truth conditions)
-- ===================================================================

-- ATTACH-BLOCKER: size gate: retain original helper span in front
/-- The universally-quantified formula `∀_s x A` evaluates to `T` under
`v` iff `A` evaluates to `T` under every update of `v` at `(s, x)`. -/
theorem msEval_all_eq_T {L : MSLanguage} {M : MSStructure L}
    (s : L.SortType) (x : Nat) (A : MSFormula L) (v : MSAssignment M) :
    msFormulaEval M (MSFormula.all s x A) v = BoolVal.T ↔
      ∀ a : M.carrier s, msFormulaEval M A (msAssignUpdate M v s x a) = BoolVal.T := by
  simp only [msFormulaEval, forallM]
  split
  · rename_i h; exact ⟨fun _ => h, fun _ => rfl⟩
  · rename_i h
    constructor
    · intro hc; exact absurd hc (by decide)
    · intro hc; exact absurd hc h

-- ATTACH-BLOCKER: size gate: retain original helper span in front
/-- The existentially-quantified formula `∃_s x A` evaluates to `T` under
`v` iff `A` evaluates to `T` under some update of `v` at `(s, x)`. -/
theorem msEval_ex_eq_T {L : MSLanguage} {M : MSStructure L}
    (s : L.SortType) (x : Nat) (A : MSFormula L) (v : MSAssignment M) :
    msFormulaEval M (MSFormula.ex s x A) v = BoolVal.T ↔
      ∃ a : M.carrier s, msFormulaEval M A (msAssignUpdate M v s x a) = BoolVal.T := by
  simp only [msFormulaEval, existsM]
  split
  · rename_i h; exact ⟨fun _ => h, fun _ => rfl⟩
  · rename_i h
    constructor
    · intro hc; exact absurd hc (by decide)
    · intro hc; exact absurd hc h

-- ATTACH-BLOCKER: size gate: retain original helper span in front
/-- The universally-quantified formula `∀_s x A` evaluates to `F` under
`v` iff `A` evaluates to `F` under some update of `v` at `(s, x)`. -/
theorem msEval_all_eq_F {L : MSLanguage} {M : MSStructure L}
    (s : L.SortType) (x : Nat) (A : MSFormula L) (v : MSAssignment M) :
    msFormulaEval M (MSFormula.all s x A) v = BoolVal.F ↔
      ∃ a : M.carrier s, msFormulaEval M A (msAssignUpdate M v s x a) = BoolVal.F := by
  constructor
  · intro hF
    apply Classical.byContradiction
    intro hne
    have hall : ∀ a, msFormulaEval M A (msAssignUpdate M v s x a) = BoolVal.T :=
      fun a => boolVal_ne_F_eq_T (fun haF => hne ⟨a, haF⟩)
    have : msFormulaEval M (MSFormula.all s x A) v = BoolVal.T :=
      (msEval_all_eq_T s x A v).mpr hall
    rw [this] at hF; exact absurd hF (by decide)
  · rintro ⟨a, ha⟩
    apply boolVal_ne_T_eq_F
    intro hT
    exact absurd ((msEval_all_eq_T s x A v).mp hT a) (by rw [ha]; decide)

-- ATTACH-BLOCKER: size gate: retain original helper span in front
/-- The existentially-quantified formula `∃_s x A` evaluates to `F` under
`v` iff `A` evaluates to `F` under every update of `v` at `(s, x)`. -/
theorem msEval_ex_eq_F {L : MSLanguage} {M : MSStructure L}
    (s : L.SortType) (x : Nat) (A : MSFormula L) (v : MSAssignment M) :
    msFormulaEval M (MSFormula.ex s x A) v = BoolVal.F ↔
      ∀ a : M.carrier s, msFormulaEval M A (msAssignUpdate M v s x a) = BoolVal.F := by
  constructor
  · intro hF a
    apply boolVal_ne_T_eq_F
    intro hT
    have : msFormulaEval M (MSFormula.ex s x A) v = BoolVal.T :=
      (msEval_ex_eq_T s x A v).mpr ⟨a, hT⟩
    rw [this] at hF; exact absurd hF (by decide)
  · intro h
    apply boolVal_ne_T_eq_F
    intro hT
    obtain ⟨a, ha⟩ := (msEval_ex_eq_T s x A v).mp hT
    exact absurd ha (by rw [h a]; decide)

-- ATTACH-BLOCKER: size gate: retain original helper span in front
/-- Eigenvariable agreement helper: if no free variable of `A` other than
the bound `(s, x)` equals the eigenvariable `(s, y)`, then the assignment
that first sets the eigenvariable `(s, y) := a` and then the bound
variable `(s, x) := a` agrees, on every free variable of `A`, with the
assignment that only sets `(s, x) := a`. Used in the `allRight`/`exLeft`
falsification cases. -/
theorem msAgreeUpdateFresh {L : MSLanguage} [DecidableEq L.SortType]
    (M : MSStructure L) (v : MSAssignment M) (s : L.SortType) (y x : Nat)
    (a : M.carrier s) (A : MSFormula L)
    (yA : ∀ z : MSVar L, z ∈ msFormulaFV A → z ≠ (s, x) → z ≠ (s, y)) :
    ∀ z : MSVar L, z ∈ msFormulaFV A →
      msAssignUpdate M (msAssignUpdate M v s y a) s x a z.1 z.2 =
        msAssignUpdate M v s x a z.1 z.2 := by
  intro z hz
  simp only [msAssignUpdate]
  by_cases h1 : z.1 = s
  · subst h1
    by_cases h2 : z.2 = x
    · subst h2; simp
    · have hzx : z ≠ (z.1, x) := by
        intro hzeq; exact h2 (congrArg Prod.snd hzeq)
      have hzy : z ≠ (z.1, y) := yA z hz hzx
      have h3 : z.2 ≠ y := fun heq => hzy (by
        have : z = (z.1, z.2) := rfl
        rw [this, heq])
      simp [h2, h3]
  · simp [h1]

-- ===================================================================
-- List membership helpers (polymorphic; mirror one-sorted Gentzen)
-- ===================================================================

-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem msMem1_cases {α : Type} {a : α} {Γ Δ : List α} {X : α}
    (h : a ∈ Γ ++ [X] ++ Δ) : a ∈ Γ ∨ a = X ∨ a ∈ Δ := by
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with (h1 | h2) | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem msMem1_left {α : Type} {a : α} {Γ Δ : List α} {X : α}
    (h : a ∈ Γ) : a ∈ Γ ++ [X] ++ Δ :=
  List.mem_append_left _ (List.mem_append_left _ h)
-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem msMem1_center {α : Type} {Γ Δ : List α} {X : α} :
    X ∈ Γ ++ [X] ++ Δ :=
  List.mem_append_left _ (List.mem_append_right _ (List.Mem.head _))
-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem msMem1_right {α : Type} {a : α} {Γ Δ : List α} {X : α}
    (h : a ∈ Δ) : a ∈ Γ ++ [X] ++ Δ :=
  List.mem_append_right _ h

-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem msMem2_cases {α : Type} {a : α} {Γ Δ : List α} {X Y : α}
    (h : a ∈ Γ ++ [X, Y] ++ Δ) : a ∈ Γ ∨ a = X ∨ a = Y ∨ a ∈ Δ := by
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with (h1 | h2 | h3) | h4
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr h4))

-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem msMem2_left {α : Type} {a : α} {Γ Δ : List α} {X Y : α}
    (h : a ∈ Γ) : a ∈ Γ ++ [X, Y] ++ Δ :=
  List.mem_append_left _ (List.mem_append_left _ h)
-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem msMem2_first {α : Type} {Γ Δ : List α} {X Y : α} :
    X ∈ Γ ++ [X, Y] ++ Δ :=
  List.mem_append_left _ (List.mem_append_right _ (List.Mem.head _))
-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem msMem2_second {α : Type} {Γ Δ : List α} {X Y : α} :
    Y ∈ Γ ++ [X, Y] ++ Δ :=
  List.mem_append_left _ (List.mem_append_right _ (List.Mem.tail _ (List.Mem.head _)))
-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem msMem2_right {α : Type} {a : α} {Γ Δ : List α} {X Y : α}
    (h : a ∈ Δ) : a ∈ Γ ++ [X, Y] ++ Δ :=
  List.mem_append_right _ h

-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem msMemcat_cases {α : Type} {a : α} {Γ Δ : List α}
    (h : a ∈ Γ ++ Δ) : a ∈ Γ ∨ a ∈ Δ := List.mem_append.mp h
-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem msMemcat_left {α : Type} {a : α} {Γ Δ : List α}
    (h : a ∈ Γ) : a ∈ Γ ++ Δ := List.mem_append_left _ h
-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem msMemcat_right {α : Type} {a : α} {Γ Δ : List α}
    (h : a ∈ Δ) : a ∈ Γ ++ Δ := List.mem_append_right _ h

-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem msMemcons_cases {α : Type} {a : α} {Γ : List α} {X : α}
    (h : a ∈ [X] ++ Γ) : a = X ∨ a ∈ Γ := by
  simp only [List.singleton_append, List.mem_cons] at h; exact h
-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem msMemcons_head {α : Type} {Γ : List α} {X : α} :
    X ∈ [X] ++ Γ := List.mem_cons_self
-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem msMemcons_tail {α : Type} {a : α} {Γ : List α} {X : α}
    (h : a ∈ Γ) : a ∈ [X] ++ Γ := List.mem_cons.mpr (Or.inr h)

-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem msMemsnoc_left {α : Type} {a : α} {Γ : List α} {X : α}
    (h : a ∈ Γ) : a ∈ Γ ++ [X] := List.mem_append_left _ h
-- ATTACH-BLOCKER: size gate: retain original helper span in front
theorem msMemsnoc_right {α : Type} {Γ : List α} {X : α} :
    X ∈ Γ ++ [X] := List.mem_append_right _ (List.Mem.head _)

-- ===================================================================
-- Lemma 10.4.1: Rule falsification preservation (many-sorted)
-- ===================================================================

-- ATTACH-BLOCKER: size gate: retain original helper span in front
/-- Lemma 10.4.1 (companion): For each one-premise rule of G, the
conclusion sequent is falsifiable in `M` iff the premise is. Many-sorted,
`BoolVal`-valued analogue of one-sorted `ruleFalsificationIff1`. Reasons
about `BoolVal` connective values via the Ch3 truth-function helper
lemmas; quantifier cases use `msFormulaSubstEvalDirect` and the §10.3
coincidence lemma. -/
theorem msRuleFalsificationIff1 {L : MSLanguage} [DecidableEq L.SortType]
    (M : MSStructure L) {prem conc : MSSequentCore L}
    (rule : MSGentzenStep1Frame prem conc) :
    msSequentFalsifiableIn M conc ↔ msSequentFalsifiableIn M prem := by
  cases rule with
  | conjLeft Γ Δ Λ A B =>
    constructor
    · intro ⟨v, hant, hsucc⟩
      refine ⟨v, fun F hF => ?_, hsucc⟩
      rcases msMem2_cases hF with h1 | h2 | h3 | h4
      · exact hant F (msMem1_left h1)
      · rw [h2]; exact (hAnd_eq_T.mp (hant _ msMem1_center)).1
      · rw [h3]; exact (hAnd_eq_T.mp (hant _ msMem1_center)).2
      · exact hant F (msMem1_right h4)
    · intro ⟨v, hant, hsucc⟩
      refine ⟨v, fun F hF => ?_, hsucc⟩
      rcases msMem1_cases hF with h1 | rfl | h3
      · exact hant F (msMem2_left h1)
      · exact hAnd_eq_T.mpr ⟨hant A msMem2_first, hant B msMem2_second⟩
      · exact hant F (msMem2_right h3)
  | disjRight Γ Δ Λ A B =>
    constructor
    · intro ⟨v, hant, hsucc⟩
      have hAB := hsucc _ msMem1_center
      obtain ⟨hA, hB⟩ := hOr_eq_F.mp hAB
      refine ⟨v, hant, fun F hF => ?_⟩
      rcases msMem2_cases hF with h1 | h2 | h3 | h4
      · exact hsucc F (msMem1_left h1)
      · rw [h2]; exact hA
      · rw [h3]; exact hB
      · exact hsucc F (msMem1_right h4)
    · intro ⟨v, hant, hsucc⟩
      refine ⟨v, hant, fun F hF => ?_⟩
      rcases msMem1_cases hF with h1 | rfl | h3
      · exact hsucc F (msMem2_left h1)
      · exact hOr_eq_F.mpr ⟨hsucc A msMem2_first, hsucc B msMem2_second⟩
      · exact hsucc F (msMem2_right h3)
  | implRight Γ Δ Λ A B =>
    constructor
    · intro ⟨v, hant, hsucc⟩
      have hAB := hsucc _ msMem1_center
      obtain ⟨hA, hB⟩ := hImplies_eq_F.mp hAB
      refine ⟨v, fun F hF => ?_, fun F hF => ?_⟩
      · rcases msMemcons_cases hF with rfl | hF'
        · exact hA
        · exact hant F hF'
      · rcases msMemcons_cases hF with rfl | hF'
        · exact hB
        · rcases msMemcat_cases hF' with hΔ | hΛ
          · exact hsucc F (msMem1_left hΔ)
          · exact hsucc F (msMem1_right hΛ)
    · intro ⟨v, hant, hsucc⟩
      refine ⟨v, fun F hF => hant F (msMemcons_tail hF), fun F hF => ?_⟩
      rcases msMem1_cases hF with h1 | rfl | h3
      · exact hsucc F (msMemcons_tail (msMemcat_left h1))
      · exact hImplies_eq_F.mpr ⟨hant A msMemcons_head, hsucc B msMemcons_head⟩
      · exact hsucc F (msMemcons_tail (msMemcat_right h3))
  | negLeft Γ Δ Λ A =>
    constructor
    · intro ⟨v, hant, hsucc⟩
      have hNA := hant _ msMem1_center
      refine ⟨v, fun F hF => ?_, fun F hF => ?_⟩
      · rcases msMemcat_cases hF with hΓ | hΔ
        · exact hant F (msMem1_left hΓ)
        · exact hant F (msMem1_right hΔ)
      · rcases msMemcons_cases hF with rfl | hΛ
        · exact hNeg_eq_T.mp hNA
        · exact hsucc F hΛ
    · intro ⟨v, hant, hsucc⟩
      have hA := hsucc A msMemcons_head
      refine ⟨v, fun F hF => ?_, fun F hF => hsucc F (msMemcons_tail hF)⟩
      rcases msMem1_cases hF with h1 | rfl | h3
      · exact hant F (msMemcat_left h1)
      · exact hNeg_eq_T.mpr hA
      · exact hant F (msMemcat_right h3)
  | negRight Γ Δ Λ A =>
    constructor
    · intro ⟨v, hant, hsucc⟩
      have hNA := hsucc _ msMem1_center
      have hA : msFormulaEval M A v = BoolVal.T := hNeg_eq_F.mp hNA
      refine ⟨v, fun F hF => ?_, fun F hF => ?_⟩
      · rcases msMemcons_cases hF with rfl | hF'
        · exact hA
        · exact hant F hF'
      · rcases msMemcat_cases hF with hΔ | hΛ
        · exact hsucc F (msMem1_left hΔ)
        · exact hsucc F (msMem1_right hΛ)
    · intro ⟨v, hant, hsucc⟩
      have hA := hant A msMemcons_head
      refine ⟨v, fun F hF => hant F (msMemcons_tail hF), fun F hF => ?_⟩
      rcases msMem1_cases hF with h1 | rfl | h3
      · exact hsucc F (msMemcat_left h1)
      · exact hNeg_eq_F.mpr hA
      · exact hsucc F (msMemcat_right h3)
  | allLeft s t Γ Δ Λ x A hfree =>
    constructor
    · intro ⟨v, hant, hsucc⟩
      have hAll := hant _ msMem1_center
      refine ⟨v, fun F hF => ?_, hsucc⟩
      rcases msMem2_cases hF with h1 | h2 | h3 | h4
      · exact hant F (msMem1_left h1)
      · -- side formula A[t/x] is T because ∀ x A is T.
        rw [h2, msFormulaSubstEvalDirect A s x t hfree v]
        exact (msEval_all_eq_T s x A v).mp hAll (msTermEval M v t)
      · rw [h3]; exact hAll
      · exact hant F (msMem1_right h4)
    · intro ⟨v, hant, hsucc⟩
      refine ⟨v, fun F hF => ?_, hsucc⟩
      rcases msMem1_cases hF with h1 | rfl | h3
      · exact hant F (msMem2_left h1)
      · exact hant _ msMem2_second
      · exact hant F (msMem2_right h3)
  | exRight s t Γ Δ Λ x A hfree =>
    constructor
    · intro ⟨v, hant, hsucc⟩
      have hExA := hsucc _ msMem1_center
      refine ⟨v, hant, fun F hF => ?_⟩
      rcases msMem2_cases hF with h1 | h2 | h3 | h4
      · exact hsucc F (msMem1_left h1)
      · -- side formula A[t/x] is F because ∃ x A is F.
        rw [h2, msFormulaSubstEvalDirect A s x t hfree v]
        exact (msEval_ex_eq_F s x A v).mp hExA (msTermEval M v t)
      · rw [h3]; exact hExA
      · exact hsucc F (msMem1_right h4)
    · intro ⟨v, hant, hsucc⟩
      refine ⟨v, hant, fun F hF => ?_⟩
      rcases msMem1_cases hF with h1 | rfl | h3
      · exact hsucc F (msMem2_left h1)
      · exact hsucc _ msMem2_second
      · exact hsucc F (msMem2_right h3)
  | allRight s y Γ Δ Λ x A hfresh hfreeFor =>
    -- Eigenvariable (s, y) is fresh in the lower sequent.
    have yA : ∀ z : MSVar L, z ∈ msFormulaFV A → z ≠ (s, x) → z ≠ (s, y) := by
      intro z hz hzx hzy
      apply hfresh (MSFormula.all s x A) (msMemcat_right msMem1_center)
      show (s, y) ∈ msFormulaFV A \ Set.singleton (s, x)
      refine ⟨hzy ▸ hz, ?_⟩
      intro hsing
      exact hzx (hzy.trans (hsing : (s, y) = (s, x)))
    constructor
    · intro ⟨v, hant, hsucc⟩
      -- ∀_s x A is F: some a with A(v[x := a]) = F.
      obtain ⟨a, ha⟩ := (msEval_all_eq_F s x A v).mp (hsucc _ msMem1_center)
      -- Update the eigenvariable to a fresh witness.
      let v' : MSAssignment M := msAssignUpdate M v s y a
      -- v' agrees with v away from (s, y).
      have coin_fresh : ∀ (F : MSFormula L), (s, y) ∉ msFormulaFV F →
          ∀ z : MSVar L, z ∈ msFormulaFV F → v z.1 z.2 = v' z.1 z.2 := by
        intro F hyF z hz
        simp only [v', msAssignUpdate]
        by_cases h1 : z.1 = s
        · subst h1
          by_cases h2 : z.2 = y
          · exact absurd (show ((z.1, y) : MSVar L) ∈ msFormulaFV F by rw [← h2]; exact hz) hyF
          · simp [h2]
        · simp [h1]
      have hant' : ∀ F ∈ Γ, msFormulaEval M F v' = BoolVal.T := fun F hF =>
        (Semantics.Substitution.msCoincidenceLemma M F v v'
          (coin_fresh F (hfresh F (msMemcat_left hF)))) ▸ hant F hF
      have hsucc' : ∀ F ∈ Δ ++ Λ, msFormulaEval M F v' = BoolVal.F := by
        intro F hF
        have hyF : (s, y) ∉ msFormulaFV F := by
          rcases List.mem_append.mp hF with hD | hL
          · exact hfresh F (msMemcat_right (msMem1_left hD))
          · exact hfresh F (msMemcat_right (msMem1_right hL))
        rw [← Semantics.Substitution.msCoincidenceLemma M F v v' (coin_fresh F hyF)]
        rcases List.mem_append.mp hF with hD | hL
        · exact hsucc F (msMem1_left hD)
        · exact hsucc F (msMem1_right hL)
      -- A[y/x] evaluated at v' is F.
      have hAyx : msFormulaEval M (msFormulaSubst A s x (MSTerm.var s y)) v' =
          BoolVal.F := by
        rw [msFormulaSubstEvalDirect A s x (MSTerm.var s y) hfreeFor v']
        -- v'[x := v' s y] agrees with v[x := a] on FV(A).
        have hval : msTermEval M v' (MSTerm.var s y) = a := by
          simp only [msTermEval, varMeaning, v', msAssignUpdate]; simp
        rw [hval]
        rw [Semantics.Substitution.msCoincidenceLemma M A
          (msAssignUpdate M v' s x a) (msAssignUpdate M v s x a)
          (msAgreeUpdateFresh M v s y x a A yA)]
        exact ha
      refine ⟨v', hant', fun F hF => ?_⟩
      rcases msMem1_cases hF with h1 | rfl | h3
      · exact hsucc' F (List.mem_append_left _ h1)
      · exact hAyx
      · exact hsucc' F (List.mem_append_right _ h3)
    · intro ⟨v, hant, hsucc⟩
      have hAyx := hsucc _ msMem1_center
      -- A[y/x] = F gives A(v[x := v s y]) = F, hence ∀ x A = F.
      have hNotA : msFormulaEval M A (msAssignUpdate M v s x (v s y)) = BoolVal.F := by
        have := msFormulaSubstEvalDirect A s x (MSTerm.var s y) hfreeFor v
        rw [this] at hAyx
        have hval : msTermEval M v (MSTerm.var s y) = v s y := by
          simp only [msTermEval, varMeaning]
        rw [hval] at hAyx
        exact hAyx
      refine ⟨v, hant, fun F hF => ?_⟩
      rcases msMem1_cases hF with h1 | rfl | h3
      · exact hsucc F (msMem1_left h1)
      · exact (msEval_all_eq_F s x A v).mpr ⟨v s y, hNotA⟩
      · exact hsucc F (msMem1_right h3)
  | exLeft s y Γ Δ Λ x A hfresh hfreeFor =>
    have yA : ∀ z : MSVar L, z ∈ msFormulaFV A → z ≠ (s, x) → z ≠ (s, y) := by
      intro z hz hzx hzy
      apply hfresh (MSFormula.ex s x A) (msMemcat_left msMem1_center)
      show (s, y) ∈ msFormulaFV A \ Set.singleton (s, x)
      refine ⟨hzy ▸ hz, ?_⟩
      intro hsing
      exact hzx (hzy.trans (hsing : (s, y) = (s, x)))
    constructor
    · intro ⟨v, hant, hsucc⟩
      -- ∃_s x A is T: some a with A(v[x := a]) = T.
      obtain ⟨a, ha⟩ := (msEval_ex_eq_T s x A v).mp (hant _ msMem1_center)
      let v' : MSAssignment M := msAssignUpdate M v s y a
      have coin_fresh : ∀ (F : MSFormula L), (s, y) ∉ msFormulaFV F →
          ∀ z : MSVar L, z ∈ msFormulaFV F → v z.1 z.2 = v' z.1 z.2 := by
        intro F hyF z hz
        simp only [v', msAssignUpdate]
        by_cases h1 : z.1 = s
        · subst h1
          by_cases h2 : z.2 = y
          · exact absurd (show ((z.1, y) : MSVar L) ∈ msFormulaFV F by rw [← h2]; exact hz) hyF
          · simp [h2]
        · simp [h1]
      have hant' : ∀ F ∈ Γ ++ Δ, msFormulaEval M F v' = BoolVal.T := by
        intro F hF
        have hyF : (s, y) ∉ msFormulaFV F := by
          rcases List.mem_append.mp hF with hΓ | hΔ
          · exact hfresh F (msMemcat_left (msMem1_left hΓ))
          · exact hfresh F (msMemcat_left (msMem1_right hΔ))
        rw [← Semantics.Substitution.msCoincidenceLemma M F v v' (coin_fresh F hyF)]
        rcases List.mem_append.mp hF with hΓ | hΔ
        · exact hant F (msMem1_left hΓ)
        · exact hant F (msMem1_right hΔ)
      have hsucc' : ∀ F ∈ Λ, msFormulaEval M F v' = BoolVal.F := by
        intro F hF
        have hyF : (s, y) ∉ msFormulaFV F := hfresh F (msMemcat_right hF)
        rw [← Semantics.Substitution.msCoincidenceLemma M F v v' (coin_fresh F hyF)]
        exact hsucc F hF
      have hAyx : msFormulaEval M (msFormulaSubst A s x (MSTerm.var s y)) v' =
          BoolVal.T := by
        rw [msFormulaSubstEvalDirect A s x (MSTerm.var s y) hfreeFor v']
        have hval : msTermEval M v' (MSTerm.var s y) = a := by
          simp only [msTermEval, varMeaning, v', msAssignUpdate]; simp
        rw [hval]
        rw [Semantics.Substitution.msCoincidenceLemma M A
          (msAssignUpdate M v' s x a) (msAssignUpdate M v s x a)
          (msAgreeUpdateFresh M v s y x a A yA)]
        exact ha
      refine ⟨v', fun F hF => ?_, hsucc'⟩
      rcases msMem1_cases hF with h1 | rfl | h3
      · exact hant' F (List.mem_append_left _ h1)
      · exact hAyx
      · exact hant' F (List.mem_append_right _ h3)
    · intro ⟨v, hant, hsucc⟩
      have hAyx := hant _ msMem1_center
      have hExA : msFormulaEval M (MSFormula.ex s x A) v = BoolVal.T := by
        apply (msEval_ex_eq_T s x A v).mpr
        refine ⟨v s y, ?_⟩
        have := msFormulaSubstEvalDirect A s x (MSTerm.var s y) hfreeFor v
        rw [this] at hAyx
        have hval : msTermEval M v (MSTerm.var s y) = v s y := by
          simp only [msTermEval, varMeaning]
        rw [hval] at hAyx
        exact hAyx
      refine ⟨v, fun F hF => ?_, hsucc⟩
      rcases msMem1_cases hF with h1 | rfl | h3
      · exact hant F (msMem1_left h1)
      · exact hExA
      · exact hant F (msMem1_right h3)



theorem hOr_eq_T {a b : BoolVal} :
    hOr a b = BoolVal.T ↔ a = BoolVal.T ∨ b = BoolVal.T := by
  cases a <;> cases b <;> simp [hOr]



theorem hImplies_eq_T {a b : BoolVal} :
    hImplies a b = BoolVal.T ↔ a = BoolVal.F ∨ b = BoolVal.T := by
  cases a <;> cases b <;> simp [hImplies]



















































/-- Lemma 10.4.1 (companion, two-premise): For each two-premise rule of G,
the conclusion sequent is falsifiable in `M` iff at least one premise is
falsifiable. Many-sorted, `BoolVal`-valued analogue of one-sorted
`ruleFalsificationIff2`. -/
theorem msRuleFalsificationIff2 {L : MSLanguage}
    (M : MSStructure L) {prem1 prem2 conc : MSSequentCore L}
    (rule : MSGentzenStep2Frame prem1 prem2 conc) :
    msSequentFalsifiableIn M conc ↔
      (msSequentFalsifiableIn M prem1 ∨ msSequentFalsifiableIn M prem2) := by
  cases rule with
  | conjRight Γ Δ Λ A B =>
    constructor
    · intro ⟨v, hant, hsucc⟩
      have hAB := hsucc _ msMem1_center
      simp only [msFormulaEval, Semantics.andM] at hAB
      by_cases hA : msFormulaEval M A v = BoolVal.T
      · right
        have hB : msFormulaEval M B v = BoolVal.F := by
          rw [hA] at hAB
          cases hb : msFormulaEval M B v with
          | T => rw [hb] at hAB; exact absurd hAB (by decide)
          | F => rfl
        refine ⟨v, hant, fun F hF => ?_⟩
        rcases msMem1_cases hF with h1 | rfl | h3
        · exact hsucc F (msMem1_left h1)
        · exact hB
        · exact hsucc F (msMem1_right h3)
      · left
        refine ⟨v, hant, fun F hF => ?_⟩
        rcases msMem1_cases hF with h1 | rfl | h3
        · exact hsucc F (msMem1_left h1)
        · exact boolVal_ne_T_eq_F hA
        · exact hsucc F (msMem1_right h3)
    · intro h; rcases h with ⟨v, hant, hsucc⟩ | ⟨v, hant, hsucc⟩
      · have hA := hsucc _ msMem1_center
        refine ⟨v, hant, fun F hF => ?_⟩
        rcases msMem1_cases hF with h1 | rfl | h3
        · exact hsucc F (msMem1_left h1)
        · simp only [msFormulaEval, Semantics.andM]; rw [hA]; rfl
        · exact hsucc F (msMem1_right h3)
      · have hB := hsucc _ msMem1_center
        refine ⟨v, hant, fun F hF => ?_⟩
        rcases msMem1_cases hF with h1 | rfl | h3
        · exact hsucc F (msMem1_left h1)
        · simp only [msFormulaEval, Semantics.andM]; rw [hB]
          cases msFormulaEval M A v <;> rfl
        · exact hsucc F (msMem1_right h3)
  | disjLeft Γ Δ Λ A B =>
    constructor
    · intro ⟨v, hant, hsucc⟩
      have hAB := hant _ msMem1_center
      rcases hOr_eq_T.mp hAB with hA | hB
      · left
        refine ⟨v, fun F hF => ?_, hsucc⟩
        rcases msMem1_cases hF with h1 | rfl | h3
        · exact hant F (msMem1_left h1)
        · exact hA
        · exact hant F (msMem1_right h3)
      · right
        refine ⟨v, fun F hF => ?_, hsucc⟩
        rcases msMem1_cases hF with h1 | rfl | h3
        · exact hant F (msMem1_left h1)
        · exact hB
        · exact hant F (msMem1_right h3)
    · intro h; rcases h with ⟨v, hant, hsucc⟩ | ⟨v, hant, hsucc⟩
      · refine ⟨v, fun F hF => ?_, hsucc⟩
        rcases msMem1_cases hF with h1 | rfl | h3
        · exact hant F (msMem1_left h1)
        · exact hOr_eq_T.mpr (Or.inl (hant A msMem1_center))
        · exact hant F (msMem1_right h3)
      · refine ⟨v, fun F hF => ?_, hsucc⟩
        rcases msMem1_cases hF with h1 | rfl | h3
        · exact hant F (msMem1_left h1)
        · exact hOr_eq_T.mpr (Or.inr (hant B msMem1_center))
        · exact hant F (msMem1_right h3)
  | implLeft Γ Δ Λ A B =>
    constructor
    · intro ⟨v, hant, hsucc⟩
      have hAB := hant _ msMem1_center
      by_cases hA : msFormulaEval M A v = BoolVal.T
      · -- A=T and A⊃B=T force B=T: prem2 falsifiable.
        have hB : msFormulaEval M B v = BoolVal.T :=
          (hImplies_eq_T.mp hAB).resolve_left (fun hAF =>
            absurd (hAF ▸ hA) (by decide))
        right
        refine ⟨v, fun F hF => ?_, hsucc⟩
        rcases msMemcons_cases hF with rfl | hF'
        · exact hB
        · rcases msMemcat_cases hF' with hΓ | hΔ
          · exact hant F (msMem1_left hΓ)
          · exact hant F (msMem1_right hΔ)
      · -- A=F: prem1 falsifiable (A is a new succedent, F).
        left
        refine ⟨v, fun F hF => ?_, fun F hF => ?_⟩
        · rcases msMemcat_cases hF with hΓ | hΔ
          · exact hant F (msMem1_left hΓ)
          · exact hant F (msMem1_right hΔ)
        · rcases msMemcons_cases hF with rfl | hΛ
          · exact boolVal_ne_T_eq_F hA
          · exact hsucc F hΛ
    · intro h; rcases h with ⟨v, hant, hsucc⟩ | ⟨v, hant, hsucc⟩
      · -- prem1 falsifiable: A (in succedent) is F, so A⊃B=T.
        have hA := hsucc A msMemcons_head
        refine ⟨v, fun F hF => ?_, fun F hF => hsucc F (msMemcons_tail hF)⟩
        rcases msMem1_cases hF with h1 | rfl | h3
        · exact hant F (msMemcat_left h1)
        · exact hImplies_eq_T.mpr (Or.inl hA)
        · exact hant F (msMemcat_right h3)
      · -- prem2 falsifiable: B (in antecedent) is T, so A⊃B=T.
        have hB := hant B msMemcons_head
        refine ⟨v, fun F hF => ?_, hsucc⟩
        rcases msMem1_cases hF with h1 | rfl | h3
        · exact hant F (msMemcons_tail (msMemcat_left h1))
        · exact hImplies_eq_T.mpr (Or.inr hB)
        · exact hant F (msMemcons_tail (msMemcat_right h3))

/-- General-carrier one-premise soundness, also used by G=. -/
theorem msRuleValidityIff1Core {L : MSLanguage} [DecidableEq L.SortType]
    {prem conc : MSSequentCore L} (rule : MSGentzenStep1Core prem conc) :
    msSequentValid conc ↔ msSequentValid prem := by
  rw [msSequentValid_iff_not_falsifiable, msSequentValid_iff_not_falsifiable]
  exact forall_congr' (fun M => not_congr (msRuleFalsificationIff1 M rule.frame))

/-- General-carrier two-premise soundness, also used by G=. -/
theorem msRuleValidityIff2Core {L : MSLanguage}
    {prem1 prem2 conc : MSSequentCore L} (rule : MSGentzenStep2Core prem1 prem2 conc) :
    msSequentValid conc ↔ (msSequentValid prem1 ∧ msSequentValid prem2) := by
  rw [msSequentValid_iff_not_falsifiable, msSequentValid_iff_not_falsifiable,
      msSequentValid_iff_not_falsifiable]
  constructor
  · intro h
    refine ⟨fun M hF => h M ?_, fun M hF => h M ?_⟩
    · exact (msRuleFalsificationIff2 M rule.frame).mpr (Or.inl hF)
    · exact (msRuleFalsificationIff2 M rule.frame).mpr (Or.inr hF)
  · intro ⟨h1, h2⟩ M hF
    rcases (msRuleFalsificationIff2 M rule.frame).mp hF with hF1 | hF2
    · exact h1 M hF1
    · exact h2 M hF2

/-- Finite soundness on the general carrier shared by G and G=. -/
theorem msProofTreeValidCore {L : MSLanguage} [DecidableEq L.SortType]
    {seq : MSSequentCore L} (t : MSGProofTreeCore seq) : msSequentValid seq := by
  induction t with
  | axiom_ s _hDomain hax =>
    intro M v hant
    obtain ⟨A, hA_ant, hA_suc⟩ := hax
    exact ⟨A, hA_suc, hant A hA_ant⟩
  | onePremise rule _ ih =>
    exact (msRuleValidityIff1Core rule).mpr ih
  | twoPremise rule _ _ ih1 ih2 =>
    exact (msRuleValidityIff2Core rule).mpr ⟨ih1, ih2⟩

/-- Lemma 10.4.1 (companion): For each one-premise rule of G, the
conclusion sequent is valid iff the premise is valid. Proved (in a later
stage) by transposing the per-rule falsifiability-iff lemmas through
`msSequentValid_iff_not_falsifiable`, exactly mirroring one-sorted
`ruleValidityIff1` — but reasoning about `BoolVal` equalities via the
§10.3 lifted connective lemmas rather than Prop logic. -/
@[blueprint "chap10__lemma_10_4_1"]
theorem msRuleValidityIff1 {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.withoutEquality)
    {prem conc : MSSequentCore L} (rule : MSGentzenStep1 hL prem conc) :
    msSequentValid conc ↔ msSequentValid prem

/-- Lemma 10.4.1 (companion): For each two-premise rule of G, the
conclusion sequent is valid iff both premises are valid. Many-sorted,
`BoolVal`-valued analogue of one-sorted `ruleValidityIff2`. -/
@[blueprint "chap10__lemma_10_4_1"]
theorem msRuleValidityIff2 {L : MSLanguage}
    (hL : L.withoutEquality)
    {prem1 prem2 conc : MSSequentCore L} (rule : MSGentzenStep2 hL prem1 prem2 conc) :
    msSequentValid conc ↔ (msSequentValid prem1 ∧ msSequentValid prem2)

/-- Lemma 10.4.1 (companion): Every (indexed) proof tree in G has a valid
conclusion sequent. Proved by induction on the tree: the `axiom_` case
uses the shared common formula (true in the antecedent by hypothesis,
hence a true witness in the succedent), and the `onePremise` /
`twoPremise` cases apply `msRuleValidityIff1.mpr` / `msRuleValidityIff2.mpr`
to the inductive hypotheses. Many-sorted analogue of one-sorted
`proofTreeValid`. -/
@[blueprint "chap10__lemma_10_4_1"]
theorem msProofTreeValid {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.withoutEquality)
    {seq : MSSequentCore L} (t : MSGProofTree hL seq) : msSequentValid seq

/-- Lemma 10.4.1: every possibly infinite sequent provable in the
many-sorted equality-free system G is valid under a shared assignment. -/
@[blueprint "chap10__lemma_10_4_1" (main := true)]
theorem msSoundnessG {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.withoutEquality) (seq : MSInfSequent L hL)
    (h : msInfSequentProvable hL seq) : msInfSequentValid seq

/-- Theorem 10.4.1 (completeness direction): a valid, possibly infinite
sequent in the equality-free six-connective domain has a finite G-provable
subsequent. Free/bound separation is imposed on the whole end sequent. -/
@[attach_debt, blueprint "chap10__theorem_10_4_1"]
theorem msSearchCompletenessValid {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.withoutEquality) (seq : MSInfSequent L hL)
    (hCross : seq.crossNoFreeBound) (hValid : msInfSequentValid seq) :
    msInfSequentProvable hL seq

/-- Theorem 10.4.1: Gödel's extended completeness theorem for many-sorted
G. A possibly infinite equality-free six-connective end sequent with no
sorted variable both free and bound is valid iff it has a finite
G-provable subsequent in the inherited order. -/
@[attach_debt, blueprint "chap10__theorem_10_4_1" (main := true)]
theorem msGoedelExtendedCompletenessG {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.withoutEquality) (seq : MSInfSequent L hL)
    (hCross : seq.crossNoFreeBound) :
    msInfSequentValid seq ↔ msInfSequentProvable hL seq

end LCS.FirstOrder.ManySorted.Gentzen
end
