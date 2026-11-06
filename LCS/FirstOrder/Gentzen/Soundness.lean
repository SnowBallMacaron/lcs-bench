import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics
import LCS.FirstOrder.SemanticsN
import LCS.FirstOrder.SemanticsN.Substitution
import LCS.FirstOrder.Gentzen.DeductionTrees
import Attach
import LCS.FirstOrder.Gentzen.Soundness.ProofsStamp

/-! # Soundness of the system G (Section 5.4.3)

Lemma 5.4.1 (substitution and evaluation), Lemma 5.4.2 (the rules preserve
falsifiability and validity) and Lemma 5.4.3 (soundness of G).
Source: Logic for Computer Science, Gallier 2015
-/

section
namespace LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution

-- ===================================================================
-- termCoincidence imported from SemanticsN

-- ===================================================================
-- Lemma 5.4.1 (Part i): Term substitution-evaluation equivalence
-- ===================================================================

/-- Lemma 5.4.1 (companion, Part i): For any terms t and r, structure
M, and assignment s, the evaluation of r[t/x] under s equals the
evaluation of r[a/x] under s, where a is the naming constant for
t_M[s]. Proved by structural induction on term r. -/
@[blueprint "chap5__lemma_5_4_1" (main := true)]
theorem termSubstNamingConst {L : Language}
    (M : Structure L) (s : Assignment (extendedInterp M))
    (t r : Term (extendedLanguage L M.carrier)) (x : Nat) :
    termEval (extendedInterp M) s (termSubst r t x) =
    termEval (extendedInterp M) s
      (termSubst r (namingConst (termEval (extendedInterp M) s t)) x) 

-- ===================================================================
-- Lemma 5.4.1 (Part ii): FormulaN substitution-evaluation equivalence
-- on the extended language
-- ===================================================================

/-- Proof of Lemma 5.4.1 (ii): Over a language without equality, replacing
    a free-for term by its naming constant preserves formula satisfaction. -/
@[blueprint "chap5__lemma_5_4_1" (main := true)]
theorem formulaSubstNamingConstNoEq {L : Language} (hL : L.withoutEquality)
    (M : Structure L) (s : Assignment (extendedInterp M))
    (A : FormulaN (extendedLanguage L M.carrier))
    (t : Term (extendedLanguage L M.carrier)) (x : Nat)
    (hfree : isFreeForN t x A) :
    formulaEvalN (extendedInterp M) (formulaSubstN A t x) s ↔
    formulaEvalN (extendedInterp M)
      (formulaSubstN A (namingConst (termEval (extendedInterp M) s t)) x) s 

-- ===================================================================
-- Helpers for list membership reasoning
-- ===================================================================

-- Decompose membership in Γ ++ [X] ++ Δ
-- retained: used by LCS.FirstOrder.Equality.Part2, LCS.FirstOrder.Gentzen.Part2
theorem mem1_cases {α : Type} {a : α} {Γ Δ : List α} {X : α}
    (h : a ∈ Γ ++ [X] ++ Δ) : a ∈ Γ ∨ a = X ∨ a ∈ Δ := by
-- BEGIN PROOF
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with (h1 | h2) | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

-- Construct membership in Γ ++ [X] ++ Δ
-- retained: used by LCS.FirstOrder.Equality.Part2, LCS.FirstOrder.Gentzen.Part2
theorem mem1_left {α : Type} {a : α} {Γ Δ : List α} {X : α}
    (h : a ∈ Γ) : a ∈ Γ ++ [X] ++ Δ :=
-- BEGIN PROOF
  List.mem_append_left _ (List.mem_append_left _ h)

-- retained: used by LCS.FirstOrder.Gentzen.Part2
theorem mem1_center {α : Type} {Γ Δ : List α} {X : α} :
    X ∈ Γ ++ [X] ++ Δ :=
-- BEGIN PROOF
  List.mem_append_left _ (List.mem_append_right _ (List.Mem.head _))

-- retained: used by LCS.FirstOrder.Equality.Part2, LCS.FirstOrder.Gentzen.Part2
theorem mem1_right {α : Type} {a : α} {Γ Δ : List α} {X : α}
    (h : a ∈ Δ) : a ∈ Γ ++ [X] ++ Δ :=
-- BEGIN PROOF
  List.mem_append_right _ h

-- Decompose membership in Γ ++ [X, Y] ++ Δ
-- retained: used by LCS.FirstOrder.Gentzen.Part2
theorem mem2_cases {α : Type} {a : α} {Γ Δ : List α} {X Y : α}
    (h : a ∈ Γ ++ [X, Y] ++ Δ) : a ∈ Γ ∨ a = X ∨ a = Y ∨ a ∈ Δ := by
-- BEGIN PROOF
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with (h1 | h2 | h3) | h4
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr h4))

-- Construct membership in Γ ++ [X, Y] ++ Δ
-- retained: used by LCS.FirstOrder.Gentzen.Part2
theorem mem2_left {α : Type} {a : α} {Γ Δ : List α} {X Y : α}
    (h : a ∈ Γ) : a ∈ Γ ++ [X, Y] ++ Δ :=
-- BEGIN PROOF
  List.mem_append_left _ (List.mem_append_left _ h)

-- retained: used by LCS.FirstOrder.Gentzen.Part2
theorem mem2_first {α : Type} {Γ Δ : List α} {X Y : α} :
    X ∈ Γ ++ [X, Y] ++ Δ :=
-- BEGIN PROOF
  List.mem_append_left _ (List.mem_append_right _ (List.Mem.head _))

-- retained: used by LCS.FirstOrder.Gentzen.Part2
theorem mem2_second {α : Type} {Γ Δ : List α} {X Y : α} :
    Y ∈ Γ ++ [X, Y] ++ Δ :=
-- BEGIN PROOF
  List.mem_append_left _ (List.mem_append_right _ (List.Mem.tail _ (List.Mem.head _)))

-- retained: used by LCS.FirstOrder.Gentzen.Part2
theorem mem2_right {α : Type} {a : α} {Γ Δ : List α} {X Y : α}
    (h : a ∈ Δ) : a ∈ Γ ++ [X, Y] ++ Δ :=
-- BEGIN PROOF
  List.mem_append_right _ h

-- Decompose/construct membership in Γ ++ Δ (no middle)
-- retained: used by LCS.FirstOrder.Equality.Part2, LCS.FirstOrder.Gentzen.Part2
theorem memcat_cases {α : Type} {a : α} {Γ Δ : List α}
    (h : a ∈ Γ ++ Δ) : a ∈ Γ ∨ a ∈ Δ := List.mem_append.mp h

-- retained: used by LCS.FirstOrder.Equality.Part2, LCS.FirstOrder.Gentzen.Part2
theorem memcat_left {α : Type} {a : α} {Γ Δ : List α}
    (h : a ∈ Γ) : a ∈ Γ ++ Δ := List.mem_append_left _ h

-- retained: used by LCS.FirstOrder.Equality.Part2, LCS.FirstOrder.Gentzen.Part2
theorem memcat_right {α : Type} {a : α} {Γ Δ : List α}
    (h : a ∈ Δ) : a ∈ Γ ++ Δ := List.mem_append_right _ h

-- Decompose/construct membership in [X] ++ Γ (cons)
-- retained: used by LCS.FirstOrder.Gentzen.Part2
theorem memcons_cases {α : Type} {a : α} {Γ : List α} {X : α}
    (h : a ∈ [X] ++ Γ) : a = X ∨ a ∈ Γ := by
-- BEGIN PROOF
  simp only [List.singleton_append, List.mem_cons] at h; exact h

-- retained: used by LCS.FirstOrder.Gentzen.Part2
theorem memcons_head {α : Type} {Γ : List α} {X : α} :
    X ∈ [X] ++ Γ := List.mem_cons_self

-- retained: used by LCS.FirstOrder.Gentzen.Part2
theorem memcons_tail {α : Type} {a : α} {Γ : List α} {X : α}
    (h : a ∈ Γ) : a ∈ [X] ++ Γ := List.mem_cons.mpr (Or.inr h)

-- ===================================================================
-- Lemma 5.4.2: Rule falsification preservation
-- ===================================================================

/-- Lemma 5.4.2: For each one-premise rule of G over a language without
equality, the conclusion sequent is falsifiable in M iff the premise is. (Lemma 5.4.2 covers both one-premise and two-premise rules; this is the one-premise primary.) -/
@[blueprint "chap5__lemma_5_4_2" (main := true)]
theorem ruleFalsificationIff1 {L : Language} (hL : L.withoutEquality) (M : Structure L)
    {prem conc : Sequent L} (rule : GentzenStep1 hL prem conc) :
    sequentFalsifiableIn M conc ↔ sequentFalsifiableIn M prem 

/-- Lemma 5.4.2 (companion, two-premise): For each two-premise rule of G
over a language without equality, the conclusion sequent is falsifiable in M iff at least one premise is
falsifiable. -/
@[blueprint "chap5__lemma_5_4_2" (main := true)]
theorem ruleFalsificationIff2 {L : Language} (hL : L.withoutEquality) (M : Structure L)
    {prem1 prem2 conc : Sequent L} (rule : GentzenStep2 hL prem1 prem2 conc) :
    sequentFalsifiableIn M conc ↔
    (sequentFalsifiableIn M prem1 ∨ sequentFalsifiableIn M prem2) 

-- retained: used by LCS.CutElim.LK.Part1
/-- Lemma 5.4.2 (companion): For each one-premise rule of G over a language
without equality, the conclusion sequent is valid iff the premise is valid. -/
theorem ruleValidityIff1 {L : Language} (hL : L.withoutEquality)
    {prem conc : Sequent L} (rule : GentzenStep1 hL prem conc) :
    sequentValid conc ↔ sequentValid prem := by
-- BEGIN PROOF
  rw [sequentValid_iff_not_falsifiable, sequentValid_iff_not_falsifiable]
  exact forall_congr' (fun M => not_congr (ruleFalsificationIff1 hL M rule))

-- retained: used by LCS.CutElim.LK.Part1
/-- Lemma 5.4.2 (companion): For each two-premise rule of G over a language
without equality, the conclusion sequent is valid iff both premises are valid. -/
theorem ruleValidityIff2 {L : Language} (hL : L.withoutEquality)
    {prem1 prem2 conc : Sequent L} (rule : GentzenStep2 hL prem1 prem2 conc) :
    sequentValid conc ↔ (sequentValid prem1 ∧ sequentValid prem2) := by
-- BEGIN PROOF
  rw [sequentValid_iff_not_falsifiable, sequentValid_iff_not_falsifiable,
      sequentValid_iff_not_falsifiable]
  constructor
  · intro h
    refine ⟨fun M hF => h M ?_, fun M hF => h M ?_⟩
    · exact (ruleFalsificationIff2 hL M rule).mpr (Or.inl hF)
    · exact (ruleFalsificationIff2 hL M rule).mpr (Or.inr hF)
  · intro ⟨h1, h2⟩ M hF
    rcases (ruleFalsificationIff2 hL M rule).mp hF with hF1 | hF2
    · exact h1 M hF1
    · exact h2 M hF2

-- ===================================================================
-- Lemma 5.4.3: Soundness of G
-- ===================================================================

-- retained: used by LCS.CutElim.LK.Part1
/-- Lemma 5.4.3 (companion): Every indexed proof tree in G over a language
without equality has a valid conclusion sequent. Proved by induction on the tree, using
`ruleValidityIff1`/`ruleValidityIff2` for the inductive steps. -/
theorem proofTreeValid {L : Language} (hL : L.withoutEquality) {s : Sequent L}
    (t : GProofTree hL s) : sequentValid s := by
-- BEGIN PROOF
  induction t with
  | axiom_ s hax =>
    intro M as hant
    obtain ⟨A, hA_ant, hA_suc⟩ := hax
    exact ⟨A, hA_suc, hant A hA_ant⟩
  | onePremise rule _ ih =>
    exact (ruleValidityIff1 hL rule).mpr ih
  | twoPremise rule _ _ ih1 ih2 =>
    exact (ruleValidityIff2 hL rule).mpr ⟨ih1, ih2⟩

/-- Lemma 5.4.3: Soundness of G over a language without equality. If a
sequent is provable (there exists an indexed GProofTree with that conclusion), then the sequent is valid. -/
@[blueprint "chap5__lemma_5_4_3" (main := true)]
theorem soundnessG {L : Language} (hL : L.withoutEquality) (seq : Sequent L)
    (h : sequentProvable hL seq) : sequentValid seq 

end LCS.FirstOrder.Gentzen
end
