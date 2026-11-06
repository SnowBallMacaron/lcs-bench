import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.PrenexForm
import Attach
import LCS.Herbrand.NNFHauptsatz.Soundness.ProofsStamp

/-! # Herbrand.NNFHauptsatz.Soundness
    Formalization of Chapter 7, Section 4.2: Soundness of G2nnf.

    Covers Lemma 7.4.1 (soundness of the system G2nnf).

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.NNFHauptsatz.Soundness

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SyntaxN.Variables
open LCS.Herbrand.NNFHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.Herbrand.PrenexForm
open LCS.FirstOrder.SemanticsN.Substitution

-- ===================================================================
-- Lemma 7.4.1 (companion def): setSequentValid
-- ===================================================================

/-- Lemma 7.4.1 (companion def): A finset-based sequent (Gamma, Delta) is valid iff for every structure M and every assignment s, if all formulae in Gamma are satisfied then some formula in Delta is satisfied. This lifts the list-based sequent validity to the finset-based representation used by G2nnf, matching the finiteness requirement of Def 6.4.2 (inherited by Def 7.4.3). -/
@[blueprint "chap7__lemma_7_4_1"]
def setSequentValid {L : Language}
    (Gamma Delta : LCS.Finset (FormulaN L)) : Prop :=
  ∀ (M : Structure L) (s : Assignment M),
    (∀ A, Membership.mem Gamma A → formulaEvalN M A s) →
    (∃ B, Membership.mem Delta B ∧ formulaEvalN M B s)

-- ===================================================================
-- Lemma 7.4.1 (companion def): setSequentFalsifiableIn
-- ===================================================================

/-- Lemma 7.4.1 (companion def): A finset-based sequent (Gamma, Delta) is falsifiable in structure M iff there exists an assignment s such that all formulae in Gamma are satisfied and all formulae in Delta are falsified. This is the contrapositive of finset-based sequent validity restricted to a particular structure. -/
def setSequentFalsifiableIn {L : Language}
    (M : Structure L)
    (Gamma Delta : LCS.Finset (FormulaN L)) : Prop :=
  ∃ (s : Assignment M),
    (∀ A, Membership.mem Gamma A → formulaEvalN M A s) ∧
    (∀ B, Membership.mem Delta B → ¬ formulaEvalN M B s)

-- ===================================================================
-- Helper: maxQuantSub elements are quantifiers
-- ===================================================================



-- ===================================================================
-- Helper: replaceMaxQuantSubCore is identity when B not in QF(A)
-- ===================================================================



-- ===================================================================
-- Lemma 7.4.1 (helper): satisfaction_preserved_subformula_subst
-- ===================================================================



-- ===================================================================
-- Lemma 7.4.1 (helper): forall_left_soundness
-- ===================================================================



-- ===================================================================
-- Helper: universal falsification for replace (for eigenvariable rules)
-- ===================================================================



-- ===================================================================
-- Helper: when all x B is universally true, replacing it preserves
-- falsification (used for the disj case of forall_right_soundness)
-- ===================================================================



-- ===================================================================
-- Lemma 7.4.1 (helper): forall_right_soundness
-- ===================================================================



-- ===================================================================
-- Lemma 7.4.1 (helper): exists_right_soundness
-- ===================================================================



-- ===================================================================
-- Helper: existential satisfaction for replace (for eigenvariable rules)
-- ===================================================================



-- ===================================================================
-- Helper: when ex x B is false, replacing it preserves satisfaction
-- ===================================================================



-- ===================================================================
-- Lemma 7.4.1 (helper): exists_left_soundness
-- ===================================================================



-- ===================================================================
-- Lemma 7.4.1 (helper): g2nnf_rule_falsification_preservation
-- ===================================================================

/-- Falsification preservation for the shared contextual rule carrier. -/
theorem g2nnf_core_rule_falsification_preservation
    {L : Language} [DecidableEq (FormulaN L)]
    (M : Structure L) (rule : G2nnfRuleCore L)
    (hSC : G2nnfRuleCore.SideConditions rule)
    (hFals : setSequentFalsifiableIn M
      (G2nnfRuleCore.conclusion rule).1
      (G2nnfRuleCore.conclusion rule).2) :
    ∃ prem ∈ G2nnfRuleCore.premises rule,
      setSequentFalsifiableIn M prem.1 prem.2 := by
  -- REPAIR(T7-06): proof pending
  sorry

/-- Lemma 7.4.1 (companion theorem): For each G2nnf inference rule satisfying
its side conditions, if the conclusion sequent is falsifiable in structure M,
then at least one premise sequent is falsifiable in M.  Quantifier rules carry
their exact selected maximal occurrence and its quantifier shape as constructor
data; their remaining side conditions enforce free-for and eigenvariable
freshness. -/
theorem g2nnf_rule_falsification_preservation
    {L : Language} (hL : L.withoutEquality) [DecidableEq (FormulaN L)]
    (M : Structure L) (rule : G2nnfRule L hL)
    (hSC : G2nnfRule.SideConditions rule)
    (hFals : setSequentFalsifiableIn M
      (G2nnfRule.conclusion rule).1
      (G2nnfRule.conclusion rule).2) :
    ∃ prem ∈ G2nnfRule.premises rule,
      setSequentFalsifiableIn M prem.1 prem.2 :=
  g2nnf_core_rule_falsification_preservation M rule.val hSC hFals

-- ===================================================================
-- Lemma 7.4.1 (rule-level step): g2nnf_soundness
-- ===================================================================



-- ===================================================================
-- List helpers for premise destructuring (used by g2nnf_tree_soundness)
-- ===================================================================

/-- In a list of length zero, no element is a member. -/
theorem list_len_zero_not_mem {α : Type u} (l : List α) (h : l.length = 0) (x : α) :
    ¬ x ∈ l := by
-- BEGIN PROOF
  cases l with
  | nil => intro hm; exact absurd hm List.not_mem_nil
  | cons a t => simp at h

/-- In a list of length one, membership implies equality with the
zeroth element. -/
theorem list_len_one_eq_zero {α : Type u} (l : List α) (h : l.length = 1) (x : α)
    (hx : x ∈ l) : x = l[0]'(by omega) := by
-- BEGIN PROOF
  cases l with
  | nil => simp at h
  | cons a t =>
    cases t with
    | nil =>
      simp at hx; simp; exact hx
    | cons b t' => simp at h

/-- In a list of length two, membership implies equality with element
0 or element 1. -/
theorem list_len_two_eq_zero_or_one {α : Type u} (l : List α) (h : l.length = 2) (x : α)
    (hx : x ∈ l) : x = l[0]'(by omega) ∨ x = l[1]'(by omega) := by
-- BEGIN PROOF
  cases l with
  | nil => simp at h
  | cons a t =>
    cases t with
    | nil => simp at h
    | cons b t' =>
      cases t' with
      | nil =>
        simp at hx
        rcases hx with hxa | hxb
        · exact Or.inl (by simp; exact hxa)
        · exact Or.inr (by simp; exact hxb)
      | cons _ _ => simp at h

-- ===================================================================
-- Lemma 7.4.1 (tree level): g2nnf_tree_soundness
-- ===================================================================

/-- Lemma 7.4.1 (companion tree level): The system G2nnf is sound — every conclusion sequent reachable by a G2nnf proof tree is valid. Stated as "not falsifiable in any structure M" for any (Γ, Δ) with a `G2nnfProofTree hL Γ Δ`. Proved by structural induction on the proof tree using the rule-level step `g2nnf_rule_falsification_preservation` at each node: if the conclusion were falsifiable, preservation exhibits a falsifiable premise, and the inductive hypothesis on the subtree indexed by that premise gives a contradiction. The axiom case has no premises, so preservation produces the required contradiction from the empty premise list. This is the form of Def 7.4.3-compatible soundness claimed in §7.4.2 of the textbook. -/
theorem g2nnf_tree_soundness {L : Language} (hL : L.withoutEquality) [DecidableEq (FormulaN L)]
    (M : Structure L) :
    {Gamma Delta : LCS.Finset (FormulaN L)} → (T : G2nnfProofTree hL Gamma Delta) →
    ¬ setSequentFalsifiableIn M Gamma Delta := by
-- BEGIN PROOF
  intro Gamma Delta T
  induction T with
  | leaf _ _ h _ _ => exact h.elim
  | extraAxiom _ _ h _ _ => exact h.elim
  | axiom_ rule hAdmit hAxiom hSC =>
    intro hFals
    obtain ⟨prem, hPremIn, _⟩ :=
      g2nnf_rule_falsification_preservation hL M ⟨rule, hAdmit⟩ hSC hFals
    exact list_len_zero_not_mem _ hAxiom prem hPremIn
  | onePremise rule hAdmit hPrem hSC sub ih =>
    intro hFals
    obtain ⟨prem, hPremIn, hPremFals⟩ :=
      g2nnf_rule_falsification_preservation hL M ⟨rule, hAdmit⟩ hSC hFals
    have hPrem0 := list_len_one_eq_zero _ hPrem prem hPremIn
    rw [hPrem0] at hPremFals
    exact ih hPremFals
  | twoPremise rule hAdmit hPrem hSC sub1 sub2 ih1 ih2 =>
    intro hFals
    obtain ⟨prem, hPremIn, hPremFals⟩ :=
      g2nnf_rule_falsification_preservation hL M ⟨rule, hAdmit⟩ hSC hFals
    rcases list_len_two_eq_zero_or_one _ hPrem prem hPremIn with h1 | h2
    · rw [h1] at hPremFals
      exact ih1 hPremFals
    · rw [h2] at hPremFals
      exact ih2 hPremFals

-- ===================================================================
-- Lemma 7.4.1 (corollary): g2nnf_provable_implies_valid
-- ===================================================================

/-- Lemma 7.4.1: The system G2nnf is sound — if a sequent `(Γ, Δ)` is provable in G2nnf (i.e. there exists a `G2nnfProofTree hL Γ Δ`), then `(Γ, Δ)` is valid. Immediate corollary of `g2nnf_tree_soundness` by eliminating the `Nonempty` witness: any model / assignment that falsifies the sequent would contradict tree-level soundness. -/
@[blueprint "chap7__lemma_7_4_1" (main := true)]
theorem g2nnf_provable_implies_valid {L : Language} (hL : L.withoutEquality) [DecidableEq (FormulaN L)]
    (Gamma Delta : LCS.Finset (FormulaN L)) :
    g2nnfProvable hL Gamma Delta → setSequentValid Gamma Delta 

end LCS.Herbrand.NNFHauptsatz.Soundness
