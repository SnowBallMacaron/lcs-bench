import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.CutElim.Hauptsatz
import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.Semantics.Subformulae
import Attach
import LCS.CutElim.Hauptsatz.Completeness.ProofsStamp

/-! # CutElim.Hauptsatz.Completeness
    Formalization of Chapter 6, Section 6.4.3.
    Completeness of G1nnf.
    Source: Logic for Computer Science, Gallier 2015
-/

-- ===================================================================
-- Lemma 6.4.2 (helper): FormulaN.isLiteral
-- ===================================================================

namespace LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.Basic

namespace FormulaN

end FormulaN

end LCS.FirstOrder.SyntaxN

-- ===================================================================
-- Lemma 6.4.2 (required def): G1nnfSequent.isValid
-- ===================================================================

namespace LCS.CutElim.Hauptsatz

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN

namespace G1nnfSequent

/-- Lemma 6.4.2 (required def): A G1nnf-sequent Gamma -> Delta is
valid iff for every L-structure M and assignment sigma, if all A in
Gamma are satisfied under (M, sigma), then some B in Delta is
satisfied under (M, sigma). Reuses the existing satisfaction
relation formulaEvalN from FirstOrder.Semantics. -/
@[blueprint "chap6__lemma_6_4_2"]
def isValid {L : Language} {hNoEq : L.withoutEquality}
    (s : G1nnfSequent L hNoEq) : Prop :=
  ∀ (M : Structure L) (σ : Assignment M),
    (∀ A ∈ s.ante, formulaEvalN M A σ) →
    (∃ B ∈ s.succ, formulaEvalN M B σ)

end G1nnfSequent

end LCS.CutElim.Hauptsatz

-- ===================================================================
-- Main completeness namespace
-- ===================================================================

namespace LCS.CutElim.Hauptsatz.Completeness

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.CutElim.Hauptsatz
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Semantics.Subformulae

-- ===================================================================
-- Lemma 6.4.2 (required def): G1nnfProvable
-- ===================================================================

/-- Lemma 6.4.2 (helper): Set-level derivability for G1nnf sequents.
The inference rules of G1nnf operate directly on sets (matching the
textbook's use of finite sets), avoiding the list-position management
needed by the list-based proof tree representation. Each constructor
corresponds to a G1nnf inference rule: axiom rules for shared or
complementary atomic/neg-atomic formulas, the cut rule, propositional
decomposition rules (conjunction left/right, disjunction left/right),
and quantifier rules (universal/existential left/right). The cut
constructor records that its cut formula is in NNF, as required by the
indexed G1nnf rule invariant. The premises use set union to add the
decomposed sub-formula while keeping the original context, reflecting
implicit contraction in set-based sequents. There is no explicit
weakening constructor: any admissible weakening must preserve the
eigenvariable side conditions stored by the quantifier rules. -/
inductive G1nnfSetDerivable {L : Language} :
    Set (FormulaN L) → Set (FormulaN L) → Prop where
  /-- Axiom (positive atomic): A ∈ S and A ∈ T where A is atomic -/
  | axiomPos (A : FormulaN L) (hAtom : A.isAtomic = true) (S T : Set (FormulaN L))
      (hS : A ∈ S) (hT : A ∈ T) : G1nnfSetDerivable S T
  /-- Axiom (negative atomic): neg A ∈ S and neg A ∈ T where A is atomic -/
  | axiomNeg (A : FormulaN L) (hAtom : A.isAtomic = true) (S T : Set (FormulaN L))
      (hS : FormulaN.neg A ∈ S) (hT : FormulaN.neg A ∈ T) : G1nnfSetDerivable S T
  /-- Axiom (complementary left): A and neg A both in S, A is atomic -/
  | axiomCompL (A : FormulaN L) (hAtom : A.isAtomic = true) (S T : Set (FormulaN L))
      (hA : A ∈ S) (hNA : FormulaN.neg A ∈ S) : G1nnfSetDerivable S T
  /-- Axiom (complementary right): A and neg A both in T, A is atomic -/
  | axiomCompR (A : FormulaN L) (hAtom : A.isAtomic = true) (S T : Set (FormulaN L))
      (hA : A ∈ T) (hNA : FormulaN.neg A ∈ T) : G1nnfSetDerivable S T
  /-- Cut rule: from S → T ∪ {A} and {A} ∪ S → T infer S → T -/
  | cut (A : FormulaN L) (S T : Set (FormulaN L))
      (hNNF : A.isNNF)
      (h1 : G1nnfSetDerivable S (fun x => x ∈ T ∨ x = A))
      (h2 : G1nnfSetDerivable (fun x => x = A ∨ x ∈ S) T) :
      G1nnfSetDerivable S T
  /-- Conjunction right: from S → T ∪ {A} and S → T ∪ {B}
      infer S → T ∪ {conj A B}. The principal formula conj A B is
      introduced in the conclusion; T is the context without it. -/
  | conjR (A B : FormulaN L) (S T : Set (FormulaN L))
      (h1 : G1nnfSetDerivable S (fun x => x ∈ T ∨ x = A))
      (h2 : G1nnfSetDerivable S (fun x => x ∈ T ∨ x = B)) :
      G1nnfSetDerivable S (fun x => x ∈ T ∨ x = FormulaN.conj A B)
  /-- Conjunction left (variant 1): from {A} ∪ S → T
      infer {conj A B} ∪ S → T. -/
  | conjL1 (A B : FormulaN L) (S T : Set (FormulaN L))
      (h : G1nnfSetDerivable (fun x => x = A ∨ x ∈ S) T) :
      G1nnfSetDerivable (fun x => x = FormulaN.conj A B ∨ x ∈ S) T
  /-- Conjunction left (variant 2): from {B} ∪ S → T
      infer {conj A B} ∪ S → T. -/
  | conjL2 (A B : FormulaN L) (S T : Set (FormulaN L))
      (h : G1nnfSetDerivable (fun x => x = B ∨ x ∈ S) T) :
      G1nnfSetDerivable (fun x => x = FormulaN.conj A B ∨ x ∈ S) T
  /-- Disjunction left: from {A} ∪ S → T and {B} ∪ S → T
      infer {disj A B} ∪ S → T. -/
  | disjL (A B : FormulaN L) (S T : Set (FormulaN L))
      (h1 : G1nnfSetDerivable (fun x => x = A ∨ x ∈ S) T)
      (h2 : G1nnfSetDerivable (fun x => x = B ∨ x ∈ S) T) :
      G1nnfSetDerivable (fun x => x = FormulaN.disj A B ∨ x ∈ S) T
  /-- Disjunction right (variant 1): from S → T ∪ {A}
      infer S → T ∪ {disj A B}. -/
  | disjR1 (A B : FormulaN L) (S T : Set (FormulaN L))
      (h : G1nnfSetDerivable S (fun x => x ∈ T ∨ x = A)) :
      G1nnfSetDerivable S (fun x => x ∈ T ∨ x = FormulaN.disj A B)
  /-- Disjunction right (variant 2): from S → T ∪ {B}
      infer S → T ∪ {disj A B}. -/
  | disjR2 (A B : FormulaN L) (S T : Set (FormulaN L))
      (h : G1nnfSetDerivable S (fun x => x ∈ T ∨ x = B)) :
      G1nnfSetDerivable S (fun x => x ∈ T ∨ x = FormulaN.disj A B)
  /-- Universal left: from {A[t/x]} ∪ S → T infer {all x A} ∪ S → T,
      where t is free for x in A (textbook Def 6.4.2 side condition). -/
  | allL (x : Nat) (A : FormulaN L) (t : Term L) (S T : Set (FormulaN L))
      (hFreeFor : LCS.FirstOrder.SyntaxN.Substitution.isFreeForN t x A)
      (h : G1nnfSetDerivable (fun f => f = Substitution.formulaSubstN A t x ∨ f ∈ S) T) :
      G1nnfSetDerivable (fun f => f = FormulaN.all x A ∨ f ∈ S) T
  /-- Universal right: from S → T ∪ {A[y/x]} infer S → T ∪ {all x A},
      where y is an eigenvariable not free in the lower sequent
      S ∪ (T ∪ {all x A}) (textbook Def 6.4.2 eigenvariable condition),
      and y is free for x in A. -/
  | allR (x : Nat) (A : FormulaN L) (y : Nat) (S T : Set (FormulaN L))
      (hFreeFor : LCS.FirstOrder.SyntaxN.Substitution.isFreeForN (.var y) x A)
      (hFreshS : ∀ F ∈ S, y ∉ LCS.FirstOrder.SyntaxN.Variables.formulaFVN F)
      (hFreshT : ∀ F ∈ T, y ∉ LCS.FirstOrder.SyntaxN.Variables.formulaFVN F)
      (hFreshAll : y ∉ LCS.FirstOrder.SyntaxN.Variables.formulaFVN (FormulaN.all x A))
      (h : G1nnfSetDerivable S (fun f => f ∈ T ∨ f = Substitution.formulaSubstN A (.var y) x)) :
      G1nnfSetDerivable S (fun f => f ∈ T ∨ f = FormulaN.all x A)
  /-- Existential left: from {A[y/x]} ∪ S → T infer {ex x A} ∪ S → T,
      where y is an eigenvariable not free in the lower sequent, and y
      is free for x in A. -/
  | exL (x : Nat) (A : FormulaN L) (y : Nat) (S T : Set (FormulaN L))
      (hFreeFor : LCS.FirstOrder.SyntaxN.Substitution.isFreeForN (.var y) x A)
      (hFreshS : ∀ F ∈ S, y ∉ LCS.FirstOrder.SyntaxN.Variables.formulaFVN F)
      (hFreshT : ∀ F ∈ T, y ∉ LCS.FirstOrder.SyntaxN.Variables.formulaFVN F)
      (hFreshEx : y ∉ LCS.FirstOrder.SyntaxN.Variables.formulaFVN (FormulaN.ex x A))
      (h : G1nnfSetDerivable (fun f => f = Substitution.formulaSubstN A (.var y) x ∨ f ∈ S) T) :
      G1nnfSetDerivable (fun f => f = FormulaN.ex x A ∨ f ∈ S) T
  /-- Existential right: from S → T ∪ {A[t/x]} infer S → T ∪ {ex x A},
      where t is free for x in A. -/
  | exR (x : Nat) (A : FormulaN L) (t : Term L) (S T : Set (FormulaN L))
      (hFreeFor : LCS.FirstOrder.SyntaxN.Substitution.isFreeForN t x A)
      (h : G1nnfSetDerivable S (fun f => f ∈ T ∨ f = Substitution.formulaSubstN A t x)) :
      G1nnfSetDerivable S (fun f => f ∈ T ∨ f = FormulaN.ex x A)

-- retained: used by LCS.CutElim.Hauptsatz.FolkToG1nnf, LCS.Herbrand.SHGTheorem.Main.SkolemEquisatisfiability
/-- Lemma 6.4.2 (helper): A G1nnf-sequent is provable if there
exists a set-level derivation using the G1nnf inference rules.
This set-level formulation matches the textbook's use of finite
sets for sequents (Definition 6.4.2), where exchange and contraction
are implicit. -/
def G1nnfProvable {L : Language} {hNoEq : L.withoutEquality}
    (s : G1nnfSequent L hNoEq) : Prop :=
  G1nnfSetDerivable s.ante s.succ

-- ===================================================================
-- §6.4.3 bridge: cut-free LK proof → G1nnf set derivation.
-- Textbook §6.4.3 Lem 6.4.2 proof adapts the Thm 5.5.1 proof to sets.
-- The following theorems assemble that adaptation.
-- ===================================================================

open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.CutElim.LK

-- retained: used by LCS.CutElim.Hauptsatz.FolkToG1nnf, LCS.Herbrand.SHGTheorem.Main.SkolemEquisatisfiability
/-- Set-level completeness helper for G1nnf over a language without equality.
A valid finite NNF sequent has a set-level derivation when no variable free
in any formula of the sequent is bound in any formula of that sequent. -/
theorem g1nnf_completeness {L : Language}
    (hNoEq : L.withoutEquality)
    (s : G1nnfSequent L hNoEq)
    (hValid : s.isValid)
    (hNoFreeBound :
      ∀ x : Nat,
        (∃ A, (A ∈ s.ante ∨ A ∈ s.succ) ∧
          x ∈ LCS.FirstOrder.SyntaxN.Variables.formulaFVN A) →
        (∀ B, (B ∈ s.ante ∨ B ∈ s.succ) →
          x ∉ LCS.FirstOrder.SyntaxN.Variables.formulaBVN B)) :
    G1nnfProvable s := by
  -- REPAIR(T6-22): proof pending
  sorry
end LCS.CutElim.Hauptsatz.Completeness
