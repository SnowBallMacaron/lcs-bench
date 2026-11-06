import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics
import LCS.FirstOrder.SemanticsN
import LCS.FirstOrder.SemanticsN.Substitution
import Attach
import LCS.FirstOrder.Gentzen.SystemG.ProofsStamp

/-! # The Gentzen system G (Section 5.4.1)

Definition 5.4.1: first-order sequents over normalized formulae, axioms, and
the inference rules of G for languages without equality.
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
-- Definition 5.4.1: First-order sequent (normalized, FormulaN-based)
-- ===================================================================

/-- Definition 5.6.2 (companion): A sequent is a pair of finite sequences of
formulae. This general form allows any equality flag; G_= and later chapters use it. -/
@[blueprint "chap5__definition_5_6_2"]
structure Sequent (L : Language) where
  antecedent : List (FormulaN L)
  succedent : List (FormulaN L)

/-- Definition 5.4.1: A first-order sequent over a language without equality
is a pair of finite sequences of formulae. -/
@[blueprint "chap5__definition_5_4_1"]
abbrev SequentNoEq (L : Language) (hL : L.withoutEquality) : Type := Sequent L

-- ===================================================================
-- Definition 5.4.1 (companion): Axiom predicate for first-order G
-- ===================================================================

/-- Definition 5.6.2 (companion): A sequent is an axiom if its antecedent and
succedent contain a common formula. This general form allows any equality flag;
G_= and later chapters use it. -/
@[blueprint "chap5__definition_5_6_2"]
def isAxiom {L : Language} (s : Sequent L) : Prop :=
  ∃ A : FormulaN L, A ∈ s.antecedent ∧ A ∈ s.succedent

/-- Definition 5.4.1: A sequent over a language without equality is an axiom
of G if its antecedent and succedent contain a common formula. -/
@[blueprint "chap5__definition_5_4_1" (main := true)]
def isAxiomNoEq {L : Language} (hL : L.withoutEquality)
    (s : SequentNoEq L hL) : Prop :=
  isAxiom s

-- ===================================================================
-- Definition 5.4.2 (indexed types): Constrained Gentzen Steps for G
-- ===================================================================

/-- Definition 5.4.1: One-premise inference rules of G over a language without
equality, indexed by premise and conclusion sequents so that each constructor enforces the structural relationship mandated by the rule. For quantifier rules, side conditions (free-for, fresh variable) are fields of the constructor. -/
@[blueprint "chap5__definition_5_4_1" (main := true)]
inductive GentzenStep1 {L : Language} (hL : L.withoutEquality) : Sequent L → Sequent L → Type where
  | conjLeft (Γ Δ Λ : List (FormulaN L)) (A B : FormulaN L) :
      GentzenStep1 hL (Sequent.mk (Γ ++ [A, B] ++ Δ) Λ)
                    (Sequent.mk (Γ ++ [FormulaN.conj A B] ++ Δ) Λ)
  | disjRight (Γ Δ Λ : List (FormulaN L)) (A B : FormulaN L) :
      GentzenStep1 hL (Sequent.mk Γ (Δ ++ [A, B] ++ Λ))
                    (Sequent.mk Γ (Δ ++ [FormulaN.disj A B] ++ Λ))
  | implRight (Γ Δ Λ : List (FormulaN L)) (A B : FormulaN L) :
      GentzenStep1 hL (Sequent.mk ([A] ++ Γ) ([B] ++ Δ ++ Λ))
                    (Sequent.mk Γ (Δ ++ [FormulaN.impl A B] ++ Λ))
  | negLeft (Γ Δ Λ : List (FormulaN L)) (A : FormulaN L) :
      GentzenStep1 hL (Sequent.mk (Γ ++ Δ) ([A] ++ Λ))
                    (Sequent.mk (Γ ++ [FormulaN.neg A] ++ Δ) Λ)
  | negRight (Γ Δ Λ : List (FormulaN L)) (A : FormulaN L) :
      GentzenStep1 hL (Sequent.mk ([A] ++ Γ) (Δ ++ Λ))
                    (Sequent.mk Γ (Δ ++ [FormulaN.neg A] ++ Λ))
  | allLeft (t : Term L) (Γ Δ Λ : List (FormulaN L))
      (x : Nat) (A : FormulaN L) (hfree : isFreeForN t x A) :
      GentzenStep1 hL
        (Sequent.mk
          (Γ ++ [formulaSubstN A t x, FormulaN.all x A] ++ Δ) Λ)
        (Sequent.mk (Γ ++ [FormulaN.all x A] ++ Δ) Λ)
  | allRight (y : Nat) (Γ Δ Λ : List (FormulaN L))
      (x : Nat) (A : FormulaN L)
      (hfresh : ∀ F ∈ (Sequent.mk Γ (Δ ++ [FormulaN.all x A] ++ Λ)).antecedent ++
        (Sequent.mk Γ (Δ ++ [FormulaN.all x A] ++ Λ)).succedent,
        y ∉ formulaFVN F)
      (hfreeFor : isFreeForN (Term.var y) x A) :
      GentzenStep1 hL
        (Sequent.mk Γ
          (Δ ++ [formulaSubstN A (Term.var y) x] ++ Λ))
        (Sequent.mk Γ (Δ ++ [FormulaN.all x A] ++ Λ))
  | exLeft (y : Nat) (Γ Δ Λ : List (FormulaN L))
      (x : Nat) (A : FormulaN L)
      (hfresh : ∀ F ∈ (Sequent.mk (Γ ++ [FormulaN.ex x A] ++ Δ) Λ).antecedent ++
        (Sequent.mk (Γ ++ [FormulaN.ex x A] ++ Δ) Λ).succedent,
        y ∉ formulaFVN F)
      (hfreeFor : isFreeForN (Term.var y) x A) :
      GentzenStep1 hL
        (Sequent.mk
          (Γ ++ [formulaSubstN A (Term.var y) x] ++ Δ) Λ)
        (Sequent.mk (Γ ++ [FormulaN.ex x A] ++ Δ) Λ)
  | exRight (t : Term L) (Γ Δ Λ : List (FormulaN L))
      (x : Nat) (A : FormulaN L) (hfree : isFreeForN t x A) :
      GentzenStep1 hL
        (Sequent.mk Γ
          (Δ ++ [formulaSubstN A t x, FormulaN.ex x A] ++ Λ))
        (Sequent.mk Γ (Δ ++ [FormulaN.ex x A] ++ Λ))

/-- Definition 5.4.1: Two-premise inference rules of G over a language without
equality, indexed by premise and conclusion sequents. -/
@[blueprint "chap5__definition_5_4_1" (main := true)]
inductive GentzenStep2 {L : Language} (hL : L.withoutEquality) :
    Sequent L → Sequent L → Sequent L → Type where
  | conjRight (Γ Δ Λ : List (FormulaN L)) (A B : FormulaN L) :
      GentzenStep2 hL (Sequent.mk Γ (Δ ++ [A] ++ Λ))
                    (Sequent.mk Γ (Δ ++ [B] ++ Λ))
                    (Sequent.mk Γ (Δ ++ [FormulaN.conj A B] ++ Λ))
  | disjLeft (Γ Δ Λ : List (FormulaN L)) (A B : FormulaN L) :
      GentzenStep2 hL (Sequent.mk (Γ ++ [A] ++ Δ) Λ)
                    (Sequent.mk (Γ ++ [B] ++ Δ) Λ)
                    (Sequent.mk (Γ ++ [FormulaN.disj A B] ++ Δ) Λ)
  | implLeft (Γ Δ Λ : List (FormulaN L)) (A B : FormulaN L) :
      GentzenStep2 hL (Sequent.mk (Γ ++ Δ) ([A] ++ Λ))
                    (Sequent.mk ([B] ++ Γ ++ Δ) Λ)
                    (Sequent.mk (Γ ++ [FormulaN.impl A B] ++ Δ) Λ)

end LCS.FirstOrder.Gentzen
end
