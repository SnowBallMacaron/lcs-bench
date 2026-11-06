import LCS.Item
import LCS.Util
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Semantics.Equivalence
import LCS.FirstOrder.SemanticsN.Substitution
import Attach
import LCS.Herbrand.PrenexForm.DisjunctiveNormalForm.ProofsStamp

/-! # Herbrand.PrenexForm.DisjunctiveNormalForm
    Chapter 7, Section 2.1: Lemma 7.2.2, every quantifier-free formula can be
    transformed into an equivalent formula in disjunctive normal form by the
    listed identities, with the companion conjunctive normal form.

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

end LCS.Herbrand.PrenexForm
