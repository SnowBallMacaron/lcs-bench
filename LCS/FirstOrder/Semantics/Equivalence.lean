import LCS.Item
import LCS.Util
import LCS.FirstOrder.SemanticsN
import LCS.FirstOrder.Semantics
import LCS.FirstOrder.Semantics.Subformulae
import Attach
import LCS.FirstOrder.Semantics.Equivalence.ProofsStamp

/-! # FirstOrder.Semantics.Equivalence
    Formalization of Chapter 5, Sections 5.3.8-5.3.9.
    Complete sets of connectives and logical equivalence.
-/

namespace LCS.FirstOrder.Semantics.Equivalence

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.Syntax
open LCS.FirstOrder.SemanticsN
open Classical

-- ===================================================================
-- §5.3.9: Formulae with the truth constant
-- ===================================================================

/-- Definition 5.3.12 (companion): The §5.3.9 formula language obtained
by adjoining primitive ⊤ to the six-connective language of §5.3.8.
Every connective and quantifier accepts formulae containing ⊤. -/
@[blueprint "chap5__definition_5_3_12"]
inductive FormulaT (L : Language) : Type where
  | top : FormulaT L
  | predN : (P : L.predSymbols) → (Fin (L.predArity P) → Term L) → FormulaT L
  | eq_ : L.hasEquality = true → Term L → Term L → FormulaT L
  | neg : FormulaT L → FormulaT L
  | conj : FormulaT L → FormulaT L → FormulaT L
  | disj : FormulaT L → FormulaT L → FormulaT L
  | impl : FormulaT L → FormulaT L → FormulaT L
  | all : Nat → FormulaT L → FormulaT L
  | ex : Nat → FormulaT L → FormulaT L

/-- Definition 5.3.12 (companion): Biconditional in the ⊤-extended
language retains the §5.3.8 abbreviation by two implications. -/
@[blueprint "chap5__definition_5_3_12"]
abbrev FormulaT.equiv {L : Language} (A B : FormulaT L) : FormulaT L :=
  .conj (.impl A B) (.impl B A)

/-- Definition 5.3.12 (companion): Embed normalized formulae in the
⊤-extended language, preserving every constructor. -/
@[blueprint "chap5__definition_5_3_12"]
def FormulaT.ofFormulaN {L : Language} : FormulaN L → FormulaT L
  | .predN P ts => .predN P ts
  | .eq_ hL t u => .eq_ hL t u
  | .neg A => .neg (ofFormulaN A)
  | .conj A B => .conj (ofFormulaN A) (ofFormulaN B)
  | .disj A B => .disj (ofFormulaN A) (ofFormulaN B)
  | .impl A B => .impl (ofFormulaN A) (ofFormulaN B)
  | .all x A => .all x (ofFormulaN A)
  | .ex x A => .ex x (ofFormulaN A)

/-- Definition 5.3.12 (companion): Evaluation in the §5.3.9 language
extends the normalized semantics with ⊤ interpreted as True. -/
@[blueprint "chap5__definition_5_3_12"]
def formulaEvalT {L : Language} (M : Structure L) :
    FormulaT L → Assignment M → Prop
  | .top => fun _ => True
  | .predN P ts => fun s => M.interpPred P (fun i => termEval M s (ts i))
  | .eq_ _ t u => fun s => termEval M s t = termEval M s u
  | .neg A => negM (formulaEvalT M A)
  | .conj A B => andM (formulaEvalT M A) (formulaEvalT M B)
  | .disj A B => orM (formulaEvalT M A) (formulaEvalT M B)
  | .impl A B => implM (formulaEvalT M A) (formulaEvalT M B)
  | .all x A => fun s => ∀ a : M.carrier, formulaEvalT M A (assignUpdate s x a)
  | .ex x A => fun s => ∃ a : M.carrier, formulaEvalT M A (assignUpdate s x a)





/-- Definition 5.3.12 (companion): Validity for ⊤-extended formulae
quantifies over every structure and every assignment. -/
@[blueprint "chap5__definition_5_3_12"]
def universallyValidT {L : Language} (A : FormulaT L) : Prop :=
  ∀ (M : Structure L) (s : Assignment M), formulaEvalT M A s

/-- Definition 5.3.12 (companion): Logical equivalence in the
⊤-extended language is validity of the biconditional. -/
@[blueprint "chap5__definition_5_3_12"]
def foLogEquivT {L : Language} (A B : FormulaT L) : Prop :=
  universallyValidT (FormulaT.equiv A B)

-- ===================================================================
-- Lemma 5.3.7: Equivalence and congruence for ⊤-extended formulae
-- ===================================================================

/-- Lemma 5.3.7 (companion): foLogEquivT is reflexive: A simeq A for all
formulae A. -/
@[blueprint "chap5__definition_5_3_12"]
theorem foLogEquivT_refl {L : Language} (A : FormulaT L) :
    foLogEquivT A A 

/-- Lemma 5.3.7 (companion): foLogEquivT is symmetric: if A simeq B then
B simeq A. -/
@[blueprint "chap5__definition_5_3_12"]
theorem foLogEquivT_symm {L : Language} {A B : FormulaT L}
    (h : foLogEquivT A B) : foLogEquivT B A 

/-- Lemma 5.3.7 (companion): foLogEquivT is transitive: if A simeq B and B simeq C
then A simeq C. -/
@[blueprint "chap5__definition_5_3_12"]
theorem foLogEquivT_trans {L : Language} {A B C : FormulaT L}
    (h1 : foLogEquivT A B) (h2 : foLogEquivT B C) :
    foLogEquivT A C 

/-- Lemma 5.3.7: Congruence for conjunction: if A simeq A' and B simeq B'
then (A wedge B) simeq (A' wedge B'). -/
@[blueprint "chap5__lemma_5_3_8"]
theorem foLogEquivT_conj {L : Language} {A A' B B' : FormulaT L}
    (hA : foLogEquivT A A') (hB : foLogEquivT B B') :
    foLogEquivT (FormulaT.conj A B) (FormulaT.conj A' B') 

/-- Lemma 5.3.7 (companion): Congruence for disjunction: if A simeq A' and
B simeq B' then (A vee B) simeq (A' vee B'). -/
@[blueprint "chap5__lemma_5_3_8"]
theorem foLogEquivT_disj {L : Language} {A A' B B' : FormulaT L}
    (hA : foLogEquivT A A') (hB : foLogEquivT B B') :
    foLogEquivT (FormulaT.disj A B) (FormulaT.disj A' B') 

/-- Lemma 5.3.7 (companion): Congruence for negation: if A simeq A' then
neg A simeq neg A'. -/
@[blueprint "chap5__lemma_5_3_8"]
theorem foLogEquivT_neg {L : Language} {A A' : FormulaT L}
    (h : foLogEquivT A A') :
    foLogEquivT (FormulaT.neg A) (FormulaT.neg A') 

-- ===================================================================
-- Definition 5.3.12: Logical equivalence relation foLogEquivN
-- ===================================================================

/-- Definition 5.3.12: The relation simeq on FORM_L is defined so that for
any two formulae A and B, A simeq B if and only if |= (A equiv B). We say that A and B are logically equivalent. (Lemma 5.3.7 below establishes that simeq is a congruence — compatible with all connectives and quantifiers.) -/
@[blueprint "chap5__definition_5_3_12" (main := true)]
def foLogEquivN {L : Language} (A B : FormulaN L) : Prop :=
  universallyValidN (FormulaN.equiv A B)

-- ===================================================================
-- Lemma 5.3.6: Valid equivalences for connective interdependence
-- ===================================================================

/-- Lemma 5.3.6(1): (A ≡ B) ≡ ((A ⇒ B) ∧ (B ⇒ A)) is universally valid. -/
@[blueprint "chap5__lemma_5_3_6" (main := true)]
theorem validF_equiv_elimination {L : Language} (A B : Formula L) :
    universallyValid (Formula.equiv_
      (Formula.equiv_ A B)
      (Formula.conj (Formula.impl A B) (Formula.impl B A))) 

/-- Lemma 5.3.6(2): (A ⇒ B) ≡ (¬A ∨ B) is universally valid. -/
@[blueprint "chap5__lemma_5_3_6" (main := true)]
theorem validF_impl_as_disj {L : Language} (A B : Formula L) :
    universallyValid (Formula.equiv_
      (Formula.impl A B)
      (Formula.disj (Formula.neg A) B)) 

/-- Lemma 5.3.6(3): (A ∨ B) ≡ (¬A ⇒ B) is universally valid. -/
@[blueprint "chap5__lemma_5_3_6" (main := true)]
theorem validF_disj_as_impl {L : Language} (A B : Formula L) :
    universallyValid (Formula.equiv_
      (Formula.disj A B)
      (Formula.impl (Formula.neg A) B)) 

/-- Lemma 5.3.6(4): (A ∨ B) ≡ ¬(¬A ∧ ¬B) is universally valid. -/
@[blueprint "chap5__lemma_5_3_6" (main := true)]
theorem validF_disj_as_neg_conj {L : Language} (A B : Formula L) :
    universallyValid (Formula.equiv_
      (Formula.disj A B)
      (Formula.neg (Formula.conj (Formula.neg A) (Formula.neg B)))) 

/-- Lemma 5.3.6(5): (A ∧ B) ≡ ¬(¬A ∨ ¬B) is universally valid. -/
@[blueprint "chap5__lemma_5_3_6" (main := true)]
theorem validF_conj_as_neg_disj {L : Language} (A B : Formula L) :
    universallyValid (Formula.equiv_
      (Formula.conj A B)
      (Formula.neg (Formula.disj (Formula.neg A) (Formula.neg B)))) 

/-- Lemma 5.3.6(6): ¬A ≡ (A ⇒ ⊥) is universally valid. -/
@[blueprint "chap5__lemma_5_3_6" (main := true)]
theorem validF_neg_as_impl_falsum {L : Language} (A : Formula L) :
    universallyValid (Formula.equiv_
      (Formula.neg A)
      (Formula.impl A (Formula.falsum))) 

/-- Lemma 5.3.6(7): ⊥ ≡ (A ∧ ¬A) is universally valid. -/
@[blueprint "chap5__lemma_5_3_6" (main := true)]
theorem validF_falsum_as_contradiction {L : Language} (A : Formula L) :
    universallyValid (Formula.equiv_ Formula.falsum
      (Formula.conj A (Formula.neg A))) 

/-- Lemma 5.3.6(8): ¬∀x A ≡ ∃x ¬A is universally valid. -/
@[blueprint "chap5__lemma_5_3_6" (main := true)]
theorem validF_neg_all_as_ex_neg {L : Language} (x : Nat)
    (A : Formula L) :
    universallyValid (Formula.equiv_
      (Formula.neg (Formula.all x A))
      (Formula.ex x (Formula.neg A))) 

/-- Lemma 5.3.6(9): ¬∃x A ≡ ∀x ¬A is universally valid. -/
@[blueprint "chap5__lemma_5_3_6" (main := true)]
theorem validF_neg_ex_as_all_neg {L : Language} (x : Nat)
    (A : Formula L) :
    universallyValid (Formula.equiv_
      (Formula.neg (Formula.ex x A))
      (Formula.all x (Formula.neg A))) 

/-- Lemma 5.3.6(10): ∀x A ≡ ¬∃x ¬A is universally valid. -/
@[blueprint "chap5__lemma_5_3_6" (main := true)]
theorem validF_all_as_neg_ex_neg {L : Language} (x : Nat)
    (A : Formula L) :
    universallyValid (Formula.equiv_
      (Formula.all x A)
      (Formula.neg (Formula.ex x (Formula.neg A)))) 

/-- Lemma 5.3.6(11): ∃x A ≡ ¬∀x ¬A is universally valid. -/
@[blueprint "chap5__lemma_5_3_6" (main := true)]
theorem validF_ex_as_neg_all_neg {L : Language} (x : Nat)
    (A : Formula L) :
    universallyValid (Formula.equiv_
      (Formula.ex x A)
      (Formula.neg (Formula.all x (Formula.neg A)))) 


/-- The primitive connectives of full first-order syntax, including ⊥ and
both quantifiers. Predicate and equality atoms contribute no connectives. -/
@[blueprint "chap5__lemma_5_3_6"]
inductive FormulaConnective where
  | bot | neg | conj | disj | impl | equiv | all | ex
  deriving DecidableEq

-- ===================================================================
-- Lemma 5.3.7 (Companions): Equivalence relation and congruence
-- ===================================================================

-- retained: used by LCS.Herbrand.PrenexForm.Part1, LCS.Herbrand.PrenexForm.Part2
/-- Lemma 5.3.7 (companion): foLogEquivN is reflexive: A simeq A for all
formulae A. -/
theorem foLogEquivN_refl {L : Language} (A : FormulaN L) :
    foLogEquivN A A :=
-- BEGIN PROOF
by
  intro M s
  simp [formulaEvalN]

-- retained: used by LCS.Herbrand.PrenexForm.Part1, LCS.Herbrand.PrenexForm.Part2
/-- Lemma 5.3.7 (companion): foLogEquivN is transitive: if A simeq B and B simeq C
then A simeq C. -/
theorem foLogEquivN_trans {L : Language} {A B C : FormulaN L}
    (h1 : foLogEquivN A B) (h2 : foLogEquivN B C) :
    foLogEquivN A C :=
-- BEGIN PROOF
by
  intro M s
  simp only [foLogEquivN, universallyValidN, validInN, formulaEvalN] at *
  obtain ⟨hab, hba⟩ := h1 M s
  obtain ⟨hbc, hcb⟩ := h2 M s
  exact ⟨fun ha => hbc (hab ha), fun hc => hba (hcb hc)⟩

/-- Lemma 5.3.7: Congruence for conjunction: if A simeq A' and B simeq B'
then (A wedge B) simeq (A' wedge B'). (Lemma 5.3.7 bundles congruence for *, neg, forall, exists; this is the conj primary.) -/
@[blueprint "chap5__lemma_5_3_7" (main := true)]
theorem foLogEquivN_conj {L : Language} {A A' B B' : FormulaN L}
    (hA : foLogEquivN A A') (hB : foLogEquivN B B') :
    foLogEquivN (FormulaN.conj A B) (FormulaN.conj A' B') 

/-- Lemma 5.3.7 (companion): Congruence for disjunction: if A simeq A' and
B simeq B' then (A vee B) simeq (A' vee B'). -/
@[blueprint "chap5__lemma_5_3_7" (main := true)]
theorem foLogEquivN_disj {L : Language} {A A' B B' : FormulaN L}
    (hA : foLogEquivN A A') (hB : foLogEquivN B B') :
    foLogEquivN (FormulaN.disj A B) (FormulaN.disj A' B') 

/-- Lemma 5.3.7 (companion): Congruence for implication: if A simeq A' and
B simeq B' then (A supset B) simeq (A' supset B'). -/
@[blueprint "chap5__lemma_5_3_7" (main := true)]
theorem foLogEquivN_impl {L : Language} {A A' B B' : FormulaN L}
    (hA : foLogEquivN A A') (hB : foLogEquivN B B') :
    foLogEquivN (FormulaN.impl A B) (FormulaN.impl A' B') 

/-- Lemma 5.3.7 (companion): Congruence for biconditional: if A simeq A' and
B simeq B' then (A equiv B) simeq (A' equiv B'). -/
@[blueprint "chap5__lemma_5_3_7" (main := true)]
theorem foLogEquivN_equiv {L : Language} {A A' B B' : FormulaN L}
    (hA : foLogEquivN A A') (hB : foLogEquivN B B') :
    foLogEquivN (FormulaN.equiv A B) (FormulaN.equiv A' B') 

/-- Lemma 5.3.7 (companion): Congruence for negation: if A simeq A' then
neg A simeq neg A'. -/
@[blueprint "chap5__lemma_5_3_7" (main := true)]
theorem foLogEquivN_neg {L : Language} {A A' : FormulaN L}
    (h : foLogEquivN A A') :
    foLogEquivN (FormulaN.neg A) (FormulaN.neg A') 

/-- Lemma 5.3.7 (companion): Congruence for universal quantification: if A simeq A'
then forall x A simeq forall x A'. -/
@[blueprint "chap5__lemma_5_3_7" (main := true)]
theorem foLogEquivN_all {L : Language} (x : Nat) {A A' : FormulaN L}
    (h : foLogEquivN A A') :
    foLogEquivN (FormulaN.all x A) (FormulaN.all x A') 

/-- Lemma 5.3.7 (companion): Congruence for existential quantification: if A simeq
A' then exists x A simeq exists x A'. -/
@[blueprint "chap5__lemma_5_3_7" (main := true)]
theorem foLogEquivN_ex {L : Language} (x : Nat) {A A' : FormulaN L}
    (h : foLogEquivN A A') :
    foLogEquivN (FormulaN.ex x A) (FormulaN.ex x A') 

-- ===================================================================
-- §5.3.8: Non-minimality of the six-connective set
-- ===================================================================





-- ===================================================================
-- Lemma 5.3.8: Boolean algebra identities for logical equivalence
-- ===================================================================

/-- Lemma 5.3.8: Associativity of disjunction (Lemma 5.3.8 bundles nineteen
Boolean-algebra identities; this is the disjunction-associativity primary): ((A vee B) vee C) simeq (A vee (B vee C)). -/
@[blueprint "chap5__lemma_5_3_8" (main := true)]
theorem foLogEquivT_disj_assoc {L : Language} (A B C : FormulaT L) :
    foLogEquivT (FormulaT.disj (FormulaT.disj A B) C)
      (FormulaT.disj A (FormulaT.disj B C)) 

/-- Lemma 5.3.8 (companion): Associativity of conjunction:
((A wedge B) wedge C) simeq (A wedge (B wedge C)). -/
@[blueprint "chap5__lemma_5_3_8" (main := true)]
theorem foLogEquivT_conj_assoc {L : Language} (A B C : FormulaT L) :
    foLogEquivT (FormulaT.conj (FormulaT.conj A B) C)
      (FormulaT.conj A (FormulaT.conj B C)) 

/-- Lemma 5.3.8 (companion): Commutativity of disjunction:
(A vee B) simeq (B vee A). -/
@[blueprint "chap5__lemma_5_3_8" (main := true)]
theorem foLogEquivT_disj_comm {L : Language} (A B : FormulaT L) :
    foLogEquivT (FormulaT.disj A B) (FormulaT.disj B A) 

/-- Lemma 5.3.8 (companion): Commutativity of conjunction:
(A wedge B) simeq (B wedge A). -/
@[blueprint "chap5__lemma_5_3_8" (main := true)]
theorem foLogEquivT_conj_comm {L : Language} (A B : FormulaT L) :
    foLogEquivT (FormulaT.conj A B) (FormulaT.conj B A) 

/-- Lemma 5.3.8 (companion): Distributivity of disjunction over conjunction:
(A vee (B wedge C)) simeq ((A vee B) wedge (A vee C)). -/
@[blueprint "chap5__lemma_5_3_8" (main := true)]
theorem foLogEquivT_disj_distrib {L : Language}
    (A B C : FormulaT L) :
    foLogEquivT (FormulaT.disj A (FormulaT.conj B C))
      (FormulaT.conj (FormulaT.disj A B) (FormulaT.disj A C)) 

/-- Lemma 5.3.8 (companion): Distributivity of conjunction over disjunction:
(A wedge (B vee C)) simeq ((A wedge B) vee (A wedge C)). -/
@[blueprint "chap5__lemma_5_3_8" (main := true)]
theorem foLogEquivT_conj_distrib {L : Language}
    (A B C : FormulaT L) :
    foLogEquivT (FormulaT.conj A (FormulaT.disj B C))
      (FormulaT.disj (FormulaT.conj A B) (FormulaT.conj A C)) 

/-- Lemma 5.3.8 (companion): De Morgan's rule for disjunction:
neg(A vee B) simeq (neg A wedge neg B). -/
@[blueprint "chap5__lemma_5_3_8" (main := true)]
theorem foLogEquivT_deMorgan_disj {L : Language}
    (A B : FormulaT L) :
    foLogEquivT (FormulaT.neg (FormulaT.disj A B))
      (FormulaT.conj (FormulaT.neg A) (FormulaT.neg B)) 

/-- Lemma 5.3.8 (companion): De Morgan's rule for conjunction:
neg(A wedge B) simeq (neg A vee neg B). -/
@[blueprint "chap5__lemma_5_3_8" (main := true)]
theorem foLogEquivT_deMorgan_conj {L : Language}
    (A B : FormulaT L) :
    foLogEquivT (FormulaT.neg (FormulaT.conj A B))
      (FormulaT.disj (FormulaT.neg A) (FormulaT.neg B)) 

/-- Lemma 5.3.8 (companion): Idempotency of disjunction:
(A vee A) simeq A. -/
@[blueprint "chap5__lemma_5_3_8" (main := true)]
theorem foLogEquivT_disj_idem {L : Language} (A : FormulaT L) :
    foLogEquivT (FormulaT.disj A A) A 

/-- Lemma 5.3.8 (companion): Idempotency of conjunction:
(A wedge A) simeq A. -/
@[blueprint "chap5__lemma_5_3_8" (main := true)]
theorem foLogEquivT_conj_idem {L : Language} (A : FormulaT L) :
    foLogEquivT (FormulaT.conj A A) A 

/-- Lemma 5.3.8 (companion): Double negation rule:
neg neg A simeq A. -/
@[blueprint "chap5__lemma_5_3_8" (main := true)]
theorem foLogEquivT_double_neg {L : Language} (A : FormulaT L) :
    foLogEquivT (FormulaT.neg (FormulaT.neg A)) A 

/-- Lemma 5.3.8 (companion): Absorption of disjunction:
(A vee (A wedge B)) simeq A. -/
@[blueprint "chap5__lemma_5_3_8" (main := true)]
theorem foLogEquivT_absorb_disj {L : Language}
    (A B : FormulaT L) :
    foLogEquivT (FormulaT.disj A (FormulaT.conj A B)) A 

/-- Lemma 5.3.8 (companion): Absorption of conjunction:
(A wedge (A vee B)) simeq A. -/
@[blueprint "chap5__lemma_5_3_8" (main := true)]
theorem foLogEquivT_absorb_conj {L : Language}
    (A B : FormulaT L) :
    foLogEquivT (FormulaT.conj A (FormulaT.disj A B)) A 

/-- Lemma 5.3.8 (companion): Excluded middle law:
(A ∨ ¬A) ≃ ⊤ for every ⊤-extended formula A. -/
@[blueprint "chap5__lemma_5_3_8" (main := true)]
theorem foLogEquivT_excluded_middle {L : Language}
    (A : FormulaT L) :
    foLogEquivT (FormulaT.disj A (FormulaT.neg A)) FormulaT.top 

/-- Lemma 5.3.8 (companion): (A ∨ ⊥) ≃ A, where ⊥ is the
embedded contradiction on the fixed rank-zero predicate P. -/
@[blueprint "chap5__lemma_5_3_8" (main := true)]
theorem foLogEquivT_disj_identity {L : Language} (A : FormulaT L)
    (P : L.predSymbols) (hP : L.predArity P = 0) :
    foLogEquivT (FormulaT.disj A (FormulaT.ofFormulaN (FormulaN.bot P hP))) A 

/-- Lemma 5.3.8 (companion): (A ∧ ⊥) ≃ ⊥, where ⊥ is the
embedded contradiction on the fixed rank-zero predicate P. -/
@[blueprint "chap5__lemma_5_3_8" (main := true)]
theorem foLogEquivT_conj_annihilation {L : Language} (A : FormulaT L)
    (P : L.predSymbols) (hP : L.predArity P = 0) :
    foLogEquivT (FormulaT.conj A (FormulaT.ofFormulaN (FormulaN.bot P hP)))
      (FormulaT.ofFormulaN (FormulaN.bot P hP)) 

/-- Lemma 5.3.8 (companion): (A ∨ ⊤) ≃ ⊤. -/
@[blueprint "chap5__lemma_5_3_8" (main := true)]
theorem foLogEquivT_disj_top {L : Language} (A : FormulaT L) :
    foLogEquivT (FormulaT.disj A FormulaT.top) FormulaT.top 

/-- Lemma 5.3.8 (companion): (A ∧ ⊤) ≃ A. -/
@[blueprint "chap5__lemma_5_3_8" (main := true)]
theorem foLogEquivT_conj_identity_top {L : Language} (A : FormulaT L) :
    foLogEquivT (FormulaT.conj A FormulaT.top) A 

/-- Lemma 5.3.8 (companion): (A ∧ ¬A) ≃ ⊥, where ⊥ is the
embedded contradiction on the fixed rank-zero predicate P. -/
@[blueprint "chap5__lemma_5_3_8" (main := true)]
theorem foLogEquivT_contradiction {L : Language} (A : FormulaT L)
    (P : L.predSymbols) (hP : L.predArity P = 0) :
    foLogEquivT (FormulaT.conj A (FormulaT.neg A))
      (FormulaT.ofFormulaN (FormulaN.bot P hP)) 





-- retained: used by LCS.Herbrand.PrenexForm.Part1
/-- Commutativity of disjunction for normalized formulae:
(A vee B) simeq (B vee A). -/
theorem foLogEquivN_disj_comm {L : Language} (A B : FormulaN L) :
    foLogEquivN (FormulaN.disj A B) (FormulaN.disj B A) :=
-- BEGIN PROOF
by
  intro M s; simp only [formulaEvalN]; exact ⟨Or.comm.mp, Or.comm.mpr⟩

-- retained: used by LCS.Herbrand.PrenexForm.Part1
/-- Commutativity of conjunction for normalized formulae:
(A wedge B) simeq (B wedge A). -/
theorem foLogEquivN_conj_comm {L : Language} (A B : FormulaN L) :
    foLogEquivN (FormulaN.conj A B) (FormulaN.conj B A) :=
-- BEGIN PROOF
by
  intro M s; simp only [formulaEvalN]; exact ⟨And.comm.mp, And.comm.mpr⟩

-- ===================================================================
-- §5.3.9: The Lindenbaum quotient and its operations
-- ===================================================================

/-- Lemma 5.3.8 (companion): Logical equivalence defines a setoid on
⊤-extended first-order formulae. -/
@[blueprint "chap5__definition_5_3_12"]
def foLogEquivSetoid (L : Language) : Setoid (FormulaT L) where
  r := foLogEquivT
  iseqv := {
    refl := foLogEquivT_refl
    symm := fun h => foLogEquivT_symm h
    trans := fun hAB hBC => foLogEquivT_trans hAB hBC
  }

/-- Lemma 5.3.8 (companion): B_L is the set of ⊤-extended formulae
modulo logical equivalence. -/
@[blueprint "chap5__lemma_5_3_8"]
def BL (L : Language) : Type := Quotient (foLogEquivSetoid L)

namespace BL

/-- Lemma 5.3.8 (companion): The logical-equivalence class [A]. -/
@[blueprint "chap5__lemma_5_3_8"]
def ofFormula {L : Language} (A : FormulaT L) : BL L :=
  Quotient.mk (foLogEquivSetoid L) A



/-- Lemma 5.3.8 (companion): [A] + [B] = [A ∨ B], independent of
representatives by congruence of disjunction. -/
@[blueprint "chap5__lemma_5_3_8"]
def add {L : Language} (a b : BL L) : BL L :=
  Quotient.liftOn₂ a b (fun A B => ofFormula (.disj A B))
    (fun _ _ _ _ hA hB => Quotient.sound (foLogEquivT_disj hA hB))

/-- Lemma 5.3.8 (companion): [A] * [B] = [A ∧ B], independent of
representatives by congruence of conjunction. -/
@[blueprint "chap5__lemma_5_3_8"]
def mul {L : Language} (a b : BL L) : BL L :=
  Quotient.liftOn₂ a b (fun A B => ofFormula (.conj A B))
    (fun _ _ _ _ hA hB => Quotient.sound (foLogEquivT_conj hA hB))

/-- Lemma 5.3.8 (companion): ¬[A] = [¬A], independent of the
representative by congruence of negation. -/
@[blueprint "chap5__lemma_5_3_8"]
def neg {L : Language} (a : BL L) : BL L :=
  Quotient.liftOn a (fun A => ofFormula (.neg A))
    (fun _ _ hA => Quotient.sound (foLogEquivT_neg hA))

/-- Lemma 5.3.8 (companion): Zero is [⊥], with ⊥ the embedded
contradiction on the fixed rank-zero predicate P. -/
@[blueprint "chap5__lemma_5_3_8"]
def zero {L : Language} (P : L.predSymbols) (hP : L.predArity P = 0) : BL L :=
  ofFormula (FormulaT.ofFormulaN (FormulaN.bot P hP))

/-- Lemma 5.3.8 (companion): One is [⊤]. -/
@[blueprint "chap5__lemma_5_3_8"]
def one {L : Language} : BL L := ofFormula .top







/- Proof of Lemma 5.3.8: Quotient induction transfers the nineteen
   formula identities to all classes in B_L. -/

theorem addAssoc {L : Language} (a b c : BL L) : add (add a b) c = add a (add b c) :=
  Quotient.inductionOn₃ a b c (fun A B C => Quotient.sound (foLogEquivT_disj_assoc A B C))

theorem mulAssoc {L : Language} (a b c : BL L) : mul (mul a b) c = mul a (mul b c) :=
  Quotient.inductionOn₃ a b c (fun A B C => Quotient.sound (foLogEquivT_conj_assoc A B C))

theorem addComm {L : Language} (a b : BL L) : add a b = add b a :=
  Quotient.inductionOn₂ a b (fun A B => Quotient.sound (foLogEquivT_disj_comm A B))

theorem mulComm {L : Language} (a b : BL L) : mul a b = mul b a :=
  Quotient.inductionOn₂ a b (fun A B => Quotient.sound (foLogEquivT_conj_comm A B))

theorem addMulDistrib {L : Language} (a b c : BL L) : add a (mul b c) = mul (add a b) (add a c) :=
  Quotient.inductionOn₃ a b c (fun A B C => Quotient.sound (foLogEquivT_disj_distrib A B C))

theorem mulAddDistrib {L : Language} (a b c : BL L) : mul a (add b c) = add (mul a b) (mul a c) :=
  Quotient.inductionOn₃ a b c (fun A B C => Quotient.sound (foLogEquivT_conj_distrib A B C))

theorem negAdd {L : Language} (a b : BL L) : neg (add a b) = mul (neg a) (neg b) :=
  Quotient.inductionOn₂ a b (fun A B => Quotient.sound (foLogEquivT_deMorgan_disj A B))

theorem negMul {L : Language} (a b : BL L) : neg (mul a b) = add (neg a) (neg b) :=
  Quotient.inductionOn₂ a b (fun A B => Quotient.sound (foLogEquivT_deMorgan_conj A B))

theorem addIdempotent {L : Language} (a : BL L) : add a a = a :=
  Quotient.inductionOn a (fun A => Quotient.sound (foLogEquivT_disj_idem A))

theorem mulIdempotent {L : Language} (a : BL L) : mul a a = a :=
  Quotient.inductionOn a (fun A => Quotient.sound (foLogEquivT_conj_idem A))

theorem negNeg {L : Language} (a : BL L) : neg (neg a) = a :=
  Quotient.inductionOn a (fun A => Quotient.sound (foLogEquivT_double_neg A))

theorem addAbsorption {L : Language} (a b : BL L) : add a (mul a b) = a :=
  Quotient.inductionOn₂ a b (fun A B => Quotient.sound (foLogEquivT_absorb_disj A B))

theorem mulAbsorption {L : Language} (a b : BL L) : mul a (add a b) = a :=
  Quotient.inductionOn₂ a b (fun A B => Quotient.sound (foLogEquivT_absorb_conj A B))

theorem addZero {L : Language} (a : BL L)
    (P : L.predSymbols) (hP : L.predArity P = 0) : add a (zero P hP) = a :=
  Quotient.inductionOn a (fun A => Quotient.sound (foLogEquivT_disj_identity A P hP))

theorem mulZero {L : Language} (a : BL L)
    (P : L.predSymbols) (hP : L.predArity P = 0) : mul a (zero P hP) = (zero P hP) :=
  Quotient.inductionOn a (fun A => Quotient.sound (foLogEquivT_conj_annihilation A P hP))

theorem addOne {L : Language} (a : BL L) : add a one = one :=
  Quotient.inductionOn a (fun A => Quotient.sound (foLogEquivT_disj_top A))

theorem mulOne {L : Language} (a : BL L) : mul a one = a :=
  Quotient.inductionOn a (fun A => Quotient.sound (foLogEquivT_conj_identity_top A))

theorem addNeg {L : Language} (a : BL L) : add a (neg a) = one :=
  Quotient.inductionOn a (fun A => Quotient.sound (foLogEquivT_excluded_middle A))

theorem mulNeg {L : Language} (a : BL L)
    (P : L.predSymbols) (hP : L.predArity P = 0) : mul a (neg a) = (zero P hP) :=
  Quotient.inductionOn a (fun A => Quotient.sound (foLogEquivT_contradiction A P hP))

end BL

/-- Lemma 5.3.8 (companion): A Boolean algebra in the source sense has
binary operations + and *, unary negation, and constants 0 and 1,
satisfying all nineteen identities of Lemma 3.3.6. -/
@[blueprint "chap5__lemma_5_3_8"]
structure IsBooleanAlgebra {α : Type} (add mul : α → α → α)
    (neg : α → α) (zero one : α) : Prop where
  addAssoc : ∀ a b c, add (add a b) c = add a (add b c)
  mulAssoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  addComm : ∀ a b, add a b = add b a
  mulComm : ∀ a b, mul a b = mul b a
  addMulDistrib : ∀ a b c, add a (mul b c) = mul (add a b) (add a c)
  mulAddDistrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  negAdd : ∀ a b, neg (add a b) = mul (neg a) (neg b)
  negMul : ∀ a b, neg (mul a b) = add (neg a) (neg b)
  addIdempotent : ∀ a, add a a = a
  mulIdempotent : ∀ a, mul a a = a
  negNeg : ∀ a, neg (neg a) = a
  addAbsorption : ∀ a b, add a (mul a b) = a
  mulAbsorption : ∀ a b, mul a (add a b) = a
  addZero : ∀ a, add a zero = a
  mulZero : ∀ a, mul a zero = zero
  addOne : ∀ a, add a one = one
  mulOne : ∀ a, mul a one = a
  addNeg : ∀ a, add a (neg a) = one
  mulNeg : ∀ a, mul a (neg a) = zero

end LCS.FirstOrder.Semantics.Equivalence
