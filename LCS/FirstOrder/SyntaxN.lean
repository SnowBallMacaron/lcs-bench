import LCS.Item
import LCS.FirstOrder.Basic
import Attach
import LCS.FirstOrder.SyntaxN.ProofsStamp

/-! # FirstOrder.SyntaxN
    Normalized first-order formulae (FormulaN) for §5.3.8 onwards.

    The textbook (Gallier, §5.3.8) restricts to the connective set
    {∧, ∨, ⊃, ¬, ∀, ∃}, treating (A ≡ B) as abbreviation for
    (A ⊃ B) ∧ (B ⊃ A) and ⊥ as abbreviation for P ∧ ¬P.

    This module defines FormulaN as a SEPARATE inductive type with
    8 constructors (no falsum, no equiv_, no pred0). It imports
    Language and Term from Basic.lean. All §5.4+ code should import
    this module instead of Syntax.lean.
-/

namespace LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.Basic

-- ===================================================================
-- Definition 5.2.3: Normalized first-order formulae (FormulaN)
-- ===================================================================

/-- Definition 5.2.3: Normalized first-order formulae — the subset of FORM_L
using connectives {∧, ∨, ⊃, ¬, ∀, ∃} per the §5.3.8 standing assumption.
Synthetic companion of Def 5.2.3 (Formula). -/
@[blueprint "chap5__definition_5_2_3"]
inductive FormulaN (L : Language) : Type where
  /-- Predicate application: P(t_1,...,t_n) -/
  | predN : (P : L.predSymbols) → (Fin (L.predArity P) → Term L) → FormulaN L
  /-- Equality: t_1 =. t_2. Only available when `L.hasEquality = true`;
      the proof argument makes the constructor uninhabited for
      without-equality languages, faithfully realizing Def 5.2.1's
      "languages obtained by omitting the equality symbol". -/
  | eq_ : L.hasEquality = true → Term L → Term L → FormulaN L
  /-- Negation: ¬A -/
  | neg : FormulaN L → FormulaN L
  /-- Conjunction: A ∧ B -/
  | conj : FormulaN L → FormulaN L → FormulaN L
  /-- Disjunction: A ∨ B -/
  | disj : FormulaN L → FormulaN L → FormulaN L
  /-- Implication: A ⊃ B -/
  | impl : FormulaN L → FormulaN L → FormulaN L
  /-- Universal quantification: ∀x, A -/
  | all : Nat → FormulaN L → FormulaN L
  /-- Existential quantification: ∃x, A -/
  | ex : Nat → FormulaN L → FormulaN L

/-- Definition 5.2.3 (required helper): classical `DecidableEq` for `FormulaN L`,
used by `LCS.Finset.insert`/`erase` on sets of normalized formulae. -/
@[blueprint "chap5__definition_5_2_3"]
noncomputable instance instDecidableEqFormulaN : DecidableEq (FormulaN L) :=
  fun a b => Classical.propDecidable (a = b)

namespace FormulaN

/-- Definition 5.2.3 (companion): §5.3.8 abbreviation — (A ≡ B) is an
abbreviation for (A ⊃ B) ∧ (B ⊃ A). Introduced by the standing
assumption at the END of §5.3.8 ("In the rest of this text, ... (A ≡ B)
will be viewed as an abbreviation for ((A ⊃ B) ∧ (B ⊃ A))"), AFTER
Lemma 5.3.6 which still operates on the general `Formula` grammar that
treats `≡` as a primitive connective. Lemma 5.3.6 formalizations
MUST use `Formula` / `Formula.equiv_`, not `FormulaN.equiv`. -/
@[blueprint "chap5__definition_5_2_3"]
abbrev equiv {L : Language} (A B : FormulaN L) : FormulaN L :=
  FormulaN.conj (FormulaN.impl A B) (FormulaN.impl B A)

/-- Definition 5.2.3 (companion): The §5.3.8 abbreviation for ⊥ is
P ∧ ¬P, with P a fixed predicate symbol of rank zero. -/
@[blueprint "chap5__definition_5_2_3"]
def bot {L : Language} (P : L.predSymbols) (hP : L.predArity P = 0) :
    FormulaN L :=
  let p := FormulaN.predN P (fun i => (hP ▸ i).elim0)
  FormulaN.conj p (FormulaN.neg p)

/-- The contradiction A ∧ ¬A associated with an arbitrary formula A. -/
@[blueprint "chap8__lemma_8_5_1"]
abbrev falsum {L : Language} (A : FormulaN L) : FormulaN L :=
  FormulaN.conj A (FormulaN.neg A)

/-- Definition 5.2.3 (companion): A normalized formula is atomic if it is
a predicate application or an equality. -/
@[blueprint "chap5__definition_5_2_3"]
def isAtomic {L : Language} : FormulaN L → Bool
  | .predN _ _ => true
  | .eq_ _ _ _ => true
  | .neg _ => false
  | .conj _ _ => false
  | .disj _ _ => false
  | .impl _ _ => false
  | .all _ _ => false
  | .ex _ _ => false

end FormulaN

end LCS.FirstOrder.SyntaxN
