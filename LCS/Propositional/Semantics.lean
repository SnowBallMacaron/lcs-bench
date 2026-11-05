import LCS.Item
import LCS.Util
import LCS.Propositional.Syntax
-- Theorem bodies are attached from the companion Proofs.lean file.
import Attach
import LCS.Propositional.Semantics.ProofsStamp

/-! # Propositional.Semantics
    Formalization of Chapter 3, Sections 3.3.1-3.3.2.
    Defines truth values, valuations, satisfaction, tautologies,
    satisfiability, and semantic consequence.
-/

namespace LCS.Propositional.Semantics

open LCS.Propositional.Syntax

-- ========= Definition 3.3.1: Truth Values (BOOL) =========

/-- Definition 3.3.1: The set of truth values BOOL = {T, F}.
    T represents true and F represents false. BOOL is totally
    ordered with F < T. -/
@[blueprint "chap3__definition_3_3_1" (main := true)]
inductive BoolVal where
  | T : BoolVal
  | F : BoolVal
  deriving DecidableEq, Repr

-- ========= Definition 3.3.1: Total Order on BOOL (companion) =========

namespace BoolVal

/-- Definition 3.3.1 (companion): The total order on BOOL with F < T.
    BoolVal.le defines F <= F, F <= T, T <= T. -/
@[blueprint "chap3__definition_3_3_1" (main := true)]
def le : BoolVal → BoolVal → Prop
  | .F, .F => True
  | .F, .T => True
  | .T, .T => True
  | .T, .F => False

end BoolVal

-- ========= Definition 3.3.2: Truth Functions for Connectives =========

/-- Definition 3.3.2: H_neg — the truth function for negation.
    H_neg(T) = F, H_neg(F) = T. -/
@[blueprint "chap3__definition_3_3_2" (main := true)]
def hNeg : BoolVal → BoolVal
  | .T => .F
  | .F => .T

/-- Definition 3.3.2: H_and — the truth function for conjunction.
    H_and(P, Q) = T iff both P and Q are T. -/
@[blueprint "chap3__definition_3_3_2" (main := true)]
def hAnd : BoolVal → BoolVal → BoolVal
  | .T, .T => .T
  | _, _ => .F

/-- Definition 3.3.2: H_or — the truth function for disjunction.
    H_or(P, Q) = F iff both P and Q are F. -/
@[blueprint "chap3__definition_3_3_2" (main := true)]
def hOr : BoolVal → BoolVal → BoolVal
  | .F, .F => .F
  | _, _ => .T

/-- Definition 3.3.2: H_implies — the truth function for implication.
    H_implies(P, Q) = F iff P = T and Q = F. -/
@[blueprint "chap3__definition_3_3_2" (main := true)]
def hImplies : BoolVal → BoolVal → BoolVal
  | .T, .F => .F
  | _, _ => .T

/-- Definition 3.3.2: H_equiv — the truth function for equivalence.
    H_equiv(P, Q) = T iff P = Q. -/
@[blueprint "chap3__definition_3_3_2" (main := true)]
def hEquiv : BoolVal → BoolVal → BoolVal
  | .T, .T => .T
  | .F, .F => .T
  | _, _ => .F

-- ========= Definition 3.3.3: Valuations and v-hat =========

/-- Definition 3.3.3: A valuation (truth assignment) is a function
    v : PS → BOOL assigning a truth value to every propositional symbol. -/
@[blueprint "chap3__definition_3_3_3" (main := true)]
abbrev Valuation := Nat → BoolVal

/-- Definition 3.3.3: The extension v-hat of a valuation v to all of PROP,
    defined by structural recursion over the formation clauses. -/
@[blueprint "chap3__definition_3_3_3" (main := true)]
def evalExt (v : Valuation) : PropFormula → BoolVal
  | .var n => v n
  | .fls => .F
  | .neg A => hNeg (evalExt v A)
  | .conj A B => hAnd (evalExt v A) (evalExt v B)
  | .disj A B => hOr (evalExt v A) (evalExt v B)
  | .impl A B => hImplies (evalExt v A) (evalExt v B)
  | .equiv_ A B => hEquiv (evalExt v A) (evalExt v B)

/-- Definition 3.4.a (companion): Evaluation of normalized propositional formulae.
    Same as evalExt but on the 5-constructor type — no fls or equiv_ cases needed. -/
@[blueprint "chap3__definition_3_4_a"]
def evalExtN (v : Valuation) : PropFormulaNormalized → BoolVal
  | .var n => v n
  | .neg A => hNeg (evalExtN v A)
  | .conj A B => hAnd (evalExtN v A) (evalExtN v B)
  | .disj A B => hOr (evalExtN v A) (evalExtN v B)
  | .impl A B => hImplies (evalExtN v A) (evalExtN v B)


/-- Definition 3.3.3 (companion): v satisfies A (v ⊨ A) iff v-hat(A) = T.
    Introduced as prose notation in §3.3.1 after the core definition. -/
@[blueprint "chap3__definition_3_3_a" (main := true)]
def satisfies (v : Valuation) (A : PropFormula) : Prop :=
  evalExt v A = BoolVal.T

/-- Definition 3.3.3 (companion): v falsifies A (v ⊭ A) iff v-hat(A) = F.
    Introduced as prose notation in §3.3.1 after the core definition. -/
@[blueprint "chap3__definition_3_3_a" (main := true)]
def falsifies (v : Valuation) (A : PropFormula) : Prop :=
  evalExt v A = BoolVal.F

-- ========= Definition 3.3.4: Validity, Satisfiability, Consequence =========

/-- Definition 3.3.4: A proposition A is valid (a tautology) iff
    v-hat(A) = T for all valuations v. -/
@[blueprint "chap3__definition_3_3_4" (main := true)]
def isValid (A : PropFormula) : Prop :=
  ∀ v : Valuation, evalExt v A = BoolVal.T

/-- Definition 3.3.4: A proposition A is satisfiable iff there exists
    a valuation v such that v-hat(A) = T. -/
@[blueprint "chap3__definition_3_3_4" (main := true)]
def isSatisfiable (A : PropFormula) : Prop :=
  ∃ v : Valuation, evalExt v A = BoolVal.T

/-- Definition 3.3.4: A proposition A is unsatisfiable iff it is not
    satisfiable, i.e., no valuation v satisfies A. -/
@[blueprint "chap3__definition_3_3_4" (main := true)]
def isUnsatisfiable (A : PropFormula) : Prop :=
  ¬ isSatisfiable A

/-- Definition 3.3.4: A is a semantic consequence of Γ (Γ ⊨ A) iff every
    valuation that makes all B ∈ Γ true also makes A true. -/
@[blueprint "chap3__definition_3_3_4" (main := true)]
def semanticConsequence (Gamma : Set PropFormula) (A : PropFormula) : Prop :=
  ∀ v : Valuation, (∀ B : PropFormula, Gamma B → evalExt v B = BoolVal.T) →
    evalExt v A = BoolVal.T

-- ========= Lemma 3.3.1: Helper — PropFormula.vars =========

/-- Lemma 3.3.1 (required helper): The set of propositional symbol
    indices occurring in a formula. Used in the statement of
    evalExt_depends_on_vars. -/
@[blueprint "chap3__lemma_3_3_1"]
def formulaVars : PropFormula → Set Nat
  | .var n => fun m => m = n
  | .fls => fun _ => False
  | .neg A => formulaVars A
  | .conj A B => formulaVars A ∪ formulaVars B
  | .disj A B => formulaVars A ∪ formulaVars B
  | .impl A B => formulaVars A ∪ formulaVars B
  | .equiv_ A B => formulaVars A ∪ formulaVars B

-- ========= Example 3.3.1: Contrapositive Evaluation =========

/-- Example 3.3.1: The contrapositive equivalence formula
    A = ((P ⊃ Q) ≡ (¬Q ⊃ ¬P)). -/
@[blueprint "chap3__example_3_3_1" (main := true)]
def contrapositiveFormula : PropFormula :=
  .equiv_ (.impl (.var 0) (.var 1)) (.impl (.neg (.var 1)) (.neg (.var 0)))

/-- Example 3.3.1: Evaluation of the contrapositive formula under
    v(P) = T, v(Q) = F. The step-by-step computation yields T. -/
@[blueprint "chap3__example_3_3_1" (main := true)]
def contrapositiveEval : BoolVal :=
  evalExt (fun n => if n = 0 then BoolVal.T else BoolVal.F)
    contrapositiveFormula

-- ========= Example 3.3.2: Tautologies, Satisfiability, Consequence =========

/-- Example 3.3.2 (companion): The tautology A => A (identity tautology).
    Named formula for the first tautology listed in Example 3.3.2. -/
@[blueprint "chap3__example_3_3_2"]
def identityTautology (A : PropFormula) : PropFormula :=
  .impl A A

/-- Example 3.3.2 (companion): The tautology neg neg A => A (double negation).
    Named formula for the second tautology listed in Example 3.3.2. -/
@[blueprint "chap3__example_3_3_2"]
def doubleNegTautology (A : PropFormula) : PropFormula :=
  .impl (.neg (.neg A)) A

/-- Example 3.3.2 (companion): The tautology (P => Q) <=> (neg Q => neg P)
    (contrapositive). Named formula for the third tautology in Example 3.3.2. -/
@[blueprint "chap3__example_3_3_2"]
def contrapositiveTautology : PropFormula :=
  .equiv_ (.impl (.var 0) (.var 1)) (.impl (.neg (.var 1)) (.neg (.var 0)))

/-- Example 3.3.2 (companion): The satisfiable formula (P or Q) and (neg P or neg Q).
    Named formula for the satisfiable claim in Example 3.3.2. -/
@[blueprint "chap3__example_3_3_2"]
def satisfiableExample : PropFormula :=
  .conj (.disj (.var 0) (.var 1)) (.disj (.neg (.var 0)) (.neg (.var 1)))

/-- Example 3.3.2 (companion): The unsatisfiable formula
    (neg P or Q) and (neg P or neg Q) and P. Named formula for the
    unsatisfiable claim in Example 3.3.2. -/
@[blueprint "chap3__example_3_3_2"]
def unsatisfiableExample : PropFormula :=
  .conj (.conj (.disj (.neg (.var 0)) (.var 1))
               (.disj (.neg (.var 0)) (.neg (.var 1))))
        (.var 0)

-- ========= Example 3.3.3: Truth Table Computation =========

/-- Example 3.3.3: The 4-row truth table for the contrapositive
    A = ((P ⊃ Q) ≡ (¬Q ⊃ ¬P)), each entry (v(P), v(Q), v-hat(A)). -/
@[blueprint "chap3__example_3_3_3" (main := true)]
def truthTableContrapositive : List (BoolVal × BoolVal × BoolVal) :=
  let formula := contrapositiveFormula
  let mkVal (p q : BoolVal) : Valuation :=
    fun n => if n = 0 then p else if n = 1 then q else BoolVal.F
  [ (BoolVal.T, BoolVal.T, evalExt (mkVal .T .T) formula),
    (BoolVal.T, BoolVal.F, evalExt (mkVal .T .F) formula),
    (BoolVal.F, BoolVal.T, evalExt (mkVal .F .T) formula),
    (BoolVal.F, BoolVal.F, evalExt (mkVal .F .F) formula) ]

-- ========= Lemma 3.3.1: Evaluation Depends Only on Occurring Variables =========

/-- Lemma 3.3.1: For any proposition A, for any two valuations v and v'
    such that v(P) = v'(P) for all propositional symbols P occurring in A,
    evalExt v A = evalExt v' A. This expresses the evaluation locality
    property: v-hat(A) depends only on the values of symbols in A. -/
@[blueprint "chap3__lemma_3_3_1" (main := true)]
theorem evalExt_depends_on_vars (A : PropFormula) (v v' : Valuation)
    (h : ∀ n : Nat, formulaVars A n → v n = v' n) :
    evalExt v A = evalExt v' A

-- ========= Lemma 3.3.2: Tautology iff Negation Unsatisfiable =========

/-- Lemma 3.3.2: A proposition A is a tautology (isValid A) if and only if
    neg A is unsatisfiable (isUnsatisfiable (.neg A)). This relates validity
    to unsatisfiability of the negation via the definition of hNeg. -/
@[blueprint "chap3__lemma_3_3_2" (main := true)]
theorem tautology_iff_neg_unsatisfiable (A : PropFormula) :
    isValid A ↔ isUnsatisfiable (.neg A)

-- ========= Example 3.3.2: Semantic Consequence Theorems =========

/-- Example 3.3.2: Modus ponens as a semantic consequence.
    A, (A => B) models B. -/
@[blueprint "chap3__example_3_3_2" (main := true)]
theorem modusPonensConsequence (A B : PropFormula) :
    semanticConsequence (fun C => C = A ∨ C = .impl A B) B

/-- Example 3.3.2: Conjunction introduction as a semantic consequence.
    A, B models (A and B). -/
@[blueprint "chap3__example_3_3_2" (main := true)]
theorem conjIntroConsequence (A B : PropFormula) :
    semanticConsequence (fun C => C = A ∨ C = B) (.conj A B)

/-- Example 3.3.2: Modus tollens as a semantic consequence.
    (A => B), neg B models neg A. -/
@[blueprint "chap3__example_3_3_2" (main := true)]
theorem modusTollensConsequence (A B : PropFormula) :
    semanticConsequence
      (fun C => C = .impl A B ∨ C = .neg B) (.neg A)

-- ========= Example 3.3.3: Truth Table All True =========

/-- Example 3.3.3: Every row of the truth table for the contrapositive
    equivalence yields T, confirming the formula is a tautology. -/
@[blueprint "chap3__example_3_3_3" (main := true)]
theorem truthTableAllTrue :
    ∀ row ∈ truthTableContrapositive, row.2.2 = BoolVal.T

-- ========= Example 3.3.2: Validity Theorems =========

/-- Example 3.3.2: The identity tautology A => A is valid. -/
@[blueprint "chap3__example_3_3_2" (main := true)]
theorem identityTautology_valid (A : PropFormula) : isValid (identityTautology A)

/-- Example 3.3.2: The double negation tautology neg neg A => A is valid. -/
@[blueprint "chap3__example_3_3_2" (main := true)]
theorem doubleNegTautology_valid (A : PropFormula) : isValid (doubleNegTautology A)

/-- Example 3.3.2: The contrapositive tautology (P => Q) <=> (neg Q => neg P) is valid. -/
@[blueprint "chap3__example_3_3_2" (main := true)]
theorem contrapositiveTautology_valid : isValid contrapositiveTautology

/-- Example 3.3.2: The displayed satisfying assignment has P = F and Q = T. -/
@[blueprint "chap3__example_3_3_2"]
theorem satisfiableExample_assignment :
    evalExt (fun n => if n = 0 then BoolVal.F else if n = 1 then BoolVal.T else BoolVal.F)
      satisfiableExample = BoolVal.T

/-- Example 3.3.2: The satisfiable formula (P or Q) and (neg P or neg Q) is satisfiable. -/
@[blueprint "chap3__example_3_3_2" (main := true)]
theorem satisfiableExample_satisfiable : isSatisfiable satisfiableExample

/-- Example 3.3.2: The unsatisfiable formula (¬P ∨ Q) ∧ (¬P ∨ ¬Q) ∧ P
    is unsatisfiable. -/
@[blueprint "chap3__example_3_3_2" (main := true)]
theorem unsatisfiableExample_unsatisfiable : isUnsatisfiable unsatisfiableExample

end LCS.Propositional.Semantics
