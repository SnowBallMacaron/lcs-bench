import LCS.Item
import LCS.Util
import LCS.Propositional.Semantics
import Attach
import LCS.Propositional.Semantics.TruthFunctions.ProofsStamp

/-! # Propositional.Semantics.TruthFunctions
    Formalization of Chapter 3, Sections 3.3.3-3.3.5.
    Covers truth functions, functional completeness, logical equivalence,
    boolean algebra structure, and NP-completeness discussion.
-/

namespace LCS.Propositional.Semantics.TruthFunctions

open LCS.Propositional.Syntax
open LCS.Propositional.Semantics

-- ========= Definition 3.3.5: Helper — PropFormula.varList =========

/-- Definition 3.3.5 (companion): Collect the distinct propositional symbol
    indices occurring in a formula, returning a list sorted ascending with
    duplicates removed. Sorting ensures the list is a canonical function of
    the set of occurring symbols (two formulas with the same symbol set get
    identical `varList`s and therefore identical truth-function indexings).
    This gives the finite domain BOOL^n for truth functions. -/
@[blueprint "chap3__definition_3_3_5"]
def varList : PropFormula → List Nat
  | .var n => [n]
  | .fls => []
  | .neg A => varList A
  | .conj A B => ((varList A ++ varList B).eraseDups).mergeSort (· ≤ ·)
  | .disj A B => ((varList A ++ varList B).eraseDups).mergeSort (· ≤ ·)
  | .impl A B => ((varList A ++ varList B).eraseDups).mergeSort (· ≤ ·)
  | .equiv_ A B => ((varList A ++ varList B).eraseDups).mergeSort (· ≤ ·)

-- ========= Definition 3.3.5: n-ary Truth Function Type =========

/-- Definition 3.3.5 (companion): An n-ary truth function is a function
    from BOOL^n to BOOL, where BOOL^n is represented as Fin n -> BoolVal. -/
@[blueprint "chap3__definition_3_3_5"]
def TruthFn (n : Nat) : Type :=
  (Fin n → BoolVal) → BoolVal

-- ========= Definition 3.3.5: Truth Function H_A =========

/-- Definition 3.3.5 (required helper): The truth function associated with
    formula A, considered as a function of the arguments in a prescribed
    variable list `vars`. Required by Lemma 3.3.3, which parameterizes
    `H_A` / `H_B` over the combined variable list of `(A ≡ B)` rather
    than over each formula's own `varList`. The textbook's canonical
    `H_A` of Def 3.3.5 is the specialization `truthFunction (varList A) A`,
    which is exposed as `H_A` below. -/
@[blueprint "chap3__definition_3_3_5"]
def truthFunction (vars : List Nat) (A : PropFormula) : TruthFn vars.length :=
  fun assignment =>
    evalExt
      (fun n =>
        match vars.findIdx? (· == n) with
        | some i =>
          if h : i < vars.length then
            assignment ⟨i, h⟩
          else BoolVal.F
        | none => BoolVal.F)
      A

/-- Definition 3.3.5: The truth function `H_A : BOOL^n → BOOL` associated
    with a formula `A`, where `n` is the number of distinct propositional
    symbols occurring in `A`. Given `(a_1, ..., a_n) ∈ BOOL^n`,
    `H_A(a_1, ..., a_n) = v̂(A)` for any valuation `v` with
    `v(P_i) = a_i` at each symbol `P_i` occurring in `A`.

    `H_A A = truthFunction (varList A) A` : the symbols of A are listed
    canonically by `varList`, and `truthFunction` evaluates A under the
    assignment. Two formulas with the same symbol set get domain-equal
    H-functions by construction. -/
@[blueprint "chap3__definition_3_3_5" (main := true)]
def H_A (A : PropFormula) : TruthFn (varList A).length :=
  truthFunction (varList A) A

-- ========= Definition 3.3.6: Logical Equivalence =========

/-- Definition 3.3.6: The logical equivalence relation on PROP.
    A ≃ B if and only if (A ≡ B) is a tautology, i.e., for all
    valuations v, v-hat(A ≡ B) = T. -/
@[blueprint "chap3__definition_3_3_6" (main := true)]
def logEquiv (A B : PropFormula) : Prop :=
  isValid (PropFormula.equiv_ A B)

-- ========= Example 3.3.4: Exclusive OR Formula =========

/-- Example 3.3.4: The proposition (P ∧ ¬Q) ∨ (¬P ∧ Q) defining the
    exclusive OR truth function. -/
@[blueprint "chap3__example_3_3_4" (main := true)]
def xorFormula : PropFormula :=
  PropFormula.disj
    (.conj (.var 0) (.neg (.var 1)))
    (.conj (.neg (.var 0)) (.var 1))

-- ========= Example 3.3.4: H_xor Function =========

/-- Example 3.3.4 (companion): The exclusive OR truth function H_xor.
    H_xor(a, b) = T if and only if a and b have different truth values. -/
@[blueprint "chap3__example_3_3_4"]
def hXor : BoolVal → BoolVal → BoolVal
  | .T, .T => .F
  | .T, .F => .T
  | .F, .T => .T
  | .F, .F => .F

-- ========= Example 3.3.4: xorFormula computes hXor =========

/-- Example 3.3.4 (companion): The formula xorFormula defines the truth
    function hXor. For all truth values a, b, evaluating xorFormula under
    v(P) = a, v(Q) = b yields hXor a b. -/
@[blueprint "chap3__example_3_3_4"]
theorem xorFormula_is_hXor (a b : BoolVal) :
    evalExt
      (fun n => if n = 0 then a else if n = 1 then b else BoolVal.F)
      xorFormula = hXor a b 

-- ========= Theorem 3.3.1 (required def): usesOnlyAndOrNeg =========

/-- Theorem 3.3.1 (required): Recursive predicate that a formula uses
    only the connectives ∧, ∨, and ¬, with propositional symbols and the
    constant ⊥ as leaves. -/
@[blueprint "chap3__theorem_3_3_1"]
def usesOnlyAndOrNeg : PropFormula → Prop
  | .var _ => True
  | .fls => True
  | .neg A => usesOnlyAndOrNeg A
  | .conj A B => usesOnlyAndOrNeg A ∧ usesOnlyAndOrNeg B
  | .disj A B => usesOnlyAndOrNeg A ∧ usesOnlyAndOrNeg B
  | .impl _ _ => False
  | .equiv_ _ _ => False

-- ========= Lemma 3.3.6 (required def): PropFormula.top =========

/-- Lemma 3.3.6 (required): A tautological formula in PROP, encoded as
    (P ∨ ¬P), used to eliminate primitive truth from PROP′. This evaluates
    to T under any valuation. -/
@[blueprint "chap3__lemma_3_3_6"]
def propTop : PropFormula :=
  PropFormula.disj (.var 0) (.neg (.var 0))

-- ========= Theorem 3.3.1: Functional Completeness (helpers) =========































-- ========= Theorem 3.3.1: Functional Completeness =========

/-- Theorem 3.3.1: For every n-ary truth function `f`, there is a
    proposition `A` using only `∧`, `∨`, `¬` such that `f = H_A`.

    Formally: there exists `A : PropFormula` such that
      - `A` uses only `{∧, ∨, ¬}`,
      - the number of distinct propositional symbols in `A` matches `n`
        (via `h : (varList A).length = n`),
      - `f = H_A A` after transporting along `h`.

    Transport is needed because `H_A A : TruthFn (varList A).length` and
    `f : TruthFn n`; the textbook silently identifies these by saying
    "let A be a formula containing exactly n distinct propositional
    symbols". The `h ▸` makes that identification explicit.

    For `n = 0`, the two truth functions are realized by `⊥` and `¬⊥`,
    which have no propositional symbols. For `n ≥ 1`, the Shannon witness
    introduces variables `{0, ..., n-1}`, yielding `(varList A).length = n`
    exactly. -/
@[blueprint "chap3__theorem_3_3_1" (main := true)]
theorem functional_completeness (n : Nat) (f : TruthFn n) :
    ∃ A : PropFormula,
      usesOnlyAndOrNeg A ∧
      ∃ (h : (varList A).length = n), f = h ▸ H_A A 

-- ========= Lemma 3.3.3: Helpers — var-list coverage and truthFunction evaluation =========





-- ========= Lemma 3.3.3: Tautological Equivalence iff Equal Evaluations iff Equal H-Functions =========

/-- Lemma 3.3.3: Let A and B be any two propositions, let {P_1,...,P_n} be
    the set of propositional symbols occurring in (A ≡ B), and let H_A and
    H_B be the truth functions associated with A and B, considered as
    functions of the arguments in {P_1,...,P_n}. The proposition (A ≡ B) is
    a tautology if and only if for all valuations v, v̂(A) = v̂(B), if and
    only if H_A = H_B.

    Formalized as a conjunction of two iffs sharing the tautology claim as
    pivot: `(tautology ↔ pointwise-eq) ∧ (tautology ↔ H-function-eq)`. The
    shared pivot `(A ≡ B)` tautology yields the full three-way equivalence
    by transitivity. The H-functions are taken over the common argument
    set `varList (.equiv_ A B)`, matching the textbook's {P_1,...,P_n}. -/
@[blueprint "chap3__lemma_3_3_3" (main := true)]
theorem tautological_equiv_iff_equal_eval (A B : PropFormula) :
    (isValid (.equiv_ A B) ↔
      ∀ v : Valuation, evalExt v A = evalExt v B) ∧
    (isValid (.equiv_ A B) ↔
      truthFunction (varList (.equiv_ A B)) A
        = truthFunction (varList (.equiv_ A B)) B) 

-- ========= Lemma 3.3.4 (1): Equivalence-Implication Tautology =========

/-- Lemma 3.3.4 (1): (A ≡ B) ≡ ((A ⊃ B) ∧ (B ⊃ A)) is a tautology.
    Equivalence is equivalent to mutual implication. -/
@[blueprint "chap3__lemma_3_3_4" (main := true)]
theorem equiv_impl_tautology (A B : PropFormula) :
    isValid (.equiv_ (.equiv_ A B) (.conj (.impl A B) (.impl B A))) 

-- ========= Lemma 3.3.4 (2): Implication-Disjunction Tautology =========

/-- Lemma 3.3.4 (2): (A ⊃ B) ≡ (¬A ∨ B) is a tautology.
    Implication is equivalent to negation-disjunction. -/
@[blueprint "chap3__lemma_3_3_4" (main := true)]
theorem impl_disj_tautology (A B : PropFormula) :
    isValid (.equiv_ (.impl A B) (.disj (.neg A) B)) 

-- ========= Lemma 3.3.4 (3): Disjunction-Implication Tautology =========

/-- Lemma 3.3.4 (3): (A ∨ B) ≡ (¬A ⊃ B) is a tautology.
    Disjunction is equivalent to negation-implication. -/
@[blueprint "chap3__lemma_3_3_4" (main := true)]
theorem disj_impl_tautology (A B : PropFormula) :
    isValid (.equiv_ (.disj A B) (.impl (.neg A) B)) 

-- ========= Lemma 3.3.4 (4): Disjunction-De Morgan Tautology =========

/-- Lemma 3.3.4 (4): (A ∨ B) ≡ ¬(¬A ∧ ¬B) is a tautology.
    Disjunction expressed via De Morgan's law. -/
@[blueprint "chap3__lemma_3_3_4" (main := true)]
theorem disj_demorgan_tautology (A B : PropFormula) :
    isValid (.equiv_ (.disj A B)
      (.neg (.conj (.neg A) (.neg B)))) 

-- ========= Lemma 3.3.4 (5): Conjunction-De Morgan Tautology =========

/-- Lemma 3.3.4 (5): (A ∧ B) ≡ ¬(¬A ∨ ¬B) is a tautology.
    Conjunction expressed via De Morgan's law. -/
@[blueprint "chap3__lemma_3_3_4" (main := true)]
theorem conj_demorgan_tautology (A B : PropFormula) :
    isValid (.equiv_ (.conj A B)
      (.neg (.disj (.neg A) (.neg B)))) 

-- ========= Lemma 3.3.4 (6): Negation-Falsum Tautology =========

/-- Lemma 3.3.4 (6): ¬A ≡ (A ⊃ ⊥) is a tautology.
    Negation is equivalent to implication to falsum. -/
@[blueprint "chap3__lemma_3_3_4" (main := true)]
theorem neg_falsum_tautology (A : PropFormula) :
    isValid (.equiv_ (.neg A) (.impl A .fls)) 

-- ========= Lemma 3.3.4 (7): Falsum-Contradiction Tautology =========

/-- Lemma 3.3.4 (7): ⊥ ≡ (A ∧ ¬A) is a tautology.
    Falsum is equivalent to a conjunction of a proposition and its negation. -/
@[blueprint "chap3__lemma_3_3_4" (main := true)]
theorem falsum_contradiction_tautology (A : PropFormula) :
    isValid (.equiv_ .fls (.conj A (.neg A))) 

/-- Lemma 3.3.4: The following tautological equivalences hold:
    (1) (A ≡ B) ≡ ((A ⊃ B) ∧ (B ⊃ A))
    (2) (A ⊃ B) ≡ (¬A ∨ B)
    (3) (A ∨ B) ≡ (¬A ⊃ B)
    (4) (A ∨ B) ≡ ¬(¬A ∧ ¬B)
    (5) (A ∧ B) ≡ ¬(¬A ∨ ¬B)
    (6) ¬A ≡ (A ⊃ ⊥)
    (7) ⊥ ≡ (A ∧ ¬A) -/
@[blueprint "chap3__lemma_3_3_4" (main := true)]
theorem lemma_3_3_4 (A B : PropFormula) :
    isValid (.equiv_ (.equiv_ A B) (.conj (.impl A B) (.impl B A))) ∧
    isValid (.equiv_ (.impl A B) (.disj (.neg A) B)) ∧
    isValid (.equiv_ (.disj A B) (.impl (.neg A) B)) ∧
    isValid (.equiv_ (.disj A B) (.neg (.conj (.neg A) (.neg B)))) ∧
    isValid (.equiv_ (.conj A B) (.neg (.disj (.neg A) (.neg B)))) ∧
    isValid (.equiv_ (.neg A) (.impl A .fls)) ∧
    isValid (.equiv_ .fls (.conj A (.neg A))) 

-- ========= Lemma 3.3.5: Congruence of Logical Equivalence =========

/-- Lemma 3.3.5 (negation): If A ≃ A', then ¬A ≃ ¬A'.
    Logical equivalence is preserved under negation. -/
@[blueprint "chap3__lemma_3_3_5" (main := true)]
theorem logEquiv_congruence_neg (A A' : PropFormula)
    (hA : logEquiv A A') :
    logEquiv (.neg A) (.neg A') 

/-- Lemma 3.3.5 (conjunction): If A ≃ A' and B ≃ B', then
    (A ∧ B) ≃ (A' ∧ B'). Logical equivalence is preserved
    under conjunction. -/
@[blueprint "chap3__lemma_3_3_5" (main := true)]
theorem logEquiv_congruence_conj (A A' B B' : PropFormula)
    (hA : logEquiv A A') (hB : logEquiv B B') :
    logEquiv (.conj A B) (.conj A' B') 

/-- Lemma 3.3.5 (disjunction): If A ≃ A' and B ≃ B', then
    (A ∨ B) ≃ (A' ∨ B'). Logical equivalence is preserved
    under disjunction. -/
@[blueprint "chap3__lemma_3_3_5" (main := true)]
theorem logEquiv_congruence_disj (A A' B B' : PropFormula)
    (hA : logEquiv A A') (hB : logEquiv B B') :
    logEquiv (.disj A B) (.disj A' B') 

/-- Lemma 3.3.5 (implication): If A ≃ A' and B ≃ B', then
    (A ⊃ B) ≃ (A' ⊃ B'). Logical equivalence is preserved
    under implication. -/
@[blueprint "chap3__lemma_3_3_5" (main := true)]
theorem logEquiv_congruence_impl (A A' B B' : PropFormula)
    (hA : logEquiv A A') (hB : logEquiv B B') :
    logEquiv (.impl A B) (.impl A' B') 

/-- Lemma 3.3.5 (equivalence): If A ≃ A' and B ≃ B', then
    (A ≡ B) ≃ (A' ≡ B'). Logical equivalence is preserved
    under the equivalence connective. -/
@[blueprint "chap3__lemma_3_3_5" (main := true)]
theorem logEquiv_congruence_equiv (A A' B B' : PropFormula)
    (hA : logEquiv A A') (hB : logEquiv B B') :
    logEquiv (.equiv_ A B) (.equiv_ A' B') 

-- ========= Lemma 3.3.6: Boolean Algebra Laws =========

/-- Lemma 3.3.6 (disjunction associativity):
    ((A ∨ B) ∨ C) ≃ (A ∨ (B ∨ C)). -/
@[blueprint "chap3__lemma_3_3_6"]
theorem logEquiv_disj_assoc (A B C : PropFormula) :
    logEquiv (.disj (.disj A B) C) (.disj A (.disj B C)) 

/-- Lemma 3.3.6 (conjunction associativity):
    ((A ∧ B) ∧ C) ≃ (A ∧ (B ∧ C)). -/
@[blueprint "chap3__lemma_3_3_6"]
theorem logEquiv_conj_assoc (A B C : PropFormula) :
    logEquiv (.conj (.conj A B) C) (.conj A (.conj B C)) 

/-- Lemma 3.3.6 (disjunction commutativity):
    (A ∨ B) ≃ (B ∨ A). -/
@[blueprint "chap3__lemma_3_3_6"]
theorem logEquiv_disj_comm (A B : PropFormula) :
    logEquiv (.disj A B) (.disj B A) 

/-- Lemma 3.3.6 (conjunction commutativity):
    (A ∧ B) ≃ (B ∧ A). -/
@[blueprint "chap3__lemma_3_3_6"]
theorem logEquiv_conj_comm (A B : PropFormula) :
    logEquiv (.conj A B) (.conj B A) 

/-- Lemma 3.3.6 (disjunction-conjunction distributivity):
    (A ∨ (B ∧ C)) ≃ ((A ∨ B) ∧ (A ∨ C)). -/
@[blueprint "chap3__lemma_3_3_6"]
theorem logEquiv_disj_conj_distrib (A B C : PropFormula) :
    logEquiv (.disj A (.conj B C))
      (.conj (.disj A B) (.disj A C)) 

/-- Lemma 3.3.6 (conjunction-disjunction distributivity):
    (A ∧ (B ∨ C)) ≃ ((A ∧ B) ∨ (A ∧ C)). -/
@[blueprint "chap3__lemma_3_3_6"]
theorem logEquiv_conj_disj_distrib (A B C : PropFormula) :
    logEquiv (.conj A (.disj B C))
      (.disj (.conj A B) (.conj A C)) 

/-- Lemma 3.3.6 (De Morgan disjunction):
    ¬(A ∨ B) ≃ (¬A ∧ ¬B). -/
@[blueprint "chap3__lemma_3_3_6"]
theorem logEquiv_demorgan_disj (A B : PropFormula) :
    logEquiv (.neg (.disj A B))
      (.conj (.neg A) (.neg B)) 

/-- Lemma 3.3.6 (De Morgan conjunction):
    ¬(A ∧ B) ≃ (¬A ∨ ¬B). -/
@[blueprint "chap3__lemma_3_3_6"]
theorem logEquiv_demorgan_conj (A B : PropFormula) :
    logEquiv (.neg (.conj A B))
      (.disj (.neg A) (.neg B)) 

/-- Lemma 3.3.6 (disjunction idempotency):
    (A ∨ A) ≃ A. -/
@[blueprint "chap3__lemma_3_3_6"]
theorem logEquiv_disj_idempotent (A : PropFormula) :
    logEquiv (.disj A A) A 

/-- Lemma 3.3.6 (conjunction idempotency):
    (A ∧ A) ≃ A. -/
@[blueprint "chap3__lemma_3_3_6"]
theorem logEquiv_conj_idempotent (A : PropFormula) :
    logEquiv (.conj A A) A 

/-- Lemma 3.3.6 (double negation):
    ¬¬A ≃ A. -/
@[blueprint "chap3__lemma_3_3_6"]
theorem logEquiv_double_neg (A : PropFormula) :
    logEquiv (.neg (.neg A)) A 

/-- Lemma 3.3.6 (disjunction absorption):
    (A ∨ (A ∧ B)) ≃ A. -/
@[blueprint "chap3__lemma_3_3_6"]
theorem logEquiv_disj_absorption (A B : PropFormula) :
    logEquiv (.disj A (.conj A B)) A 

/-- Lemma 3.3.6 (conjunction absorption):
    (A ∧ (A ∨ B)) ≃ A. -/
@[blueprint "chap3__lemma_3_3_6"]
theorem logEquiv_conj_absorption (A B : PropFormula) :
    logEquiv (.conj A (.disj A B)) A 

/-- Lemma 3.3.6 (disjunction identity):
    (A ∨ ⊥) ≃ A. Falsum is the identity for disjunction. -/
@[blueprint "chap3__lemma_3_3_6"]
theorem logEquiv_disj_identity (A : PropFormula) :
    logEquiv (.disj A .fls) A 

/-- Lemma 3.3.6 (conjunction annihilation):
    (A ∧ ⊥) ≃ ⊥. Falsum annihilates conjunction. -/
@[blueprint "chap3__lemma_3_3_6"]
theorem logEquiv_conj_annihilation (A : PropFormula) :
    logEquiv (.conj A .fls) .fls 

/-- Lemma 3.3.6 (disjunction top):
    (A ∨ ⊤) ≃ ⊤. Top annihilates disjunction. -/
@[blueprint "chap3__lemma_3_3_6"]
theorem logEquiv_disj_top (A : PropFormula) :
    logEquiv (.disj A propTop) propTop 

/-- Lemma 3.3.6 (conjunction identity top):
    (A ∧ ⊤) ≃ A. Top is the identity for conjunction. -/
@[blueprint "chap3__lemma_3_3_6"]
theorem logEquiv_conj_identity_top (A : PropFormula) :
    logEquiv (.conj A propTop) A 

/-- Lemma 3.3.6 (excluded middle):
    (A ∨ ¬A) ≃ ⊤. -/
@[blueprint "chap3__lemma_3_3_6"]
theorem logEquiv_excluded_middle (A : PropFormula) :
    logEquiv (.disj A (.neg A)) propTop 

/-- Lemma 3.3.6 (contradiction):
    (A ∧ ¬A) ≃ ⊥. -/
@[blueprint "chap3__lemma_3_3_6"]
theorem logEquiv_contradiction (A : PropFormula) :
    logEquiv (.conj A (.neg A)) .fls 

-- ========= Section 3.3.4: PROP′ with primitive truth =========

/-- The freely generated syntax PROP′ obtained by adjoining the truth constant
    to PROP. Every connective takes extended formulas as its arguments. -/
@[blueprint "chap3__lemma_3_3_6"]
inductive PropFormulaExtended where
  | var : Nat → PropFormulaExtended
  | fls : PropFormulaExtended
  | top : PropFormulaExtended
  | neg : PropFormulaExtended → PropFormulaExtended
  | conj : PropFormulaExtended → PropFormulaExtended → PropFormulaExtended
  | disj : PropFormulaExtended → PropFormulaExtended → PropFormulaExtended
  | impl : PropFormulaExtended → PropFormulaExtended → PropFormulaExtended
  | equiv_ : PropFormulaExtended → PropFormulaExtended → PropFormulaExtended
  deriving DecidableEq, Repr

namespace PropFormulaExtended

/-- Interpretation of PROP′, extending the original clauses by ⊤ ↦ T. -/
@[blueprint "chap3__lemma_3_3_6"]
def eval (v : Valuation) : PropFormulaExtended → BoolVal
  | .var n => v n
  | .fls => .F
  | .top => .T
  | .neg A => hNeg (eval v A)
  | .conj A B => hAnd (eval v A) (eval v B)
  | .disj A B => hOr (eval v A) (eval v B)
  | .impl A B => hImplies (eval v A) (eval v B)
  | .equiv_ A B => hEquiv (eval v A) (eval v B)





/-- Eliminate primitive truth to reuse established laws of the original syntax. -/
def toFormula : PropFormulaExtended → PropFormula
  | .var n => .var n
  | .fls => .fls
  | .top => propTop
  | .neg A => .neg A.toFormula
  | .conj A B => .conj A.toFormula B.toFormula
  | .disj A B => .disj A.toFormula B.toFormula
  | .impl A B => .impl A.toFormula B.toFormula
  | .equiv_ A B => .equiv_ A.toFormula B.toFormula

/-- Truth elimination preserves interpretation at every occurrence of ⊤. -/
theorem evalEqToFormula (v : Valuation) (A : PropFormulaExtended) :
    eval v A = evalExt v A.toFormula := by
  induction A with
  | top => simp only [eval, toFormula, propTop, evalExt]; cases v 0 <;> rfl
  | _ => simp_all [eval, toFormula, evalExt]

/-- Logical equivalence on PROP′ is tautologicity of its equivalence formula. -/
@[blueprint "chap3__lemma_3_3_6"]
def logEquiv (A B : PropFormulaExtended) : Prop :=
  ∀ v : Valuation, eval v (.equiv_ A B) = BoolVal.T



theorem logEquivIffTranslated (A B : PropFormulaExtended) :
    logEquiv A B ↔
      LCS.Propositional.Semantics.TruthFunctions.logEquiv A.toFormula B.toFormula := by
  unfold logEquiv
  simp only [evalEqToFormula]
  rfl

/-- Equivalence of extended formulas is equality under all valuations. -/
@[blueprint "chap3__lemma_3_3_6"]
theorem logEquivIffEqualEval (A B : PropFormulaExtended) :
    logEquiv A B ↔ ∀ v : Valuation, eval v A = eval v B 

@[blueprint "chap3__lemma_3_3_6"]
theorem congruenceNeg (A A' : PropFormulaExtended)
    (hA : logEquiv A A') : logEquiv (.neg A) (.neg A') 

@[blueprint "chap3__lemma_3_3_6"]
theorem congruenceConj (A A' B B' : PropFormulaExtended)
    (hA : logEquiv A A') (hB : logEquiv B B') : logEquiv (.conj A B) (.conj A' B') 

@[blueprint "chap3__lemma_3_3_6"]
theorem congruenceDisj (A A' B B' : PropFormulaExtended)
    (hA : logEquiv A A') (hB : logEquiv B B') : logEquiv (.disj A B) (.disj A' B') 

/-- Lemma 3.3.6 for arbitrary propositions of PROP′. -/
@[blueprint "chap3__lemma_3_3_6" (main := true)]
theorem logEquiv_disj_assoc (A B C : PropFormulaExtended) :
    logEquiv (.disj (.disj A B) C) (.disj A (.disj B C)) 

/-- Lemma 3.3.6 for arbitrary propositions of PROP′. -/
@[blueprint "chap3__lemma_3_3_6" (main := true)]
theorem logEquiv_conj_assoc (A B C : PropFormulaExtended) :
    logEquiv (.conj (.conj A B) C) (.conj A (.conj B C)) 

/-- Lemma 3.3.6 for arbitrary propositions of PROP′. -/
@[blueprint "chap3__lemma_3_3_6" (main := true)]
theorem logEquiv_disj_comm (A B : PropFormulaExtended) :
    logEquiv (.disj A B) (.disj B A) 

/-- Lemma 3.3.6 for arbitrary propositions of PROP′. -/
@[blueprint "chap3__lemma_3_3_6" (main := true)]
theorem logEquiv_conj_comm (A B : PropFormulaExtended) :
    logEquiv (.conj A B) (.conj B A) 

/-- Lemma 3.3.6 for arbitrary propositions of PROP′. -/
@[blueprint "chap3__lemma_3_3_6" (main := true)]
theorem logEquiv_disj_conj_distrib (A B C : PropFormulaExtended) :
    logEquiv (.disj A (.conj B C))
      (.conj (.disj A B) (.disj A C)) 

/-- Lemma 3.3.6 for arbitrary propositions of PROP′. -/
@[blueprint "chap3__lemma_3_3_6" (main := true)]
theorem logEquiv_conj_disj_distrib (A B C : PropFormulaExtended) :
    logEquiv (.conj A (.disj B C))
      (.disj (.conj A B) (.conj A C)) 

/-- Lemma 3.3.6 for arbitrary propositions of PROP′. -/
@[blueprint "chap3__lemma_3_3_6" (main := true)]
theorem logEquiv_demorgan_disj (A B : PropFormulaExtended) :
    logEquiv (.neg (.disj A B))
      (.conj (.neg A) (.neg B)) 

/-- Lemma 3.3.6 for arbitrary propositions of PROP′. -/
@[blueprint "chap3__lemma_3_3_6" (main := true)]
theorem logEquiv_demorgan_conj (A B : PropFormulaExtended) :
    logEquiv (.neg (.conj A B))
      (.disj (.neg A) (.neg B)) 

/-- Lemma 3.3.6 for arbitrary propositions of PROP′. -/
@[blueprint "chap3__lemma_3_3_6" (main := true)]
theorem logEquiv_disj_idempotent (A : PropFormulaExtended) :
    logEquiv (.disj A A) A 

/-- Lemma 3.3.6 for arbitrary propositions of PROP′. -/
@[blueprint "chap3__lemma_3_3_6" (main := true)]
theorem logEquiv_conj_idempotent (A : PropFormulaExtended) :
    logEquiv (.conj A A) A 

/-- Lemma 3.3.6 for arbitrary propositions of PROP′. -/
@[blueprint "chap3__lemma_3_3_6" (main := true)]
theorem logEquiv_double_neg (A : PropFormulaExtended) :
    logEquiv (.neg (.neg A)) A 

/-- Lemma 3.3.6 for arbitrary propositions of PROP′. -/
@[blueprint "chap3__lemma_3_3_6" (main := true)]
theorem logEquiv_disj_absorption (A B : PropFormulaExtended) :
    logEquiv (.disj A (.conj A B)) A 

/-- Lemma 3.3.6 for arbitrary propositions of PROP′. -/
@[blueprint "chap3__lemma_3_3_6" (main := true)]
theorem logEquiv_conj_absorption (A B : PropFormulaExtended) :
    logEquiv (.conj A (.disj A B)) A 

/-- Lemma 3.3.6 for arbitrary propositions of PROP′. -/
@[blueprint "chap3__lemma_3_3_6" (main := true)]
theorem logEquiv_disj_identity (A : PropFormulaExtended) :
    logEquiv (.disj A .fls) A 

/-- Lemma 3.3.6 for arbitrary propositions of PROP′. -/
@[blueprint "chap3__lemma_3_3_6" (main := true)]
theorem logEquiv_conj_annihilation (A : PropFormulaExtended) :
    logEquiv (.conj A .fls) .fls 

/-- Lemma 3.3.6 for arbitrary propositions of PROP′. -/
@[blueprint "chap3__lemma_3_3_6" (main := true)]
theorem logEquiv_disj_top (A : PropFormulaExtended) :
    logEquiv (.disj A .top) .top 

/-- Lemma 3.3.6 for arbitrary propositions of PROP′. -/
@[blueprint "chap3__lemma_3_3_6" (main := true)]
theorem logEquiv_conj_identity_top (A : PropFormulaExtended) :
    logEquiv (.conj A .top) A 

/-- Lemma 3.3.6 for arbitrary propositions of PROP′. -/
@[blueprint "chap3__lemma_3_3_6" (main := true)]
theorem logEquiv_excluded_middle (A : PropFormulaExtended) :
    logEquiv (.disj A (.neg A)) .top 

/-- Lemma 3.3.6 for arbitrary propositions of PROP′. -/
@[blueprint "chap3__lemma_3_3_6" (main := true)]
theorem logEquiv_contradiction (A : PropFormulaExtended) :
    logEquiv (.conj A (.neg A)) .fls 

end PropFormulaExtended

-- ========= Lemma 3.3.6: The quotient Boolean algebra B_PROP =========

/-- Logical equivalence is an equivalence relation on PROP′. -/
@[blueprint "chap3__lemma_3_3_6"]
def logEquivSetoid : Setoid PropFormulaExtended where
  r := PropFormulaExtended.logEquiv
  iseqv := {
    refl := fun A => (PropFormulaExtended.logEquivIffEqualEval A A).mpr (fun _ => rfl)
    symm := fun {A B} h => (PropFormulaExtended.logEquivIffEqualEval B A).mpr
      (fun v => ((PropFormulaExtended.logEquivIffEqualEval A B).mp h v).symm)
    trans := fun {A B C} hAB hBC => (PropFormulaExtended.logEquivIffEqualEval A C).mpr
      (fun v => ((PropFormulaExtended.logEquivIffEqualEval A B).mp hAB v).trans
        ((PropFormulaExtended.logEquivIffEqualEval B C).mp hBC v))
  }

/-- The textbook's B_PROP: propositions of PROP′ modulo logical equivalence. -/
@[blueprint "chap3__lemma_3_3_6"]
def BProp : Type := Quotient logEquivSetoid

namespace BProp

/-- The logical-equivalence class [A] of a proposition A. -/
@[blueprint "chap3__lemma_3_3_6"]
def ofFormula (A : PropFormulaExtended) : BProp := Quotient.mk logEquivSetoid A

/-- [A] + [B] = [A ∨ B], well-defined by congruence of disjunction. -/
@[blueprint "chap3__lemma_3_3_6"]
def add (a b : BProp) : BProp :=
  Quotient.liftOn₂ a b (fun A B => ofFormula (.disj A B))
    (fun A B A' B' hA hB => Quotient.sound (PropFormulaExtended.congruenceDisj A A' B B' hA hB))

/-- [A] * [B] = [A ∧ B], well-defined by congruence of conjunction. -/
@[blueprint "chap3__lemma_3_3_6"]
def mul (a b : BProp) : BProp :=
  Quotient.liftOn₂ a b (fun A B => ofFormula (.conj A B))
    (fun A B A' B' hA hB => Quotient.sound (PropFormulaExtended.congruenceConj A A' B B' hA hB))

/-- ¬[A] = [¬A], well-defined by congruence of negation. -/
@[blueprint "chap3__lemma_3_3_6"]
def neg (a : BProp) : BProp :=
  Quotient.liftOn a (fun A => ofFormula (.neg A))
    (fun A A' hA => Quotient.sound (PropFormulaExtended.congruenceNeg A A' hA))

/-- The Boolean zero is [⊥]. -/
@[blueprint "chap3__lemma_3_3_6"]
def zero : BProp := ofFormula .fls

/-- The Boolean one is [⊤]. -/
@[blueprint "chap3__lemma_3_3_6"]
def one : BProp := ofFormula .top

/- Proof of Lemma 3.3.6: Quotient induction transfers each formula law
   to every equivalence class in B_PROP. -/

end BProp

end LCS.Propositional.Semantics.TruthFunctions
