import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Equality
import LCS.FirstOrder.ManySorted.CongruenceClosure
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.Satisfiability
import Attach
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.DisjunctiveNormalForm.ProofsStamp

section
namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.FirstOrder.ManySorted.Equality
open LCS.FirstOrder.ManySorted.CongruenceClosure
open LCS.Propositional.Semantics
namespace MSFormula

/-- Lemma 10.6.1 (companion): A literal is an atomic formula or the
negation of an atomic formula (Pattern 5: a syntactic predicate on the
§10.2 `MSFormula` type, reusing `MSFormula.isAtomic`). -/
@[blueprint "chap10__lemma_10_6_1"]
def isLiteral {L : MSLanguage} (A : MSFormula L) : Prop :=
  A.isAtomic ∨ (∃ B, A = MSFormula.neg B ∧ B.isAtomic)

end MSFormula

/-- Lemma 10.6.1 (companion): A conjunction of literals — a finite
right-nested conjunction of literals whose satisfiability the reduction
targets. Recurses structurally on the formula: a conjunction `A ∧ B` is
a conjunction of literals iff `A` is a literal and `B` is again a
conjunction of literals; any other formula must itself be a literal. -/
@[blueprint "chap10__lemma_10_6_1"]
def msIsConjunctionOfLiterals {L : MSLanguage} : MSFormula L → Prop
  | MSFormula.conj A B =>
      MSFormula.isLiteral (MSFormula.conj A B) ∨
        (MSFormula.isLiteral A ∧ msIsConjunctionOfLiterals B)
  | A => MSFormula.isLiteral A

/-- Lemma 10.6.1 (companion): A formula is in disjunctive normal form
iff it is a right-nested disjunction `C_1 ∨ … ∨ C_n` of conjuncts, each
conjunct a conjunction of literals — the DNF `B` with `A ≡ B` asserted
valid by Lemma 10.6.1. -/
@[blueprint "chap10__lemma_10_6_1"]
def msIsDNF {L : MSLanguage} : MSFormula L → Prop
  | MSFormula.disj C D =>
      msIsConjunctionOfLiterals (MSFormula.disj C D) ∨
        (msIsConjunctionOfLiterals C ∧ msIsDNF D)
  | B => msIsConjunctionOfLiterals B

/-- Lemma 10.6.1 (companion): `Ci` is one of the top-level disjuncts
`C_1, …, C_n` of a DNF formula `B = C_1 ∨ … ∨ C_n`. Used to state "every
conjunct C_i is unsatisfiable". -/
@[blueprint "chap10__lemma_10_6_1"]
def msIsDisjunctOf {L : MSLanguage} (Ci : MSFormula L) :
    MSFormula L → Prop
  | MSFormula.disj C D =>
      msIsDisjunctOf Ci C ∨ msIsDisjunctOf Ci D
  | B => Ci = B ∧ msIsConjunctionOfLiterals B

/-- Lemma 10.6.1 (companion): The literal `X` occurs as one of the
conjuncts of a conjunction-of-literals `C`. Used to phrase the
no-equality trivial case (C contains some `P t_1…t_n` and its
negation). Recurses structurally on the conjunction tree `C` (container
first, element second). -/
@[blueprint "chap10__lemma_10_6_1"]
def msConjunctContains {L : MSLanguage} :
    MSFormula L → MSFormula L → Prop
  | MSFormula.conj A B, X =>
      MSFormula.conj A B = X ∨
        (msConjunctContains A X ∨ msConjunctContains B X)
  | C, X => C = X

/-- Lemma 10.6.1 (companion): A nonnegated equation `t_i =̇_{s_i} u_i`
between terms of sort `s_i` occurring in the conjunction `C`. -/
@[blueprint "chap10__lemma_10_6_1"]
def msIsPositiveEquation {L : MSLanguage} (A : MSFormula L) : Prop :=
  ∃ (hL : L.hasEquality = true) (s : L.SortType) (t u : MSTerm L s),
    A = MSFormula.eq_ hL s t u

/-- Lemma 10.6.1 (companion): A negation `¬ r_j =̇_{s'_j} v_j` of an
equation between terms of sort `s'_j` occurring in `C`. -/
@[blueprint "chap10__lemma_10_6_1"]
def msIsNegatedEquation {L : MSLanguage} (A : MSFormula L) : Prop :=
  ∃ (hL : L.hasEquality = true) (s : L.SortType) (r v : MSTerm L s),
    A = MSFormula.neg (MSFormula.eq_ hL s r v)

/-- Lemma 10.6.1 (companion): A quantifier-free formula is exactly an
open formula (reuses the §10.2 `MSFormula.isOpen` predicate, Pattern
5). -/
@[blueprint "chap10__lemma_10_6_1"]
def msIsQuantifierFree {L : MSLanguage} (A : MSFormula L) : Prop :=
  MSFormula.isOpen A

/-- Lemma 10.6.1 (companion): The with-equality normal form of a conjunct
`C`: a conjunction of literals every literal of which is an equality or
the negation of an equality — the input shape consumed by Definition
10.6.3. -/
@[blueprint "chap10__lemma_10_6_1"]
def msIsConjunctionOfEquations {L : MSLanguage} (C : MSFormula L) : Prop :=
  msIsConjunctionOfLiterals C ∧
    ∀ X, msConjunctContains C X → MSFormula.isLiteral X →
      (msIsPositiveEquation X ∨ msIsNegatedEquation X)

-- ===================================================================
-- Lemma 10.6.1 (companion): DNF construction and eval combinators
-- ===================================================================

/-- Lemma 10.6.1 (companion): evaluation of a disjunction unfolds to
`hOr` of the component evaluations. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem msFormulaEval_disj {L : MSLanguage} (M : MSStructure L)
    (A B : MSFormula L) (v : MSAssignment M) :
    msFormulaEval M (MSFormula.disj A B) v
      = hOr (msFormulaEval M A v) (msFormulaEval M B v) 

/-- Lemma 10.6.1 (companion): evaluation of a negation unfolds to `hNeg`
of the component evaluation. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem msFormulaEval_neg {L : MSLanguage} (M : MSStructure L)
    (A : MSFormula L) (v : MSAssignment M) :
    msFormulaEval M (MSFormula.neg A) v
      = hNeg (msFormulaEval M A v) 

/-- Lemma 10.6.1 (companion): evaluation of an equivalence unfolds to
`hEquiv` of the component evaluations. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem msFormulaEval_equiv {L : MSLanguage} (M : MSStructure L)
    (A B : MSFormula L) (v : MSAssignment M) :
    msFormulaEval M (MSFormula.equiv_ A B) v
      = hEquiv (msFormulaEval M A v) (msFormulaEval M B v) 

/-- Lemma 10.6.1 (companion): an atomic formula is a literal. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem isLiteral_of_isAtomic {L : MSLanguage} {A : MSFormula L}
    (h : A.isAtomic) : MSFormula.isLiteral A 

/-- Lemma 10.6.1 (companion): a literal is a conjunction of literals. The
literal `A` is never a conjunction (atomic or a negation), so the
`msIsConjunctionOfLiterals` recursion lands on the catch-all clause. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem msIsConjunctionOfLiterals_of_isLiteral {L : MSLanguage}
    {A : MSFormula L} (h : MSFormula.isLiteral A) :
    msIsConjunctionOfLiterals A 

/-- Lemma 10.6.1 (companion): a conjunction of literals is a DNF. A
conjunction of literals is never a top-level disjunction, so the
`msIsDNF` recursion lands on the catch-all clause. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem msIsDNF_of_msIsConjunctionOfLiterals {L : MSLanguage}
    {A : MSFormula L} (h : msIsConjunctionOfLiterals A) : msIsDNF A 

/-- Lemma 10.6.1 (companion): The disjunction combinator on DNF formulae:
prepend the disjuncts of the (right-nested) DNF `B` in front of `D`. The
result is again a DNF and evaluates to `hOr (eval B) (eval D)`. -/
@[blueprint "chap10__lemma_10_6_1"]
def dnfOr {L : MSLanguage} : MSFormula L → MSFormula L → MSFormula L
  | MSFormula.disj C R, D => MSFormula.disj C (dnfOr R D)
  | B, D => MSFormula.disj B D

/-- Lemma 10.6.1 (companion): The conjunction-append combinator on
conjunctions-of-literals: append the literals of the (right-nested)
conjunction `C` in front of `D`. Result evaluates to
`hAnd (eval C) (eval D)`. -/
@[blueprint "chap10__lemma_10_6_1"]
def conjConj {L : MSLanguage} : MSFormula L → MSFormula L → MSFormula L
  | MSFormula.conj l R, D => MSFormula.conj l (conjConj R D)
  | l, D => MSFormula.conj l D

/-- Lemma 10.6.1 (companion): Distribute a single conjunction-of-literals
`C` over the disjuncts of a DNF `D`, producing the DNF `C ∧ D` (i.e.
`(C ∧ D_1) ∨ … ∨ (C ∧ D_n)`). Evaluates to `hAnd (eval C) (eval D)`. -/
@[blueprint "chap10__lemma_10_6_1"]
def distLeft {L : MSLanguage} (C : MSFormula L) : MSFormula L → MSFormula L
  | MSFormula.disj D R => dnfOr (conjConj C D) (distLeft C R)
  | D => conjConj C D

/-- Lemma 10.6.1 (companion): The conjunction combinator on DNF formulae,
distributing `∧` over `∨`: for `B = C_1 ∨ … ∨ C_n` and a DNF `D`, produce
`(C_1 ∧ D) ∨ … ∨ (C_n ∧ D)`. Result is a DNF evaluating to
`hAnd (eval B) (eval D)`. -/
@[blueprint "chap10__lemma_10_6_1"]
def dnfAnd {L : MSLanguage} : MSFormula L → MSFormula L → MSFormula L
  | MSFormula.disj C R, D => dnfOr (distLeft C D) (dnfAnd R D)
  | C, D => distLeft C D

/-- Lemma 10.6.1 (companion): Negate a single literal into a DNF: an
atomic literal `a` becomes `¬a`; a negated atom `¬a` becomes `a` (double
negation). Evaluates to `hNeg (eval l)` on literals. -/
@[blueprint "chap10__lemma_10_6_1"]
def negLit {L : MSLanguage} : MSFormula L → MSFormula L
  | MSFormula.neg a => a
  | l => MSFormula.neg l

/-- Lemma 10.6.1 (companion): Negate a conjunction-of-literals into a DNF
by De Morgan: `¬(l_1 ∧ … ∧ l_k) = ¬l_1 ∨ … ∨ ¬l_k`. -/
@[blueprint "chap10__lemma_10_6_1"]
def negConj {L : MSLanguage} : MSFormula L → MSFormula L
  | MSFormula.conj l R => dnfOr (negLit l) (negConj R)
  | l => negLit l

/-- Lemma 10.6.1 (companion): Negate a DNF into a DNF by De Morgan:
`¬(C_1 ∨ … ∨ C_n) = ¬C_1 ∧ … ∧ ¬C_n`, distributing each `¬C_i`. -/
@[blueprint "chap10__lemma_10_6_1"]
def dnfNeg {L : MSLanguage} : MSFormula L → MSFormula L
  | MSFormula.disj C R => dnfAnd (negConj C) (dnfNeg R)
  | C => negConj C

/-- Lemma 10.6.1 (companion): The disjunctive normal form of a
quantifier-free formula, by recursion over the connectives:
literals are kept; `∧`, `∨`, `¬` use the distributing combinators;
`⊃` and `≡` are first rewritten with the standard boolean equivalences
`A ⊃ B = ¬A ∨ B` and `A ≡ B = (A ∧ B) ∨ (¬A ∧ ¬B)`. Quantifiers cannot
occur in a quantifier-free formula; on them the function returns `⊥`
(never used in the validity argument). -/
@[blueprint "chap10__lemma_10_6_1"]
def toDNF {L : MSLanguage} : MSFormula L → MSFormula L
  | MSFormula.falsum     => MSFormula.falsum
  | MSFormula.pred P ts  => MSFormula.pred P ts
  | MSFormula.eq_ hL s t u => MSFormula.eq_ hL s t u
  | MSFormula.neg A      => dnfNeg (toDNF A)
  | MSFormula.conj A B   => dnfAnd (toDNF A) (toDNF B)
  | MSFormula.disj A B   => dnfOr (toDNF A) (toDNF B)
  | MSFormula.impl A B   => dnfOr (dnfNeg (toDNF A)) (toDNF B)
  | MSFormula.equiv_ A B =>
      dnfOr (dnfAnd (toDNF A) (toDNF B))
        (dnfAnd (dnfNeg (toDNF A)) (dnfNeg (toDNF B)))
  | MSFormula.all _ _ _  => MSFormula.falsum
  | MSFormula.ex _ _ _   => MSFormula.falsum

-- --- DNF-shape preservation lemmas for the combinators ---

/-- Lemma 10.6.1 (companion): `dnfOr` of two DNFs is a DNF. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem msIsDNF_dnfOr {L : MSLanguage} :
    ∀ (B D : MSFormula L), msIsDNF B → msIsDNF D → msIsDNF (dnfOr B D) 

/-- Lemma 10.6.1 (companion): `conjConj` of two conjunctions-of-literals
is a conjunction-of-literals. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem msIsConjunctionOfLiterals_conjConj {L : MSLanguage} :
    ∀ (C D : MSFormula L), msIsConjunctionOfLiterals C →
      msIsConjunctionOfLiterals D → msIsConjunctionOfLiterals (conjConj C D) 

/-- Lemma 10.6.1 (companion): `distLeft C D` is a DNF whenever `C` is a
conjunction-of-literals and `D` is a DNF. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem msIsDNF_distLeft {L : MSLanguage} (C : MSFormula L)
    (hC : msIsConjunctionOfLiterals C) :
    ∀ D : MSFormula L, msIsDNF D → msIsDNF (distLeft C D) 

/-- Lemma 10.6.1 (companion): `dnfAnd` of two DNFs is a DNF. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem msIsDNF_dnfAnd {L : MSLanguage} :
    ∀ (B D : MSFormula L), msIsDNF B → msIsDNF D → msIsDNF (dnfAnd B D) 

/-- Lemma 10.6.1 (companion): `negLit` of a literal is a literal (hence a
conjunction-of-literals / DNF). -/
@[blueprint "chap10__lemma_10_6_1"]
theorem msIsConjunctionOfLiterals_negLit {L : MSLanguage} (l : MSFormula L)
    (hl : MSFormula.isLiteral l) : msIsConjunctionOfLiterals (negLit l) 

/-- Lemma 10.6.1 (companion): `negConj` of a conjunction-of-literals is a
DNF. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem msIsDNF_negConj {L : MSLanguage} :
    ∀ (C : MSFormula L), msIsConjunctionOfLiterals C → msIsDNF (negConj C) 

/-- Lemma 10.6.1 (companion): `dnfNeg` of a DNF is a DNF. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem msIsDNF_dnfNeg {L : MSLanguage} :
    ∀ (B : MSFormula L), msIsDNF B → msIsDNF (dnfNeg B) 

/-- Lemma 10.6.1 (companion): `toDNF A` is a DNF for every open formula
`A` (no quantifiers occur). -/
@[blueprint "chap10__lemma_10_6_1"]
theorem msIsDNF_toDNF {L : MSLanguage} :
    ∀ (A : MSFormula L), MSFormula.isOpen A → msIsDNF (toDNF A) 

-- --- evaluation correctness lemmas for the combinators ---

/-- Lemma 10.6.1 (companion): `dnfOr` evaluates to `hOr` of the
evaluations of its arguments. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem eval_dnfOr {L : MSLanguage} (M : MSStructure L) (v : MSAssignment M) :
    ∀ (B D : MSFormula L),
      msFormulaEval M (dnfOr B D) v
        = hOr (msFormulaEval M B v) (msFormulaEval M D v) 

/-- Lemma 10.6.1 (companion): `conjConj` evaluates to `hAnd` of the
evaluations of its arguments. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem eval_conjConj {L : MSLanguage} (M : MSStructure L) (v : MSAssignment M) :
    ∀ (C D : MSFormula L),
      msFormulaEval M (conjConj C D) v
        = hAnd (msFormulaEval M C v) (msFormulaEval M D v) 

/-- Lemma 10.6.1 (companion): `distLeft C D` evaluates to
`hAnd (eval C) (eval D)`. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem eval_distLeft {L : MSLanguage} (M : MSStructure L) (v : MSAssignment M)
    (C : MSFormula L) :
    ∀ (D : MSFormula L),
      msFormulaEval M (distLeft C D) v
        = hAnd (msFormulaEval M C v) (msFormulaEval M D v) 

/-- Lemma 10.6.1 (companion): `dnfAnd` evaluates to `hAnd` of the
evaluations of its arguments. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem eval_dnfAnd {L : MSLanguage} (M : MSStructure L) (v : MSAssignment M) :
    ∀ (B D : MSFormula L),
      msFormulaEval M (dnfAnd B D) v
        = hAnd (msFormulaEval M B v) (msFormulaEval M D v) 

/-- Lemma 10.6.1 (companion): `negLit l` evaluates to `hNeg (eval l)`. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem eval_negLit {L : MSLanguage} (M : MSStructure L) (v : MSAssignment M) :
    ∀ (l : MSFormula L),
      msFormulaEval M (negLit l) v = hNeg (msFormulaEval M l v) 

/-- Lemma 10.6.1 (companion): `negConj C` evaluates to `hNeg (eval C)`. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem eval_negConj {L : MSLanguage} (M : MSStructure L) (v : MSAssignment M) :
    ∀ (C : MSFormula L),
      msFormulaEval M (negConj C) v = hNeg (msFormulaEval M C v) 

/-- Lemma 10.6.1 (companion): `dnfNeg B` evaluates to `hNeg (eval B)`. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem eval_dnfNeg {L : MSLanguage} (M : MSStructure L) (v : MSAssignment M) :
    ∀ (B : MSFormula L),
      msFormulaEval M (dnfNeg B) v = hNeg (msFormulaEval M B v) 

/-- Lemma 10.6.1 (companion): the DNF `toDNF A` of an open formula `A`
evaluates exactly like `A` — `eval (toDNF A) v = eval A v` for every
structure and assignment. By induction on the formula structure; the
combinator eval lemmas reduce each connective to its `BoolVal` truth
function, and `⊃`/`≡` are discharged by the boolean identities
`A ⊃ B = ¬A ∨ B` and `A ≡ B = (A ∧ B) ∨ (¬A ∧ ¬B)`. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem eval_toDNF {L : MSLanguage} (M : MSStructure L) (v : MSAssignment M) :
    ∀ (A : MSFormula L), MSFormula.isOpen A →
      msFormulaEval M (toDNF A) v = msFormulaEval M A v 

/-- Lemma 10.6.1 (companion): a disjunct `Ci` of a DNF `B` that is
satisfied at `(M, v)` makes `B` itself true at `(M, v)`. By induction on
the disjunction structure of `B`. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem disjunctOf_eval {L : MSLanguage} (M : MSStructure L) (v : MSAssignment M) :
    ∀ (B Ci : MSFormula L), msIsDisjunctOf Ci B →
      msFormulaEval M Ci v = BoolVal.T → msFormulaEval M B v = BoolVal.T 

/-- Lemma 10.6.1 (companion): a conjunct contained in `C` is true in any
model of `C` — if `C_M[v] = T` and `msConjunctContains C X`, then
`X_M[v] = T`. By induction on the conjunction tree of `C`. (Stated here
for use in the no-equality case of Lemma 10.6.1; the same fact, phrased
for the §10.6.2 development, is `msConjunctContains_eval` below.) -/
@[blueprint "chap10__lemma_10_6_1"]
theorem conjunctContains_eval {L : MSLanguage} (M : MSStructure L)
    (v : MSAssignment M) :
    ∀ (C X : MSFormula L), msConjunctContains C X →
      msFormulaEval M C v = BoolVal.T → msFormulaEval M X v = BoolVal.T 

end LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
end
