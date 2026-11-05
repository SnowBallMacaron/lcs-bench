import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.Syntax
import LCS.FirstOrder.Syntax.Variables
import Attach
import LCS.FirstOrder.Syntax.Substitution.ProofsStamp

/-! # FirstOrder.Syntax.Substitution
    Formalization of Chapter 5, Section 5.2.5.
    Substitutions and freeness conditions.
-/

open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax

namespace LCS.FirstOrder.Syntax.Substitution

-- ===================================================================
-- Definition 5.2.6 (companion): Formula substitution A[t/x]
-- ===================================================================

/-- Definition 5.2.6: The operation A[t/x] that substitutes term t for free
occurrences of variable x in formula A, defined recursively: - bot[t/x] = bot - (P h)[t/x] = P h (zero-rank predicate unchanged) - (P t1...tn)[t/x] = P (t1[t/x])...(tn[t/x]) - (t1 =. t2)[t/x] = (t1[t/x]) =. (t2[t/x]) - (B * C)[t/x] = B[t/x] * C[t/x] for * in {and, or, imp, equiv} - (neg B)[t/x] = neg B[t/x] - (forall y B)[t/x] = forall y B[t/x] if x != y, else forall y B - (exists y B)[t/x] = exists y B[t/x] if x != y, else exists y B -/
@[blueprint "chap5__definition_5_2_6" (main := true)]
def formulaSubst {L : Language} :
    Formula L -> Term L -> Nat -> Formula L
  | .falsum, _, _ => .falsum
  | .pred0 P h, _, _ => .pred0 P h
  | .predN P hP ts, t, x => .predN P hP (fun i => termSubst (ts i) t x)
  | .eq_ hL t1 t2, t, x => .eq_ hL (termSubst t1 t x) (termSubst t2 t x)
  | .conj A B, t, x => .conj (formulaSubst A t x) (formulaSubst B t x)
  | .disj A B, t, x => .disj (formulaSubst A t x) (formulaSubst B t x)
  | .impl A B, t, x => .impl (formulaSubst A t x) (formulaSubst B t x)
  | .equiv_ A B, t, x =>
    .equiv_ (formulaSubst A t x) (formulaSubst B t x)
  | .neg A, t, x => .neg (formulaSubst A t x)
  | .all y A, t, x =>
    if x != y then .all y (formulaSubst A t x) else .all y A
  | .ex y A, t, x =>
    if x != y then .ex y (formulaSubst A t x) else .ex y A

-- ===================================================================
-- Definition 5.2.7: Free-for predicate (t is free for x in A)
-- ===================================================================

/-- Definition 5.2.7: A term t is free for x in A if substituting t for x
in A does not cause any variable in t to become bound. Defined recursively: - Atomic formulae: always True - (B * C): t free for x in B and t free for x in C - (neg B): t free for x in B - (forall y B) or (exists y B): x = y, or (y not in FV(t) and t free for x in B) -/
@[blueprint "chap5__definition_5_2_7" (main := true)]
def isFreeFor {L : Language} :
    Term L -> Nat -> Formula L -> Prop
  | _, _, .falsum => True
  | _, _, .pred0 _ _ => True
  | _, _, .predN _ _ _ => True
  | _, _, .eq_ _ _ _ => True
  | t, x, .conj A B => isFreeFor t x A /\ isFreeFor t x B
  | t, x, .disj A B => isFreeFor t x A /\ isFreeFor t x B
  | t, x, .impl A B => isFreeFor t x A /\ isFreeFor t x B
  | t, x, .equiv_ A B => isFreeFor t x A /\ isFreeFor t x B
  | t, x, .neg A => isFreeFor t x A
  | t, x, .all y A =>
    x = y \/ (Not (Membership.mem (termFV t) y) /\ isFreeFor t x A)
  | t, x, .ex y A =>
    x = y \/ (Not (Membership.mem (termFV t) y) /\ isFreeFor t x A)

-- ===================================================================
-- Example 5.2.4: Substitution examples
-- ===================================================================

-- We need a language with unary P, binary Q, unary f, unary g.

/-- Example 5.2.4 (companion): Function symbols for the substitution example
language — f (unary) and g (unary). -/
@[blueprint "chap5__example_5_2_4"]
inductive ExSubstFunc : Type where
  | f : ExSubstFunc
  | g : ExSubstFunc

/-- Example 5.2.4 (companion): Predicate symbols for the substitution example
language — P (unary) and Q (binary). -/
@[blueprint "chap5__example_5_2_4"]
inductive ExSubstPred : Type where
  | P : ExSubstPred
  | Q : ExSubstPred

/-- Example 5.2.4 (companion): The example language for substitution with
unary functions f, g and predicates P (unary), Q (binary). -/
@[blueprint "chap5__example_5_2_4"]
def exSubstLanguage : Language where
  funSymbols := ExSubstFunc
  funArity := fun
    | .f => 1
    | .g => 1
  constSymbols := Empty
  predSymbols := ExSubstPred
  predArity := fun
    | .P => 1
    | .Q => 2

-- Variable assignments: x = 0, y = 1

/-- Example 5.2.4: The formula A = forall x(P(x) imp Q(x, f(y))),
where x = 0, y = 1. -/
@[blueprint "chap5__example_5_2_4"]
def substExample_5_2_4_formula : Formula exSubstLanguage :=
  Formula.all 0
    (Formula.impl
      (Formula.predN ExSubstPred.P (by decide)
        (fun _ => Term.var 0))
      (Formula.predN ExSubstPred.Q (by decide)
        (vec2 (Term.var 0)
          (Term.func ExSubstFunc.f (fun _ => Term.var 1)))))

/-- Example 5.2.4: The substitution term t = g(y), where y = 1. -/
@[blueprint "chap5__example_5_2_4"]
def substExample_5_2_4_term_gy : Term exSubstLanguage :=
  Term.func ExSubstFunc.g (fun _ => Term.var 1)







/-- Example 5.2.4: Substituting g(y) for x in f(x) gives f(g(y)). -/
@[blueprint "chap5__example_5_2_4" (main := true)]
theorem substExample_5_2_4_term_subst_eq :
    termSubst (Term.func ExSubstFunc.f (fun _ => Term.var 0))
      substExample_5_2_4_term_gy 0 =
    Term.func ExSubstFunc.f (fun _ => substExample_5_2_4_term_gy) 

/-- Example 5.2.4: Substituting g(y) for free y in A gives
∀x(P(x) ⊃ Q(x, f(g(y)))). -/
@[blueprint "chap5__example_5_2_4" (main := true)]
theorem substExample_5_2_4_free_var_subst_eq :
    formulaSubst substExample_5_2_4_formula substExample_5_2_4_term_gy 1 =
    Formula.all 0
      (Formula.impl
        (Formula.predN ExSubstPred.P (by decide) (fun _ => Term.var 0))
        (Formula.predN ExSubstPred.Q (by decide)
          (vec2 (Term.var 0)
            (Term.func ExSubstFunc.f (fun _ => substExample_5_2_4_term_gy))))) 

/-- Example 5.2.4: Substitution for the bound variable x leaves A unchanged. -/
@[blueprint "chap5__example_5_2_4" (main := true)]
theorem substExample_5_2_4_bound_var_subst_eq :
    formulaSubst substExample_5_2_4_formula substExample_5_2_4_term_gy 0 =
      substExample_5_2_4_formula 

-- ===================================================================
-- Example 5.2.5: Variable capture
-- ===================================================================

-- Uses arithLanguage with less-than predicate. Variables: x = 0, y = 1.

/-- Example 5.2.5: The formula exists x(x < y) before substitution,
where x = 0, y = 1. -/
@[blueprint "chap5__example_5_2_5"]
def captureExample_5_2_5_before : Formula arithLanguage :=
  Formula.ex 0
    (Formula.predN ArithPred.lt (by decide)
      (vec2 (Term.var 0) (Term.var 1)))

/-- Example 5.2.5: The formula exists x(x < x) after substituting x for y,
i.e., (exists x(x < y))[x/y] = exists x(x < x). This demonstrates variable capture: x becomes bound by exists x, changing the formula's meaning. The original may be satisfied but exists x(x < x) is false in ordered structures. -/
@[blueprint "chap5__example_5_2_5"]
def captureExample_5_2_5_after : Formula arithLanguage :=
  formulaSubst captureExample_5_2_5_before (Term.var 0) 1

/-- Example 5.2.5: Substituting x for y in ∃x(x < y) yields ∃x(x < x). -/
@[blueprint "chap5__example_5_2_5" (main := true)]
theorem captureExample_5_2_5_after_eq :
    formulaSubst captureExample_5_2_5_before (Term.var 0) 1 =
      Formula.ex 0 (Formula.predN ArithPred.lt (by decide) (fun _ => Term.var 0)) 

/-- Example 5.2.5: The result ∃x(x < x) is a sentence. -/
@[blueprint "chap5__example_5_2_5"]
theorem captureExample_5_2_5_isSentence :
    Variables.Formula.isSentence captureExample_5_2_5_after 

-- ===================================================================
-- Example 5.2.6: Free-for predicate examples
-- ===================================================================

-- Uses exSubstLanguage. A = forall x(P(x) imp Q(x, f(y))),
-- B = forall x(P(x) imp forall z Q(z, f(y))).
-- Variables: x = 0, y = 1, z = 2.

/-- Example 5.2.6: The formula B = forall x(P(x) imp forall z Q(z, f(y))),
where x = 0, y = 1, z = 2. -/
@[blueprint "chap5__example_5_2_6"]
def freeForExample_5_2_6_formulaB : Formula exSubstLanguage :=
  Formula.all 0
    (Formula.impl
      (Formula.predN ExSubstPred.P (by decide) (fun _ => Term.var 0))
      (Formula.all 2
        (Formula.predN ExSubstPred.Q (by decide)
          (vec2 (Term.var 2)
            (Term.func ExSubstFunc.f (fun _ => Term.var 1))))))

/-- Example 5.2.6: isFreeFor g(y) y A holds: g(y) is free for y in forall
x(P(x) imp Q(x, f(y))) because y in g(y) does not get captured by forall x. -/
@[blueprint "chap5__example_5_2_6" (main := true)]
theorem freeForExample_5_2_6_positive :
  isFreeFor
    (Term.func ExSubstFunc.g (fun _ => Term.var 1))
    1
    substExample_5_2_4_formula 

/-- Example 5.2.6: not (isFreeFor g(x) y A): g(x) is not free for y in
forall x(P(x) imp Q(x, f(y))) because x in g(x) would be captured by forall x. -/
@[blueprint "chap5__example_5_2_6" (main := true)]
theorem freeForExample_5_2_6_capture :
  Not (isFreeFor
    (Term.func ExSubstFunc.g (fun _ => Term.var 0))
    1
    substExample_5_2_4_formula) 

/-- Example 5.2.6: not (isFreeFor g(z) y B): g(z) is not free for y in
forall x(P(x) imp forall z Q(z, f(y))) because z in g(z) would be captured by the inner forall z. -/
@[blueprint "chap5__example_5_2_6" (main := true)]
theorem freeForExample_5_2_6_nested :
  Not (isFreeFor
    (Term.func ExSubstFunc.g (fun _ => Term.var 2))
    1
    freeForExample_5_2_6_formulaB) 

/-- Example 5.2.6: isFreeFor g(z) z B holds: g(z) is free for z in B
because z is bound by forall z, so the x = y disjunct in the quantifier case is satisfied and no substitution occurs. -/
@[blueprint "chap5__example_5_2_6" (main := true)]
theorem freeForExample_5_2_6_trivial :
  isFreeFor
    (Term.func ExSubstFunc.g (fun _ => Term.var 2))
    2
    freeForExample_5_2_6_formulaB 

end LCS.FirstOrder.Syntax.Substitution
