import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.Semantics
import LCS.FirstOrder.Syntax.Substitution
import LCS.FirstOrder.Syntax.Variables
import Attach
import LCS.FirstOrder.Semantics.Substitution.ProofsStamp

/-! # FirstOrder.Semantics.Substitution
    Formalization of Chapter 5, Sections 5.3.4-5.3.5.
    A more convenient semantics via extended languages, and free variables lemma.
-/

open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax
open LCS.FirstOrder.Syntax.Variables
open LCS.FirstOrder.Syntax.Substitution
open LCS.FirstOrder.Semantics

namespace LCS.FirstOrder.Semantics.Substitution

-- ===================================================================
-- Definition 5.3.8: Extended languages need not be countable
-- ===================================================================





/-- Definition 5.3.8 (companion): For every language L, some structure S
has an extended language L(S) whose constant symbols are not countable. -/
@[blueprint "chap5__definition_5_3_8"]
theorem extendedConstants_not_countable (L : Language) :
    ∃ S : Structure L,
      ¬ Nonempty (Countable (extendedLanguage L S.carrier).constSymbols) 

/-- Definition 5.3.8 (companion): If L has equality or a positive-arity
predicate, some structure S has uncountably many L(S)-formulae. Naming
constants occur in equality atoms or in an argument of that predicate. -/
@[blueprint "chap5__definition_5_3_8"]
theorem extendedFormulae_not_countable (L : Language)
    (h : L.hasEquality = true ∨ ∃ P, 0 < L.predArity P) :
    ∃ S : Structure L,
      ¬ Nonempty (Countable (Formula (extendedLanguage L S.carrier))) 

-- ===================================================================
-- Helper: Lift terms and formulae from L to extendedLanguage L M
-- ===================================================================

/-- Definition 5.3.8 (companion): Lift a term from language L to the
extended language L(M) by mapping each constant c to Sum.inl c. -/
@[blueprint "chap5__definition_5_3_8"]
def liftTerm {L : Language} {M : Type} : Term L → Term (extendedLanguage L M)
  | .var x => .var x
  | .const c => .const (Sum.inl c)
  | .func f ts => .func f (fun i => liftTerm (ts i))

/-- Definition 5.3.8 (companion): Lift a formula from language L to the
extended language L(M) by lifting all embedded terms. -/
@[blueprint "chap5__definition_5_3_8"]
def liftFormula {L : Language} {M : Type} :
    Formula L → Formula (extendedLanguage L M)
  | .falsum => .falsum
  | .pred0 P h => .pred0 P h
  | .predN P hP ts => .predN P hP (fun i => liftTerm (ts i))
  | .eq_ hL t1 t2 => .eq_ hL (liftTerm t1) (liftTerm t2)
  | .conj A B => .conj (liftFormula A) (liftFormula B)
  | .disj A B => .disj (liftFormula A) (liftFormula B)
  | .impl A B => .impl (liftFormula A) (liftFormula B)
  | .equiv_ A B => .equiv_ (liftFormula A) (liftFormula B)
  | .neg A => .neg (liftFormula A)
  | .all i A => .all i (liftFormula A)
  | .ex i A => .ex i (liftFormula A)

-- ===================================================================
-- Lemma 5.3.1: Substitution-evaluation equivalence
-- ===================================================================

/-- Lemma 5.3.1 (companion, Part (i), term variant): For any term t of L(S),
assignment s, element m and variable x_i, evaluating t under s[x_i := m]
equals evaluating t[namingConst m / x_i] under s, both in the extended
interpretation of S. -/
@[blueprint "chap5__lemma_5_3_1" (main := true)]
theorem termSubstEval {L : Language} (S : Structure L)
    (t : Term (extendedLanguage L S.carrier)) (s : Assignment (extendedInterp S))
    (m : S.carrier) (i : Nat) :
    termEval (extendedInterp S) (assignUpdate s i m) t =
    termEval (extendedInterp S) s
      (termSubst t (namingConst m) i) 

/-- Lemma 5.3.1 (companion — naming-constant variant): For any formula A of L(S),
assignment s, element m and variable x_i, evaluating A under s[x_i := m]
equals evaluating A[namingConst m / x_i] under s in the extended
structure. -/
@[blueprint "chap5__lemma_5_3_1" (main := true)]
theorem formulaSubstEval {L : Language} (S : Structure L)
    (A : Formula (extendedLanguage L S.carrier)) (s : Assignment (extendedInterp S))
    (m : S.carrier) (i : Nat) :
    formulaEval (extendedInterp S) A (assignUpdate s i m) ↔
    formulaEval (extendedInterp S)
      (formulaSubst A (namingConst m) i) s 

-- ===================================================================
-- Lemma 5.3.2: Convenient semantics for quantifiers
-- ===================================================================

/-- Lemma 5.3.2: For any formula B of L(S), assignment s and variable x_i, (forall
x_i B)_M[s] = T iff (B[m/x_i])_M[s] = T for all m in M. This gives a substitution-based characterization of universal quantification using naming constants. (Lemma 5.3.2 bundles a forall-variant and exists-variant claim; this is the forall primary.) -/
@[blueprint "chap5__lemma_5_3_2" (main := true)]
theorem forallSemantics {L : Language} (S : Structure L)
    (B : Formula (extendedLanguage L S.carrier)) (s : Assignment (extendedInterp S)) (i : Nat) :
    formulaEval (extendedInterp S) (Formula.all i B) s ↔
    ∀ m : S.carrier,
      formulaEval (extendedInterp S)
        (formulaSubst B (namingConst m) i) s 

/-- Lemma 5.3.2 (companion, Part 2): For any formula B of L(S), assignment s
and variable x_i, (exists x_i B)_M[s] = T iff (B[m/x_i])_M[s] = T
for some m in M. Existential quantification via substitution of
naming constants. -/
@[blueprint "chap5__lemma_5_3_2" (main := true)]
theorem existsSemantics {L : Language} (S : Structure L)
    (B : Formula (extendedLanguage L S.carrier)) (s : Assignment (extendedInterp S)) (i : Nat) :
    formulaEval (extendedInterp S) (Formula.ex i B) s ↔
    ∃ m : S.carrier,
      formulaEval (extendedInterp S)
        (formulaSubst B (namingConst m) i) s 

-- ===================================================================
-- Lemma 5.3.3: Coincidence lemma (helper for terms)
-- ===================================================================



-- ===================================================================
-- Lemma 5.3.3: Coincidence lemma
-- ===================================================================

/-- Lemma 5.3.3 (companion — Formula variant): Given a formula A with free
variables {y_1,...,y_n}, if two assignments s_1 and s_2 agree on all
free variables of A (i.e., for all y in FV(A), s_1(y) = s_2(y)), then
A_M[s_1] = A_M[s_2]. The truth value of a formula depends only on the
values of its free variables. -/
@[blueprint "chap5__lemma_5_3_3" (main := true)]
theorem coincidenceLemma {L : Language} (S : Structure L)
    (A : Formula L)
    (s1 s2 : Assignment S)
    (h : ∀ y, y ∈ formulaFV A → s1 y = s2 y) :
    formulaEval S A s1 ↔ formulaEval S A s2 



/-- Lemma 5.3.3 (companion, consequence): For a sentence A and any structure S,
either A is true under every assignment in S or its negation is true under
every assignment in S. -/
@[blueprint "chap5__lemma_5_3_3"]
theorem sentenceExcludedMiddle {L : Language} (S : Structure L)
    (A : Formula L) (hSent : Formula.isSentence A) :
    validIn S A ∨ validIn S (Formula.neg A) 



end LCS.FirstOrder.Semantics.Substitution
