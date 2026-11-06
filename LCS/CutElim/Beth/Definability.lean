import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.CutElim.CompletenessBridge
import LCS.CutElim.LKe
import LCS.CutElim.Interpolation
import LCS.FirstOrder.Syntax
import LCS.FirstOrder.Semantics
import Attach
import LCS.CutElim.Beth.Definability.ProofsStamp

section
namespace LCS.CutElim.Beth
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Completeness
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.SyntaxN.Variables
open Classical

/-- Ordinary predicate symbols occurring in a formula, with equality exempt. -/
@[blueprint "chap6__theorem_6_6_2"]
def formulaPredSymbolsN {L : Language} : FormulaN L → Set L.predSymbols
  | .predN P _ => fun Q => Q = P
  | .eq_ _ _ _ => ∅
  | .neg A => formulaPredSymbolsN A
  | .conj A B => formulaPredSymbolsN A ∪ formulaPredSymbolsN B
  | .disj A B => formulaPredSymbolsN A ∪ formulaPredSymbolsN B
  | .impl A B => formulaPredSymbolsN A ∪ formulaPredSymbolsN B
  | .all _ A => formulaPredSymbolsN A
  | .ex _ A => formulaPredSymbolsN A

/-- Predicate-symbol occurrence for the §6.6 setup: some P denotes an
ordinary predicate P, and none denotes equality ≐. -/
@[blueprint "chap6__definition_6_6_1"]
def formulaPredSymbolsEqN {L : Language} : FormulaN L → Option L.predSymbols → Prop
  | .predN P _, Q => Q = some P
  | .eq_ _ _ _, Q => Q = none
  | .neg A, Q => formulaPredSymbolsEqN A Q
  | .conj A B, Q => formulaPredSymbolsEqN A Q ∨ formulaPredSymbolsEqN B Q
  | .disj A B, Q => formulaPredSymbolsEqN A Q ∨ formulaPredSymbolsEqN B Q
  | .impl A B, Q => formulaPredSymbolsEqN A Q ∨ formulaPredSymbolsEqN B Q
  | .all _ A, Q => formulaPredSymbolsEqN A Q
  | .ex _ A, Q => formulaPredSymbolsEqN A Q

/-- The finite list of distinct predicate symbols P₁,…,P_k.
Equality is represented by none and is admissible only in a language
with equality; ordinary predicates are represented by some P. -/
@[blueprint "chap6__definition_6_6_1"]
structure PredList (L : Language) where
  syms : List (Option L.predSymbols)
  nodup : syms.Nodup
  eqAdmissible : none ∈ syms → L.hasEquality = true

/-- Expand a language by one fresh predicate of arity n. Old predicates
are some P; the new predicate is none. All other symbols and equality
retain their interpretation in the original language. -/
@[blueprint "chap6__definition_6_6_2"]
def _root_.LCS.FirstOrder.Basic.Language.addPred (L : Language) (n : Nat) : Language where
  funSymbols := L.funSymbols
  funArity := L.funArity
  constSymbols := L.constSymbols
  predSymbols := Option L.predSymbols
  predArity
    | some P => L.predArity P
    | none => n
  hasEquality := L.hasEquality

/-- Embed terms into a predicate expansion; term-forming symbols are unchanged. -/
@[blueprint "chap6__definition_6_6_2"]
def _root_.LCS.FirstOrder.Basic.Term.liftAddPred {L : Language} (n : Nat) :
    Term L → Term (L.addPred n)
  | .var x => .var x
  | .const c => .const c
  | .func f ts => .func f (fun i => (ts i).liftAddPred n)

/-- Embed formulae into a predicate expansion, sending each old predicate P
to some P and preserving equality, connectives, and quantifiers. -/
@[blueprint "chap6__definition_6_6_2"]
def _root_.LCS.FirstOrder.SyntaxN.FormulaN.liftAddPred {L : Language} (n : Nat) :
    FormulaN L → FormulaN (L.addPred n)
  | .predN P ts => .predN (some P) (fun i => (ts i).liftAddPred n)
  | .eq_ h t u => .eq_ h (t.liftAddPred n) (u.liftAddPred n)
  | .neg A => .neg (A.liftAddPred n)
  | .conj A B => .conj (A.liftAddPred n) (B.liftAddPred n)
  | .disj A B => .disj (A.liftAddPred n) (B.liftAddPred n)
  | .impl A B => .impl (A.liftAddPred n) (B.liftAddPred n)
  | .all x A => .all x (A.liftAddPred n)
  | .ex x A => .ex x (A.liftAddPred n)

/-- Definition 6.6.2 (required helper): Substitute predicate symbol
Q by Q' (with same arity) in a formula, rewriting every occurrence of
`.predN Q ts` to `.predN Q' (coerced ts)`. Used in Def 6.6.2 to state
that A(P_1,...,P_k,Q') is the result of substituting Q' for Q in
A(P_1,...,P_k,Q). In the predicate expansion, this substitutes none
for some Q in the embedded axiom formula. -/
@[blueprint "chap6__definition_6_6_2"]
noncomputable def formulaPredSubstN {L : Language}
    (Q Qcopy : L.predSymbols)
    (h : L.predArity Qcopy = L.predArity Q) :
    FormulaN L → FormulaN L
  | .predN P ts =>
      if hpq : P = Q then
        .predN Qcopy
          (fun i => ts (Fin.cast (h.trans (congrArg L.predArity hpq.symm)) i))
      else
        .predN P ts
  | .eq_ hL t1 t2 => .eq_ hL t1 t2
  | .neg A => .neg (formulaPredSubstN Q Qcopy h A)
  | .conj A B =>
      .conj (formulaPredSubstN Q Qcopy h A) (formulaPredSubstN Q Qcopy h B)
  | .disj A B =>
      .disj (formulaPredSubstN Q Qcopy h A) (formulaPredSubstN Q Qcopy h B)
  | .impl A B =>
      .impl (formulaPredSubstN Q Qcopy h A) (formulaPredSubstN Q Qcopy h B)
  | .all x A => .all x (formulaPredSubstN Q Qcopy h A)
  | .ex x A => .ex x (formulaPredSubstN Q Qcopy h A)

-- ===================================================================
-- Helpers for Beth definability structures
-- ===================================================================
/-- Definition 6.6.1 (required helper): Build the universal quantifier
prefix forall x_0 (forall x_1 (... (forall x_{n-1} A))). Used in the
statement of Def 6.6.1 (the ∀x_1...∀x_n quantifier prefix in the
provability condition), and transitively in Def 6.6.2 and Thm 6.6.2. -/
@[blueprint "chap6__definition_6_6_1"]
def bethUniversalPrefix {L : Language} (n : Nat) (A : FormulaN L) :
    FormulaN L :=
  (List.range n).foldr (fun i acc => FormulaN.all i acc) A

/-- Definition 6.6.1 (required helper): Build Q(x_0, ..., x_{n-1})
for a predicate Q of arity n. Used in the statement of Def 6.6.1
(the atomic form Q(x_1,...,x_n) on the left of the biconditional in
the provability condition), and transitively in Def 6.6.2,
Thm 6.6.1, and Thm 6.6.2. -/
@[blueprint "chap6__definition_6_6_1"]
def bethPredApplied {L : Language} (P : L.predSymbols) : FormulaN L :=
  FormulaN.predN P (fun i => Term.var i.val)

-- ===================================================================
-- Definition 6.6.1: ExplicitDefinability
-- ===================================================================
/-- Definition 6.6.1: Q is defined explicitly from P_1,...,P_k in the
theory based on A_1,...,A_m iff there exists a formula D(P_1,...,P_k)
such that the axiom conjunction implies Q is equivalent to D.
The allowed predicates form a finite duplicate-free list, may include ≐,
and exclude Q. The predicates of A are among that list and Q; those of D
are among the list, with at least one listed predicate occurring in D. -/
@[blueprint "chap6__definition_6_6_1" (main := true)]
structure ExplicitDefinability (L : Language) : Type 1 where
  /-- The conjunction A_1 wedge ... wedge A_m of closed formulae
      serving as axioms -/
  axiomFormula : FormulaN L
  /-- The predicate symbol Q whose definability is investigated -/
  predQ : L.predSymbols
  /-- The rank n > 0 of Q -/
  rankPositive : L.predArity predQ > 0
  /-- STANDING ASSUMPTION #18 (§6.6): Each A_i is a closed formula
      (sentence) -/
  axiomsClosed : formulaFVN axiomFormula = ∅
  /-- The finite list of distinct allowed predicates P₁,…,P_k, counting ≐ -/
  preds : PredList L
  /-- Q is distinct from each of P_1,...,P_k -/
  predQ_not_in_P : some predQ ∉ preds.syms
  /-- Predicate symbols of A are among P_1,...,P_k,Q -/
  axiomFormula_predSyms_in :
    ∀ p, formulaPredSymbolsEqN axiomFormula p → p ∈ preds.syms ∨ p = some predQ
  /-- The L-formula D whose predicate symbols are among
      P_1,...,P_k -/
  definingFormula : FormulaN L
  /-- The set of free variables of D is a subset of
      {x_0,...,x_{n-1}} -/
  freeVarRestriction :
    ∀ v, v ∈ formulaFVN definingFormula → v < L.predArity predQ
  /-- The predicate symbols of D are among P_1,...,P_k (D does not
      mention Q) -/
  definingFormula_predSyms_in :
    ∀ p, formulaPredSymbolsEqN definingFormula p → p ∈ preds.syms
  /-- At least one listed P_i occurs in D; equality counts as an occurrence -/
  definingFormula_has_predP :
    ∃ p ∈ preds.syms, formulaPredSymbolsEqN definingFormula p
  /-- The formula A supset forall x_0...forall x_{n-1}
      (Q(x_0,...,x_{n-1}) equiv D(P_1,...,P_k)) is universally
      valid -/
  provabilityCondition :
    universallyValidN
      (FormulaN.impl axiomFormula
        (bethUniversalPrefix (L.predArity predQ)
          (FormulaN.equiv (bethPredApplied predQ) definingFormula)))

-- ===================================================================
-- Definition 6.6.2: ImplicitDefinability
-- ===================================================================
/-- Definition 6.6.2: Q is defined implicitly from P₁,…,P_k when
A(P,Q) ∧ A(P,Q′) ⊃ ∀x̄ (Q(x̄) ≡ Q′(x̄)) is valid in the expansion
by a fresh predicate Q′. The finite list of distinct P_i may include ≐
when L has equality and excludes Q. All predicate symbols of A, counting
≐, are among P₁,…,P_k,Q. -/
@[blueprint "chap6__definition_6_6_2" (main := true)]
structure ImplicitDefinability (L : Language) : Type 1 where
  /-- The axiom conjunction A(P₁,…,P_k,Q) in the original language -/
  axiomFormula : FormulaN L
  /-- The predicate Q whose definability is investigated -/
  predQ : L.predSymbols
  /-- The rank n > 0 of Q -/
  rankPositive : L.predArity predQ > 0
  /-- The axiom conjunction is closed -/
  axiomsClosed : formulaFVN axiomFormula = ∅
  /-- The finite list of distinct defining predicates, counting ≐ -/
  preds : PredList L
  /-- Q is distinct from every listed P_i -/
  predQ_not_in_P : some predQ ∉ preds.syms
  /-- All predicate symbols of A, including equality, are among P₁,…,P_k,Q -/
  axiomFormula_predSyms_in :
    ∀ p, formulaPredSymbolsEqN axiomFormula p → p ∈ preds.syms ∨ p = some predQ
  /-- Validity is quantified over structures of the expansion. The fresh
      predicate none has Q's arity and replaces some Q in the second copy of A. -/
  validityCondition :
    let Aplus := axiomFormula.liftAddPred (L.predArity predQ)
    universallyValidN
      (FormulaN.impl
        (FormulaN.conj Aplus (formulaPredSubstN (some predQ) none rfl Aplus))
        (bethUniversalPrefix (L.predArity predQ)
          (FormulaN.equiv
            (bethPredApplied (L := L.addPred (L.predArity predQ)) (some predQ))
            (bethPredApplied (L := L.addPred (L.predArity predQ)) none))))

/-- An interpretation of L on a specified carrier M. The common carrier
makes pointwise comparison of two interpretations well-typed. -/
@[blueprint "chap6__definition_6_6_2"]
structure InterpretationOn (L : Language) (M : Type) where
  interpFunc : (f : L.funSymbols) → (Fin (L.funArity f) → M) → M
  interpConst : L.constSymbols → M
  interpPred : (P : L.predSymbols) → (Fin (L.predArity P) → M) → Prop

end LCS.CutElim.Beth
end
