import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.CutElim.CompletenessBridge
import LCS.CutElim.LKe
import LCS.CutElim.Interpolation
import LCS.FirstOrder.Syntax
import LCS.FirstOrder.Semantics
import Attach
import LCS.CutElim.Beth.Part1.ProofsStamp

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

/-- Theorem 6.6.2 (required helper): The set of function symbols
occurring in a term. Used in the body of `formulaFuncSymbolsN` to
collect function symbols from terms occurring in a formula. -/
@[blueprint "chap6__theorem_6_6_2"]
def termFuncSymbolsLocal {L : Language} : Term L → Set L.funSymbols
  | .var _ => ∅
  | .const _ => ∅
  | .func f ts => fun g => g = f ∨ ∃ i, termFuncSymbolsLocal (ts i) g

/-- Theorem 6.6.2 (required helper): The set of function symbols
occurring in a formula. Used in Thm 6.6.2(b) to state that the
defining formula D does not contain the function being defined. -/
@[blueprint "chap6__theorem_6_6_2"]
def formulaFuncSymbolsN {L : Language} : FormulaN L → Set L.funSymbols
  | .predN _ ts => fun f => ∃ i, termFuncSymbolsLocal (ts i) f
  | .eq_ _ t1 t2 => termFuncSymbolsLocal t1 ∪ termFuncSymbolsLocal t2
  | .neg A => formulaFuncSymbolsN A
  | .conj A B => formulaFuncSymbolsN A ∪ formulaFuncSymbolsN B
  | .disj A B => formulaFuncSymbolsN A ∪ formulaFuncSymbolsN B
  | .impl A B => formulaFuncSymbolsN A ∪ formulaFuncSymbolsN B
  | .all _ A => formulaFuncSymbolsN A
  | .ex _ A => formulaFuncSymbolsN A

/-- Theorem 6.6.2 (required helper): Substitute function symbol f
by f' (with same arity) in a term, rewriting every occurrence of
`.func f ts` to `.func f' (coerced ts)`. Used by
`formulaFuncSubstN` (Thm 6.6.2 b)
to recurse into terms occurring in predicate applications and equalities. -/
@[blueprint "chap6__theorem_6_6_2"]
noncomputable def termFuncSubstN {L : Language}
    (f f' : L.funSymbols)
    (h : L.funArity f' = L.funArity f) :
    Term L → Term L
  | .var n => .var n
  | .const c => .const c
  | .func g ts =>
      if hfg : g = f then
        .func f' (fun i =>
          termFuncSubstN f f' h
            (ts (Fin.cast (h.trans (congrArg L.funArity hfg.symm)) i)))
      else
        .func g (fun i => termFuncSubstN f f' h (ts i))

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

/-- Theorem 6.6.2 (required helper): Substitute function symbol f
by f' in a formula (recursing into terms under predN and eq_). Used
in Thm 6.6.2(b) to state that A(P_1,...,P_k,f') is the result of
substituting f' for f in A(P_1,...,P_k,f). In the fresh-function expansion this substitutes
none for some f in the embedded axiom formula. -/
@[blueprint "chap6__theorem_6_6_2"]
noncomputable def formulaFuncSubstN {L : Language}
    (f f' : L.funSymbols)
    (h : L.funArity f' = L.funArity f) :
    FormulaN L → FormulaN L
  | .predN P ts => .predN P (fun i => termFuncSubstN f f' h (ts i))
  | .eq_ hL t1 t2 => .eq_ hL (termFuncSubstN f f' h t1) (termFuncSubstN f f' h t2)
  | .neg A => .neg (formulaFuncSubstN f f' h A)
  | .conj A B =>
      .conj (formulaFuncSubstN f f' h A) (formulaFuncSubstN f f' h B)
  | .disj A B =>
      .disj (formulaFuncSubstN f f' h A) (formulaFuncSubstN f f' h B)
  | .impl A B =>
      .impl (formulaFuncSubstN f f' h A) (formulaFuncSubstN f f' h B)
  | .all x A => .all x (formulaFuncSubstN f f' h A)
  | .ex x A => .ex x (formulaFuncSubstN f f' h A)

/-- Adjoin a fresh function of arity n; none names the fresh symbol. -/
@[blueprint "chap6__theorem_6_6_2"]
def _root_.LCS.FirstOrder.Basic.Language.addFun (L : Language) (n : Nat) : Language where
  funSymbols := Option L.funSymbols
  funArity
    | some f => L.funArity f
    | none => n
  constSymbols := L.constSymbols
  predSymbols := L.predSymbols
  predArity := L.predArity
  hasEquality := L.hasEquality

/-- Embed terms into the fresh-function expansion. -/
@[blueprint "chap6__theorem_6_6_2"]
def _root_.LCS.FirstOrder.Basic.Term.liftAddFun {L : Language} (n : Nat) :
    Term L → Term (L.addFun n)
  | .var x => .var x
  | .const c => .const c
  | .func f ts => .func (some f) (fun i => (ts i).liftAddFun n)

/-- Embed formulae into the fresh-function expansion, preserving predicates and equality. -/
@[blueprint "chap6__theorem_6_6_2"]
def _root_.LCS.FirstOrder.SyntaxN.FormulaN.liftAddFun {L : Language} (n : Nat) :
    FormulaN L → FormulaN (L.addFun n)
  | .predN P ts => .predN P (fun i => (ts i).liftAddFun n)
  | .eq_ h t u => .eq_ h (t.liftAddFun n) (u.liftAddFun n)
  | .neg A => .neg (A.liftAddFun n)
  | .conj A B => .conj (A.liftAddFun n) (B.liftAddFun n)
  | .disj A B => .disj (A.liftAddFun n) (B.liftAddFun n)
  | .impl A B => .impl (A.liftAddFun n) (B.liftAddFun n)
  | .all x A => .all x (A.liftAddFun n)
  | .ex x A => .ex x (A.liftAddFun n)

/-- Adjoin a fresh constant; none names the fresh symbol. -/
@[blueprint "chap6__theorem_6_6_2"]
def _root_.LCS.FirstOrder.Basic.Language.addConst (L : Language) : Language where
  funSymbols := L.funSymbols
  funArity := L.funArity
  constSymbols := Option L.constSymbols
  predSymbols := L.predSymbols
  predArity := L.predArity
  hasEquality := L.hasEquality

/-- Embed terms into the fresh-constant expansion. -/
@[blueprint "chap6__theorem_6_6_2"]
def _root_.LCS.FirstOrder.Basic.Term.liftAddConst {L : Language} :
    Term L → Term (L.addConst)
  | .var x => .var x
  | .const c => .const (some c)
  | .func f ts => .func f (fun i => (ts i).liftAddConst)

/-- Embed formulae into the fresh-constant expansion, preserving predicates and equality. -/
@[blueprint "chap6__theorem_6_6_2"]
def _root_.LCS.FirstOrder.SyntaxN.FormulaN.liftAddConst {L : Language} :
    FormulaN L → FormulaN (L.addConst)
  | .predN P ts => .predN P (fun i => (ts i).liftAddConst)
  | .eq_ h t u => .eq_ h (t.liftAddConst) (u.liftAddConst)
  | .neg A => .neg (A.liftAddConst)
  | .conj A B => .conj (A.liftAddConst) (B.liftAddConst)
  | .disj A B => .disj (A.liftAddConst) (B.liftAddConst)
  | .impl A B => .impl (A.liftAddConst) (B.liftAddConst)
  | .all x A => .all x (A.liftAddConst)
  | .ex x A => .ex x (A.liftAddConst)

/-- Replace a constant throughout a term, including nested function arguments. -/
@[blueprint "chap6__theorem_6_6_2"]
noncomputable def termConstSubstN {L : Language} (c c' : L.constSymbols) :
    Term L → Term L
  | .var x => .var x
  | .const d => .const (if d = c then c' else d)
  | .func f ts => .func f (fun i => termConstSubstN c c' (ts i))

/-- Replace a constant throughout a formula. -/
@[blueprint "chap6__theorem_6_6_2"]
noncomputable def formulaConstSubstN {L : Language} (c c' : L.constSymbols) :
    FormulaN L → FormulaN L
  | .predN P ts => .predN P (fun i => termConstSubstN c c' (ts i))
  | .eq_ h t u => .eq_ h (termConstSubstN c c' t) (termConstSubstN c c' u)
  | .neg A => .neg (formulaConstSubstN c c' A)
  | .conj A B => .conj (formulaConstSubstN c c' A) (formulaConstSubstN c c' B)
  | .disj A B => .disj (formulaConstSubstN c c' A) (formulaConstSubstN c c' B)
  | .impl A B => .impl (formulaConstSubstN c c' A) (formulaConstSubstN c c' B)
  | .all x A => .all x (formulaConstSubstN c c' A)
  | .ex x A => .ex x (formulaConstSubstN c c' A)



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

/-- Package a fixed-carrier interpretation as an L-structure on a nonempty domain. -/
@[blueprint "chap6__definition_6_6_2"]
def InterpretationOn.toStructure {L : Language} {M : Type}
    (I : InterpretationOn L M) (hM : Nonempty M) : Structure L where
  carrier := M
  carrierNonempty := hM
  interpFunc := I.interpFunc
  interpConst := I.interpConst
  interpPred := I.interpPred

/-- The two-structure implicit-definability criterion in the
other-symbols-fixed reading: interpretations on the same nonempty carrier
agree on every listed P_i and on every other nonlogical symbol except Q.
If both satisfy A, they agree on Q at every argument tuple.
Equality, represented by none in the predicate list, is the carrier's
identity relation in both structures, so its agreement is automatic. -/
@[blueprint "chap6__definition_6_6_2"]
def TwoStructureImplicit {L : Language}
    (A : FormulaN L) (preds : PredList L) (Q : L.predSymbols) : Prop :=
  ∀ (M : Type) (hM : Nonempty M) (I J : InterpretationOn L M),
    (∀ P, some P ∈ preds.syms → ∀ a, I.interpPred P a ↔ J.interpPred P a) →
    I.interpFunc = J.interpFunc →
    I.interpConst = J.interpConst →
    (∀ P, P ≠ Q → ∀ a, I.interpPred P a ↔ J.interpPred P a) →
    validInN (I.toStructure hM) A →
    validInN (J.toStructure hM) A →
    ∀ a, I.interpPred Q a ↔ J.interpPred Q a

/-- Explicit validity implies the Definition 6.6.2 validity condition
in the fresh-predicate expansion. The defining formula uses only listed
predicates, including equality when listed, and Q is not listed. -/
theorem explicit_implies_implicit_validity {L : Language}
    (A D : FormulaN L) (preds : PredList L) (Q : L.predSymbols)
    (hQ : some Q ∉ preds.syms)
    (hExplicit : universallyValidN
      (.impl A (bethUniversalPrefix (L.predArity Q)
        (.equiv (bethPredApplied Q) D))))
    (hD : ∀ p, formulaPredSymbolsEqN D p → p ∈ preds.syms) :
    let Aplus := A.liftAddPred (L.predArity Q)
    universallyValidN
      (FormulaN.impl
        (FormulaN.conj Aplus (formulaPredSubstN (some Q) none rfl Aplus))
        (bethUniversalPrefix (L.predArity Q)
          (FormulaN.equiv
            (bethPredApplied (L := L.addPred (L.predArity Q)) (some Q))
            (bethPredApplied (L := L.addPred (L.predArity Q)) none)))) := by
  -- Lift the explicit equivalence to L⁺ and substitute fresh Q′ for Q.
  -- D is unaffected because its ordinary predicates exclude Q.
  -- REPAIR(T6-60): proof pending
  sorry

/-- A Definition 6.6.1 explicit-definability package satisfies the
implicit-definability validity condition over the fresh expansion. -/
@[blueprint "chap6__definition_6_6_2"]
theorem explicit_implies_implicit {L : Language} (e : ExplicitDefinability L) :
    let Aplus := e.axiomFormula.liftAddPred (L.predArity e.predQ)
    universallyValidN
      (FormulaN.impl
        (FormulaN.conj Aplus (formulaPredSubstN (some e.predQ) none rfl Aplus))
        (bethUniversalPrefix (L.predArity e.predQ)
          (FormulaN.equiv
            (bethPredApplied (L := L.addPred (L.predArity e.predQ)) (some e.predQ))
            (bethPredApplied (L := L.addPred (L.predArity e.predQ)) none)))) 

/-- The fresh-copy validity condition yields the two-structure criterion
when all symbols other than Q are fixed. -/
theorem bethImplicitValidity_twoStructure {L : Language}
    (A : FormulaN L) (preds : PredList L) (Q : L.predSymbols)
    (hImplicit :
      let Aplus := A.liftAddPred (L.predArity Q)
      universallyValidN
        (FormulaN.impl
          (FormulaN.conj Aplus (formulaPredSubstN (some Q) none rfl Aplus))
          (bethUniversalPrefix (L.predArity Q)
            (FormulaN.equiv
              (bethPredApplied (L := L.addPred (L.predArity Q)) (some Q))
              (bethPredApplied (L := L.addPred (L.predArity Q)) none))))) :
    TwoStructureImplicit A preds Q := by
  -- Interpret old symbols using the first model and the fresh predicate
  -- using the second model's Q. Agreement off Q identifies the copied A
  -- with A in the second model; specialize the universal prefix.
  -- REPAIR(T6-60): proof pending
  sorry

/-- Padoa's method, corrected by E-PADOA: two models of A on one carrier,
agreeing on every symbol except Q but disagreeing on Q, rule out an
explicit definition of Q from the listed predicates.

Erratum: the printed method omits the model and other-symbol agreement
requirements. Without the model requirement, A = ∀x(Q(x) ≡ P(x)) is a
counterexample: arbitrary structures can agree on P and differ on Q,
although D = P(x) defines Q under A. Even requiring models is insufficient
if constants may vary: A = ∀x(Q(x) ≡ x ≐ c), with P₁ = ≐, explicitly defines
Q by x ≐ c, but models on {0,1} choosing c = 0 and c = 1 agree on ≐ and
disagree on Q. The adopted statement fixes functions and constants as well. -/
@[blueprint "chap6__theorem_6_6_1"]
theorem padoa_method {L : Language}
    (A : FormulaN L) (preds : PredList L) (Q : L.predSymbols)
    (M : Type) (hM : Nonempty M) (I J : InterpretationOn L M)
    (hFunc : I.interpFunc = J.interpFunc)
    (hConst : I.interpConst = J.interpConst)
    (hPred : ∀ P, P ≠ Q → ∀ a, I.interpPred P a ↔ J.interpPred P a)
    (hAI : validInN (I.toStructure hM) A)
    (hAJ : validInN (J.toStructure hM) A)
    (hDiff : ∃ a, ¬ (I.interpPred Q a ↔ J.interpPred Q a)) :
    ¬ ∃ e : ExplicitDefinability L,
      e.axiomFormula = A ∧ e.predQ = Q ∧ e.preds = preds

-- ===================================================================
-- Theorem 6.6.1 (companion, part a): SomePredOccurs
-- ===================================================================

/-- Theorem 6.6.1 (companion, part a): At least one predicate symbol
P_i from the finite list actually occurs in the axiom formula. -/
@[blueprint "chap6__theorem_6_6_1"]
def SomePredOccurs {L : Language}
    (A : FormulaN L) (preds : PredList L) : Prop :=
  ∃ p ∈ preds.syms, formulaPredSymbolsEqN A p

-- ===================================================================
-- Theorem 6.6.1 (companion, part b): NoPredOccurs
-- ===================================================================

/-- Theorem 6.6.1 (companion, part b): None of the predicate symbols
P_1,...,P_k occur in the axiom formula. -/
@[blueprint "chap6__theorem_6_6_1"]
def NoPredOccurs {L : Language}
    (A : FormulaN L) (preds : PredList L) : Prop :=
  ∀ p ∈ preds.syms, ¬ formulaPredSymbolsEqN A p

-- ===================================================================
-- Theorem 6.6.1 (companion, part b): UnivTrueOrFalse
-- ===================================================================

/-- Theorem 6.6.1 (companion, part b): Q is either universally true
or universally false under the axioms, in the original language L. -/
@[blueprint "chap6__theorem_6_6_1"]
def UnivTrueOrFalse {L : Language}
    (implDef : ImplicitDefinability L) : Prop :=
  universallyValidN
    (FormulaN.impl implDef.axiomFormula
      (bethUniversalPrefix (L.predArity implDef.predQ)
        (bethPredApplied implDef.predQ))) ∨
  universallyValidN
    (FormulaN.impl implDef.axiomFormula
      (bethUniversalPrefix (L.predArity implDef.predQ)
        (FormulaN.neg (bethPredApplied implDef.predQ))))

-- ===================================================================
-- Theorem 6.6.1/6.6.2: ExplicitDefinabilityWitness
-- ===================================================================

/-- Theorem 6.6.1 (required helper): Predicate capturing that a
formula D explicitly defines Q from P_1,...,P_k for the given implDef:
namely, A(P_1,...,P_k,Q) ⊃ ∀x_1...∀x_n (Q(x_1,...,x_n) ≡ D(P_1,...,P_k))
is universally valid, with D's predicates among P_1,...,P_k, free vars
in {x_0,...,x_{n-1}}, and at least one P_i occurring. Used in the
statement of Theorem 6.6.1(a), for languages without equality. -/
@[blueprint "chap6__theorem_6_6_1"]
def ExplicitDefinabilityWitness {L : Language}
    (implDef : ImplicitDefinability L) (D : FormulaN L) : Prop :=
  (∀ v, v ∈ formulaFVN D → v < L.predArity implDef.predQ) ∧
  (∀ p, formulaPredSymbolsEqN D p → p ∈ implDef.preds.syms) ∧
  (∃ p ∈ implDef.preds.syms, formulaPredSymbolsEqN D p) ∧
  universallyValidN
    (FormulaN.impl implDef.axiomFormula
      (bethUniversalPrefix (L.predArity implDef.predQ)
        (FormulaN.equiv (bethPredApplied implDef.predQ) D)))

/-- Theorem 6.6.2(a): implicit definability of Q from the finite list
of distinct ordinary predicates P₁,…,P_k. The closed axiom formula A
may contain equality, which is logical under R-BETH-EQ and is exempt
from the predicate restriction. Implicit definability is validity of
A(P,Q) ∧ A(P,Q′) ⊃ ∀x̄ (Q(x̄) ≡ Q′(x̄)) in the fresh-Q′ expansion. -/
@[blueprint "chap6__theorem_6_6_2"]
structure ImplicitDefinabilityEq (L : Language) : Type 1 where
  /-- The axiom conjunction A(P₁,…,P_k,Q) in the original language -/
  axiomFormula : FormulaN L
  /-- The predicate Q whose definability is investigated -/
  predQ : L.predSymbols
  /-- The rank n > 0 of Q -/
  rankPositive : L.predArity predQ > 0
  /-- The axiom conjunction is closed -/
  axiomsClosed : formulaFVN axiomFormula = ∅
  /-- The finite list of distinct defining predicates -/
  preds : PredList L
  /-- Q is distinct from every listed P_i -/
  predQ_not_in_P : some predQ ∉ preds.syms
  /-- Equality is logical and is not one of the listed P_i -/
  eq_not_in_P : none ∉ preds.syms
  /-- The ordinary predicates of A are among P₁,…,P_k,Q; equality is exempt -/
  axiomFormula_predSyms_in :
    ∀ P, formulaPredSymbolsN axiomFormula P → some P ∈ preds.syms ∨ P = predQ
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

/-- Theorem 6.6.2(a), adopted equality-logical reading (R-BETH-EQ):
D may contain equality, and its ordinary predicate symbols are among
the finite list P₁,…,P_k. The record excludes equality from that list.
There is no requirement that a listed predicate occur in D, so the
empty-list case is included. The free-variable bound and the defining
equivalence under A are the explicit-definability conditions. -/
@[blueprint "chap6__theorem_6_6_2"]
def ExplicitDefinabilityWitnessEq {L : Language}
    (implDef : ImplicitDefinabilityEq L) (D : FormulaN L) : Prop :=
  (∀ v, v ∈ formulaFVN D → v < L.predArity implDef.predQ) ∧
  (∀ P, formulaPredSymbolsN D P → some P ∈ implDef.preds.syms) ∧
  universallyValidN
    (FormulaN.impl implDef.axiomFormula
      (bethUniversalPrefix (L.predArity implDef.predQ)
        (FormulaN.equiv (bethPredApplied implDef.predQ) D)))

-- ===================================================================
-- Theorem 6.6.2 (companion, part b): ImplicitDefinabilityFunc
-- ===================================================================

/-- The arity of a function or constant; constants have arity zero. -/
@[blueprint "chap6__theorem_6_6_2"]
def bethSymbolArity {L : Language} : L.funSymbols ⊕ L.constSymbols → Nat
  | .inl f => L.funArity f
  | .inr _ => 0

/-- Occurrence of the function or constant being defined in a formula. -/
@[blueprint "chap6__theorem_6_6_2"]
def bethSymbolOccurs {L : Language} (A : FormulaN L) :
    L.funSymbols ⊕ L.constSymbols → Prop
  | .inl f => formulaFuncSymbolsN A f
  | .inr c => LCS.CutElim.Interpolation.formulaConstSymbolsN A c

/-- Apply a function to x₀,…,xₙ₋₁, or use a constant directly. -/
@[blueprint "chap6__theorem_6_6_2"]
def bethSymbolTerm {L : Language} : L.funSymbols ⊕ L.constSymbols → Term L
  | .inl f => .func f (fun i => .var i.val)
  | .inr c => .const c

/-- The expansion containing a fresh copy of the selected function or constant. -/
@[blueprint "chap6__theorem_6_6_2"]
def bethSymbolExpansion {L : Language} :
    L.funSymbols ⊕ L.constSymbols → Language
  | .inl f => L.addFun (L.funArity f)
  | .inr _ => L.addConst

/-- Embed a formula in the expansion for the selected symbol. -/
@[blueprint "chap6__theorem_6_6_2"]
def bethLiftSymbolFormula {L : Language} (f : L.funSymbols ⊕ L.constSymbols)
    (A : FormulaN L) : FormulaN (bethSymbolExpansion f) :=
  match f with
  | .inl g => A.liftAddFun (L.funArity g)
  | .inr _ => A.liftAddConst

/-- The copy of A obtained by replacing the selected symbol by its fresh copy. -/
@[blueprint "chap6__theorem_6_6_2"]
noncomputable def bethCopySymbolFormula {L : Language}
    (f : L.funSymbols ⊕ L.constSymbols) (A : FormulaN L) :
    FormulaN (bethSymbolExpansion f) :=
  match f with
  | .inl g => formulaFuncSubstN (some g) none rfl (A.liftAddFun (L.funArity g))
  | .inr c => formulaConstSubstN (some c) none A.liftAddConst

/-- Equality of the original symbol and its fresh copy on the same arguments.
For constants this is c ≐ c′, with no argument tuple. -/
@[blueprint "chap6__theorem_6_6_2"]
def bethSymbolCopyEquality {L : Language} (hEq : L.hasEquality = true)
    (f : L.funSymbols ⊕ L.constSymbols) : FormulaN (bethSymbolExpansion f) :=
  match f with
  | .inl g =>
      .eq_ hEq (.func (some g) (fun i => .var i.val))
        (.func none (fun i => .var i.val))
  | .inr c => .eq_ hEq (.const (some c)) (.const none)

/-- Theorem 6.6.2(b): A function or constant occurring in the closed axiom
formula is implicitly defined when A and its fresh-copy version force
the two symbols to agree in the expansion. Under R-BETH-EQ, equality
is logical, may occur in A, and is excluded from the list P₁,…,P_k. -/
@[blueprint "chap6__theorem_6_6_2"]
structure ImplicitDefinabilityFunc (L : Language) : Type 1 where
  axiomFormula : FormulaN L
  /-- A function symbol or a constant symbol; constants have rank zero -/
  f : L.funSymbols ⊕ L.constSymbols
  /-- The selected symbol occurs in A -/
  occurs : bethSymbolOccurs axiomFormula f
  axiomsClosed : formulaFVN axiomFormula = ∅
  preds : PredList L
  eq_not_in_P : none ∉ preds.syms
  /-- Equality is exempt from this restriction on ordinary predicates -/
  axiomFormula_predSyms_in :
    ∀ P, formulaPredSymbolsN axiomFormula P → some P ∈ preds.syms
  hasEquality : L.hasEquality = true
  /-- Validity is over the expansion with a genuinely fresh copy -/
  validityCondition :
    universallyValidN
      (FormulaN.impl
        (FormulaN.conj (bethLiftSymbolFormula f axiomFormula)
          (bethCopySymbolFormula f axiomFormula))
        (bethUniversalPrefix (bethSymbolArity f)
          (bethSymbolCopyEquality hasEquality f)))

-- ===================================================================
-- Theorem 6.6.2 (companion, part b): ExplicitDefinabilityFunc
-- ===================================================================

-- ATTACH-BLOCKER: unsupported untagged structure
/-- Theorem 6.6.2 (companion, part b): A positive-arity function f is
defined explicitly from P_1,...,P_k by a formula D whose free
variables are among {x_0,...,x_n}, where x_n is the output variable y,
and NOT containing f (or f'),
such that A ⊃ ∀x_1...∀x_n ∀y (f(x_1,...,x_n) = y ≡ D) is valid.
The separate constant-symbol case is not represented by this
`funSymbols` branch. -/
structure ExplicitDefinabilityFunc (L : Language) : Type 1 where
  /-- The axiom conjunction A(P_1,...,P_k,f) -/
  axiomFormula : FormulaN L
  /-- The positive-arity function symbol f being defined -/
  funcF : L.funSymbols
  /-- The rank n > 0 of f -/
  rankPositive : L.funArity funcF > 0
  /-- The fresh copy f' used in the implicit-definability premise -/
  funcF' : L.funSymbols
  /-- f and f' are distinct -/
  funcF'_ne : funcF' ≠ funcF
  /-- f' has the same arity as f -/
  copyArity : L.funArity funcF' = L.funArity funcF
  /-- f' is genuinely new for A(P_1,...,P_k,f) -/
  funcF'_fresh : ¬ formulaFuncSymbolsN axiomFormula funcF'
  /-- STANDING ASSUMPTION #18 (§6.6): axiomFormula is closed -/
  axiomsClosed : formulaFVN axiomFormula = ∅
  /-- The set of allowed defining predicate symbols P_1,...,P_k -/
  predsP : Set L.predSymbols
  /-- The set of allowed defining function symbols (containing neither
      f nor f') -/
  funcsAllowed : Set L.funSymbols
  /-- f is distinct from every allowed function symbol -/
  funcF_not_in_allowed : funcF ∉ funcsAllowed
  /-- f' is distinct from every allowed function symbol -/
  funcF'_not_in_allowed : funcF' ∉ funcsAllowed
  /-- Predicate symbols of A are among P_1,...,P_k -/
  axiomFormula_predSyms_in :
    ∀ P, formulaPredSymbolsN axiomFormula P → P ∈ predsP
  /-- The defining formula D(P_1,...,P_k) -/
  definingFormula : FormulaN L
  /-- Free vars of D are among {x_0,...,x_n}, including the output
      variable y at position funArity in the quantifier prefix. -/
  freeVarRestriction :
    ∀ v, v ∈ formulaFVN definingFormula → v < L.funArity funcF + 1
  /-- Predicate symbols of D are among P_1,...,P_k -/
  definingFormula_predSyms_in :
    ∀ P, formulaPredSymbolsN definingFormula P → P ∈ predsP
  /-- Every function symbol of D is allowed; together with
      `funcF_not_in_allowed` and `funcF'_not_in_allowed`, this encodes
      that D contains neither f nor f'. -/
  definingFormula_funcSyms_in :
    ∀ g, formulaFuncSymbolsN definingFormula g → g ∈ funcsAllowed
  /-- STANDING ASSUMPTION (§6.6): L has equality so we can form `t1 = t2`. -/
  hasEquality : L.hasEquality = true
  /-- The formula A ⊃ ∀x_1...∀x_n ∀y (f(x_1,...,x_n) = y ≡ D) is
      universally valid. -/
  explicitCondition :
    universallyValidN
      (FormulaN.impl axiomFormula
        (bethUniversalPrefix (L.funArity funcF + 1)
          (FormulaN.equiv
            (FormulaN.eq_ hasEquality
              (Term.func funcF (fun i => Term.var i.val))
              (Term.var (L.funArity funcF)))
            definingFormula)))

/-- Theorem 6.6.2(b): D is a formula of the original language whose
ordinary predicates are among P₁,…,P_k and which does not contain the
selected function or constant. Its fresh copy is outside this language.
Under R-BETH-FV, D may use x₀,…,xₙ₋₁ and the output variable y = xₙ.
Under R-BETH-EQ, equality may occur in D. For a constant, the defining
equation is c ≐ y and only y is quantified. -/
@[blueprint "chap6__theorem_6_6_2"]
def ExplicitDefinabilityFuncWitness {L : Language}
    (implDef : ImplicitDefinabilityFunc L) (D : FormulaN L) : Prop :=
  (∀ v, v ∈ formulaFVN D → v < bethSymbolArity implDef.f + 1) ∧
  (∀ P, formulaPredSymbolsN D P → some P ∈ implDef.preds.syms) ∧
  (¬ bethSymbolOccurs D implDef.f) ∧
  universallyValidN
    (FormulaN.impl implDef.axiomFormula
      (bethUniversalPrefix (bethSymbolArity implDef.f + 1)
        (FormulaN.equiv
          (FormulaN.eq_ implDef.hasEquality
            (bethSymbolTerm implDef.f)
            (Term.var (bethSymbolArity implDef.f)))
          D)))

-- ATTACH-BLOCKER: unsupported untagged example
/-- Regression: the standalone explicit-definability API encodes that
its defining formula contains neither f nor its copy f'. -/
example (explicitDef : ExplicitDefinabilityFunc L) :
    (¬ formulaFuncSymbolsN explicitDef.definingFormula
        explicitDef.funcF) ∧
      (¬ formulaFuncSymbolsN explicitDef.definingFormula
        explicitDef.funcF') := by
  constructor
  · intro hOccurs
    exact explicitDef.funcF_not_in_allowed
      (explicitDef.definingFormula_funcSyms_in explicitDef.funcF hOccurs)
  · intro hOccurs
    exact explicitDef.funcF'_not_in_allowed
      (explicitDef.definingFormula_funcSyms_in explicitDef.funcF' hOccurs)

-- ===================================================================
-- Theorem 6.6.2 function-copy API regressions
-- ===================================================================

-- ATTACH-BLOCKER: private declaration
private inductive BethFuncCopyRegressionFunc where
  | original
  | copy
deriving DecidableEq

-- ATTACH-BLOCKER: private declaration
private def bethFuncCopyRegressionLanguage : Language where
  funSymbols := BethFuncCopyRegressionFunc
  funArity := fun _ => 1
  constSymbols := Empty
  predSymbols := Empty
  predArity := Empty.elim
  hasEquality := true

-- ATTACH-BLOCKER: private declaration
private def bethFuncCopyRegressionApp
    (f : bethFuncCopyRegressionLanguage.funSymbols) (x : Nat) :
    Term bethFuncCopyRegressionLanguage :=
  Term.func f (fun _ => Term.var x)

-- ATTACH-BLOCKER: private declaration
/-- Regression fixture: a unary axiom comparing two source-language functions. -/
private def bethFuncCopyRegressionBadA :
    FormulaN bethFuncCopyRegressionLanguage :=
  FormulaN.all 0
    (FormulaN.eq_ rfl
      (bethFuncCopyRegressionApp .original 0)
      (bethFuncCopyRegressionApp .copy 0))

-- ATTACH-BLOCKER: private declaration
/-- Regression fixture: a legitimate unary axiom mentioning only the
original function and forcing it to be the identity. -/
private def bethFuncCopyRegressionGoodA :
    FormulaN bethFuncCopyRegressionLanguage :=
  FormulaN.all 0
    (FormulaN.eq_ rfl
      (bethFuncCopyRegressionApp .original 0)
      (Term.var 0))

-- ATTACH-BLOCKER: private declaration
private theorem bethFuncCopyRegressionBoundSetEmpty :
    ((Set.iUnion (fun _ : Fin 1 => Set.singleton 0) ∪
        Set.singleton 0) \ Set.singleton 0) = (∅ : Set Nat) := by
  funext v
  apply propext
  change
    ((((∃ _ : Fin 1, v = 0) ∨ v = 0) ∧ ¬ v = 0) ↔ False)
  constructor
  · intro h
    rcases h.1 with hi | hv
    · obtain ⟨_, hv⟩ := hi
      exact h.2 hv
    · exact h.2 hv
  · exact False.elim

-- ATTACH-BLOCKER: unsupported untagged example
/-- The source-language symbol named copy occurs in the two-function axiom. -/
example :
    formulaFuncSymbolsN bethFuncCopyRegressionBadA
      BethFuncCopyRegressionFunc.copy := by
  change
    (BethFuncCopyRegressionFunc.copy =
        BethFuncCopyRegressionFunc.original ∨ _) ∨
      (BethFuncCopyRegressionFunc.copy =
        BethFuncCopyRegressionFunc.copy ∨ _)
  exact Or.inr (Or.inl rfl)

-- ATTACH-BLOCKER: unsupported untagged example
/-- The fresh expansion symbol is absent from an embedded source axiom,
even when that axiom uses both source-language function symbols. -/
example :
    ¬ formulaFuncSymbolsN
      (bethFuncCopyRegressionBadA.liftAddFun 1)
      (none : Option bethFuncCopyRegressionLanguage.funSymbols) := by
  simp [bethFuncCopyRegressionBadA, bethFuncCopyRegressionApp,
    FormulaN.liftAddFun, Term.liftAddFun, formulaFuncSymbolsN,
    termFuncSymbolsLocal, Set.union, Set.empty]

-- ATTACH-BLOCKER: unsupported untagged example
/-- The identity-function axiom gives an implicit-definability package
whose comparison function is the fresh none in the expansion. -/
noncomputable example :
    ∃ implDef : ImplicitDefinabilityFunc bethFuncCopyRegressionLanguage,
      implDef.axiomFormula = bethFuncCopyRegressionGoodA ∧
      implDef.f = Sum.inl BethFuncCopyRegressionFunc.original := by
  let implDef : ImplicitDefinabilityFunc bethFuncCopyRegressionLanguage :=
    { axiomFormula := bethFuncCopyRegressionGoodA
      f := .inl .original
      occurs := Or.inl (Or.inl rfl)
      axiomsClosed := by
        simp only [bethFuncCopyRegressionGoodA,
          bethFuncCopyRegressionApp, formulaFVN, termFV]
        exact bethFuncCopyRegressionBoundSetEmpty
      preds := ⟨[], List.nodup_nil, fun h => by cases h⟩
      eq_not_in_P := by simp
      axiomFormula_predSyms_in := fun P => Empty.elim P
      hasEquality := rfl
      validityCondition := by
        intro M s hA
        have hA' :
            (∀ a : M.carrier,
              M.interpFunc (some BethFuncCopyRegressionFunc.original)
                (fun _ => a) = a) ∧
            (∀ a : M.carrier,
              M.interpFunc none (fun _ => a) = a) := by
          simpa [bethLiftSymbolFormula, bethCopySymbolFormula,
            bethFuncCopyRegressionGoodA, bethFuncCopyRegressionApp,
            bethFuncCopyRegressionLanguage, bethSymbolExpansion,
            FormulaN.liftAddFun, Term.liftAddFun, Language.addFun,
            formulaFuncSubstN, termFuncSubstN, formulaEvalN,
            termEval, assignUpdate] using hA
        have hGoal :
            ∀ a : M.carrier,
              M.interpFunc (some BethFuncCopyRegressionFunc.original)
                  (fun _ => a) =
                M.interpFunc none (fun _ => a) :=
          fun a => (hA'.1 a).trans (hA'.2 a).symm
        simpa [bethSymbolArity, bethSymbolCopyEquality, bethSymbolExpansion,
          bethFuncCopyRegressionLanguage, Language.addFun, bethUniversalPrefix,
          formulaEvalN, termEval, assignUpdate, List.foldr] using hGoal }
  exact ⟨implDef, rfl, rfl⟩

end LCS.CutElim.Beth
end

