import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.CutElim.CompletenessBridge
import LCS.CutElim.LKe
import LCS.CutElim.Interpolation
import LCS.FirstOrder.Syntax
import LCS.FirstOrder.Semantics
import LCS.CutElim.Beth.Definability
import Attach
import LCS.CutElim.Beth.WithEquality.ProofsStamp

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

-- ===================================================================
-- Theorem 6.6.2 (companion, part a): beth_with_equality_part_a
-- ===================================================================
/-- Theorem 6.6.2 (companion, part a): Implicit definability of a
predicate implies explicit definability under the adopted equality-logical
reading R-BETH-EQ: D may contain equality, including when the P-list is empty.

STANDING ASSUMPTION #12 (§5.6): Theorem 6.6.2 is for first-order
languages WITH equality; encoded by `L.hasEquality = true`. -/
theorem beth_with_equality_part_a
    (L : Language)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (hEq : L.hasEquality = true)
    (implDef : ImplicitDefinabilityEq L) :
    ∃ D : FormulaN L, ExplicitDefinabilityWitnessEq implDef D :=
-- BEGIN PROOF
by
  -- REPAIR(T6-58): proof pending
  sorry

-- ===================================================================
-- Theorem 6.6.2 (companion, part b): beth_with_equality_part_b
-- ===================================================================
/-- Theorem 6.6.2 (companion, part b): Implicit definability of a
function or constant occurring in A implies explicit definability.

STANDING ASSUMPTION #12 (§5.6): Theorem 6.6.2 is for first-order
languages WITH equality; encoded by `L.hasEquality = true`. -/
theorem beth_with_equality_part_b
    (L : Language)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (hEq : L.hasEquality = true)
    (implDef : ImplicitDefinabilityFunc L) :
    ∃ D : FormulaN L, ExplicitDefinabilityFuncWitness implDef D :=
-- BEGIN PROOF
by
  -- Use equality interpolation in the selected symbol's fresh expansion
  -- and lower the defining formula to L, retaining the output variable y.
  -- REPAIR(T6-57c): proof pending
  sorry

-- ===================================================================
-- Theorem 6.6.2: beth_definability_with_equality
-- ===================================================================
/-- Theorem 6.6.2: (Beth's definability theorem, with equality)
(a) Implicit definability of a predicate implies explicit
definability under R-BETH-EQ, allowing equality in D and an empty P-list.
(b) Implicit definability of a function or constant
occurring in A implies explicit definability.

STANDING ASSUMPTION #12 (§5.6): Theorem 6.6.2 is for first-order
languages WITH equality; encoded by `L.hasEquality = true`. -/
@[blueprint "chap6__theorem_6_6_2" (main := true)]
theorem beth_definability_with_equality
    (L : Language)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (hEq : L.hasEquality = true) :
    (∀ implDef : ImplicitDefinabilityEq L,
      ∃ D : FormulaN L, ExplicitDefinabilityWitnessEq implDef D) ∧
    (∀ implDef : ImplicitDefinabilityFunc L,
      ∃ D : FormulaN L, ExplicitDefinabilityFuncWitness implDef D) 

end LCS.CutElim.Beth
end
