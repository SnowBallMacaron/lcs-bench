import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Syntax.Algebra
import Attach
import LCS.FirstOrder.Gentzen.SignedFormulae.ProofsStamp

/-! # FirstOrder.Gentzen.SignedFormulae
    Formalization of Chapter 5, Sections 5.4.4-5.4.5.
    Signed formulae, type-a/b/c/d classification, term algebras,
    language reducts and expansions.
    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.FirstOrder.Gentzen.SignedFormulae

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen

-- ===================================================================
-- Definition 5.4.3: First-order signed formulae (normalized, FormulaN)
-- ===================================================================

/-- Definition 5.6.1 (companion): A signed formula over FormulaN, for any
    equality flag. Signed formulae in §5.6.1 admit equality atoms. -/
@[blueprint "chap5__definition_5_6_1"]
inductive SignedFormula (L : Language) : Type where
  | trueF : FormulaN L → SignedFormula L
  | falseF : FormulaN L → SignedFormula L

/-- Definition 5.4.3: Signed formulae over a language without equality. -/
@[blueprint "chap5__definition_5_4_3"]
abbrev SignedFormulaNoEq (L : Language) (hL : L.withoutEquality) := SignedFormula L

namespace SignedFormula

/-- Definition 5.6.1 (companion): Satisfaction of a signed formula, for any
    equality flag. T A is satisfied when A holds under (M, s), and F A when
    A does not hold. The formula A may contain equality atoms. -/
@[blueprint "chap5__definition_5_6_1"]
def satisfiedBy {L : Language} (M : Structure L)
    (s : Assignment M) : SignedFormula L → Prop
  | .trueF A => formulaEvalN M A s
  | .falseF A => ¬ formulaEvalN M A s

/-- Definition 5.4.4: Satisfaction of a signed formula over a language
    without equality: T A holds iff A holds, and F A holds iff A does not. -/
@[blueprint "chap5__definition_5_4_4" (main := true)]
def satisfiedByNoEq {L : Language} (hL : L.withoutEquality) (M : Structure L)
    (s : Assignment M) (A : SignedFormulaNoEq L hL) : Prop :=
  satisfiedBy M s A

/-- Definition 5.4.7 (companion): The conjugate of a signed formula. -/
@[blueprint "chap5__definition_5_4_7"]
def conjugate {L : Language} : SignedFormula L → SignedFormula L
  | .trueF A => .falseF A
  | .falseF A => .trueF A

end SignedFormula

-- ===================================================================
-- Definition 5.4.3 (companion type): Type-A signed formulae
-- ===================================================================

/-- Definition 5.6.1 (companion): Type-A signed formulae, for any equality
    flag: T(X ∧ Y), F(X ∨ Y), F(X ⊃ Y), T(¬X), and F(¬X).
    The constituent formulae may contain equality atoms. -/
@[blueprint "chap5__definition_5_6_1"]
inductive TypeA (L : Language) : Type where
  | tConj : FormulaN L → FormulaN L → TypeA L
  | fDisj : FormulaN L → FormulaN L → TypeA L
  | fImpl : FormulaN L → FormulaN L → TypeA L
  | tNeg : FormulaN L → TypeA L
  | fNeg : FormulaN L → TypeA L

/-- Definition 5.4.3: Type-A signed formulae over a language without equality. -/
@[blueprint "chap5__definition_5_4_3" (main := true)]
abbrev TypeANoEq (L : Language) (hL : L.withoutEquality) := TypeA L

namespace TypeA

/-- Definition 5.4.3 (companion): Converts a type-A formula to its corresponding
signed formula. -/
@[blueprint "chap5__definition_5_6_1"]
def toSigned {L : Language} : TypeA L → SignedFormula L
  | tConj X Y => .trueF (.conj X Y)
  | fDisj X Y => .falseF (.disj X Y)
  | fImpl X Y => .falseF (.impl X Y)
  | tNeg X => .trueF (.neg X)
  | fNeg X => .falseF (.neg X)

/-- Definition 5.4.3 (companion): The first component A1 of a type-A formula. -/
@[blueprint "chap5__definition_5_6_1"]
def comp1 {L : Language} : TypeA L → SignedFormula L
  | tConj X _ => .trueF X
  | fDisj X _ => .falseF X
  | fImpl X _ => .trueF X
  | tNeg X => .falseF X
  | fNeg X => .trueF X

/-- Definition 5.4.3 (companion): The second component A2 of a type-A formula. -/
@[blueprint "chap5__definition_5_6_1"]
def comp2 {L : Language} : TypeA L → SignedFormula L
  | tConj _ Y => .trueF Y
  | fDisj _ Y => .falseF Y
  | fImpl _ Y => .falseF Y
  | tNeg X => .falseF X
  | fNeg X => .trueF X

end TypeA

-- ===================================================================
-- Definition 5.4.3 (companion type): Type-B signed formulae
-- ===================================================================

/-- Definition 5.6.1 (companion): Type-B signed formulae, for any equality
    flag: F(X ∧ Y), T(X ∨ Y), and T(X ⊃ Y).
    The constituent formulae may contain equality atoms. -/
@[blueprint "chap5__definition_5_6_1"]
inductive TypeB (L : Language) : Type where
  | fConj : FormulaN L → FormulaN L → TypeB L
  | tDisj : FormulaN L → FormulaN L → TypeB L
  | tImpl : FormulaN L → FormulaN L → TypeB L

/-- Definition 5.4.3: Type-B signed formulae over a language without equality. -/
@[blueprint "chap5__definition_5_4_3" (main := true)]
abbrev TypeBNoEq (L : Language) (hL : L.withoutEquality) := TypeB L

namespace TypeB

/-- Definition 5.4.3 (companion): Converts a type-B formula to its corresponding
signed formula. -/
@[blueprint "chap5__definition_5_6_1"]
def toSigned {L : Language} : TypeB L → SignedFormula L
  | fConj X Y => .falseF (.conj X Y)
  | tDisj X Y => .trueF (.disj X Y)
  | tImpl X Y => .trueF (.impl X Y)

/-- Definition 5.4.3 (companion): The first component B1 of a type-B formula. -/
@[blueprint "chap5__definition_5_6_1"]
def comp1 {L : Language} : TypeB L → SignedFormula L
  | fConj X _ => .falseF X
  | tDisj X _ => .trueF X
  | tImpl X _ => .falseF X

/-- Definition 5.4.3 (companion): The second component B2 of a type-B formula. -/
@[blueprint "chap5__definition_5_6_1"]
def comp2 {L : Language} : TypeB L → SignedFormula L
  | fConj _ Y => .falseF Y
  | tDisj _ Y => .trueF Y
  | tImpl _ Y => .trueF Y

end TypeB

-- ===================================================================
-- Definition 5.4.3 (companion type): Type-C signed formulae
-- ===================================================================

/-- Definition 5.6.1 (companion): Type-C signed formulae, for any equality
    flag: T(∀x X) and F(∃x X). The body may contain equality atoms. -/
@[blueprint "chap5__definition_5_6_1"]
inductive TypeC (L : Language) : Type where
  | tAll : Nat → FormulaN L → TypeC L
  | fEx : Nat → FormulaN L → TypeC L

/-- Definition 5.4.3: Type-C signed formulae over a language without equality. -/
@[blueprint "chap5__definition_5_4_3" (main := true)]
abbrev TypeCNoEq (L : Language) (hL : L.withoutEquality) := TypeC L

namespace TypeC

/-- Definition 5.4.3 (companion): Converts a type-C formula to its corresponding
signed formula. -/
@[blueprint "chap5__definition_5_6_1"]
def toSigned {L : Language} : TypeC L → SignedFormula L
  | tAll x Y => .trueF (.all x Y)
  | fEx x Y => .falseF (.ex x Y)

/-- Definition 5.4.3 (companion): The bound variable of a type-C formula. -/
@[blueprint "chap5__definition_5_6_1"]
def var {L : Language} : TypeC L → Nat
  | tAll x _ | fEx x _ => x

/-- Definition 5.4.3 (companion): The quantified body of a type-C formula. -/
@[blueprint "chap5__definition_5_6_1"]
def body {L : Language} : TypeC L → FormulaN L
  | tAll _ Y | fEx _ Y => Y

/-- Definition 5.4.3 (companion): The component C(t), for a term t free
for the bound variable in the quantified body. -/
@[blueprint "chap5__definition_5_6_1"]
def comp {L : Language} (c : TypeC L) (t : Term L)
    (_h : isFreeForN t c.var c.body) : SignedFormula L :=
  match c with
  | tAll x Y => .trueF (formulaSubstN Y t x)
  | fEx x Y => .falseF (formulaSubstN Y t x)

end TypeC

-- ===================================================================
-- Definition 5.4.3 (companion type): Type-D signed formulae
-- ===================================================================

/-- Definition 5.6.1 (companion): Type-D signed formulae, for any equality
    flag: T(∃x X) and F(∀x X). The body may contain equality atoms. -/
@[blueprint "chap5__definition_5_6_1"]
inductive TypeD (L : Language) : Type where
  | tEx : Nat → FormulaN L → TypeD L
  | fAll : Nat → FormulaN L → TypeD L

/-- Definition 5.4.3: Type-D signed formulae over a language without equality. -/
@[blueprint "chap5__definition_5_4_3" (main := true)]
abbrev TypeDNoEq (L : Language) (hL : L.withoutEquality) := TypeD L

namespace TypeD

/-- Definition 5.4.3 (companion): Converts a type-D formula to its corresponding
signed formula. -/
@[blueprint "chap5__definition_5_6_1"]
def toSigned {L : Language} : TypeD L → SignedFormula L
  | tEx x Y => .trueF (.ex x Y)
  | fAll x Y => .falseF (.all x Y)

/-- Definition 5.4.3 (companion): The bound variable of a type-D formula. -/
@[blueprint "chap5__definition_5_6_1"]
def var {L : Language} : TypeD L → Nat
  | tEx x _ | fAll x _ => x

/-- Definition 5.4.3 (companion): The quantified body of a type-D formula. -/
@[blueprint "chap5__definition_5_6_1"]
def body {L : Language} : TypeD L → FormulaN L
  | tEx _ Y | fAll _ Y => Y

/-- Definition 5.4.3 (companion): The component D(t), for a term t free
for the bound variable in the quantified body. -/
@[blueprint "chap5__definition_5_6_1"]
def comp {L : Language} (c : TypeD L) (t : Term L)
    (_h : isFreeForN t c.var c.body) : SignedFormula L :=
  match c with
  | tEx x Y => .trueF (formulaSubstN Y t x)
  | fAll x Y => .falseF (formulaSubstN Y t x)

end TypeD

-- ===================================================================
-- Definition 5.4.5: Term algebra
-- ===================================================================

/-- Definition 5.4.5: Given a first-order language L, a nonempty set H of
terms in TERM_L is a term algebra iff: (i) For every n-ary function symbol f in L (n > 0), for any terms t1,...,tn in H, f t1...tn is also in H. (ii) Every constant symbol c in L is also in H. -/
@[blueprint "chap5__definition_5_4_5" (main := true)]
structure IsTermAlgebra (L : Language) (H : Set (Term L)) : Prop where
  /-- The set H is nonempty -/
  nonempty : ∃ t, t ∈ H
  /-- Closure under function symbols: for every function symbol f,
      if all argument terms are in H, then func f ts is in H -/
  closedFunc : ∀ (f : L.funSymbols) (ts : Fin (L.funArity f) → Term L),
    (∀ i, ts i ∈ H) → Term.func f ts ∈ H
  /-- Every constant symbol is in H -/
  closedConst : ∀ (c : L.constSymbols), Term.const c ∈ H

/-- Definition 5.4.5 (remark, "term algebras are algebras"): A nonempty
set H of terms is a term algebra exactly when the constant and function
constructors restrict to operations on the subtype of terms in H. -/
@[blueprint "chap5__definition_5_4_5"]
theorem isTermAlgebra_iff_constructorOperations
    {L : Language} (H : Set (Term L)) (hH : ∃ t, H t) :
    IsTermAlgebra L H ↔
      ∃ (constH : L.constSymbols → {t : Term L // H t})
        (funcH : (f : L.funSymbols) →
          (Fin (L.funArity f) → {t : Term L // H t}) →
          {t : Term L // H t}),
        (∀ c, (constH c).val = Term.const c) ∧
        ∀ f ts,
          (funcH f ts).val = Term.func f (fun i => (ts i).val) 

/-- Definition 5.4.5 (remark): A nonempty term algebra closed under a
positive-arity function symbol cannot be covered by a finite tuple of terms. -/
@[blueprint "chap5__definition_5_4_5"]
theorem termAlgebra_infinite {L : Language} {H : Set (Term L)}
    (f : L.funSymbols) (hf : 0 < L.funArity f) (hH : IsTermAlgebra L H) :
    ¬ ∃ (n : Nat) (e : Fin n → Term L), ∀ t ∈ H, ∃ i, e i = t 



-- ATTACH-BLOCKER: unsupported untagged structure
/-- Definition 5.4.5 (companion, generated): A generated term algebra is a term
algebra H that is additionally closed under sub-terms. -/
structure IsGeneratedTermAlgebra (L : Language) (H : Set (Term L))
    extends IsTermAlgebra L H where
  /-- Sub-term closure: if func f ts is in H, then each ts i is in H -/
  closedSubterm : ∀ (f : L.funSymbols) (ts : Fin (L.funArity f) → Term L),
    Term.func f ts ∈ H → ∀ i, ts i ∈ H

-- ===================================================================
-- Definition 5.4.6: Language reduct
-- ===================================================================

/-- Definition 5.4.6 (companion): Function symbols occurring in a term,
including the outer function symbol of every application. -/
@[blueprint "chap5__definition_5_4_6"]
def termFunSyms {L : Language} : Term L → Set L.funSymbols
  | .var _ => ∅
  | .const _ => ∅
  | .func f ts => fun g => g = f ∨ ∃ i, g ∈ termFunSyms (ts i)

/-- Definition 5.4.6 (companion): Constant symbols occurring in a term. -/
@[blueprint "chap5__definition_5_4_6"]
def termConstSyms {L : Language} (t : Term L) : Set L.constSymbols :=
  fun c => Term.const c ∈ termConstsList t

/-- Definition 5.4.6 (companion): Function symbols occurring in a normalized
formula, including the terms on both sides of an equality atom. -/
@[blueprint "chap5__definition_5_4_6"]
def formulaFunSymsN {L : Language} : FormulaN L → Set L.funSymbols
  | .predN _ ts => fun f => ∃ i, f ∈ termFunSyms (ts i)
  | .eq_ _ t u => termFunSyms t ∪ termFunSyms u
  | .neg A => formulaFunSymsN A
  | .conj A B => formulaFunSymsN A ∪ formulaFunSymsN B
  | .disj A B => formulaFunSymsN A ∪ formulaFunSymsN B
  | .impl A B => formulaFunSymsN A ∪ formulaFunSymsN B
  | .all _ A => formulaFunSymsN A
  | .ex _ A => formulaFunSymsN A

/-- Definition 5.4.6 (companion): Constant symbols occurring in a normalized formula. -/
@[blueprint "chap5__definition_5_4_6"]
def formulaConstSymsN {L : Language} (A : FormulaN L) : Set L.constSymbols :=
  fun c => Term.const c ∈ formulaConstsList A

/-- Definition 5.4.6 (companion): Predicate symbols occurring in a normalized
formula. Equality is represented by the language flag, not a predicate symbol. -/
@[blueprint "chap5__definition_5_4_6"]
def formulaPredSymsN {L : Language} : FormulaN L → Set L.predSymbols
  | .predN P _ => fun Q => Q = P
  | .eq_ _ _ _ => ∅
  | .neg A => formulaPredSymsN A
  | .conj A B => formulaPredSymsN A ∪ formulaPredSymsN B
  | .disj A B => formulaPredSymsN A ∪ formulaPredSymsN B
  | .impl A B => formulaPredSymsN A ∪ formulaPredSymsN B
  | .all _ A => formulaPredSymsN A
  | .ex _ A => formulaPredSymsN A

/-- Definition 5.4.6 (companion): Function symbols occurring in a signed set. -/
@[blueprint "chap5__definition_5_4_6"]
def signedSetFunSyms {L : Language} (S : Set (SignedFormula L)) : Set L.funSymbols :=
  fun f => ∃ sf ∈ S, match sf with
    | .trueF A => f ∈ formulaFunSymsN A
    | .falseF A => f ∈ formulaFunSymsN A

/-- Definition 5.4.6 (companion): Constant symbols occurring in a signed set. -/
@[blueprint "chap5__definition_5_4_6"]
def signedSetConstSyms {L : Language} (S : Set (SignedFormula L)) : Set L.constSymbols :=
  fun c => ∃ sf ∈ S, match sf with
    | .trueF A => c ∈ formulaConstSymsN A
    | .falseF A => c ∈ formulaConstSymsN A

/-- Definition 5.4.6 (companion): Predicate symbols occurring in a signed set. -/
@[blueprint "chap5__definition_5_4_6"]
def signedSetPredSyms {L : Language} (S : Set (SignedFormula L)) : Set L.predSymbols :=
  fun P => ∃ sf ∈ S, match sf with
    | .trueF A => P ∈ formulaPredSymsN A
    | .falseF A => P ∈ formulaPredSymsN A

/-- Definition 5.4.7 (companion): Syntactic occurrence of a term as itself
or as a subterm at any depth in a function argument. -/
@[blueprint "chap5__definition_5_4_7"]
inductive TermOccursIn {L : Language} : Term L → Term L → Prop where
  | self (t : Term L) : TermOccursIn t t
  | arg {t : Term L} (f : L.funSymbols) (ts : Fin (L.funArity f) → Term L)
      (i : Fin (L.funArity f)) : TermOccursIn t (ts i) → TermOccursIn t (.func f ts)

/-- Definition 5.4.7 (companion): Term occurrence in a normalized formula,
including subterms of atomic arguments and occurrences under quantifiers. -/
@[blueprint "chap5__definition_5_4_7"]
def termOccursInFormulaN {L : Language} (t : Term L) : FormulaN L → Prop
  | .predN _ ts => ∃ i, TermOccursIn t (ts i)
  | .eq_ _ r u => TermOccursIn t r ∨ TermOccursIn t u
  | .neg A => termOccursInFormulaN t A
  | .conj A B => termOccursInFormulaN t A ∨ termOccursInFormulaN t B
  | .disj A B => termOccursInFormulaN t A ∨ termOccursInFormulaN t B
  | .impl A B => termOccursInFormulaN t A ∨ termOccursInFormulaN t B
  | .all _ A => termOccursInFormulaN t A
  | .ex _ A => termOccursInFormulaN t A

/-- Definition 5.4.7 (companion): Term occurrence in a signed formula,
independent of its sign. -/
@[blueprint "chap5__definition_5_4_7"]
def occursIn {L : Language} (t : Term L) : SignedFormula L → Prop
  | .trueF A => termOccursInFormulaN t A
  | .falseF A => termOccursInFormulaN t A

/-- Definition 5.4.6: L is a reduct of L' if L's constants, functions, and
predicates are injectively embedded into L' with compatible arities. -/
@[blueprint "chap5__definition_5_4_6" (main := true)]
structure IsLanguageReduct (L L' : Language) where
  /-- Injective embedding of constant symbols -/
  constEmbed : L.constSymbols → L'.constSymbols
  /-- The constant embedding is injective -/
  constInj : Function.Injective constEmbed
  /-- Injective embedding of function symbols -/
  funEmbed : L.funSymbols → L'.funSymbols
  /-- The function embedding is injective -/
  funInj : Function.Injective funEmbed
  /-- Function arities are compatible -/
  funArityCompat : ∀ f, L'.funArity (funEmbed f) = L.funArity f
  /-- Injective embedding of predicate symbols -/
  predEmbed : L.predSymbols → L'.predSymbols
  /-- The predicate embedding is injective -/
  predInj : Function.Injective predEmbed
  /-- Predicate arities are compatible -/
  predArityCompat : ∀ P, L'.predArity (predEmbed P) = L.predArity P
attribute [blueprint "chap5__definition_5_4_6"] _root_.LCS.FirstOrder.Gentzen.SignedFormulae.IsLanguageReduct.predArityCompat

attribute [blueprint "chap5__definition_5_4_6"] _root_.LCS.FirstOrder.Gentzen.SignedFormulae.IsLanguageReduct.funArityCompat


/-- Definition 5.4.6 (iii): The language L_S contains exactly the constants,
functions, and predicates occurring in S, with the arities and equality flag of L. -/
@[blueprint "chap5__definition_5_4_6" (main := true)]
def reductLanguage (L : Language) (S : Set (SignedFormula L)) : Language where
  funSymbols := { f : L.funSymbols // f ∈ signedSetFunSyms S }
  funArity := fun f => L.funArity f.val
  constSymbols := { c : L.constSymbols // c ∈ signedSetConstSyms S }
  predSymbols := { P : L.predSymbols // P ∈ signedSetPredSyms S }
  predArity := fun P => L.predArity P.val
  hasEquality := L.hasEquality

/-- Definition 5.4.6 (companion): The occurrence language L_S is a reduct
of L via the subtype inclusions. -/
@[blueprint "chap5__definition_5_4_6"]
def reductLanguage_isReduct (L : Language) (S : Set (SignedFormula L)) :
    IsLanguageReduct (reductLanguage L S) L where
  constEmbed := Subtype.val
  constInj := fun _ _ h => Subtype.ext h
  funEmbed := Subtype.val
  funInj := fun _ _ h => Subtype.ext h
  funArityCompat := fun _ => rfl
  predEmbed := Subtype.val
  predInj := fun _ _ h => Subtype.ext h
  predArityCompat := fun _ => rfl

-- ===================================================================
-- Definition 5.4.7: Term algebra over the occurrence language
-- ===================================================================

/-- Definition 5.4.7 (companion): A nonempty set of ambient terms is a term
algebra over L_S when its symbols occur in S and it is closed under precisely
those function and constant symbols. -/
@[blueprint "chap5__definition_5_4_7"]
structure IsTermAlgebraOver (L : Language) (S : Set (SignedFormula L))
    (H : Set (Term L)) : Prop where
  /-- The algebra has at least one term. -/
  nonempty : ∃ t, t ∈ H
  /-- Every symbol in a member term belongs to the occurrence language. -/
  symbols : ∀ t ∈ H,
    termFunSyms t ⊆ signedSetFunSyms S ∧ termConstSyms t ⊆ signedSetConstSyms S
  /-- Closure under the function symbols occurring in S. -/
  closedFunc : ∀ (f : L.funSymbols), f ∈ signedSetFunSyms S →
    ∀ (ts : Fin (L.funArity f) → Term L),
      (∀ i, ts i ∈ H) → Term.func f ts ∈ H
  /-- Every constant occurring in S belongs to the algebra. -/
  closedConst : ∀ (c : L.constSymbols), c ∈ signedSetConstSyms S → Term.const c ∈ H

-- retained: used by LCS.FirstOrder.Completeness.InfiniteSearch
/-- All terms using only the function and constant symbols of S form a
term algebra over the occurrence language L_S. -/
theorem occurrenceTerms_isTermAlgebraOver {L : Language} (S : Set (SignedFormula L)) :
    IsTermAlgebraOver L S (fun t => termFunSyms t ⊆ signedSetFunSyms S ∧
      termConstSyms t ⊆ signedSetConstSyms S) := by
  refine { nonempty := ?_, symbols := fun _ h => h, closedFunc := ?_, closedConst := ?_ }
  · exact ⟨Term.var 0, fun _ h => h.elim, fun _ h => by cases h⟩
  · intro f hf ts hts
    constructor
    · intro g hg
      rcases hg with rfl | ⟨i, hi⟩
      · exact hf
      · exact (hts i).1 g hi
    · intro c hc
      change Term.const c ∈ termConstsList (.func f ts) at hc
      simp only [termConstsList, ← List.flatMap_eq_foldl, List.mem_flatMap, List.mem_ofFn] at hc
      obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hc
      exact (hts i).2 c hi
  · intro c hc
    exact ⟨fun _ h => h.elim, fun d hd => by
      have he : d = c := Term.const.inj (List.mem_singleton.mp hd)
      exact he ▸ hc⟩



-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Constants in a function application occur in one of its arguments. -/
theorem termConstSyms_func_iff {L : Language} (f : L.funSymbols)
    (ts : Fin (L.funArity f) → Term L) (c : L.constSymbols) :
    c ∈ termConstSyms (.func f ts) ↔ ∃ i, c ∈ termConstSyms (ts i) := by
  change Term.const c ∈ termConstsList (.func f ts) ↔ _
  simp only [termConstsList, ← List.flatMap_eq_foldl, List.mem_flatMap, List.mem_ofFn]
  constructor
  · rintro ⟨i, ⟨j, rfl⟩, h⟩
    exact ⟨j, h⟩
  · rintro ⟨i, h⟩
    exact ⟨i, ⟨i, rfl⟩, h⟩

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Every symbol of an occurring subterm occurs in the containing term. -/
theorem TermOccursIn.symbols {L : Language} {t u : Term L} (h : TermOccursIn t u) :
    termFunSyms t ⊆ termFunSyms u ∧ termConstSyms t ⊆ termConstSyms u := by
  induction h with
  | self => exact ⟨fun _ h => h, fun _ h => h⟩
  | arg f ts i _ ih =>
    exact ⟨fun g hg => Or.inr ⟨i, ih.1 g hg⟩,
      fun c hc => (termConstSyms_func_iff f ts c).mpr ⟨i, ih.2 c hc⟩⟩

-- retained: used by LCS.FirstOrder.Equality.Part2, LCS.FirstOrder.Gentzen.Hintikka.Model.Proofs
/-- Every symbol of a term occurring in a formula occurs in that formula. -/
theorem termOccursInFormulaN_symbols {L : Language} {t : Term L} (A : FormulaN L)
    (h : termOccursInFormulaN t A) :
    termFunSyms t ⊆ formulaFunSymsN A ∧ termConstSyms t ⊆ formulaConstSymsN A := by
  induction A with
  | predN P ts =>
    obtain ⟨i, hi⟩ := h
    refine ⟨fun f hf => ⟨i, hi.symbols.1 f hf⟩, ?_⟩
    intro c hc
    change Term.const c ∈ formulaConstsList (.predN P ts)
    simp only [formulaConstsList, ← List.flatMap_eq_foldl, List.mem_flatMap, List.mem_ofFn]
    exact ⟨i, ⟨i, rfl⟩, hi.symbols.2 c hc⟩
  | eq_ hEq r u =>
    rcases h with h | h
    · exact ⟨fun f hf => Or.inl (h.symbols.1 f hf),
        fun c hc => List.mem_append_left _ (h.symbols.2 c hc)⟩
    · exact ⟨fun f hf => Or.inr (h.symbols.1 f hf),
        fun c hc => List.mem_append_right _ (h.symbols.2 c hc)⟩
  | neg A ih => exact ih h
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
    rcases h with h | h
    · exact ⟨fun f hf => Or.inl ((ihA h).1 f hf),
        fun c hc => List.mem_append_left _ ((ihA h).2 c hc)⟩
    · exact ⟨fun f hf => Or.inr ((ihB h).1 f hf),
        fun c hc => List.mem_append_right _ ((ihB h).2 c hc)⟩
  | all _ A ih => exact ih h
  | ex _ A ih => exact ih h





-- ===================================================================
-- Definition 5.4.6 (companion): Structure reduct
-- ===================================================================

/-- Definition 5.4.6: An L-structure M is a reduct of an L'-structure M' if
they share a domain and L-symbol interpretations agree via the embedding. -/
@[blueprint "chap5__definition_5_4_6" (main := true)]
structure IsStructureReduct {L L' : Language} (hR : IsLanguageReduct L L')
    (M : Structure L) (M' : Structure L') : Prop where
  /-- The domains are equal -/
  sameDomain : M.carrier = M'.carrier
  /-- Constant interpretations are compatible via the embedding -/
  constCompat : ∀ c,
    M'.interpConst (hR.constEmbed c) =
    cast (by rw [sameDomain]) (M.interpConst c)
  /-- Function interpretations are compatible via the embedding -/
  funcCompat : ∀ (f : L.funSymbols)
    (args : Fin (L.funArity f) → M'.carrier),
    M'.interpFunc (hR.funEmbed f)
      (hR.funArityCompat f ▸ args) =
    cast (by rw [sameDomain])
      (M.interpFunc f (fun i =>
        cast (by rw [sameDomain]) (args i)))
  /-- Predicate interpretations are compatible via the embedding -/
  predCompat : ∀ (P : L.predSymbols)
    (args : Fin (L.predArity P) → M'.carrier),
    M'.interpPred (hR.predEmbed P)
      (hR.predArityCompat P ▸ args) ↔
    M.interpPred P (fun i =>
      cast (by rw [sameDomain]) (args i))
attribute [blueprint "chap5__definition_5_4_6"] _root_.LCS.FirstOrder.Gentzen.SignedFormulae.IsStructureReduct.sameDomain



/-- Definition 5.4.6 (companion): Embed terms along a language reduct. -/
@[blueprint "chap5__definition_5_4_6"]
def Term.mapReduct {L L' : Language} (hR : IsLanguageReduct L L') : Term L → Term L'
  | .var x => .var x
  | .const c => .const (hR.constEmbed c)
  | .func f ts => .func (hR.funEmbed f)
      (fun i => Term.mapReduct hR (ts (Fin.cast (hR.funArityCompat f) i)))

/-- Definition 5.4.6 (companion): Embed formulae along a language reduct
whose target language admits equality whenever the source does. -/
@[blueprint "chap5__definition_5_4_6"]
def FormulaN.mapReduct {L L' : Language} (hR : IsLanguageReduct L L')
    (hEq : L.hasEquality = true → L'.hasEquality = true) : FormulaN L → FormulaN L'
  | .predN P ts => .predN (hR.predEmbed P)
      (fun i => Term.mapReduct hR (ts (Fin.cast (hR.predArityCompat P) i)))
  | .eq_ h t u => .eq_ (hEq h) (Term.mapReduct hR t) (Term.mapReduct hR u)
  | .neg A => .neg (FormulaN.mapReduct hR hEq A)
  | .conj A B => .conj (FormulaN.mapReduct hR hEq A) (FormulaN.mapReduct hR hEq B)
  | .disj A B => .disj (FormulaN.mapReduct hR hEq A) (FormulaN.mapReduct hR hEq B)
  | .impl A B => .impl (FormulaN.mapReduct hR hEq A) (FormulaN.mapReduct hR hEq B)
  | .all x A => .all x (FormulaN.mapReduct hR hEq A)
  | .ex x A => .ex x (FormulaN.mapReduct hR hEq A)

/-- Proof of Definition 5.4.6 (Note): Every structure of a reduct language
has an expansion on the same nonempty carrier. Symbols outside the embedding
receive arbitrary interpretations. -/
@[blueprint "chap5__definition_5_4_6"]
theorem exists_structureExpansion {L L' : Language} (hR : IsLanguageReduct L L')
    (M : Structure L) : ∃ M' : Structure L', IsStructureReduct hR M M' 

/-- Proof of Definition 5.4.6 (Note, formulae): Satisfaction agrees between
a structure and its expansion for transported formulae and assignments,
provided equality in the source language is available in the target. -/
@[blueprint "chap5__definition_5_4_6"]
theorem formulaEvalN_mapReduct {L L' : Language} {hR : IsLanguageReduct L L'}
    (hEq : L.hasEquality = true → L'.hasEquality = true)
    {M : Structure L} {M' : Structure L'} (h : IsStructureReduct hR M M')
    (A : FormulaN L) (s : Assignment M) :
    formulaEvalN M' (FormulaN.mapReduct hR hEq A) (fun x => cast h.sameDomain (s x)) ↔
      formulaEvalN M A s 

-- ===================================================================
-- Definition 5.4.4 (companion): Signed set satisfaction
-- ===================================================================

namespace SignedSet

/-- Definition 5.6.1 (companion, set extension): A set of signed formulae,
    for any equality flag, is satisfied by (M, s) iff every member is
    satisfied by (M, s). Its formulae may contain equality atoms. -/
@[blueprint "chap5__definition_5_6_1"]
def satisfiedBy {L : Language} (M : Structure L)
    (s : Assignment M) (S : Set (SignedFormula L)) : Prop :=
  ∀ sf, sf ∈ S → SignedFormula.satisfiedBy M s sf

end SignedSet

-- ===================================================================
-- Helper: Substitution-evaluation for ground (closed) terms
-- ===================================================================





-- ===================================================================
-- Lemma 5.4.4: Type-c universal satisfaction and type-d existential
-- ===================================================================

/-- Proof of Lemma 5.4.4 (companion): Naming constants have no free variables
and are free for every variable. -/
@[blueprint "chap5__lemma_5_4_4"]
theorem namingConst_freeForN {L : Language} {D : Type} (a : D)
    (x : Nat) (A : FormulaN (extendedLanguage L D)) :
    isFreeForN (namingConst a) x A 





/-- Proof of Lemma 5.4.4 (i): Over a language without equality, a type-c
    formula is satisfied iff all its naming-constant components are satisfied. -/
@[blueprint "chap5__lemma_5_4_4" (main := true)]
theorem typeC_satisfaction_iffNoEq {L : Language} (hL : L.withoutEquality)
    (S : Structure L) (s : Assignment (extendedInterp S))
    (C : TypeC (extendedLanguage L S.carrier)) :
    SignedFormula.satisfiedBy (extendedInterp S) s (TypeC.toSigned C) ↔
    ∀ a : S.carrier,
      SignedFormula.satisfiedBy (extendedInterp S) s
        (TypeC.comp C (namingConst a) (namingConst_freeForN a C.var C.body)) 

/-- Proof of Lemma 5.4.4 (ii): Over a language without equality, a type-d
    formula is satisfied iff some naming-constant component is satisfied. -/
@[blueprint "chap5__lemma_5_4_4" (main := true)]
theorem typeD_satisfaction_iffNoEq {L : Language} (hL : L.withoutEquality)
    (S : Structure L) (s : Assignment (extendedInterp S))
    (D : TypeD (extendedLanguage L S.carrier)) :
    SignedFormula.satisfiedBy (extendedInterp S) s (TypeD.toSigned D) ↔
    ∃ a : S.carrier,
      SignedFormula.satisfiedBy (extendedInterp S) s
        (TypeD.comp D (namingConst a) (namingConst_freeForN a D.var D.body)) 

-- ===================================================================
-- Free variables of a signed formula
-- ===================================================================

/-- Definition 5.4.7 (companion): The set of free variables of a signed
formula. -/
@[blueprint "chap5__definition_5_4_7"]
def signedFormulaFreeVars {L : Language} : SignedFormula L → Set Nat
  | .trueF A => formulaFVN A
  | .falseF A => formulaFVN A

/-- Definition 5.4.7 (companion): Variables free in at least one member
of a signed set. -/
@[blueprint "chap5__definition_5_4_7"]
def signedSetFreeVars {L : Language} (S : Set (SignedFormula L)) : Set Nat :=
  fun x => ∃ sf ∈ S, x ∈ signedFormulaFreeVars sf

end LCS.FirstOrder.Gentzen.SignedFormulae
