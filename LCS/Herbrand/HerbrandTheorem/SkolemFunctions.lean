import LCS.Item
import LCS.CutElim.Hauptsatz
import LCS.Util
import LCS.FirstOrder.Semantics.Subformulae
import LCS.Herbrand.PrenexForm
import LCS.Herbrand.SharpenedHauptsatz.Theorem
import LCS.CutElim.Interpolation.Equality
import LCS.Herbrand.HerbrandTheorem.Preliminaries
import Attach
import LCS.Herbrand.HerbrandTheorem.SkolemFunctions.ProofsStamp

/-! # Herbrand.HerbrandTheorem.SkolemFunctions
    Chapter 7, Section 5.2: Skolem function and constant symbols.

    Definition 7.5.1 (Skolem function and constant symbols for the universal
    quantifier occurrences of prenex formulae, with the extended language),
    Definition 7.5.2 (functional form of a prenex sequent), and the Warning
    on the validity/satisfiability duality of Skolemization.

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.HerbrandTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.CutElim.LK
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen
open LCS.CutElim.Interpolation.Equality

/-- An occurrence in a sentence's outermost-first universal prefix, including
vacuous binders. Sentence positions distinguish occurrences across Γ. -/
@[blueprint "chap7__definition_7_5_1"]
structure UniversalPrefixOccurrence {L : Language} (Γ : List (FormulaN L)) where
  sentence : Fin Γ.length
  position : Fin (prenexPrefix (Γ.get sentence)).length
  universal : ((prenexPrefix (Γ.get sentence)).get position).1 = .universal

/-- Ordered existential binders strictly above this universal occurrence. -/
@[blueprint "chap7__definition_7_5_1"]
def UniversalPrefixOccurrence.dependencies {L : Language}
    {Γ : List (FormulaN L)} (o : UniversalPrefixOccurrence Γ) : List Nat :=
  ((prenexPrefix (Γ.get o.sentence)).take o.position.val).filterMap fun
    | (.existential, x) => some x
    | (.universal, _) => none

/-- Positive-dependency universal occurrences index the new function symbols. -/
@[blueprint "chap7__definition_7_5_1"]
def ValiditySkolemFunction {L : Language} (Γ : List (FormulaN L)) :=
  {o : UniversalPrefixOccurrence Γ // 0 < o.dependencies.length}

/-- Zero-dependency universal occurrences index the new constant symbols. -/
@[blueprint "chap7__definition_7_5_1"]
def ValiditySkolemConstant {L : Language} (Γ : List (FormulaN L)) :=
  {o : UniversalPrefixOccurrence Γ // o.dependencies.length = 0}

/-- Definition 7.5.1: extend all of L by disjoint families indexed by sentence
and universal occurrence. Existing symbols, ranks, predicates and equality are
preserved. New functions have positive rank; zero dependencies give constants. -/
@[blueprint "chap7__definition_7_5_1"]
def validitySkolemLanguage {L : Language} (Γ : List (FormulaN L)) : Language where
  funSymbols := Sum L.funSymbols (ValiditySkolemFunction Γ)
  funArity := fun
    | .inl f => L.funArity f
    | .inr o => o.val.dependencies.length
  constSymbols := Sum L.constSymbols (ValiditySkolemConstant Γ)
  predSymbols := L.predSymbols
  predArity := L.predArity
  hasEquality := L.hasEquality

/-- Definition 7.5.1: allocation on a normalized prenex input sequent.
The indexed extension and its symbol assignments are determined by Γ;
there is one new symbol per universal occurrence, even for a vacuous binder. -/
@[blueprint "chap7__definition_7_5_1" (main := true)]
structure ValiditySkolemAllocation {L : Language} (Γ : List (FormulaN L)) : Type where
  inputConvention : HerbrandInputConvention Γ
  prenex : ∀ A ∈ Γ, isPrenex A

/-- The Skolem term uses all ordered existential dependencies as arguments,
and uses the constant constructor exactly when there are no dependencies. -/
@[blueprint "chap7__definition_7_5_2"]
def ValiditySkolemAllocation.term {L : Language} {Γ : List (FormulaN L)}
    (_allocation : ValiditySkolemAllocation Γ) (o : UniversalPrefixOccurrence Γ) :
    Term (validitySkolemLanguage Γ) :=
  if h : o.dependencies.length = 0 then
    .const (.inr ⟨o, h⟩)
  else
    .func (.inr ⟨o, Nat.pos_of_ne_zero h⟩)
      (fun i => .var (o.dependencies.get i))

/-- Canonical allocation for a normalized prenex input; no symbol supply in L
is needed, since the extension contains the occurrence-indexed new symbols. -/
@[blueprint "chap7__definition_7_5_1"]
def mkValiditySkolemAllocation {L : Language} (Γ : List (FormulaN L))
    (hΓ : HerbrandInputConvention Γ) (hPrenex : ∀ A ∈ Γ, isPrenex A) :
    ValiditySkolemAllocation Γ :=
  ⟨hΓ, hPrenex⟩

-- ===================================================================
-- Definition 7.5.1: SkolemData
-- ===================================================================

/-- Definition 7.5.1: canonical allocation for the normalized prenex sequent Γ.
Every universal occurrence indexes a distinct new function or constant in an
extension of all of L; its rank is determined by its existential dependencies. -/
@[blueprint "chap7__definition_7_5_1" (main := true)]
abbrev SkolemData (L : Language) (Γ : List (FormulaN L)) :=
  ValiditySkolemAllocation Γ

-- ===================================================================
-- Definition 7.5.1 (companion def): mkSkolemData
-- ===================================================================

/-- Canonical Skolem data for the globally renamed input Γ. -/
def mkSkolemData {L : Language} (Γ : List (FormulaN L))
    (hΓ : HerbrandInputConvention Γ) (hPrenex : ∀ A ∈ Γ, isPrenex A) :
    SkolemData L Γ :=
  mkValiditySkolemAllocation Γ hΓ hPrenex

/-- Integrity of the source convention and prenex domain; occurrence identity,
rank and dependency order are fixed by the indexed representation. -/
@[blueprint "chap7__definition_7_5_1"]
def SkolemData.WellFormed {L : Language} {Γ : List (FormulaN L)}
    (_sd : SkolemData L Γ) : Prop :=
  HerbrandInputConvention Γ ∧ ∀ A ∈ Γ, isPrenex A

/-- Embed every original term into the validity-Skolem signature extension. -/
@[blueprint "chap7__definition_7_5_1"]
def liftValidityTerm {L : Language} (Γ : List (FormulaN L)) :
    Term L → Term (validitySkolemLanguage Γ)
  | .var x => .var x
  | .const c => .const (.inl c)
  | .func f ts => .func (.inl f) (fun i => liftValidityTerm Γ (ts i))

/-- Embed a source formula, preserving its connectives, binders and predicates. -/
@[blueprint "chap7__definition_7_5_1"]
def liftValidityFormula {L : Language} (Γ : List (FormulaN L)) :
    FormulaN L → FormulaN (validitySkolemLanguage Γ)
  | .predN P ts => .predN P (fun i => liftValidityTerm Γ (ts i))
  | .eq_ h t u => .eq_ h (liftValidityTerm Γ t) (liftValidityTerm Γ u)
  | .neg A => .neg (liftValidityFormula Γ A)
  | .conj A B => .conj (liftValidityFormula Γ A) (liftValidityFormula Γ B)
  | .disj A B => .disj (liftValidityFormula Γ A) (liftValidityFormula Γ B)
  | .impl A B => .impl (liftValidityFormula Γ A) (liftValidityFormula Γ B)
  | .all x A => .all x (liftValidityFormula Γ A)
  | .ex x A => .ex x (liftValidityFormula Γ A)

-- ===================================================================
-- Definition 7.5.2 (companion def): skolemTerm
-- ===================================================================

/-- Definition 7.5.2: the term allocated to the universal occurrence `o` in Γ.
Zero dependencies give `Term.const`; positive dependencies give `Term.func`
with the existential variables strictly above `o`, in outermost-first order.
The function rank and argument-vector length are both definitionally the length
of this same dependency list, including existential binders unused in the matrix. -/
@[blueprint "chap7__definition_7_5_2"]
def skolemTerm {L : Language} {Γ : List (FormulaN L)}
    (sd : SkolemData L Γ) (o : UniversalPrefixOccurrence Γ) :
    Term (validitySkolemLanguage Γ) := sd.term o

/-- Definition 7.5.2: functional form of the selected sentence of Γ in its
allocated extension. `sd` carries `HerbrandInputConvention Γ` and prenexness.
Every step is indexed by a position in the original sentence's full prefix;
its symbol and dependencies are therefore independent of the shrinking body.
The right fold starts with the embedded matrix, substitutes the allocated term
at each universal, and reconstructs each existential. Thus all universals,
including vacuous ones, are removed and existential order is preserved.
Global binder distinctness ensures that each inserted term's existential
variables are captured only by their original enclosing existential binders. -/
@[blueprint "chap7__definition_7_5_2"]
def functionalForm {L : Language} {Γ : List (FormulaN L)}
    (sd : SkolemData L Γ) (j : Fin Γ.length) :
    FormulaN (validitySkolemLanguage Γ) :=
  let prefix_ := prenexPrefix (Γ.get j)
  (List.ofFn (fun p : Fin prefix_.length => p)).foldr (fun p body =>
    match h : (prefix_.get p).1 with
    | .universal => formulaSubstN body (skolemTerm sd ⟨j, p, h⟩) (prefix_.get p).2
    | .existential => .ex (prefix_.get p).2 body)
    (liftValidityFormula Γ (prenexMatrix (Γ.get j)))

/-- Definition 7.5.2: apply the single allocation indexed by Γ to every source
sentence, in sequent order. All results share `validitySkolemLanguage Γ`, so
symbols from different sentences retain their distinct occurrence identities.
For an empty input sequent, the resulting list is empty. -/
@[blueprint "chap7__definition_7_5_2" (main := true)]
def functionalFormSequent {L : Language} {Γ : List (FormulaN L)}
    (sd : SkolemData L Γ) : List (FormulaN (validitySkolemLanguage Γ)) :=
  List.ofFn (functionalForm sd)

end LCS.Herbrand.HerbrandTheorem
