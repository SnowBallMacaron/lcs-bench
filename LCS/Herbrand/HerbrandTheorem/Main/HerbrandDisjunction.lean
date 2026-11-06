import LCS.Item
import LCS.Util
import LCS.Herbrand.HerbrandTheorem
import Attach
import LCS.Herbrand.HerbrandTheorem.Main.HerbrandDisjunction.ProofsStamp

/-! # Herbrand.HerbrandTheorem.Main.HerbrandDisjunction
    Chapter 7, Section 5.4: the notions in the statement of Theorem 7.5.1.

    Quantifier-free substitution instances of the matrices of the functional
    form, ground terms over the language of the symbols of the sequent and its
    Skolem symbols (with the special constant # when there are no constants),
    sequences of substitution pairs, and the Herbrand disjunction they define.

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.HerbrandTheorem.Main
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.HerbrandTheorem
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.CutElim.LK
open LCS.CutElim.LKe.Equivalence

/-- Theorem 7.5.1 (companion def): Predicate asserting that the substitution instance sigma(B) is quantifier-free: FirstOrder.SemanticsN.isQuantifierFree (applyFormula sigma B). -/
@[blueprint "chap7__theorem_7_5_1"]
def IsQuantifierFreeSubstInstance {L : Language}
    (B : FormulaN L) (sigma : Substitution L) : Prop :=
  FirstOrder.SemanticsN.isQuantifierFree
    (Substitution.applyFormula sigma B)

-- ===================================================================
-- Theorem 7.5.1 (companion def): IsGroundTerm
-- ===================================================================

/-- Theorem 7.5.1 (companion def): Predicate asserting that a term t is a ground term (contains no variables — all leaves are constants). The Herbrand-language constraint (symbols of t must occur in Gamma / Skolem symbols of its functional form) is imposed separately by `IsGroundTermOverHerbrandLang`. -/
@[blueprint "chap7__theorem_7_5_1"]
def IsGroundTerm {L : Language} : Term L → Prop
  | .var _ => False
  | .const _ => True
  | .func _ ts => ∀ i, IsGroundTerm (ts i)

/-- Theorem 7.5.1 (companion def): Collects all constant symbols occurring
    in a term. Delegates to the identical Ch6 definition to avoid
    maintenance duplication. -/
@[blueprint "chap7__theorem_7_5_1"]
def termConstSymbols {L : Language} (t : Term L) : Set L.constSymbols :=
  LCS.CutElim.Interpolation.termConstSymbols t

/-- Theorem 7.5.1 (companion def): Collects all function symbols occurring
    in a term. -/
@[blueprint "chap7__theorem_7_5_1"]
def termFuncSymbols {L : Language} : Term L → Set L.funSymbols
  | .var _ => ∅
  | .const _ => ∅
  | .func f ts => fun g => g = f ∨ ∃ i, termFuncSymbols (ts i) g

/-- Theorem 7.5.1 (companion def): Collects all constant symbols occurring
    in a formula (recursing through subformulae and subterms). -/
@[blueprint "chap7__theorem_7_5_1"]
def fmlaConstSymbols {L : Language} : FormulaN L → Set L.constSymbols
  | .predN _ ts => fun c => ∃ i, termConstSymbols (ts i) c
  | .eq_ _ t1 t2 => termConstSymbols t1 ∪ termConstSymbols t2
  | .conj A B => fmlaConstSymbols A ∪ fmlaConstSymbols B
  | .disj A B => fmlaConstSymbols A ∪ fmlaConstSymbols B
  | .impl A B => fmlaConstSymbols A ∪ fmlaConstSymbols B
  | .neg A => fmlaConstSymbols A
  | .all _ A => fmlaConstSymbols A
  | .ex _ A => fmlaConstSymbols A

/-- Theorem 7.5.1 (companion def): Collects all function symbols occurring
    in a formula. -/
@[blueprint "chap7__theorem_7_5_1"]
def fmlaFuncSymbols {L : Language} : FormulaN L → Set L.funSymbols
  | .predN _ ts => fun f => ∃ i, termFuncSymbols (ts i) f
  | .eq_ _ t1 t2 => termFuncSymbols t1 ∪ termFuncSymbols t2
  | .conj A B => fmlaFuncSymbols A ∪ fmlaFuncSymbols B
  | .disj A B => fmlaFuncSymbols A ∪ fmlaFuncSymbols B
  | .impl A B => fmlaFuncSymbols A ∪ fmlaFuncSymbols B
  | .neg A => fmlaFuncSymbols A
  | .all _ A => fmlaFuncSymbols A
  | .ex _ A => fmlaFuncSymbols A

/-- Theorem 7.5.1 (companion def): Collects all constant symbols occurring
    in any formula of a list (i.e., all constants from Gamma). -/
@[blueprint "chap7__theorem_7_5_1"]
def listConstSymbols {L : Language}
    (gamma : List (FormulaN L)) : Set L.constSymbols :=
  fun c => ∃ A ∈ gamma, fmlaConstSymbols A c

/-- Theorem 7.5.1 (companion def): Collects all function symbols occurring
    in any formula of a list. -/
@[blueprint "chap7__theorem_7_5_1"]
def listFuncSymbols {L : Language}
    (gamma : List (FormulaN L)) : Set L.funSymbols :=
  fun f => ∃ A ∈ gamma, fmlaFuncSymbols A f

-- ===================================================================
-- Theorem 7.5.1 (companion def): IsGroundTermOverHerbrandLang
-- ===================================================================

/-- The witness signature extends the canonical validity-Skolem signature by
one distinguished constant #. Old symbols and all ranks are preserved; # is
disjoint from every old and occurrence-indexed Skolem constant. -/
@[blueprint "chap7__theorem_7_5_1"]
def herbrandWitnessLanguage {L : Language} (gamma : List (FormulaN L)) : Language :=
  extendedLanguage (validitySkolemLanguage gamma) Unit

/-- Embed a validity-Skolem formula into the constant-completed witness signature.
The existing term embedding preserves functions and maps constants injectively. -/
@[blueprint "chap7__theorem_7_5_1"]
def liftHerbrandFormula {L : Language} {gamma : List (FormulaN L)} :
    FormulaN (validitySkolemLanguage gamma) → FormulaN (herbrandWitnessLanguage gamma)
  | .predN P ts => .predN P (fun i => LCS.FirstOrder.Semantics.Substitution.liftTerm (ts i))
  | .eq_ h t u => .eq_ h (LCS.FirstOrder.Semantics.Substitution.liftTerm t)
      (LCS.FirstOrder.Semantics.Substitution.liftTerm u)
  | .conj A B => .conj (liftHerbrandFormula A) (liftHerbrandFormula B)
  | .disj A B => .disj (liftHerbrandFormula A) (liftHerbrandFormula B)
  | .impl A B => .impl (liftHerbrandFormula A) (liftHerbrandFormula B)
  | .neg A => .neg (liftHerbrandFormula A)
  | .all x A => .all x (liftHerbrandFormula A)
  | .ex x A => .ex x (liftHerbrandFormula A)

/-- Formulae determining the occurring-symbol language: the embedded original
sequent together with its functional form under the same canonical allocation. -/
@[blueprint "chap7__theorem_7_5_1"]
def herbrandSymbolSources {L : Language} {gamma : List (FormulaN L)}
    (sd : SkolemData L gamma) : List (FormulaN (validitySkolemLanguage gamma)) :=
  gamma.map (liftValidityFormula gamma) ++ functionalFormSequent sd

/-- The occurring original-plus-Skolem language needs a grounding constant
exactly when it has no ground term. This also accounts for nullary functions. -/
@[blueprint "chap7__theorem_7_5_1"]
def HerbrandGroundingNeeded {L : Language} {gamma : List (FormulaN L)}
    (sd : SkolemData L gamma) : Prop :=
  ¬ ∃ t : Term (validitySkolemLanguage gamma), IsGroundTerm t ∧
    (∀ c, termConstSymbols t c → listConstSymbols (herbrandSymbolSources sd) c) ∧
    (∀ f, termFuncSymbols t f → listFuncSymbols (herbrandSymbolSources sd) f)

/-- The chosen grounding constant: `some c` selects an ambient constant of L;
`none` selects the adjoined #. The choice is shared by the whole witness sequence. -/
@[blueprint "chap7__theorem_7_5_1"]
def herbrandGroundingConstant {L : Language} {gamma : List (FormulaN L)} :
    Option L.constSymbols → (herbrandWitnessLanguage gamma).constSymbols
  | some c => .inl (.inl c)
  | none => .inr ()

/-- Ground terms over original-occurring and Skolem-occurring symbols in the
actual witness extension. If that occurring language has no ground term, the
single chosen ambient constant or # is also admitted, as in SQ039. Arbitrary
unused ambient symbols and unused allocated Skolem symbols are not admitted. -/
@[blueprint "chap7__theorem_7_5_1"]
def IsGroundTermOverHerbrandLang {L : Language} {gamma : List (FormulaN L)}
    (sd : SkolemData L gamma) (seed : Option L.constSymbols)
    (t : Term (herbrandWitnessLanguage gamma)) : Prop :=
  IsGroundTerm t ∧
  (∀ c, termConstSymbols t c →
    (∃ d, c = Sum.inl d ∧ listConstSymbols (herbrandSymbolSources sd) d) ∨
    (HerbrandGroundingNeeded sd ∧ c = herbrandGroundingConstant seed)) ∧
  (∀ f, termFuncSymbols t f → listFuncSymbols (herbrandSymbolSources sd) f)

-- ===================================================================
-- Theorem 7.5.1 (companion def): IsConstructibleFromFunctionalForm
-- ===================================================================

/-- The ordered existential variables of the original prenex prefix, including
vacuous binders. Tuple positions refer to this list before matrix restriction. -/
@[blueprint "chap7__theorem_7_5_1"]
def existentialPrefixVariables {L : Language} (A : FormulaN L) : List Nat :=
  (prenexPrefix A).filterMap fun
    | (.existential, x) => some x
    | (.universal, _) => none

/-- A finite ordered sequence of source-associated full-prefix term tuples.
Every occurrence stores its source index and one term for every existential
binder of that source, including vacuous ones. Groundness and admissibility are
certified by IsConstructibleFromFunctionalForm. Repetitions, empty sequences
and unused source sentences are allowed; no provenance is inferred from matrices. -/
@[blueprint "chap7__theorem_7_5_1"]
structure SubstitutionPairSeq {L : Language} (gamma : List (FormulaN L)) : Type where
  /-- One shared ambient/adjoined grounding constant. -/
  seed : Option L.constSymbols
  /-- Number of witness occurrences, with order and multiplicity retained. -/
  length : Nat
  /-- Explicit source sentence of each witness occurrence. -/
  source : Fin length → Fin gamma.length
  /-- Complete tuple in the original existential-prefix order. -/
  terms : (i : Fin length) →
    Fin (existentialPrefixVariables (gamma.get (source i))).length →
      Term (herbrandWitnessLanguage gamma)

/-- The matrix of the functional form of the stored source, under the common
allocation. Coincident matrices never erase the stored source association. -/
@[blueprint "chap7__theorem_7_5_1"]
def SubstitutionPairSeq.matrices {L : Language} {gamma : List (FormulaN L)}
    (sps : SubstitutionPairSeq gamma) (sd : SkolemData L gamma)
    (i : Fin sps.length) : FormulaN (herbrandWitnessLanguage gamma) :=
  prenexMatrix (liftHerbrandFormula (functionalForm sd (sps.source i)))

/-- Assign the complete tuple to all original existential-prefix variables;
variables outside this prefix keep their own variable terms. Vacuous assignments
are retained here, before the separate matrix restriction. -/
@[blueprint "chap7__theorem_7_5_1"]
def SubstitutionPairSeq.prefixAssignment {L : Language} {gamma : List (FormulaN L)}
    (sps : SubstitutionPairSeq gamma) (i : Fin sps.length) :
    Substitution (herbrandWitnessLanguage gamma) :=
  let xs := existentialPrefixVariables (gamma.get (sps.source i))
  fun x => (List.ofFn (fun k : Fin xs.length => k)).foldr
    (fun k rest => if xs.get k = x then sps.terms i k else rest) (.var x)

/-- The formula substitution is the full-prefix assignment restricted to the
actual free variables of the associated functional-form matrix. -/
@[blueprint "chap7__theorem_7_5_1"]
def SubstitutionPairSeq.substitutions {L : Language} {gamma : List (FormulaN L)}
    (sps : SubstitutionPairSeq gamma) (sd : SkolemData L gamma)
    (i : Fin sps.length) : Substitution (herbrandWitnessLanguage gamma) :=
  Substitution.restrictToFormula (sps.prefixAssignment i) (sps.matrices sd i)

/-- The associated ordered Herbrand sequent. Every entry uses its stored source
and complete tuple, restricting the assignment only at the matrix application.
The finite list retains repetitions and has no coverage requirement on Γ. -/
@[blueprint "chap7__theorem_7_5_1"]
def HerbrandDisjunction {L : Language} {gamma : List (FormulaN L)}
    (sd : SkolemData L gamma) (sps : SubstitutionPairSeq gamma) :
    Sequent (herbrandWitnessLanguage gamma) :=
  { antecedent := []
    succedent := List.ofFn (fun i =>
      Substitution.applyFormula (sps.substitutions sd i) (sps.matrices sd i)) }

/-- Source-associated constructibility: all entries of every full-prefix tuple
are ground in the common witness language, including entries for vacuous binders.
The unrestricted prefix assignment has its proof-local domain; only its matrix
restriction must satisfy the general formula substitution admissibility rules. -/
@[blueprint "chap7__theorem_7_5_1"]
def IsConstructibleFromFunctionalForm {L : Language}
    (gamma : List (FormulaN L)) (sps : SubstitutionPairSeq gamma)
    (sd : SkolemData L gamma) : Prop :=
  ∀ i : Fin sps.length,
    (∀ k, IsGroundTermOverHerbrandLang sd sps.seed (sps.terms i k)) ∧
    Substitution.IsExistentialPrefixAssignment (sps.prefixAssignment i)
      (liftHerbrandFormula (liftValidityFormula gamma (gamma.get (sps.source i)))) ∧
    FirstOrder.SemanticsN.isQuantifierFree (sps.matrices sd i) ∧
    Substitution.Admissible (sps.substitutions sd i) (sps.matrices sd i) ∧
    IsQuantifierFreeSubstInstance (sps.matrices sd i) (sps.substitutions sd i)

-- ===================================================================
-- Theorem 7.5.1 (companion def): SkolemTermOrder
-- ===================================================================

/-- Theorem 7.5.1 (companion def): The partial ordering on the set HT of Skolem terms used in the converse direction of Herbrand's theorem: t1 < t2 iff t1 is a proper subterm of t2 within the Herbrand term universe. Defines a well-founded partial order on ground Skolem terms. -/
@[blueprint "chap7__example_7_5_3"]
def isProperSubterm {L : Language} :
    Term L → Term L → Prop
  | _, .var _ => False
  | _, .const _ => False
  | t, .func _ ts =>
    (∃ i, ts i = t) ∨ (∃ i, isProperSubterm t (ts i))

end LCS.Herbrand.HerbrandTheorem.Main
