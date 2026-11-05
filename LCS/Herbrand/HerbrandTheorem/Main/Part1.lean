import LCS.Item
import LCS.Util
import LCS.Herbrand.HerbrandTheorem
import Attach
import LCS.Herbrand.HerbrandTheorem.Main.Part1.ProofsStamp

section
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
-- Theorem 7.5.1 (companion def): IsMatrixOfExistentialSentence
-- ===================================================================

/-- Theorem 7.5.1 (companion def): Predicate asserting that B is the quantifier-free matrix of some sentence exists x_1 ... exists x_k B occurring in the given formula list (the functional form of Gamma). B is quantifier-free and there exist existential variables such that the corresponding existential sentence appears in the list. -/
@[blueprint "chap7__theorem_7_5_1"]
def IsMatrixOfExistentialSentence {L : Language}
    (B : FormulaN L) (functionalFormGamma : List (FormulaN L)) :
    Prop :=
  FirstOrder.SemanticsN.isQuantifierFree B ∧
  ∃ A ∈ functionalFormGamma, prenexMatrix A = B ∧
    ∀ p ∈ prenexPrefix A, p.1 = QuantifierKind.existential

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

/-- The set of ground witness terms for the source-associated allocation and
chosen grounding constant, in the canonical Skolem extension completed by #. -/
@[blueprint "chap7__theorem_7_5_1"]
def herbrandLanguageSymbols {L : Language} {gamma : List (FormulaN L)}
    (sd : SkolemData L gamma) (seed : Option L.constSymbols) :
    Set (Term (herbrandWitnessLanguage gamma)) :=
  fun t => IsGroundTermOverHerbrandLang sd seed t

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



-- ===================================================================
-- Theorem 7.5.1 (companion def): folkProofTreeAllRightEigenvariables
-- ===================================================================



-- ===================================================================
-- Theorem 7.5.1 (companion def): skolemSubstForEigenvariables
-- ===================================================================



-- ===================================================================
-- Example 7.5.3 (companion type): HerbrandExFunc
-- ===================================================================

/-- Example 7.5.3 (companion type): Unary Skolem function symbols f
    and g for the Herbrand theorem example. -/
@[blueprint "chap7__example_7_5_3"]
inductive HerbrandExFunc : Type where
  /-- Unary Skolem function f -/
  | f : HerbrandExFunc
  /-- Unary Skolem function g -/
  | g : HerbrandExFunc

-- ===================================================================
-- Example 7.5.3 (companion type): HerbrandExConst
-- ===================================================================

/-- Example 7.5.3 (companion type): Skolem constant a for the
    Herbrand theorem example. -/
@[blueprint "chap7__example_7_5_3"]
inductive HerbrandExConst : Type where
  /-- Skolem constant a -/
  | a : HerbrandExConst

-- ===================================================================
-- Example 7.5.3 (companion type): HerbrandExPred
-- ===================================================================

/-- Example 7.5.3 (companion type): Binary predicates P and Q for the
    Herbrand theorem example. -/
@[blueprint "chap7__example_7_5_3"]
inductive HerbrandExPred : Type where
  /-- Binary predicate P -/
  | P : HerbrandExPred
  /-- Binary predicate Q -/
  | Q : HerbrandExPred

-- ===================================================================
-- Example 7.5.3 (companion def): herbrandExLang
-- ===================================================================

/-- Example 7.5.3 (companion def): An extended language with binary predicates P, Q, Skolem function symbols f (unary), g (unary), and Skolem constant a. This is the Herbrand language for the example. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExLang : Language where
  funSymbols := HerbrandExFunc
  funArity := fun
    | .f => 1
    | .g => 1
  constSymbols := HerbrandExConst
  predSymbols := HerbrandExPred
  predArity := fun _ => 2

-- ===================================================================
-- Example 7.5.3: herbrandExampleSequent
-- ===================================================================

/-- Example 7.5.3: The original prenex sequent -> exists x forall y not P(x,y), exists y_1 forall z not Q(y_1,z), forall x_1 exists y_2 exists z_1(P(x_1,y_2) and Q(y_2,z_1)). Variables: x=0, y=1, y_1=2, z=3, x_1=4, y_2=5, z_1=6. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExampleSequent : Sequent herbrandExLang :=
  let mkP (a b : Term herbrandExLang) :=
    FormulaN.predN HerbrandExPred.P (vec2 a b)
  let mkQ (a b : Term herbrandExLang) :=
    FormulaN.predN HerbrandExPred.Q (vec2 a b)
  -- exists x forall y not P(x, y)
  let f1 := FormulaN.ex 0
    (FormulaN.all 1
      (FormulaN.neg (mkP (Term.var 0) (Term.var 1))))
  -- exists y_1 forall z not Q(y_1, z)
  let f2 := FormulaN.ex 2
    (FormulaN.all 3
      (FormulaN.neg (mkQ (Term.var 2) (Term.var 3))))
  -- forall x_1 exists y_2 exists z_1(P(x_1,y_2) and Q(y_2,z_1))
  let f3 := FormulaN.all 4
    (FormulaN.ex 5
      (FormulaN.ex 6
        (FormulaN.conj
          (mkP (Term.var 4) (Term.var 5))
          (mkQ (Term.var 5) (Term.var 6)))))
  { antecedent := []
    succedent := [f1, f2, f3] }

-- ===================================================================
-- Example 7.5.3 (companion def): herbrandExFunctionalForm
-- ===================================================================

/-- Example 7.5.3 (companion def): The functional form -> exists x not P(x, f(x)), exists y_1 not Q(y_1, g(y_1)), exists y_2 exists z_1(P(a, y_2) and Q(y_2, z_1)), obtained from the original sequent by Skolemization (replacing universally bound variables with Skolem terms and deleting universal quantifiers). -/
@[blueprint "chap7__example_7_5_3" (main := true)]
def herbrandExFunctionalForm : Sequent herbrandExLang :=
  let mkP (a b : Term herbrandExLang) :=
    FormulaN.predN HerbrandExPred.P (vec2 a b)
  let mkQ (a b : Term herbrandExLang) :=
    FormulaN.predN HerbrandExPred.Q (vec2 a b)
  let fx := Term.func HerbrandExFunc.f (fun _ => Term.var 0)
  let gy1 := Term.func HerbrandExFunc.g (fun _ => Term.var 2)
  let a := Term.const HerbrandExConst.a
  -- exists x not P(x, f(x))
  let f1 := FormulaN.ex 0
    (FormulaN.neg (mkP (Term.var 0) fx))
  -- exists y_1 not Q(y_1, g(y_1))
  let f2 := FormulaN.ex 2
    (FormulaN.neg (mkQ (Term.var 2) gy1))
  -- exists y_2 exists z_1(P(a, y_2) and Q(y_2, z_1))
  let f3 := FormulaN.ex 5
    (FormulaN.ex 6
      (FormulaN.conj
        (mkP a (Term.var 5))
        (mkQ (Term.var 5) (Term.var 6))))
  { antecedent := []
    succedent := [f1, f2, f3] }

-- ===================================================================
-- Example 7.5.3 (companion def): herbrandExDisjunction
-- ===================================================================

/-- Example 7.5.3 (companion def): The Herbrand disjunction -> not P(a, f(a)), not Q(f(a), g(f(a))), P(a, f(a)) and Q(f(a), g(f(a))), obtained from the functional form by substituting ground terms for existentially bound variables and deleting remaining quantifiers. This is the provable sequent H. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExDisjunction : Sequent herbrandExLang :=
  let mkP (a b : Term herbrandExLang) :=
    FormulaN.predN HerbrandExPred.P (vec2 a b)
  let mkQ (a b : Term herbrandExLang) :=
    FormulaN.predN HerbrandExPred.Q (vec2 a b)
  let a := Term.const HerbrandExConst.a
  let fa := Term.func HerbrandExFunc.f (fun _ => a)
  let gfa := Term.func HerbrandExFunc.g (fun _ => fa)
  -- not P(a, f(a))
  let g1 := FormulaN.neg (mkP a fa)
  -- not Q(f(a), g(f(a)))
  let g2 := FormulaN.neg (mkQ fa gfa)
  -- P(a, f(a)) and Q(f(a), g(f(a)))
  let g3 := FormulaN.conj (mkP a fa) (mkQ fa gfa)
  { antecedent := []
    succedent := [g1, g2, g3] }

-- ===================================================================
-- Example 7.5.3 (companion def): herbrandExTermSetHT
-- ===================================================================

/-- Example 7.5.3 (companion def): The Herbrand term set HT = [a, f(a), g(f(a))], the list of ground Skolem terms appearing in the Herbrand disjunction. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExTermSetHT : List (Term herbrandExLang) :=
  let a := Term.const HerbrandExConst.a
  let fa := Term.func HerbrandExFunc.f (fun _ => a)
  let gfa := Term.func HerbrandExFunc.g (fun _ => fa)
  [a, fa, gfa]

-- ===================================================================
-- Example 7.5.3 (companion def): herbrandExHTOrder
-- ===================================================================

/-- Example 7.5.3 (companion def): The partial ordering on HT: a < f(a), a < g(f(a)), f(a) < g(f(a)), determined by the subterm relation on Skolem terms. Defined concretely using isProperSubterm. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExHTOrder :
    Term herbrandExLang → Term herbrandExLang → Prop :=
  fun t1 t2 => isProperSubterm t1 t2

-- ===================================================================
-- Example 7.5.3 (companion def): herbrandExMaximalElements
-- ===================================================================



-- ===================================================================
-- Example 7.5.3 (companion def): herbrandExProofReconstructionOrder
-- ===================================================================

/-- Example 7.5.3 (companion def): The order in which exists:right and forall:right rules are iteratively applied during proof reconstruction: first process g(f(a)) (the largest element), then f(a), then a. This determines the sequence of quantifier rule applications from the Herbrand disjunction back to the original sequent. Computed by iteratively selecting the maximal element (one with no term above it in the remaining set) from herbrandExTermSetHT under herbrandExHTOrder, removing it, and repeating. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExProofReconstructionOrder :
    List (Term herbrandExLang) :=
  -- Iteratively extract maximal elements from HT under the subterm order.
  -- A term t is maximal in a list if no other term in the list has t as
  -- a proper subterm (i.e., no s in the list satisfies herbrandExHTOrder t s).
  let a := Term.const HerbrandExConst.a
  let fa := Term.func HerbrandExFunc.f (fun _ => a)
  let gfa := Term.func HerbrandExFunc.g (fun _ => fa)
  -- Step 1: From HT = [a, fa, gfa], g(f(a)) is maximal
  --   (no term in HT has g(f(a)) as a subterm).
  -- Step 2: From remaining [a, fa], f(a) is maximal
  --   (no term in [a, fa] has f(a) as a subterm).
  -- Step 3: From remaining [a], a is the only (and maximal) element.
  [gfa, fa, a]







/-- Example 7.5.3: the finite naming map g(f(a))↦u=7, f(a)↦v=8,
a↦w=9. It is undefined outside the three displayed Herbrand terms. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExFreshName : Term herbrandExLang → Option Nat
  | .const .a => some 9
  | .func .f ts => match ts ⟨0, by decide⟩ with
    | .const .a => some 8
    | _ => none
  | .func .g ts => match ts ⟨0, by decide⟩ with
    | .func .f us => match us ⟨0, by decide⟩ with
      | .const .a => some 7
      | _ => none
    | _ => none
  | .var _ => none

/-- Example 7.5.3: the actual inverse finite map on the fresh names u,v,w. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExFreshTerm : Nat → Option (Term herbrandExLang)
  | 7 => some (.func .g (fun _ => .func .f (fun _ => .const .a)))
  | 8 => some (.func .f (fun _ => .const .a))
  | 9 => some (.const .a)
  | _ => none



/-- Example 7.5.3: replace a maximal named term before visiting its arguments.
Thus g(f(a)) becomes u as a whole, rather than g(v) or g(f(w)). -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExReplaceTerm (t : Term herbrandExLang) : Term herbrandExLang :=
  match herbrandExFreshName t with
  | some x => .var x
  | none => match t with
    | .var x => .var x
    | .const c => .const c
    | .func f ts => .func f (fun i => herbrandExReplaceTerm (ts i))

/-- Example 7.5.3: apply maximal-term replacement at each atomic argument.
The concrete input H is quantifier-free; connectives and order are retained. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExReplaceFormula : FormulaN herbrandExLang → FormulaN herbrandExLang
  | .predN p ts => .predN p (fun i => herbrandExReplaceTerm (ts i))
  | .eq_ h s t => .eq_ h (herbrandExReplaceTerm s) (herbrandExReplaceTerm t)
  | .neg A => .neg (herbrandExReplaceFormula A)
  | .conj A B => .conj (herbrandExReplaceFormula A) (herbrandExReplaceFormula B)
  | .disj A B => .disj (herbrandExReplaceFormula A) (herbrandExReplaceFormula B)
  | .impl A B => .impl (herbrandExReplaceFormula A) (herbrandExReplaceFormula B)
  | .all x A => .all x (herbrandExReplaceFormula A)
  | .ex x A => .ex x (herbrandExReplaceFormula A)

/-- Example 7.5.3: P(s,t) in the concrete binary signature. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExP (s t : Term herbrandExLang) : FormulaN herbrandExLang :=
  .predN .P (vec2 s t)

/-- Example 7.5.3: Q(s,t) in the concrete binary signature. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExQ (s t : Term herbrandExLang) : FormulaN herbrandExLang :=
  .predN .Q (vec2 s t)

/-- Example 7.5.3: H′ is → ¬P(w,v), ¬Q(v,u), P(w,v) ∧ Q(v,u),
with fresh u=7, v=8, w=9. Original binder names remain 0–6. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExHPrime : Sequent herbrandExLang :=
  ⟨[], [.neg (herbrandExP (.var 9) (.var 8)), .neg (herbrandExQ (.var 8) (.var 7)),
    .conj (herbrandExP (.var 9) (.var 8)) (herbrandExQ (.var 8) (.var 7))]⟩



/-- Example 7.5.3: the propositional proof of H′ with its two identity leaves,
weakenings, conjunction and Q-before-P negations. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExHPrimeProof : FOLKProofTree herbrandExHPrime :=
  let p := herbrandExP (.var 9) (.var 8)
  let q := herbrandExQ (.var 8) (.var 7)
  let pAx := FOLKProofTree.axiom_ (Sequent.mk [p] [p]) ⟨p, rfl, rfl⟩
  let qAx := FOLKProofTree.axiom_ (Sequent.mk [q] [q]) ⟨q, rfl, rfl⟩
  let left := FOLKProofTree.onePremise (.exchangeLeft [] q p [] [p])
    (.onePremise (.weakenLeft q [p] [p]) pAx)
  let right := FOLKProofTree.onePremise (.weakenLeft p [q] [q]) qAx
  let conj := FOLKProofTree.twoPremise (.andRight p q [p, q] []) left right
  let negQ := FOLKProofTree.onePremise
    (.exchangeRight [p] [] (.conj p q) (.neg q) [])
    (.onePremise (.negRight q [p] [.conj p q])
      (.onePremise (.exchangeLeft [] p q [] [.conj p q]) conj))
  .onePremise (.exchangeRight [] [] (.neg q) (.neg p) [.conj p q])
    (.onePremise (.exchangeRight [] [.neg q] (.conj p q) (.neg p) [])
      (.onePremise (.negRight p [] [.neg q, .conj p q]) negQ))

/-- Example 7.5.3: corrected first boundary, retaining free v=8 until the
next existential step; only z₁=6 is bound here (SQ043). -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExReconstruction1 : Sequent herbrandExLang :=
  ⟨[], [.neg (herbrandExP (.var 9) (.var 8)), .neg (herbrandExQ (.var 8) (.var 7)),
    .ex 6 (.conj (herbrandExP (.var 9) (.var 8)) (herbrandExQ (.var 8) (.var 6))) ]⟩

/-- Example 7.5.3: second boundary introduces y₂=5 outside z₁=6. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExReconstruction2 : Sequent herbrandExLang :=
  ⟨[], [.neg (herbrandExP (.var 9) (.var 8)), .neg (herbrandExQ (.var 8) (.var 7)),
    .ex 5 (.ex 6 (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))]⟩

/-- Example 7.5.3: third boundary restores ∀z on the second formula, using
u=7 as eigenvariable, corresponding to the maximal term g(f(a)). -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExReconstruction3 : Sequent herbrandExLang :=
  ⟨[], [.neg (herbrandExP (.var 9) (.var 8)), .all 3 (.neg (herbrandExQ (.var 8) (.var 3))),
    .ex 5 (.ex 6 (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))]⟩

/-- Example 7.5.3: lawful cumulative reconstruction prefix 1, retaining
all preceding boundaries and the concrete proof of H′. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExPrefix1 : FOLKProofTree herbrandExReconstruction1 := by
  have substAtom (p : HerbrandExPred) (a b t : Term herbrandExLang) (x : Nat) :
      formulaSubstN (.predN p (vec2 a b)) t x =
        .predN p (vec2 (termSubst a t x) (termSubst b t x)) := by
    apply congrArg (FormulaN.predN (L := herbrandExLang) p)
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
  have r : FOLKStep1 herbrandExHPrime herbrandExReconstruction1 := by
    simpa [herbrandExHPrime, herbrandExReconstruction1, herbrandExP, herbrandExQ,
      formulaSubstN, substAtom, termSubst] using
      (FOLKStep1.exRight (L := herbrandExLang) (.var 7) 6
        (.conj (herbrandExP (.var 9) (.var 8)) (herbrandExQ (.var 8) (.var 6)))
        [] [.neg (herbrandExP (.var 9) (.var 8)), .neg (herbrandExQ (.var 8) (.var 7))]
        (by simp [isFreeForN, herbrandExP, herbrandExQ, termFV, Membership.mem, Set.singleton]))
  exact .onePremise r herbrandExHPrimeProof

/-- Example 7.5.3: lawful cumulative reconstruction prefix 2, retaining
all preceding boundaries and the concrete proof of H′. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExPrefix2 : FOLKProofTree herbrandExReconstruction2 := by
  have substAtom (p : HerbrandExPred) (a b t : Term herbrandExLang) (x : Nat) :
      formulaSubstN (.predN p (vec2 a b)) t x =
        .predN p (vec2 (termSubst a t x) (termSubst b t x)) := by
    apply congrArg (FormulaN.predN (L := herbrandExLang) p)
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
  have r : FOLKStep1 herbrandExReconstruction1 herbrandExReconstruction2 := by
    simpa [herbrandExReconstruction1, herbrandExReconstruction2, herbrandExP, herbrandExQ,
      formulaSubstN, substAtom, termSubst] using
      (FOLKStep1.exRight (L := herbrandExLang) (.var 8) 5
        (.ex 6 (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))
        [] [.neg (herbrandExP (.var 9) (.var 8)), .neg (herbrandExQ (.var 8) (.var 7))]
        (by simp [isFreeForN, herbrandExP, herbrandExQ, termFV, Membership.mem, Set.singleton]))
  exact .onePremise r herbrandExPrefix1

/-- Example 7.5.3: the third cumulative prefix, with exchanges exposing Q
and restoring the displayed order. The eigenvariable is fresh in the whole
conclusion, not just in its principal formula. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExPrefix3 : FOLKProofTree herbrandExReconstruction3 := by
  have substAtom (p : HerbrandExPred) (a b t : Term herbrandExLang) (x : Nat) :
      formulaSubstN (.predN p (vec2 a b)) t x =
        .predN p (vec2 (termSubst a t x) (termSubst b t x)) := by
    apply congrArg (FormulaN.predN (L := herbrandExLang) p)
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
  let np := FormulaN.neg (herbrandExP (.var 9) (.var 8))
  let nq := FormulaN.neg (herbrandExQ (.var 8) (.var 7))
  let c2 := FormulaN.ex 5 (.ex 6
    (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))
  let aq := FormulaN.all 3 (.neg (herbrandExQ (.var 8) (.var 3)))
  have finTwo (R : Fin 2 → Prop) : (∃ i, R i) ↔ R 0 ∨ R 1 := by
    constructor
    · rintro ⟨⟨i, hi⟩, h⟩
      match i, hi with
      | 0, _ => exact Or.inl h
      | 1, _ => exact Or.inr h
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  have finTwoAll (R : Fin 2 → Prop) : (∀ i, R i) ↔ R 0 ∧ R 1 := by
    constructor
    · intro h; exact ⟨h 0, h 1⟩
    · rintro ⟨h0, h1⟩ ⟨i, hi⟩
      match i, hi with
      | 0, _ => exact h0
      | 1, _ => exact h1
  have fresh : ∀ F ∈ ([] : List (FormulaN herbrandExLang)) ++ ([np, c2] ++ [aq]),
      7 ∉ formulaFVN F := by
    intro F hF
    simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl
    all_goals simp [np, c2, aq, formulaFVN, herbrandExP, herbrandExQ,
      Membership.mem, Set.iUnion, Set.union, Set.diff, Set.singleton,
      termFV, vec2, herbrandExLang, finTwo, finTwoAll]
  have r : FOLKStep1 ⟨[], [np, c2, nq]⟩ ⟨[], [np, c2, aq]⟩ := by
    simpa [nq, aq, formulaSubstN, herbrandExQ, substAtom, termSubst] using
      (FOLKStep1.allRight (L := herbrandExLang) 7 3
        (.neg (herbrandExQ (.var 8) (.var 3))) [] [np, c2] fresh
        (by simp [isFreeForN, herbrandExQ]))
  exact .onePremise (.exchangeRight [] [np] c2 aq [])
    (.onePremise r (.onePremise (.exchangeRight [] [np] nq c2 []) herbrandExPrefix2))



/-- Example 7.5.3: translate the f/g/a term spelling used in Example 7.5.2
into the identical symbols of this example's signature. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExFromSkolemTerm : Term exampleLang_7_5 → Term herbrandExLang
  | .var x => .var x
  | .const .a => .const .a
  | .func .f ts => .func .f (fun i => herbrandExFromSkolemTerm (ts i))
  | .func .g ts => .func .g (fun i => herbrandExFromSkolemTerm (ts i))

/-- Example 7.5.3: the same signature spelling on formulas, preserving binders. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExFromSkolemFormula : FormulaN exampleLang_7_5 → FormulaN herbrandExLang
  | .predN p ts => .predN (match p with | .P => .P | .Q => .Q)
      (fun i => herbrandExFromSkolemTerm (ts i))
  | .eq_ h s t => .eq_ h (herbrandExFromSkolemTerm s) (herbrandExFromSkolemTerm t)
  | .neg A => .neg (herbrandExFromSkolemFormula A)
  | .conj A B => .conj (herbrandExFromSkolemFormula A) (herbrandExFromSkolemFormula B)
  | .disj A B => .disj (herbrandExFromSkolemFormula A) (herbrandExFromSkolemFormula B)
  | .impl A B => .impl (herbrandExFromSkolemFormula A) (herbrandExFromSkolemFormula B)
  | .all x A => .all x (herbrandExFromSkolemFormula A)
  | .ex x A => .ex x (herbrandExFromSkolemFormula A)

/-- Example 7.5.3: canonical constant allocated to ∀x₁ in the third sentence. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExCanonicalA : Term (validitySkolemLanguage skolemExampleSequent_7_3_4) :=
  .const (.inr ⟨⟨⟨2, by decide⟩, ⟨0, by decide⟩, rfl⟩, rfl⟩)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 7.5.3: fresh w=9 avoids the complete original variable list. -/
theorem herbrandExSigmaNameFresh :
    ∀ x ∈ sourceVariableIndices skolemExampleSequent_7_3_4, 9 ≠ x := by
  intro x hx
  change x ∈ [0, 1, 2, 3, 4, 5, 6] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  omega

/-- Example 7.5.3: the restriction of the concrete bijection a↦w to the
single universal term required for the third sentence's σ-matrix. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExSigmaNames : FreshTermNames skolemExampleSequent_7_3_4 [herbrandExCanonicalA] where
  name := fun _ _ => 9
  injective := by
    intro t u ht hu _
    exact (List.mem_singleton.mp ht).trans (List.mem_singleton.mp hu).symm
  fresh := fun _ _ x hx => herbrandExSigmaNameFresh x hx

/-- Example 7.5.3: residual existential assignment y₂↦v, z₁↦u for the
third original sentence; the still-free universal name w is fixed. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExSigmaAssignment : Substitution (validitySkolemLanguage skolemExampleSequent_7_3_4) :=
  fun x => if x = 5 then .var 8 else if x = 6 then .var 7 else .var x

end LCS.Herbrand.HerbrandTheorem.Main
end

