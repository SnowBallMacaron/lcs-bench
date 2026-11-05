import LCS.Herbrand.HerbrandTheorem.Main
import LCS.Herbrand.SHGTheorem.Main
import LCS.Propositional.Infinite.Compactness

/-! # Herbrand and SHG theorem schemas

Problems 7.6.11(b) and 7.6.15 concern the expansion version of SHG,
Theorem 7.5.1 for LK, and completeness for prenex formulae. These propositions
make the statements available as explicit premises of the metaderivations.
-/

namespace LCS.Herbrand.Metatheory

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.Herbrand.HerbrandTheorem
open LCS.Herbrand.HerbrandTheorem.Main
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.SHGTheorem.Main
open LCS.CutElim.LK

/-- Ground terms using exactly the permitted occurring-symbol signature. -/
def groundTermOver {L : Language} (B : FormulaN L) (t : Term L) : Prop :=
  IsGroundTerm t ∧
  (∀ c, termConstSymbols t c → fmlaConstSymbols B c) ∧
  (∀ f, termFuncSymbols t f → fmlaFuncSymbols B f)

/-- Problem 7.6.11: delete every universal quantifier in the Skolem form,
including those below connectives, and embed the result in the signature
completed by one constant #. On Skolem forms this is the quantifier-free B*.
Other constructors are preserved; in particular this operation does not
silently erase an existential quantifier from an arbitrary input. -/
def expansionMatrix {L : Language} (hL : L.withoutEquality) :
    FormulaN L → FormulaN (extendedLanguage L Unit)
  | .predN P ts => .predN P
      (fun i => LCS.FirstOrder.Semantics.Substitution.liftTerm (ts i))
  | .eq_ h t u => .eq_ h
      (LCS.FirstOrder.Semantics.Substitution.liftTerm t)
      (LCS.FirstOrder.Semantics.Substitution.liftTerm u)
  | .neg A => .neg (expansionMatrix hL A)
  | .conj A B => .conj (expansionMatrix hL A) (expansionMatrix hL B)
  | .disj A B => .disj (expansionMatrix hL A) (expansionMatrix hL B)
  | .impl A B => .impl (expansionMatrix hL A) (expansionMatrix hL B)
  | .all _ A => expansionMatrix hL A
  | .ex x A => .ex x (expansionMatrix hL A)

/-- The free universe for Problem 7.6.11 consists of closed terms over the
symbols occurring in B. The single adjoined constant # is admitted precisely
when that occurring signature has no ground term, including the possibility
of ground terms built from nullary functions. Unused ambient symbols are
excluded. This is the standing nonempty-universe convention. -/
def expansionGroundTerm {L : Language} (_hL : L.withoutEquality) (B : FormulaN L)
    (t : Term (extendedLanguage L Unit)) : Prop :=
  IsGroundTerm t ∧
  (∀ c, termConstSymbols t c →
    (∃ d, c = Sum.inl d ∧ fmlaConstSymbols B d) ∨
    ((¬ ∃ u : Term L, groundTermOver B u) ∧ c = Sum.inr ())) ∧
  (∀ f, termFuncSymbols t f → fmlaFuncSymbols B f)

/-- E(A,H) in Problem 7.6.11: simultaneous ground instances of B*, where B
is the canonical Skolem form of the fixed rectified NNF sentence A. Every
free variable of B* is assigned a term of its free universe. Values of the
substitution outside those variables have no effect. The result is explicitly
quantifier-free and closed in the same completed Skolem signature. -/
def herbrandExpansion {L : Language} (hL : L.withoutEquality)
    (spec : SkolemSpec L) :
    Set (FormulaN (extendedLanguage spec.language Unit)) :=
  fun C => isQuantifierFree C ∧ FormulaN.isClosed C ∧
    ∃ sigma : Substitution (extendedLanguage spec.language Unit),
      (∀ x, x ∈ formulaFVN (expansionMatrix (L := spec.language) hL (SK spec)) →
        expansionGroundTerm (L := spec.language) hL (SK spec) (sigma x)) ∧
      C = Substitution.applyFormula sigma (expansionMatrix (L := spec.language) hL (SK spec))

/-- A nonempty finite conjunction from E(A,H), retaining every leaf's
membership in that same expansion. ConjunctionFlattening allows any binary
association and preserves leaf order and multiplicity. -/
def finiteExpansionConjunction {L : Language} (hL : L.withoutEquality)
    (spec : SkolemSpec L)
    (F : FormulaN (extendedLanguage spec.language Unit)) : Prop :=
  ∃ leaves : List (FormulaN (extendedLanguage spec.language Unit)),
    ConjunctionFlattening F leaves ∧
    ∀ C ∈ leaves, herbrandExpansion hL spec C

/-- Problem 7.6.11(b), the expansion/conjunction SHG schema over equality-free
languages. SkolemSpec supplies the standing rectified NNF sentence domain.
The right side is the actual finite-expansion unsatisfiability conclusion. -/
def SHGSchema : Prop :=
  ∀ (L : Language) (hL : L.withoutEquality) (spec : SkolemSpec L),
    ¬ satisfiableN spec.source ↔
      ∃ F : FormulaN (extendedLanguage spec.language Unit),
        finiteExpansionConjunction hL spec F ∧ ¬ satisfiableN F

/-- Theorem 7.5.1, as used in Problem 7.6.15: the equality-free LK
biconditional with its normalized, source-associated substitution witnesses.
All hypotheses and the witness signature are those of herbrandTheorem_LK.
This definition states the premise; it does not invoke that theorem's proof. -/
def HerbrandLKSchema : Prop :=
  ∀ (L : Language) (_hL : L.withoutEquality) (Gamma : List (FormulaN L)),
    allSequentFormulaeArePrenex (Sequent.mk [] Gamma) →
    (∀ A ∈ Gamma, FormulaN.isSentence A) →
    (∀ A ∈ Gamma, isRectified A) → Gamma.Nodup →
    (folkProvable (Sequent.mk [] Gamma) ↔
      ∃ (Delta : List (FormulaN L)) (sps : SubstitutionPairSeq Delta)
        (sd : SkolemData L Delta),
        IsHerbrandNormalization Gamma Delta ∧
        IsConstructibleFromFunctionalForm Delta sps sd ∧
        folkProvable (HerbrandDisjunction sd sps))

/-- Completeness for prenex formulae in Problem 7.6.15: validity under all
structures and assignments implies LK-provability. Free variables are allowed;
there is no added sentence, NNF, or rectification restriction on this schema. -/
def PrenexCompletenessSchema : Prop :=
  ∀ (L : Language) (_hL : L.withoutEquality) (A : FormulaN L),
    isPrenex A → universallyValidN A → folkProvable (Sequent.mk [] [A])

/-- The permitted compactness premise of Problem 7.6.11(b), stated on the
existing propositional syntax and Boolean valuations of Theorem 3.5.3.
Every finite nonempty subset must be satisfiable by one valuation; the
conclusion supplies one valuation satisfying the entire set. -/
def PropositionalCompactnessSchema : Prop :=
  ∀ Gamma : Set LCS.Propositional.Syntax.PropFormulaNormalized,
    LCS.Propositional.Infinite.Compactness.finiteSubsetSatisfiable Gamma →
    LCS.Propositional.Infinite.Compactness.setSatisfiable Gamma

/-- The singleton expansion lemma of Problem 7.6.11(a), obtained there from
the free-structure argument of Problem 7.6.10. A rectified NNF sentence is
satisfiable iff its entire ground expansion is satisfied in one structure
over the completed Skolem signature. The same structure satisfies all
instances; the existential model is outside the universal formula binder.
This premise does not assert compactness or select a finite conjunction. -/
def ExpansionSatisfiabilitySchema : Prop :=
  ∀ (L : Language) (hL : L.withoutEquality) (spec : SkolemSpec L),
    satisfiableN spec.source ↔
      ∃ M : Structure (extendedLanguage spec.language Unit),
        ∀ C, herbrandExpansion hL spec C → validInN M C

/-- Problem 7.6.11(b): propositional compactness and the free-structure
expansion lemma yield the expansion/conjunction SHG schema. Both permitted
background premises are explicit. The completeness-independent derivation
requires the ground-atom/propositional correspondence and the passage from
a finite set of expansion instances to its nonempty conjunction.
The proof dependency audit remains pending until this proof is supplied. -/
theorem shgFromExpansionCompactness
    (hCompactness : PropositionalCompactnessSchema)
    (hExpansion : ExpansionSatisfiabilitySchema) : SHGSchema := by
  -- REPAIR(T7-104): proof pending
  sorry

/-- Problem 7.6.15(a): the LK Herbrand theorem and the expansion/conjunction
SHG theorem imply completeness for all prenex formulae over equality-free
languages. The proof must connect the normalized witnesses of the two
premises and recover the original formula, including its free variables.
The permitted background is ordinary syntax, semantics and propositional
reasoning. First-order completeness may not be used to discharge this proof
or the supplied Herbrand/SHG premises; that dependency audit is pending. -/
theorem prenexCompletenessFromHerbrandSHG
    (hHerbrand : HerbrandLKSchema) (hSHG : SHGSchema) :
    PrenexCompletenessSchema := by
  -- REPAIR(T7-105): proof pending
  sorry

/-- Problem 7.6.15(b): the LK Herbrand theorem and completeness for prenex
formulae imply the expansion/conjunction SHG theorem for rectified NNF
sentences over equality-free languages. The proof must preserve the fixed
source and occurring Skolem signature when passing through prenex forms and
Herbrand disjunctions. Its semantic and propositional background is ordinary;
the desired SHG theorem may not be imported as a proof of the conclusion.
The proof and its premise-dependency audit are pending. -/
theorem shgFromHerbrandPrenexCompleteness
    (hHerbrand : HerbrandLKSchema) (hCompleteness : PrenexCompletenessSchema) :
    SHGSchema := by
  -- REPAIR(T7-105): proof pending
  sorry

end LCS.Herbrand.Metatheory
