import LCS.FirstOrder.ManySorted.Equality.Reduction
import Attach
import LCS.FirstOrder.ManySorted.Metatheory.ProofsStamp

/-! The many-sorted metatheorems of §§10.5.3–10.5.4.

The equality-Hintikka bridge states the sorted quotient-model obligation of
§5.6. The three metatheorems below are the named many-sorted conclusions of
Lemma 10.5.2. The source-language wrapper supplies the countability used by
the inherited chapter-5 endpoints; semantic assignments remain unrestricted.
-/

namespace LCS.FirstOrder.ManySorted.Metatheory

open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.FirstOrder.ManySorted.Gentzen
open LCS.FirstOrder.ManySorted.Equality
open LCS.FirstOrder.ManySorted.Equality.Reduction
open LCS.Propositional.Semantics

/-- Theorem 10.5.1 (companion): the equality relation on each term carrier
used in the Hintikka quotient: t and u are related when T(t = u) lies in S.
Its equivalence and compatibility properties follow from the equality-Hintikka
conditions, including congruence for equality itself. -/
@[blueprint "chap10__theorem_10_5_1"]
def msHintikkaEquality {L : MSLanguage} (hL : L.hasEquality = true)
    (S : Set (MSSignedFormula L)) {s : L.SortType}
    (t u : MSTerm L s) : Prop :=
  MSSignedFormula.trueF (MSFormula.eq_ hL s t u) ∈ S

/-- Theorem 10.5.1 (companion): the sorted equality-Hintikka quotient bridge.
Every carrier of M is represented by H, and evaluation identifies exactly the
pairs in the signed equality relation. The SAME M and v satisfy all signs in S.
Nonempty term carriers, function/constant closure, atomic consistency, free-for
instances, and the positive-rank equality rules are supplied by hTA and hHS.
This is the many-sorted counterpart of the quotient-model argument of §5.6.3. -/
@[attach_debt, blueprint "chap10__theorem_10_5_1"]
theorem msHintikkaSetEqQuotientSatisfiable {L : MSLanguage}
    [DecidableEq L.SortType] (hL : L.hasEquality = true)
    (H : (s : L.SortType) → Set (MSTerm L s))
    (S : Set (MSSignedFormula L)) (hTA : MSIsGeneratedTermAlgebra L H)
    (hHS : MSIsHintikkaSetEq L hL H S) :
    ∃ (M : MSStructure L) (v : MSAssignment M),
      (∀ s (a : M.carrier s), ∃ t : MSTerm L s,
        t ∈ H s ∧ msTermEval M v t = a) ∧
      (∀ s (t u : MSTerm L s), t ∈ H s → u ∈ H s →
        (msTermEval M v t = msTermEval M v u ↔ msHintikkaEquality hL S t u)) ∧
      (∀ A, MSSignedFormula.trueF A ∈ S → msFormulaEval M A v = BoolVal.T) ∧
      (∀ A, MSSignedFormula.falseF A ∈ S → msFormulaEval M A v = BoolVal.F)

/-- Lemma 10.5.2 (companion): every formula of an arbitrary theory is true
in one fixed structure under one shared, unrestricted sorted assignment. -/
@[blueprint "chap10__lemma_10_5_2"]
def msTheorySatisfiedIn {L : MSLanguage} (M : MSStructure L)
    (v : MSAssignment M) (T : Set (MSFormula L)) : Prop :=
  ∀ A, T A → msFormulaEval M A v = BoolVal.T

/-- Lemma 10.5.2 (companion): arbitrary-set satisfiability. MSStructure
requires every data-sort carrier to be nonempty, also for the empty theory. -/
@[blueprint "chap10__lemma_10_5_2"]
def msTheorySatisfiable {L : MSLanguage} (T : Set (MSFormula L)) : Prop :=
  ∃ (M : MSStructure L) (v : MSAssignment M), msTheorySatisfiedIn M v T

/-- Lemma 10.5.2 (companion): every nonempty finite subset is satisfiable.
A finite list enumerates the subset; repetition has no semantic effect.
There is no nonemptiness assumption on the ambient theory. -/
@[blueprint "chap10__lemma_10_5_2"]
def msNonemptyFiniteSubsetsSatisfiable {L : MSLanguage}
    (T : Set (MSFormula L)) : Prop :=
  ∀ Γ : List (MSFormula L), Γ ≠ [] → (∀ A ∈ Γ, T A) →
    msTheorySatisfiable (fun A => A ∈ Γ)

/-- Lemma 10.5.2 (companion): compactness in G's equality-free regime,
for arbitrary sets and the printed nonempty finite-subset premise. -/
@[attach_debt, blueprint "chap10__lemma_10_5_2"]
theorem msCompactnessG (L : MSFirstOrderLanguage)
    (hL : L.toMSLanguage.withoutEquality) (T : Set (MSFormula L.toMSLanguage))
    (hFinite : msNonemptyFiniteSubsetsSatisfiable T) : msTheorySatisfiable T

/-- Lemma 10.5.2 (companion): the empty equality-free theory is satisfiable,
with nonempty carriers and a full assignment, even when there are no atoms. -/
@[attach_debt, blueprint "chap10__lemma_10_5_2"]
theorem msEmptyTheorySatisfiableG {L : MSLanguage} (hL : L.withoutEquality) :
    msTheorySatisfiable (L := L) (fun _ => False)

/-- Lemma 10.5.2 (companion): compactness in the equality regime, using
the general language carrier with hasEquality = true and shared assignments. -/
@[attach_debt, blueprint "chap10__lemma_10_5_2"]
theorem msCompactnessEq (L : MSFirstOrderLanguage)
    (hL : L.hasEquality = true) (T : Set (MSFormula L.toMSLanguage))
    (hFinite : msNonemptyFiniteSubsetsSatisfiable T) : msTheorySatisfiable T

/-- Lemma 10.5.2 (companion): the empty equality theory is satisfiable;
identity equality is interpreted in a structure with nonempty sort carriers. -/
@[attach_debt, blueprint "chap10__lemma_10_5_2"]
theorem msEmptyTheorySatisfiableEq {L : MSLanguage} (hL : L.hasEquality = true) :
    msTheorySatisfiable (L := L) (fun _ => False)

/-- Lemma 10.5.2 (companion): G-consistency means there is a formula B in
the calculus presentation for which no finite list of premises from T proves
T ⇒ B. This uses the actual G proof predicate, including its domain. -/
@[blueprint "chap10__lemma_10_5_2"]
def msTheoryConsistentG {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.withoutEquality) (T : Set (MSFormula L)) : Prop :=
  ∃ B : MSFormula L, msIsSixConnective B ∧ ¬ msTheoryProvableG hL T B

/-- Lemma 10.5.2 (companion): G=-consistency is nonprovability of some
six-connective conclusion from every finite list selected from T. -/
@[blueprint "chap10__lemma_10_5_2"]
def msTheoryConsistentEq {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.hasEquality = true) (T : Set (MSFormula L)) : Prop :=
  ∃ B : MSFormula L, msIsSixConnective B ∧ ¬ msTheoryProvableEq hL T B

/-- Lemma 10.5.2 (companion): the inherited set-wide free/bound convention.
A sorted variable free in any member is bound in no member of the theory. -/
@[blueprint "chap10__lemma_10_5_2"]
def msTheoryCrossNoFreeBound {L : MSLanguage} [DecidableEq L.SortType]
    (T : Set (MSFormula L)) : Prop :=
  ∀ A, T A → ∀ B, T B → ∀ x : MSVar L,
    x ∈ msFormulaFV A → x ∉ msFormulaBV B

/-- Lemma 10.5.2 (companion): model existence for a G-consistent theory
in the six-connective presentation, with the set-wide §5.5.4 convention. -/
@[attach_debt, blueprint "chap10__lemma_10_5_2"]
theorem msModelExistenceG (L : MSFirstOrderLanguage) [DecidableEq L.SortType]
    (hL : L.toMSLanguage.withoutEquality) (T : Set (MSFormula L.toMSLanguage))
    (hT : ∀ A, T A → msIsSixConnective A)
    (hConsistent : msTheoryConsistentG hL T) (hFB : msTheoryCrossNoFreeBound T) :
    msTheorySatisfiable T

/-- Lemma 10.5.2 (companion): model existence for a G=-consistent theory
in the six-connective presentation, on the domain of §5.6.6. -/
@[attach_debt, blueprint "chap10__lemma_10_5_2"]
theorem msModelExistenceEq (L : MSFirstOrderLanguage) [DecidableEq L.SortType]
    (hL : L.hasEquality = true) (T : Set (MSFormula L.toMSLanguage))
    (hT : ∀ A, T A → msIsSixConnective A)
    (hConsistent : msTheoryConsistentEq hL T) : msTheorySatisfiable T

/-- Lemma 10.5.2 (companion): at-most-countability of the tagged TOTAL
data domain, not merely countability of each sort separately. -/
@[blueprint "chap10__lemma_10_5_2"]
def msCountableTotalDomain {L : MSLanguage} (M : MSStructure L) : Prop :=
  ∃ code : (Sigma M.carrier) → Nat, Function.Injective code

/-- Lemma 10.5.2 (companion): Löwenheim–Skolem in the equality-free regime.
One output structure and assignment satisfy all of T, and that very structure
has an injection of its tagged total data domain into Nat. T may be empty. -/
@[attach_debt, blueprint "chap10__lemma_10_5_2"]
theorem msLowenheimSkolemG (L : MSFirstOrderLanguage)
    (hL : L.toMSLanguage.withoutEquality) (T : Set (MSFormula L.toMSLanguage))
    (hSat : msTheorySatisfiable T) :
    ∃ (M : MSStructure L.toMSLanguage) (v : MSAssignment M),
      msTheorySatisfiedIn M v T ∧ msCountableTotalDomain M

/-- Lemma 10.5.2 (companion): Löwenheim–Skolem with identity equality,
including the empty theory and unrestricted semantic assignments. -/
@[attach_debt, blueprint "chap10__lemma_10_5_2"]
theorem msLowenheimSkolemEq (L : MSFirstOrderLanguage)
    (hL : L.hasEquality = true) (T : Set (MSFormula L.toMSLanguage))
    (hSat : msTheorySatisfiable T) :
    ∃ (M : MSStructure L.toMSLanguage) (v : MSAssignment M),
      msTheorySatisfiedIn M v T ∧ msCountableTotalDomain M

/-! Lemma 10.5.2: reduction-to-metatheorem relationships.

The concrete reduction endpoints are
`LCS.FirstOrder.ManySorted.Equality.Reduction.msReductionToOneSorted` and
`LCS.FirstOrder.ManySorted.Equality.Reduction.msReductionToOneSortedEq`.
They use `msFormulaTranslate`, `msReductionPremises` (T′, all MS typing and
nonemptiness axioms, and shared FV(T) ∪ FV(A) guards), injective sorted-variable
renaming, and finite proof support. The transfer follows the matching G/G=
regime. Primitive formulae enter the six-connective presentation through
abbreviation expansion before invoking these consequence endpoints.

The named conclusions and read-only chapter-5 endpoints are:
* `msCompactnessG` / `msCompactnessEq` correspond to
  `LCS.FirstOrder.Completeness.MetaTheorems.compactnessNoEq` /
  `LCS.FirstOrder.Equality.MetaTheorems.compactness_eq` (5.5.3 / 5.6.3).
  Finite translated fragments require only finitely many source formulae and
  shared guards. Empty theories use `msEmptyTheorySatisfiableG` / `Eq`.
* `msModelExistenceG` / `msModelExistenceEq` correspond to
  `LCS.FirstOrder.Completeness.MetaTheorems.consistent_implies_satisfiableNNoEq` /
  `LCS.FirstOrder.Equality.MetaTheorems.consistent_implies_satisfiable_eq`
  (5.5.4 / 5.6.4). Consistency uses the matching finite-support predicates;
  the G member retains set-wide free/bound separation.
* `msLowenheimSkolemG` / `msLowenheimSkolemEq` correspond to
  `LCS.FirstOrder.Completeness.MetaTheorems.lowenheim_skolemNoEq` /
  `LCS.FirstOrder.Equality.MetaTheorems.lowenheim_skolem_eq` (5.5.2 / 5.6.2).
  Restriction of a translated model to each D_s gives nonempty carriers.
  Pairing the countable sort code with the one-sorted domain code bounds the
  tagged total domain of the SAME satisfying model.

These statements supply the compactness, model-existence and Löwenheim–Skolem
instances asserted in §10.5.4. Their derivations still require the semantic
translation/restriction lemma with shared assignments, the countable-language
encoding, the abbreviation bridge, and the finite-support reduction proofs.
The stated conclusions and this dependency map do not assert that those
proof adaptations have been completed.
-/

end LCS.FirstOrder.ManySorted.Metatheory
