import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.FirstOrder.Semantics.Equivalence
import Attach
import LCS.CutElim.Hauptsatz.ProofsStamp

/-! # CutElim.Hauptsatz
    Formalization of Chapter 6, Sections 6.4.1-6.4.2.
    Negation normal form and the Gentzen system G1nnf.
    Source: Logic for Computer Science, Gallier 2015
-/

-- ===================================================================
-- Definition 6.4.1: FormulaN.isNNF — negation normal form predicate
-- ===================================================================

namespace LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN.Substitution

namespace FormulaN

/-- Definition 6.4.1: The set of formulae in negation normal form (NNF)
is the smallest set such that (1) for every atomic formula A, both A
and neg A are in NNF; (2) if A and B are in NNF, then A or B and
A and B are in NNF; (3) if A is in NNF, then forall x A and exists x A
are in NNF. Since FormulaN has no falsum, pred0, or equiv_ constructors, the definition is simpler.-/
@[blueprint "chap6__definition_6_4_1" (main := true)]
def isNNF {L : Language} : FormulaN L → Prop
  | .predN _ _ => True
  | .eq_ _ _ _ => True
  | .neg (.predN _ _) => True
  | .neg (.eq_ _ _ _) => True
  | .disj A B => A.isNNF ∧ B.isNNF
  | .conj A B => A.isNNF ∧ B.isNNF
  | .all _ A => A.isNNF
  | .ex _ A => A.isNNF
  | _ => False

open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Equivalence

/-- The NNF conversion with a polarity: `true` converts the formula and
`false` converts its negation. Recursion follows the formula structure. -/
@[blueprint "chap6__lemma_6_4_1"]
def toNNFAux {L : Language} : Bool → FormulaN L → FormulaN L
  | true, .predN P ts => .predN P ts
  | false, .predN P ts => .neg (.predN P ts)
  | true, .eq_ hL t u => .eq_ hL t u
  | false, .eq_ hL t u => .neg (.eq_ hL t u)
  | true, .neg A => toNNFAux false A
  | false, .neg A => toNNFAux true A
  | true, .conj A B => .conj (toNNFAux true A) (toNNFAux true B)
  | false, .conj A B => .disj (toNNFAux false A) (toNNFAux false B)
  | true, .disj A B => .disj (toNNFAux true A) (toNNFAux true B)
  | false, .disj A B => .conj (toNNFAux false A) (toNNFAux false B)
  | true, .impl A B => .disj (toNNFAux false A) (toNNFAux true B)
  | false, .impl A B => .conj (toNNFAux true A) (toNNFAux false B)
  | true, .all x A => .all x (toNNFAux true A)
  | false, .all x A => .ex x (toNNFAux false A)
  | true, .ex x A => .ex x (toNNFAux true A)
  | false, .ex x A => .all x (toNNFAux false A)

/-- The conversion in the proof of Lemma 6.4.1. Atoms and negated atoms
are unchanged; double negations are removed; De Morgan's laws push
negations through conjunctions, disjunctions and quantifiers. Positive
connectives are converted componentwise, retaining every bound variable.
As an extension outside the source clauses, implication is converted to
`¬A ∨ B`, and negated implication to `A ∧ ¬B`, recursively in NNF. -/
@[blueprint "chap6__example_6_4_1"]
def toNNF {L : Language} (A : FormulaN L) : FormulaN L :=
  toNNFAux true A

/-- Proof of Lemma 6.4.1: The conversion produces a formula in NNF. -/
theorem toNNF_isNNF {L : Language} (A : FormulaN L) : (toNNF A).isNNF := by
  have h (B : FormulaN L) (pol : Bool) : (toNNFAux pol B).isNNF := by
    induction B generalizing pol <;> cases pol <;> simp_all [toNNFAux, isNNF]
  exact h A true

/-- Proof of Lemma 6.4.1: The conversion preserves logical equivalence. -/
theorem toNNF_equiv {L : Language} (A : FormulaN L) :
    foLogEquivN A (toNNF A) := by
  classical
  have h (B : FormulaN L) (pol : Bool) (M : Structure L) (s : Assignment M) :
      formulaEvalN M (toNNFAux pol B) s ↔
        if pol then formulaEvalN M B s else ¬ formulaEvalN M B s := by
    induction B generalizing pol s <;> cases pol <;>
      simp_all [toNNFAux, formulaEvalN, negM, Basic.andM, Basic.orM, implM]
    all_goals
      exact ⟨fun h hp => h.elim (fun hn => False.elim (hn hp)) id,
        fun h => Classical.byCases (fun hp => Or.inr (h hp)) Or.inl⟩
  intro M s
  exact ⟨(h A true M s).mpr, (h A true M s).mp⟩

end FormulaN

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.FormulaRenaming, LCS.CutElim.Hauptsatz.CutElimination.Freshening, LCS.CutElim.Hauptsatz.CutElimination.Substitution, LCS.Herbrand.SHGTheorem.Herbrand.LowerConstruction, LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds
/-- NNF is preserved under term substitution: `formulaSubstN A t x` is in
NNF whenever A is. Used by the §6.4.3 proof of Lem 6.4.2 to check that
substitution instances produced during the Hintikka-set construction stay
within the NNF grammar on which G1nnf operates. -/
theorem isNNF_formulaSubstN {L : Language} (A : FormulaN L) (t : Term L) (x : Nat) :
    A.isNNF → (formulaSubstN A t x).isNNF := by
-- BEGIN PROOF
  intro h
  induction A with
  | predN _ _ => exact trivial
  | eq_ _ _ _ => exact trivial
  | neg A ih =>
    cases A with
    | predN _ _ => exact trivial
    | eq_ _ _ _ => exact trivial
    | _ => exact h.elim
  | conj A B ihA ihB =>
    simp only [formulaSubstN, FormulaN.isNNF]; exact ⟨ihA h.1, ihB h.2⟩
  | disj A B ihA ihB =>
    simp only [formulaSubstN, FormulaN.isNNF]; exact ⟨ihA h.1, ihB h.2⟩
  | impl _ _ _ _ => exact h.elim
  | all y A ih =>
    simp only [formulaSubstN]
    by_cases hxy : (x != y) = true
    · simp [hxy, FormulaN.isNNF]; exact ih h
    · simp [hxy]; exact h
  | ex y A ih =>
    simp only [formulaSubstN]
    by_cases hxy : (x != y) = true
    · simp [hxy, FormulaN.isNNF]; exact ih h
    · simp [hxy]; exact h

end LCS.FirstOrder.SyntaxN

namespace LCS.CutElim.Hauptsatz

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Equivalence

/-- The §6.1 convention for finite-set sequents: a variable free in any
formula on either side is bound in no formula on either side. -/
@[blueprint "chap6__lemma_6_4_7"]
def finsetCrossNoFreeBound {L : Language}
    (Γ Δ : LCS.Finset (FormulaN L)) : Prop :=
  ∀ x, (∃ A, (A ∈ Γ ∨ A ∈ Δ) ∧ x ∈ formulaFVN A) →
    ∀ B, (B ∈ Γ ∨ B ∈ Δ) → x ∉ formulaBVN B



-- ===================================================================
-- Definition 6.4.2 (companion type): G1nnfSequent
-- ===================================================================

/-- Definition 6.4.2: A sequent of the system G1nnf over a language without equality
is a pair Gamma -> Delta where Gamma and Delta are finite sets of
formulae in negation normal form, matching the textbook's Definition
6.4.2: "The sequents of the system G1nnf are pairs Gamma -> Delta,
where Gamma and Delta are finite sets of formulae in NNF." Using
sets gives exchange and contraction for free (sets are unordered
and idempotent). -/
@[blueprint "chap6__definition_6_4_2" (main := true)]
structure G1nnfSequent (L : Language) (hL : L.withoutEquality) : Type where
  /-- The antecedent Gamma: a set of NNF formulae -/
  ante : Set (FormulaN L)
  /-- The succedent Delta: a set of NNF formulae -/
  succ : Set (FormulaN L)
  /-- All formulae in the antecedent are in NNF -/
  ante_nnf : ∀ A ∈ ante, FormulaN.isNNF A
  /-- All formulae in the succedent are in NNF -/
  succ_nnf : ∀ A ∈ succ, FormulaN.isNNF A
  /-- The antecedent is finite (textbook Def 6.4.2: "finite sets") -/
  ante_finite : Set.Finite ante
  /-- The succedent is finite (textbook Def 6.4.2: "finite sets") -/
  succ_finite : Set.Finite succ

namespace G1nnfFinsetSequent

/-- The Finset-indexed presentation of a G1nnf sequent contains only
formulae in negation normal form on both sides. This is the Finset-level
counterpart of the NNF fields of `G1nnfSequent`. -/
@[blueprint "chap6__definition_6_4_2"]
def IsNNF {L : Language}
    (s : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) : Prop :=
  (∀ A ∈ s.1, FormulaN.isNNF A) ∧
  (∀ A ∈ s.2, FormulaN.isNNF A)

namespace IsNNF

-- retained: used by LCS.CutElim.Beth.Part2, LCS.CutElim.Hauptsatz.Equality.Part2, LCS.CutElim.Interpolation.ConstantSubstitution, LCS.CutElim.Interpolation.Equality.Axioms, LCS.CutElim.Interpolation.Equality.Reduction, LCS.CutElim.Interpolation.Equality.Replay, LCS.CutElim.Interpolation.Equality.Support, LCS.CutElim.Interpolation.FreshPredicate, LCS.CutElim.Interpolation.InterpolantRepair, LCS.CutElim.Interpolation.KeyLemma.Cases, LCS.CutElim.Interpolation.Partitions, LCS.CutElim.Interpolation.QuantifierCases, LCS.CutElim.Interpolation.RuleSubstitution, LCS.CutElim.Interpolation.VariableSubstitution, LCS.CutElim.LK.Part1, LCS.CutElim.LK.Part1.Proofs, LCS.CutElim.LK.Part2, LCS.CutElim.LKe, LCS.CutElim.LKe.Equivalence, LCS.CutElim.LKe.Equivalence.AtomicLeaves, LCS.CutElim.LKe.Equivalence.AtomicLeaves.Proofs, LCS.CutElim.LKe.Equivalence.AtomicTranslation, LCS.CutElim.LKe.Equivalence.ConjunctionPermutation, LCS.CutElim.LKe.Equivalence.ContextPermutation, LCS.CutElim.LKe.Equivalence.EqualityTranslation, LCS.CutElim.LKe.Equivalence.ImplicationPermutation, LCS.CutElim.LKe.Equivalence.ImplicationPermutation.Proofs, LCS.CutElim.LKe.Equivalence.Normalization, LCS.CutElim.LKe.Equivalence.Validity, LCS.CutElim.Robinson, LCS.FOResolution.Method.Completeness.Completeness, LCS.FirstOrder.Completeness, LCS.FirstOrder.Completeness.Basic, LCS.FirstOrder.Completeness.InfiniteSearch, LCS.FirstOrder.Completeness.MetaTheorems, LCS.FirstOrder.Completeness.Search.Part1, LCS.FirstOrder.Completeness.Search.Part2, LCS.FirstOrder.Equality.MetaTheorems, LCS.FirstOrder.Equality.Part1, LCS.FirstOrder.Equality.Part2, LCS.FirstOrder.Equality.Search.Part1, LCS.FirstOrder.Equality.Search.Part2, LCS.FirstOrder.Gentzen.Hintikka.Examples, LCS.FirstOrder.Gentzen.Part1, LCS.FirstOrder.Gentzen.Part2, LCS.FirstOrder.Gentzen.Search.NoFunction.Growth, LCS.FirstOrder.Gentzen.Search.NoFunction.LeafInvariant, LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.QuotientModel, LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.QuotientModel.Proofs, LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.CongruenceModel.Proofs, LCS.FirstOrder.ManySorted.Equality, LCS.FirstOrder.ManySorted.Equality.Reduction, LCS.FirstOrder.ManySorted.Gentzen.Calculus, LCS.FirstOrder.Semantics.Equivalence, LCS.Herbrand.HerbrandTheorem.Main.Part1, LCS.Herbrand.HerbrandTheorem.Main.Part2, LCS.Herbrand.HerbrandTheorem.Part1, LCS.Herbrand.HerbrandTheorem.Part2, LCS.Herbrand.Metatheory, LCS.Herbrand.SHGTheorem.Herbrand.SyntaxAllocation, LCS.Herbrand.SharpenedHauptsatz, LCS.Herbrand.SharpenedHauptsatz.Theorem.Part1, LCS.Herbrand.SharpenedHauptsatz.Theorem.Part2, LCS.Propositional.Infinite.Compactness, LCS.Propositional.Infinite.Compactness.Proofs, LCS.Propositional.Infinite.Part1, LCS.Propositional.Infinite.Part2, LCS.Propositional.Infinite.Part2.Proofs, LCS.Propositional.LK, LCS.Propositional.Semantics.TruthFunctions, LCS.Propositional.Systems.G, LCS.Propositional.Systems.G.Search.LeafExpansion, LCS.Propositional.Systems.G.Search.SearchRounds, LCS.Propositional.Systems.G.Search.Termination.Proofs, LCS.Propositional.Systems.G.Search.Validity.Proofs, LCS.Resolution.GCNF.Proofs, LCS.Resolution.Method.FiniteGraph.Proofs, LCS.Resolution.Method.Part1, LCS.Resolution.Method.Part2.Proofs, LCS.Util
/-- Construct Finset-sequent NNF evidence from its two pointwise sides. -/
theorem mk {L : Language} {Gamma Delta : LCS.Finset (FormulaN L)}
    (hGamma : ∀ A ∈ Gamma, FormulaN.isNNF A)
    (hDelta : ∀ A ∈ Delta, FormulaN.isNNF A) :
    IsNNF (Gamma, Delta) :=
  ⟨hGamma, hDelta⟩

/-- Every antecedent member of an NNF Finset sequent is in NNF. -/
theorem left {L : Language} {Gamma Delta : LCS.Finset (FormulaN L)}
    (h : IsNNF (Gamma, Delta)) {A : FormulaN L} (hA : A ∈ Gamma) :
    FormulaN.isNNF A :=
  h.1 A hA

/-- Every succedent member of an NNF Finset sequent is in NNF. -/
theorem right {L : Language} {Gamma Delta : LCS.Finset (FormulaN L)}
    (h : IsNNF (Gamma, Delta)) {A : FormulaN L} (hA : A ∈ Delta) :
    FormulaN.isNNF A :=
  h.2 A hA

/-- Inserting on the left preserves and reflects Finset-sequent NNF. -/
theorem insert_left_iff {L : Language} (A : FormulaN L)
    (Gamma Delta : LCS.Finset (FormulaN L)) :
    IsNNF (LCS.Finset.insert A Gamma, Delta) ↔
      FormulaN.isNNF A ∧ IsNNF (Gamma, Delta) := by
  constructor
  · intro h
    refine ⟨h.left (LCS.Finset.mem_insert.mpr (Or.inl rfl)), ?_⟩
    refine ⟨?_, h.2⟩
    intro B hB
    exact h.left (LCS.Finset.mem_insert.mpr (Or.inr hB))
  · rintro ⟨hA, h⟩
    refine ⟨?_, h.2⟩
    intro B hB
    rcases LCS.Finset.mem_insert.mp hB with hBA | hB
    · exact hBA ▸ hA
    · exact h.left hB

/-- Inserting an NNF formula on the left preserves Finset-sequent NNF. -/
theorem insert_left {L : Language} {A : FormulaN L}
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (hA : FormulaN.isNNF A) (h : IsNNF (Gamma, Delta)) :
    IsNNF (LCS.Finset.insert A Gamma, Delta) :=
  (insert_left_iff A Gamma Delta).2 ⟨hA, h⟩

/-- Inserting on the right preserves and reflects Finset-sequent NNF. -/
theorem insert_right_iff {L : Language} (A : FormulaN L)
    (Gamma Delta : LCS.Finset (FormulaN L)) :
    IsNNF (Gamma, LCS.Finset.insert A Delta) ↔
      FormulaN.isNNF A ∧ IsNNF (Gamma, Delta) := by
  constructor
  · intro h
    refine ⟨h.right (LCS.Finset.mem_insert.mpr (Or.inl rfl)), ?_⟩
    refine ⟨h.1, ?_⟩
    intro B hB
    exact h.right (LCS.Finset.mem_insert.mpr (Or.inr hB))
  · rintro ⟨hA, h⟩
    refine ⟨h.1, ?_⟩
    intro B hB
    rcases LCS.Finset.mem_insert.mp hB with hBA | hB
    · exact hBA ▸ hA
    · exact h.right hB

/-- Inserting an NNF formula on the right preserves Finset-sequent NNF. -/
theorem insert_right {L : Language} {A : FormulaN L}
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (hA : FormulaN.isNNF A) (h : IsNNF (Gamma, Delta)) :
    IsNNF (Gamma, LCS.Finset.insert A Delta) :=
  (insert_right_iff A Gamma Delta).2 ⟨hA, h⟩

/-- Pointwise union on both sides preserves and reflects Finset-sequent NNF. -/
theorem union_iff {L : Language}
    (Gamma₁ Delta₁ Gamma₂ Delta₂ : LCS.Finset (FormulaN L)) :
    IsNNF
        (LCS.Finset.union Gamma₁ Gamma₂, LCS.Finset.union Delta₁ Delta₂) ↔
      IsNNF (Gamma₁, Delta₁) ∧ IsNNF (Gamma₂, Delta₂) := by
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro A hA
      exact h.left (LCS.Finset.mem_union.mpr (Or.inl hA))
    · intro A hA
      exact h.right (LCS.Finset.mem_union.mpr (Or.inl hA))
    · intro A hA
      exact h.left (LCS.Finset.mem_union.mpr (Or.inr hA))
    · intro A hA
      exact h.right (LCS.Finset.mem_union.mpr (Or.inr hA))
  · rintro ⟨h₁, h₂⟩
    constructor
    · intro A hA
      rcases LCS.Finset.mem_union.mp hA with hA | hA
      · exact h₁.left hA
      · exact h₂.left hA
    · intro A hA
      rcases LCS.Finset.mem_union.mp hA with hA | hA
      · exact h₁.right hA
      · exact h₂.right hA

/-- Pointwise union of two NNF Finset sequents is in NNF. -/
theorem union {L : Language}
    {Gamma₁ Delta₁ Gamma₂ Delta₂ : LCS.Finset (FormulaN L)}
    (h₁ : IsNNF (Gamma₁, Delta₁)) (h₂ : IsNNF (Gamma₂, Delta₂)) :
    IsNNF
      (LCS.Finset.union Gamma₁ Gamma₂, LCS.Finset.union Delta₁ Delta₂) :=
  (union_iff Gamma₁ Delta₁ Gamma₂ Delta₂).2 ⟨h₁, h₂⟩

end IsNNF

end G1nnfFinsetSequent

-- ===================================================================
-- Definition 6.4.2: G1nnfRule — Inference rules of the system G1nnf
-- ===================================================================

/-- Definition 6.4.6 (companion): The base inference rules used by G1nnf=,
over an arbitrary language. The rules operate on pairs of finite sets
of NNF formulae. The rules include four axiom schemas (positive atomic,
negative atomic, complementary left, complementary right), the cut rule,
propositional rules (conjunction left 1 and 2, conjunction right,
disjunction left, disjunction right 1 and 2), and quantifier rules
(universal left, universal right with eigenvariable, existential left
with eigenvariable, existential right). Each constructor carries the
principal formula and relevant parameters (terms for instantiation,
variables for eigenvariable conditions). -/
@[blueprint "chap6__definition_6_4_6"]
inductive G1nnfRule (L : Language) : Type where
  /-- Axiom (positive atomic): Gamma, A -> A, Delta where A is atomic -/
  | axiomPosAtomic (A : FormulaN L) (hAtom : A.isAtomic = true)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G1nnfRule L
  /-- Axiom (negative atomic): Gamma, neg A -> neg A, Delta where A
      is atomic -/
  | axiomNegAtomic (A : FormulaN L) (hAtom : A.isAtomic = true)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G1nnfRule L
  /-- Axiom (complementary left): Gamma, A, neg A -> Delta where A
      is atomic -/
  | axiomCompLeft (A : FormulaN L) (hAtom : A.isAtomic = true)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G1nnfRule L
  /-- Axiom (complementary right): Gamma -> Delta, A, neg A where A
      is atomic -/
  | axiomCompRight (A : FormulaN L) (hAtom : A.isAtomic = true)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G1nnfRule L
  /-- Cut rule: from Gamma -> Delta, A and A, Lambda -> Theta infer
      Gamma, Lambda -> Delta, Theta. A is the cut formula; Lam and Theta
      are the independent contexts of the second premise. -/
  | cut (A : FormulaN L) (Lam Theta : LCS.Finset (FormulaN L)) : G1nnfRule L
  /-- Conjunction left (variant 1): from A, Gamma -> Delta infer
      A and B, Gamma -> Delta -/
  | conjLeft1 (A B : FormulaN L) : G1nnfRule L
  /-- Conjunction left (variant 2): from B, Gamma -> Delta infer
      A and B, Gamma -> Delta -/
  | conjLeft2 (A B : FormulaN L) : G1nnfRule L
  /-- Conjunction right: from Gamma -> Delta, A and Gamma -> Delta, B
      infer Gamma -> Delta, A and B -/
  | conjRight (A B : FormulaN L) : G1nnfRule L
  /-- Disjunction left: from A, Gamma -> Delta and B, Gamma -> Delta
      infer A or B, Gamma -> Delta -/
  | disjLeft (A B : FormulaN L) : G1nnfRule L
  /-- Disjunction right (variant 1): from Gamma -> Delta, A infer
      Gamma -> Delta, A or B -/
  | disjRight1 (A B : FormulaN L) : G1nnfRule L
  /-- Disjunction right (variant 2): from Gamma -> Delta, B infer
      Gamma -> Delta, A or B -/
  | disjRight2 (A B : FormulaN L) : G1nnfRule L
  /-- Universal quantification left: from A[t/x], Gamma -> Delta infer
      forall x A, Gamma -> Delta, where t is free for x in A -/
  | allLeft (x : Nat) (A : FormulaN L) (t : Term L) : G1nnfRule L
  /-- Universal quantification right: from Gamma -> Delta, A[y/x] infer
      Gamma -> Delta, forall x A, where y is the eigenvariable not free
      in the conclusion -/
  | allRight (x : Nat) (A : FormulaN L) (y : Nat) : G1nnfRule L
  /-- Existential quantification left: from A[y/x], Gamma -> Delta
      infer exists x A, Gamma -> Delta, where y is the eigenvariable
      not free in the conclusion -/
  | exLeft (x : Nat) (A : FormulaN L) (y : Nat) : G1nnfRule L
  /-- Existential quantification right: from Gamma -> Delta, A[t/x]
      infer Gamma -> Delta, exists x A, where t is free for x
      in A -/
  | exRight (x : Nat) (A : FormulaN L) (t : Term L) : G1nnfRule L

/-- Definition 6.4.2: The G1nnf inference rules over a language without equality. -/
@[blueprint "chap6__definition_6_4_2" (main := true)]
abbrev G1nnfRuleNoEq (L : Language) (hL : L.withoutEquality) := G1nnfRule L

-- ===================================================================
-- Definition 6.4.2 (companion def): G1nnfRule.conclusion
-- ===================================================================



namespace G1nnfRule

open LCS.FirstOrder.SyntaxN.Substitution
open LCS.Finset

/-- Definition 6.4.6 (companion): Returns the conclusion sequent
(as a pair of Finsets) of a G1nnf rule applied in context Finsets
Gamma and Delta. The principal formula is introduced in the conclusion
while the side formulae appear in the premises. Uses Finset.insert
to match the textbook's set-based formulation of Def 6.4.2. -/
@[blueprint "chap6__definition_6_4_6"]
noncomputable def conclusion {L : Language} :
    G1nnfRule L → LCS.Finset (FormulaN L) → LCS.Finset (FormulaN L) →
    LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)
  | .axiomPosAtomic A _ rG rD, _, _ =>
    (LCS.Finset.insert A rG, LCS.Finset.insert A rD)
  | .axiomNegAtomic A _ rG rD, _, _ =>
    (LCS.Finset.insert (.neg A) rG, LCS.Finset.insert (.neg A) rD)
  | .axiomCompLeft A _ rG rD, _, _ =>
    (LCS.Finset.insert A (LCS.Finset.insert (.neg A) rG), rD)
  | .axiomCompRight A _ rG rD, _, _ =>
    (rG, LCS.Finset.insert A (LCS.Finset.insert (.neg A) rD))
  | .cut _ Lam Theta, Gamma, Delta =>
    (LCS.Finset.union Gamma Lam, LCS.Finset.union Delta Theta)
  | .conjLeft1 A B, Gamma, Delta =>
    (LCS.Finset.insert (.conj A B) Gamma, Delta)
  | .conjLeft2 A B, Gamma, Delta =>
    (LCS.Finset.insert (.conj A B) Gamma, Delta)
  | .conjRight A B, Gamma, Delta =>
    (Gamma, LCS.Finset.insert (.conj A B) Delta)
  | .disjLeft A B, Gamma, Delta =>
    (LCS.Finset.insert (.disj A B) Gamma, Delta)
  | .disjRight1 A B, Gamma, Delta =>
    (Gamma, LCS.Finset.insert (.disj A B) Delta)
  | .disjRight2 A B, Gamma, Delta =>
    (Gamma, LCS.Finset.insert (.disj A B) Delta)
  | .allLeft x A _, Gamma, Delta =>
    (LCS.Finset.insert (.all x A) Gamma, Delta)
  | .allRight x A _, Gamma, Delta =>
    (Gamma, LCS.Finset.insert (.all x A) Delta)
  | .exLeft x A _, Gamma, Delta =>
    (LCS.Finset.insert (.ex x A) Gamma, Delta)
  | .exRight x A _, Gamma, Delta =>
    (Gamma, LCS.Finset.insert (.ex x A) Delta)

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Freshening, LCS.CutElim.Hauptsatz.CutElimination.Substitution, LCS.CutElim.Hauptsatz.Equality.Part2
/-- A cut with Lambda = Gamma and Theta = Delta concludes Gamma -> Delta. -/
theorem cut_shared_conclusion {L : Language} (A : FormulaN L)
    (Gamma Delta : LCS.Finset (FormulaN L)) :
    conclusion (.cut A Gamma Delta) Gamma Delta = (Gamma, Delta) := by
  apply Prod.ext <;> apply LCS.Finset.ext <;> intro F
  all_goals simp only [conclusion, LCS.Finset.mem_union, or_self]

-- ===================================================================
-- Definition 6.4.2 (companion def): G1nnfRule.premises
-- ===================================================================

/-- Definition 6.4.6 (companion): Returns the list of premise sequents
(as pairs of Finsets) for each G1nnf rule applied in context Finsets
Gamma and Delta. Axioms have no premises (empty list). One-premise
rules return a singleton list. Two-premise rules (cut, conjRight,
disjLeft) return a pair. The side formulae (substitution instances or
subformulae) appear in the premises. -/
@[blueprint "chap6__definition_6_4_6"]
noncomputable def premises {L : Language} :
    G1nnfRule L → LCS.Finset (FormulaN L) → LCS.Finset (FormulaN L) →
    List (LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L))
  | .axiomPosAtomic _ _ _ _, _, _ => []
  | .axiomNegAtomic _ _ _ _, _, _ => []
  | .axiomCompLeft _ _ _ _, _, _ => []
  | .axiomCompRight _ _ _ _, _, _ => []
  | .cut A Lam Theta, Gamma, Delta =>
    [(Gamma, LCS.Finset.insert A Delta),
     (LCS.Finset.insert A Lam, Theta)]
  | .conjLeft1 A _, Gamma, Delta =>
    [(LCS.Finset.insert A Gamma, Delta)]
  | .conjLeft2 _ B, Gamma, Delta =>
    [(LCS.Finset.insert B Gamma, Delta)]
  | .conjRight A B, Gamma, Delta =>
    [(Gamma, LCS.Finset.insert A Delta),
     (Gamma, LCS.Finset.insert B Delta)]
  | .disjLeft A B, Gamma, Delta =>
    [(LCS.Finset.insert A Gamma, Delta),
     (LCS.Finset.insert B Gamma, Delta)]
  | .disjRight1 A _, Gamma, Delta =>
    [(Gamma, LCS.Finset.insert A Delta)]
  | .disjRight2 _ B, Gamma, Delta =>
    [(Gamma, LCS.Finset.insert B Delta)]
  | .allLeft x A t, Gamma, Delta =>
    [(LCS.Finset.insert (formulaSubstN A t x) Gamma, Delta)]
  | .allRight x A y, Gamma, Delta =>
    [(Gamma, LCS.Finset.insert (formulaSubstN A (.var y) x) Delta)]
  | .exLeft x A y, Gamma, Delta =>
    [(LCS.Finset.insert (formulaSubstN A (.var y) x) Gamma, Delta)]
  | .exRight x A t, Gamma, Delta =>
    [(Gamma, LCS.Finset.insert (formulaSubstN A t x) Delta)]

-- ===================================================================
-- Definition 6.4.2 (companion def): G1nnfRule.SideConditions
-- ===================================================================

/-- Definition 6.4.6 (companion): Side conditions of a base G1nnf rule.
The axiom, propositional, and cut rules have no additional conditions.
For universal-left and existential-right, the instantiating term must
be free for the quantified variable in the body. For universal-right
and existential-left, the eigenvariable must be free for the quantified
variable in the body and absent from the free variables of every formula
in both contexts and of the principal quantified formula. Thus it does
not occur free anywhere in the lower sequent, exactly as required by
Definition 6.4.2. -/
@[blueprint "chap6__definition_6_4_6"]
def SideConditions {L : Language} :
    G1nnfRule L → LCS.Finset (FormulaN L) → LCS.Finset (FormulaN L) → Prop
  | .axiomPosAtomic _ _ _ _, _, _ => True
  | .axiomNegAtomic _ _ _ _, _, _ => True
  | .axiomCompLeft _ _ _ _, _, _ => True
  | .axiomCompRight _ _ _ _, _, _ => True
  | .cut _ _ _, _, _ => True
  | .conjLeft1 _ _, _, _ => True
  | .conjLeft2 _ _, _, _ => True
  | .conjRight _ _, _, _ => True
  | .disjLeft _ _, _, _ => True
  | .disjRight1 _ _, _, _ => True
  | .disjRight2 _ _, _, _ => True
  | .allLeft x A t, _, _ =>
    isFreeForN t x A
  | .allRight x A y, Gamma, Delta =>
    isFreeForN (.var y) x A ∧
    y ∉ formulaFVN (.all x A) ∧
    (∀ F ∈ Gamma, y ∉ formulaFVN F) ∧
    (∀ F ∈ Delta, y ∉ formulaFVN F)
  | .exLeft x A y, Gamma, Delta =>
    isFreeForN (.var y) x A ∧
    y ∉ formulaFVN (.ex x A) ∧
    (∀ F ∈ Gamma, y ∉ formulaFVN F) ∧
    (∀ F ∈ Delta, y ∉ formulaFVN F)
  | .exRight x A t, _, _ =>
    isFreeForN t x A

/-- A legal G1nnf rule application satisfies the rule-specific side
conditions and has an NNF conclusion sequent. When this condition is stored
at every recursive proof-tree node, premise subtrees enforce the same
invariant at the next level. -/
@[blueprint "chap6__definition_6_4_6"]
def ApplicationConditions {L : Language}
    (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L)) : Prop :=
  SideConditions rule Gamma Delta ∧
    G1nnfFinsetSequent.IsNNF (rule.conclusion Gamma Delta)

-- END PROOF

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.EigenWeakening, LCS.CutElim.Hauptsatz.CutElimination.Freshening, LCS.CutElim.Hauptsatz.CutElimination.Trees, LCS.CutElim.Hauptsatz.Equality.Part1
/-- Definition 6.4.2 (companion regression): The free-for and three
freshness witnesses construct positive universal-right side conditions. -/
theorem sideConditions_allRight_of_fresh {L : Language}
    (x y : Nat) (A : FormulaN L)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (hFreeFor : isFreeForN (.var y) x A)
    (hFreshPrincipal : y ∉ formulaFVN (.all x A))
    (hFreshGamma : ∀ F ∈ Gamma, y ∉ formulaFVN F)
    (hFreshDelta : ∀ F ∈ Delta, y ∉ formulaFVN F) :
    SideConditions (.allRight x A y) Gamma Delta :=
  ⟨hFreeFor, hFreshPrincipal, hFreshGamma, hFreshDelta⟩

-- END PROOF

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.EigenWeakening, LCS.CutElim.Hauptsatz.CutElimination.Trees
/-- Definition 6.4.2 (companion regression): The free-for and three
freshness witnesses construct positive existential-left side conditions. -/
theorem sideConditions_exLeft_of_fresh {L : Language}
    (x y : Nat) (A : FormulaN L)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (hFreeFor : isFreeForN (.var y) x A)
    (hFreshPrincipal : y ∉ formulaFVN (.ex x A))
    (hFreshGamma : ∀ F ∈ Gamma, y ∉ formulaFVN F)
    (hFreshDelta : ∀ F ∈ Delta, y ∉ formulaFVN F) :
    SideConditions (.exLeft x A y) Gamma Delta :=
  ⟨hFreeFor, hFreshPrincipal, hFreshGamma, hFreshDelta⟩


-- END PROOF




-- END PROOF

end G1nnfRule

-- ===================================================================
-- Example 6.4.1 (companion type): NnfExPred
-- ===================================================================

/-- Example 6.4.1 (companion type): Predicate symbols for the
example language: P (unary), Q (unary), R (binary). -/
@[blueprint "chap6__example_6_4_1"]
inductive NnfExPred : Type where
  | P : NnfExPred
  | Q : NnfExPred
  | R : NnfExPred

-- ===================================================================
-- Example 6.4.1 (companion def): nnfExLang
-- ===================================================================

/-- Example 6.4.1 (companion): The example language with predicates
P (unary), Q (unary), R (binary), no function symbols, constants or equality. -/
@[blueprint "chap6__example_6_4_1"]
def nnfExLang : Language where
  funSymbols := Empty
  funArity := fun e => e.elim
  constSymbols := Empty
  predSymbols := NnfExPred
  predArity := fun
    | .P => 1
    | .Q => 1
    | .R => 2
  hasEquality := false

/-- Example 6.4.1 (helper): Build a Fin 1 -> Term from a single
variable index. -/
@[blueprint "chap6__example_6_4_1"]
def nnfVec1 (n : Nat) : Fin 1 → Term nnfExLang
  | ⟨0, _⟩ => .var n

/-- Example 6.4.1 (helper): Build a Fin 2 -> Term from two
variable indices. -/
@[blueprint "chap6__example_6_4_1"]
def nnfVec2 (n m : Nat) : Fin 2 → Term nnfExLang
  | ⟨0, _⟩ => .var n
  | ⟨1, _⟩ => .var m

-- ===================================================================
-- Example 6.4.1: nnfEx_formulaA
-- ===================================================================

/-- Example 6.4.1: The formula
A = forall x (P(x) or not exists y (Q(y) and R(x, y)))
    or not (P(y) and not forall x P(x)).
Variables: x = 0, y = 1. -/
@[blueprint "chap6__example_6_4_1"]
def nnfEx_formulaA : FormulaN nnfExLang :=
  .disj
    (.all 0
      (.disj
        (.predN .P (nnfVec1 0))
        (.neg
          (.ex 1
            (.conj
              (.predN .Q (nnfVec1 1))
              (.predN .R (nnfVec2 0 1)))))))
    (.neg
      (.conj
        (.predN .P (nnfVec1 1))
        (.neg (.all 0 (.predN .P (nnfVec1 0))))))

-- ===================================================================
-- Example 6.4.1 (companion def): nnfEx_subNnf1
-- ===================================================================

/-- Example 6.4.1 (companion): The NNF of not exists y (Q(y) and R(x, y))
is forall y (not Q(y) or not R(x, y)). Demonstrates quantifier
negation and De Morgan's law. -/
@[blueprint "chap6__example_6_4_1"]
def nnfEx_subNnf1 : FormulaN nnfExLang :=
  .all 1
    (.disj
      (.neg (.predN .Q (nnfVec1 1)))
      (.neg (.predN .R (nnfVec2 0 1))))

/-- Example 6.4.1: Converting ¬∃y (Q(y) ∧ R(x, y)) gives
∀y (¬Q(y) ∨ ¬R(x, y)), with x = 0 and y = 1. -/
@[blueprint "chap6__example_6_4_1" (main := true)]
theorem nnfEx_subNnf1_spec :
    FormulaN.toNNF (L := nnfExLang)
      (.neg (.ex 1 (.conj (.predN .Q (nnfVec1 1))
        (.predN .R (nnfVec2 0 1))))) = nnfEx_subNnf1 

-- ===================================================================
-- Example 6.4.1 (companion def): nnfEx_subNnf2
-- ===================================================================

/-- Example 6.4.1 (companion): The NNF of not (P(y) and not forall x P(x))
is (not P(y) or forall x P(x)). Demonstrates conjunction negation
and double negation elimination. -/
@[blueprint "chap6__example_6_4_1"]
def nnfEx_subNnf2 : FormulaN nnfExLang :=
  .disj
    (.neg (.predN .P (nnfVec1 1)))
    (.all 0 (.predN .P (nnfVec1 0)))

/-- Example 6.4.1: Converting ¬(P(y) ∧ ¬∀x P(x)) gives
¬P(y) ∨ ∀x P(x), with x = 0 and y = 1. -/
@[blueprint "chap6__example_6_4_1" (main := true)]
theorem nnfEx_subNnf2_spec :
    FormulaN.toNNF (L := nnfExLang)
      (.neg (.conj (.predN .P (nnfVec1 1))
        (.neg (.all 0 (.predN .P (nnfVec1 0)))))) = nnfEx_subNnf2 

-- ===================================================================
-- Example 6.4.1 (companion def): nnfEx_formulaA_nnf
-- ===================================================================

/-- Example 6.4.1: The complete NNF of A is
forall x (P(x) or forall y (not Q(y) or not R(x, y)))
or (not P(y) or forall x P(x)). -/
@[blueprint "chap6__example_6_4_1"]
def nnfEx_formulaA_nnf : FormulaN nnfExLang :=
  .disj
    (.all 0
      (.disj
        (.predN .P (nnfVec1 0))
        (.all 1
          (.disj
            (.neg (.predN .Q (nnfVec1 1)))
            (.neg (.predN .R (nnfVec2 0 1)))))))
    (.disj
      (.neg (.predN .P (nnfVec1 1)))
      (.all 0 (.predN .P (nnfVec1 0))))

/-- Example 6.4.1: Converting A gives the displayed complete NNF. -/
@[blueprint "chap6__example_6_4_1" (main := true)]
theorem nnfEx_formulaA_nnf_spec :
    FormulaN.toNNF nnfEx_formulaA = nnfEx_formulaA_nnf 

-- ===================================================================
-- Lemma 6.4.1: nnf_equivalence — every FormulaN has an NNF equivalent
-- ===================================================================



/-- Lemma 6.4.1: Every FormulaN is equivalent to another FormulaN
in negation normal form. -/
@[blueprint "chap6__lemma_6_4_1" (main := true)]
theorem nnf_equivalence {L : Language} (A : FormulaN L) :
    ∃ B : FormulaN L,
      FormulaN.isNNF B ∧ foLogEquivN A B 

end LCS.CutElim.Hauptsatz
