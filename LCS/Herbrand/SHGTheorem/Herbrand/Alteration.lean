import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.SyntaxAllocation
import LCS.Herbrand.SHGTheorem.Herbrand.OccurrenceLineage
import LCS.Herbrand.SHGTheorem.Herbrand.CanonicalMapRegression
import LCS.Herbrand.SHGTheorem.Herbrand.NestedMapRegression

section
namespace LCS.Herbrand.SHGTheorem.Herbrand
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.Equality
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.Herbrand.PrenexForm
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae

/-- Lemma 7.6.2 (companion structure): Proof-relevant capability for
a G2nnf source tree whose `∃:left` occurrences admit one exact
canonical eigenvariable-to-Skolem map. This is Type-valued data, not a
proposition from which a map is recovered by choice: a caller must
supply both the map and its occurrence-sensitive canonicality
certificate. -/
structure G2nnfSkolemCanonicalizable {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] (spec : SkolemSpec L)
    {Γ Δ : LCS.Finset (FormulaN L)}
    (sourceTree : G2nnfProofTree hL Γ Δ) : Type where
  /-- The exact map to be consumed by the alteration. -/
  eigenvarMap : EigenvarSkolemMap spec
  /-- Exact domain, allocation, lineage, ordering, range, and
  capture-safety evidence for that map and this source tree. -/
  canonical :
    IsCanonicalEigenvarMapG2nnf (hL := hL) sourceTree spec eigenvarMap

/-- Lemma 7.6.2 (companion structure): Exact sharpened-Hauptsatz
input in an equality-free language consumed by the G2 bottom-up alteration.
The indexed source tree
is rooted at `spec.source ->`; its cut-free and pure-variable
certificates and its occurrence-sensitive midsequent witness are the
actual outputs supplied by Theorem 7.4.1. Canonicalizability is
additional explicit source data: this interface does not claim that
cut-freeness, purity, and a midsequent witness manufacture it. -/
structure G2nnfSkolemAlterationInput {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] (spec : SkolemSpec L) where
  /-- The exact proof tree to alter, rooted at the source sentence. -/
  sourceTree : G2nnfProofTree hL
    ({spec.source} : LCS.Finset (FormulaN L))
    (∅ : LCS.Finset (FormulaN L))
  /-- A proof-relevant canonical map for this exact source tree. -/
  sourceCanonicalization :
    G2nnfSkolemCanonicalizable (hL := hL) spec sourceTree
  /-- The exact midsequent occurrence selected in `sourceTree`. -/
  midsequent :
    LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)
  /-- Theorem 7.4.1 supplies a cut-free G2 proof. -/
  sourceCutFree : sourceTree.isCutFree
  /-- Theorem 7.4.1 supplies a pure-variable G2 proof. -/
  sourcePureVariable : IsPureVariableProofG2nnf sourceTree
  /-- Theorem 7.4.1 ties the midsequent to one exact tree occurrence. -/
  sourceMidsequent : IsMidsequentG2nnf sourceTree midsequent

/-- Lemma 7.6.2 (companion structure): Result of the G2 bottom-up
eigenvariable-to-Skolem alteration. The final heterogeneous map is the
exact map carried by `input.sourceCanonicalization`, rather than a
second map chosen by the result. The altered proof is indexed directly
by `SK spec ->`. Its midsequent is not an arbitrary output: it is the
safe final substitution of the exact input midsequent. -/
structure G2nnfSkolemAlteration {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] (spec : SkolemSpec L)
    [DecidableEq (FormulaN spec.language)]
    (input : G2nnfSkolemAlterationInput (hL := hL) spec) where
  /-- Capture-safety at the exact input midsequent antecedent. -/
  midAntecedentFreeFor :
    EigenvarSkolemMapFreeForFinset spec
      input.sourceCanonicalization.eigenvarMap input.midsequent.1
  /-- Capture-safety at the exact input midsequent succedent. -/
  midSuccedentFreeFor :
    EigenvarSkolemMapFreeForFinset spec
      input.sourceCanonicalization.eigenvarMap input.midsequent.2
  /-- The altered proof has the textbook target root `SK spec ->`. -/
  alteredTree : G2nnfProofTree (L := spec.language) hL
    ({SK spec} : LCS.Finset (FormulaN spec.language))
    (∅ : LCS.Finset (FormulaN spec.language))
  /-- The altered midsequent is exactly the capture-safe final
  substitution of `input.midsequent`, and occurs in `alteredTree`. -/
  alteredMidsequent :
    IsMidsequentG2nnf alteredTree
      (applyEigenvarSubstFinset spec
          input.sourceCanonicalization.eigenvarMap input.midsequent.1
          midAntecedentFreeFor,
       applyEigenvarSubstFinset spec
          input.sourceCanonicalization.eigenvarMap input.midsequent.2
          midSuccedentFreeFor)

/-- Computed compatibility projection for the unique map consumed by a
G2 alteration. It cannot differ from the map in the input capability. -/
def G2nnfSkolemAlteration.eigenvarMap {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {spec : SkolemSpec L}
    [DecidableEq (FormulaN spec.language)]
    {input : G2nnfSkolemAlterationInput (hL := hL) spec}
    (_ : G2nnfSkolemAlteration (hL := hL) spec input) :
    EigenvarSkolemMap spec :=
  input.sourceCanonicalization.eigenvarMap

/-- Computed compatibility theorem for the canonicality certificate
carried by the input capability. -/
theorem G2nnfSkolemAlteration.canonical {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {spec : SkolemSpec L}
    [DecidableEq (FormulaN spec.language)]
    {input : G2nnfSkolemAlterationInput (hL := hL) spec}
    (alteration : G2nnfSkolemAlteration (hL := hL) spec input) :
    IsCanonicalEigenvarMapG2nnf (hL := hL) input.sourceTree spec
      alteration.eigenvarMap :=
  input.sourceCanonicalization.canonical

/-- Lemma 7.6.2 (companion def): Perform the G2 bottom-up alteration
on an explicitly canonicalizable sharpened-Hauptsatz input in an
equality-free language. The implementation consumes the exact map and certificate in
`input.sourceCanonicalization`, alters the indexed source tree to
`SK spec ->`, and preserves the exact midsequent through the safe final
substitution recorded by `G2nnfSkolemAlteration`. -/
def eigenvariableToSkolemSubst {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] (spec : SkolemSpec L)
    [DecidableEq (FormulaN spec.language)]
    (input : G2nnfSkolemAlterationInput (hL := hL) spec) :
    G2nnfSkolemAlteration (hL := hL) spec input := by
  -- REPAIR(T7-23d): proof pending; pre-existing construction placeholder retained (OD-A17 / OD-7-14)
  sorry

/-- Lemma 7.6.2 (companion structure): Equality-system
sharpened-Hauptsatz input consumed by the symmetric alteration
specification. The indexed source tree is rooted at
`spec.source ->`; purity, absence of essential cuts, and the
occurrence-sensitive equality midsequent are exactly the evidence
provided by Theorem 7.4.2. -/
structure G2nnfEqSkolemAlterationInput {L : Language}
    (hL : L.hasEquality = true)
    [DecidableEq (FormulaN L)] (spec : SkolemSpec L) where
  /-- The exact equality proof tree to alter. -/
  sourceTree : G2nnfEqProofTree hL
    ({spec.source} : LCS.Finset (FormulaN L))
    (∅ : LCS.Finset (FormulaN L))
  /-- The exact equality midsequent occurrence selected in the tree. -/
  midsequent :
    LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)
  /-- Theorem 7.4.2 supplies a pure-variable equality proof. -/
  sourcePureVariable : IsPureVariableProof_G2nnfEq sourceTree
  /-- Theorem 7.4.2 supplies a proof without essential cuts. -/
  sourceHasNoEssentialCuts : sourceTree.hasNoEssentialCuts
  /-- Theorem 7.4.2 ties the midsequent to one exact tree occurrence. -/
  sourceMidsequent : IsMidsequent_G2nnfEq sourceTree midsequent

/-- Lemma 7.6.2 (companion structure): Exact equality-system target
of the bottom-up alteration. The canonical relation follows only
`.base` G2 quantifier occurrences inside the equality proof tree. The
altered tree is indexed by `SK spec ->`, and its equality midsequent
is the safe final substitution of the exact input midsequent. -/
structure G2nnfEqSkolemAlteration {L : Language}
    (hL : L.hasEquality = true)
    [DecidableEq (FormulaN L)] (spec : SkolemSpec L)
    [DecidableEq (FormulaN spec.language)]
    (input : G2nnfEqSkolemAlterationInput hL spec) where
  /-- Final internally chosen equality-system partial substitution. -/
  eigenvarMap : EigenvarSkolemMap spec
  /-- Exact `.base` occurrence linkage and canonical-map certificate. -/
  canonical :
    IsCanonicalEigenvarMapG2nnfEq input.sourceTree spec eigenvarMap
  /-- Capture-safety at the exact input midsequent antecedent. -/
  midAntecedentFreeFor :
    EigenvarSkolemMapFreeForFinset spec eigenvarMap input.midsequent.1
  /-- Capture-safety at the exact input midsequent succedent. -/
  midSuccedentFreeFor :
    EigenvarSkolemMapFreeForFinset spec eigenvarMap input.midsequent.2
  /-- The altered equality proof has target root `SK spec ->`. -/
  alteredTree : G2nnfEqProofTree (L := spec.language) hL
    ({SK spec} : LCS.Finset (FormulaN spec.language))
    (∅ : LCS.Finset (FormulaN spec.language))
  /-- The altered equality midsequent is exactly the capture-safe
  final substitution of `input.midsequent`. -/
  alteredMidsequent :
    IsMidsequent_G2nnfEq alteredTree
      (applyEigenvarSubstFinset spec eigenvarMap input.midsequent.1
          midAntecedentFreeFor,
       applyEigenvarSubstFinset spec eigenvarMap input.midsequent.2
          midSuccedentFreeFor)

/-- Lemma 7.6.2 (companion specification): Type-valued target for the
future equality alteration implementation. This declaration asserts
no inhabitant and therefore introduces neither a fabricated equality
tree nor a second staged proof hole. -/
def eigenvariableToSkolemSubstEqTarget {L : Language}
    (hL : L.hasEquality = true)
    [DecidableEq (FormulaN L)] (spec : SkolemSpec L)
    [DecidableEq (FormulaN spec.language)]
    (input : G2nnfEqSkolemAlterationInput hL spec) : Type :=
  G2nnfEqSkolemAlteration hL spec input

end LCS.Herbrand.SHGTheorem.Herbrand
end

section
namespace LCS.Herbrand.SHGTheorem.Herbrand
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.Equality
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.Herbrand.PrenexForm
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
namespace EigenvariableToSkolemSubstInterfaceRegression

/-- The G2 interface has no separate bare map argument: after fixing
`spec`, its explicit input is the sharpened-Hauptsatz bundle carrying
proof-relevant source canonicalization data. -/
example {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    [DecidableEq (FormulaN spec.language)] :
    (input : G2nnfSkolemAlterationInput (hL := hL) spec) →
      G2nnfSkolemAlteration (hL := hL) spec input :=
  eigenvariableToSkolemSubst (hL := hL) spec

/-- The G2 result exposes the exact map and canonical certificate from
the input capability through computed compatibility projections. -/
example {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    [DecidableEq (FormulaN spec.language)]
    (input : G2nnfSkolemAlterationInput (hL := hL) spec) :
    IsCanonicalEigenvarMapG2nnf (hL := hL) input.sourceTree spec
      (eigenvariableToSkolemSubst (hL := hL) spec input).eigenvarMap :=
  (eigenvariableToSkolemSubst (hL := hL) spec input).canonical

/-- The compatibility map cannot vary with the alteration result. -/
example {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    [DecidableEq (FormulaN spec.language)]
    (input : G2nnfSkolemAlterationInput (hL := hL) spec) :
    (eigenvariableToSkolemSubst (hL := hL) spec input).eigenvarMap =
      input.sourceCanonicalization.eigenvarMap :=
  rfl

/-- The altered G2 tree is definitionally in `spec.language` and
rooted at the exact Skolem form, not at a caller-supplied mapped root. -/
example {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    [DecidableEq (FormulaN spec.language)]
    (input : G2nnfSkolemAlterationInput (hL := hL) spec) :
    G2nnfProofTree (L := spec.language) hL
      ({SK spec} : LCS.Finset (FormulaN spec.language))
      (∅ : LCS.Finset (FormulaN spec.language)) :=
  (eigenvariableToSkolemSubst (hL := hL) spec input).alteredTree

/-- The equality interface likewise accepts no map and returns only
the exact Type-valued target specification. -/
example {L : Language} (hL : L.hasEquality = true)
    [DecidableEq (FormulaN L)] (spec : SkolemSpec L)
    [DecidableEq (FormulaN spec.language)] :
    (input : G2nnfEqSkolemAlterationInput hL spec) → Type :=
  eigenvariableToSkolemSubstEqTarget hL spec

/-- Any future equality inhabitant is forced to live in the exact
Skolem language and to prove `SK spec ->`. -/
example {L : Language} (hL : L.hasEquality = true)
    [DecidableEq (FormulaN L)] (spec : SkolemSpec L)
    [DecidableEq (FormulaN spec.language)]
    (input : G2nnfEqSkolemAlterationInput hL spec)
    (result : eigenvariableToSkolemSubstEqTarget hL spec input) :
    G2nnfEqProofTree (L := spec.language) hL
      ({SK spec} : LCS.Finset (FormulaN spec.language))
      (∅ : LCS.Finset (FormulaN spec.language)) := by
  exact result.alteredTree

end EigenvariableToSkolemSubstInterfaceRegression
end LCS.Herbrand.SHGTheorem.Herbrand
end

section
namespace LCS.Herbrand.SHGTheorem.Herbrand
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.Equality
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.Herbrand.PrenexForm
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae

/-- Lemma 7.6.2 (companion def): Predicate asserting that `Cs` is a
nonempty enumeration of the c-instances in the antecedent of one
actual midsequent occurrence of the equality-free proof of `B ->`. The explicit
midsequent witness ties the extracted formulae to `T`, records its
empty succedent, and retains genuine `CInstance` provenance for every
listed formula. -/
def midsequentCInstances {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (B : FormulaN L)
    (T : G2nnfProofTree hL
      ({B} : LCS.Finset (FormulaN L))
      (∅ : LCS.Finset (FormulaN L)))
    (mid : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L))
    (Cs : List (FormulaN L)) : Prop :=
  IsMidsequentG2nnf T mid ∧
  mid.2 = (∅ : LCS.Finset (FormulaN L)) ∧
  Cs ≠ [] ∧
  LCS.Finset.ofList Cs = mid.1 ∧
  (∀ C, C ∈ Cs → isCInstanceOf C B)

-- ===================================================================
-- Lemma 7.6.1 (helper): literal_cinstance_eq
-- ===================================================================

/-- Helper: A c-instance of a literal (atomic or negated atomic) must
equal the literal itself, since literals have no sub-structure to
instantiate. -/
theorem literal_cinstance_eq {L : Language}
    (A : FormulaN L)
    (hLit : A.isAtomic ∨ (∃ B, A = .neg B ∧ B.isAtomic))
    (K : FormulaN L)
    (hK : isCInstanceOf K A) : K = A := by
-- BEGIN PROOF
  obtain ⟨ci, hsrc, hform, _hwf⟩ := hK
  cases ci with
  | atom C hC =>
    have hs : C = A := hsrc
    have hf : C = K := by unfold CInstance.toFormula at hform; exact hform
    rw [← hf, hs]
  | negAtom C hC =>
    have hs : FormulaN.neg C = A := hsrc
    have hf : FormulaN.neg C = K := by
      unfold CInstance.toFormula at hform; exact hform
    rw [← hf, hs]
  | connective star C' D' _ _ =>
    -- ci.source = .conj C' D' (star = true) or .disj C' D' (star = false).
    -- hsrc equates this to A, but A is a literal — constructor mismatch.
    rcases hLit with hAtom | ⟨B, hNeg, _⟩
    · cases star with
      | true =>
        have hs : FormulaN.conj C' D' = A := by
          have := hsrc; unfold CInstance.source at this; exact this
        rw [← hs] at hAtom
        simp [FormulaN.isAtomic] at hAtom
      | false =>
        have hs : FormulaN.disj C' D' = A := by
          have := hsrc; unfold CInstance.source at this; exact this
        rw [← hs] at hAtom
        simp [FormulaN.isAtomic] at hAtom
    · subst hNeg
      cases star with
      | true =>
        have hs : FormulaN.conj C' D' = FormulaN.neg B := by
          have := hsrc; unfold CInstance.source at this; exact this
        exact absurd hs (by intro h; cases h)
      | false =>
        have hs : FormulaN.disj C' D' = FormulaN.neg B := by
          have := hsrc; unfold CInstance.source at this; exact this
        exact absurd hs (by intro h; cases h)
  | forallInst x C' _ _ _ _ _ _ =>
    -- ci.source = .all x C', but A is a literal — constructor mismatch.
    rcases hLit with hAtom | ⟨B, hNeg, _⟩
    · have hs : FormulaN.all x C' = A := by
        have := hsrc; unfold CInstance.source at this; exact this
      rw [← hs] at hAtom
      simp [FormulaN.isAtomic] at hAtom
    · subst hNeg
      have hs : FormulaN.all x C' = FormulaN.neg B := by
        have := hsrc; unfold CInstance.source at this; exact this
      exact absurd hs (by intro h; cases h)

/-- Helper: A literal is a c-instance of itself. -/
theorem literal_self_cinstance {L : Language}
    (A : FormulaN L)
    (hLit : A.isAtomic ∨ (∃ B, A = .neg B ∧ B.isAtomic)) :
    isCInstanceOf A A := by
-- BEGIN PROOF
  rcases hLit with hA | ⟨B, hEq, hB⟩
  · -- Atomic case: CInstance.atom A hA has source = A, toFormula = A.
    refine ⟨CInstance.atom A hA, ?_, ?_, ?_⟩
    · show CInstance.source (CInstance.atom A hA) = A
      unfold CInstance.source; rfl
    · show CInstance.toFormula (CInstance.atom A hA) = A
      unfold CInstance.toFormula; rfl
    · exact True.intro
  · -- Negated atomic case: A = .neg B with B atomic; use CInstance.negAtom B hB.
    subst hEq
    refine ⟨CInstance.negAtom B hB, ?_, ?_, ?_⟩
    · show CInstance.source (CInstance.negAtom B hB) = FormulaN.neg B
      unfold CInstance.source; rfl
    · show CInstance.toFormula (CInstance.negAtom B hB) = FormulaN.neg B
      unfold CInstance.toFormula; rfl
    · exact True.intro

-- ===================================================================
-- Lemma 7.6.1 (companion theorem): g2nnfCInstanceCombinationLiteral
-- ===================================================================

/-- Lemma 7.6.1 (companion theorem): Base case (i) in an equality-free language: if A is a literal (atomic or negated atomic), then its only c-instance is A itself, so K = L = A and D = A. The sequent D -> (K and L) becomes A -> (A and A), which is provable. -/
theorem g2nnfCInstanceCombinationLiteral {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (A : FormulaN L)
    (hLit : A.isAtomic ∨ (∃ B, A = .neg B ∧ B.isAtomic))
    (K Ls : FormulaN L)
    (hK : isCInstanceOf K A)
    (hL : isCInstanceOf Ls A) :
    ∃ D, isCInstanceOf D A ∧
      Nonempty (G2nnfProofTree hNoEq
        ({D} : LCS.Finset (FormulaN L))
        ({FormulaN.conj K Ls} : LCS.Finset (FormulaN L))) := by
-- BEGIN PROOF
  -- Since A is a literal, any c-instance of A equals A itself.
  have hKeq : K = A := literal_cinstance_eq A hLit K hK
  have hLeq : Ls = A := literal_cinstance_eq A hLit Ls hL
  refine ⟨A, literal_self_cinstance A hLit, ?_⟩
  rw [hKeq, hLeq]
  have hAQF : isQuantifierFree A := by
    rcases hLit with hAtom | ⟨B, rfl, hBAtom⟩
    · exact AllRectified.isQuantifierFree_of_isAtomic A hAtom
    · simpa [isQuantifierFree] using
        AllRectified.isQuantifierFree_of_isAtomic B hBAtom
  have hARect : isRectified A :=
    AllRectified.isRectified_of_isQuantifierFree A hAQF
  have hConjRect : isRectified (.conj A A) :=
    AllRectified.isRectified_of_isQuantifierFree (.conj A A)
      ⟨hAQF, hAQF⟩
  -- Build identity trees {C} ⊢ {C} for any literal C, then combine
  -- with conjRight to obtain {A} ⊢ {A ∧ A}.
  have atomicNNF : ∀ C : FormulaN L, C.isAtomic → C.isNNF := by
    intro C hC
    cases C <;> simp_all [FormulaN.isAtomic, FormulaN.isNNF]
  have hn : ∀ {B C : FormulaN L}, B.isNNF → C.isNNF →
      AllNNF (({B} : LCS.Finset (FormulaN L)), {C}) := by
    intro B C hB hC
    constructor <;> intro F h
    · have he := (LCS.Finset.mem_singleton F B).mp h
      subst F; exact hB
    · have he := (LCS.Finset.mem_singleton F C).mp h
      subst F; exact hC
  have hIdent : ∀ (C : FormulaN L),
      (C.isAtomic ∨ (∃ B, C = .neg B ∧ B.isAtomic)) →
      Nonempty (G2nnfProofTree hNoEq
        ({C} : LCS.Finset (FormulaN L))
        ({C} : LCS.Finset (FormulaN L))) := by
    intro C hC
    rcases hC with hAtom | ⟨B, hEq, hBAtom⟩
    · -- C atomic: use axiomPosId in empty context.
      refine ⟨G2nnfDeductionTreeCore.axiom_
        (G2nnfRuleCore.axiomPosId C hAtom LCS.Finset.empty LCS.Finset.empty)
        ⟨rfl, rfl⟩ rfl
        ⟨trivial, hn (atomicNNF C hAtom) (atomicNNF C hAtom),
          (by intro seq h; cases h), allRectified_singletons
          (AllRectified.isRectified_of_isAtomic C hAtom)
          (AllRectified.isRectified_of_isAtomic C hAtom)⟩⟩
    · -- C = .neg B with B atomic: use axiomNegId in empty context.
      subst hEq
      have hNegRect : isRectified (.neg B) :=
        AllRectified.isRectified_of_isQuantifierFree (.neg B)
          (by
            simpa [isQuantifierFree] using
              AllRectified.isQuantifierFree_of_isAtomic B hBAtom)
      have hNegNNF : (FormulaN.neg B).isNNF := by
        cases B <;> simp_all [FormulaN.isAtomic, FormulaN.isNNF]
      refine ⟨G2nnfDeductionTreeCore.axiom_
        (G2nnfRuleCore.axiomNegId B hBAtom LCS.Finset.empty LCS.Finset.empty)
        ⟨rfl, rfl⟩ rfl
        ⟨trivial, hn hNegNNF hNegNNF,
          (by intro seq h; cases h),
          allRectified_singletons hNegRect hNegRect⟩⟩
  obtain ⟨t1⟩ := hIdent A hLit
  obtain ⟨t2⟩ := hIdent A hLit
  -- conjRight A A in context ({A}, ∅):
  --   premises = [({A}, {A}), ({A}, {A})]
  --   conclusion = ({A}, {conj A A})
  have hANNF : A.isNNF := by
    rcases hLit with hAtom | ⟨B, rfl, hB⟩
    · exact atomicNNF A hAtom
    · cases B <;> simp_all [FormulaN.isAtomic, FormulaN.isNNF]
  refine ⟨G2nnfDeductionTreeCore.twoPremise
    (G2nnfRuleCore.conjRight A A
      ({A} : LCS.Finset (FormulaN L))
      (LCS.Finset.empty : LCS.Finset (FormulaN L)))
    trivial rfl
    ⟨trivial, hn hANNF ⟨hANNF, hANNF⟩,
      (by
        intro seq h
        simp only [G2nnfRuleCore.premises, List.mem_cons,
          List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> exact hn hANNF hANNF),
      allRectified_singletons hARect hConjRect⟩
    t1
    t2⟩

-- ===================================================================
-- Helper: Decompose c-instance of a connective (conj or disj)
-- ===================================================================

/-- Helper: A c-instance of a binary connective (conj or disj) decomposes
into c-instances of the subformulae. -/
theorem cinstance_connective_decompose {L : Language}
    (star : Bool) (B C K : FormulaN L)
    (hK : isCInstanceOf K (if star then FormulaN.conj B C else FormulaN.disj B C)) :
    ∃ (ciH ciK : CInstance L),
      ciH.source = B ∧ ciK.source = C ∧
      CInstance.WellFormed ciH ∧ CInstance.WellFormed ciK ∧
      K = (if star then FormulaN.conj ciH.toFormula ciK.toFormula
           else FormulaN.disj ciH.toFormula ciK.toFormula) := by
-- BEGIN PROOF
  obtain ⟨ci, hSrc, hForm, hWF⟩ := hK
  cases ci with
  | atom A hA =>
    -- ci.source = A, so hSrc : A = conj/disj B C. But A is atomic: contradiction.
    cases star with
    | true =>
      have hSrc' : A = FormulaN.conj B C := by
        have := hSrc
        unfold CInstance.source at this
        exact this
      rw [hSrc'] at hA
      cases hA
    | false =>
      have hSrc' : A = FormulaN.disj B C := by
        have := hSrc
        unfold CInstance.source at this
        exact this
      rw [hSrc'] at hA
      cases hA
  | negAtom A hA =>
    -- ci.source = .neg A, so hSrc : .neg A = conj/disj B C. Contradiction.
    cases star with
    | true =>
      have hSrc' : FormulaN.neg A = FormulaN.conj B C := by
        have := hSrc
        unfold CInstance.source at this
        exact this
      exact absurd hSrc' (by intro h; cases h)
    | false =>
      have hSrc' : FormulaN.neg A = FormulaN.disj B C := by
        have := hSrc
        unfold CInstance.source at this
        exact this
      exact absurd hSrc' (by intro h; cases h)
  | connective cStar C' D' H K' =>
    -- ci.source depends on cStar. hSrc : conj/disj C' D' = conj/disj B C.
    cases star with
    | true =>
      cases cStar with
      | true =>
        -- hSrc : conj C' D' = conj B C
        have hSrc' : FormulaN.conj C' D' = FormulaN.conj B C := by
          have := hSrc
          unfold CInstance.source at this
          simpa using this
        have hCB : C' = B := (FormulaN.conj.injEq C' D' B C).mp hSrc' |>.1
        have hDC : D' = C := (FormulaN.conj.injEq C' D' B C).mp hSrc' |>.2
        -- hWF : H.source = C' ∧ K'.source = D' ∧ H.WellFormed ∧ K'.WellFormed
        have hWF' : CInstance.source H = C' ∧ CInstance.source K' = D' ∧
            CInstance.WellFormed H ∧ CInstance.WellFormed K' := hWF
        obtain ⟨hHsrc, hKsrc, hHwf, hKwf⟩ := hWF'
        refine ⟨H, K', ?_, ?_, hHwf, hKwf, ?_⟩
        · rw [hHsrc, hCB]
        · rw [hKsrc, hDC]
        · show K = FormulaN.conj H.toFormula K'.toFormula
          have hForm' : FormulaN.conj H.toFormula K'.toFormula = K := by
            have := hForm
            unfold CInstance.toFormula at this
            simpa using this
          exact hForm'.symm
      | false =>
        -- ci.source = disj C' D', hSrc : disj C' D' = conj B C, contradiction
        have hSrc' : FormulaN.disj C' D' = FormulaN.conj B C := by
          have := hSrc
          unfold CInstance.source at this
          simpa using this
        exact absurd hSrc' (by intro h; cases h)
    | false =>
      cases cStar with
      | true =>
        -- ci.source = conj C' D', hSrc : conj C' D' = disj B C, contradiction
        have hSrc' : FormulaN.conj C' D' = FormulaN.disj B C := by
          have := hSrc
          unfold CInstance.source at this
          simpa using this
        exact absurd hSrc' (by intro h; cases h)
      | false =>
        -- hSrc : disj C' D' = disj B C
        have hSrc' : FormulaN.disj C' D' = FormulaN.disj B C := by
          have := hSrc
          unfold CInstance.source at this
          simpa using this
        have hCB : C' = B := (FormulaN.disj.injEq C' D' B C).mp hSrc' |>.1
        have hDC : D' = C := (FormulaN.disj.injEq C' D' B C).mp hSrc' |>.2
        have hWF' : CInstance.source H = C' ∧ CInstance.source K' = D' ∧
            CInstance.WellFormed H ∧ CInstance.WellFormed K' := hWF
        obtain ⟨hHsrc, hKsrc, hHwf, hKwf⟩ := hWF'
        refine ⟨H, K', ?_, ?_, hHwf, hKwf, ?_⟩
        · rw [hHsrc, hCB]
        · rw [hKsrc, hDC]
        · show K = FormulaN.disj H.toFormula K'.toFormula
          have hForm' : FormulaN.disj H.toFormula K'.toFormula = K := by
            have := hForm
            unfold CInstance.toFormula at this
            simpa using this
          exact hForm'.symm
  | forallInst x C' t₀ h₀ tsRest hsRest _ _ =>
    -- ci.source = all x C', so hSrc : all x C' = conj/disj B C. Contradiction.
    cases star with
    | true =>
      have hSrc' : FormulaN.all x C' = FormulaN.conj B C := by
        have := hSrc
        unfold CInstance.source at this
        exact this
      exact absurd hSrc' (by intro h; cases h)
    | false =>
      have hSrc' : FormulaN.all x C' = FormulaN.disj B C := by
        have := hSrc
        unfold CInstance.source at this
        exact this
      exact absurd hSrc' (by intro h; cases h)

-- ===================================================================
-- Helper: G2nnf identity tree for quantifier-free NNF formulas
-- ===================================================================

/-- Helper: In an equality-free language, for any quantifier-free NNF
formula A, the sequent
A -> A is derivable in G2nnf. Proof by structural induction on the
quantifier-free formula: atomic uses axiomPosId, negated atomic uses
axiomNegId, conjunction uses conjRight with conjLeft1/conjLeft2,
disjunction uses disjLeft with disjRight1/disjRight2. -/
theorem g2nnf_identity_qf {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (A : FormulaN L)
    (hNNF : FormulaN.isNNF A)
    (hQF : LCS.FirstOrder.SemanticsN.isQuantifierFree A) :
    Nonempty (G2nnfProofTree hL
      ({A} : LCS.Finset (FormulaN L))
      ({A} : LCS.Finset (FormulaN L))) := by
  have hn : ∀ {B C : FormulaN L}, B.isNNF → C.isNNF →
      AllNNF (({B} : LCS.Finset (FormulaN L)), {C}) := by
    intro B C hB hC
    constructor <;> intro F h
    · have he := (LCS.Finset.mem_singleton F B).mp h
      subst F; exact hB
    · have he := (LCS.Finset.mem_singleton F C).mp h
      subst F; exact hC
  induction A with
  | predN P args =>
      have hRect : isRectified (.predN P args) :=
        AllRectified.isRectified_of_isQuantifierFree _ trivial
      exact ⟨G2nnfDeductionTreeCore.axiom_
        (G2nnfRuleCore.axiomPosId (.predN P args) rfl
          LCS.Finset.empty LCS.Finset.empty)
        ⟨rfl, rfl⟩ rfl
        ⟨trivial, hn hNNF hNNF,
          (by intro seq h; cases h),
          allRectified_singletons hRect hRect⟩⟩
  | eq_ hEq lhs rhs =>
      have hRect : isRectified (.eq_ hEq lhs rhs) :=
        AllRectified.isRectified_of_isQuantifierFree _ trivial
      exact ⟨G2nnfDeductionTreeCore.axiom_
        (G2nnfRuleCore.axiomPosId (.eq_ hEq lhs rhs) rfl
          LCS.Finset.empty LCS.Finset.empty)
        ⟨rfl, rfl⟩ rfl
        ⟨trivial, hn hNNF hNNF,
          (by intro seq h; cases h),
          allRectified_singletons hRect hRect⟩⟩
  | neg B =>
      cases B with
      | predN P args =>
          have hRect : isRectified (.neg (.predN P args)) :=
            AllRectified.isRectified_of_isQuantifierFree _ trivial
          exact ⟨G2nnfDeductionTreeCore.axiom_
            (G2nnfRuleCore.axiomNegId (.predN P args) rfl
              LCS.Finset.empty LCS.Finset.empty)
            ⟨rfl, rfl⟩ rfl
            ⟨trivial, hn hNNF hNNF,
              (by intro seq h; cases h),
              allRectified_singletons hRect hRect⟩⟩
      | eq_ hEq lhs rhs =>
          have hRect : isRectified (.neg (.eq_ hEq lhs rhs)) :=
            AllRectified.isRectified_of_isQuantifierFree _ trivial
          exact ⟨G2nnfDeductionTreeCore.axiom_
            (G2nnfRuleCore.axiomNegId (.eq_ hEq lhs rhs) rfl
              LCS.Finset.empty LCS.Finset.empty)
            ⟨rfl, rfl⟩ rfl
            ⟨trivial, hn hNNF hNNF,
              (by intro seq h; cases h),
              allRectified_singletons hRect hRect⟩⟩
      | neg _ | conj _ _ | disj _ _ | impl _ _ | all _ _ | ex _ _ =>
          exact hNNF.elim
  | conj B C ihB ihC =>
      obtain ⟨tB⟩ := ihB hNNF.1 hQF.1
      obtain ⟨tC⟩ := ihC hNNF.2 hQF.2
      have hBRect : isRectified B :=
        AllRectified.isRectified_of_isQuantifierFree B hQF.1
      have hCRect : isRectified C :=
        AllRectified.isRectified_of_isQuantifierFree C hQF.2
      have hConjRect : isRectified (.conj B C) :=
        AllRectified.isRectified_of_isQuantifierFree (.conj B C) hQF
      have left :
          G2nnfProofTree hL
            ({FormulaN.conj B C} : LCS.Finset (FormulaN L))
            ({B} : LCS.Finset (FormulaN L)) :=
        G2nnfDeductionTreeCore.onePremise
          (G2nnfRuleCore.conjLeft1 B C
            LCS.Finset.empty
          ({B} : LCS.Finset (FormulaN L))) trivial
          rfl
          ⟨trivial, hn hNNF hNNF.1,
          (by
            intro seq h
            simp only [G2nnfRuleCore.premises, List.mem_cons,
              List.not_mem_nil, or_false] at h
            subst seq
            exact G2nnfDeductionTreeCore.allNNF tB),
          allRectified_singletons hConjRect hBRect⟩
          tB
      have right :
          G2nnfProofTree hL
            ({FormulaN.conj B C} : LCS.Finset (FormulaN L))
            ({C} : LCS.Finset (FormulaN L)) :=
        G2nnfDeductionTreeCore.onePremise
          (G2nnfRuleCore.conjLeft2 B C
            LCS.Finset.empty
          ({C} : LCS.Finset (FormulaN L))) trivial
          rfl
          ⟨trivial, hn hNNF hNNF.2,
          (by
            intro seq h
            simp only [G2nnfRuleCore.premises, List.mem_cons,
              List.not_mem_nil, or_false] at h
            subst seq
            exact G2nnfDeductionTreeCore.allNNF tC),
          allRectified_singletons hConjRect hCRect⟩
          tC
      exact ⟨G2nnfDeductionTreeCore.twoPremise
        (G2nnfRuleCore.conjRight B C
          ({FormulaN.conj B C} : LCS.Finset (FormulaN L))
        LCS.Finset.empty) trivial rfl
        ⟨trivial, hn hNNF hNNF,
          (by
            intro seq h
            simp only [G2nnfRuleCore.premises, List.mem_cons,
              List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl
            · exact G2nnfDeductionTreeCore.allNNF left
            · exact G2nnfDeductionTreeCore.allNNF right),
          allRectified_singletons hConjRect hConjRect⟩
        left right⟩
  | disj B C ihB ihC =>
      obtain ⟨tB⟩ := ihB hNNF.1 hQF.1
      obtain ⟨tC⟩ := ihC hNNF.2 hQF.2
      have hBRect : isRectified B :=
        AllRectified.isRectified_of_isQuantifierFree B hQF.1
      have hCRect : isRectified C :=
        AllRectified.isRectified_of_isQuantifierFree C hQF.2
      have hDisjRect : isRectified (.disj B C) :=
        AllRectified.isRectified_of_isQuantifierFree (.disj B C) hQF
      have left :
          G2nnfProofTree hL
            ({B} : LCS.Finset (FormulaN L))
            ({FormulaN.disj B C} : LCS.Finset (FormulaN L)) :=
        G2nnfDeductionTreeCore.onePremise
          (G2nnfRuleCore.disjRight1 B C
            ({B} : LCS.Finset (FormulaN L))
          LCS.Finset.empty) trivial
          rfl
          ⟨trivial, hn hNNF.1 hNNF,
          (by
            intro seq h
            simp only [G2nnfRuleCore.premises, List.mem_cons,
              List.not_mem_nil, or_false] at h
            subst seq
            exact G2nnfDeductionTreeCore.allNNF tB),
          allRectified_singletons hBRect hDisjRect⟩
          tB
      have right :
          G2nnfProofTree hL
            ({C} : LCS.Finset (FormulaN L))
            ({FormulaN.disj B C} : LCS.Finset (FormulaN L)) :=
        G2nnfDeductionTreeCore.onePremise
          (G2nnfRuleCore.disjRight2 B C
            ({C} : LCS.Finset (FormulaN L))
          LCS.Finset.empty) trivial
          rfl
          ⟨trivial, hn hNNF.2 hNNF,
          (by
            intro seq h
            simp only [G2nnfRuleCore.premises, List.mem_cons,
              List.not_mem_nil, or_false] at h
            subst seq
            exact G2nnfDeductionTreeCore.allNNF tC),
          allRectified_singletons hCRect hDisjRect⟩
          tC
      exact ⟨G2nnfDeductionTreeCore.twoPremise
        (G2nnfRuleCore.disjLeft B C
          LCS.Finset.empty
        ({FormulaN.disj B C} : LCS.Finset (FormulaN L))) trivial
        rfl
        ⟨trivial, hn hNNF hNNF,
          (by
            intro seq h
            simp only [G2nnfRuleCore.premises, List.mem_cons,
              List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl
            · exact G2nnfDeductionTreeCore.allNNF left
            · exact G2nnfDeductionTreeCore.allNNF right),
          allRectified_singletons hDisjRect hDisjRect⟩
        left right⟩
  | impl _ _ _ _ =>
      exact hNNF.elim
  | all _ _ _ =>
      exact hQF.elim
  | ex _ _ _ =>
      exact hQF.elim

theorem nnf_right_conj_local {L : Language}
    (fs : List (FormulaN L)) (init : FormulaN L)
    (hInit : FormulaN.isNNF init)
    (hFs : ∀ f, f ∈ fs → FormulaN.isNNF f) :
    FormulaN.isNNF
      (fs.foldr (fun f rest first => FormulaN.conj first (rest f)) id init) := by
  induction fs generalizing init with
  | nil => exact hInit
  | cons f rest ih =>
      exact ⟨hInit, ih f (hFs f (by simp))
        (fun g hg => hFs g (by simp; right; exact hg))⟩

/-- Compound-instance formulae remain in NNF.  This structural fact is
used only to build identity proofs for the quantifier-free formulae
stored in `CInstance` witnesses. -/
theorem cInstance_toFormula_isNNF {L : Language}
    (ci : CInstance L) : FormulaN.isNNF ci.toFormula := by
  match ci with
  | .atom B hAtom =>
    simp only [CInstance.toFormula]
    cases B <;> simp_all [FormulaN.isAtomic, FormulaN.isNNF]
  | .negAtom B hAtom =>
    simp only [CInstance.toFormula]
    cases B <;> simp_all [FormulaN.isAtomic, FormulaN.isNNF]
  | .connective true C D H K =>
    simp only [CInstance.toFormula, FormulaN.isNNF]
    exact ⟨cInstance_toFormula_isNNF H, cInstance_toFormula_isNNF K⟩
  | .connective false C D H K =>
    simp only [CInstance.toFormula, FormulaN.isNNF]
    exact ⟨cInstance_toFormula_isNNF H, cInstance_toFormula_isNNF K⟩
  | .forallInst x C t₀ h₀ tsRest hsRest _ _ =>
    simp only [CInstance.toFormula]
    apply nnf_right_conj_local
    · exact cInstance_toFormula_isNNF h₀
    · intro f hf
      rw [List.mem_map] at hf
      obtain ⟨h, hMem, heq⟩ := hf
      rw [← heq]
      exact cInstance_toFormula_isNNF h
termination_by sizeOf ci
decreasing_by
  all_goals first
    | (simp_wf; omega)
    | (simp_wf
       have := List.sizeOf_lt_of_mem hMem
       omega)

abbrev G2FormulaFinset {L : Language}
    [DecidableEq (FormulaN L)] :=
  LCS.Finset (FormulaN L)

private theorem g2nnf_insert_singleton_comm {α : Type}
    [DecidableEq α] (a b : α) :
    LCS.Finset.insert a ({b} : LCS.Finset α) =
      LCS.Finset.insert b ({a} : LCS.Finset α) := by
  apply LCS.Finset.ext
  intro x
  change x ∈ LCS.Finset.insert a (LCS.Finset.singleton b) ↔
    x ∈ LCS.Finset.insert b (LCS.Finset.singleton a)
  rw [LCS.Finset.mem_insert, LCS.Finset.mem_insert,
      LCS.Finset.mem_singleton, LCS.Finset.mem_singleton]
  exact or_comm

/-- Weakening explicitly preserves the NNF and rectification domains. -/
def g2nnfWeakLeft {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γ Δ : G2FormulaFinset} (A : FormulaN L)
    (hNNF : A.isNNF) (hA : isRectified A)
    (t : G2nnfProofTree hL Γ Δ) :
    G2nnfProofTree hL (LCS.Finset.insert A Γ) Δ := by
  have hn := G2nnfDeductionTreeCore.allNNF t
  exact .onePremise (.weakLeft A Γ Δ) trivial rfl
    ⟨trivial,
      ⟨(by intro F h; rcases LCS.Finset.mem_insert.mp h with rfl | h
           exact hNNF
           exact hn.1 F h), hn.2⟩,
      (by intro seq h
          simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
          subst seq; exact hn),
      AllRectified.insert_left hA t.allRectified⟩ t

/-- Right weakening retains explicit NNF evidence for the added formula. -/
private def g2nnfWeakRight {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γ Δ : G2FormulaFinset} (A : FormulaN L)
    (hNNF : A.isNNF) (hA : isRectified A)
    (t : G2nnfProofTree hL Γ Δ) :
    G2nnfProofTree hL Γ (LCS.Finset.insert A Δ) := by
  have hn := G2nnfDeductionTreeCore.allNNF t
  exact .onePremise (.weakRight A Γ Δ) trivial rfl
    ⟨trivial,
      ⟨hn.1, (by intro F h; rcases LCS.Finset.mem_insert.mp h with rfl | h
                 exact hNNF
                 exact hn.2 F h)⟩,
      (by intro seq h
          simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
          subst seq; exact hn),
      AllRectified.insert_right hA t.allRectified⟩ t

/-- Cut retains independent premise contexts and their union at the root. -/
def g2nnfCut {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γ Δ Λ Θ : G2FormulaFinset} (A : FormulaN L)
    (left : G2nnfProofTree hL Γ (LCS.Finset.insert A Δ))
    (right : G2nnfProofTree hL (LCS.Finset.insert A Λ) Θ) :
    G2nnfProofTree hL (LCS.Finset.union Γ Λ) (LCS.Finset.union Δ Θ) := by
  have hl := G2nnfDeductionTreeCore.allNNF left
  have hr := G2nnfDeductionTreeCore.allNNF right
  exact .twoPremise (.cut A Λ Θ Γ Δ) trivial rfl
    ⟨trivial,
      ⟨(by intro F h; rcases LCS.Finset.mem_union.mp h with h | h
           exact hl.1 F h
           exact hr.1 F (LCS.Finset.mem_insert.mpr (Or.inr h))),
       (by intro F h; rcases LCS.Finset.mem_union.mp h with h | h
           exact hl.2 F (LCS.Finset.mem_insert.mpr (Or.inr h))
           exact hr.2 F h)⟩,
      (by intro seq h
          simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl
          exact hl
          exact hr),
      AllRectified.union (AllRectified.of_insert_right left.allRectified)
        (AllRectified.of_insert_left right.allRectified)⟩ left right

/-- Compose singleton derivations by cut with empty unused contexts. -/
def g2nnfCompose {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (A B C : FormulaN L)
    (p : G2nnfProofTree hL
      ({A} : G2FormulaFinset) ({B} : G2FormulaFinset))
    (q : G2nnfProofTree hL
      ({B} : G2FormulaFinset) ({C} : G2FormulaFinset)) :
    G2nnfProofTree hL
      ({A} : G2FormulaFinset) ({C} : G2FormulaFinset) := by
  have t := g2nnfCut (hL := hL) (Γ := {A}) (Δ := ∅) (Λ := ∅) (Θ := {C}) B p q
  have hLeft : LCS.Finset.union ({A} : G2FormulaFinset) ∅ = {A} := by
    apply LCS.Finset.ext
    intro F
    simp [LCS.Finset.mem_union, LCS.Finset.mem_empty]
  have hRight : LCS.Finset.union (∅ : G2FormulaFinset) {C} = {C} := by
    apply LCS.Finset.ext
    intro F
    simp [LCS.Finset.mem_union, LCS.Finset.mem_empty]
  rw [hLeft, hRight] at t
  exact t

/-- NNF evidence for singleton premise and conclusion formulae. -/
theorem allNNF_singletons {L : Language}
    [DecidableEq (FormulaN L)] {A B : FormulaN L}
    (hA : A.isNNF) (hB : B.isNNF) : AllNNF (({A} : LCS.Finset (FormulaN L)), {B}) := by
  constructor <;> intro F h
  · have he := (LCS.Finset.mem_singleton F A).mp h
    subst F; exact hA
  · have he := (LCS.Finset.mem_singleton F B).mp h
    subst F; exact hB

def g2nnfConjProjLeft {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (A B : FormulaN L)
    (hConjNNF : FormulaN.isNNF (.conj A B)) (hConj : isRectified (.conj A B))
    (idA : G2nnfProofTree hNoEq
      ({A} : G2FormulaFinset) ({A} : G2FormulaFinset)) :
    G2nnfProofTree hNoEq
      ({FormulaN.conj A B} : G2FormulaFinset)
      ({A} : G2FormulaFinset) :=
  .onePremise (.conjLeft1 A B ∅ ({A} : G2FormulaFinset)) trivial rfl
    ⟨trivial, allNNF_singletons hConjNNF hConjNNF.1,
      (by intro seq h
          simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
          subst seq; exact G2nnfDeductionTreeCore.allNNF idA),
      AllRectified.insert_left hConj
        (AllRectified.of_insert_left idA.allRectified)⟩ idA

def g2nnfConjProjRight {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (A B : FormulaN L)
    (hConjNNF : FormulaN.isNNF (.conj A B)) (hConj : isRectified (.conj A B))
    (idB : G2nnfProofTree hNoEq
      ({B} : G2FormulaFinset) ({B} : G2FormulaFinset)) :
    G2nnfProofTree hNoEq
      ({FormulaN.conj A B} : G2FormulaFinset)
      ({B} : G2FormulaFinset) :=
  .onePremise (.conjLeft2 A B ∅ ({B} : G2FormulaFinset)) trivial rfl
    ⟨trivial, allNNF_singletons hConjNNF hConjNNF.2,
      (by intro seq h
          simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
          subst seq; exact G2nnfDeductionTreeCore.allNNF idB),
      AllRectified.insert_left hConj
        (AllRectified.of_insert_left idB.allRectified)⟩ idB

def g2nnfCombineConj {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (X Y A B C D : FormulaN L)
    (hXQF : isQuantifierFree X) (hYQF : isQuantifierFree Y)
    (hAQF : isQuantifierFree A) (hBQF : isQuantifierFree B)
    (hCQF : isQuantifierFree C) (hDQF : isQuantifierFree D)
    (p : G2nnfProofTree hNoEq
      ({X} : G2FormulaFinset)
      ({FormulaN.conj A B} : G2FormulaFinset))
    (q : G2nnfProofTree hNoEq
      ({Y} : G2FormulaFinset)
      ({FormulaN.conj C D} : G2FormulaFinset))
    (idA : G2nnfProofTree hNoEq
      ({A} : G2FormulaFinset) ({A} : G2FormulaFinset))
    (idB : G2nnfProofTree hNoEq
      ({B} : G2FormulaFinset) ({B} : G2FormulaFinset))
    (idC : G2nnfProofTree hNoEq
      ({C} : G2FormulaFinset) ({C} : G2FormulaFinset))
    (idD : G2nnfProofTree hNoEq
      ({D} : G2FormulaFinset) ({D} : G2FormulaFinset)) :
    G2nnfProofTree hNoEq
      ({FormulaN.conj X Y} : G2FormulaFinset)
      ({FormulaN.conj (FormulaN.conj A C) (FormulaN.conj B D)} :
        G2FormulaFinset) := by
  have hXNNF : FormulaN.isNNF X :=
    (G2nnfDeductionTreeCore.allNNF p).1 X
      ((LCS.Finset.mem_singleton X X).mpr rfl)
  have hYNNF : FormulaN.isNNF Y :=
    (G2nnfDeductionTreeCore.allNNF q).1 Y
      ((LCS.Finset.mem_singleton Y Y).mpr rfl)
  have hANNF : FormulaN.isNNF A :=
    (G2nnfDeductionTreeCore.allNNF idA).1 A
      ((LCS.Finset.mem_singleton A A).mpr rfl)
  have hBNNF : FormulaN.isNNF B :=
    (G2nnfDeductionTreeCore.allNNF idB).1 B
      ((LCS.Finset.mem_singleton B B).mpr rfl)
  have hCNNF : FormulaN.isNNF C :=
    (G2nnfDeductionTreeCore.allNNF idC).1 C
      ((LCS.Finset.mem_singleton C C).mpr rfl)
  have hDNNF : FormulaN.isNNF D :=
    (G2nnfDeductionTreeCore.allNNF idD).1 D
      ((LCS.Finset.mem_singleton D D).mpr rfl)
  have hARect : isRectified A :=
    AllRectified.isRectified_of_isQuantifierFree A hAQF
  have hBRect : isRectified B :=
    AllRectified.isRectified_of_isQuantifierFree B hBQF
  have hCRect : isRectified C :=
    AllRectified.isRectified_of_isQuantifierFree C hCQF
  have hDRect : isRectified D :=
    AllRectified.isRectified_of_isQuantifierFree D hDQF
  have hXYRect : isRectified (.conj X Y) :=
    AllRectified.isRectified_of_isQuantifierFree (.conj X Y)
      ⟨hXQF, hYQF⟩
  have hABRect : isRectified (.conj A B) :=
    AllRectified.isRectified_of_isQuantifierFree (.conj A B)
      ⟨hAQF, hBQF⟩
  have hCDRect : isRectified (.conj C D) :=
    AllRectified.isRectified_of_isQuantifierFree (.conj C D)
      ⟨hCQF, hDQF⟩
  have hACRect : isRectified (.conj A C) :=
    AllRectified.isRectified_of_isQuantifierFree (.conj A C)
      ⟨hAQF, hCQF⟩
  have hBDRect : isRectified (.conj B D) :=
    AllRectified.isRectified_of_isQuantifierFree (.conj B D)
      ⟨hBQF, hDQF⟩
  have hTargetRect :
      isRectified (.conj (.conj A C) (.conj B D)) :=
    AllRectified.isRectified_of_isQuantifierFree
      (.conj (.conj A C) (.conj B D))
      ⟨⟨hAQF, hCQF⟩, ⟨hBQF, hDQF⟩⟩
  have pA :
      G2nnfProofTree hNoEq
        ({X} : G2FormulaFinset) ({A} : G2FormulaFinset) :=
    g2nnfCompose (hL := hNoEq) X (.conj A B) A p
      (g2nnfConjProjLeft (hNoEq := hNoEq) A B ⟨hANNF, hBNNF⟩ hABRect idA)
  have pB :
      G2nnfProofTree hNoEq
        ({X} : G2FormulaFinset) ({B} : G2FormulaFinset) :=
    g2nnfCompose (hL := hNoEq) X (.conj A B) B p
      (g2nnfConjProjRight (hNoEq := hNoEq) A B ⟨hANNF, hBNNF⟩ hABRect idB)
  have qC :
      G2nnfProofTree hNoEq
        ({Y} : G2FormulaFinset) ({C} : G2FormulaFinset) :=
    g2nnfCompose (hL := hNoEq) Y (.conj C D) C q
      (g2nnfConjProjLeft (hNoEq := hNoEq) C D ⟨hCNNF, hDNNF⟩ hCDRect idC)
  have qD :
      G2nnfProofTree hNoEq
        ({Y} : G2FormulaFinset) ({D} : G2FormulaFinset) :=
    g2nnfCompose (hL := hNoEq) Y (.conj C D) D q
      (g2nnfConjProjRight (hNoEq := hNoEq) C D ⟨hCNNF, hDNNF⟩ hCDRect idD)
  have leftA :
      G2nnfProofTree hNoEq
        ({FormulaN.conj X Y} : G2FormulaFinset)
        ({A} : G2FormulaFinset) :=
    .onePremise (.conjLeft1 X Y ∅ ({A} : G2FormulaFinset)) trivial rfl
      ⟨trivial, allNNF_singletons ⟨hXNNF, hYNNF⟩ hANNF,
      (by intro seq h
          simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
          subst seq; exact G2nnfDeductionTreeCore.allNNF pA),
      allRectified_singletons hXYRect hARect⟩
    pA
  have leftC :
      G2nnfProofTree hNoEq
        ({FormulaN.conj X Y} : G2FormulaFinset)
        ({C} : G2FormulaFinset) :=
    .onePremise (.conjLeft2 X Y ∅ ({C} : G2FormulaFinset)) trivial rfl
      ⟨trivial, allNNF_singletons ⟨hXNNF, hYNNF⟩ hCNNF,
      (by intro seq h
          simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
          subst seq; exact G2nnfDeductionTreeCore.allNNF qC),
      allRectified_singletons hXYRect hCRect⟩
    qC
  have left :
      G2nnfProofTree hNoEq
        ({FormulaN.conj X Y} : G2FormulaFinset)
        ({FormulaN.conj A C} : G2FormulaFinset) :=
    .twoPremise (.conjRight A C ({FormulaN.conj X Y} : G2FormulaFinset) ∅) trivial
      rfl
      ⟨trivial, allNNF_singletons ⟨hXNNF, hYNNF⟩ ⟨hANNF, hCNNF⟩,
      (by intro seq h
          simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl
          exact G2nnfDeductionTreeCore.allNNF leftA
          exact G2nnfDeductionTreeCore.allNNF leftC),
      allRectified_singletons hXYRect hACRect⟩
    leftA leftC
  have rightB :
      G2nnfProofTree hNoEq
        ({FormulaN.conj X Y} : G2FormulaFinset)
        ({B} : G2FormulaFinset) :=
    .onePremise (.conjLeft1 X Y ∅ ({B} : G2FormulaFinset)) trivial rfl
      ⟨trivial, allNNF_singletons ⟨hXNNF, hYNNF⟩ hBNNF,
      (by intro seq h
          simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
          subst seq; exact G2nnfDeductionTreeCore.allNNF pB),
      allRectified_singletons hXYRect hBRect⟩
    pB
  have rightD :
      G2nnfProofTree hNoEq
        ({FormulaN.conj X Y} : G2FormulaFinset)
        ({D} : G2FormulaFinset) :=
    .onePremise (.conjLeft2 X Y ∅ ({D} : G2FormulaFinset)) trivial rfl
      ⟨trivial, allNNF_singletons ⟨hXNNF, hYNNF⟩ hDNNF,
      (by intro seq h
          simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
          subst seq; exact G2nnfDeductionTreeCore.allNNF qD),
      allRectified_singletons hXYRect hDRect⟩
    qD
  have right :
      G2nnfProofTree hNoEq
        ({FormulaN.conj X Y} : G2FormulaFinset)
        ({FormulaN.conj B D} : G2FormulaFinset) :=
    .twoPremise (.conjRight B D ({FormulaN.conj X Y} : G2FormulaFinset) ∅) trivial
      rfl
      ⟨trivial, allNNF_singletons ⟨hXNNF, hYNNF⟩ ⟨hBNNF, hDNNF⟩,
      (by intro seq h
          simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl
          exact G2nnfDeductionTreeCore.allNNF rightB
          exact G2nnfDeductionTreeCore.allNNF rightD),
      allRectified_singletons hXYRect hBDRect⟩
    rightB rightD
  exact .twoPremise (.conjRight (.conj A C) (.conj B D) ({FormulaN.conj X Y} : G2FormulaFinset) ∅) trivial
    rfl
    ⟨trivial, allNNF_singletons ⟨hXNNF, hYNNF⟩ ⟨⟨hANNF, hCNNF⟩, ⟨hBNNF, hDNNF⟩⟩,
      (by intro seq h
          simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl
          exact G2nnfDeductionTreeCore.allNNF left
          exact G2nnfDeductionTreeCore.allNNF right),
      allRectified_singletons hXYRect hTargetRect⟩
    left right

end LCS.Herbrand.SHGTheorem.Herbrand
end

