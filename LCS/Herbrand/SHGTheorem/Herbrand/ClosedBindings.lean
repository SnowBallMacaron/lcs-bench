import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.CanonicalEigenvarMap
import LCS.Herbrand.SHGTheorem.Herbrand.FormulaProvenance

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

private def ClosedFormulaProvenance.exSubLeftRelevant
    {L : Language} {spec : SkolemSpec L}
    {seed : ClosedTerm spec.language}
    {A B : FormulaN L}
    (prior : ClosedFormulaProvenance spec seed A)
    (occurrence : MaxQuantifierOccurrence A)
    (x y : Nat)
    (hSelected :
      occurrence.selected = FormulaN.ex x B)
    (hRelevant : x ∈ formulaFVN B)
    (index : Fin spec.n)
    (hScopeCovered :
      prior.universalMap.Covers (spec.skolemScope index))
    (closedRange : ClosedTerm spec.language)
    (hRange :
      closedRange.1 =
        closeSkolemTermWithSeed seed prior.universalMap
          (exactSkolemTerm spec index)) :
    ClosedFormulaProvenance spec seed
      (occurrence.replace
        (formulaSubstN B (.var y) x)) :=
  ⟨prior.events ++
      [.exSubLeftRelevant A B occurrence x y hSelected
        hRelevant index prior.universalMap hScopeCovered
        closedRange hRange],
    prior.universalMap,
    .exSubLeftRelevant prior.replay occurrence x y hSelected
      hRelevant index hScopeCovered closedRange hRange,
    (closedFormulaExSubLeft_invariants
      occurrence x (.var y) hSelected prior.universalMap
      prior.scopeAligned prior.frontierReady).1,
    (closedFormulaExSubLeft_invariants
      occurrence x (.var y) hSelected prior.universalMap
      prior.scopeAligned prior.frontierReady).2⟩

private def ClosedFormulaProvenance.exSubLeftVacuous
    {L : Language} {spec : SkolemSpec L}
    {seed : ClosedTerm spec.language}
    {A B : FormulaN L}
    (prior : ClosedFormulaProvenance spec seed A)
    (occurrence : MaxQuantifierOccurrence A)
    (x y : Nat)
    (hSelected :
      occurrence.selected = FormulaN.ex x B)
    (hVacuous : x ∉ formulaFVN B) :
    ClosedFormulaProvenance spec seed
      (occurrence.replace
        (formulaSubstN B (.var y) x)) :=
  ⟨prior.events ++
      [.exSubLeftVacuous A B occurrence x y hSelected
        hVacuous],
    prior.universalMap,
    .exSubLeftVacuous prior.replay occurrence x y hSelected
      hVacuous,
    (closedFormulaExSubLeft_invariants
      occurrence x (.var y) hSelected prior.universalMap
      prior.scopeAligned prior.frontierReady).1,
    (closedFormulaExSubLeft_invariants
      occurrence x (.var y) hSelected prior.universalMap
      prior.scopeAligned prior.frontierReady).2⟩

/-- Close one exact Skolem allocation from the universal choices stored in
the supplied provenance.  The explicit coverage argument proves that every
free variable of the exact allocation is mapped; the seed branch of the
underlying normalizer is therefore unreachable on that allocation. -/
private def ClosedFormulaProvenance.closedAllocation
    {L : Language} {spec : SkolemSpec L}
    {seed : ClosedTerm spec.language} {A : FormulaN L}
    (provenance : ClosedFormulaProvenance spec seed A)
    (i : Fin spec.n)
    (_hScopeCovered :
      provenance.universalMap.Covers (spec.skolemScope i)) :
    ClosedTerm spec.language :=
  ⟨closeSkolemTermWithSeed seed provenance.universalMap
      (exactSkolemTerm spec i),
    closeSkolemTermWithSeed_isClosed seed provenance.universalMap
      (exactSkolemTerm spec i)⟩

/-- Existential package for a current formula and its Type-valued source
provenance.  Keeping a list of these cells preserves both principal and
retained-context alternatives when `Finset.insert` collapses equal formula
values. -/
structure ClosedFormulaProvenanceCell
    {L : Language} (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language) where
  formula : FormulaN L
  provenance : ClosedFormulaProvenance spec seed formula

/-- Select every provenance cell equal to the requested principal formula
using the supplied decidable equality, preserving list order and all matching
histories. Equality transports each cell's indexed provenance to the target. -/
def matchingClosedFormulaProvenances
    {L : Language} [DecidableEq (FormulaN L)] (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language) (A : FormulaN L) :
    List (ClosedFormulaProvenanceCell spec seed) →
      List (ClosedFormulaProvenance spec seed A)
  | [] => []
  | cell :: rest =>
      if h : cell.formula = A then
        (h ▸ cell.provenance) ::
          matchingClosedFormulaProvenances spec seed A rest
      else
        matchingClosedFormulaProvenances spec seed A rest

/-- Retain precisely the explicit context cells.  A cell equal to the
principal is retained when it also belongs to the raw context, so the
principal and context branches remain intentionally nonexclusive. -/
private def retainClosedFormulaContext
    {L : Language} [DecidableEq (FormulaN L)]
    {spec : SkolemSpec L}
    (seed : ClosedTerm spec.language)
    (Gamma : LCS.Finset (FormulaN L)) :
    List (ClosedFormulaProvenanceCell spec seed) →
      List (ClosedFormulaProvenanceCell spec seed)
  | [] => []
  | cell :: rest =>
      if cell.formula ∈ Gamma then
        cell :: retainClosedFormulaContext seed Gamma rest
      else
        retainClosedFormulaContext seed Gamma rest

/-- Principal/context update at a universal-left rule.  Each principal
history freezes its choice with the current pathPrefix map before any later
existential allocation is inserted. -/
def closedFormulaProvenanceAllSubLeft
    {L : Language} [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    (prefixMap : ClosedEigenvarMap spec.language)
    (A B : FormulaN L)
    (occurrence : MaxQuantifierOccurrence A)
    (x : Nat) (t : Term L)
    (hSelected :
      occurrence.selected = FormulaN.all x B)
    (Gamma : LCS.Finset (FormulaN L))
    (cells : List (ClosedFormulaProvenanceCell spec seed)) :
    List (ClosedFormulaProvenanceCell spec seed) :=
  let choice : ClosedTerm spec.language :=
    ⟨closeSkolemTermWithSeed seed prefixMap
        (liftEigenvarBaseTerm spec t),
      closeSkolemTermWithSeed_isClosed seed prefixMap
        (liftEigenvarBaseTerm spec t)⟩
  (matchingClosedFormulaProvenances spec seed A cells).map
      (fun prior =>
        { formula :=
            occurrence.replace (formulaSubstN B t x)
          provenance :=
            .allSubLeft prior occurrence x t hSelected
              prefixMap choice rfl }) ++
    retainClosedFormulaContext seed Gamma cells

/-- Principal/context update at a relevant existential-left rule.  Exactly
the selected principal lineage is transformed.  Other matching principal
histories are not carried into the successor as principal alternatives;
raw-context cells are retained separately. -/
def closedFormulaProvenanceExSubLeftRelevant
    {L : Language} [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    (A B : FormulaN L)
    (occurrence : MaxQuantifierOccurrence A)
    (x y : Nat)
    (hSelected :
      occurrence.selected = FormulaN.ex x B)
    (hRelevant : x ∈ formulaFVN B)
    (i : Fin spec.n)
    (prior : ClosedFormulaProvenance spec seed A)
    (hScopeCovered :
      prior.universalMap.Covers (spec.skolemScope i))
    (Gamma : LCS.Finset (FormulaN L))
    (cells : List (ClosedFormulaProvenanceCell spec seed)) :
    List (ClosedFormulaProvenanceCell spec seed) :=
  let closedRange := prior.closedAllocation i hScopeCovered
  [{ formula :=
       occurrence.replace
         (formulaSubstN B (.var y) x)
     provenance :=
       .exSubLeftRelevant prior occurrence x y hSelected
         hRelevant i hScopeCovered closedRange rfl }] ++
    retainClosedFormulaContext seed Gamma cells

/-- A vacuous existential-left step changes the formula provenance but does
not manufacture either an allocation range or an eigenvariable-map cell. -/
def closedFormulaProvenanceExSubLeftVacuous
    {L : Language} [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    (A B : FormulaN L)
    (occurrence : MaxQuantifierOccurrence A)
    (x y : Nat)
    (hSelected :
      occurrence.selected = FormulaN.ex x B)
    (hVacuous : x ∉ formulaFVN B)
    (Gamma : LCS.Finset (FormulaN L))
    (cells : List (ClosedFormulaProvenanceCell spec seed)) :
    List (ClosedFormulaProvenanceCell spec seed) :=
  (matchingClosedFormulaProvenances spec seed A cells).map
      (fun prior =>
        { formula :=
            occurrence.replace
              (formulaSubstN B (.var y) x)
          provenance :=
            .exSubLeftVacuous prior occurrence x y hSelected
              hVacuous }) ++
    retainClosedFormulaContext seed Gamma cells

/-- Extensional coverage of a current antecedent by Type-valued formula
provenance cells.  Multiple cells with the same formula are deliberately
permitted. -/
def ClosedFormulaProvenanceCovers
    {L : Language} {spec : SkolemSpec L}
    {seed : ClosedTerm spec.language}
    (cells : List (ClosedFormulaProvenanceCell spec seed))
    (Gamma : LCS.Finset (FormulaN L)) : Prop :=
  ∀ A, A ∈ Gamma →
    ∃ cell, cell ∈ cells ∧ cell.formula = A

/-- Closed binding data for one relevant G2nnf existential-left rule.
The occurrence is exact, the index is the deterministic Step-3 allocation,
and the range equation points to the universal choices frozen in the
selected Type-valued provenance. -/
structure ClosedG2nnfBindingData
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    {Δroot : LCS.Finset (FormulaN L)}
    (root : G2nnfProofTree hNoEq
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot) where
  occurrence : G2nnfExSubLeftOccurrence (hL := hNoEq) root
  index : Fin spec.n
  binding :
    G2nnfRetentiveAllocationBinding spec occurrence index
  provenance :
    ClosedFormulaProvenance spec seed occurrence.ambient
  scopeCovered :
    provenance.universalMap.Covers
      (spec.skolemScope index)

/-- Equality-system closed binding data. -/
structure ClosedG2nnfEqBindingData
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    {Δroot : LCS.Finset (FormulaN L)}
    (root : G2nnfEqProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot) where
  occurrence : G2nnfEqExSubLeftOccurrence root
  index : Fin spec.n
  binding :
    G2nnfEqRetentiveAllocationBinding spec occurrence index
  provenance :
    ClosedFormulaProvenance spec seed occurrence.ambient
  scopeCovered :
    provenance.universalMap.Covers
      (spec.skolemScope index)

/-- The certified closed range is computed from the selected G2nnf
lineage and its explicit scope-coverage proof. -/
private def ClosedG2nnfBindingData.closedRange
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {spec : SkolemSpec L}
    {seed : ClosedTerm spec.language}
    {Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    (data : ClosedG2nnfBindingData (hNoEq := hNoEq) spec seed root) :
    ClosedTerm spec.language :=
  data.provenance.closedAllocation
    data.index data.scopeCovered

/-- Equality-system certified closed range. -/
private def ClosedG2nnfEqBindingData.closedRange
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {spec : SkolemSpec L}
    {seed : ClosedTerm spec.language}
    {Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    (data : ClosedG2nnfEqBindingData spec seed root) :
    ClosedTerm spec.language :=
  data.provenance.closedAllocation
    data.index data.scopeCovered

/-- Eigenvariables carried by a chronological G2nnf binding list. -/
def closedG2nnfBindingEigenvariables
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {spec : SkolemSpec L}
    {seed : ClosedTerm spec.language}
    {DeltaRoot : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq
      ({spec.source} : LCS.Finset (FormulaN L)) DeltaRoot}
    (bindings : List (ClosedG2nnfBindingData (hNoEq := hNoEq) spec seed root)) :
    List Nat :=
  bindings.map (fun data => data.occurrence.eigenvariable)

/-- Equality-system binding eigenvariables. -/
def closedG2nnfEqBindingEigenvariables
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {spec : SkolemSpec L}
    {seed : ClosedTerm spec.language}
    {DeltaRoot : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) DeltaRoot}
    (bindings :
      List (ClosedG2nnfEqBindingData spec seed root)) :
    List Nat :=
  bindings.map (fun data => data.occurrence.eigenvariable)

/-- Canonical proof-wide map obtained by folding the exact chronological
G2nnf binding list.  There is no separately mutable map field. -/
def closedG2nnfBindingMap
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {spec : SkolemSpec L}
    {seed : ClosedTerm spec.language}
    {DeltaRoot : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq
      ({spec.source} : LCS.Finset (FormulaN L)) DeltaRoot}
    (bindings : List (ClosedG2nnfBindingData (hNoEq := hNoEq) spec seed root)) :
    ClosedEigenvarMap spec.language :=
  bindings.foldl
    (fun eigenMap data =>
      eigenMap.insert data.occurrence.eigenvariable
        data.closedRange)
    ClosedEigenvarMap.empty

/-- Equality-system canonical binding fold. -/
def closedG2nnfEqBindingMap
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {spec : SkolemSpec L}
    {seed : ClosedTerm spec.language}
    {DeltaRoot : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) DeltaRoot}
    (bindings :
      List (ClosedG2nnfEqBindingData spec seed root)) :
    ClosedEigenvarMap spec.language :=
  bindings.foldl
    (fun eigenMap data =>
      eigenMap.insert data.occurrence.eigenvariable
        data.closedRange)
    ClosedEigenvarMap.empty

/-- Construct the only certified G2nnf binding for the supplied exact
relevant occurrence and selected covered lineage. -/
def makeClosedG2nnfBindingData
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    {Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    (occurrence : G2nnfExSubLeftOccurrence (hL := hNoEq) root)
    (hQuantifier :
      AllRulesQuantifierOnPath occurrence.path)
    (hRelevant :
      occurrence.boundVar ∈ formulaFVN occurrence.body)
    (provenance :
      ClosedFormulaProvenance
        spec seed occurrence.ambient)
    (hScopeCovered :
      provenance.universalMap.Covers
        (spec.skolemScope
          (g2nnfRetentiveAllocationIndex
            spec occurrence hQuantifier))) :
    ClosedG2nnfBindingData (hNoEq := hNoEq) spec seed root :=
  { occurrence := occurrence
    index :=
      g2nnfRetentiveAllocationIndex
        spec occurrence hQuantifier
    binding :=
      g2nnfRetentiveAllocationIndex_binding
        spec occurrence hQuantifier hRelevant
    provenance := provenance
    scopeCovered := hScopeCovered }

/-- Equality-system certified binding constructor. -/
def makeClosedG2nnfEqBindingData
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    {Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    (occurrence : G2nnfEqExSubLeftOccurrence root)
    (hQuantifier :
      AllRulesQuantifierOnPath_G2nnfEq occurrence.path)
    (hRelevant :
      occurrence.boundVar ∈ formulaFVN occurrence.body)
    (provenance :
      ClosedFormulaProvenance
        spec seed occurrence.ambient)
    (hScopeCovered :
      provenance.universalMap.Covers
        (spec.skolemScope
          (g2nnfEqRetentiveAllocationIndex
            spec occurrence hQuantifier))) :
    ClosedG2nnfEqBindingData spec seed root :=
  { occurrence := occurrence
    index :=
      g2nnfEqRetentiveAllocationIndex
        spec occurrence hQuantifier
    binding :=
      g2nnfEqRetentiveAllocationIndex_binding
        spec occurrence hQuantifier hRelevant
    provenance := provenance
    scopeCovered := hScopeCovered }

end LCS.Herbrand.SHGTheorem.Herbrand
end
