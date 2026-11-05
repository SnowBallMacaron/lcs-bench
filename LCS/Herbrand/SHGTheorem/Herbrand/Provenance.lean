import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.SyntaxAllocation
import LCS.Herbrand.SHGTheorem.Herbrand.OccurrenceLineage
import LCS.Herbrand.SHGTheorem.Herbrand.CanonicalMapRegression
import LCS.Herbrand.SHGTheorem.Herbrand.NestedMapRegression
import LCS.Herbrand.SHGTheorem.Herbrand.Alteration
import LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination
import LCS.Herbrand.SHGTheorem.Herbrand.ClosedSubstitution
import LCS.Herbrand.SHGTheorem.Herbrand.ScopeAndPurity

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

/-- An exposed existential's exact allocation scope is covered by its
construction-enforced provenance map. -/
private theorem ClosedFormulaProvenance.scopeCovered_of_allocation
    {L : Language} {spec : SkolemSpec L}
    {seed : ClosedTerm spec.language}
    {A B sourceBody : FormulaN L}
    (provenance : ClosedFormulaProvenance spec seed A)
    (occurrence : MaxQuantifierOccurrence A)
    (x : Nat)
    (hSelected :
      occurrence.selected = FormulaN.ex x B)
    (i : Fin spec.n) (scope : List Nat)
    (hAllocation :
      spec.allocation i =
        (FormulaN.ex x sourceBody, scope))
    (hScope : spec.skolemScope i = scope) :
    provenance.universalMap.Covers
      (spec.skolemScope i) := by
  obtain ⟨readyScope, hReadySource, hReadyCovers⟩ :=
    closedFormulaFrontierReady_selected_ex
      occurrence x hSelected provenance.frontierReady
  have hAllocationSource :
      QuantifierSourceScope
        spec.source [] x scope :=
    skolemAllocation_sourceScope
      spec i hAllocation
  have hScopeEq : readyScope = scope :=
    quantifierSourceScope_unique spec.hRect.2
      hReadySource hAllocationSource
  rw [hScope, ← hScopeEq]
  exact hReadyCovers

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

/-- A covered formula has at least one explicit matching provenance. -/
private theorem matchingClosedFormulaProvenances_nonempty_of_cell
    {L : Language} [DecidableEq (FormulaN L)]
    {spec : SkolemSpec L}
    {seed : ClosedTerm spec.language}
    (A : FormulaN L)
    (cells : List (ClosedFormulaProvenanceCell spec seed))
    {cell : ClosedFormulaProvenanceCell spec seed}
    (hCell : cell ∈ cells)
    (hFormula : cell.formula = A) :
    ∃ provenance,
      provenance ∈ matchingClosedFormulaProvenances
        spec seed A cells := by
  induction cells with
  | nil =>
      simp at hCell
  | cons head tail ih =>
      by_cases hHead : head.formula = A
      · refine ⟨hHead ▸ head.provenance, ?_⟩
        simp [matchingClosedFormulaProvenances, hHead]
      · have hTail : cell ∈ tail := by
          rcases List.mem_cons.mp hCell with hEq | hTail
          · subst cell
            exact (hHead hFormula).elim
          · exact hTail
        obtain ⟨provenance, hProvenance⟩ :=
          ih hTail
        exact
          ⟨provenance, by
            simpa [matchingClosedFormulaProvenances, hHead] using
              hProvenance⟩

theorem matchingClosedFormulaProvenances_nonempty_of_covers
    {L : Language} [DecidableEq (FormulaN L)]
    {spec : SkolemSpec L}
    {seed : ClosedTerm spec.language}
    {cells : List (ClosedFormulaProvenanceCell spec seed)}
    {Gamma : LCS.Finset (FormulaN L)}
    (hCovers :
      ClosedFormulaProvenanceCovers cells Gamma)
    (A : FormulaN L) (hA : A ∈ Gamma) :
    ∃ provenance,
      provenance ∈ matchingClosedFormulaProvenances
        spec seed A cells := by
  obtain ⟨cell, hCell, hFormula⟩ := hCovers A hA
  exact matchingClosedFormulaProvenances_nonempty_of_cell
    A cells hCell hFormula

/-- Exact membership characterization for context retention. -/
private theorem mem_retainClosedFormulaContext
    {L : Language} [DecidableEq (FormulaN L)]
    {spec : SkolemSpec L}
    (seed : ClosedTerm spec.language)
    (Gamma : LCS.Finset (FormulaN L))
    (cells : List (ClosedFormulaProvenanceCell spec seed))
    (cell : ClosedFormulaProvenanceCell spec seed) :
    cell ∈ retainClosedFormulaContext seed Gamma cells ↔
      cell ∈ cells ∧ cell.formula ∈ Gamma := by
  induction cells with
  | nil =>
      simp [retainClosedFormulaContext]
  | cons head tail ih =>
      constructor
      · intro hMem
        by_cases hHead : head.formula ∈ Gamma
        · rw [retainClosedFormulaContext, if_pos hHead] at hMem
          rcases List.mem_cons.mp hMem with hEq | hTail
          · subst cell
            exact ⟨List.mem_cons_self, hHead⟩
          · obtain ⟨hCellTail, hCellFormula⟩ :=
              ih.mp hTail
            exact
              ⟨List.mem_cons.mpr (Or.inr hCellTail),
                hCellFormula⟩
        · rw [retainClosedFormulaContext, if_neg hHead] at hMem
          obtain ⟨hCellTail, hCellFormula⟩ :=
            ih.mp hMem
          exact
            ⟨List.mem_cons.mpr (Or.inr hCellTail),
              hCellFormula⟩
      · rintro ⟨hMem, hCellFormula⟩
        rcases List.mem_cons.mp hMem with hEq | hTail
        · subst cell
          rw [retainClosedFormulaContext, if_pos hCellFormula]
          exact List.mem_cons_self
        · by_cases hHead : head.formula ∈ Gamma
          · rw [retainClosedFormulaContext, if_pos hHead]
            exact List.mem_cons.mpr
              (Or.inr (ih.mpr ⟨hTail, hCellFormula⟩))
          · rw [retainClosedFormulaContext, if_neg hHead]
            exact ih.mpr ⟨hTail, hCellFormula⟩

/-- Generic collision-tolerant coverage theorem for a left principal
transition: transform every matching principal provenance and retain every
raw-context cell. -/
private theorem closedFormulaProvenance_transition_covers
    {L : Language} [DecidableEq (FormulaN L)]
    {spec : SkolemSpec L}
    {seed : ClosedTerm spec.language}
    {cells : List (ClosedFormulaProvenanceCell spec seed)}
    {Gamma : LCS.Finset (FormulaN L)}
    (A replacement : FormulaN L)
    (make :
      ClosedFormulaProvenance spec seed A →
        ClosedFormulaProvenance spec seed replacement)
    (hCovers :
      ClosedFormulaProvenanceCovers cells
        (LCS.Finset.insert A Gamma)) :
    ClosedFormulaProvenanceCovers
      ((matchingClosedFormulaProvenances
          spec seed A cells).map
        (fun prior =>
          { formula := replacement
            provenance := make prior }) ++
        retainClosedFormulaContext seed Gamma cells)
      (LCS.Finset.insert replacement Gamma) := by
  intro F hF
  rcases LCS.Finset.mem_insert.mp hF with hPrincipal | hContext
  · subst F
    obtain ⟨prior, hPrior⟩ :=
      matchingClosedFormulaProvenances_nonempty_of_covers
        hCovers A
          (LCS.Finset.mem_insert.mpr (Or.inl rfl))
    refine
      ⟨{ formula := replacement
         provenance := make prior },
        List.mem_append.mpr (Or.inl ?_), rfl⟩
    exact List.mem_map.mpr ⟨prior, hPrior, rfl⟩
  · obtain ⟨cell, hCell, hFormula⟩ :=
      hCovers F
        (LCS.Finset.mem_insert.mpr (Or.inr hContext))
    refine
      ⟨cell, List.mem_append.mpr (Or.inr ?_), hFormula⟩
    apply
      (mem_retainClosedFormulaContext
        seed Gamma cells cell).mpr
    exact ⟨hCell, hFormula ▸ hContext⟩

/-- Universal-left provenance transition preserves exact antecedent
coverage, including formula-value collisions. -/
theorem closedFormulaProvenanceAllSubLeft_covers
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
    (cells : List (ClosedFormulaProvenanceCell spec seed))
    (hCovers :
      ClosedFormulaProvenanceCovers cells
        (LCS.Finset.insert A Gamma)) :
    ClosedFormulaProvenanceCovers
      (closedFormulaProvenanceAllSubLeft
        spec seed prefixMap A B occurrence x t
        hSelected Gamma cells)
      (LCS.Finset.insert
        (occurrence.replace (formulaSubstN B t x))
        Gamma) := by
  unfold closedFormulaProvenanceAllSubLeft
  dsimp only
  apply closedFormulaProvenance_transition_covers
    A (occurrence.replace (formulaSubstN B t x))
  exact hCovers

/-- Relevant existential-left provenance transition preserves coverage. -/
theorem closedFormulaProvenanceExSubLeftRelevant_covers
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
    (cells : List (ClosedFormulaProvenanceCell spec seed))
    (hCovers :
      ClosedFormulaProvenanceCovers cells
        (LCS.Finset.insert A Gamma)) :
    ClosedFormulaProvenanceCovers
      (closedFormulaProvenanceExSubLeftRelevant
        spec seed A B occurrence x y hSelected
        hRelevant i prior hScopeCovered Gamma cells)
      (LCS.Finset.insert
        (occurrence.replace
          (formulaSubstN B (.var y) x))
        Gamma) := by
  intro F hF
  rcases LCS.Finset.mem_insert.mp hF with
    hPrincipal | hContext
  · subst F
    refine
      ⟨{ formula :=
           occurrence.replace
             (formulaSubstN B (.var y) x)
         provenance :=
           .exSubLeftRelevant prior occurrence x y hSelected
             hRelevant i hScopeCovered
             (prior.closedAllocation i hScopeCovered) rfl },
        ?_, rfl⟩
    simp [closedFormulaProvenanceExSubLeftRelevant]
  · obtain ⟨cell, hCell, hFormula⟩ :=
      hCovers F
        (LCS.Finset.mem_insert.mpr (Or.inr hContext))
    refine
      ⟨cell, ?_, hFormula⟩
    apply List.mem_append.mpr
    right
    apply
      (mem_retainClosedFormulaContext
        seed Gamma cells cell).mpr
    exact ⟨hCell, hFormula ▸ hContext⟩

/-- Vacuous existential-left provenance transition preserves coverage
without allocating a range. -/
theorem closedFormulaProvenanceExSubLeftVacuous_covers
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
    (cells : List (ClosedFormulaProvenanceCell spec seed))
    (hCovers :
      ClosedFormulaProvenanceCovers cells
        (LCS.Finset.insert A Gamma)) :
    ClosedFormulaProvenanceCovers
      (closedFormulaProvenanceExSubLeftVacuous
        spec seed A B occurrence x y hSelected
        hVacuous Gamma cells)
      (LCS.Finset.insert
        (occurrence.replace
          (formulaSubstN B (.var y) x))
        Gamma) := by
  unfold closedFormulaProvenanceExSubLeftVacuous
  apply closedFormulaProvenance_transition_covers
    A
      (occurrence.replace
        (formulaSubstN B (.var y) x))
  exact hCovers

/-- The computable data component of the allocation selected by a source
existential binder.  `findIdx` supplies the `Nat`; the membership proof is
used only for the `Fin` bound and never as a Prop-to-Type choice oracle. -/
private def skolemAllocationIndexOfBinder
    {L : Language} (spec : SkolemSpec L) (x : Nat)
    (hx : x ∈ existentialBinderSequence spec.source) :
    Fin spec.n :=
  let binders :=
    spec.allocations.map existentialDescriptorBinder
  let k := binders.findIdx (· == x)
  ⟨k, by
    have hxBinders : x ∈ binders := by
      simpa [binders, SkolemSpec.allocations,
        existentialDescriptors,
        existentialDescriptorsAux_binders] using hx
    have hWitness :
        ∃ y, y ∈ binders ∧ (y == x) = true :=
      ⟨x, hxBinders, by simp⟩
    have hk : k < binders.length :=
      List.findIdx_lt_length.mpr hWitness
    simpa [k, binders, SkolemSpec.n] using hk⟩

/-- The deterministic binder index agrees with any exact allocation whose
descriptor has that binder.  Rectification supplies binder-list `Nodup`. -/
private theorem skolemAllocationIndexOfBinder_eq_of_allocation
    {L : Language} (spec : SkolemSpec L) (x : Nat)
    (hx : x ∈ existentialBinderSequence spec.source)
    (j : Fin spec.n) (sourceBody : FormulaN L)
    (scope : List Nat)
    (hj :
      spec.allocation j =
        (FormulaN.ex x sourceBody, scope)) :
    skolemAllocationIndexOfBinder spec x hx = j := by
  let binders :=
    spec.allocations.map existentialDescriptorBinder
  let i := skolemAllocationIndexOfBinder spec x hx
  have hNodup : binders.Nodup := by
    dsimp only [binders]
    rw [SkolemSpec.allocations, existentialDescriptors,
      existentialDescriptorsAux_binders]
    exact existentialBinderSequence_nodup
      spec.source spec.hRect.2
  have hiLt : i.val < binders.length := by
    simpa [i, binders, SkolemSpec.n] using i.isLt
  have hjLt : j.val < binders.length := by
    simpa [binders, SkolemSpec.n] using j.isLt
  have hiValue : binders[i.val] = x := by
    have hFoundLt :
        binders.findIdx (· == x) < binders.length :=
      List.findIdx_lt_length.mpr
        ⟨x, by
          simpa [binders, SkolemSpec.allocations,
            existentialDescriptors,
            existentialDescriptorsAux_binders] using hx,
          by simp⟩
    have hFound :
        ((binders[binders.findIdx (· == x)]'hFoundLt) == x) =
          true :=
      List.findIdx_getElem
        (xs := binders) (p := fun y => y == x)
        (w := hFoundLt)
    have hEq :
        binders[binders.findIdx (· == x)]'hFoundLt = x :=
      beq_iff_eq.mp hFound
    simpa [i, skolemAllocationIndexOfBinder, binders] using hEq
  have hjValue : binders[j.val] = x := by
    simp only [binders, List.getElem_map]
    change existentialDescriptorBinder (spec.allocation j) = x
    rw [hj]
    rfl
  apply Fin.ext
  by_cases hij : i.val = j.val
  · exact hij
  · rcases Nat.lt_or_gt_of_ne hij with hij | hji
    · exact False.elim
        ((List.pairwise_iff_getElem.mp hNodup
          i.val j.val hiLt hjLt hij)
          (hiValue.trans hjValue.symm))
    · exact False.elim
        ((List.pairwise_iff_getElem.mp hNodup
          j.val i.val hjLt hiLt hji)
          (hjValue.trans hiValue.symm))

/-- The source binder of one exact relevant G2nnf existential-left
occurrence is present in the source allocation traversal. -/
private theorem g2nnfRetentiveOccurrence_sourceBinder
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    {Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    (occurrence : G2nnfExSubLeftOccurrence (hL := hNoEq) root)
    (hQuantifier :
      AllRulesQuantifierOnPath occurrence.path) :
    occurrence.boundVar ∈
      existentialBinderSequence spec.source := by
  have hAmbient :
      occurrence.ambient ∈
        LCS.Finset.insert occurrence.ambient occurrence.gamma :=
    LCS.Finset.mem_insert.mpr (Or.inl rfl)
  have hLineage :
      g2nnfRetentiveAntecedentLineage
        occurrence.path spec.source occurrence.ambient :=
    g2nnfRetentiveAntecedentLineage_from_singleton
      occurrence.path hQuantifier hAmbient
  apply g2nnfRetentiveAntecedentLineage_exBinders
    hLineage occurrence.boundVar
  exact maxQuantifierOccurrence_exBinder_mem
    occurrence.maxOccurrence occurrence.hSelected

/-- Equality-system source-binder extraction. -/
private theorem g2nnfEqRetentiveOccurrence_sourceBinder
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    {Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    (occurrence : G2nnfEqExSubLeftOccurrence root)
    (hQuantifier :
      AllRulesQuantifierOnPath_G2nnfEq occurrence.path) :
    occurrence.boundVar ∈
      existentialBinderSequence spec.source := by
  have hAmbient :
      occurrence.ambient ∈
        LCS.Finset.insert occurrence.ambient occurrence.gamma :=
    LCS.Finset.mem_insert.mpr (Or.inl rfl)
  have hLineage :
      g2nnfEqRetentiveAntecedentLineage
        occurrence.path spec.source occurrence.ambient :=
    g2nnfEqRetentiveAntecedentLineage_from_singleton
      occurrence.path hQuantifier hAmbient
  apply g2nnfEqRetentiveAntecedentLineage_exBinders
    hLineage occurrence.boundVar
  exact maxQuantifierOccurrence_exBinder_mem
    occurrence.maxOccurrence occurrence.hSelected

/-- Deterministic exact allocation index for a G2nnf rule occurrence. -/
def g2nnfRetentiveAllocationIndex
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    {Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    (occurrence : G2nnfExSubLeftOccurrence (hL := hNoEq) root)
    (hQuantifier :
      AllRulesQuantifierOnPath occurrence.path) :
    Fin spec.n :=
  skolemAllocationIndexOfBinder spec occurrence.boundVar
    (g2nnfRetentiveOccurrence_sourceBinder
      spec occurrence hQuantifier)

/-- Deterministic exact allocation index for an equality-system rule
occurrence. -/
def g2nnfEqRetentiveAllocationIndex
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    {Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    (occurrence : G2nnfEqExSubLeftOccurrence root)
    (hQuantifier :
      AllRulesQuantifierOnPath_G2nnfEq occurrence.path) :
    Fin spec.n :=
  skolemAllocationIndexOfBinder spec occurrence.boundVar
    (g2nnfEqRetentiveOccurrence_sourceBinder
      spec occurrence hQuantifier)

/-- The deterministic G2nnf index satisfies the exact Step-3 binding
predicate.  Existential elimination is used only inside this Prop proof;
the returned `Fin` data was already computed by `findIdx`. -/
theorem g2nnfRetentiveAllocationIndex_binding
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    {Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    (occurrence : G2nnfExSubLeftOccurrence (hL := hNoEq) root)
    (hQuantifier :
      AllRulesQuantifierOnPath occurrence.path)
    (hRelevant :
      occurrence.boundVar ∈ formulaFVN occurrence.body) :
    G2nnfRetentiveAllocationBinding spec occurrence
      (g2nnfRetentiveAllocationIndex
        spec occurrence hQuantifier) := by
  obtain ⟨j, hBinding, _hUnique⟩ :=
    g2nnfRetentiveAllocationBinding_existsUnique
      spec occurrence hQuantifier hRelevant
  rcases hBinding with
    ⟨hRelevant', hLineage, sourceAddress, sourceBody, scope,
      hSite, hAddress, hFormula, hAllocation, hSelected,
      hScope, hScopeNodup⟩
  have hIndex :
      g2nnfRetentiveAllocationIndex
          spec occurrence hQuantifier = j := by
    apply skolemAllocationIndexOfBinder_eq_of_allocation
      spec occurrence.boundVar
      (g2nnfRetentiveOccurrence_sourceBinder
        spec occurrence hQuantifier)
      j sourceBody scope hAllocation
  rw [hIndex]
  exact
    ⟨hRelevant', hLineage, sourceAddress, sourceBody, scope,
      hSite, hAddress, hFormula, hAllocation, hSelected,
      hScope, hScopeNodup⟩

/-- Equality-system deterministic binding theorem. -/
theorem g2nnfEqRetentiveAllocationIndex_binding
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    {Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    (occurrence : G2nnfEqExSubLeftOccurrence root)
    (hQuantifier :
      AllRulesQuantifierOnPath_G2nnfEq occurrence.path)
    (hRelevant :
      occurrence.boundVar ∈ formulaFVN occurrence.body) :
    G2nnfEqRetentiveAllocationBinding spec occurrence
      (g2nnfEqRetentiveAllocationIndex
        spec occurrence hQuantifier) := by
  obtain ⟨j, hBinding, _hUnique⟩ :=
    g2nnfEqRetentiveAllocationBinding_existsUnique
      spec occurrence hQuantifier hRelevant
  rcases hBinding with
    ⟨hRelevant', hLineage, sourceAddress, sourceBody, scope,
      hSite, hAddress, hFormula, hAllocation, hSelected,
      hScope, hScopeNodup⟩
  have hIndex :
      g2nnfEqRetentiveAllocationIndex
          spec occurrence hQuantifier = j := by
    apply skolemAllocationIndexOfBinder_eq_of_allocation
      spec occurrence.boundVar
      (g2nnfEqRetentiveOccurrence_sourceBinder
        spec occurrence hQuantifier)
      j sourceBody scope hAllocation
  rw [hIndex]
  exact
    ⟨hRelevant', hLineage, sourceAddress, sourceBody, scope,
      hSite, hAddress, hFormula, hAllocation, hSelected,
      hScope, hScopeNodup⟩

/-- The selected G2nnf provenance has every exact allocation argument
available before the relevant existential-left step is crossed. -/
theorem closedFormulaProvenance_scopeCovered_g2nnf
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {spec : SkolemSpec L}
    {seed : ClosedTerm spec.language}
    {Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    (occurrence : G2nnfExSubLeftOccurrence (hL := hNoEq) root)
    (i : Fin spec.n)
    (binding :
      G2nnfRetentiveAllocationBinding spec occurrence i)
    (provenance :
      ClosedFormulaProvenance
        spec seed occurrence.ambient) :
    provenance.universalMap.Covers
      (spec.skolemScope i) := by
  rcases binding with
    ⟨_hRelevant, _hLineage, _sourceAddress,
      sourceBody, scope, _hSite, _hAddress, _hFormula,
      hAllocation, _hSelected, hScope, _hScopeNodup⟩
  exact provenance.scopeCovered_of_allocation
    occurrence.maxOccurrence occurrence.boundVar
    occurrence.hSelected i scope hAllocation hScope

/-- Equality-system mirror of exact provenance scope coverage. -/
theorem closedFormulaProvenance_scopeCovered_g2nnfEq
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {spec : SkolemSpec L}
    {seed : ClosedTerm spec.language}
    {Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    (occurrence : G2nnfEqExSubLeftOccurrence root)
    (i : Fin spec.n)
    (binding :
      G2nnfEqRetentiveAllocationBinding spec occurrence i)
    (provenance :
      ClosedFormulaProvenance
        spec seed occurrence.ambient) :
    provenance.universalMap.Covers
      (spec.skolemScope i) := by
  rcases binding with
    ⟨_hRelevant, _hLineage, _sourceAddress,
      sourceBody, scope, _hSite, _hAddress, _hFormula,
      hAllocation, _hSelected, hScope, _hScopeNodup⟩
  exact provenance.scopeCovered_of_allocation
    occurrence.maxOccurrence occurrence.boundVar
    occurrence.hSelected i scope hAllocation hScope

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

/-- Enumerate exact relevant G2nnf occurrences along one supplied path,
threading the exact root-to-current pfx. -/
private noncomputable def
    g2nnfRelevantExSubLeftOccurrencesOnPathAux
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γcur Δcur Γnode Δnode :
      LCS.Finset (FormulaN L)}
    (root : G2nnfProofTree hNoEq Γroot Δroot)
    {current : G2nnfProofTree hNoEq Γcur Δcur}
    (pfx : G2nnfProofTree.RootToNodePath root current)
    {node : G2nnfProofTree hNoEq Γnode Δnode} :
    G2nnfProofTree.RootToNodePath current node →
      List (G2nnfExSubLeftOccurrence (hL := hNoEq) root)
  | .root _ => []
  | .onePremise rule hAdmit hPrem hSC sub tail =>
      let step :
          G2nnfProofTree.RootToNodePath
            (.onePremise rule hAdmit hPrem hSC sub) sub :=
        .onePremise rule hAdmit hPrem hSC sub (.root sub)
      let subPrefix := pfx.trans step
      let rest := g2nnfRelevantExSubLeftOccurrencesOnPathAux root subPrefix tail
      match rule with
      | .exSubLeft A occurrence x B y hSelected Gamma Delta =>
          letI : Decidable (x ∈ formulaFVN B) := Classical.propDecidable _
          if hRelevant : x ∈ formulaFVN B then
            ({ ambient := A
               maxOccurrence := occurrence
               boundVar := x
               body := B
               eigenvariable := y
               hSelected := hSelected
               gamma := Gamma
               delta := Delta
               hPrem := hPrem
               hSC := hSC
               premise := sub
               path := pfx } :
              G2nnfExSubLeftOccurrence (hL := hNoEq) root) ::
              rest
          else
            rest
      | _ =>
          rest
  | .leftPremise rule hAdmit hPrem hSC sub₁ sub₂ tail =>
      let step :
          G2nnfProofTree.RootToNodePath
            (.twoPremise rule hAdmit hPrem hSC sub₁ sub₂)
            sub₁ :=
        .leftPremise rule hAdmit hPrem hSC sub₁ sub₂
          (.root sub₁)
      g2nnfRelevantExSubLeftOccurrencesOnPathAux
        root (pfx.trans step) tail
  | .rightPremise rule hAdmit hPrem hSC sub₁ sub₂ tail =>
      let step :
          G2nnfProofTree.RootToNodePath
            (.twoPremise rule hAdmit hPrem hSC sub₁ sub₂)
            sub₂ :=
        .rightPremise rule hAdmit hPrem hSC sub₁ sub₂
          (.root sub₂)
      g2nnfRelevantExSubLeftOccurrencesOnPathAux
        root (pfx.trans step) tail

private noncomputable def
    g2nnfRelevantExSubLeftOccurrencesOnPath
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode :
      LCS.Finset (FormulaN L)}
    (root : G2nnfProofTree hNoEq Γroot Δroot)
    {node : G2nnfProofTree hNoEq Γnode Δnode}
    (path : G2nnfProofTree.RootToNodePath root node) :
    List (G2nnfExSubLeftOccurrence (hL := hNoEq) root) :=
  g2nnfRelevantExSubLeftOccurrencesOnPathAux
    root (.root root) path

/-- Equality-system exact relevant-occurrence enumeration. -/
private noncomputable def
    g2nnfEqRelevantExSubLeftOccurrencesOnPathAux
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γcur Δcur Γnode Δnode :
      LCS.Finset (FormulaN L)}
    (root : G2nnfEqProofTree hL Γroot Δroot)
    {current : G2nnfEqProofTree hL Γcur Δcur}
    (pfx :
      G2nnfEqProofTree.RootToNodePath root current)
    {node : G2nnfEqProofTree hL Γnode Δnode} :
    G2nnfEqProofTree.RootToNodePath current node →
      List (G2nnfEqExSubLeftOccurrence root)
  | .root _ => []
  | .onePremise rule hAdmit hPrem hSC sub tail =>
      let step :
          G2nnfEqProofTree.RootToNodePath
            (.onePremise rule hAdmit hPrem hSC sub) sub :=
        .onePremise rule hAdmit hPrem hSC sub (.root sub)
      let subPrefix := pfx.trans step
      let rest := g2nnfEqRelevantExSubLeftOccurrencesOnPathAux root subPrefix tail
      match rule with
      | .exSubLeft A occurrence x B y hSelected Gamma Delta =>
          letI : Decidable (x ∈ formulaFVN B) := Classical.propDecidable _
          if hRelevant : x ∈ formulaFVN B then
            ({ ambient := A
               maxOccurrence := occurrence
               boundVar := x
               body := B
               eigenvariable := y
               hSelected := hSelected
               gamma := Gamma
               delta := Delta
               hPrem := hPrem
               hSC := hSC
               premise := sub
               path := pfx } :
              G2nnfEqExSubLeftOccurrence root) ::
              rest
          else
            rest
      | _ =>
          rest
  | .leftPremise rule hAdmit hPrem hSC sub₁ sub₂ tail =>
      let step :
          G2nnfEqProofTree.RootToNodePath
            (.twoPremise rule hAdmit hPrem hSC sub₁ sub₂)
            sub₁ :=
        .leftPremise rule hAdmit hPrem hSC sub₁ sub₂
          (.root sub₁)
      g2nnfEqRelevantExSubLeftOccurrencesOnPathAux
        root (pfx.trans step) tail
  | .rightPremise rule hAdmit hPrem hSC sub₁ sub₂ tail =>
      let step :
          G2nnfEqProofTree.RootToNodePath
            (.twoPremise rule hAdmit hPrem hSC sub₁ sub₂)
            sub₂ :=
        .rightPremise rule hAdmit hPrem hSC sub₁ sub₂
          (.root sub₂)
      g2nnfEqRelevantExSubLeftOccurrencesOnPathAux
        root (pfx.trans step) tail

private noncomputable def
    g2nnfEqRelevantExSubLeftOccurrencesOnPath
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode :
      LCS.Finset (FormulaN L)}
    (root : G2nnfEqProofTree hL Γroot Δroot)
    {node : G2nnfEqProofTree hL Γnode Δnode}
    (path : G2nnfEqProofTree.RootToNodePath root node) :
    List (G2nnfEqExSubLeftOccurrence root) :=
  g2nnfEqRelevantExSubLeftOccurrencesOnPathAux
    root (.root root) path

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

/-- A construction trace tying final cells and bindings to every exact
equality-free G2nnf Core path step.  The relevant constructor stores membership of the
selected provenance in the predecessor state. -/
inductive ClosedG2nnfLowerTrace
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    {Δroot : LCS.Finset (FormulaN L)}
    (root : G2nnfProofTree hNoEq
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot) :
    {Γnode Δnode : LCS.Finset (FormulaN L)} →
    (node : G2nnfProofTree hNoEq Γnode Δnode) →
    G2nnfProofTree.RootToNodePath root node →
    List (ClosedFormulaProvenanceCell spec seed) →
    List (ClosedG2nnfBindingData (hNoEq := hNoEq) spec seed root) → Type where
  | root :
      ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root root (.root root)
        [{ formula := spec.source
           provenance :=
             ClosedFormulaProvenance.source spec seed }]
        []
  | allSubLeft
      {A B : FormulaN L}
      {occurrence : MaxQuantifierOccurrence A}
      {x : Nat} {t : Term L}
      {hSelected :
        occurrence.selected = FormulaN.all x B}
      {Gamma Delta : LCS.Finset (FormulaN L)}
      {hPrem :
        ((G2nnfRuleCore.allSubLeft A occurrence x B t
          hSelected Gamma Delta).premises).length = 1}
      {hSC :
        G2nnfRuleCore.SideConditions
          (.allSubLeft A occurrence x B t hSelected Gamma Delta)}
      {sub : G2nnfProofTree hNoEq
        (((G2nnfRuleCore.allSubLeft A occurrence x B t
          hSelected Gamma Delta).premises)[0]'(by omega)).1
        (((G2nnfRuleCore.allSubLeft A occurrence x B t
          hSelected Gamma Delta).premises)[0]'(by omega)).2}
      {pfx :
        G2nnfProofTree.RootToNodePath root
          (.onePremise
            (.allSubLeft A occurrence x B t hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)}
      {cells : List (ClosedFormulaProvenanceCell spec seed)}
      {bindings :
        List (ClosedG2nnfBindingData (hNoEq := hNoEq) spec seed root)}
      (prior :
        ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root
          (.onePremise
            (.allSubLeft A occurrence x B t hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)
          pfx cells bindings) :
      ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root sub
        (pfx.trans
          (.onePremise
            (.allSubLeft A occurrence x B t hSelected Gamma Delta)
            (by trivial) hPrem hSC sub (.root sub)))
        (closedFormulaProvenanceAllSubLeft
          spec seed (closedG2nnfBindingMap bindings)
          A B occurrence x t hSelected Gamma cells)
        bindings
  | allSubRight
      {A B : FormulaN L}
      {occurrence : MaxQuantifierOccurrence A}
      {x y : Nat}
      {hSelected :
        occurrence.selected = FormulaN.all x B}
      {Gamma Delta : LCS.Finset (FormulaN L)}
      {hPrem :
        ((G2nnfRuleCore.allSubRight A occurrence x B y
          hSelected Gamma Delta).premises).length = 1}
      {hSC :
        G2nnfRuleCore.SideConditions
          (.allSubRight A occurrence x B y hSelected Gamma Delta)}
      {sub : G2nnfProofTree hNoEq
        (((G2nnfRuleCore.allSubRight A occurrence x B y
          hSelected Gamma Delta).premises)[0]'(by omega)).1
        (((G2nnfRuleCore.allSubRight A occurrence x B y
          hSelected Gamma Delta).premises)[0]'(by omega)).2}
      {pfx :
        G2nnfProofTree.RootToNodePath root
          (.onePremise
            (.allSubRight A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)}
      {cells : List (ClosedFormulaProvenanceCell spec seed)}
      {bindings :
        List (ClosedG2nnfBindingData (hNoEq := hNoEq) spec seed root)}
      (prior :
        ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root
          (.onePremise
            (.allSubRight A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)
          pfx cells bindings) :
      ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root sub
        (pfx.trans
          (.onePremise
            (.allSubRight A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub (.root sub)))
        cells bindings
  | exSubLeftRelevant
      {A B : FormulaN L}
      {occurrence : MaxQuantifierOccurrence A}
      {x y : Nat}
      {hSelected :
        occurrence.selected = FormulaN.ex x B}
      {Gamma Delta : LCS.Finset (FormulaN L)}
      {hPrem :
        ((G2nnfRuleCore.exSubLeft A occurrence x B y
          hSelected Gamma Delta).premises).length = 1}
      {hSC :
        G2nnfRuleCore.SideConditions
          (.exSubLeft A occurrence x B y hSelected Gamma Delta)}
      {sub : G2nnfProofTree hNoEq
        (((G2nnfRuleCore.exSubLeft A occurrence x B y
          hSelected Gamma Delta).premises)[0]'(by omega)).1
        (((G2nnfRuleCore.exSubLeft A occurrence x B y
          hSelected Gamma Delta).premises)[0]'(by omega)).2}
      {pfx :
        G2nnfProofTree.RootToNodePath root
          (.onePremise
            (.exSubLeft A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)}
      {cells : List (ClosedFormulaProvenanceCell spec seed)}
      {bindings :
        List (ClosedG2nnfBindingData (hNoEq := hNoEq) spec seed root)}
      (priorTrace :
        ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root
          (.onePremise
            (.exSubLeft A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)
          pfx cells bindings)
      (hPrefix : AllRulesQuantifierOnPath pfx)
      (hRelevant : x ∈ formulaFVN B)
      (prior :
        ClosedFormulaProvenance spec seed A)
      (hPrior :
        prior ∈
          matchingClosedFormulaProvenances
            spec seed A cells)
      (hScopeCovered :
        prior.universalMap.Covers
          (spec.skolemScope
            (g2nnfRetentiveAllocationIndex spec
              ({ ambient := A
                 maxOccurrence := occurrence
                 boundVar := x
                 body := B
                 eigenvariable := y
                 hSelected := hSelected
                 gamma := Gamma
                 delta := Delta
                 hPrem := hPrem
                 hSC := hSC
                 premise := sub
                 path := pfx } :
                G2nnfExSubLeftOccurrence (hL := hNoEq) root)
              hPrefix))) :
      ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root sub
        (pfx.trans
          (.onePremise
            (.exSubLeft A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub (.root sub)))
        (closedFormulaProvenanceExSubLeftRelevant
          spec seed A B occurrence x y hSelected hRelevant
          (g2nnfRetentiveAllocationIndex spec
            ({ ambient := A
               maxOccurrence := occurrence
               boundVar := x
               body := B
               eigenvariable := y
               hSelected := hSelected
               gamma := Gamma
               delta := Delta
               hPrem := hPrem
               hSC := hSC
               premise := sub
               path := pfx } :
              G2nnfExSubLeftOccurrence (hL := hNoEq) root)
            hPrefix)
          prior hScopeCovered Gamma cells)
        (bindings ++
          [makeClosedG2nnfBindingData (hNoEq := hNoEq) spec seed
            ({ ambient := A
               maxOccurrence := occurrence
               boundVar := x
               body := B
               eigenvariable := y
               hSelected := hSelected
               gamma := Gamma
               delta := Delta
               hPrem := hPrem
               hSC := hSC
               premise := sub
               path := pfx } :
              G2nnfExSubLeftOccurrence (hL := hNoEq) root)
            hPrefix hRelevant prior hScopeCovered])
  | exSubLeftVacuous
      {A B : FormulaN L}
      {occurrence : MaxQuantifierOccurrence A}
      {x y : Nat}
      {hSelected :
        occurrence.selected = FormulaN.ex x B}
      {Gamma Delta : LCS.Finset (FormulaN L)}
      {hPrem :
        ((G2nnfRuleCore.exSubLeft A occurrence x B y
          hSelected Gamma Delta).premises).length = 1}
      {hSC :
        G2nnfRuleCore.SideConditions
          (.exSubLeft A occurrence x B y hSelected Gamma Delta)}
      {sub : G2nnfProofTree hNoEq
        (((G2nnfRuleCore.exSubLeft A occurrence x B y
          hSelected Gamma Delta).premises)[0]'(by omega)).1
        (((G2nnfRuleCore.exSubLeft A occurrence x B y
          hSelected Gamma Delta).premises)[0]'(by omega)).2}
      {pfx :
        G2nnfProofTree.RootToNodePath root
          (.onePremise
            (.exSubLeft A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)}
      {cells : List (ClosedFormulaProvenanceCell spec seed)}
      {bindings :
        List (ClosedG2nnfBindingData (hNoEq := hNoEq) spec seed root)}
      (prior :
        ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root
          (.onePremise
            (.exSubLeft A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)
          pfx cells bindings)
      (hVacuous : x ∉ formulaFVN B) :
      ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root sub
        (pfx.trans
          (.onePremise
            (.exSubLeft A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub (.root sub)))
        (closedFormulaProvenanceExSubLeftVacuous
          spec seed A B occurrence x y hSelected hVacuous
          Gamma cells)
        bindings
  | exSubRight
      {A B : FormulaN L}
      {occurrence : MaxQuantifierOccurrence A}
      {x : Nat} {t : Term L}
      {hSelected :
        occurrence.selected = FormulaN.ex x B}
      {Gamma Delta : LCS.Finset (FormulaN L)}
      {hPrem :
        ((G2nnfRuleCore.exSubRight A occurrence x B t
          hSelected Gamma Delta).premises).length = 1}
      {hSC :
        G2nnfRuleCore.SideConditions
          (.exSubRight A occurrence x B t hSelected Gamma Delta)}
      {sub : G2nnfProofTree hNoEq
        (((G2nnfRuleCore.exSubRight A occurrence x B t
          hSelected Gamma Delta).premises)[0]'(by omega)).1
        (((G2nnfRuleCore.exSubRight A occurrence x B t
          hSelected Gamma Delta).premises)[0]'(by omega)).2}
      {pfx :
        G2nnfProofTree.RootToNodePath root
          (.onePremise
            (.exSubRight A occurrence x B t hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)}
      {cells : List (ClosedFormulaProvenanceCell spec seed)}
      {bindings :
        List (ClosedG2nnfBindingData (hNoEq := hNoEq) spec seed root)}
      (prior :
        ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root
          (.onePremise
            (.exSubRight A occurrence x B t hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)
          pfx cells bindings) :
      ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root sub
        (pfx.trans
          (.onePremise
            (.exSubRight A occurrence x B t hSelected Gamma Delta)
            (by trivial) hPrem hSC sub (.root sub)))
        cells bindings

/-- Endpoint-indexed G2nnf state.  The trace prevents arbitrary cells or
bindings from being attached to a path. -/
structure ClosedG2nnfLowerState
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    {Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    (root : G2nnfProofTree hNoEq
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot)
    (node : G2nnfProofTree hNoEq Γnode Δnode) where
  path : G2nnfProofTree.RootToNodePath root node
  pathQuantifier : AllRulesQuantifierOnPath path
  pathPure :
    isPureVariableProofG2nnfAux root node path
  formulaProvenance :
    List (ClosedFormulaProvenanceCell spec seed)
  bindings : List (ClosedG2nnfBindingData (hNoEq := hNoEq) spec seed root)
  trace :
    ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root node path
      formulaProvenance bindings
  covers :
    ClosedFormulaProvenanceCovers formulaProvenance Γnode
  live :
    AntecedentVariablesLive
      (closedG2nnfBindingEigenvariables bindings) Γnode
  bindingEigenvariablesNodup :
    (closedG2nnfBindingEigenvariables bindings).Nodup

end LCS.Herbrand.SHGTheorem.Herbrand
end

