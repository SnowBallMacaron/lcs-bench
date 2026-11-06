import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.EigenvarSubstitution
import LCS.Herbrand.SHGTheorem.Herbrand.OccurrenceLineage

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

/-- Retentive allocation alignment for one relevant existential-left
occurrence at the endpoint of its exact G2nnf lower path.  The dependent
occurrence certificate ties the ambient and selected existential to the
actual endpoint rule, while the site lookup ties one allocation index
simultaneously to its source address, existential binder/body, and
universal scope. -/
def G2nnfRetentiveAllocationBinding
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    {Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    (occurrence : G2nnfExSubLeftOccurrence (hL := hL) root)
    (i : Fin spec.n) : Prop :=
  occurrence.boundVar ∈ formulaFVN occurrence.body ∧
    g2nnfRetentiveAntecedentLineage
      occurrence.path spec.source occurrence.ambient ∧
    ∃ sourceAddress sourceBody scope,
      (existentialSitesAux spec.source [])[i.val]? =
          some
            (sourceAddress,
              (FormulaN.ex occurrence.boundVar sourceBody, scope)) ∧
        skolemOccurrenceAddress? spec i =
          some sourceAddress ∧
        formulaAtOccurrenceAddress spec.source sourceAddress =
          some (FormulaN.ex occurrence.boundVar sourceBody) ∧
        spec.allocation i =
          (FormulaN.ex occurrence.boundVar sourceBody, scope) ∧
        occurrence.maxOccurrence.selected =
          FormulaN.ex occurrence.boundVar occurrence.body ∧
        spec.skolemScope i = scope ∧
        scope.Nodup

/-- Equality-system mirror of retentive allocation alignment. -/
noncomputable def G2nnfEqRetentiveAllocationBinding
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    {Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    (occurrence : G2nnfEqExSubLeftOccurrence root)
    (i : Fin spec.n) : Prop :=
  occurrence.boundVar ∈ formulaFVN occurrence.body ∧
    g2nnfEqRetentiveAntecedentLineage
      occurrence.path spec.source occurrence.ambient ∧
    ∃ sourceAddress sourceBody scope,
      (existentialSitesAux spec.source [])[i.val]? =
          some
            (sourceAddress,
              (FormulaN.ex occurrence.boundVar sourceBody, scope)) ∧
        skolemOccurrenceAddress? spec i =
          some sourceAddress ∧
        formulaAtOccurrenceAddress spec.source sourceAddress =
          some (FormulaN.ex occurrence.boundVar sourceBody) ∧
        spec.allocation i =
          (FormulaN.ex occurrence.boundVar sourceBody, scope) ∧
        occurrence.maxOccurrence.selected =
          FormulaN.ex occurrence.boundVar occurrence.body ∧
        spec.skolemScope i = scope ∧
        scope.Nodup

/-- Every relevant G2nnf existential-left cell in a singleton-source
quantifier path has exactly one source allocation.  The occurrence
certificate fixes the endpoint rule without adding that rule to its strict
ancestor path.  Existence follows the collision-tolerant lineage;
uniqueness and scope `Nodup` follow from the source's rectification
invariant. -/
theorem g2nnfRetentiveAllocationBinding_existsUnique
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    {Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    (occurrence : G2nnfExSubLeftOccurrence (hL := hL) root)
    (hQuantifier :
      AllRulesQuantifierOnPath occurrence.path)
    (hRelevant :
      occurrence.boundVar ∈ formulaFVN occurrence.body) :
    ∃ i : Fin spec.n,
      G2nnfRetentiveAllocationBinding spec occurrence i ∧
        ∀ j : Fin spec.n,
          G2nnfRetentiveAllocationBinding spec occurrence j →
            j = i := by
  have hAmbient :
      occurrence.ambient ∈
        LCS.Finset.insert occurrence.ambient occurrence.gamma :=
    LCS.Finset.mem_insert.mpr (Or.inl rfl)
  have hLineage :
      g2nnfRetentiveAntecedentLineage
        occurrence.path spec.source occurrence.ambient :=
    g2nnfRetentiveAntecedentLineage_from_singleton
      occurrence.path hQuantifier hAmbient
  have hAmbientBinder :
      occurrence.boundVar ∈
        existentialBinderSequence occurrence.ambient :=
    maxQuantifierOccurrence_exBinder_mem
      occurrence.maxOccurrence occurrence.hSelected
  have hSourceBinder :
      occurrence.boundVar ∈
        existentialBinderSequence spec.source :=
    g2nnfRetentiveAntecedentLineage_exBinders
      hLineage occurrence.boundVar hAmbientBinder
  obtain ⟨i, sourceBody, scope, hAllocation⟩ :=
    skolemAllocation_exists_of_exBinder spec hSourceBinder
  obtain ⟨sourceAddress, hSite, hAddress, hFormula⟩ :=
    skolem_site_lookup spec i
  have hScope :
      spec.skolemScope i = scope := by
    simp [SkolemSpec.skolemScope, hAllocation]
  have hScopeNodup : scope.Nodup := by
    rw [← hScope]
    exact skolemScope_nodup spec i
  refine ⟨i, ?_, ?_⟩
  · refine
      ⟨hRelevant, hLineage, sourceAddress, sourceBody, scope,
        ?_, hAddress, ?_, hAllocation, occurrence.hSelected,
        hScope, hScopeNodup⟩
    · simpa [hAllocation] using hSite
    · simpa [hAllocation] using hFormula
  · intro j hBinding
    rcases hBinding with
      ⟨_hOtherRelevant, _hOtherLineage,
        otherAddress, otherBody, otherScope, hOtherSite,
        hOtherAddress, hOtherFormula,
        hOtherAllocation, hOtherSelected,
        hOtherScope, hOtherScopeNodup⟩
    exact
      skolemAllocation_index_unique_of_binder spec
        hOtherAllocation hAllocation

/-- Equality-system existence and uniqueness for the same relevant
lower-path cell. -/
theorem g2nnfEqRetentiveAllocationBinding_existsUnique
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
    ∃ i : Fin spec.n,
      G2nnfEqRetentiveAllocationBinding spec occurrence i ∧
        ∀ j : Fin spec.n,
          G2nnfEqRetentiveAllocationBinding spec occurrence j →
            j = i := by
  have hAmbient :
      occurrence.ambient ∈
        LCS.Finset.insert occurrence.ambient occurrence.gamma :=
    LCS.Finset.mem_insert.mpr (Or.inl rfl)
  have hLineage :
      g2nnfEqRetentiveAntecedentLineage
        occurrence.path spec.source occurrence.ambient :=
    g2nnfEqRetentiveAntecedentLineage_from_singleton
      occurrence.path hQuantifier hAmbient
  have hAmbientBinder :
      occurrence.boundVar ∈
        existentialBinderSequence occurrence.ambient :=
    maxQuantifierOccurrence_exBinder_mem
      occurrence.maxOccurrence occurrence.hSelected
  have hSourceBinder :
      occurrence.boundVar ∈
        existentialBinderSequence spec.source :=
    g2nnfEqRetentiveAntecedentLineage_exBinders
      hLineage occurrence.boundVar hAmbientBinder
  obtain ⟨i, sourceBody, scope, hAllocation⟩ :=
    skolemAllocation_exists_of_exBinder spec hSourceBinder
  obtain ⟨sourceAddress, hSite, hAddress, hFormula⟩ :=
    skolem_site_lookup spec i
  have hScope :
      spec.skolemScope i = scope := by
    simp [SkolemSpec.skolemScope, hAllocation]
  have hScopeNodup : scope.Nodup := by
    rw [← hScope]
    exact skolemScope_nodup spec i
  refine ⟨i, ?_, ?_⟩
  · refine
      ⟨hRelevant, hLineage, sourceAddress, sourceBody, scope,
        ?_, hAddress, ?_, hAllocation, occurrence.hSelected,
        hScope, hScopeNodup⟩
    · simpa [hAllocation] using hSite
    · simpa [hAllocation] using hFormula
  · intro j hBinding
    rcases hBinding with
      ⟨_hOtherRelevant, _hOtherLineage,
        otherAddress, otherBody, otherScope, hOtherSite,
        hOtherAddress, hOtherFormula,
        hOtherAllocation, hOtherSelected,
        hOtherScope, hOtherScopeNodup⟩
    exact
      skolemAllocation_index_unique_of_binder spec
        hOtherAllocation hAllocation

/-- The computable data component of the allocation selected by a source
existential binder.  `findIdx` supplies the `Nat`; the membership proof is
used only for the `Fin` bound and never as a Prop-to-Type choice oracle. -/
def skolemAllocationIndexOfBinder
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
theorem skolemAllocationIndexOfBinder_eq_of_allocation
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
theorem g2nnfRetentiveOccurrence_sourceBinder
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
theorem g2nnfEqRetentiveOccurrence_sourceBinder
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

end LCS.Herbrand.SHGTheorem.Herbrand
end
