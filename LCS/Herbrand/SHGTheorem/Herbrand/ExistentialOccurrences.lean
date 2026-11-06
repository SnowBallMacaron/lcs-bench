import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality

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

/-- A structural address distinguishes equal subformula syntax at
different positions. Quantifier bodies use one common step because the
constructor kind is recovered from the formula at the preceding
address. -/
inductive FormulaOccurrenceAddressStep : Type where
  | connectiveLeft
  | connectiveRight
  | quantifierBody
  deriving DecidableEq

abbrev FormulaOccurrenceAddress := List FormulaOccurrenceAddressStep

/-- Look up the exact formula occurrence selected by an address. -/
def formulaAtOccurrenceAddress {L : Language} :
    FormulaN L → FormulaOccurrenceAddress → Option (FormulaN L)
  | A, [] => some A
  | .conj A _, .connectiveLeft :: rest =>
    formulaAtOccurrenceAddress A rest
  | .conj _ B, .connectiveRight :: rest =>
    formulaAtOccurrenceAddress B rest
  | .disj A _, .connectiveLeft :: rest =>
    formulaAtOccurrenceAddress A rest
  | .disj _ B, .connectiveRight :: rest =>
    formulaAtOccurrenceAddress B rest
  | .all _ A, .quantifierBody :: rest =>
    formulaAtOccurrenceAddress A rest
  | .ex _ A, .quantifierBody :: rest =>
    formulaAtOccurrenceAddress A rest
  | _, _ => none

/-- Exact source addresses of existential occurrences, in the same
preorder and with the same multiplicity as
`SkolemSpec.allocations`. -/
def existentialOccurrenceAddresses {L : Language} :
    FormulaN L → List FormulaOccurrenceAddress
  | .conj A B =>
    (existentialOccurrenceAddresses A).map
        (FormulaOccurrenceAddressStep.connectiveLeft :: ·) ++
      (existentialOccurrenceAddresses B).map
        (FormulaOccurrenceAddressStep.connectiveRight :: ·)
  | .disj A B =>
    (existentialOccurrenceAddresses A).map
        (FormulaOccurrenceAddressStep.connectiveLeft :: ·) ++
      (existentialOccurrenceAddresses B).map
        (FormulaOccurrenceAddressStep.connectiveRight :: ·)
  | .all _ A =>
    (existentialOccurrenceAddresses A).map
      (FormulaOccurrenceAddressStep.quantifierBody :: ·)
  | .ex _ A =>
    [] :: (existentialOccurrenceAddresses A).map
      (FormulaOccurrenceAddressStep.quantifierBody :: ·)
  | _ => []

/-- Pair each exact existential occurrence address with the descriptor
payload generated at that same preorder position.  This is deliberately
structural rather than a `zip`: the two projections below certify that
address and descriptor traversal stay synchronized. -/
def existentialSitesAux {L : Language} :
    FormulaN L → List Nat →
      List
        (FormulaOccurrenceAddress ×
          (FormulaN L × List Nat))
  | .conj A B, scope =>
      (existentialSitesAux A scope).map
          (fun site =>
            (FormulaOccurrenceAddressStep.connectiveLeft ::
              site.1, site.2)) ++
        (existentialSitesAux B scope).map
          (fun site =>
            (FormulaOccurrenceAddressStep.connectiveRight ::
              site.1, site.2))
  | .disj A B, scope =>
      (existentialSitesAux A scope).map
          (fun site =>
            (FormulaOccurrenceAddressStep.connectiveLeft ::
              site.1, site.2)) ++
        (existentialSitesAux B scope).map
          (fun site =>
            (FormulaOccurrenceAddressStep.connectiveRight ::
              site.1, site.2))
  | .all x A, scope =>
      (existentialSitesAux A (scope ++ [x])).map
        (fun site =>
          (FormulaOccurrenceAddressStep.quantifierBody ::
            site.1, site.2))
  | .ex x A, scope =>
      ([], (FormulaN.ex x A, scope)) ::
        (existentialSitesAux A scope).map
          (fun site =>
          (FormulaOccurrenceAddressStep.quantifierBody ::
              site.1, site.2))
  | _, _ => []

private theorem map_fst_map_siteAddressPrefix
    {α : Type} (step : FormulaOccurrenceAddressStep)
    (sites : List (FormulaOccurrenceAddress × α)) :
    (sites.map
        (fun site => (step :: site.1, site.2))).map Prod.fst =
      (sites.map Prod.fst).map (step :: ·) := by
  induction sites with
  | nil => rfl
  | cons site sites ih =>
      simp only [List.map_cons, Prod.fst]
      rw [ih]

/-- Erasing descriptor payloads from the paired site traversal recovers
the exact occurrence-address traversal, including multiplicity. -/
private theorem existentialSitesAux_addresses {L : Language}
    (A : FormulaN L) (scope : List Nat) :
    (existentialSitesAux A scope).map Prod.fst =
      existentialOccurrenceAddresses A := by
  induction A generalizing scope with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg _ _ => rfl
  | conj A B ihA ihB =>
      simp only [existentialSitesAux,
        existentialOccurrenceAddresses, List.map_append]
      rw [map_fst_map_siteAddressPrefix,
        map_fst_map_siteAddressPrefix]
      rw [ihA scope, ihB scope]
  | disj A B ihA ihB =>
      simp only [existentialSitesAux,
        existentialOccurrenceAddresses, List.map_append]
      rw [map_fst_map_siteAddressPrefix,
        map_fst_map_siteAddressPrefix]
      rw [ihA scope, ihB scope]
  | impl _ _ _ _ => rfl
  | all x A ih =>
      simp only [existentialSitesAux,
        existentialOccurrenceAddresses]
      rw [map_fst_map_siteAddressPrefix]
      rw [ih (scope ++ [x])]
  | ex x A ih =>
      simp only [existentialSitesAux,
        existentialOccurrenceAddresses, List.map_cons, Prod.fst]
      rw [map_fst_map_siteAddressPrefix]
      rw [ih scope]

/-- Erasing occurrence addresses from the paired site traversal recovers
the exact descriptor traversal, including scope and multiplicity. -/
private theorem existentialSitesAux_descriptors {L : Language}
    (A : FormulaN L) (scope : List Nat) :
    (existentialSitesAux A scope).map Prod.snd =
      existentialDescriptorsAux A scope := by
  induction A generalizing scope with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg _ _ => rfl
  | conj A B ihA ihB =>
      have hA := ihA scope
      have hB := ihB scope
      unfold existentialDescriptorsAux at hA hB
      simp [existentialSitesAux, existentialDescriptorsAux,
        universalScopeAux, List.map_map, Function.comp_def,
        hA, hB]
  | disj A B ihA ihB =>
      have hA := ihA scope
      have hB := ihB scope
      unfold existentialDescriptorsAux at hA hB
      simp [existentialSitesAux, existentialDescriptorsAux,
        universalScopeAux, List.map_map, Function.comp_def,
        hA, hB]
  | impl _ _ _ _ => rfl
  | all x A ih =>
      have hA := ih (scope ++ [x])
      unfold existentialDescriptorsAux at hA
      simp [existentialSitesAux, existentialDescriptorsAux,
        universalScopeAux, List.map_map, Function.comp_def, hA]
  | ex x A ih =>
      have hA := ih scope
      unfold existentialDescriptorsAux at hA
      simp [existentialSitesAux, existentialDescriptorsAux,
        universalScopeAux, List.map_map, Function.comp_def, hA]

private theorem existentialSitesAux_length {L : Language}
    (A : FormulaN L) (scope : List Nat) :
    (existentialSitesAux A scope).length =
      (existentialDescriptorsAux A scope).length := by
  calc
    (existentialSitesAux A scope).length =
        ((existentialSitesAux A scope).map Prod.snd).length := by
          rw [List.length_map]
    _ = (existentialDescriptorsAux A scope).length := by
          rw [existentialSitesAux_descriptors]

/-- Every paired site's address looks up the formula payload stored in
that site. -/
private theorem existentialSitesAux_formulaAt {L : Language}
    (A : FormulaN L) (scope : List Nat)
    (site :
      FormulaOccurrenceAddress × (FormulaN L × List Nat))
    (hSite : site ∈ existentialSitesAux A scope) :
    formulaAtOccurrenceAddress A site.1 =
      some site.2.1 := by
  induction A generalizing scope site with
  | predN _ _ =>
      simp [existentialSitesAux] at hSite
  | eq_ _ _ _ =>
      simp [existentialSitesAux] at hSite
  | neg _ _ =>
      simp [existentialSitesAux] at hSite
  | conj A B ihA ihB =>
      simp only [existentialSitesAux, List.mem_append,
        List.mem_map] at hSite
      rcases hSite with hSite | hSite
      · rcases hSite with
          ⟨⟨address, ⟨formula, capturedScope⟩⟩,
            hInner, rfl⟩
        exact ihA scope _ hInner
      · rcases hSite with
          ⟨⟨address, ⟨formula, capturedScope⟩⟩,
            hInner, rfl⟩
        exact ihB scope _ hInner
  | disj A B ihA ihB =>
      simp only [existentialSitesAux, List.mem_append,
        List.mem_map] at hSite
      rcases hSite with hSite | hSite
      · rcases hSite with
          ⟨⟨address, ⟨formula, capturedScope⟩⟩,
            hInner, rfl⟩
        exact ihA scope _ hInner
      · rcases hSite with
          ⟨⟨address, ⟨formula, capturedScope⟩⟩,
            hInner, rfl⟩
        exact ihB scope _ hInner
  | impl _ _ _ _ =>
      simp [existentialSitesAux] at hSite
  | all x A ih =>
      simp only [existentialSitesAux, List.mem_map] at hSite
      rcases hSite with
        ⟨⟨address, ⟨formula, capturedScope⟩⟩,
          hInner, rfl⟩
      exact ih (scope ++ [x]) _ hInner
  | ex x A ih =>
      simp only [existentialSitesAux, List.mem_cons,
        List.mem_map] at hSite
      rcases hSite with rfl | hSite
      · rfl
      · rcases hSite with
          ⟨⟨address, ⟨formula, capturedScope⟩⟩,
            hInner, rfl⟩
        exact ih scope _ hInner

def skolemOccurrenceAddress? {L : Language} (spec : SkolemSpec L)
    (i : Fin spec.n) : Option FormulaOccurrenceAddress :=
  (existentialOccurrenceAddresses spec.source)[i.val]?

/-- Every allocation index looks up one synchronized source site.  Its
address, descriptor payload, and formula lookup therefore refer to the
same existential occurrence rather than merely equal syntax. -/
theorem skolem_site_lookup {L : Language}
    (spec : SkolemSpec L) (i : Fin spec.n) :
    ∃ address,
      (existentialSitesAux spec.source [])[i.val]? =
          some (address, spec.allocation i) ∧
        skolemOccurrenceAddress? spec i = some address ∧
        formulaAtOccurrenceAddress spec.source address =
          some (spec.allocation i).1 := by
  let sites := existentialSitesAux spec.source []
  have hSitesLength : sites.length = spec.n := by
    calc
      sites.length =
          (existentialDescriptorsAux spec.source []).length :=
        existentialSitesAux_length spec.source []
      _ = spec.n := by
        rfl
  have hiSites : i.val < sites.length := by
    rw [hSitesLength]
    exact i.isLt
  let address := (sites[i.val]'hiSites).1
  let descriptor := (sites[i.val]'hiSites).2
  have hSiteLookup :
      sites[i.val]? = some (address, descriptor) := by
    apply List.getElem?_eq_some_iff.mpr
    exact ⟨hiSites, rfl⟩
  have hDescriptorLookup :
      (existentialDescriptorsAux spec.source [])[i.val]? =
        some descriptor := by
    rw [← existentialSitesAux_descriptors]
    simp [sites, hSiteLookup]
  have hAllocationLookup :
      (existentialDescriptorsAux spec.source [])[i.val]? =
        some (spec.allocation i) := by
    apply List.getElem?_eq_some_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa [SkolemSpec.n, SkolemSpec.allocations,
        existentialDescriptors] using i.isLt
    · simp [SkolemSpec.allocation, SkolemSpec.allocations,
        existentialDescriptors]
      rfl
  have hDescriptor : descriptor = spec.allocation i :=
    Option.some.inj
      (hDescriptorLookup.symm.trans hAllocationLookup)
  have hAddressLookup :
      (existentialOccurrenceAddresses spec.source)[i.val]? =
        some address := by
    rw [← existentialSitesAux_addresses spec.source []]
    simp [sites, hSiteLookup]
  have hSiteMem :
      (address, descriptor) ∈
        existentialSitesAux spec.source [] :=
    List.mem_of_getElem? (by
      simpa [sites] using hSiteLookup)
  have hFormula :=
    existentialSitesAux_formulaAt spec.source []
      (address, descriptor) hSiteMem
  rw [hDescriptor] at hFormula
  exact
    ⟨address,
      by simpa [sites, hDescriptor] using hSiteLookup,
      by simpa [skolemOccurrenceAddress?] using hAddressLookup,
      hFormula⟩

/-- Existential binders in the same constructor preorder used by the
descriptor traversal.  Negation and implication are leaves here for the
same reason they are leaves in `universalScopeAux`; a `SkolemSpec` source
is NNF. -/
def existentialBinderSequence {L : Language} :
    FormulaN L → List Nat
  | .conj A B =>
      existentialBinderSequence A ++ existentialBinderSequence B
  | .disj A B =>
      existentialBinderSequence A ++ existentialBinderSequence B
  | .all _ A => existentialBinderSequence A
  | .ex x A => x :: existentialBinderSequence A
  | _ => []

def existentialDescriptorBinder {L : Language}
    (descriptor : FormulaN L × List Nat) : Nat :=
  match descriptor.1 with
  | .ex x _ => x
  | _ => 0

/-- Descriptor erasure to binder indices agrees with the structural
existential-binder sequence. -/
theorem existentialDescriptorsAux_binders {L : Language}
    (A : FormulaN L) (scope : List Nat) :
    (existentialDescriptorsAux A scope).map
        existentialDescriptorBinder =
      existentialBinderSequence A := by
  induction A generalizing scope with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg _ _ => rfl
  | conj A B ihA ihB =>
      have hA := ihA scope
      have hB := ihB scope
      unfold existentialDescriptorsAux at hA hB
      simp [existentialDescriptorsAux, universalScopeAux,
        existentialBinderSequence, existentialDescriptorBinder,
        hA, hB]
  | disj A B ihA ihB =>
      have hA := ihA scope
      have hB := ihB scope
      unfold existentialDescriptorsAux at hA hB
      simp [existentialDescriptorsAux, universalScopeAux,
        existentialBinderSequence, existentialDescriptorBinder,
        hA, hB]
  | impl _ _ _ _ => rfl
  | all x A ih =>
      have hA := ih (scope ++ [x])
      unfold existentialDescriptorsAux at hA
      simp [existentialDescriptorsAux, universalScopeAux,
        existentialBinderSequence, existentialDescriptorBinder, hA]
  | ex x A ih =>
      have hA := ih scope
      unfold existentialDescriptorsAux at hA
      simp [existentialDescriptorsAux, universalScopeAux,
        existentialBinderSequence, existentialDescriptorBinder, hA]

/-- Every descriptor cell is headed by an existential constructor; the
fallback branch of `existentialDescriptorBinder` is therefore unreachable
on allocation data. -/
private theorem existentialDescriptor_isExistential {L : Language}
    (A : FormulaN L) (scope : List Nat)
    (descriptor : FormulaN L × List Nat)
    (hDescriptor :
      descriptor ∈ existentialDescriptorsAux A scope) :
    ∃ x B, descriptor.1 = FormulaN.ex x B := by
  unfold existentialDescriptorsAux at hDescriptor
  obtain ⟨pair, _hPairMem, hPair⟩ :=
    List.mem_filterMap.mp hDescriptor
  rcases pair with ⟨formula, capturedScope⟩
  cases formula with
  | predN _ _ => simp at hPair
  | eq_ _ _ _ => simp at hPair
  | neg _ => simp at hPair
  | conj _ _ => simp at hPair
  | disj _ _ => simp at hPair
  | impl _ _ => simp at hPair
  | all _ _ => simp at hPair
  | ex x B =>
      have hEq :
          (FormulaN.ex x B, capturedScope) = descriptor :=
        Option.some.inj hPair
      exact ⟨x, B, by rw [← hEq]⟩

/-- Every existential binder recorded by the descriptor traversal is a
bound variable of the ambient formula. -/
private theorem existentialBinderSequence_mem_formulaBVN
    {L : Language} (A : FormulaN L) {x : Nat}
    (hx : x ∈ existentialBinderSequence A) :
    x ∈ formulaBVN A := by
  induction A with
  | predN _ _ =>
      simp [existentialBinderSequence] at hx
  | eq_ _ _ _ =>
      simp [existentialBinderSequence] at hx
  | neg _ _ =>
      simp [existentialBinderSequence] at hx
  | conj A B ihA ihB =>
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inl (ihA hx)
      · exact Or.inr (ihB hx)
  | disj A B ihA ihB =>
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inl (ihA hx)
      · exact Or.inr (ihB hx)
  | impl _ _ _ _ =>
      simp [existentialBinderSequence] at hx
  | all y A ih =>
      exact Or.inl (ih hx)
  | ex y A ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr rfl
      · exact Or.inl (ih hx)

/-- Distinct quantifier bindings make the ordered existential-binder
sequence duplicate-free. -/
theorem existentialBinderSequence_nodup {L : Language}
    (A : FormulaN L) (hDistinct : distinctQuantifierBindings A) :
    (existentialBinderSequence A).Nodup := by
  induction A with
  | predN _ _ => exact List.nodup_nil
  | eq_ _ _ _ => exact List.nodup_nil
  | neg A ih =>
      exact List.nodup_nil
  | conj A B ihA ihB =>
      rw [existentialBinderSequence, List.nodup_append]
      refine
        ⟨ihA hDistinct.1, ihB hDistinct.2.1, ?_⟩
      intro x hx y hy hxy
      subst y
      exact hDistinct.2.2 x
        ⟨existentialBinderSequence_mem_formulaBVN A hx,
          existentialBinderSequence_mem_formulaBVN B hy⟩
  | disj A B ihA ihB =>
      rw [existentialBinderSequence, List.nodup_append]
      refine
        ⟨ihA hDistinct.1, ihB hDistinct.2.1, ?_⟩
      intro x hx y hy hxy
      subst y
      exact hDistinct.2.2 x
        ⟨existentialBinderSequence_mem_formulaBVN A hx,
          existentialBinderSequence_mem_formulaBVN B hy⟩
  | impl A B ihA ihB =>
      exact List.nodup_nil
  | all y A ih =>
      exact ih hDistinct.1
  | ex y A ih =>
      rw [existentialBinderSequence, List.nodup_cons]
      refine ⟨?_, ih hDistinct.1⟩
      intro hy
      exact hDistinct.2
        (existentialBinderSequence_mem_formulaBVN A hy)

/-- Substitution changes terms only and therefore preserves the ordered
existential-binder sequence exactly. -/
private theorem existentialBinderSequence_formulaSubstN
    {L : Language} (A : FormulaN L) (t : Term L) (x : Nat) :
    existentialBinderSequence (formulaSubstN A t x) =
      existentialBinderSequence A := by
  induction A with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg _ _ => rfl
  | conj A B ihA ihB =>
      simp [formulaSubstN, existentialBinderSequence, ihA, ihB]
  | disj A B ihA ihB =>
      simp [formulaSubstN, existentialBinderSequence, ihA, ihB]
  | impl _ _ _ _ => rfl
  | all y A ih =>
      simp only [formulaSubstN]
      split <;> simp [existentialBinderSequence, ih]
  | ex y A ih =>
      simp only [formulaSubstN]
      split <;> simp [existentialBinderSequence, ih]

/-- Existential binders of a selected maximal occurrence already occur in
the ambient formula. -/
private theorem maxQuantifierOccurrence_selected_exBinders_subset
    {L : Language} {A : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A) :
    ∀ x, x ∈ existentialBinderSequence occurrence.selected →
      x ∈ existentialBinderSequence A := by
  induction occurrence with
  | all _ _ =>
      intro x hx
      exact hx
  | ex _ _ =>
      intro x hx
      exact hx
  | conjLeft occurrence B ih =>
      intro x hx
      exact List.mem_append.mpr (Or.inl (ih x hx))
  | conjRight A occurrence ih =>
      intro x hx
      exact List.mem_append.mpr (Or.inr (ih x hx))
  | disjLeft occurrence B ih =>
      intro x hx
      exact List.mem_append.mpr (Or.inl (ih x hx))
  | disjRight A occurrence ih =>
      intro x hx
      exact List.mem_append.mpr (Or.inr (ih x hx))

/-- A selected maximal existential contributes its binder to the ambient
existential-binder sequence. -/
theorem maxQuantifierOccurrence_exBinder_mem
    {L : Language} {A B : FormulaN L} {x : Nat}
    (occurrence : MaxQuantifierOccurrence A)
    (hSelected :
      occurrence.selected = FormulaN.ex x B) :
    x ∈ existentialBinderSequence A := by
  apply maxQuantifierOccurrence_selected_exBinders_subset
    occurrence x
  rw [hSelected]
  exact List.mem_cons_self

/-- Exact selected replacement can only retain existential binders from
the ambient formula or introduce binders from the supplied replacement. -/
private theorem maxQuantifierOccurrence_replace_exBinders_subset
    {L : Language} {A : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A)
    (replacement : FormulaN L) :
    ∀ x,
      x ∈ existentialBinderSequence
          (occurrence.replace replacement) →
        x ∈ existentialBinderSequence A ∨
          x ∈ existentialBinderSequence replacement := by
  induction occurrence with
  | all _ _ =>
      intro x hx
      exact Or.inr hx
  | ex _ _ =>
      intro x hx
      exact Or.inr hx
  | conjLeft occurrence B ih =>
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases ih x hx with hx | hx
        · exact Or.inl
            (List.mem_append.mpr (Or.inl hx))
        · exact Or.inr hx
      · exact Or.inl
          (List.mem_append.mpr (Or.inr hx))
  | conjRight A occurrence ih =>
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inl
          (List.mem_append.mpr (Or.inl hx))
      · rcases ih x hx with hx | hx
        · exact Or.inl
            (List.mem_append.mpr (Or.inr hx))
        · exact Or.inr hx
  | disjLeft occurrence B ih =>
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases ih x hx with hx | hx
        · exact Or.inl
            (List.mem_append.mpr (Or.inl hx))
        · exact Or.inr hx
      · exact Or.inl
          (List.mem_append.mpr (Or.inr hx))
  | disjRight A occurrence ih =>
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inl
          (List.mem_append.mpr (Or.inl hx))
      · rcases ih x hx with hx | hx
        · exact Or.inl
            (List.mem_append.mpr (Or.inr hx))
        · exact Or.inr hx

theorem maxQuantifierOccurrence_replace_allSub_exBinders
    {L : Language} {A B : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A)
    (x : Nat) (t : Term L)
    (hSelected :
      occurrence.selected = FormulaN.all x B) :
    ∀ y,
      y ∈ existentialBinderSequence
          (occurrence.replace (formulaSubstN B t x)) →
        y ∈ existentialBinderSequence A := by
  intro y hy
  rcases
      maxQuantifierOccurrence_replace_exBinders_subset occurrence
        (formulaSubstN B t x) y hy with
    hy | hy
  · exact hy
  · rw [existentialBinderSequence_formulaSubstN] at hy
    apply maxQuantifierOccurrence_selected_exBinders_subset
      occurrence y
    rw [hSelected]
    exact hy

theorem maxQuantifierOccurrence_replace_exSub_exBinders
    {L : Language} {A B : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A)
    (x : Nat) (t : Term L)
    (hSelected :
      occurrence.selected = FormulaN.ex x B) :
    ∀ y,
      y ∈ existentialBinderSequence
          (occurrence.replace (formulaSubstN B t x)) →
        y ∈ existentialBinderSequence A := by
  intro y hy
  rcases
      maxQuantifierOccurrence_replace_exBinders_subset occurrence
        (formulaSubstN B t x) y hy with
    hy | hy
  · exact hy
  · rw [existentialBinderSequence_formulaSubstN] at hy
    apply maxQuantifierOccurrence_selected_exBinders_subset
      occurrence y
    rw [hSelected]
    exact List.mem_cons.mpr (Or.inr hy)

/-- Every source existential binder names one computed allocation. -/
theorem skolemAllocation_exists_of_exBinder {L : Language}
    (spec : SkolemSpec L) {x : Nat}
    (hx : x ∈ existentialBinderSequence spec.source) :
    ∃ (i : Fin spec.n) (sourceBody : FormulaN L)
        (scope : List Nat),
      spec.allocation i =
        (FormulaN.ex x sourceBody, scope) := by
  have hxDescriptors :
      x ∈
        (existentialDescriptorsAux spec.source []).map
          existentialDescriptorBinder := by
    rw [existentialDescriptorsAux_binders]
    exact hx
  rcases List.mem_map.mp hxDescriptors with
    ⟨descriptor, hDescriptor, hBinder⟩
  obtain ⟨y, sourceBody, hFormula⟩ :=
    existentialDescriptor_isExistential
      spec.source [] descriptor hDescriptor
  rcases descriptor with ⟨formula, scope⟩
  simp only [Prod.fst] at hFormula
  have hyx : y = x := by
    rw [hFormula] at hBinder
    simpa [existentialDescriptorBinder] using hBinder
  subst y
  subst formula
  obtain ⟨k, hk, hGet⟩ :=
    List.mem_iff_getElem.mp hDescriptor
  let i : Fin spec.n :=
    ⟨k, by
      simpa [SkolemSpec.n, SkolemSpec.allocations,
        existentialDescriptors] using hk⟩
  refine ⟨i, sourceBody, scope, ?_⟩
  exact hGet

/-- Under rectification's distinct-binding half, an existential binder
determines its allocation index uniquely. -/
theorem skolemAllocation_index_unique_of_binder
    {L : Language} (spec : SkolemSpec L)
    {i j : Fin spec.n} {x : Nat}
    {bodyI bodyJ : FormulaN L} {scopeI scopeJ : List Nat}
    (hi :
      spec.allocation i = (FormulaN.ex x bodyI, scopeI))
    (hj :
      spec.allocation j = (FormulaN.ex x bodyJ, scopeJ)) :
    i = j := by
  have hNodup :
      (spec.allocations.map
        existentialDescriptorBinder).Nodup := by
    rw [SkolemSpec.allocations, existentialDescriptors,
      existentialDescriptorsAux_binders]
    exact existentialBinderSequence_nodup
      spec.source spec.hRect.2
  have hiLt :
      i.val <
        (spec.allocations.map
          existentialDescriptorBinder).length := by
    simpa [SkolemSpec.n] using i.isLt
  have hjLt :
      j.val <
        (spec.allocations.map
          existentialDescriptorBinder).length := by
    simpa [SkolemSpec.n] using j.isLt
  have hiValue :
      (spec.allocations.map
        existentialDescriptorBinder)[i.val] = x := by
    simp only [List.getElem_map]
    change
      existentialDescriptorBinder (spec.allocation i) = x
    rw [hi]
    rfl
  have hjValue :
      (spec.allocations.map
        existentialDescriptorBinder)[j.val] = x := by
    simp only [List.getElem_map]
    change
      existentialDescriptorBinder (spec.allocation j) = x
    rw [hj]
    rfl
  apply Fin.ext
  by_cases hEq : i.val = j.val
  · exact hEq
  · rcases Nat.lt_or_gt_of_ne hEq with hij | hji
    · exact False.elim
        ((List.pairwise_iff_getElem.mp hNodup
          i.val j.val hiLt hjLt hij)
          (hiValue.trans hjValue.symm))
    · exact False.elim
        ((List.pairwise_iff_getElem.mp hNodup
          j.val i.val hjLt hiLt hji)
          (hjValue.trans hiValue.symm))

/-- Every scope emitted from a distinct-binding formula is duplicate-free,
provided the incoming scope is duplicate-free and names no binder in the
current formula. -/
private theorem existentialScopesAux_all_nodup {L : Language}
    (A : FormulaN L) (scope : List Nat)
    (hScope : scope.Nodup)
    (hOutside :
      ∀ x, x ∈ scope → x ∉ formulaBVN A)
    (hDistinct : distinctQuantifierBindings A) :
    ∀ capturedScope,
      capturedScope ∈ existentialScopesAux A scope →
        capturedScope.Nodup := by
  induction A generalizing scope with
  | predN _ _ =>
      intro capturedScope hCaptured
      simp [existentialScopesAux] at hCaptured
  | eq_ _ _ _ =>
      intro capturedScope hCaptured
      simp [existentialScopesAux] at hCaptured
  | neg _ _ =>
      intro capturedScope hCaptured
      simp [existentialScopesAux] at hCaptured
  | conj A B ihA ihB =>
      intro capturedScope hCaptured
      rcases List.mem_append.mp hCaptured with
        hCaptured | hCaptured
      · apply ihA scope hScope _ hDistinct.1
          capturedScope hCaptured
        intro x hx hxA
        exact hOutside x hx (Or.inl hxA)
      · apply ihB scope hScope _ hDistinct.2.1
          capturedScope hCaptured
        intro x hx hxB
        exact hOutside x hx (Or.inr hxB)
  | disj A B ihA ihB =>
      intro capturedScope hCaptured
      rcases List.mem_append.mp hCaptured with
        hCaptured | hCaptured
      · apply ihA scope hScope _ hDistinct.1
          capturedScope hCaptured
        intro x hx hxA
        exact hOutside x hx (Or.inl hxA)
      · apply ihB scope hScope _ hDistinct.2.1
          capturedScope hCaptured
        intro x hx hxB
        exact hOutside x hx (Or.inr hxB)
  | impl _ _ _ _ =>
      intro capturedScope hCaptured
      simp [existentialScopesAux] at hCaptured
  | all x A ih =>
      apply ih (scope ++ [x])
      · rw [List.nodup_append]
        refine ⟨hScope, by simp, ?_⟩
        intro y hy z hz hyz
        have hzEq : z = x := List.mem_singleton.mp hz
        subst z
        subst y
        exact hOutside x hy (Or.inr rfl)
      · intro y hy hyA
        rcases List.mem_append.mp hy with hy | hy
        · exact hOutside y hy (Or.inl hyA)
        · have hyEq : y = x := List.mem_singleton.mp hy
          subst y
          exact hDistinct.2 hyA
      · exact hDistinct.1
  | ex x A ih =>
      intro capturedScope hCaptured
      rcases List.mem_cons.mp hCaptured with
        rfl | hCaptured
      · exact hScope
      · apply ih scope hScope _ hDistinct.1
          capturedScope hCaptured
        intro y hy hyA
        exact hOutside y hy (Or.inl hyA)

/-- Every computed Skolem scope is duplicate-free. -/
theorem skolemScope_nodup {L : Language}
    (spec : SkolemSpec L) (i : Fin spec.n) :
    (spec.skolemScope i).Nodup := by
  have hAllocationMem :
      spec.allocation i ∈ spec.allocations :=
    List.get_mem spec.allocations i
  have hScopeMem :
      spec.skolemScope i ∈
        spec.allocations.map Prod.snd := by
    apply List.mem_map.mpr
    exact ⟨spec.allocation i, hAllocationMem, rfl⟩
  rw [SkolemSpec.allocations, existentialDescriptors,
    existentialDescriptorsAux_scopes] at hScopeMem
  exact
    existentialScopesAux_all_nodup spec.source []
      List.nodup_nil
      (by
        intro x hx
        simp at hx)
      spec.hRect.2
      (spec.skolemScope i) hScopeMem

end LCS.Herbrand.SHGTheorem.Herbrand
end
