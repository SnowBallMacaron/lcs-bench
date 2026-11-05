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

/-- Rectification evidence for a singleton-to-singleton G2 sequent. -/
theorem allRectified_singletons {L : Language}
    [DecidableEq (FormulaN L)] {A B : FormulaN L}
    (hA : isRectified A) (hB : isRectified B) :
    AllRectified
      (({A} : LCS.Finset (FormulaN L)),
       ({B} : LCS.Finset (FormulaN L))) := by
  constructor
  · intro F hF
    have hFA : F = A := (LCS.Finset.mem_singleton F A).mp hF
    subst F
    exact hA
  · intro F hF
    have hFB : F = B := (LCS.Finset.mem_singleton F B).mp hF
    subst F
    exact hB

/-- The project-local finite-set singleton is extensionally the result of
inserting its element into the empty finite set. -/
theorem finset_insert_empty_eq_singleton {L : Language}
    [DecidableEq (FormulaN L)] (A : FormulaN L) :
    LCS.Finset.insert A (LCS.Finset.empty :
      LCS.Finset (FormulaN L)) =
      LCS.Finset.singleton A := by
  apply LCS.Finset.ext
  intro F
  rw [LCS.Finset.mem_insert, LCS.Finset.mem_singleton]
  constructor
  · rintro (rfl | hEmpty)
    · rfl
    · exact (LCS.Finset.not_mem_empty hEmpty).elim
  · exact Or.inl

-- ===================================================================
-- Lemma 7.6.1 (companion def): implSequent
-- ===================================================================

/-- Lemma 7.6.1 (companion def): Constructs the sequent D -> K and L
encoding the provability statement "D implies (K and L)". The
antecedent contains D and the succedent contains the conjunction
K and L. This is used to state the conclusion of the c-instance
combination lemma. -/
def implSequent {L : Language}
    (D : FormulaN L) (KL : FormulaN L) : Sequent L :=
  Sequent.mk [D] [KL]

-- ===================================================================
-- Lemma 7.6.2 (companion def): negSequent
-- ===================================================================

/-- Lemma 7.6.2 (companion def): Constructs the sequent encoding
provability of not C. Represented as the sequent C -> (empty
succedent), so that provability of this sequent corresponds to
provability of not C. Alternatively: if C -> is provable, then
not C is a consequence. -/
def negSequent {L : Language}
    (C : FormulaN L) : Sequent L :=
  Sequent.mk [C] []

-- ===================================================================
-- Lemma 7.6.2 (companion def): listConj
-- ===================================================================

/-- Lemma 7.6.2 (companion def): Constructs the conjunction
`C₁ ∧ C₂ ∧ ... ∧ Cₘ` from a structurally nonempty list, represented
by its head and tail. A singleton returns its head; longer inputs
build a right-associated conjunction. Requiring a head avoids an
equality-dependent sentinel for the vacuous conjunction. -/
def listConj {L : Language} :
    FormulaN L → List (FormulaN L) → FormulaN L
  | head, [] => head
  | head, next :: rest => .conj head (listConj next rest)

-- ===================================================================
-- Lemma 7.6.2 (companion def): eigenvariableToSkolemSubst
-- ===================================================================

/-- Lemma 7.6.2 (helper): A partial eigenvariable map into the exact
Skolem extension computed by `spec`. A `none` cell means that the
variable is not an eigenvariable introduced by an `∃:left` occurrence
and must therefore remain unchanged. -/
abbrev EigenvarSkolemMap {L : Language} (spec : SkolemSpec L) :=
  Nat → Option (Term spec.language)

/-- Lemma 7.6.2 (helper): Lift a base-language term into the exact
Skolem extension. Every old constant and function symbol is embedded through
`Sum.inl`; this helper never manufactures or selects a Skolem head. -/
def liftEigenvarBaseTerm {L : Language} (spec : SkolemSpec L) :
    Term L → Term spec.language
  | .var x => .var x
  | .const c => .const (Sum.inl c)
  | .func f ts =>
    .func (Sum.inl f) (fun i => liftEigenvarBaseTerm spec (ts i))

/-- Lemma 7.6.2 (helper): Mask one bound variable from a partial
eigenvariable map. This is used under both quantifier constructors so
only free occurrences are replaced. -/
def maskEigenvarSkolemMap {L : Language} (spec : SkolemSpec L)
    (x : Nat) (eigenvarMap : EigenvarSkolemMap spec) :
    EigenvarSkolemMap spec :=
  fun y => if y = x then none else eigenvarMap y

/-- Lemma 7.6.2 (helper): Apply a heterogeneous partial eigenvariable
map to a base-language term. A mapped variable is replaced by its
exact extended-language term; an unmapped variable is the identity.
Base constants and every base function symbol are lifted through
`Sum.inl`. -/
def applyEigenvarSubstTerm {L : Language} (spec : SkolemSpec L)
    (eigenvarMap : EigenvarSkolemMap spec) :
    Term L → Term spec.language
  | .var x =>
    match eigenvarMap x with
    | some t => t
    | none => .var x
  | .const c => .const (Sum.inl c)
  | .func f ts =>
    .func (Sum.inl f)
      (fun i => applyEigenvarSubstTerm spec eigenvarMap (ts i))

/-- Lemma 7.6.2 (helper): Apply an eigenvariable map inside a term that
already belongs to the exact Skolem extension. Unlike
`applyEigenvarSubstTerm`, function heads are preserved rather than
lifted. This is the composition step used to turn a later raw range
such as `f₁(y₀)` into the final range `f₁(f₀)`. -/
def applyEigenvarSkolemMapTerm {L : Language} (spec : SkolemSpec L)
    (eigenvarMap : EigenvarSkolemMap spec) :
    Term spec.language → Term spec.language
  | .var x =>
    match eigenvarMap x with
    | some t => t
    | none => .var x
  | .const c => .const c
  | .func f ts =>
    .func f (fun i => applyEigenvarSkolemMapTerm spec eigenvarMap (ts i))

@[simp]
theorem applyEigenvarSkolemMapTerm_empty {L : Language}
    (spec : SkolemSpec L) (t : Term spec.language) :
    applyEigenvarSkolemMapTerm spec (fun _ => none) t = t := by
  induction t with
  | var => rfl
  | const => rfl
  | func f ts ih =>
    simp only [applyEigenvarSkolemMapTerm]
    congr
    funext i
    exact ih i

/-- Lemma 7.6.2 (helper): Capture-safety of one term occurrence under
the binders currently surrounding it. Only variables actually mapped
at that occurrence constrain the map range; a mapped term must avoid
every surrounding binder. -/
def EigenvarSkolemMapFreeForTermAt {L : Language}
    (spec : SkolemSpec L) (eigenvarMap : EigenvarSkolemMap spec) :
    List Nat → Term L → Prop
  | bound, .var y =>
    ∀ t, eigenvarMap y = some t →
      ∀ x, x ∈ bound → ¬ Membership.mem (termFV t) x
  | _, .const _ => True
  | bound, .func _ ts =>
    ∀ i, EigenvarSkolemMapFreeForTermAt spec eigenvarMap bound (ts i)

/-- Lemma 7.6.2 (helper): Formula-relative free-for condition for the
heterogeneous eigenvariable map. Entering a quantifier both masks its
bound variable from the map domain and records that binder as forbidden
in the range of every substitution that remains active below it. -/
def EigenvarSkolemMapFreeForFormulaAt {L : Language}
    (spec : SkolemSpec L) :
    List Nat → EigenvarSkolemMap spec → FormulaN L → Prop
  | bound, eigenvarMap, .predN _ ts =>
    ∀ i, EigenvarSkolemMapFreeForTermAt spec eigenvarMap bound (ts i)
  | bound, eigenvarMap, .eq_ _ t1 t2 =>
    EigenvarSkolemMapFreeForTermAt spec eigenvarMap bound t1 ∧
      EigenvarSkolemMapFreeForTermAt spec eigenvarMap bound t2
  | bound, eigenvarMap, .conj A B =>
    EigenvarSkolemMapFreeForFormulaAt spec bound eigenvarMap A ∧
      EigenvarSkolemMapFreeForFormulaAt spec bound eigenvarMap B
  | bound, eigenvarMap, .disj A B =>
    EigenvarSkolemMapFreeForFormulaAt spec bound eigenvarMap A ∧
      EigenvarSkolemMapFreeForFormulaAt spec bound eigenvarMap B
  | bound, eigenvarMap, .impl A B =>
    EigenvarSkolemMapFreeForFormulaAt spec bound eigenvarMap A ∧
      EigenvarSkolemMapFreeForFormulaAt spec bound eigenvarMap B
  | bound, eigenvarMap, .neg A =>
    EigenvarSkolemMapFreeForFormulaAt spec bound eigenvarMap A
  | bound, eigenvarMap, .all x A =>
    EigenvarSkolemMapFreeForFormulaAt spec (x :: bound)
      (maskEigenvarSkolemMap spec x eigenvarMap) A
  | bound, eigenvarMap, .ex x A =>
    EigenvarSkolemMapFreeForFormulaAt spec (x :: bound)
      (maskEigenvarSkolemMap spec x eigenvarMap) A

def EigenvarSkolemMapFreeForFormula {L : Language}
    (spec : SkolemSpec L) (eigenvarMap : EigenvarSkolemMap spec)
    (A : FormulaN L) : Prop :=
  EigenvarSkolemMapFreeForFormulaAt spec [] eigenvarMap A

def EigenvarSkolemMapFreeForFinset {L : Language}
    (spec : SkolemSpec L) (eigenvarMap : EigenvarSkolemMap spec)
    (S : LCS.Finset (FormulaN L)) : Prop :=
  ∀ A, A ∈ S → EigenvarSkolemMapFreeForFormula spec eigenvarMap A

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
namespace EigenvarSubstitution

/-- Stable computational core of formula application. Public callers
should use `applyEigenvarSubstFormula`, whose formula-relative free-for
guard records the required capture-safety evidence. -/
def applyFormulaRaw {L : Language}
    (spec : SkolemSpec L) (eigenvarMap : EigenvarSkolemMap spec) :
    FormulaN L → FormulaN spec.language
  | .predN P ts =>
    .predN P (fun i =>
      applyEigenvarSubstTerm spec eigenvarMap (ts i))
  | .eq_ h t1 t2 =>
    .eq_ h (applyEigenvarSubstTerm spec eigenvarMap t1)
      (applyEigenvarSubstTerm spec eigenvarMap t2)
  | .conj A B =>
    .conj (applyFormulaRaw spec eigenvarMap A)
      (applyFormulaRaw spec eigenvarMap B)
  | .disj A B =>
    .disj (applyFormulaRaw spec eigenvarMap A)
      (applyFormulaRaw spec eigenvarMap B)
  | .impl A B =>
    .impl (applyFormulaRaw spec eigenvarMap A)
      (applyFormulaRaw spec eigenvarMap B)
  | .neg A =>
    .neg (applyFormulaRaw spec eigenvarMap A)
  | .all x A =>
    .all x
      (applyFormulaRaw spec
        (maskEigenvarSkolemMap spec x eigenvarMap) A)
  | .ex x A =>
    .ex x
      (applyFormulaRaw spec
        (maskEigenvarSkolemMap spec x eigenvarMap) A)

end EigenvarSubstitution
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

/-- Lemma 7.6.2 (helper): Applies the map only after the caller proves
that no mapped term can be captured by a binder in this formula. -/
def applyEigenvarSubstFormula {L : Language} (spec : SkolemSpec L)
    (eigenvarMap : EigenvarSkolemMap spec) (A : FormulaN L)
    (_hFreeFor :
      EigenvarSkolemMapFreeForFormula spec eigenvarMap A) :
    FormulaN spec.language :=
  EigenvarSubstitution.applyFormulaRaw spec eigenvarMap A

/-- Lemma 7.6.2 (helper): Applies an eigenvariable-to-Skolem
substitution to every formula in a base-language `LCS.Finset`,
producing an `LCS.Finset` over the exact Skolem extension. -/
noncomputable def applyEigenvarSubstFinset {L : Language}
    (spec : SkolemSpec L) [DecidableEq (FormulaN spec.language)]
    (eigenvarMap : EigenvarSkolemMap spec)
    (S : LCS.Finset (FormulaN L))
    (_hFreeFor : EigenvarSkolemMapFreeForFinset spec eigenvarMap S) :
    LCS.Finset (FormulaN spec.language) :=
  LCS.Finset.image
    (EigenvarSubstitution.applyFormulaRaw spec eigenvarMap) S

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

/-- Convert the connective-only address stored by an exact maximal
quantifier occurrence into the formula-occurrence address vocabulary used by
the Skolem-lineage layer. -/
def maxQuantifierOccurrenceFormulaAddress {L : Language}
    {A : FormulaN L} :
    MaxQuantifierOccurrence A → FormulaOccurrenceAddress
  | .all _ _ => []
  | .ex _ _ => []
  | .conjLeft occurrence _ =>
      .connectiveLeft ::
        maxQuantifierOccurrenceFormulaAddress occurrence
  | .conjRight _ occurrence =>
      .connectiveRight ::
        maxQuantifierOccurrenceFormulaAddress occurrence
  | .disjLeft occurrence _ =>
      .connectiveLeft ::
        maxQuantifierOccurrenceFormulaAddress occurrence
  | .disjRight _ occurrence =>
      .connectiveRight ::
        maxQuantifierOccurrenceFormulaAddress occurrence

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

/-- Looking up the converted address recovers the formula selected by the
exact maximal occurrence. -/
theorem formulaAt_maxQuantifierOccurrenceFormulaAddress {L : Language}
    {A : FormulaN L} (occurrence : MaxQuantifierOccurrence A) :
    formulaAtOccurrenceAddress A
        (maxQuantifierOccurrenceFormulaAddress occurrence) =
      some occurrence.selected := by
  induction occurrence <;>
    simp_all [maxQuantifierOccurrenceFormulaAddress,
      formulaAtOccurrenceAddress, MaxQuantifierOccurrence.selected]

/-- An address is the selected occurrence itself or descends below it. -/
def addressAtOrBelowExactMaxQuantifier {L : Language}
    {A : FormulaN L} (occurrence : MaxQuantifierOccurrence A)
    (address : FormulaOccurrenceAddress) : Prop :=
  ∃ suffix,
    address =
      maxQuantifierOccurrenceFormulaAddress occurrence ++ suffix

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

/-- Addresses of maximal quantified subformulae. This is the
position-sensitive counterpart of `maxQuantSubformulae`; unlike the
set-valued API it retains multiplicity. -/
def maxQuantifierOccurrenceAddresses {L : Language} :
    FormulaN L → List FormulaOccurrenceAddress
  | .conj A B =>
    (maxQuantifierOccurrenceAddresses A).map
        (FormulaOccurrenceAddressStep.connectiveLeft :: ·) ++
      (maxQuantifierOccurrenceAddresses B).map
        (FormulaOccurrenceAddressStep.connectiveRight :: ·)
  | .disj A B =>
    (maxQuantifierOccurrenceAddresses A).map
        (FormulaOccurrenceAddressStep.connectiveLeft :: ·) ++
      (maxQuantifierOccurrenceAddresses B).map
        (FormulaOccurrenceAddressStep.connectiveRight :: ·)
  | .all _ _ => [[]]
  | .ex _ _ => [[]]
  | _ => []

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

structure FormulaOccurrenceFocus (L : Language) where
  ambient : FormulaN L
  address : FormulaOccurrenceAddress

inductive G2nnfPremiseChoice : Type where
  | only
  | left
  | right
  deriving DecidableEq

/-- The formula inserted on the left by a rule conclusion, if the
rule has a left principal. A context occurrence with the same syntax
is deliberately not treated as distinct: `Finset` has only one such
cell, so the rule must be followed as principal. -/
def g2nnfLeftPrincipal? {L : Language} :
    G2nnfRuleCore L → Option (FormulaN L)
  | .axiomPosId A _ _ _ => some A
  | .axiomNegId A _ _ _ => some (.neg A)
  | .axiomCompRight _ _ _ _ => none
  | .axiomCompLeft A _ _ _ => some A
  | .weakLeft A _ _ => some A
  | .weakRight _ _ _ => none
  | .conjLeft1 A B _ _ => some (.conj A B)
  | .conjLeft2 A B _ _ => some (.conj A B)
  | .conjRight _ _ _ _ => none
  | .disjLeft A B _ _ => some (.disj A B)
  | .disjRight1 _ _ _ _ => none
  | .disjRight2 _ _ _ _ => none
  | .cut _ _ _ _ _ => none
  | .allSubLeft A _ _ _ _ _ _ _ => some A
  | .allSubRight _ _ _ _ _ _ _ _ => none
  | .exSubLeft A _ _ _ _ _ _ _ => some A
  | .exSubRight _ _ _ _ _ _ _ _ => none

/-- Formula inserted into the selected premise antecedent, if any. -/
def g2nnfLeftPremiseInserted? {L : Language}
    [DecidableEq (FormulaN L)]
    (rule : G2nnfRuleCore L) (choice : G2nnfPremiseChoice) :
    Option (FormulaN L) :=
  match rule, choice with
  | .conjLeft1 A _ _ _, .only => some A
  | .conjLeft2 _ B _ _, .only => some B
  | .disjLeft A _ _ _, .left => some A
  | .disjLeft _ B _ _, .right => some B
  | .cut A _ _ _ _, .right => some A
  | .allSubLeft _ occurrence x B t _ _ _, .only =>
    some (occurrence.replace (formulaSubstN B t x))
  | .exSubLeft _ occurrence x B y _ _ _, .only =>
    some (occurrence.replace (formulaSubstN B (.var y) x))
  | _, _ => none

/-- Antecedent side context of the selected premise. A right cut premise
uses its own stored frame; the left premise retains the first frame. -/
def g2nnfLeftPremiseContext {L : Language} (rule : G2nnfRuleCore L)
    (choice : G2nnfPremiseChoice) : LCS.Finset (FormulaN L) :=
  match rule, choice with
  | .cut _ Lambda _ _ _, .right => Lambda
  | _, _ => (g2nnfRuleSideContexts rule).1

def focusIsStrictContext {L : Language}
    [DecidableEq (FormulaN L)] (rule : G2nnfRuleCore L)
    (choice : G2nnfPremiseChoice)
    (focus : FormulaOccurrenceFocus L) : Prop :=
  focus.ambient ∈ g2nnfLeftPremiseContext rule choice ∧
    (match g2nnfLeftPrincipal? rule with
     | some principal => focus.ambient ≠ principal
     | none => True) ∧
    match g2nnfLeftPremiseInserted? rule choice with
    | some inserted => focus.ambient ≠ inserted
    | none => True

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
namespace FormulaOccurrenceLineage

/-- Prepend the optional substitution contributed by one rule step to
the substitutions already replayed along the remainder of a path. -/
def prependSubstitution {L : Language}
    (head : Option (Nat × Term L)) (tail : List (Nat × Term L)) :
    List (Nat × Term L) :=
  match head with
  | some substitution => substitution :: tail
  | none => tail

end FormulaOccurrenceLineage
end LCS.Herbrand.SHGTheorem.Herbrand
end

