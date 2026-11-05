import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Equality
import Attach
import LCS.Herbrand.NNFHauptsatz.Part1.ProofsStamp

section
namespace LCS.Herbrand.NNFHauptsatz
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality

/-- The standing §7.4 invariant that every formula in a sequent is
rectified.  It is kept separate from the raw rule carrier and enforced at
each rule application through `G2nnfRule.SideConditions`. -/
@[blueprint "chap7__definition_7_4_3"]
def AllRectified {L : Language}
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) : Prop :=
  (∀ A, A ∈ seq.1 → isRectified A) ∧
  (∀ A, A ∈ seq.2 → isRectified A)

end LCS.Herbrand.NNFHauptsatz
end

section
namespace LCS.Herbrand.NNFHauptsatz
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality
namespace AllRectified

-- ATTACH-BLOCKER: private declaration
/-- The local set identity needed by the structural quantifier-free
rectification proof. -/
private theorem empty_union_empty :
    (∅ : Set Nat) ∪ ∅ = ∅ := by
  funext x
  apply propext
  constructor
  · rintro (hx | hx) <;> exact hx
  · exact False.elim

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Quantifier-free normalized formulae are rectified because they contain no
bound-variable occurrences. -/
theorem formulaBVN_eq_empty_of_isQuantifierFree {L : Language}
    (A : FormulaN L) (hQF : isQuantifierFree A) :
    formulaBVN A = ∅ := by
  induction A with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg A ih =>
      simpa [isQuantifierFree, formulaBVN] using ih hQF
  | conj A B ihA ihB =>
      rcases hQF with ⟨hA, hB⟩
      rw [formulaBVN, ihA hA, ihB hB]
      exact empty_union_empty
  | disj A B ihA ihB =>
      rcases hQF with ⟨hA, hB⟩
      rw [formulaBVN, ihA hA, ihB hB]
      exact empty_union_empty
  | impl A B ihA ihB =>
      rcases hQF with ⟨hA, hB⟩
      rw [formulaBVN, ihA hA, ihB hB]
      exact empty_union_empty
  | all _ _ => exact hQF.elim
  | ex _ _ => exact hQF.elim

-- retained: used by LCS.Herbrand.NNFHauptsatz.Equality.Part1, LCS.Herbrand.NNFHauptsatz.Part2.Proofs, LCS.Herbrand.NNFHauptsatz.Theorem.Example, LCS.Herbrand.NNFHauptsatz.Theorem.Midsequents, LCS.Herbrand.SHGTheorem.Herbrand.Alteration, LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination, LCS.Herbrand.SHGTheorem.Herbrand.CanonicalMapRegression, LCS.Herbrand.SHGTheorem.Herbrand.LowerConstruction, LCS.Herbrand.SHGTheorem.Herbrand.NestedMapRegression
theorem distinctQuantifierBindings_of_isQuantifierFree {L : Language}
    (A : FormulaN L) (hQF : isQuantifierFree A) :
    distinctQuantifierBindings A := by
  induction A with
  | predN _ _ => trivial
  | eq_ _ _ _ => trivial
  | neg A ih =>
      exact ih hQF
  | conj A B ihA ihB =>
      rcases hQF with ⟨hA, hB⟩
      refine ⟨ihA hA, ihB hB, ?_⟩
      rw [formulaBVN_eq_empty_of_isQuantifierFree A hA]
      intro x hx
      exact False.elim hx.1
  | disj A B ihA ihB =>
      rcases hQF with ⟨hA, hB⟩
      refine ⟨ihA hA, ihB hB, ?_⟩
      rw [formulaBVN_eq_empty_of_isQuantifierFree A hA]
      intro x hx
      exact False.elim hx.1
  | impl A B ihA ihB =>
      rcases hQF with ⟨hA, hB⟩
      refine ⟨ihA hA, ihB hB, ?_⟩
      rw [formulaBVN_eq_empty_of_isQuantifierFree A hA]
      intro x hx
      exact False.elim hx.1
  | all _ _ => exact hQF.elim
  | ex _ _ => exact hQF.elim

-- retained: used by LCS.Herbrand.NNFHauptsatz.Equality.Part1, LCS.Herbrand.NNFHauptsatz.Part2.Proofs, LCS.Herbrand.NNFHauptsatz.Theorem.Example, LCS.Herbrand.NNFHauptsatz.Theorem.Midsequents, LCS.Herbrand.SHGTheorem.Herbrand.Alteration, LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination, LCS.Herbrand.SHGTheorem.Herbrand.CanonicalMapRegression, LCS.Herbrand.SHGTheorem.Herbrand.LowerConstruction, LCS.Herbrand.SHGTheorem.Herbrand.NestedMapRegression
theorem isRectified_of_isQuantifierFree {L : Language}
    (A : FormulaN L) (hQF : isQuantifierFree A) :
    isRectified A := by
  refine ⟨?_, distinctQuantifierBindings_of_isQuantifierFree A hQF⟩
  intro x hx
  have hBV := formulaBVN_eq_empty_of_isQuantifierFree A hQF
  rw [hBV] at hx
  exact hx.2

-- retained: used by LCS.Herbrand.NNFHauptsatz.Equality.Part1, LCS.Herbrand.NNFHauptsatz.Theorem.Purity.Proofs, LCS.Herbrand.SHGTheorem.Herbrand.Alteration
theorem isQuantifierFree_of_isAtomic {L : Language}
    (A : FormulaN L) (hAtomic : A.isAtomic = true) :
    isQuantifierFree A := by
  cases A <;> simp_all [FormulaN.isAtomic, isQuantifierFree]

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example, LCS.Herbrand.SHGTheorem.Herbrand.Alteration
theorem isRectified_of_isAtomic {L : Language}
    (A : FormulaN L) (hAtomic : A.isAtomic = true) :
    isRectified A :=
  isRectified_of_isQuantifierFree A
    (isQuantifierFree_of_isAtomic A hAtomic)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem empty {L : Language} :
    AllRectified
      ((LCS.Finset.empty, LCS.Finset.empty) :
        LCS.Finset (FormulaN L) ×
          LCS.Finset (FormulaN L)) := by
  constructor
  · intro A hA
    exact (LCS.Finset.not_mem_empty hA).elim
  · intro A hA
    exact (LCS.Finset.not_mem_empty hA).elim

-- retained: used by LCS.Herbrand.NNFHauptsatz.Equality.Part1, LCS.Herbrand.NNFHauptsatz.Theorem.Purity.Proofs
theorem of_allQuantifierFree {L : Language}
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L))
    (hQF :
      (∀ A, A ∈ seq.1 → isQuantifierFree A) ∧
      (∀ A, A ∈ seq.2 → isQuantifierFree A)) :
    AllRectified seq :=
  ⟨fun A hA => isRectified_of_isQuantifierFree A (hQF.1 A hA),
   fun A hA => isRectified_of_isQuantifierFree A (hQF.2 A hA)⟩

-- retained: used by LCS.CutElim.Hauptsatz, LCS.CutElim.Hauptsatz.CutElimination.Freshening, LCS.CutElim.Hauptsatz.CutElimination.Substitution, LCS.CutElim.Hauptsatz.CutElimination.Trees, LCS.CutElim.Hauptsatz.Equality.Part1.Proofs, LCS.CutElim.Hauptsatz.Equality.Part2.Proofs, LCS.Herbrand.NNFHauptsatz.Theorem.Example, LCS.Herbrand.SHGTheorem.Herbrand.Alteration, LCS.Herbrand.SHGTheorem.Herbrand.CanonicalMapRegression, LCS.Herbrand.SHGTheorem.Herbrand.NestedMapRegression
theorem insert_left {L : Language} [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)} {A : FormulaN L}
    (hA : isRectified A) (hSeq : AllRectified (Γ, Δ)) :
    AllRectified (LCS.Finset.insert A Γ, Δ) := by
  refine ⟨?_, hSeq.2⟩
  intro F hF
  rcases LCS.Finset.mem_insert.mp hF with rfl | hF
  · exact hA
  · exact hSeq.1 F hF

-- retained: used by LCS.CutElim.Hauptsatz, LCS.CutElim.Hauptsatz.CutElimination.Freshening, LCS.CutElim.Hauptsatz.CutElimination.Substitution, LCS.CutElim.Hauptsatz.CutElimination.Trees, LCS.CutElim.Hauptsatz.Equality.Part1.Proofs, LCS.CutElim.Hauptsatz.Equality.Part2.Proofs, LCS.Herbrand.NNFHauptsatz.Equality.Part1, LCS.Herbrand.NNFHauptsatz.Theorem.Example, LCS.Herbrand.NNFHauptsatz.Theorem.Paths, LCS.Herbrand.SHGTheorem.Herbrand.Alteration, LCS.Herbrand.SHGTheorem.Herbrand.CanonicalMapRegression
theorem insert_right {L : Language} [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)} {A : FormulaN L}
    (hA : isRectified A) (hSeq : AllRectified (Γ, Δ)) :
    AllRectified (Γ, LCS.Finset.insert A Δ) := by
  refine ⟨hSeq.1, ?_⟩
  intro F hF
  rcases LCS.Finset.mem_insert.mp hF with rfl | hF
  · exact hA
  · exact hSeq.2 F hF

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example, LCS.Herbrand.SHGTheorem.Herbrand.Alteration
theorem of_insert_left {L : Language} [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)} {A : FormulaN L}
    (hSeq : AllRectified (LCS.Finset.insert A Γ, Δ)) :
    AllRectified (Γ, Δ) :=
  ⟨fun F hF => hSeq.1 F (LCS.Finset.mem_insert.mpr (Or.inr hF)),
   hSeq.2⟩

-- retained: used by LCS.Herbrand.NNFHauptsatz.Equality.Part1, LCS.Herbrand.NNFHauptsatz.Theorem.Example, LCS.Herbrand.NNFHauptsatz.Theorem.Paths, LCS.Herbrand.SHGTheorem.Herbrand.Alteration
theorem of_insert_right {L : Language} [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)} {A : FormulaN L}
    (hSeq : AllRectified (Γ, LCS.Finset.insert A Δ)) :
    AllRectified (Γ, Δ) :=
  ⟨hSeq.1,
   fun F hF => hSeq.2 F (LCS.Finset.mem_insert.mpr (Or.inr hF))⟩

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Rectification is preserved when independently rectified sequent
contexts are combined. -/
theorem union {L : Language} [DecidableEq (FormulaN L)]
    {Γ₁ Γ₂ Δ₁ Δ₂ : LCS.Finset (FormulaN L)}
    (h₁ : AllRectified (Γ₁, Δ₁))
    (h₂ : AllRectified (Γ₂, Δ₂)) :
    AllRectified
      (LCS.Finset.union Γ₁ Γ₂, LCS.Finset.union Δ₁ Δ₂) := by
  constructor
  · intro F hF
    rcases LCS.Finset.mem_union.mp hF with hF | hF
    · exact h₁.1 F hF
    · exact h₂.1 F hF
  · intro F hF
    rcases LCS.Finset.mem_union.mp hF with hF | hF
    · exact h₁.2 F hF
    · exact h₂.2 F hF

end AllRectified
end LCS.Herbrand.NNFHauptsatz
end

section
namespace LCS.Herbrand.NNFHauptsatz
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality

/-- Definition 7.4.1 (required helper): singleton-`Set` constructor used to build the mathematical set QF(A) of maximal quantified subformulae in `maxQuantSubformulae`. Sequent containers in G2nnf use `LCS.Finset` instead (Definition 7.4.3). -/
@[blueprint "chap7__definition_7_4_1"]
def sng {L : Language} (A : FormulaN L) : Set (FormulaN L) := fun x => x = A

-- ===================================================================
-- Occurrence-sensitive maximal quantified subformula infrastructure
-- ===================================================================

/-- One branch step in the address of a maximal quantified occurrence.
Unlike formula equality, an address distinguishes the two copies in `Q ∧ Q`
or `Q ∨ Q`. -/
@[blueprint "chap7__definition_7_4_1"]
inductive MaxQuantifierOccurrenceStep : Type where
  | left
  | right
  deriving DecidableEq

/-- A branch address through conjunctions and disjunctions. -/
@[blueprint "chap7__definition_7_4_1"]
abbrev MaxQuantifierOccurrenceAddress :=
  List MaxQuantifierOccurrenceStep

/-- A proof-relevant path to one maximal quantified occurrence of `A`.
The path stops as soon as it reaches `∀` or `∃`; consequently it cannot select
a quantifier nested below another quantifier.  The four branch constructors
retain occurrence identity even when the selected formula has the same syntax
in both branches. -/
@[blueprint "chap7__definition_7_4_1"]
inductive MaxQuantifierOccurrence {L : Language} :
    FormulaN L → Type where
  | all (x : Nat) (B : FormulaN L) :
      MaxQuantifierOccurrence (.all x B)
  | ex (x : Nat) (B : FormulaN L) :
      MaxQuantifierOccurrence (.ex x B)
  | conjLeft {A : FormulaN L}
      (occurrence : MaxQuantifierOccurrence A) (B : FormulaN L) :
      MaxQuantifierOccurrence (.conj A B)
  | conjRight (A : FormulaN L) {B : FormulaN L}
      (occurrence : MaxQuantifierOccurrence B) :
      MaxQuantifierOccurrence (.conj A B)
  | disjLeft {A : FormulaN L}
      (occurrence : MaxQuantifierOccurrence A) (B : FormulaN L) :
      MaxQuantifierOccurrence (.disj A B)
  | disjRight (A : FormulaN L) {B : FormulaN L}
      (occurrence : MaxQuantifierOccurrence B) :
      MaxQuantifierOccurrence (.disj A B)

end LCS.Herbrand.NNFHauptsatz
end

section
namespace LCS.Herbrand.NNFHauptsatz
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality
namespace MaxQuantifierOccurrence

/-- The maximal quantified formula selected by an occurrence path. -/
@[blueprint "chap7__definition_7_4_1"]
def selected {L : Language} {A : FormulaN L} :
    MaxQuantifierOccurrence A → FormulaN L
  | .all x B => .all x B
  | .ex x B => .ex x B
  | .conjLeft occurrence _ => occurrence.selected
  | .conjRight _ occurrence => occurrence.selected
  | .disjLeft occurrence _ => occurrence.selected
  | .disjRight _ occurrence => occurrence.selected

/-- The left/right address encoded by an occurrence path. -/
@[blueprint "chap7__definition_7_4_1"]
def address {L : Language} {A : FormulaN L} :
    MaxQuantifierOccurrence A → MaxQuantifierOccurrenceAddress
  | .all _ _ => []
  | .ex _ _ => []
  | .conjLeft occurrence _ => .left :: occurrence.address
  | .conjRight _ occurrence => .right :: occurrence.address
  | .disjLeft occurrence _ => .left :: occurrence.address
  | .disjRight _ occurrence => .right :: occurrence.address

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination, LCS.Herbrand.SHGTheorem.Herbrand.ClosedSubstitution, LCS.Herbrand.SHGTheorem.Herbrand.ScopeAndPurity
/-- Look up a formula at a branch address.  Maximal-quantifier addresses never
descend through a quantifier, so only conjunction and disjunction steps are
accepted. -/
def lookup {L : Language} :
    FormulaN L → MaxQuantifierOccurrenceAddress → Option (FormulaN L)
  | A, [] => some A
  | .conj A _, .left :: rest => lookup A rest
  | .conj _ B, .right :: rest => lookup B rest
  | .disj A _, .left :: rest => lookup A rest
  | .disj _ B, .right :: rest => lookup B rest
  | _, _ => none

/-- Replace exactly the selected occurrence and leave every other branch
unchanged.  No formula equality test is needed because the occurrence path
already determines the replacement site. -/
@[blueprint "chap7__definition_7_4_2"]
def replace {L : Language} {A : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A) (replacement : FormulaN L) :
    FormulaN L :=
  match occurrence with
  | .all _ _ => replacement
  | .ex _ _ => replacement
  | .conjLeft inner B => .conj (inner.replace replacement) B
  | .conjRight A inner => .conj A (inner.replace replacement)
  | .disjLeft inner B => .disj (inner.replace replacement) B
  | .disjRight A inner => .disj A (inner.replace replacement)





-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Every selected formula is headed by a quantifier. -/
theorem selected_eq_all_or_ex {L : Language} {A : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A) :
    (∃ x B, occurrence.selected = FormulaN.all x B) ∨
      ∃ x B, occurrence.selected = FormulaN.ex x B := by
  induction occurrence with
  | all x B => exact Or.inl ⟨x, B, rfl⟩
  | ex x B => exact Or.inr ⟨x, B, rfl⟩
  | conjLeft _ _ ih => exact ih
  | conjRight _ _ ih => exact ih
  | disjLeft _ _ ih => exact ih
  | disjRight _ _ ih => exact ih



-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Bound variables of the selected formula already occur bound in the
ambient formula. -/
theorem selected_bv_subset {L : Language} {A : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A) :
    formulaBVN occurrence.selected ⊆ formulaBVN A := by
  induction occurrence with
  | all _ _ =>
      intro v hv
      exact hv
  | ex _ _ =>
      intro v hv
      exact hv
  | conjLeft _ _ ih =>
      intro v hv
      exact Or.inl (ih v hv)
  | conjRight _ _ ih =>
      intro v hv
      exact Or.inr (ih v hv)
  | disjLeft _ _ ih =>
      intro v hv
      exact Or.inl (ih v hv)
  | disjRight _ _ ih =>
      intro v hv
      exact Or.inr (ih v hv)









-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The selected formula occurs at exactly this maximal occurrence in the
ambient formula.  Equality is equality of occurrence witnesses, not merely
formula syntax. -/
def IsUnique {L : Language} {A : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A) : Prop :=
  ∀ other : MaxQuantifierOccurrence A,
    other.selected = occurrence.selected → other = occurrence

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Every maximal quantified occurrence contributes at least its own binder
to the bound variables of the selected formula. -/
theorem selected_has_bound_variable {L : Language} {A : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A) :
    ∃ x, x ∈ formulaBVN occurrence.selected := by
  rcases occurrence.selected_eq_all_or_ex with
    ⟨x, B, hSelected⟩ | ⟨x, B, hSelected⟩
  · refine ⟨x, ?_⟩
    rw [hSelected]
    exact Or.inr rfl
  · refine ⟨x, ?_⟩
    rw [hSelected]
    exact Or.inr rfl

-- retained: used by LCS.Herbrand.NNFHauptsatz.Part2
/-- The §7.4 standing distinct-binding invariant makes the selected maximal
quantifier occurrence syntax-unique. -/
theorem isUnique_of_distinctQuantifierBindings
    {L : Language} {A : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A)
    (hDistinct : distinctQuantifierBindings A) :
    occurrence.IsUnique := by
  induction occurrence with
  | all _ _ =>
      intro other _
      cases other
      rfl
  | ex _ _ =>
      intro other _
      cases other
      rfl
  | conjLeft occurrence B ih =>
      intro other hSelected
      cases other with
      | conjLeft other _ =>
          cases ih hDistinct.1 other hSelected
          rfl
      | conjRight _ other =>
          exfalso
          obtain ⟨x, hxSelected⟩ :=
            occurrence.selected_has_bound_variable
          have hxLeft :=
            occurrence.selected_bv_subset x hxSelected
          have hxOtherSelected :
              x ∈ formulaBVN other.selected := by
            rw [show other.selected = occurrence.selected by
              simpa only [MaxQuantifierOccurrence.selected] using hSelected]
            exact hxSelected
          have hxRight :=
            other.selected_bv_subset x hxOtherSelected
          exact hDistinct.2.2 x ⟨hxLeft, hxRight⟩
  | conjRight A occurrence ih =>
      intro other hSelected
      cases other with
      | conjLeft other _ =>
          exfalso
          obtain ⟨x, hxSelected⟩ :=
            occurrence.selected_has_bound_variable
          have hxRight :=
            occurrence.selected_bv_subset x hxSelected
          have hxOtherSelected :
              x ∈ formulaBVN other.selected := by
            rw [show other.selected = occurrence.selected by
              simpa only [MaxQuantifierOccurrence.selected] using hSelected]
            exact hxSelected
          have hxLeft :=
            other.selected_bv_subset x hxOtherSelected
          exact hDistinct.2.2 x ⟨hxLeft, hxRight⟩
      | conjRight _ other =>
          cases ih hDistinct.2.1 other hSelected
          rfl
  | disjLeft occurrence B ih =>
      intro other hSelected
      cases other with
      | disjLeft other _ =>
          cases ih hDistinct.1 other hSelected
          rfl
      | disjRight _ other =>
          exfalso
          obtain ⟨x, hxSelected⟩ :=
            occurrence.selected_has_bound_variable
          have hxLeft :=
            occurrence.selected_bv_subset x hxSelected
          have hxOtherSelected :
              x ∈ formulaBVN other.selected := by
            rw [show other.selected = occurrence.selected by
              simpa only [MaxQuantifierOccurrence.selected] using hSelected]
            exact hxSelected
          have hxRight :=
            other.selected_bv_subset x hxOtherSelected
          exact hDistinct.2.2 x ⟨hxLeft, hxRight⟩
  | disjRight A occurrence ih =>
      intro other hSelected
      cases other with
      | disjLeft other _ =>
          exfalso
          obtain ⟨x, hxSelected⟩ :=
            occurrence.selected_has_bound_variable
          have hxRight :=
            occurrence.selected_bv_subset x hxSelected
          have hxOtherSelected :
              x ∈ formulaBVN other.selected := by
            rw [show other.selected = occurrence.selected by
              simpa only [MaxQuantifierOccurrence.selected] using hSelected]
            exact hxSelected
          have hxLeft :=
            other.selected_bv_subset x hxOtherSelected
          exact hDistinct.2.2 x ⟨hxLeft, hxRight⟩
      | disjRight _ other =>
          cases ih hDistinct.2.1 other hSelected
          rfl



end MaxQuantifierOccurrence
end LCS.Herbrand.NNFHauptsatz
end

section
namespace LCS.Herbrand.NNFHauptsatz
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality

/-- Every formula on either side of a finite sequent is in NNF. -/
@[blueprint "chap7__definition_7_4_3"]
def AllNNF {L : Language}
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) : Prop :=
  (∀ A, A ∈ seq.1 → A.isNNF) ∧ (∀ A, A ∈ seq.2 → A.isNNF)

/-- General rule instances shared by the ordinary and equality systems.
Contexts are data of the instance; cut carries two independent context pairs.
Ordinary axioms are contextual here. `BareAtomicAxiom` selects the bare
instances for the equality-free public calculus. NNF and logical side
conditions are checked at every tree node. -/
@[blueprint "chap7__definition_7_4_4"]
inductive G2nnfRuleCore (L : Language) : Type where
  /-- Contextual positive identity: Gamma, A -> Delta, A for atomic A -/
  | axiomPosId (A : FormulaN L) (hAtom : A.isAtomic)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Contextual negative identity: Gamma, not A -> Delta, not A for atomic A -/
  | axiomNegId (A : FormulaN L) (hAtom : A.isAtomic)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Contextual complementary right: Gamma -> Delta, A, not A for atomic A -/
  | axiomCompRight (A : FormulaN L) (hAtom : A.isAtomic)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Contextual complementary left: Gamma, A, not A -> Delta for atomic A -/
  | axiomCompLeft (A : FormulaN L) (hAtom : A.isAtomic)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Weakening left: from Gamma -> Delta infer A, Gamma -> Delta -/
  | weakLeft (A : FormulaN L)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Weakening right: from Gamma -> Delta infer Gamma -> Delta, A -/
  | weakRight (A : FormulaN L)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Conjunction left (variant 1): from A, Gamma -> Delta infer
      A and B, Gamma -> Delta -/
  | conjLeft1 (A B : FormulaN L)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Conjunction left (variant 2): from B, Gamma -> Delta infer
      A and B, Gamma -> Delta -/
  | conjLeft2 (A B : FormulaN L)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Conjunction right: from Gamma -> Delta, A and Gamma -> Delta, B
      infer Gamma -> Delta, A and B -/
  | conjRight (A B : FormulaN L)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Disjunction left: from A, Gamma -> Delta and B, Gamma -> Delta
      infer A or B, Gamma -> Delta -/
  | disjLeft (A B : FormulaN L)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Disjunction right (variant 1): from Gamma -> Delta, A infer
      Gamma -> Delta, A or B -/
  | disjRight1 (A B : FormulaN L)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Disjunction right (variant 2): from Gamma -> Delta, B infer
      Gamma -> Delta, A or B -/
  | disjRight2 (A B : FormulaN L)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Cut rule: from Gamma -> Delta, A and A, Lambda -> Theta infer
      Gamma, Lambda -> Delta, Theta -/
  | cut (A : FormulaN L) (Lambda Theta : LCS.Finset (FormulaN L))
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Forall-subformula left: replace exactly the selected maximal occurrence
      of `forall x B` by `B[t/x]`.  The occurrence and its selected-formula
      equation are constructor data, so duplicate equal formulae remain
      distinct and QF-membership is enforced structurally. -/
  | allSubLeft (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A) (x : Nat)
      (B : FormulaN L) (t : Term L)
      (hSelected : occurrence.selected = FormulaN.all x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Forall-subformula right: replace exactly the selected maximal occurrence
      of `forall x B` by `B[y/x]`; `y` is fresh for the lower sequent. -/
  | allSubRight (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A) (x : Nat)
      (B : FormulaN L) (y : Nat)
      (hSelected : occurrence.selected = FormulaN.all x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Exists-subformula left: replace exactly the selected maximal occurrence
      of `exists x B` by `B[y/x]`; `y` is fresh for the lower sequent. -/
  | exSubLeft (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A) (x : Nat)
      (B : FormulaN L) (y : Nat)
      (hSelected : occurrence.selected = FormulaN.ex x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L
  /-- Exists-subformula right: replace exactly the selected maximal occurrence
      of `exists x B` by `B[t/x]`. -/
  | exSubRight (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A) (x : Nat)
      (B : FormulaN L) (t : Term L)
      (hSelected : occurrence.selected = FormulaN.ex x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L

end LCS.Herbrand.NNFHauptsatz
end

section
namespace LCS.Herbrand.NNFHauptsatz
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality
namespace G2nnfRuleCore

/-- The actual conclusion, including the union of independent cut contexts. -/
@[blueprint "chap7__definition_7_4_4"]
def conclusion {L : Language} [DecidableEq (FormulaN L)] :
    G2nnfRuleCore L →
    LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)
  | .axiomPosId A _ Gamma Delta =>
    (LCS.Finset.insert A Gamma, LCS.Finset.insert A Delta)
  | .axiomNegId A _ Gamma Delta =>
    (LCS.Finset.insert (.neg A) Gamma, LCS.Finset.insert (.neg A) Delta)
  | .axiomCompRight A _ Gamma Delta =>
    (Gamma, LCS.Finset.insert A (LCS.Finset.insert (.neg A) Delta))
  | .axiomCompLeft A _ Gamma Delta =>
    (LCS.Finset.insert A (LCS.Finset.insert (.neg A) Gamma), Delta)
  | .weakLeft A Gamma Delta =>
    (LCS.Finset.insert A Gamma, Delta)
  | .weakRight A Gamma Delta =>
    (Gamma, LCS.Finset.insert A Delta)
  | .conjLeft1 A B Gamma Delta =>
    (LCS.Finset.insert (.conj A B) Gamma, Delta)
  | .conjLeft2 A B Gamma Delta =>
    (LCS.Finset.insert (.conj A B) Gamma, Delta)
  | .conjRight A B Gamma Delta =>
    (Gamma, LCS.Finset.insert (.conj A B) Delta)
  | .disjLeft A B Gamma Delta =>
    (LCS.Finset.insert (.disj A B) Gamma, Delta)
  | .disjRight1 A B Gamma Delta =>
    (Gamma, LCS.Finset.insert (.disj A B) Delta)
  | .disjRight2 A B Gamma Delta =>
    (Gamma, LCS.Finset.insert (.disj A B) Delta)
  | .cut _ Lambda Theta Gamma Delta =>
    (LCS.Finset.union Gamma Lambda, LCS.Finset.union Delta Theta)
  | .allSubLeft A _ _ _ _ _ Gamma Delta =>
    (LCS.Finset.insert A Gamma, Delta)
  | .allSubRight A _ _ _ _ _ Gamma Delta =>
    (Gamma, LCS.Finset.insert A Delta)
  | .exSubLeft A _ _ _ _ _ Gamma Delta =>
    (LCS.Finset.insert A Gamma, Delta)
  | .exSubRight A _ _ _ _ _ Gamma Delta =>
    (Gamma, LCS.Finset.insert A Delta)

/-- The actual premises; quantifier rules replace exactly their stored maximal
occurrence and retain the selected-formula equation. -/
@[blueprint "chap7__definition_7_4_4"]
def premises {L : Language} [DecidableEq (FormulaN L)] :
    G2nnfRuleCore L →
    List (LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L))
  | .axiomPosId _ _ _ _ => []
  | .axiomNegId _ _ _ _ => []
  | .axiomCompRight _ _ _ _ => []
  | .axiomCompLeft _ _ _ _ => []
  | .weakLeft _ Gamma Delta => [(Gamma, Delta)]
  | .weakRight _ Gamma Delta => [(Gamma, Delta)]
  | .conjLeft1 A _ Gamma Delta =>
    [(LCS.Finset.insert A Gamma, Delta)]
  | .conjLeft2 _ B Gamma Delta =>
    [(LCS.Finset.insert B Gamma, Delta)]
  | .conjRight A B Gamma Delta =>
    [(Gamma, LCS.Finset.insert A Delta),
     (Gamma, LCS.Finset.insert B Delta)]
  | .disjLeft A B Gamma Delta =>
    [(LCS.Finset.insert A Gamma, Delta),
     (LCS.Finset.insert B Gamma, Delta)]
  | .disjRight1 A _ Gamma Delta =>
    [(Gamma, LCS.Finset.insert A Delta)]
  | .disjRight2 _ B Gamma Delta =>
    [(Gamma, LCS.Finset.insert B Delta)]
  | .cut A Lambda Theta Gamma Delta =>
    [(Gamma, LCS.Finset.insert A Delta),
     (LCS.Finset.insert A Lambda, Theta)]
  | .allSubLeft _ occurrence x B t _ Gamma Delta =>
    [(LCS.Finset.insert
        (occurrence.replace (formulaSubstN B t x))
        Gamma, Delta)]
  | .allSubRight _ occurrence x B y _ Gamma Delta =>
    [(Gamma,
      LCS.Finset.insert
        (occurrence.replace (formulaSubstN B (.var y) x)) Delta)]
  | .exSubLeft _ occurrence x B y _ Gamma Delta =>
    [(LCS.Finset.insert
        (occurrence.replace (formulaSubstN B (.var y) x)) Gamma, Delta)]
  | .exSubRight _ occurrence x B t _ Gamma Delta =>
    [(Gamma,
      LCS.Finset.insert
        (occurrence.replace (formulaSubstN B t x)) Delta)]

/-- Free-for and eigenvariable freshness at the stored inference contexts. -/
@[blueprint "chap7__definition_7_4_4"]
def LogicalSideConditions {L : Language} :
    G2nnfRuleCore L → Prop
  | .axiomPosId _ _ _ _ => True
  | .axiomNegId _ _ _ _ => True
  | .axiomCompRight _ _ _ _ => True
  | .axiomCompLeft _ _ _ _ => True
  | .weakLeft _ _ _ => True
  | .weakRight _ _ _ => True
  | .conjLeft1 _ _ _ _ => True
  | .conjLeft2 _ _ _ _ => True
  | .conjRight _ _ _ _ => True
  | .disjLeft _ _ _ _ => True
  | .disjRight1 _ _ _ _ => True
  | .disjRight2 _ _ _ _ => True
  | .cut _ _ _ _ _ => True
  | .allSubLeft _ _ x B t _ _ _ =>
    isFreeForN t x B
  | .allSubRight A _ x B y _ Gamma Delta =>
    isFreeForN (Term.var y) x B ∧
    ¬ Membership.mem (formulaFVN A) y ∧
    (∀ F, Membership.mem Gamma F → ¬ Membership.mem (formulaFVN F) y) ∧
    (∀ F, Membership.mem Delta F → ¬ Membership.mem (formulaFVN F) y)
  | .exSubLeft A _ x B y _ Gamma Delta =>
    isFreeForN (Term.var y) x B ∧
    ¬ Membership.mem (formulaFVN A) y ∧
    (∀ F, Membership.mem Gamma F → ¬ Membership.mem (formulaFVN F) y) ∧
    (∀ F, Membership.mem Delta F → ¬ Membership.mem (formulaFVN F) y)
  | .exSubRight _ _ x B t _ _ _ =>
    isFreeForN t x B

/-- Select bare atomic axiom instances; every non-axiom rule is admitted.
The context fields are empty, so an admitted zero-premise rule has exactly
one of the four printed bare conclusions. -/
@[blueprint "chap7__definition_7_4_3"]
def BareAtomicAxiom {L : Language} : G2nnfRuleCore L → Prop
  | .axiomPosId _ _ Gamma Delta | .axiomNegId _ _ Gamma Delta
    | .axiomCompRight _ _ Gamma Delta | .axiomCompLeft _ _ Gamma Delta =>
      Gamma = LCS.Finset.empty ∧ Delta = LCS.Finset.empty
  | _ => True

/-- A legal core inference has NNF premises and conclusion, satisfies the
local quantifier conditions, and retains the standing rectification convention.
NNF is checked on every formula, including cut formulae and weakening formulae. -/
@[blueprint "chap7__definition_7_4_4"]
structure SideConditions {L : Language} [DecidableEq (FormulaN L)]
    (rule : G2nnfRuleCore L) : Prop where
  logical : rule.LogicalSideConditions
  conclusionNNF : AllNNF rule.conclusion
  premisesNNF : ∀ seq ∈ rule.premises, AllNNF seq
  conclusionRectified : AllRectified rule.conclusion

end G2nnfRuleCore
end LCS.Herbrand.NNFHauptsatz
end

section
namespace LCS.Herbrand.NNFHauptsatz
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality

/-- Shared indexed tree recursion for both calculi. Each ordinary inference
requires `admitRule` and the core side conditions. Extra axioms are permitted only
by `extraAxiom`, with explicit NNF and rectification evidence. Open leaves
require `openLeaf` and the same sequent invariants. The default admits arbitrary
NNF rectified open sequents; setting `openLeaf` to False gives proof trees. -/
@[blueprint "chap7__definition_7_4_4"]
inductive G2nnfDeductionTreeCore {L : Language} [DecidableEq (FormulaN L)]
    (admitRule : G2nnfRuleCore L → Prop)
    (extraAxiom : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) → Prop)
    (openLeaf : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) → Prop :=
      fun _ => True) :
    LCS.Finset (FormulaN L) → LCS.Finset (FormulaN L) → Type where
  | leaf (Gamma Delta : LCS.Finset (FormulaN L))
      (hOpen : openLeaf (Gamma, Delta)) (hNNF : AllNNF (Gamma, Delta))
      (hRect : AllRectified (Gamma, Delta)) :
      G2nnfDeductionTreeCore admitRule extraAxiom openLeaf Gamma Delta
  | extraAxiom (Gamma Delta : LCS.Finset (FormulaN L))
      (hExtra : extraAxiom (Gamma, Delta)) (hNNF : AllNNF (Gamma, Delta))
      (hRect : AllRectified (Gamma, Delta)) :
      G2nnfDeductionTreeCore admitRule extraAxiom openLeaf Gamma Delta
  | axiom_ (rule : G2nnfRuleCore L) (hAdmit : admitRule rule)
      (hAxiom : rule.premises.length = 0) (hSC : rule.SideConditions) :
      G2nnfDeductionTreeCore admitRule extraAxiom openLeaf
        rule.conclusion.1 rule.conclusion.2
  | onePremise (rule : G2nnfRuleCore L) (hAdmit : admitRule rule)
      (hPrem : rule.premises.length = 1) (hSC : rule.SideConditions)
      (sub : G2nnfDeductionTreeCore admitRule extraAxiom openLeaf
        (rule.premises[0]'(by omega)).1 (rule.premises[0]'(by omega)).2) :
      G2nnfDeductionTreeCore admitRule extraAxiom openLeaf
        rule.conclusion.1 rule.conclusion.2
  | twoPremise (rule : G2nnfRuleCore L) (hAdmit : admitRule rule)
      (hPrem : rule.premises.length = 2) (hSC : rule.SideConditions)
      (sub1 : G2nnfDeductionTreeCore admitRule extraAxiom openLeaf
        (rule.premises[0]'(by omega)).1 (rule.premises[0]'(by omega)).2)
      (sub2 : G2nnfDeductionTreeCore admitRule extraAxiom openLeaf
        (rule.premises[1]'(by omega)).1 (rule.premises[1]'(by omega)).2) :
      G2nnfDeductionTreeCore admitRule extraAxiom openLeaf
        rule.conclusion.1 rule.conclusion.2

/-- Closed trees use the same recursion as deductions, with open leaves
excluded at every depth. Rule admission and extra axioms remain parameters. -/
@[blueprint "chap7__definition_7_4_4"]
abbrev G2nnfProofTreeCore {L : Language} [DecidableEq (FormulaN L)]
    (admitRule : G2nnfRuleCore L → Prop)
    (extraAxiom : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) → Prop) :=
  G2nnfDeductionTreeCore admitRule extraAxiom (fun _ => False)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Every node of a core tree has an NNF conclusion, including open leaves
and extra axioms. Applying this lemma to any subtree gives the same invariant. -/
theorem G2nnfDeductionTreeCore.allNNF {L : Language} [DecidableEq (FormulaN L)]
    {admitRule : G2nnfRuleCore L → Prop}
    {extraAxiom openLeaf : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) → Prop}
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (tree : G2nnfDeductionTreeCore admitRule extraAxiom openLeaf Gamma Delta) :
    AllNNF (Gamma, Delta) := by
  cases tree with
  | leaf _ _ _ hNNF _ => exact hNNF
  | extraAxiom _ _ _ hNNF _ => exact hNNF
  | axiom_ _ _ _ hSC => exact hSC.conclusionNNF
  | onePremise _ _ _ hSC _ => exact hSC.conclusionNNF
  | twoPremise _ _ _ hSC _ _ => exact hSC.conclusionNNF

-- ===================================================================
-- Definition 7.4.3: G2nnfRule — Inference rules of the system G2nnf
-- ===================================================================

/-- Definition 7.4.3: Rule instances of the equality-free G2nnf calculus.
The shared carrier stores all inference contexts. Ordinary zero-premise
instances are restricted to the four bare atomic schemes; contextual uses
require explicit weakening. Logical and NNF requirements are enforced by
`SideConditions` at every inference. -/
@[blueprint "chap7__definition_7_4_3" (main := true)]
abbrev G2nnfRule (L : Language) (_hL : L.withoutEquality) :=
  {rule : G2nnfRuleCore L // rule.BareAtomicAxiom}

-- ===================================================================
-- Example 7.4.1 (companion type): QPolExPred
-- ===================================================================

/-- Example 7.4.1 (companion type): Predicate symbols for the
quantifier polarity example: P (unary) and Q (unary). -/
@[blueprint "chap7__example_7_4_1"]
inductive QPolExPred : Type where
  | P : QPolExPred
  | Q : QPolExPred

-- ===================================================================
-- Example 7.4.1 (companion type): QPolExConst
-- ===================================================================

/-- Example 7.4.1 (companion type): Constant symbols for the
quantifier polarity example: a and b. -/
@[blueprint "chap7__example_7_4_1"]
inductive QPolExConst : Type where
  | a : QPolExConst
  | b : QPolExConst

-- ===================================================================
-- Example 7.4.1 (companion def): qPolExLang
-- ===================================================================

/-- Example 7.4.1 (companion def): A language with unary predicates
P and Q, constants a and b, no function symbols, and no equality. -/
@[blueprint "chap7__example_7_4_1"]
def qPolExLang : Language where
  hasEquality := false
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := QPolExConst
  predSymbols := QPolExPred
  predArity := fun
    | .P => 1
    | .Q => 1

-- ===================================================================
-- Example 7.4.1: quantifierPolarityExFormula
-- ===================================================================

/-- Example 7.4.1: The formula A = P(a) or not(Q(b) and forall x Q(x)). Demonstrates the quantifier rule polarity problem: the subformula forall x Q(x) is under a negation, so the correct rule to apply is exists-left, not forall-left. Variables: x = 0. -/
@[blueprint "chap7__example_7_4_1"]
def quantifierPolarityExFormula : FormulaN qPolExLang :=
  FormulaN.disj
    (FormulaN.predN QPolExPred.P
      (fun _ => Term.const QPolExConst.a))
    (FormulaN.neg
      (FormulaN.conj
        (FormulaN.predN QPolExPred.Q
          (fun _ => Term.const QPolExConst.b))
        (FormulaN.all 0
          (FormulaN.predN QPolExPred.Q
            (fun _ => Term.var 0)))))

-- ===================================================================
-- Example 7.4.1 (companion def): quantifierPolarityExNNF
-- ===================================================================

/-- Example 7.4.1 (companion def): The logically equivalent NNF form P(a) or (not Q(b) or exists x not Q(x)). In NNF, only atoms are negated, so the quantifier directly indicates the applicable rule without ambiguity from negation parity. Variables: x = 0. -/
@[blueprint "chap7__example_7_4_1"]
def quantifierPolarityExNNF : FormulaN qPolExLang :=
  FormulaN.disj
    (FormulaN.predN QPolExPred.P
      (fun _ => Term.const QPolExConst.a))
    (FormulaN.disj
      (FormulaN.neg
        (FormulaN.predN QPolExPred.Q
          (fun _ => Term.const QPolExConst.b)))
      (FormulaN.ex 0
        (FormulaN.neg
          (FormulaN.predN QPolExPred.Q
            (fun _ => Term.var 0)))))

end LCS.Herbrand.NNFHauptsatz
end

section
namespace LCS.Herbrand.NNFHauptsatz
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality
section QuantifierPolarity
-- ATTACH-BLOCKER: global set_option
set_option backward.isDefEq.respectTransparency false

/-- Quantifier heads, independent of sequent side. -/
@[blueprint "chap7__example_7_4_1"]
inductive PolarityQuantifierHead where
  | universal | existential
  deriving DecidableEq

@[blueprint "chap7__example_7_4_1"]
def PolarityQuantifierHead.dual : PolarityQuantifierHead → PolarityQuantifierHead
  | .universal => .existential
  | .existential => .universal

@[blueprint "chap7__example_7_4_1"]
def PolarityQuantifierHead.formula {L : Language} :
    PolarityQuantifierHead → Nat → FormulaN L → FormulaN L
  | .universal => FormulaN.all
  | .existential => FormulaN.ex

/-- The side of the whole antecedent/succedent formula; normalization does
not move that formula to the other side. -/
@[blueprint "chap7__example_7_4_1"]
inductive PolaritySequentSide where
  | antecedent | succedent
  deriving DecidableEq

/-- The four quantifier inference kinds of Definition 7.4.3. -/
@[blueprint "chap7__example_7_4_1"]
inductive PolarityRuleKind where
  | allLeft | allRight | exLeft | exRight
  deriving DecidableEq

-- ATTACH-BLOCKER: section options: helper requires front context
/-- Constructor-level quantifier kind in the actual Core rule family. -/
def G2nnfRuleCore.quantifierRuleKind {L : Language} :
    G2nnfRuleCore L → Option PolarityRuleKind
  | .allSubLeft .. => some .allLeft
  | .allSubRight .. => some .allRight
  | .exSubLeft .. => some .exLeft
  | .exSubRight .. => some .exRight
  | _ => none

@[blueprint "chap7__example_7_4_1"]
def polarityRuleKind (side : PolaritySequentSide) (head : PolarityQuantifierHead)
    (negative : Bool) : PolarityRuleKind :=
  match side, (if negative then head.dual else head) with
  | .antecedent, .universal => .allLeft
  | .succedent, .universal => .allRight
  | .antecedent, .existential => .exLeft
  | .succedent, .existential => .exRight

/-- A selected quantified occurrence through a propositional context.
The Boolean index is odd negative-context parity: negation and the antecedent
of an implication flip it. Implication is read as its usual negation/disjunction
abbreviation. Paths stop at quantifiers, as required for G2 maximal occurrences.
Distinct branch constructors retain distinct occurrences of equal formulae. -/
@[blueprint "chap7__example_7_4_1"]
inductive QuantifierContextOccurrence {L : Language} :
    FormulaN L → PolarityQuantifierHead → Nat → FormulaN L → Bool → Type where
  | all (x : Nat) (B : FormulaN L) :
      QuantifierContextOccurrence (.all x B) .universal x B false
  | ex (x : Nat) (B : FormulaN L) :
      QuantifierContextOccurrence (.ex x B) .existential x B false
  | neg {A k x B n} (o : QuantifierContextOccurrence A k x B n) :
      QuantifierContextOccurrence (.neg A) k x B (!n)
  | conjLeft {A k x B n} (o : QuantifierContextOccurrence A k x B n) (C : FormulaN L) :
      QuantifierContextOccurrence (.conj A C) k x B n
  | conjRight (C : FormulaN L) {A k x B n} (o : QuantifierContextOccurrence A k x B n) :
      QuantifierContextOccurrence (.conj C A) k x B n
  | disjLeft {A k x B n} (o : QuantifierContextOccurrence A k x B n) (C : FormulaN L) :
      QuantifierContextOccurrence (.disj A C) k x B n
  | disjRight (C : FormulaN L) {A k x B n} (o : QuantifierContextOccurrence A k x B n) :
      QuantifierContextOccurrence (.disj C A) k x B n
  | implLeft {A k x B n} (o : QuantifierContextOccurrence A k x B n) (C : FormulaN L) :
      QuantifierContextOccurrence (.impl A C) k x B (!n)
  | implRight (C : FormulaN L) {A k x B n} (o : QuantifierContextOccurrence A k x B n) :
      QuantifierContextOccurrence (.impl C A) k x B n

/-- The surviving binary branch address after negations are pushed inward.
Negation nodes disappear; implication retains its left/right branch positions. -/
@[blueprint "chap7__example_7_4_1"]
def QuantifierContextOccurrence.nnfAddress {L : Language} {A : FormulaN L}
    {k x B n} : QuantifierContextOccurrence A k x B n → MaxQuantifierOccurrenceAddress
  | .all .. | .ex .. => []
  | .neg o => o.nnfAddress
  | .conjLeft o _ | .disjLeft o _ | .implLeft o _ => .left :: o.nnfAddress
  | .conjRight _ o | .disjRight _ o | .implRight _ o => .right :: o.nnfAddress

-- ATTACH-BLOCKER: section options: helper requires front context
/-- Exact normalized occurrence and selected formula, for either incoming
polarity. The address constraint prevents selecting an unrelated equal subformula. -/
theorem QuantifierContextOccurrence.normalization {L : Language} {A : FormulaN L}
    {k x B n} (o : QuantifierContextOccurrence A k x B n) (positive : Bool) :
    ∃ q : MaxQuantifierOccurrence (FormulaN.toNNFAux positive A),
      q.address = o.nnfAddress ∧
      q.selected = (if positive != n then k else k.dual).formula x
        (FormulaN.toNNFAux (positive != n) B) := by
  induction o generalizing positive with
  | all x B =>
    cases positive
    · exact ⟨.ex x _, rfl, rfl⟩
    · exact ⟨.all x _, rfl, rfl⟩
  | ex x B =>
    cases positive
    · exact ⟨.all x _, rfl, rfl⟩
    · exact ⟨.ex x _, rfl, rfl⟩
  | @neg A k x B n o ih =>
    cases positive <;> cases n
    · exact ih true
    · exact ih true
    · exact ih false
    · exact ih false
  | conjLeft o C ih =>
    cases positive
    · rcases ih false with ⟨q, ha, hs⟩
      exact ⟨.disjLeft q _, congrArg (List.cons MaxQuantifierOccurrenceStep.left) ha, hs⟩
    · rcases ih true with ⟨q, ha, hs⟩
      exact ⟨.conjLeft q _, congrArg (List.cons MaxQuantifierOccurrenceStep.left) ha, hs⟩
  | conjRight C o ih =>
    cases positive
    · rcases ih false with ⟨q, ha, hs⟩
      exact ⟨.disjRight _ q, congrArg (List.cons MaxQuantifierOccurrenceStep.right) ha, hs⟩
    · rcases ih true with ⟨q, ha, hs⟩
      exact ⟨.conjRight _ q, congrArg (List.cons MaxQuantifierOccurrenceStep.right) ha, hs⟩
  | disjLeft o C ih =>
    cases positive
    · rcases ih false with ⟨q, ha, hs⟩
      exact ⟨.conjLeft q _, congrArg (List.cons MaxQuantifierOccurrenceStep.left) ha, hs⟩
    · rcases ih true with ⟨q, ha, hs⟩
      exact ⟨.disjLeft q _, congrArg (List.cons MaxQuantifierOccurrenceStep.left) ha, hs⟩
  | disjRight C o ih =>
    cases positive
    · rcases ih false with ⟨q, ha, hs⟩
      exact ⟨.conjRight _ q, congrArg (List.cons MaxQuantifierOccurrenceStep.right) ha, hs⟩
    · rcases ih true with ⟨q, ha, hs⟩
      exact ⟨.disjRight _ q, congrArg (List.cons MaxQuantifierOccurrenceStep.right) ha, hs⟩
  | @implLeft A k x B n o C ih =>
    cases positive <;> cases n
    · rcases ih true with ⟨q, ha, hs⟩
      exact ⟨.conjLeft q _, congrArg (List.cons MaxQuantifierOccurrenceStep.left) ha, hs⟩
    · rcases ih true with ⟨q, ha, hs⟩
      exact ⟨.conjLeft q _, congrArg (List.cons MaxQuantifierOccurrenceStep.left) ha, hs⟩
    · rcases ih false with ⟨q, ha, hs⟩
      exact ⟨.disjLeft q _, congrArg (List.cons MaxQuantifierOccurrenceStep.left) ha, hs⟩
    · rcases ih false with ⟨q, ha, hs⟩
      exact ⟨.disjLeft q _, congrArg (List.cons MaxQuantifierOccurrenceStep.left) ha, hs⟩
  | implRight C o ih =>
    cases positive
    · rcases ih false with ⟨q, ha, hs⟩
      exact ⟨.conjRight _ q, congrArg (List.cons MaxQuantifierOccurrenceStep.right) ha, hs⟩
    · rcases ih true with ⟨q, ha, hs⟩
      exact ⟨.disjRight _ q, congrArg (List.cons MaxQuantifierOccurrenceStep.right) ha, hs⟩

/-- Read the rule kind directly from the normalized selected quantifier and
its sequent side. Non-quantifier heads have no quantifier rule kind. -/
@[blueprint "chap7__example_7_4_1"]
def normalizedQuantifierRuleKind {L : Language} (side : PolaritySequentSide) :
    FormulaN L → Option PolarityRuleKind
  | .all _ _ => some (match side with | .antecedent => .allLeft | .succedent => .allRight)
  | .ex _ _ => some (match side with | .antecedent => .exLeft | .succedent => .exRight)
  | _ => none

/-- Section 7.4.1 / Example 7.4.1: the exact selected occurrence normalizes
to the same surviving address. Its rule kind is determined by its quantifier
head, its formula's sequent side, and negative-context parity. Odd parity
dualizes the quantifier; even parity preserves it. This classifies the NNF
inference kind, not a legal application to the original non-NNF formula. -/
@[blueprint "chap7__example_7_4_1" (main := true)]
theorem quantifierOccurrence_ruleKind {L : Language} (_hL : L.withoutEquality)
    {A : FormulaN L} {k x B negative}
    (o : QuantifierContextOccurrence A k x B negative) (side : PolaritySequentSide) :
    ∃ q : MaxQuantifierOccurrence A.toNNF,
      q.address = o.nnfAddress ∧
      q.selected = (if negative then k.dual else k).formula x (FormulaN.toNNFAux (!negative) B) ∧
      normalizedQuantifierRuleKind side q.selected = some (polarityRuleKind side k negative) 

/-- The exact negative universal occurrence in the antecedent formula of
Example 7.4.1: disjunction-right, negation, conjunction-right. -/
@[blueprint "chap7__example_7_4_1"]
def quantifierPolarityExOccurrence :
    QuantifierContextOccurrence quantifierPolarityExFormula .universal 0
      (FormulaN.predN QPolExPred.Q (fun _ => Term.var 0)) true :=
  .disjRight _ (.neg (.conjRight _ (.all 0 _)))

/-- Example 7.4.1: normalization of the antecedent formula itself gives the
printed NNF formula, whose selected quantifier requires exists-left. -/
@[blueprint "chap7__example_7_4_1" (main := true)]
theorem quantifierPolarityEx_ruleKind :
    quantifierPolarityExFormula.toNNF = quantifierPolarityExNNF ∧
    ∃ q : MaxQuantifierOccurrence quantifierPolarityExNNF,
      q.address = [.right, .right] ∧
      q.selected = FormulaN.ex 0 (FormulaN.neg
        (FormulaN.predN QPolExPred.Q (fun _ => Term.var 0))) ∧
      normalizedQuantifierRuleKind .antecedent q.selected = some .exLeft 

-- ATTACH-BLOCKER: section options: helper requires front context
/-- Example 7.4.1: the corresponding actual G2 quantifier schema is
exists-left at the normalized right/right occurrence. This identifies the
schema; its free-for/eigenvariable and sequent guards remain separate. -/
theorem quantifierPolarityEx_ruleSchema :
    let q : MaxQuantifierOccurrence quantifierPolarityExNNF :=
      .disjRight _ (.disjRight _ (.ex 0 _))
    (G2nnfRuleCore.exSubLeft quantifierPolarityExNNF q 0
      (FormulaN.neg (FormulaN.predN QPolExPred.Q (fun _ => Term.var 0)))
      1 rfl LCS.Finset.empty LCS.Finset.empty).quantifierRuleKind = some .exLeft := by
  rfl

/-- Example 7.4.1: the printed NNF is equivalent to the antecedent formula,
without negating that whole antecedent or changing its sequent side. -/
@[blueprint "chap7__example_7_4_1" (main := true)]
theorem quantifierPolarityEx_equiv :
    LCS.FirstOrder.Semantics.Equivalence.foLogEquivN
      quantifierPolarityExFormula quantifierPolarityExNNF 

end QuantifierPolarity
end LCS.Herbrand.NNFHauptsatz
end

