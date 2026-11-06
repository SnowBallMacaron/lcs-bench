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
import LCS.Herbrand.NNFHauptsatz.Rectification.ProofsStamp

/-! # Herbrand.NNFHauptsatz.Rectification

Section 7.4.1 standing convention: all formulae are rectified.
The sequent invariant `AllRectified` and its closure lemmas.
-/

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
