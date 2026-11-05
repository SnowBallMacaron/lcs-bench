import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.SharpenedHauptsatz
import LCS.Herbrand.NNFHauptsatz.Renaming.Part1

section
namespace LCS.Herbrand.NNFHauptsatz
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.SharpenedHauptsatz

/-- Maximal quantified subformula membership is transported as a set
image under uniform renaming. -/
theorem maxQuantSubformulae_formulaVarMapN_iff {L : Language}
    (ρ : Nat → Nat) (A Q' : FormulaN L) :
    Q' ∈ maxQuantSubformulaeCore (formulaVarMapN ρ A) ↔
      ∃ Q, Q ∈ maxQuantSubformulaeCore A ∧ formulaVarMapN ρ Q = Q' := by
  induction A with
  | predN P ts =>
      simp only [formulaVarMapN, maxQuantSubformulaeCore]
      constructor
      · intro hQ
        exact hQ.elim
      · rintro ⟨Q, hQ, _⟩
        exact hQ.elim
  | eq_ hL t₁ t₂ =>
      simp only [formulaVarMapN, maxQuantSubformulaeCore]
      constructor
      · intro hQ
        exact hQ.elim
      · rintro ⟨Q, hQ, _⟩
        exact hQ.elim
  | neg A ih =>
      simp only [formulaVarMapN, maxQuantSubformulaeCore]
      constructor
      · intro hQ
        exact hQ.elim
      · rintro ⟨Q, hQ, _⟩
        exact hQ.elim
  | conj A B ihA ihB =>
      simp only [formulaVarMapN, maxQuantSubformulaeCore]
      constructor
      · rintro (hQ | hQ)
        · rcases ihA.mp hQ with ⟨Q, hQ, hMap⟩
          exact ⟨Q, Or.inl hQ, hMap⟩
        · rcases ihB.mp hQ with ⟨Q, hQ, hMap⟩
          exact ⟨Q, Or.inr hQ, hMap⟩
      · rintro ⟨Q, hQ | hQ, hMap⟩
        · exact Or.inl (ihA.mpr ⟨Q, hQ, hMap⟩)
        · exact Or.inr (ihB.mpr ⟨Q, hQ, hMap⟩)
  | disj A B ihA ihB =>
      simp only [formulaVarMapN, maxQuantSubformulaeCore]
      constructor
      · rintro (hQ | hQ)
        · rcases ihA.mp hQ with ⟨Q, hQ, hMap⟩
          exact ⟨Q, Or.inl hQ, hMap⟩
        · rcases ihB.mp hQ with ⟨Q, hQ, hMap⟩
          exact ⟨Q, Or.inr hQ, hMap⟩
      · rintro ⟨Q, hQ | hQ, hMap⟩
        · exact Or.inl (ihA.mpr ⟨Q, hQ, hMap⟩)
        · exact Or.inr (ihB.mpr ⟨Q, hQ, hMap⟩)
  | impl A B ihA ihB =>
      simp only [formulaVarMapN, maxQuantSubformulaeCore]
      constructor
      · intro hQ
        exact hQ.elim
      · rintro ⟨Q, hQ, _⟩
        exact hQ.elim
  | all x A ih =>
      simp only [formulaVarMapN, maxQuantSubformulaeCore]
      constructor
      · intro hQ
        exact ⟨FormulaN.all x A, rfl, hQ.symm⟩
      · rintro ⟨Q, hQ, hMap⟩
        subst Q
        exact hMap.symm
  | ex x A ih =>
      simp only [formulaVarMapN, maxQuantSubformulaeCore]
      constructor
      · intro hQ
        exact ⟨FormulaN.ex x A, rfl, hQ.symm⟩
      · rintro ⟨Q, hQ, hMap⟩
        subst Q
        exact hMap.symm

/-- At the renamed source formula, maximal quantified subformula membership
reflects exactly for an injective renaming. -/
theorem formulaVarMapN_mem_maxQuantSubformulae_iff {L : Language}
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (A Q : FormulaN L) :
    formulaVarMapN ρ Q ∈
        maxQuantSubformulaeCore (formulaVarMapN ρ A) ↔
      Q ∈ maxQuantSubformulaeCore A := by
  rw [maxQuantSubformulae_formulaVarMapN_iff]
  constructor
  · rintro ⟨P, hP, hEq⟩
    have hPQ : P = Q := formulaVarMapN_injective hρ hEq
    simpa [hPQ] using hP
  · intro hQ
    exact ⟨Q, hQ, rfl⟩

/-- Equality-directed global maximal-quantifier replacement commutes with
injective uniform renaming. -/
theorem formulaVarMapN_replaceMaxQuantSub
    {L : Language} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (A B C : FormulaN L) :
    formulaVarMapN ρ (replaceMaxQuantSubCore A B C) =
      replaceMaxQuantSubCore (formulaVarMapN ρ A)
        (formulaVarMapN ρ B) (formulaVarMapN ρ C) := by
  induction A with
  | predN P ts =>
      rfl
  | eq_ hL t₁ t₂ =>
      rfl
  | neg A ih =>
      rfl
  | conj A₁ A₂ ih₁ ih₂ =>
      simp only [replaceMaxQuantSubCore, formulaVarMapN]
      by_cases hAB : FormulaN.conj A₁ A₂ = B
      · have hMap :
            FormulaN.conj (formulaVarMapN ρ A₁) (formulaVarMapN ρ A₂) =
              formulaVarMapN ρ B :=
          congrArg (formulaVarMapN ρ) hAB
        rw [if_pos hAB, if_pos hMap]
      · have hMap :
            FormulaN.conj (formulaVarMapN ρ A₁) (formulaVarMapN ρ A₂) ≠
              formulaVarMapN ρ B :=
          fun h => hAB (formulaVarMapN_injective hρ h)
        rw [if_neg hAB, if_neg hMap, formulaVarMapN, ih₁, ih₂]
  | disj A₁ A₂ ih₁ ih₂ =>
      simp only [replaceMaxQuantSubCore, formulaVarMapN]
      by_cases hAB : FormulaN.disj A₁ A₂ = B
      · have hMap :
            FormulaN.disj (formulaVarMapN ρ A₁) (formulaVarMapN ρ A₂) =
              formulaVarMapN ρ B :=
          congrArg (formulaVarMapN ρ) hAB
        rw [if_pos hAB, if_pos hMap]
      · have hMap :
            FormulaN.disj (formulaVarMapN ρ A₁) (formulaVarMapN ρ A₂) ≠
              formulaVarMapN ρ B :=
          fun h => hAB (formulaVarMapN_injective hρ h)
        rw [if_neg hAB, if_neg hMap, formulaVarMapN, ih₁, ih₂]
  | impl A₁ A₂ ih₁ ih₂ =>
      rfl
  | all x A ih =>
      simp only [replaceMaxQuantSubCore, formulaVarMapN]
      by_cases hAB : FormulaN.all x A = B
      · have hMap :
            FormulaN.all (ρ x) (formulaVarMapN ρ A) =
              formulaVarMapN ρ B :=
          congrArg (formulaVarMapN ρ) hAB
        rw [if_pos hAB, if_pos hMap]
      · have hMap :
            FormulaN.all (ρ x) (formulaVarMapN ρ A) ≠
              formulaVarMapN ρ B :=
          fun h => hAB (formulaVarMapN_injective hρ h)
        rw [if_neg hAB, if_neg hMap]
        rfl
  | ex x A ih =>
      simp only [replaceMaxQuantSubCore, formulaVarMapN]
      by_cases hAB : FormulaN.ex x A = B
      · have hMap :
            FormulaN.ex (ρ x) (formulaVarMapN ρ A) =
              formulaVarMapN ρ B :=
          congrArg (formulaVarMapN ρ) hAB
        rw [if_pos hAB, if_pos hMap]
      · have hMap :
            FormulaN.ex (ρ x) (formulaVarMapN ρ A) ≠
              formulaVarMapN ρ B :=
          fun h => hAB (formulaVarMapN_injective hρ h)
        rw [if_neg hAB, if_neg hMap]
        rfl

/-! ## Indexed G2nnf rule and proof-tree transport

The syntax map above is lifted through every annotation stored by a G2nnf
rule and then through the indexed proof-tree constructors.  The premise
indices are not definitionally equal because finite-context renaming is an
image operation, so the tree map deliberately exposes and uses exact
pointwise premise equations.
-/

/-- Uniform variable renaming on both sides of a finite sequent. -/
noncomputable def g2nnfSequentVarMap {L : Language}
    (ρ : Nat → Nat)
    (S : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) :
    LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L) :=
  (formulaFinsetVarMapN ρ S.1, formulaFinsetVarMapN ρ S.2)

/-- Pointwise freshness from free variables is preserved when both the
formulae and the tested variable are transported by an injective map. -/
theorem formulaFinsetVarMapN_fresh_free
    {L : Language} (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (S : LCS.Finset (FormulaN L)) (y : Nat)
    (hFresh : ∀ F, F ∈ S → ¬ Membership.mem (formulaFVN F) y) :
    ∀ F, F ∈ formulaFinsetVarMapN ρ S →
      ¬ Membership.mem (formulaFVN F) (ρ y) := by
  intro F hF
  rcases (mem_formulaFinsetVarMapN_iff ρ S F).mp hF with
    ⟨A, hA, rfl⟩
  intro hy
  exact hFresh A hA
    ((formulaFVN_formulaVarMapN_image_iff ρ hρ A y).mp hy)

end LCS.Herbrand.NNFHauptsatz
end

section
namespace LCS.Herbrand.NNFHauptsatz
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.SharpenedHauptsatz
namespace G2nnfRuleCore

/-- Rename every variable-bearing field of a G2nnf rule.  In particular this
maps stored axiom contexts, cut formulae, exact maximal occurrences,
quantifier binders, eigenvariables, and instantiation terms. -/
noncomputable def varMap {L : Language} (ρ : Nat → Nat) :
    G2nnfRuleCore L → G2nnfRuleCore L
  | .axiomPosId A hAtom Γ Δ =>
      .axiomPosId (formulaVarMapN ρ A)
        (by
          rw [formulaVarMapN_isAtomic]
          exact hAtom)
        (formulaFinsetVarMapN ρ Γ) (formulaFinsetVarMapN ρ Δ)
  | .axiomNegId A hAtom Γ Δ =>
      .axiomNegId (formulaVarMapN ρ A)
        (by
          rw [formulaVarMapN_isAtomic]
          exact hAtom)
        (formulaFinsetVarMapN ρ Γ) (formulaFinsetVarMapN ρ Δ)
  | .axiomCompRight A hAtom Γ Δ =>
      .axiomCompRight (formulaVarMapN ρ A)
        (by
          rw [formulaVarMapN_isAtomic]
          exact hAtom)
        (formulaFinsetVarMapN ρ Γ) (formulaFinsetVarMapN ρ Δ)
  | .axiomCompLeft A hAtom Γ Δ =>
      .axiomCompLeft (formulaVarMapN ρ A)
        (by
          rw [formulaVarMapN_isAtomic]
          exact hAtom)
        (formulaFinsetVarMapN ρ Γ) (formulaFinsetVarMapN ρ Δ)
  | .weakLeft A Gamma Delta =>
      .weakLeft (formulaVarMapN ρ A)
        (formulaFinsetVarMapN ρ Gamma) (formulaFinsetVarMapN ρ Delta)

  | .weakRight A Gamma Delta =>
      .weakRight (formulaVarMapN ρ A)
        (formulaFinsetVarMapN ρ Gamma) (formulaFinsetVarMapN ρ Delta)

  | .conjLeft1 A B Gamma Delta =>
      .conjLeft1 (formulaVarMapN ρ A) (formulaVarMapN ρ B)
        (formulaFinsetVarMapN ρ Gamma) (formulaFinsetVarMapN ρ Delta)

  | .conjLeft2 A B Gamma Delta =>
      .conjLeft2 (formulaVarMapN ρ A) (formulaVarMapN ρ B)
        (formulaFinsetVarMapN ρ Gamma) (formulaFinsetVarMapN ρ Delta)

  | .conjRight A B Gamma Delta =>
      .conjRight (formulaVarMapN ρ A) (formulaVarMapN ρ B)
        (formulaFinsetVarMapN ρ Gamma) (formulaFinsetVarMapN ρ Delta)

  | .disjLeft A B Gamma Delta =>
      .disjLeft (formulaVarMapN ρ A) (formulaVarMapN ρ B)
        (formulaFinsetVarMapN ρ Gamma) (formulaFinsetVarMapN ρ Delta)

  | .disjRight1 A B Gamma Delta =>
      .disjRight1 (formulaVarMapN ρ A) (formulaVarMapN ρ B)
        (formulaFinsetVarMapN ρ Gamma) (formulaFinsetVarMapN ρ Delta)

  | .disjRight2 A B Gamma Delta =>
      .disjRight2 (formulaVarMapN ρ A) (formulaVarMapN ρ B)
        (formulaFinsetVarMapN ρ Gamma) (formulaFinsetVarMapN ρ Delta)

  | .cut A Lambda Theta Gamma Delta =>
      .cut (formulaVarMapN ρ A) (formulaFinsetVarMapN ρ Lambda)
        (formulaFinsetVarMapN ρ Theta)
        (formulaFinsetVarMapN ρ Gamma) (formulaFinsetVarMapN ρ Delta)

  | .allSubLeft A occurrence x B t hSelected Gamma Delta =>
      .allSubLeft (formulaVarMapN ρ A) (occurrence.varMap ρ)
        (ρ x) (formulaVarMapN ρ B) (termVarMap ρ t)
        (by
          rw [MaxQuantifierOccurrence.selected_varMap, hSelected]
          rfl)
        (formulaFinsetVarMapN ρ Gamma) (formulaFinsetVarMapN ρ Delta)

  | .allSubRight A occurrence x B y hSelected Gamma Delta =>
      .allSubRight (formulaVarMapN ρ A) (occurrence.varMap ρ)
        (ρ x) (formulaVarMapN ρ B) (ρ y)
        (by
          rw [MaxQuantifierOccurrence.selected_varMap, hSelected]
          rfl)
        (formulaFinsetVarMapN ρ Gamma) (formulaFinsetVarMapN ρ Delta)

  | .exSubLeft A occurrence x B y hSelected Gamma Delta =>
      .exSubLeft (formulaVarMapN ρ A) (occurrence.varMap ρ)
        (ρ x) (formulaVarMapN ρ B) (ρ y)
        (by
          rw [MaxQuantifierOccurrence.selected_varMap, hSelected]
          rfl)
        (formulaFinsetVarMapN ρ Gamma) (formulaFinsetVarMapN ρ Delta)

  | .exSubRight A occurrence x B t hSelected Gamma Delta =>
      .exSubRight (formulaVarMapN ρ A) (occurrence.varMap ρ)
        (ρ x) (formulaVarMapN ρ B) (termVarMap ρ t)
        (by
          rw [MaxQuantifierOccurrence.selected_varMap, hSelected]
          rfl)
        (formulaFinsetVarMapN ρ Gamma) (formulaFinsetVarMapN ρ Delta)

/-- Finite-context union transport is independent of the equality instance. -/
theorem union_varMap {L : Language} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (S T : LCS.Finset (FormulaN L)) :
    formulaFinsetVarMapN ρ (LCS.Finset.union S T) =
      LCS.Finset.union (formulaFinsetVarMapN ρ S) (formulaFinsetVarMapN ρ T) := by
  apply LCS.Finset.ext
  intro B
  simp only [mem_formulaFinsetVarMapN_iff, LCS.Finset.mem_union]
  constructor
  · rintro ⟨A, hA | hA, hEq⟩
    · exact Or.inl ⟨A, hA, hEq⟩
    · exact Or.inr ⟨A, hA, hEq⟩
  · rintro (⟨A, hA, hEq⟩ | ⟨A, hA, hEq⟩)
    · exact ⟨A, Or.inl hA, hEq⟩
    · exact ⟨A, Or.inr hA, hEq⟩

/-- Rule conclusions commute exactly with uniform variable renaming. -/
theorem conclusion_varMap {L : Language} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (rule : G2nnfRuleCore L) :
    (rule.varMap ρ).conclusion =
      g2nnfSequentVarMap ρ (rule.conclusion) := by
  cases rule <;>
    simp only [varMap, conclusion, g2nnfSequentVarMap]
  all_goals
    repeat rw [formulaFinsetVarMapN_insert_with_instance]
  all_goals
    repeat rw [union_varMap]
    try rfl

/-- The full ordered premise list commutes with injective uniform renaming.
List order is retained, which is essential for occurrence-sensitive binary
paths and exact branch encodings. -/
theorem premises_varMap {L : Language} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (rule : G2nnfRuleCore L) :
    (rule.varMap ρ).premises =
      (rule.premises).map (g2nnfSequentVarMap ρ) := by
  cases rule <;>
    simp only [varMap, premises, g2nnfSequentVarMap, List.map]
  all_goals
    repeat rw [formulaFinsetVarMapN_insert_with_instance]
    repeat rw [MaxQuantifierOccurrence.replace_varMap]
    repeat rw [formulaVarMapN_formulaSubstN ρ hρ]
  all_goals
    rfl

/-- Renaming does not change rule arity. -/
theorem premises_length_varMap
    {L : Language} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (rule : G2nnfRuleCore L) :
    ((rule.varMap ρ).premises).length =
      (rule.premises).length := by
  simpa using congrArg List.length
    (premises_varMap ρ hρ rule)

/-- Pointwise indexed form of `premises_varMap`. -/
theorem premises_nth_varMap
    {L : Language} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (rule : G2nnfRuleCore L)
    (n : Nat) (hn : n < (rule.premises).length) :
    ((rule.varMap ρ).premises)[n]'
          (by rw [premises_length_varMap ρ hρ]; exact hn) =
      g2nnfSequentVarMap ρ ((rule.premises)[n]'hn) := by
  have hEq := premises_varMap ρ hρ rule
  have :
      ((rule.varMap ρ).premises)[n]'
            (by rw [premises_length_varMap ρ hρ]; exact hn) =
        ((rule.premises).map
          (g2nnfSequentVarMap ρ))[n]'
            (by rw [List.length_map]; exact hn) := by
    simp [hEq]
  rw [this, List.getElem_map]

/-- Rule-local logical side conditions are preserved by injective uniform
renaming. -/
theorem coreSideConditions_varMap
    {L : Language} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (rule : G2nnfRuleCore L)
    (hSC : rule.LogicalSideConditions) :
    (rule.varMap ρ).LogicalSideConditions := by
  cases rule with
  | allSubLeft A occurrence x B t hSelected Gamma Delta =>
      exact (isFreeForN_formulaVarMapN_iff ρ hρ t x B).mpr hSC
  | allSubRight A occurrence x B y hSelected Gamma Delta =>
      rcases hSC with ⟨hFree, hA, hGamma, hDelta⟩
      refine ⟨
        (isFreeForN_formulaVarMapN_iff ρ hρ (.var y) x B).mpr hFree,
        ?_, formulaFinsetVarMapN_fresh_free ρ hρ Gamma y hGamma,
        formulaFinsetVarMapN_fresh_free ρ hρ Delta y hDelta⟩
      intro hy
      exact hA
        ((formulaFVN_formulaVarMapN_image_iff ρ hρ A y).mp hy)
  | exSubLeft A occurrence x B y hSelected Gamma Delta =>
      rcases hSC with ⟨hFree, hA, hGamma, hDelta⟩
      refine ⟨
        (isFreeForN_formulaVarMapN_iff ρ hρ (.var y) x B).mpr hFree,
        ?_, formulaFinsetVarMapN_fresh_free ρ hρ Gamma y hGamma,
        formulaFinsetVarMapN_fresh_free ρ hρ Delta y hDelta⟩
      intro hy
      exact hA
        ((formulaFVN_formulaVarMapN_image_iff ρ hρ A y).mp hy)
  | exSubRight A occurrence x B t hSelected Gamma Delta =>
      exact (isFreeForN_formulaVarMapN_iff ρ hρ t x B).mpr hSC
  | _ => trivial

/-- Full G2nnf side conditions, including the standing rectification
invariant, are preserved by injective uniform renaming. -/
theorem sideConditions_varMap
    {L : Language} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (rule : G2nnfRuleCore L)
    (hSC : rule.SideConditions) :
    (rule.varMap ρ).SideConditions := by
  -- REPAIR(T7-06): proof pending
  sorry

/-- Renaming preserves admission of bare atomic leaves. -/
theorem bareAtomicAxiom_varMap {L : Language} (ρ : Nat → Nat)
    (rule : G2nnfRuleCore L) (h : rule.BareAtomicAxiom) :
    (rule.varMap ρ).BareAtomicAxiom := by
  cases rule <;> simp only [varMap, BareAtomicAxiom] at *
  all_goals try trivial
  all_goals rcases h with ⟨rfl, rfl⟩; exact ⟨formulaFinsetVarMapN_empty ρ, formulaFinsetVarMapN_empty ρ⟩

end G2nnfRuleCore
end LCS.Herbrand.NNFHauptsatz
end

section
namespace LCS.Herbrand.NNFHauptsatz
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.SharpenedHauptsatz
namespace G2nnfProofTree

/-- Transport an indexed G2nnf proof tree across equal conclusion indices. -/
noncomputable def castTree {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Gamma Delta Gamma' Delta' : LCS.Finset (FormulaN L)}
    (hGamma : Gamma = Gamma') (hDelta : Delta = Delta')
    (T : G2nnfProofTree hL Gamma Delta) :
    G2nnfProofTree hL Gamma' Delta' :=
  hGamma ▸ hDelta ▸ T

/-- Structural depth of an indexed G2nnf proof tree. -/
def depth {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)] :
    {Gamma Delta : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Gamma Delta → Nat
  | _, _, .leaf _ _ h _ _ => h.elim
  | _, _, .extraAxiom _ _ h _ _ => h.elim
  | _, _, .axiom_ _ _ _ _ => 0
  | _, _, .onePremise _ _ _ _ sub => (depth (hL := hL) sub) + 1
  | _, _, .twoPremise _ _ _ _ sub1 sub2 =>
      max (depth (hL := hL) sub1) (depth (hL := hL) sub2) + 1

/-- Index transport does not change structural depth. -/
theorem depth_castTree {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta Gamma' Delta' : LCS.Finset (FormulaN L)}
    (hGamma : Gamma = Gamma') (hDelta : Delta = Delta')
    (T : G2nnfProofTree hL Gamma Delta) :
    (T.castTree (hL := hL) hGamma hDelta).depth (hL := hL) = T.depth (hL := hL) := by
  subst Gamma'
  subst Delta'
  rfl

/-- Lift an injective variable renaming through an indexed G2nnf proof tree.
The recursive subtrees are explicitly cast to the mapped rule's exact
premise indices. -/
noncomputable def varMap {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (hρ : Function.Injective ρ) :
    {Gamma Delta : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Gamma Delta →
      G2nnfProofTree hL (formulaFinsetVarMapN ρ Gamma) (formulaFinsetVarMapN ρ Delta)
  | _, _, .leaf _ _ h _ _ => h.elim
  | _, _, .extraAxiom _ _ h _ _ => h.elim
  | _, _, .axiom_ rule hAdmit hAxiom hSC =>
      have hConclusion :=
        G2nnfRuleCore.conclusion_varMap ρ rule
      have hEq1 :
          ((rule.varMap ρ).conclusion).1 =
            formulaFinsetVarMapN ρ (rule.conclusion).1 :=
        congrArg Prod.fst hConclusion
      have hEq2 :
          ((rule.varMap ρ).conclusion).2 =
            formulaFinsetVarMapN ρ (rule.conclusion).2 :=
        congrArg Prod.snd hConclusion
      have hAxiom' :
          ((rule.varMap ρ).premises).length = 0 := by
        rw [G2nnfRuleCore.premises_length_varMap ρ hρ]
        exact hAxiom
      have hSC' :=
        G2nnfRuleCore.sideConditions_varMap ρ hρ rule hSC
      castTree (hL := hL) hEq1 hEq2
        (G2nnfDeductionTreeCore.axiom_ (rule.varMap ρ)
          (G2nnfRuleCore.bareAtomicAxiom_varMap ρ rule hAdmit) hAxiom' hSC')
  | _, _, .onePremise rule hAdmit hPrem hSC sub =>
      let subNew := varMap (hL := hL) ρ hρ sub
      have hConclusion :=
        G2nnfRuleCore.conclusion_varMap ρ rule
      have hEq1 :
          ((rule.varMap ρ).conclusion).1 =
            formulaFinsetVarMapN ρ (rule.conclusion).1 :=
        congrArg Prod.fst hConclusion
      have hEq2 :
          ((rule.varMap ρ).conclusion).2 =
            formulaFinsetVarMapN ρ (rule.conclusion).2 :=
        congrArg Prod.snd hConclusion
      have hPrem' :
          ((rule.varMap ρ).premises).length = 1 := by
        rw [G2nnfRuleCore.premises_length_varMap ρ hρ]
        exact hPrem
      have hSC' :=
        G2nnfRuleCore.sideConditions_varMap ρ hρ rule hSC
      have hPrem0 : 0 < (rule.premises).length := by
        rw [hPrem]
        omega
      have hPremEq :=
        G2nnfRuleCore.premises_nth_varMap
          ρ hρ rule 0 hPrem0
      have h1 :
          (((rule.varMap ρ).premises)[0]'(by omega)).1 =
            formulaFinsetVarMapN ρ
              ((rule.premises)[0]'hPrem0).1 := by
        simpa [g2nnfSequentVarMap] using congrArg Prod.fst hPremEq
      have h2 :
          (((rule.varMap ρ).premises)[0]'(by omega)).2 =
            formulaFinsetVarMapN ρ
              ((rule.premises)[0]'hPrem0).2 := by
        simpa [g2nnfSequentVarMap] using congrArg Prod.snd hPremEq
      have subCast :
          G2nnfProofTree hL
            (((rule.varMap ρ).premises)[0]'(by omega)).1
            (((rule.varMap ρ).premises)[0]'(by omega)).2 :=
        subNew.castTree (hL := hL) h1.symm h2.symm
      castTree (hL := hL) hEq1 hEq2
        (G2nnfDeductionTreeCore.onePremise (rule.varMap ρ)
          (G2nnfRuleCore.bareAtomicAxiom_varMap ρ rule hAdmit)
          hPrem' hSC' subCast)
  | _, _, .twoPremise rule hAdmit hPrem hSC sub1 sub2 =>
      let subNew1 := varMap (hL := hL) ρ hρ sub1
      let subNew2 := varMap (hL := hL) ρ hρ sub2
      have hConclusion :=
        G2nnfRuleCore.conclusion_varMap ρ rule
      have hEq1 :
          ((rule.varMap ρ).conclusion).1 =
            formulaFinsetVarMapN ρ (rule.conclusion).1 :=
        congrArg Prod.fst hConclusion
      have hEq2 :
          ((rule.varMap ρ).conclusion).2 =
            formulaFinsetVarMapN ρ (rule.conclusion).2 :=
        congrArg Prod.snd hConclusion
      have hPrem' :
          ((rule.varMap ρ).premises).length = 2 := by
        rw [G2nnfRuleCore.premises_length_varMap ρ hρ]
        exact hPrem
      have hSC' :=
        G2nnfRuleCore.sideConditions_varMap ρ hρ rule hSC
      have hPrem0 : 0 < (rule.premises).length := by
        rw [hPrem]
        omega
      have hPrem1 : 1 < (rule.premises).length := by
        rw [hPrem]
        omega
      have hPremEq0 :=
        G2nnfRuleCore.premises_nth_varMap
          ρ hρ rule 0 hPrem0
      have hPremEq1 :=
        G2nnfRuleCore.premises_nth_varMap
          ρ hρ rule 1 hPrem1
      have h1_0 :
          (((rule.varMap ρ).premises)[0]'(by omega)).1 =
            formulaFinsetVarMapN ρ
              ((rule.premises)[0]'hPrem0).1 := by
        simpa [g2nnfSequentVarMap] using congrArg Prod.fst hPremEq0
      have h2_0 :
          (((rule.varMap ρ).premises)[0]'(by omega)).2 =
            formulaFinsetVarMapN ρ
              ((rule.premises)[0]'hPrem0).2 := by
        simpa [g2nnfSequentVarMap] using congrArg Prod.snd hPremEq0
      have h1_1 :
          (((rule.varMap ρ).premises)[1]'(by omega)).1 =
            formulaFinsetVarMapN ρ
              ((rule.premises)[1]'hPrem1).1 := by
        simpa [g2nnfSequentVarMap] using congrArg Prod.fst hPremEq1
      have h2_1 :
          (((rule.varMap ρ).premises)[1]'(by omega)).2 =
            formulaFinsetVarMapN ρ
              ((rule.premises)[1]'hPrem1).2 := by
        simpa [g2nnfSequentVarMap] using congrArg Prod.snd hPremEq1
      have subCast1 :
          G2nnfProofTree hL
            (((rule.varMap ρ).premises)[0]'(by omega)).1
            (((rule.varMap ρ).premises)[0]'(by omega)).2 :=
        subNew1.castTree (hL := hL) h1_0.symm h2_0.symm
      have subCast2 :
          G2nnfProofTree hL
            (((rule.varMap ρ).premises)[1]'(by omega)).1
            (((rule.varMap ρ).premises)[1]'(by omega)).2 :=
        subNew2.castTree (hL := hL) h1_1.symm h2_1.symm
      castTree (hL := hL) hEq1 hEq2
        (G2nnfDeductionTreeCore.twoPremise (rule.varMap ρ)
          (G2nnfRuleCore.bareAtomicAxiom_varMap ρ rule hAdmit)
          hPrem' hSC' subCast1 subCast2)

/-- Uniform proof-tree renaming preserves structural depth exactly. -/
theorem depth_varMap {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta) :
    (T.varMap (hL := hL) ρ hρ).depth (hL := hL) = T.depth (hL := hL) := by
  induction T with
  | leaf _ _ h _ _ => exact h.elim
  | extraAxiom _ _ h _ _ => exact h.elim
  | axiom_ rule hAdmit hAxiom hSC =>
      simp only [varMap]
      refine (depth_castTree (hL := hL) _ _ _).trans ?_
      rfl
  | onePremise rule hAdmit hPrem hSC sub ih =>
      simp only [varMap]
      refine (depth_castTree (hL := hL) _ _ _).trans ?_
      simp only [depth, depth_castTree, ih]
  | twoPremise rule hAdmit hPrem hSC sub1 sub2 ih1 ih2 =>
      simp only [varMap]
      refine (depth_castTree (hL := hL) _ _ _).trans ?_
      simp only [depth, depth_castTree, ih1, ih2]

end G2nnfProofTree
end LCS.Herbrand.NNFHauptsatz
end

