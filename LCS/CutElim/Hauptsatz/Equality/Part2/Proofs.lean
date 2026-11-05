import LCS.CutElim.Hauptsatz.Equality.Part2

section

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SyntaxN.Substitution LCS.FirstOrder.SyntaxN.Variables

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

open LCS

namespace LCS.CutElim.Hauptsatz.Equality

helper /-- The textbook unary-function example satisfies the repaired equality-axiom
admissibility predicate. -/
theorem g1nnfEqAxiomExample_wellFormed {L : Language}
    (hL : L.hasEquality = true) (f : L.funSymbols)
    (hArity : L.funArity f = 1) (s t : Term L) :
    (g1nnfEqAxiomExample hL f hArity s t).WellFormed := by
  have hi : ∃ _i : Fin (L.funArity f), True := by
    refine ⟨⟨0, by omega⟩, trivial⟩
  simpa [g1nnfEqAxiomExample, G1nnfEqAxiom.WellFormed,
    G1nnfEqAxiom.IsEligibleAtom, G1nnfEqAxiom.toSequent,
    FormulaN.isAtomic] using
    And.intro (Or.inl hi) (Or.inl hi)

helper /-- Exact regression for the textbook example:
`-> neg (s = t), f(s) = f(t)`. -/
theorem g1nnfEqAxiomExample_toSequent {L : Language}
    (hL : L.hasEquality = true) (f : L.funSymbols)
    (hArity : L.funArity f = 1) (s t : Term L) :
    let ss : Fin (L.funArity f) → Term L := fun _ => s
    let ts : Fin (L.funArity f) → Term L := fun _ => t
    (g1nnfEqAxiomExample hL f hArity s t).toSequent =
      (Finset.empty,
       Finset.insert (.neg (.eq_ hL s t))
         (Finset.singleton (.eq_ hL (.func f ss) (.func f ts)))) := by
  dsimp only
  apply Prod.ext
  · apply Finset.ext
    intro A
    simp only [g1nnfEqAxiomExample, G1nnfEqAxiom.toSequent,
      Finset.mem_erase, Finset.mem_union, Finset.mem_ofList,
      List.mem_map, List.mem_finRange]
    constructor
    · rintro ⟨hmem, hne⟩
      rcases hmem with hEq | hEmpty
      · rcases hEq with ⟨_, _, hEqA⟩
        exact (hne hEqA.symm).elim
      · exact hEmpty
    · intro hempty
      exact (Finset.not_mem_empty hempty).elim
  · apply Finset.ext
    intro A
    simp only [g1nnfEqAxiomExample, G1nnfEqAxiom.toSequent,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (hNeg | hOut | hEmpty)
      · exact Or.inl hNeg
      · exact Or.inr hOut
      · exact (Finset.not_mem_empty hEmpty).elim
    · rintro (hNeg | hOut)
      · exact Or.inl hNeg
      · exact Or.inr (Or.inl hOut)

end LCS.CutElim.Hauptsatz.Equality

end

section

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SyntaxN.Substitution LCS.FirstOrder.SyntaxN.Variables

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

open LCS

namespace LCS.CutElim.Hauptsatz.Equality

namespace G1nnfEqProofTree



end G1nnfEqProofTree

end LCS.CutElim.Hauptsatz.Equality

end

section

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SyntaxN.Substitution LCS.FirstOrder.SyntaxN.Variables

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

open LCS

namespace LCS.CutElim.Hauptsatz.Equality

namespace G1nnfEqProofTree

helper /-- Term substitution changes terms but preserves every predicate symbol and
hence preserves the maximal predicate rank of a formula. -/
theorem G1nnfEqProofTree.ambientFormulaPredRank_formulaSubstN {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) :
    ambientFormulaPredRank (formulaSubstN A t x) =
      ambientFormulaPredRank A := by
  induction A with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg _ ih =>
      simp only [formulaSubstN, ambientFormulaPredRank, ih]
  | conj _ _ ihA ihB =>
      simp only [formulaSubstN, ambientFormulaPredRank, ihA, ihB]
  | disj _ _ ihA ihB =>
      simp only [formulaSubstN, ambientFormulaPredRank, ihA, ihB]
  | impl _ _ ihA ihB =>
      simp only [formulaSubstN, ambientFormulaPredRank, ihA, ihB]
  | all _ _ ih =>
      simp only [formulaSubstN]
      split
      · simp only [ambientFormulaPredRank, ih]
      · rfl
  | ex _ _ ih =>
      simp only [formulaSubstN]
      split
      · simp only [ambientFormulaPredRank, ih]
      · rfl

helper /-- The literal-only compatibility rank never exceeds the structural formula
rank. -/
theorem G1nnfEqProofTree.literalPredRank_le_ambientFormulaPredRank {L : Language}
    (A : FormulaN L) :
    literalPredRank A ≤ ambientFormulaPredRank A := by
  cases A with
  | predN _ _ => exact Nat.le_refl _
  | eq_ _ _ _ => exact Nat.le_refl _
  | neg A =>
      cases A <;> simp [literalPredRank]
  | conj _ _ => exact Nat.zero_le _
  | disj _ _ => exact Nat.zero_le _
  | impl _ _ => exact Nat.zero_le _
  | all _ _ => exact Nat.zero_le _
  | ex _ _ => exact Nat.zero_le _

end G1nnfEqProofTree

end LCS.CutElim.Hauptsatz.Equality

end

section

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SyntaxN.Substitution LCS.FirstOrder.SyntaxN.Variables

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

open LCS

namespace LCS.CutElim.Hauptsatz.Equality

namespace G1nnfEqRule

helper /-- A wrapped base cut contributes the structural predicate rank of its cut
formula. -/
@[simp]
theorem G1nnfEqRule.ambientCutPredRank_base_cut {L : Language}
    {hL : L.hasEquality = true}
    (A : FormulaN L) (Λ Θ : Finset (FormulaN L)) :
    ambientCutPredRank (hL := hL) (.base (.cut A Λ Θ)) =
      G1nnfEqProofTree.ambientFormulaPredRank A :=
  rfl

end G1nnfEqRule

end LCS.CutElim.Hauptsatz.Equality

end

section

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SyntaxN.Substitution LCS.FirstOrder.SyntaxN.Variables

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

open LCS

namespace LCS.CutElim.Hauptsatz.Equality

namespace G1nnfEqProofTree

helper /-- Internal ambient invariant: collect the maximum predicate rank occurring
in any cut formula, and reserve rank two for equality even when a tree has no
cuts. This stronger measure is intentionally not the tagged textbook `m`. -/
noncomputable def G1nnfEqProofTree.ambientPredRankTree {L : Language}
    {hL : L.hasEquality = true} :
    {Γ Δ : Finset (FormulaN L)} →
    G1nnfEqProofTree hL Γ Δ → Nat
  | _, _, .axiom_ _ _ _ _ _ => 2
  | _, _, .onePremise _ _ _ _ _ sub => ambientPredRankTree sub
  | _, _, .twoPremise rule _ _ _ _ sub1 sub2 =>
    max rule.ambientCutPredRank
      (max (ambientPredRankTree sub1) (ambientPredRankTree sub2))

helper /-- Constructor equation for the equality-rank reserve at proof leaves. -/
@[simp]
theorem G1nnfEqProofTree.ambientPredRankTree_axiom {L : Language}
    {hL : L.hasEquality = true}
    (rule : G1nnfEqRule L hL) (Gamma Delta : Finset (FormulaN L))
    (hAxiom : (rule.premises Gamma Delta).length = 0)
    (hAC : rule.ApplicationConditions Gamma Delta) :
    ambientPredRankTree (.axiom_ rule Gamma Delta hAxiom hAC) = 2 :=
  rfl

helper /-- Constructor equation for one-premise rank propagation. -/
@[simp]
theorem G1nnfEqProofTree.ambientPredRankTree_onePremise {L : Language}
    {hL : L.hasEquality = true}
    (rule : G1nnfEqRule L hL) (Gamma Delta : Finset (FormulaN L))
    (hPrem : (rule.premises Gamma Delta).length = 1)
    (hAC : rule.ApplicationConditions Gamma Delta)
    (sub : G1nnfEqProofTree hL
      ((rule.premises Gamma Delta)[0]'(by omega)).1
      ((rule.premises Gamma Delta)[0]'(by omega)).2) :
    ambientPredRankTree (.onePremise rule Gamma Delta hPrem hAC sub) =
      ambientPredRankTree sub :=
  rfl

helper /-- Constructor equation for binary rank propagation through a rule. -/
@[simp]
theorem G1nnfEqProofTree.ambientPredRankTree_twoPremise {L : Language}
    {hL : L.hasEquality = true}
    (rule : G1nnfEqRule L hL) (Gamma Delta : Finset (FormulaN L))
    (hPrem : (rule.premises Gamma Delta).length = 2)
    (hAC : rule.ApplicationConditions Gamma Delta)
    (sub1 : G1nnfEqProofTree hL
      ((rule.premises Gamma Delta)[0]'(by omega)).1
      ((rule.premises Gamma Delta)[0]'(by omega)).2)
    (sub2 : G1nnfEqProofTree hL
      ((rule.premises Gamma Delta)[1]'(by omega)).1
      ((rule.premises Gamma Delta)[1]'(by omega)).2) :
    ambientPredRankTree
        (.twoPremise rule Gamma Delta hPrem hAC sub1 sub2) =
      max rule.ambientCutPredRank
        (max (ambientPredRankTree sub1) (ambientPredRankTree sub2)) :=
  rfl

helper /-- Every proof tree retains rank two for the distinguished equality
predicate, independently of whether it contains a cut. -/
theorem G1nnfEqProofTree.two_le_ambientPredRankTree {L : Language}
    {hL : L.hasEquality = true}
    {Γ Δ : Finset (FormulaN L)}
    (T : G1nnfEqProofTree hL Γ Δ) :
    2 ≤ ambientPredRankTree T := by
  induction T with
  | axiom_ =>
      exact Nat.le_refl 2
  | onePremise _ _ _ _ _ sub ih =>
      exact ih
  | twoPremise _ _ _ _ _ sub1 sub2 ih1 _ =>
      exact Nat.le_trans
        (Nat.le_trans ih1 (Nat.le_max_left _ _))
        (Nat.le_max_right _ _)

helper /-- Transporting conclusion indices does not change the tree-wide predicate
rank. -/
theorem G1nnfEqProofTree.ambientPredRankTree_cast {L : Language}
    {hL : L.hasEquality = true}
    {Γ Δ Γ' Δ' : Finset (FormulaN L)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (T : G1nnfEqProofTree hL Γ Δ) :
    ambientPredRankTree (cast hΓ hΔ T) = ambientPredRankTree T := by
  subst Γ'
  subst Δ'
  rfl

helper /-- Internal ambient bound for future reduction proofs. It includes every
predicate occurring in the principal formula and in all cut formulae of both
input trees, with equality rank reserved by `ambientPredRankTree`. -/
noncomputable def G1nnfEqProofTree.ambientPredRank {L : Language}
    {hL : L.hasEquality = true}
    {Γ₁ Δ₁ Γ₂ Δ₂ : Finset (FormulaN L)}
    (A : FormulaN L)
    (T1 : G1nnfEqProofTree hL Γ₁ Δ₁)
    (T2 : G1nnfEqProofTree hL Γ₂ Δ₂) : Nat :=
  max (ambientFormulaPredRank A)
    (max (ambientPredRankTree T1) (ambientPredRankTree T2))

helper @[simp]
theorem G1nnfEqProofTree.literalPredRank_predN {L : Language} (P : L.predSymbols)
    (ts : Fin (L.predArity P) → Term L) :
    literalPredRank (.predN P ts) = L.predArity P :=
  rfl

helper @[simp]
theorem G1nnfEqProofTree.literalPredRank_negPredN {L : Language} (P : L.predSymbols)
    (ts : Fin (L.predArity P) → Term L) :
    literalPredRank (.neg (.predN P ts)) = L.predArity P :=
  rfl

helper @[simp]
theorem G1nnfEqProofTree.literalPredRank_eq {L : Language} (hL : L.hasEquality = true)
    (s t : Term L) :
    literalPredRank (.eq_ hL s t) = 2 :=
  rfl

helper @[simp]
theorem G1nnfEqProofTree.literalPredRank_negEq {L : Language} (hL : L.hasEquality = true)
    (s t : Term L) :
    literalPredRank (.neg (.eq_ hL s t)) = 2 :=
  rfl

helper /-- Adversarial regression: the literal-only compatibility rank loses a
positive-arity predicate underneath a connective, while the structural rank
still detects it. -/
theorem G1nnfEqProofTree.literalPredRank_misses_composite_predicate {L : Language}
    (P : L.predSymbols) (ts : Fin (L.predArity P) → Term L)
    (hPos : 0 < L.predArity P) :
    literalPredRank (.conj (.predN P ts) (.neg (.predN P ts))) <
      ambientFormulaPredRank
        (.conj (.predN P ts) (.neg (.predN P ts))) := by
  simpa only [literalPredRank, ambientFormulaPredRank, Nat.max_self] using hPos

helper theorem G1nnfEqProofTree.ambientFormulaPredRank_le_ambientPredRank {L : Language}
    {hL : L.hasEquality = true}
    {Γ₁ Δ₁ Γ₂ Δ₂ : Finset (FormulaN L)}
    (A : FormulaN L)
    (T1 : G1nnfEqProofTree hL Γ₁ Δ₁)
    (T2 : G1nnfEqProofTree hL Γ₂ Δ₂) :
    ambientFormulaPredRank A ≤ ambientPredRank A T1 T2 :=
  Nat.le_max_left _ _

helper theorem G1nnfEqProofTree.literalPredRank_le_ambientPredRank {L : Language}
    {hL : L.hasEquality = true}
    {Γ₁ Δ₁ Γ₂ Δ₂ : Finset (FormulaN L)}
    (A : FormulaN L)
    (T1 : G1nnfEqProofTree hL Γ₁ Δ₁)
    (T2 : G1nnfEqProofTree hL Γ₂ Δ₂) :
    literalPredRank A ≤ ambientPredRank A T1 T2 :=
  Nat.le_trans (literalPredRank_le_ambientFormulaPredRank A)
    (ambientFormulaPredRank_le_ambientPredRank A T1 T2)

helper theorem G1nnfEqProofTree.maxPredRankTree_left_le_maxPredRank {L : Language}
    {hL : L.hasEquality = true}
    {Γ₁ Δ₁ Γ₂ Δ₂ : Finset (FormulaN L)}
    (A : FormulaN L)
    (T1 : G1nnfEqProofTree hL Γ₁ Δ₁)
    (T2 : G1nnfEqProofTree hL Γ₂ Δ₂) :
    maxPredRankTree T1 ≤ maxPredRank A T1 T2 :=
  Nat.le_max_left _ _

helper theorem G1nnfEqProofTree.maxPredRankTree_right_le_maxPredRank {L : Language}
    {hL : L.hasEquality = true}
    {Γ₁ Δ₁ Γ₂ Δ₂ : Finset (FormulaN L)}
    (A : FormulaN L)
    (T1 : G1nnfEqProofTree hL Γ₁ Δ₁)
    (T2 : G1nnfEqProofTree hL Γ₂ Δ₂) :
    maxPredRankTree T2 ≤ maxPredRank A T1 T2 :=
  Nat.le_max_right _ _

helper /-- The left tree's structural ambient rank is bounded by the aggregate
ambient rank. -/
theorem G1nnfEqProofTree.ambientPredRankTree_left_le_ambientPredRank {L : Language}
    {hL : L.hasEquality = true}
    {Γ₁ Δ₁ Γ₂ Δ₂ : Finset (FormulaN L)}
    (A : FormulaN L)
    (T1 : G1nnfEqProofTree hL Γ₁ Δ₁)
    (T2 : G1nnfEqProofTree hL Γ₂ Δ₂) :
    ambientPredRankTree T1 ≤ ambientPredRank A T1 T2 :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

helper /-- The right tree's structural ambient rank is bounded by the aggregate
ambient rank. -/
theorem G1nnfEqProofTree.ambientPredRankTree_right_le_ambientPredRank {L : Language}
    {hL : L.hasEquality = true}
    {Γ₁ Δ₁ Γ₂ Δ₂ : Finset (FormulaN L)}
    (A : FormulaN L)
    (T1 : G1nnfEqProofTree hL Γ₁ Δ₁)
    (T2 : G1nnfEqProofTree hL Γ₂ Δ₂) :
    ambientPredRankTree T2 ≤ ambientPredRank A T1 T2 :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

helper /-- Componentwise characterization of an upper bound on the aggregate
ambient predicate rank. -/
theorem G1nnfEqProofTree.ambientPredRank_le_iff {L : Language}
    {hL : L.hasEquality = true}
    {Γ₁ Δ₁ Γ₂ Δ₂ : Finset (FormulaN L)}
    (A : FormulaN L)
    (T1 : G1nnfEqProofTree hL Γ₁ Δ₁)
    (T2 : G1nnfEqProofTree hL Γ₂ Δ₂)
    (m : Nat) :
    ambientPredRank A T1 T2 ≤ m ↔
      ambientFormulaPredRank A ≤ m ∧
        ambientPredRankTree T1 ≤ m ∧ ambientPredRankTree T2 ≤ m := by
  simp only [ambientPredRank, Nat.max_le]

helper /-- Classifier tightness regression: equality roots and base-axiom roots are
disjoint because they classify the proof constructor, not just its sequent. -/
theorem G1nnfEqProofTree.equalityAxiomRoot_not_baseAxiomRoot {L : Language}
    {hL : L.hasEquality = true}
    {Γ Δ : Finset (FormulaN L)}
    (T : G1nnfEqProofTree hL Γ Δ) :
    T.IsEqualityAxiomRoot → ¬ T.IsBaseAxiomRoot := by
  cases T with
  | axiom_ rule Gamma Delta hAxiom hAC =>
      cases rule <;>
        simp [IsEqualityAxiomRoot, IsBaseAxiomRoot,
          reductionRootKind]
  | onePremise =>
      simp [IsEqualityAxiomRoot, reductionRootKind]
  | twoPremise =>
      simp [IsEqualityAxiomRoot, reductionRootKind]

helper /-- Classifier tightness regression: equality leaves, base-system leaves,
and inference roots exhaust all proof constructors. -/
theorem G1nnfEqProofTree.equalityAxiomRoot_or_baseAxiomRoot_or_inferenceRoot {L : Language}
    {hL : L.hasEquality = true}
    {Γ Δ : Finset (FormulaN L)}
    (T : G1nnfEqProofTree hL Γ Δ) :
    T.IsEqualityAxiomRoot ∨ T.IsBaseAxiomRoot ∨ T.IsInferenceRoot := by
  cases T with
  | axiom_ rule Gamma Delta hAxiom hAC =>
      cases rule <;>
        simp [IsEqualityAxiomRoot, IsBaseAxiomRoot, IsInferenceRoot,
          reductionRootKind]
  | onePremise =>
      simp [IsEqualityAxiomRoot, IsBaseAxiomRoot, IsInferenceRoot,
        reductionRootKind]
  | twoPremise =>
      simp [IsEqualityAxiomRoot, IsBaseAxiomRoot, IsInferenceRoot,
        reductionRootKind]

end G1nnfEqProofTree

end LCS.CutElim.Hauptsatz.Equality

end

section

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SyntaxN.Substitution LCS.FirstOrder.SyntaxN.Variables

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

open LCS

namespace LCS.CutElim.Hauptsatz.Equality

proof_of g1nnfEq_completeness := by
  -- BEGIN PROOF
    -- This requires completeness of LKe (Thm 6.3.1) plus G1nnfEq simulation.
    -- Sorry'd as it depends on sorry'd Thm 6.3.1 chain.
    -- DEBT(Lemma 6.4.8: completeness of G1nnf= through Theorem 6.3.1 and the LKe simulation; proof pending)
    sorry


helper /-- Lemma 6.4.9 (companion): The sequent s = t, t = r → s = r is
provable in G1nnfEq without essential cuts. Textbook Lem 6.4.9 Case 3
chains inessential cuts, so the transitivity sequent must itself be
provable with `hasNoEssentialCuts` to preserve the chain. -/
theorem g1nnfEq_transitivity_sequent {L : Language} (hL : L.hasEquality = true)
    (s t r : Term L) :
    ∃ T : G1nnfEqProofTree hL
      (Finset.insert (.eq_ hL s t)
        (Finset.insert (.eq_ hL t r) Finset.empty))
      (Finset.insert (.eq_ hL s r) Finset.empty),
      T.hasNoEssentialCuts := by
-- BEGIN PROOF
  let C : FormulaN L := .eq_ hL s s
  let Gamma : Finset (FormulaN L) :=
    Finset.insert (.eq_ hL s t)
      (Finset.insert (.eq_ hL t r) Finset.empty)
  let Delta : Finset (FormulaN L) :=
    Finset.insert (.eq_ hL s r) Finset.empty
  change ∃ T : G1nnfEqProofTree hL Gamma Delta,
    T.hasNoEssentialCuts
  have hNNF : G1nnfFinsetSequent.IsNNF (Gamma, Delta) := by
    exact G1nnfFinsetSequent.IsNNF.insert_right
      (A := .eq_ hL s r) trivial
      (G1nnfFinsetSequent.IsNNF.insert_left
        (A := .eq_ hL s t) trivial
        (G1nnfFinsetSequent.IsNNF.insert_left
          (A := .eq_ hL t r) trivial
          G1nnfFinsetSequent.IsNNF.empty))
  have hNNFRefl :
      G1nnfFinsetSequent.IsNNF (Gamma, Finset.insert C Delta) :=
    G1nnfFinsetSequent.IsNNF.insert_right (A := C) trivial hNNF
  let TRefl : G1nnfEqProofTree hL Gamma (Finset.insert C Delta) :=
    g1nnfEqProofTree_accepts_eqAxiom
      (.refl (hL := hL) s Gamma Delta) trivial hNNFRefl
  let TCongRaw :=
    g1nnfEqProofTree_accepts_eqCong (hL := hL) s t s r
      (Finset.empty : Finset (FormulaN L)) Finset.empty
      G1nnfFinsetSequent.IsNNF.empty
  have hCongAnte :
      (G1nnfEqAxiom.eqCong (hL := hL) s t s r
        Finset.empty Finset.empty).toSequent.1 =
        Finset.insert C Gamma := by
    change
      Finset.insert (.eq_ hL s t)
        (Finset.union
          (Finset.ofList [C, .eq_ hL t r]) Finset.empty) =
      Finset.insert C
        (Finset.insert (.eq_ hL s t)
          (Finset.insert (.eq_ hL t r) Finset.empty))
    have hPairs :
        Finset.union
          (Finset.ofList [C, .eq_ hL t r]) Finset.empty =
        Finset.insert C
          (Finset.insert (.eq_ hL t r) Finset.empty) := by
      change
        Finset.insert (.eq_ hL t r) (Finset.insert C Finset.empty) =
        Finset.insert C (Finset.insert (.eq_ hL t r) Finset.empty)
      exact LCS.Finset.insert_comm _ _ _
    rw [hPairs]
    exact LCS.Finset.insert_comm _ _ _
  let TCong : G1nnfEqProofTree hL (Finset.insert C Gamma) Delta :=
    G1nnfEqProofTree.cast hCongAnte rfl TCongRaw
  have hConc :
      (G1nnfEqRule.base (hL := hL) (.cut C Gamma Delta)).conclusion
        Gamma Delta = (Gamma, Delta) :=
    G1nnfRule.cut_shared_conclusion C Gamma Delta
  have hBaseAC :
      G1nnfRule.ApplicationConditions (.cut C Gamma Delta) Gamma Delta := by
    refine ⟨trivial, ?_⟩
    simpa only [G1nnfRule.cut_shared_conclusion] using hNNF
  have hAC :
      G1nnfEqRule.ApplicationConditions (hL := hL)
        (.base (.cut C Gamma Delta)) Gamma Delta :=
    (G1nnfEqRule.applicationConditions_base_iff (hL := hL)
      (.cut C Gamma Delta) Gamma Delta).2 hBaseAC
  let core := G1nnfEqProofTree.twoPremise
    (.base (.cut C Gamma Delta)) Gamma Delta rfl hAC TRefl TCong
  let T : G1nnfEqProofTree hL Gamma Delta :=
    G1nnfEqProofTree.cast
      (congrArg Prod.fst hConc) (congrArg Prod.snd hConc) core
  refine ⟨T, ?_⟩
  have hReflRank : TRefl.essentialCutRank = 0 := rfl
  have hCongRank : TCong.essentialCutRank = 0 := by
    dsimp only [TCong]
    refine (G1nnfEqProofTree.essentialCutRank_cast _ _ _).trans ?_
    rfl
  change T.essentialCutRank = 0
  dsimp only [T]
  rw [G1nnfEqProofTree.essentialCutRank_cast]
  change max TRefl.essentialCutRank TCong.essentialCutRank = 0
  rw [hReflRank, hCongRank]
  rfl

proof_of g1nnfEq_reduction_lemma := by
  -- REPAIR(T6-33): proof pending (hand proof: feasibility-T6-78 §A)
  sorry


proof_of g1nnfEq_cut_elimination := by
  -- REPAIR(T6-33): proof pending; truth open under E-CUTFB
  sorry


end LCS.CutElim.Hauptsatz.Equality

end
