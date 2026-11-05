import LCS.FOResolution.Method.Completeness.Substitutions

section

namespace LCS.FOResolution.Method.Completeness

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SemanticsN

open LCS.FOResolution.ClauseForm

open LCS.FOResolution.Unification

open LCS.FOResolution.Method

open LCS.FOResolution.GroundResolution

open LCS.FOResolution.Method.Soundness

open LCS.FOResolution.Method.HerbrandBridge

open LCS.CutElim.LK

open LCS.FirstOrder.Gentzen

open LCS.Herbrand.NNFHauptsatz

open LCS.Herbrand.NNFHauptsatz.Theorem

open Classical

proof_of exLiftHom_preserves_premises := by
  revert v
  decide

proof_of exLiftHom_onto := by
  intro v
  exact ⟨v, rfl⟩

proof_of exLiftHom_roots := by
  exact ⟨rfl, rfl, rfl⟩

proof_of exLiftHom_node_labels := by
  -- REPAIR(T8-84): proof pending
  sorry

proof_of exLiftedDAG_inferences_legal := by
  -- REPAIR(T8-84): proof pending
  sorry

proof_of exLiftGroundDAG_inferences_legal := by
  -- REPAIR(T8-84): proof pending
  sorry

proof_of exLiftingExample_refutations := by
  constructor
  · refine ⟨?_, exLiftedDAG_inferences_legal, rfl⟩
    intro ⟨n, hn⟩ h
    have hCases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨
        n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
    rcases hCases with hN | hN | hN | hN | hN | hN | hN | hN <;>
      subst n <;> simp [exLiftingExample, exLiftedDAG] at h ⊢
  · refine ⟨?_, exLiftGroundDAG_inferences_legal, rfl⟩
    intro ⟨n, hn⟩ h
    have hCases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨
        n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
    rcases hCases with hN | hN | hN | hN | hN | hN | hN | hN <;>
      subst n <;> simp [exLiftingExample, exLiftGroundDAG] at h ⊢












helper /-- Theorem 8.4.1 (for Term L): If a list of first-order terms is
    unifiable, then a most general unifier exists. This is the central
    result of unification theory, proved in the textbook via the
    unification algorithm. Here the flat term-set problem is represented
    faithfully by its Cartesian equation system and solved by the concrete
    terminating Robinson solver. -/
theorem mgu_exists_of_unifiable {L : Language} (hNoEq : L.withoutEquality)
    (ts : List (Term L))
    (sigma : Nat → Term L) (hUnif : IsUnifierCore sigma ts) :
    ∃ mu : Nat → Term L, IsUnifierCore mu ts ∧ IsMGUCore mu ts := by
-- BEGIN PROOF
  let pairs : List (Term L × Term L) :=
    ts.flatMap fun t₁ => ts.map fun t₂ => (t₁, t₂)
  have pair_mem (t₁ : Term L) (ht₁ : t₁ ∈ ts)
      (t₂ : Term L) (ht₂ : t₂ ∈ ts) :
      (t₁, t₂) ∈ pairs := by
    unfold pairs
    exact List.mem_flatMap.mpr
      ⟨t₁, ht₁, List.mem_map.mpr ⟨t₂, ht₂, rfl⟩⟩
  have pairwise_of_unifier (tau : Nat → Term L)
      (hTau : IsUnifierCore tau ts) :
      IsPairwiseUnifier tau pairs := by
    intro pair hPair
    unfold pairs at hPair
    obtain ⟨t₁, ht₁, hPair⟩ := List.mem_flatMap.mp hPair
    obtain ⟨t₂, ht₂, hPair⟩ := List.mem_map.mp hPair
    subst pair
    exact hTau t₁ t₂ ht₁ ht₂
  have unifier_of_pairwise (tau : Nat → Term L)
      (hTau : IsPairwiseUnifier tau pairs) :
      IsUnifierCore tau ts := by
    intro t₁ t₂ ht₁ ht₂
    exact hTau (t₁, t₂) (pair_mem t₁ ht₁ t₂ ht₂)
  obtain ⟨mu, hMuPair, hMuMGU⟩ :=
    mgu_exists_of_pairwise_unifiable
      pairs sigma (pairwise_of_unifier sigma hUnif)
  have hMu : IsUnifierCore mu ts :=
    unifier_of_pairwise mu hMuPair
  refine ⟨mu, hMu, ?_⟩
  refine ⟨hMu, ?_, ?_⟩
  · intro x hx
    obtain ⟨pair, hPair, hVars⟩ :=
      hMuMGU.2.1 x hx
    unfold pairs at hPair
    obtain ⟨t₁, ht₁, hPair⟩ := List.mem_flatMap.mp hPair
    obtain ⟨t₂, ht₂, hPair⟩ := List.mem_map.mp hPair
    subst pair
    rcases hVars with hVars | hVars
    · exact ⟨t₁, ht₁, hVars⟩
    · exact ⟨t₂, ht₂, hVars⟩
  · intro tau hTau
    exact hMuMGU.2.2 tau
      (pairwise_of_unifier tau hTau)































helper /-- litSetUnifTerms foldl is invariant under LitSetConjugate, since
    both pos(predN P args) and neg(predN P args) contribute the same
    argument terms. -/
theorem litSetUnifTerms_conjugate_foldl {L : Language} (hNoEq : L.withoutEquality)
    (lits : List (FOLiteral L hNoEq)) (acc : List (Term L)) :
    ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) lits).foldl (fun acc lit =>
      match lit with
      | .pos (.predN _ args) => acc ++ List.ofFn args
      | .neg (.predN _ args) => acc ++ List.ofFn args
      | _ => acc) acc =
    lits.foldl (fun acc lit =>
      match lit with
      | .pos (.predN _ args) => acc ++ List.ofFn args
      | .neg (.predN _ args) => acc ++ List.ofFn args
      | _ => acc) acc := by
-- BEGIN PROOF
  simp only [LitSetConjugate]
  induction lits generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map, List.foldl_cons]
    cases hd with
    | pos f => simp only [FOLiteral.conjugate, FOLiteralCore.conjugate]; cases f <;> exact ih _
    | neg f => simp only [FOLiteral.conjugate, FOLiteralCore.conjugate]; cases f <;> exact ih _

helper /-- litSetUnifTerms is invariant under LitSetConjugate: both positive
    and negative predN literals contribute the same argument terms. -/
theorem litSetUnifTerms_LitSetConjugate {L : Language} (hNoEq : L.withoutEquality)
    (lits : List (FOLiteral L hNoEq)) :
    (litSetUnifTerms (hNoEq := by all_goals exact hNoEq)) ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) lits) = (litSetUnifTerms (hNoEq := by all_goals exact hNoEq)) lits := by
-- BEGIN PROOF
  simp only [litSetUnifTerms]
  exact (litSetUnifTerms_conjugate_foldl (hNoEq := by all_goals exact hNoEq)) lits []

helper /-- litSetUnifTerms is invariant under LitSetAbs: the absolute value
    either leaves the list unchanged (if positive head) or conjugates
    it (if negative head), and conjugation does not change the
    extracted predicate argument terms. -/
theorem litSetUnifTerms_LitSetAbs {L : Language} (hNoEq : L.withoutEquality)
    (lits : List (FOLiteral L hNoEq)) :
    (litSetUnifTerms (hNoEq := by all_goals exact hNoEq)) ((LitSetAbs (hNoEq := by all_goals exact hNoEq)) lits) = (litSetUnifTerms (hNoEq := by all_goals exact hNoEq)) lits := by
-- BEGIN PROOF
  cases lits with
  | nil => simp [LitSetAbs, litSetUnifTerms]
  | cons hd tl =>
    cases hd with
    | pos B => simp [LitSetAbs]
    | neg B => simp [LitSetAbs]; exact (litSetUnifTerms_LitSetConjugate (hNoEq := by all_goals exact hNoEq)) _

helper /-- Helper: List.ofFn after pointwise substitution equals map over
    the original List.ofFn. -/
theorem ofFn_subst_eq_map {L : Language} (sigma : Nat → Term L) {P : L.predSymbols}
    (args : Fin (L.predArity P) → Term L) :
    List.ofFn (fun i => termSubstAll (args i) sigma) =
    (List.ofFn args).map (fun t => termSubstAll t sigma) := by
-- BEGIN PROOF
  rw [List.map_ofFn]; rfl

helper /-- litSetUnifTerms distributes over substLits via map: applying sigma
    to a literal list and then extracting unification terms equals
    extracting terms first and then applying sigma pointwise. -/
theorem litSetUnifTerms_substLits_foldl {L : Language} (hNoEq : L.withoutEquality)
    (sigma : Nat → Term L) (lits : List (FOLiteral L hNoEq)) (acc : List (Term L)) :
    ((substLits (hNoEq := by all_goals exact hNoEq)) sigma lits).foldl (fun acc lit =>
      match lit with
      | .pos (.predN _ args) => acc ++ List.ofFn args
      | .neg (.predN _ args) => acc ++ List.ofFn args
      | _ => acc) (acc.map (fun t => termSubstAll t sigma)) =
    (lits.foldl (fun acc lit =>
      match lit with
      | .pos (.predN _ args) => acc ++ List.ofFn args
      | .neg (.predN _ args) => acc ++ List.ofFn args
      | _ => acc) acc).map (fun t => termSubstAll t sigma) := by
-- BEGIN PROOF
  simp only [substLits]
  induction lits generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.foldl_cons]
    cases hd with
    | pos f =>
      simp only [substLit]
      cases f with
      | predN P args =>
        show (List.map ((substLit (hNoEq := by all_goals exact hNoEq)) sigma) tl).foldl _
            ((acc.map _) ++ List.ofFn (fun i => termSubstAll (args i) sigma)) =
          (tl.foldl _ (acc ++ List.ofFn args)).map _
        rw [ofFn_subst_eq_map, ← List.map_append]
        exact ih (acc ++ List.ofFn args)
      | eq_ t1 t2 => exact ih acc
    | neg f =>
      simp only [substLit]
      cases f with
      | predN P args =>
        show (List.map ((substLit (hNoEq := by all_goals exact hNoEq)) sigma) tl).foldl _
            ((acc.map _) ++ List.ofFn (fun i => termSubstAll (args i) sigma)) =
          (tl.foldl _ (acc ++ List.ofFn args)).map _
        rw [ofFn_subst_eq_map, ← List.map_append]
        exact ih (acc ++ List.ofFn args)
      | eq_ t1 t2 => exact ih acc

helper /-- litSetUnifTerms of a substituted literal list equals the pointwise
    substitution of the original unification terms. -/
theorem litSetUnifTerms_substLits {L : Language} (hNoEq : L.withoutEquality)
    (sigma : Nat → Term L) (lits : List (FOLiteral L hNoEq)) :
    (litSetUnifTerms (hNoEq := by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) sigma lits) =
    ((litSetUnifTerms (hNoEq := by all_goals exact hNoEq)) lits).map (fun t => termSubstAll t sigma) := by
-- BEGIN PROOF
  unfold litSetUnifTerms
  have := (litSetUnifTerms_substLits_foldl (hNoEq := by all_goals exact hNoEq)) sigma lits ([] : List (Term L))
  simp only [List.map_nil] at this
  exact this



end LCS.FOResolution.Method.Completeness

end
