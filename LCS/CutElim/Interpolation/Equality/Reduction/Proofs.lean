import LCS.CutElim.Interpolation.Equality.Reduction

section

namespace LCS.CutElim.Interpolation.Equality

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.SignedFormulae

open LCS.CutElim.LK

open LCS.CutElim.LKe

open LCS.CutElim.LKe.Equivalence

open LCS.CutElim.Interpolation

open LCS.FirstOrder.Completeness

open LCS.FirstOrder.Equality

open LCS.FirstOrder.Equality.Completeness

open LCS.FirstOrder.Gentzen.Hintikka

helper /-- Lemma 6.5.4 (companion): Every formula in
closedEqualityAxioms S has no free variables. The closed
reflexivity axiom, function congruence axioms, and predicate
congruence axioms are all universally quantified, hence
closed. -/
theorem se_formulae_closed {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L) :
    ∀ A ∈ closedEqualityAxioms hL S,
      formulaFVN A = ∅ :=
-- BEGIN PROOF
by
  intro A hA
  simp only [closedEqualityAxioms] at hA
  rcases List.mem_append.mp hA with hLeft | hRight
  · rcases List.mem_append.mp hLeft with hRefl | hFun
    · simp only [List.mem_singleton] at hRefl
      subst hRefl
      simp only [closedReflAxiom, formulaFVN, termFV]
      ext v
      simp only [Set.diff, Set.union, Set.singleton, Set.empty]
      exact ⟨fun ⟨h1, h2⟩ => h2 (h1.elim id id), fun h => h.elim⟩
    · rw [List.mem_map] at hFun
      obtain ⟨f, _, hfEq⟩ := hFun
      subst hfEq
      exact closedFunCongAxiom_closed hL f
  · rcases List.mem_append.mp hRight with hPred | hEq
    · rw [List.mem_map] at hPred
      obtain ⟨P, _, hPEq⟩ := hPred
      subst hPEq
      exact closedPredCongAxiom_closed hL P
    · have hEq := eq_of_mem_optionalSingleton _ hEq
      subst hEq
      exact closedEqCongAxiom_closed hL

helper /-- Lemma 6.5.4 (companion): The negation of the reflexivity axiom
neg(forall z (z = z)) is unsatisfiable in LKe. The sequent
[neg(forall z (z=z))] -> [] is LKe-provable via semantic validity
(since forall z (z=z) is universally valid). FormulaN has no
falsum constructor, so the original bot equivalence is expressed
as unsatisfiability of the negated reflexivity formula. -/
theorem neg_refl_lke_unsat {L : Language} (hL : L.hasEquality = true) (z : Nat) :
    let negRefl : FormulaN L :=
      FormulaN.neg (FormulaN.all z
        (FormulaN.eq_ hL (Term.var z) (Term.var z)))
    lkeProvable (Sequent.mk [negRefl] []) :=
-- BEGIN PROOF
by
  intro negRefl
  apply lkeProvable_of_sequentValid
  intro M s hAnte
  have hNeg := hAnte _ (List.Mem.head _)
  exfalso; apply hNeg; intro a; trivial



helper /-- Every `LK_bot`-provable sequent is valid in structures that interpret
the distinguished nullary predicate `botP` as false. -/
theorem lkBotProvable_validWithBotFalse {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    (s : Sequent L) (h : lkBotProvable botP hBotArity s) :
    sequentValidWithBotFalse botP hBotArity s := by
-- BEGIN PROOF
  obtain ⟨t⟩ := h
  exact folkBotProofTree_valid t

helper theorem closedReflAxiom_constSymbols_empty {L : Language} (hL : L.hasEquality = true) :
    formulaConstSymbolsN (closedReflAxiom (L := L) hL) = ∅ := by
-- BEGIN PROOF
  simp [formulaConstSymbolsN, closedReflAxiom, termConstSymbols]
  ext; simp [Set.union, Set.empty]

helper theorem closedReflAxiom_predSymbols_empty {L : Language} (hL : L.hasEquality = true) :
    formulaPredSymbolsN (closedReflAxiom (L := L) hL) = ∅ := by
-- BEGIN PROOF
  simp [formulaPredSymbolsN, closedReflAxiom]

helper theorem closedEqCongAxiom_constSymbols_empty {L : Language}
    (hL : L.hasEquality = true) :
    formulaConstSymbolsN (closedEqCongAxiom (L := L) hL) = ∅ := by
-- BEGIN PROOF
  simp only [closedEqCongAxiom, formulaConstSymbolsN_allList]
  ext c
  simp [eqCongruenceImplEq, formulaConstSymbolsN,
    termConstSymbols, Set.union, Set.empty]

helper theorem closedEqCongAxiom_predSymbols_empty {L : Language}
    (hL : L.hasEquality = true) :
    formulaPredSymbolsN (closedEqCongAxiom (L := L) hL) = ∅ := by
-- BEGIN PROOF
  simp only [closedEqCongAxiom, formulaPredSymbolsN_allList]
  ext P
  simp [eqCongruenceImplEq, formulaPredSymbolsN, Set.union, Set.empty]

helper theorem closedEqualityAxioms_constSymbols_empty {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L) (F : FormulaN L)
    (hF : F ∈ closedEqualityAxioms hL S) :
    formulaConstSymbolsN F = ∅ := by
-- BEGIN PROOF
  simp only [closedEqualityAxioms] at hF
  rcases List.mem_append.mp hF with hLeft | hRight
  · rcases List.mem_append.mp hLeft with hRefl | hFun
    · simp only [List.mem_singleton] at hRefl; subst hRefl
      exact closedReflAxiom_constSymbols_empty hL
    · rw [List.mem_map] at hFun; obtain ⟨f, _, rfl⟩ := hFun
      exact closedFunCongAxiom_constSymbols_empty hL f
  · rcases List.mem_append.mp hRight with hPred | hEq
    · rw [List.mem_map] at hPred; obtain ⟨P, _, rfl⟩ := hPred
      exact closedPredCongAxiom_constSymbols_empty hL P
    · have hEq := eq_of_mem_optionalSingleton _ hEq
      subst hEq
      exact closedEqCongAxiom_constSymbols_empty hL

helper theorem closedEqualityAxiomsForSide_constSymbols_empty {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (gamma delta : List (FormulaN L)) (F : FormulaN L)
    (hF : F ∈ closedEqualityAxiomsForSide hL gamma delta) :
    formulaConstSymbolsN F = ∅ := by
-- BEGIN PROOF
  simp only [closedEqualityAxiomsForSide] at hF
  rcases List.mem_append.mp hF with hLeft | hRight
  · rcases List.mem_append.mp hLeft with hRefl | hFun
    · simp only [List.mem_singleton] at hRefl; subst hRefl
      exact closedReflAxiom_constSymbols_empty hL
    · rw [List.mem_map] at hFun; obtain ⟨f, _, rfl⟩ := hFun
      exact closedFunCongAxiom_constSymbols_empty hL f
  · rcases List.mem_append.mp hRight with hPred | hEq
    · rw [List.mem_map] at hPred; obtain ⟨P, _, rfl⟩ := hPred
      exact closedPredCongAxiom_constSymbols_empty hL P
    · have hEq := eq_of_mem_optionalSingleton _ hEq
      subst hEq
      exact closedEqCongAxiom_constSymbols_empty hL

helper theorem conjoin_predSymbols_sub {L : Language}
    (hd : FormulaN L) (tl : List (FormulaN L))
    (S : Set L.predSymbols)
    (h : ∀ A ∈ hd :: tl, ∀ P, formulaPredSymbolsN A P → S P) :
    ∀ P, formulaPredSymbolsN (conjoinFormulae hd (hd :: tl)) P →
      S P := by
  induction tl generalizing hd with
  | nil => exact h hd List.mem_cons_self
  | cons x xs ih =>
    intro P hP
    rw [conjoin_cons_cons] at hP
    rcases hP with hh | ht
    · exact h hd List.mem_cons_self P hh
    · exact ih x (fun A hA => h A (List.mem_cons_of_mem hd hA)) P ht

helper theorem premises_predSymbols_sub {L : Language} (hL : L.hasEquality = true)
    (Q : L.predSymbols) :
    let n := L.predArity Q
    ∀ A ∈ (List.finRange n).map (fun (i : Fin n) =>
        FormulaN.eq_ hL (Term.var (i : Nat) : Term L)
          (Term.var (n + (i : Nat)))) ++
      [FormulaN.predN Q
        (fun (i : Fin n) => Term.var (i : Nat))],
    ∀ P, formulaPredSymbolsN A P → P = Q := by
-- BEGIN PROOF
  intro n A hA P hP
  rcases List.mem_append.mp hA with hEq | hPred
  · rw [List.mem_map] at hEq; obtain ⟨i, _, rfl⟩ := hEq
    simp only [formulaPredSymbolsN] at hP
    exact hP.elim
  · simp only [List.mem_singleton] at hPred; subst hPred
    simp only [formulaPredSymbolsN] at hP
    exact hP

helper theorem closedEqualityAxiomsForSide_predSymbols_sub {L : Language}
    (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (gamma delta : List (FormulaN L)) (F : FormulaN L)
    (hF : F ∈ closedEqualityAxiomsForSide hL gamma delta)
    (P : L.predSymbols) (hP : formulaPredSymbolsN F P) :
    P ∈ sequentPredSymbolsList
      { antecedent := gamma, succedent := delta } := by
-- BEGIN PROOF
  simp only [closedEqualityAxiomsForSide] at hF
  rcases List.mem_append.mp hF with hLeft | hRight
  · rcases List.mem_append.mp hLeft with hRefl | hFun
    · simp only [List.mem_singleton] at hRefl; subst hRefl
      rw [closedReflAxiom_predSymbols_empty hL] at hP; exact hP.elim
    · rw [List.mem_map] at hFun; obtain ⟨f, _, rfl⟩ := hFun
      rw [closedFunCongAxiom_predSymbols_empty hL f] at hP
      exact hP.elim
  · rcases List.mem_append.mp hRight with hPred | hEq
    · rw [List.mem_map] at hPred
      obtain ⟨Q, hQMem, rfl⟩ := hPred
      have hPeq : P = Q := by
        unfold closedPredCongAxiom at hP; simp only [] at hP
        rw [formulaPredSymbolsN_quantifyAll,
          formulaPredSymbolsN_quantifyAll] at hP
        generalize hprem : (List.finRange (L.predArity Q)).map _ ++
          [FormulaN.predN Q _] = premises at hP
        cases premises with
        | nil =>
          simp only [formulaPredSymbolsN] at hP
          exact hP
        | cons hd tl =>
          simp only [formulaPredSymbolsN] at hP
          rcases hP with hAnte | hCons
          · have hSub := conjoin_predSymbols_sub hd tl
              (fun R => R = Q) (fun A hA R hR =>
                premises_predSymbols_sub hL Q A (hprem ▸ hA) R hR)
            exact hSub P hAnte
          · exact hCons
      subst hPeq; exact hQMem
    · have hEq := eq_of_mem_optionalSingleton _ hEq
      subst hEq
      rw [closedEqCongAxiom_predSymbols_empty hL] at hP
      exact hP.elim

helper theorem formulaPredSyms_to_formulaPredSymbolsN {L : Language}
    (A : FormulaN L) (P : L.predSymbols)
    (h : P ∈ sequentPredSymbolsList.formulaPredSyms A) :
    formulaPredSymbolsN A P := by
-- BEGIN PROOF
  induction A with
  | predN Q ts =>
    simp [sequentPredSymbolsList.formulaPredSyms] at h
    simp [formulaPredSymbolsN]; exact h
  | eq_ t1 t2 =>
    simp [sequentPredSymbolsList.formulaPredSyms] at h
  | conj A B ihA ihB =>
    simp [sequentPredSymbolsList.formulaPredSyms,
      List.mem_append] at h
    simp [formulaPredSymbolsN]
    rcases h with hA | hB
    · exact Or.inl (ihA hA)
    · exact Or.inr (ihB hB)
  | disj A B ihA ihB =>
    simp [sequentPredSymbolsList.formulaPredSyms,
      List.mem_append] at h
    simp [formulaPredSymbolsN]
    rcases h with hA | hB
    · exact Or.inl (ihA hA)
    · exact Or.inr (ihB hB)
  | impl A B ihA ihB =>
    simp [sequentPredSymbolsList.formulaPredSyms,
      List.mem_append] at h
    simp [formulaPredSymbolsN]
    rcases h with hA | hB
    · exact Or.inl (ihA hA)
    · exact Or.inr (ihB hB)
  | neg A ih => exact ih h
  | all _ A ih => exact ih h
  | ex _ A ih => exact ih h

helper theorem sequentPredSymbolsList_to_listFormulaPredSymbols {L : Language}
    [DecidableEq L.predSymbols]
    (gamma delta : List (FormulaN L)) (P : L.predSymbols)
    (h : P ∈ sequentPredSymbolsList
      { antecedent := gamma, succedent := delta }) :
    listFormulaPredSymbols (gamma ++ delta) P := by
-- BEGIN PROOF
  simp only [sequentPredSymbolsList] at h
  rw [List.mem_eraseDups, List.mem_flatMap] at h
  obtain ⟨G, hGmem, hGP⟩ := h
  exact ⟨G, hGmem, formulaPredSyms_to_formulaPredSymbolsN G P hGP⟩

helper theorem closedEqualityAxiomsForSide_valid {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (gamma delta : List (FormulaN L)) (F : FormulaN L)
    (hF : F ∈ closedEqualityAxiomsForSide hL gamma delta) :
    ∀ (M : Structure L) (s : Assignment M),
      formulaEvalN M F s := by
-- BEGIN PROOF
  simp only [closedEqualityAxiomsForSide] at hF
  rcases List.mem_append.mp hF with hLeft | hRight
  · rcases List.mem_append.mp hLeft with hRefl | hFun
    · simp only [List.mem_singleton] at hRefl; subst hRefl
      intro M s
      simp [closedReflAxiom, formulaEvalN, termEval, assignUpdate]
    · rw [List.mem_map] at hFun; obtain ⟨f, _, rfl⟩ := hFun
      exact closedFunCongAxiom_eval hL f
  · rcases List.mem_append.mp hRight with hPred | hEq
    · rw [List.mem_map] at hPred
      obtain ⟨P, _, rfl⟩ := hPred
      exact closedPredCongAxiom_eval hL P
    · have hEq := eq_of_mem_optionalSingleton _ hEq
      subst hEq
      exact closedEqCongAxiom_eval hL

helper theorem closedEqualityAxiomsForSide_closed {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (gamma delta : List (FormulaN L)) (F : FormulaN L)
    (hF : F ∈ closedEqualityAxiomsForSide hL gamma delta) :
    formulaFVN F = ∅ := by
-- BEGIN PROOF
  simp only [closedEqualityAxiomsForSide] at hF
  rcases List.mem_append.mp hF with hLeft | hRight
  · rcases List.mem_append.mp hLeft with hRefl | hFun
    · simp only [List.mem_singleton] at hRefl; subst hRefl
      simp only [closedReflAxiom, formulaFVN, termFV]
      ext v
      simp only [Set.diff, Set.union, Set.singleton, Set.empty]
      exact ⟨fun ⟨h1, h2⟩ => h2 (h1.elim id id), fun h => h.elim⟩
    · rw [List.mem_map] at hFun; obtain ⟨f, _, rfl⟩ := hFun
      exact closedFunCongAxiom_closed hL f
  · rcases List.mem_append.mp hRight with hPred | hEq
    · rw [List.mem_map] at hPred
      obtain ⟨P, _, rfl⟩ := hPred
      exact closedPredCongAxiom_closed hL P
    · have hEq := eq_of_mem_optionalSingleton _ hEq
      subst hEq
      exact closedEqCongAxiom_closed hL

proof_of interpolation_key_lemma_equality := by
  -- BEGIN PROOF
    -- REPAIR(T6-V2-08): proof pending
    sorry


helper /-- A choice of the LKₑ interpolant supplied by Lemma 6.5.4. -/
noncomputable def interpolation_key_lemma_equality_witness {L : Language}
    (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (s : Sequent L)
    (hProv : lkeProvable s)
    (p : SequentPartition s) : FormulaN L :=
  Classical.choose (interpolation_key_lemma_equality hL botP hBotArity s hProv p)

helper /-- The chosen Lemma 6.5.4 witness satisfies `IsLKeInterpolant`,
including LKₑ-provability of both interpolant sequents. -/
theorem interpolation_key_lemma_equality_witness_spec {L : Language}
    (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (s : Sequent L)
    (hProv : lkeProvable s)
    (p : SequentPartition s) :
    IsLKeInterpolant hL botP hBotArity p
      (interpolation_key_lemma_equality_witness hL botP hBotArity s hProv p) :=
  Classical.choose_spec (interpolation_key_lemma_equality hL botP hBotArity s hProv p)

helper /-- Theorem 6.5.2 (required helper): The trivial partition of an
implication sequent `[A] -> [B]` into `Gamma_1 := [A]`,
`Delta_1 := []`, `Gamma_2 := []`, `Delta_2 := [B]`. This is the
partition used in the proof of Theorem 6.5.2 to reduce from Lemma
6.5.4. -/
def craig_interpolation_equality_partition {L : Language}
    (A B : FormulaN L) :
    SequentPartition ({ antecedent := [A], succedent := [B] } : Sequent L) :=
  { gamma1 := [A], delta1 := []
    gamma2 := [], delta2 := [B]
    gamma_partition := .left A .nil
    delta_partition := .right B .nil }

proof_of craig_interpolation_equality := by
  -- BEGIN PROOF
    -- Adjoin a fresh nullary predicate so that A and B are ⊥-free,
    -- lift the derivation, and apply interpolation_key_lemma_equality.
    -- Replace ⊥ in the interpolant by ¬∀z(z ≐ z) and lower the two
    -- LKₑ derivations back to LKₑ over the original language.
    -- REPAIR(T6-50): proof pending
    sorry


helper /-- A choice of the interpolant supplied by Theorem 6.5.2. -/
noncomputable def craig_interpolation_equality_witness {L : Language}
    (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (A B : FormulaN L)
    (hProv : lkeProvable
      { antecedent := [A], succedent := [B] }) : FormulaN L :=
  Classical.choose (craig_interpolation_equality hL A B hProv)

helper /-- The chosen Theorem 6.5.2 witness satisfies
`IsLKeImplicationInterpolant`. -/
theorem craig_interpolation_equality_witness_spec {L : Language}
    (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (A B : FormulaN L)
    (hProv : lkeProvable
      { antecedent := [A], succedent := [B] }) :
    IsLKeImplicationInterpolant A B
      (craig_interpolation_equality_witness hL A B hProv) :=
  Classical.choose_spec (craig_interpolation_equality hL A B hProv)

proof_of craig_interpolation_equality_strong := by
  -- REPAIR(T6-51): proof pending
  sorry


helper /-- Theorem 6.3.1 (companion): A valid sequent is LKₑ-provable.
This delegates to the semantic bridge `lkeProvable_of_valid`, which
closes a formula over its support language, obtains a proof there,
then lifts and decodes that proof using cuts. -/
theorem lkeProvableN_of_sequentValidN {L : Language} [Countable (Term L)]
    (seq : Sequent L)
    (hValid : sequentValid seq) :
    lkeProvable seq := by
-- BEGIN PROOF
  exact LCS.CutElim.LKe.Equivalence.lkeProvable_of_valid seq hValid

end LCS.CutElim.Interpolation.Equality

end
