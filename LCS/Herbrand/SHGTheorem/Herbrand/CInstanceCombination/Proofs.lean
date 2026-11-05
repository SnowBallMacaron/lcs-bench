import LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination

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



helper /-- Lemma 7.6.1, literal case: the only c-instance of a literal is
itself. The combination sequent is provable in G1nnf without equality and
in G1nnf= with equality. This asserts existence, not an effective algorithm. -/
theorem cInstance_combination_literal {L : Language}
    [DecidableEq (FormulaN L)]
    (A : FormulaN L)
    (hLit : A.isAtomic ∨ (∃ B, A = .neg B ∧ B.isAtomic))
    (K Ls : FormulaN L)
    (hK : isCInstanceOf K A) (hL : isCInstanceOf Ls A) :
    (∀ hNoEq : L.withoutEquality,
      ∃ D, isCInstanceOf D A ∧
        Nonempty (G1nnfProofTree hNoEq
          ({D} : LCS.Finset (FormulaN L))
          ({FormulaN.conj K Ls} : LCS.Finset (FormulaN L)))) ∧
    (∀ hEq : L.hasEquality = true,
      ∃ D, isCInstanceOf D A ∧
        Nonempty (LCS.CutElim.Hauptsatz.Equality.G1nnfEqProofTree hEq
          ({D} : LCS.Finset (FormulaN L))
          ({FormulaN.conj K Ls} : LCS.Finset (FormulaN L)))) := by
  have hk := literal_cinstance_eq A hLit K hK
  have hl := literal_cinstance_eq A hLit Ls hL
  subst K; subst Ls
  have hNNF : A.isNNF := by
    rcases hLit with hAtom | ⟨B, rfl, hAtom⟩
    · cases A <;> simp_all [FormulaN.isAtomic, FormulaN.isNNF]
    · cases B <;> simp_all [FormulaN.isAtomic, FormulaN.isNNF]
  constructor
  · intro hNoEq
    have hIdA : Nonempty (G1nnfProofTree hNoEq {A} {A}) := by
      rcases hLit with hAtom | ⟨B, rfl, hAtom⟩
      · exact ⟨.axiom_ (.axiomPosAtomic A hAtom ∅ ∅) ∅ ∅ rfl
          ⟨trivial, allNNF_singletons hNNF hNNF⟩⟩
      · exact ⟨.axiom_ (.axiomNegAtomic B hAtom ∅ ∅) ∅ ∅ rfl
          ⟨trivial, allNNF_singletons hNNF hNNF⟩⟩
    obtain ⟨idA⟩ := hIdA
    exact ⟨A, hK, ⟨.twoPremise (.conjRight A A) {A} ∅ rfl
      ⟨trivial, allNNF_singletons hNNF ⟨hNNF, hNNF⟩⟩ idA idA⟩⟩
  · intro hEq
    have hIdA : Nonempty (LCS.CutElim.Hauptsatz.Equality.G1nnfEqProofTree hEq {A} {A}) := by
      rcases hLit with hAtom | ⟨B, rfl, hAtom⟩
      · exact ⟨.axiom_ (.base (.axiomPosAtomic A hAtom ∅ ∅)) ∅ ∅ rfl
          ⟨trivial, allNNF_singletons hNNF hNNF⟩⟩
      · exact ⟨.axiom_ (.base (.axiomNegAtomic B hAtom ∅ ∅)) ∅ ∅ rfl
          ⟨trivial, allNNF_singletons hNNF hNNF⟩⟩
    obtain ⟨idA⟩ := hIdA
    exact ⟨A, hK, ⟨.twoPremise (.base (.conjRight A A)) {A} ∅ rfl
      ⟨trivial, allNNF_singletons hNNF ⟨hNNF, hNNF⟩⟩ idA idA⟩⟩

proof_of cInstance_combination := by
  have hShape : isSkolemNormalFormShape B := hSkolem.1
  clear hSkolem
  constructor
  · intro hNoEq
    induction B generalizing K Ls with
    | predN P args =>
        exact (cInstance_combination_literal (.predN P args)
          (Or.inl rfl) K Ls hK hL).1 hNoEq
    | eq_ hEq t₁ t₂ =>
        exact (cInstance_combination_literal (.eq_ hEq t₁ t₂)
          (Or.inl rfl) K Ls hK hL).1 hNoEq
    | neg A =>
        exact (cInstance_combination_literal (.neg A)
          (Or.inr ⟨A, rfl, hShape⟩) K Ls hK hL).1 hNoEq
    | conj B C ihB ihC =>
        exact (cInstance_combination_connective B C true
          (.conj B C) rfl K Ls hK hL).1 hNoEq
          (fun K' Ls' hK' hL' => ihB hNNF.1 K' Ls' hK' hL' hShape.1)
          (fun K' Ls' hK' hL' => ihC hNNF.2 K' Ls' hK' hL' hShape.2)
    | disj B C ihB ihC =>
        exact (cInstance_combination_connective B C false
          (.disj B C) rfl K Ls hK hL).1 hNoEq
          (fun K' Ls' hK' hL' => ihB hNNF.1 K' Ls' hK' hL' hShape.1)
          (fun K' Ls' hK' hL' => ihC hNNF.2 K' Ls' hK' hL' hShape.2)
    | impl _ _ _ _ => exact hNNF.elim
    | all x C ih =>
        exact (cInstance_combination_universal x C K Ls hK hL).1 hNoEq
    | ex _ _ _ => exact hShape.elim
  · intro hEq
    induction B generalizing K Ls with
    | predN P args =>
        exact (cInstance_combination_literal (.predN P args)
          (Or.inl rfl) K Ls hK hL).2 hEq
    | eq_ hEq t₁ t₂ =>
        exact (cInstance_combination_literal (.eq_ hEq t₁ t₂)
          (Or.inl rfl) K Ls hK hL).2 hEq
    | neg A =>
        exact (cInstance_combination_literal (.neg A)
          (Or.inr ⟨A, rfl, hShape⟩) K Ls hK hL).2 hEq
    | conj B C ihB ihC =>
        exact (cInstance_combination_connective B C true
          (.conj B C) rfl K Ls hK hL).2 hEq
          (fun K' Ls' hK' hL' => ihB hNNF.1 K' Ls' hK' hL' hShape.1)
          (fun K' Ls' hK' hL' => ihC hNNF.2 K' Ls' hK' hL' hShape.2)
    | disj B C ihB ihC =>
        exact (cInstance_combination_connective B C false
          (.disj B C) rfl K Ls hK hL).2 hEq
          (fun K' Ls' hK' hL' => ihB hNNF.1 K' Ls' hK' hL' hShape.1)
          (fun K' Ls' hK' hL' => ihC hNNF.2 K' Ls' hK' hL' hShape.2)
    | impl _ _ _ _ => exact hNNF.elim
    | all x C ih =>
        exact (cInstance_combination_universal x C K Ls hK hL).2 hEq
    | ex _ _ _ => exact hShape.elim


helper /-- The antecedent at an actual midsequent occurrence is itself the
conclusion of an indexed G2nnf proof with empty succedent. The tree is
the exact occurrence stored by `IsMidsequentG2nnf`; emptiness follows
from the quantifier-only path below that occurrence. -/
theorem midsequentAntecedentProvable {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {B : FormulaN L}
    (T : G2nnfProofTree hNoEq
      ({B} : LCS.Finset (FormulaN L))
      (∅ : LCS.Finset (FormulaN L)))
    (mid : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L))
    (hMid : IsMidsequentG2nnf T mid) :
    Nonempty (G2nnfProofTree hNoEq
      mid.1 (∅ : LCS.Finset (FormulaN L))) := by
  rcases hMid.midOccurrence with
    ⟨occurrence, _hAbove, hQuantifier⟩
  have hSuccedent :
      mid.2 = (∅ : LCS.Finset (FormulaN L)) :=
    G2nnfProofTree.succedent_eq_empty_of_quantifierPath
      occurrence.path hQuantifier rfl
  refine ⟨?_⟩
  rw [← hSuccedent]
  exact occurrence.node

helper /-- Lemma 7.6.2 (companion theorem): The intermediate result: given
a proof of `B ->` and a nonempty c-instance enumeration of an actual
midsequent antecedent, the sequent `C_1, ..., C_m ->` is provable.
This theorem performs only the index transport from the exact
midsequent subtree to the finset represented by `Cs`. -/
theorem midsequentCInstancesProvable {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (B : FormulaN L)
    (T : G2nnfProofTree hNoEq
      ({B} : LCS.Finset (FormulaN L))
      (∅ : LCS.Finset (FormulaN L)))
    (mid : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L))
    (Cs : List (FormulaN L))
    (hMid : IsMidsequentG2nnf T mid ∧
      mid.2 = (∅ : LCS.Finset (FormulaN L)) ∧ Cs ≠ [] ∧
      LCS.Finset.ofList Cs = mid.1 ∧ (∀ C ∈ Cs, isCInstanceOf C B)) :
    Nonempty (G2nnfProofTree hNoEq
      (LCS.Finset.ofList Cs)
      (∅ : LCS.Finset (FormulaN L))) := by
  rcases hMid with ⟨hIsMid, _, _, hCs, _⟩
  rw [hCs]
  exact midsequentAntecedentProvable (hNoEq := hNoEq) T mid hIsMid

helper /-- A repaired midsequent extraction is semantically unsatisfiable:
in every structure and assignment, at least one listed c-instance is
false. This is the empty-succedent instance of G2nnf soundness,
applied to the exact projected midsequent tree. -/
theorem midsequentCInstancesSemanticallyUnsatisfiable {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (B : FormulaN L)
    (T : G2nnfProofTree hNoEq
      ({B} : LCS.Finset (FormulaN L))
      (∅ : LCS.Finset (FormulaN L)))
    (mid : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L))
    (Cs : List (FormulaN L))
    (hMid : IsMidsequentG2nnf T mid ∧
      mid.2 = (∅ : LCS.Finset (FormulaN L)) ∧ Cs ≠ [] ∧
      LCS.Finset.ofList Cs = mid.1 ∧ (∀ C ∈ Cs, isCInstanceOf C B)) :
    ∀ (M : Structure L) (s : Assignment M),
      ∃ C ∈ Cs, ¬ formulaEvalN M C s := by
  rcases hMid with ⟨hIsMid, _, _, hCs, _⟩
  obtain ⟨midTree⟩ :=
    midsequentAntecedentProvable (hNoEq := hNoEq) T mid hIsMid
  have projectedTree :
      G2nnfProofTree hNoEq
        (LCS.Finset.ofList Cs)
        (∅ : LCS.Finset (FormulaN L)) := by
    rw [hCs]
    exact midTree
  intro M s
  apply Classical.byContradiction
  intro hNoFalse
  apply
    LCS.Herbrand.NNFHauptsatz.Soundness.g2nnf_tree_soundness
      hNoEq M projectedTree
  refine ⟨s, ?_, ?_⟩
  · intro C hC
    apply Classical.byContradiction
    intro hFalse
    exact hNoFalse
      ⟨C, LCS.Finset.mem_ofList.mp hC, hFalse⟩
  · intro C hC
    exact (LCS.Finset.not_mem_empty hC).elim















end LCS.Herbrand.SHGTheorem.Herbrand

end
