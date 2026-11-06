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

end LCS.Herbrand.SHGTheorem.Herbrand
end
