import LCS.CutElim.Hauptsatz

namespace LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN.Substitution



end LCS.FirstOrder.SyntaxN

namespace LCS.CutElim.Hauptsatz

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Equivalence

helper /-- Restricting both sides of a finite-set sequent preserves the §6.1 convention. -/
theorem CutElim.Hauptsatz.finsetCrossNoFreeBound_mono {L : Language}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (hΓ : Γ' ⊆ Γ) (hΔ : Δ' ⊆ Δ)
    (hCross : finsetCrossNoFreeBound Γ Δ) :
    finsetCrossNoFreeBound Γ' Δ' := by
  intro x ⟨A, hA, hx⟩ B hB
  exact hCross x ⟨A, hA.elim (fun h => Or.inl (hΓ A h))
    (fun h => Or.inr (hΔ A h)), hx⟩ B
    (hB.elim (fun h => Or.inl (hΓ B h)) (fun h => Or.inr (hΔ B h)))

namespace G1nnfFinsetSequent

namespace IsNNF



end IsNNF

end G1nnfFinsetSequent

helper /-- Definition 6.4.2 (helper): Convert a list of formulae to a set.
Used to bridge between the list-based proof tree representation
and the set-based sequent type from Definition 6.4.2. -/
def CutElim.Hauptsatz.listAsSet {L : Language} (l : List (FormulaN L)) : Set (FormulaN L) :=
  fun x => x ∈ l

namespace G1nnfRule

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.Finset



helper /-- Unfolding characterization of legal G1nnf rule applications. -/
theorem CutElim.Hauptsatz.G1nnfRule.applicationConditions_iff {L : Language}
    (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L)) :
    ApplicationConditions rule Gamma Delta ↔
      SideConditions rule Gamma Delta ∧
        G1nnfFinsetSequent.IsNNF (rule.conclusion Gamma Delta) :=
  Iff.rfl

helper /-- A legal application satisfies the existing rule-specific side conditions. -/
theorem CutElim.Hauptsatz.G1nnfRule.applicationConditions_sideConditions {L : Language}
    {rule : G1nnfRule L} {Gamma Delta : LCS.Finset (FormulaN L)}
    (h : ApplicationConditions rule Gamma Delta) :
    SideConditions rule Gamma Delta :=
  h.1

helper /-- A legal application has an NNF conclusion sequent. -/
theorem CutElim.Hauptsatz.G1nnfRule.applicationConditions_conclusion_isNNF {L : Language}
    {rule : G1nnfRule L} {Gamma Delta : LCS.Finset (FormulaN L)}
    (h : ApplicationConditions rule Gamma Delta) :
    G1nnfFinsetSequent.IsNNF (rule.conclusion Gamma Delta) :=
  h.2





helper /-- Definition 6.4.2 (companion regression): A free-for witness is
exactly the positive side-condition evidence needed by universal-left. -/
theorem CutElim.Hauptsatz.G1nnfRule.sideConditions_allLeft_of_freeFor {L : Language}
    (x : Nat) (A : FormulaN L) (t : Term L)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (hFreeFor : isFreeForN t x A) :
    SideConditions (.allLeft x A t) Gamma Delta :=
  hFreeFor

helper /-- Definition 6.4.2 (companion regression): Universal-left rejects
substitution of `v₁` for `v₀` through a quantifier binding `v₁`,
because that substitution would capture the inserted variable. -/
theorem CutElim.Hauptsatz.G1nnfRule.sideConditions_allLeft_rejects_capture {L : Language}
    (B : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L)) :
    ¬ SideConditions (.allLeft 0 (.all 1 B) (.var 1)) Gamma Delta := by
-- BEGIN PROOF
  intro h
  change 0 = 1 ∨
    (¬ Membership.mem (termFV (Term.var 1)) 1 ∧ isFreeForN (.var 1) 0 B) at h
  rcases h with hEq | ⟨hNotFree, _⟩
  · cases hEq
  · exact hNotFree (show Membership.mem (Set.singleton 1) 1 from rfl)







helper /-- Definition 6.4.2 (companion regression): Existential-left rejects
the analogous non-fresh pattern whenever the eigenvariable occurs free
in a succedent formula. -/
theorem CutElim.Hauptsatz.G1nnfRule.sideConditions_exLeft_rejects_nonfresh {L : Language}
    (x y : Nat) (A C : FormulaN L)
    (Gamma : LCS.Finset (FormulaN L))
    (hyC : y ∈ formulaFVN C) :
    ¬ SideConditions (.exLeft x A y) Gamma (LCS.Finset.singleton C) := by
-- BEGIN PROOF
  intro h
  exact (h.2.2.2 C (by simp)) hyC

helper /-- Definition 6.4.2 (companion regression): A free-for witness is
exactly the positive side-condition evidence needed by existential-right. -/
theorem CutElim.Hauptsatz.G1nnfRule.sideConditions_exRight_of_freeFor {L : Language}
    (x : Nat) (A : FormulaN L) (t : Term L)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (hFreeFor : isFreeForN t x A) :
    SideConditions (.exRight x A t) Gamma Delta :=
  hFreeFor

helper /-- Definition 6.4.2 (companion regression): Existential-right rejects
substitution of `v₁` for `v₀` through a quantifier binding `v₁`,
because that substitution would capture the inserted variable. -/
theorem CutElim.Hauptsatz.G1nnfRule.sideConditions_exRight_rejects_capture {L : Language}
    (B : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L)) :
    ¬ SideConditions (.exRight 0 (.ex 1 B) (.var 1)) Gamma Delta := by
-- BEGIN PROOF
  intro h
  change 0 = 1 ∨
    (¬ Membership.mem (termFV (Term.var 1)) 1 ∧ isFreeForN (.var 1) 0 B) at h
  rcases h with hEq | ⟨hNotFree, _⟩
  · cases hEq
  · exact hNotFree (show Membership.mem (Set.singleton 1) 1 from rfl)

end G1nnfRule



proof_of nnfEx_subNnf1_spec := open LCS.CutElim.Hauptsatz.Proofs.CutElim.Hauptsatz in
  rfl


proof_of nnfEx_subNnf2_spec := open LCS.CutElim.Hauptsatz.Proofs.CutElim.Hauptsatz in
  rfl


proof_of nnfEx_formulaA_nnf_spec := open LCS.CutElim.Hauptsatz.Proofs.CutElim.Hauptsatz in
  rfl


helper /-- Lemma 6.4.1 (required helper): Every FormulaN and its negation
each have an NNF equivalent. -/
theorem CutElim.Hauptsatz.nnf_both {L : Language} (A : FormulaN L) :
    (∃ B : FormulaN L, FormulaN.isNNF B ∧ foLogEquivN A B) ∧
    (∃ B : FormulaN L, FormulaN.isNNF B ∧ foLogEquivN (FormulaN.neg A) B) :=
-- BEGIN PROOF
  ⟨⟨A.toNNF, A.toNNF_isNNF, A.toNNF_equiv⟩,
    ⟨(FormulaN.neg A).toNNF, (FormulaN.neg A).toNNF_isNNF,
      (FormulaN.neg A).toNNF_equiv⟩⟩

proof_of nnf_equivalence := open LCS.CutElim.Hauptsatz.Proofs.CutElim.Hauptsatz in
  -- BEGIN PROOF
    ⟨A.toNNF, A.toNNF_isNNF, A.toNNF_equiv⟩


end LCS.CutElim.Hauptsatz
