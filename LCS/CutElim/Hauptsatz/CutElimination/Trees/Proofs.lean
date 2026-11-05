import LCS.CutElim.Hauptsatz.CutElimination.Trees

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

namespace LCS.CutElim.Hauptsatz

namespace G1nnfProofTree



end G1nnfProofTree

end LCS.CutElim.Hauptsatz

end

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

namespace LCS.CutElim.Hauptsatz

proof_of g1nnf_soundness := open LCS.FirstOrder.SemanticsN LCS.FirstOrder.SemanticsN.Substitution in
  by
    classical
    induction T with
    | axiom_ rule Γ Δ hAxiom hAC =>
      cases rule with
      | axiomPosAtomic A _ rΓ rΔ =>
        intro M val hΓ
        exact ⟨A, LCS.Finset.mem_insert.mpr (Or.inl rfl),
          hΓ A (LCS.Finset.mem_insert.mpr (Or.inl rfl))⟩
      | axiomNegAtomic A _ rΓ rΔ =>
        intro M val hΓ
        exact ⟨.neg A, LCS.Finset.mem_insert.mpr (Or.inl rfl),
          hΓ (.neg A) (LCS.Finset.mem_insert.mpr (Or.inl rfl))⟩
      | axiomCompLeft A _ rΓ rΔ =>
        intro M val hΓ
        have hA := hΓ A (LCS.Finset.mem_insert.mpr (Or.inl rfl))
        have hnA := hΓ (.neg A) (LCS.Finset.mem_insert.mpr
          (Or.inr (LCS.Finset.mem_insert.mpr (Or.inl rfl))))
        exact (hnA hA).elim
      | axiomCompRight A _ rΓ rΔ =>
        intro M val _
        by_cases hA : formulaEvalN M A val
        · exact ⟨A, LCS.Finset.mem_insert.mpr (Or.inl rfl), hA⟩
        · exact ⟨.neg A, LCS.Finset.mem_insert.mpr
            (Or.inr (LCS.Finset.mem_insert.mpr (Or.inl rfl))), hA⟩
      | conjLeft1 A B => simp [G1nnfRule.premises] at hAxiom
      | conjLeft2 A B => simp [G1nnfRule.premises] at hAxiom
      | disjRight1 A B => simp [G1nnfRule.premises] at hAxiom
      | disjRight2 A B => simp [G1nnfRule.premises] at hAxiom
      | allLeft x A t => simp [G1nnfRule.premises] at hAxiom
      | allRight x A y => simp [G1nnfRule.premises] at hAxiom
      | exLeft x A y => simp [G1nnfRule.premises] at hAxiom
      | exRight x A t => simp [G1nnfRule.premises] at hAxiom
      | cut A Lam Theta => simp [G1nnfRule.premises] at hAxiom
      | conjRight A B => simp [G1nnfRule.premises] at hAxiom
      | disjLeft A B => simp [G1nnfRule.premises] at hAxiom
    | onePremise rule Γ Δ hPrem hAC sub ih =>
      cases rule with
      | conjLeft1 A B =>
        intro M val hΓ
        apply ih M val
        intro F hF
        rcases LCS.Finset.mem_insert.mp hF with hEq | hF
        · subst F
          exact (hΓ (.conj A B) (LCS.Finset.mem_insert.mpr (Or.inl rfl))).1
        · exact hΓ F (LCS.Finset.mem_insert.mpr (Or.inr hF))
      | conjLeft2 A B =>
        intro M val hΓ
        apply ih M val
        intro F hF
        rcases LCS.Finset.mem_insert.mp hF with hEq | hF
        · subst F
          exact (hΓ (.conj A B) (LCS.Finset.mem_insert.mpr (Or.inl rfl))).2
        · exact hΓ F (LCS.Finset.mem_insert.mpr (Or.inr hF))
      | disjRight1 A B =>
        intro M val hΓ
        obtain ⟨F, hF, hEval⟩ := ih M val hΓ
        rcases LCS.Finset.mem_insert.mp hF with hEq | hF
        · subst F
          exact ⟨.disj A B, LCS.Finset.mem_insert.mpr (Or.inl rfl), Or.inl hEval⟩
        · exact ⟨F, LCS.Finset.mem_insert.mpr (Or.inr hF), hEval⟩
      | disjRight2 A B =>
        intro M val hΓ
        obtain ⟨F, hF, hEval⟩ := ih M val hΓ
        rcases LCS.Finset.mem_insert.mp hF with hEq | hF
        · subst F
          exact ⟨.disj A B, LCS.Finset.mem_insert.mpr (Or.inl rfl), Or.inr hEval⟩
        · exact ⟨F, LCS.Finset.mem_insert.mpr (Or.inr hF), hEval⟩
      | allLeft x A t =>
        intro M val hΓ
        apply ih M val
        intro F hF
        rcases LCS.Finset.mem_insert.mp hF with hEq | hF
        · subst F
          exact (formulaSubstEvalDirectN val A t x hAC.1).mpr
            (hΓ (.all x A) (LCS.Finset.mem_insert.mpr (Or.inl rfl)) (termEval M val t))
        · exact hΓ F (LCS.Finset.mem_insert.mpr (Or.inr hF))
      | exRight x A t =>
        intro M val hΓ
        obtain ⟨F, hF, hEval⟩ := ih M val hΓ
        rcases LCS.Finset.mem_insert.mp hF with hEq | hF
        · subst F
          exact ⟨.ex x A, LCS.Finset.mem_insert.mpr (Or.inl rfl),
            termEval M val t, (formulaSubstEvalDirectN val A t x hAC.1).mp hEval⟩
        · exact ⟨F, LCS.Finset.mem_insert.mpr (Or.inr hF), hEval⟩
      | allRight x A y =>
        intro M val hΓ
        obtain ⟨hFree, hPrincipal, hFreshΓ, hFreshΔ⟩ := hAC.1
        by_cases hΔ : ∃ B ∈ Δ, formulaEvalN M B val
        · obtain ⟨B, hB, hEval⟩ := hΔ
          exact ⟨B, LCS.Finset.mem_insert.mpr (Or.inr hB), hEval⟩
        · refine ⟨.all x A, LCS.Finset.mem_insert.mpr (Or.inl rfl), ?_⟩
          intro a
          have hΓy : ∀ F ∈ Γ, formulaEvalN M F (assignUpdate val y a) := by
            intro F hF
            exact (coincidenceLemmaN M F val (assignUpdate val y a)
              (fun z hz => by
                simp [assignUpdate]; intro hzy
                exact absurd (hzy ▸ hz) (hFreshΓ F hF))).mp (hΓ F hF)
          obtain ⟨B, hB, hEval⟩ := ih M (assignUpdate val y a) hΓy
          rcases LCS.Finset.mem_insert.mp hB with hEq | hB
          · subst B
            rw [formulaSubstEvalDirectN (assignUpdate val y a) A (.var y) x hFree] at hEval
            simp [termEval, assignUpdate] at hEval
            have yA : ∀ z, z ∈ formulaFVN A → z ≠ x → z ≠ y := by
              intro z hz hzx hzy
              subst z
              exact hPrincipal (by simp [formulaFVN]; exact ⟨hz, hzx⟩)
            exact (coincidenceLemmaN M A
              (fun k => if k = x then a else if k = y then a else val k)
              (assignUpdate val x a)
              (fun z hz => by
                simp [assignUpdate]
                split
                · rfl
                · rename_i hzx
                  split
                  · rename_i hzy
                    exact absurd hzy (yA z hz hzx)
                  · rfl)).mp hEval
          · have hBs : formulaEvalN M B val :=
              (coincidenceLemmaN M B (assignUpdate val y a) val
                (fun z hz => by
                  simp [assignUpdate]; intro hzy
                  exact absurd (hzy ▸ hz) (hFreshΔ B hB))).mp hEval
            exact (hΔ ⟨B, hB, hBs⟩).elim
      | exLeft x A y =>
        intro M val hΓ
        obtain ⟨hFree, hPrincipal, hFreshΓ, hFreshΔ⟩ := hAC.1
        obtain ⟨a, ha⟩ := hΓ (.ex x A) (LCS.Finset.mem_insert.mpr (Or.inl rfl))
        have yA : ∀ z, z ∈ formulaFVN A → z ≠ x → z ≠ y := by
          intro z hz hzx hzy
          subst z
          exact hPrincipal (by simp [formulaFVN]; exact ⟨hz, hzx⟩)
        have hAyx : formulaEvalN M (formulaSubstN A (.var y) x)
            (assignUpdate val y a) := by
          rw [formulaSubstEvalDirectN (assignUpdate val y a) A (.var y) x hFree]
          simp [termEval, assignUpdate]
          exact (coincidenceLemmaN M A (assignUpdate val x a)
            (fun k => if k = x then a else if k = y then a else val k)
            (fun z hz => by
              simp [assignUpdate]
              split
              · rfl
              · rename_i hzx
                split
                · rename_i hzy
                  exact absurd hzy (yA z hz hzx)
                · rfl)).mp ha
        obtain ⟨B, hB, hEval⟩ := ih M (assignUpdate val y a) (by
          intro F hF
          rcases LCS.Finset.mem_insert.mp hF with hEq | hF
          · subst F
            exact hAyx
          · exact (coincidenceLemmaN M F val (assignUpdate val y a)
              (fun z hz => by
                simp [assignUpdate]; intro hzy
                exact absurd (hzy ▸ hz) (hFreshΓ F hF))).mp
              (hΓ F (LCS.Finset.mem_insert.mpr (Or.inr hF))))
        exact ⟨B, hB,
          (coincidenceLemmaN M B (assignUpdate val y a) val
            (fun z hz => by
              simp [assignUpdate]; intro hzy
              exact absurd (hzy ▸ hz) (hFreshΔ B hB))).mp hEval⟩
      | axiomPosAtomic A hAtom rΓ rΔ => simp [G1nnfRule.premises] at hPrem
      | axiomNegAtomic A hAtom rΓ rΔ => simp [G1nnfRule.premises] at hPrem
      | axiomCompLeft A hAtom rΓ rΔ => simp [G1nnfRule.premises] at hPrem
      | axiomCompRight A hAtom rΓ rΔ => simp [G1nnfRule.premises] at hPrem
      | cut A Lam Theta => simp [G1nnfRule.premises] at hPrem
      | conjRight A B => simp [G1nnfRule.premises] at hPrem
      | disjLeft A B => simp [G1nnfRule.premises] at hPrem
    | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
      cases rule with
      | cut A Lam Theta =>
        intro M val hΓ
        obtain ⟨B, hB, hEval⟩ := ih1 M val
          (fun F hF => hΓ F (LCS.Finset.mem_union.mpr (Or.inl hF)))
        rcases LCS.Finset.mem_insert.mp hB with hEq | hB
        · subst B
          obtain ⟨C, hC, hCtrue⟩ := ih2 M val (by
            intro F hF
            rcases LCS.Finset.mem_insert.mp hF with hEq | hF
            · subst F
              exact hEval
            · exact hΓ F (LCS.Finset.mem_union.mpr (Or.inr hF)))
          exact ⟨C, LCS.Finset.mem_union.mpr (Or.inr hC), hCtrue⟩
        · exact ⟨B, LCS.Finset.mem_union.mpr (Or.inl hB), hEval⟩
      | conjRight A B =>
        intro M val hΓ
        obtain ⟨F, hF, hA⟩ := ih1 M val hΓ
        rcases LCS.Finset.mem_insert.mp hF with hEq | hF
        · subst F
          obtain ⟨F, hF, hB⟩ := ih2 M val hΓ
          rcases LCS.Finset.mem_insert.mp hF with hEq | hF
          · subst F
            exact ⟨.conj A B, LCS.Finset.mem_insert.mpr (Or.inl rfl), hA, hB⟩
          · exact ⟨F, LCS.Finset.mem_insert.mpr (Or.inr hF), hB⟩
        · exact ⟨F, LCS.Finset.mem_insert.mpr (Or.inr hF), hA⟩
      | disjLeft A B =>
        intro M val hΓ
        have hAB := hΓ (.disj A B) (LCS.Finset.mem_insert.mpr (Or.inl rfl))
        rcases hAB with hA | hB
        · apply ih1 M val
          intro F hF
          rcases LCS.Finset.mem_insert.mp hF with hEq | hF
          · subst F
            exact hA
          · exact hΓ F (LCS.Finset.mem_insert.mpr (Or.inr hF))
        · apply ih2 M val
          intro F hF
          rcases LCS.Finset.mem_insert.mp hF with hEq | hF
          · subst F
            exact hB
          · exact hΓ F (LCS.Finset.mem_insert.mpr (Or.inr hF))
      | axiomPosAtomic A hAtom rΓ rΔ => simp [G1nnfRule.premises] at hPrem
      | axiomNegAtomic A hAtom rΓ rΔ => simp [G1nnfRule.premises] at hPrem
      | axiomCompLeft A hAtom rΓ rΔ => simp [G1nnfRule.premises] at hPrem
      | axiomCompRight A hAtom rΓ rΔ => simp [G1nnfRule.premises] at hPrem
      | conjLeft1 A B => simp [G1nnfRule.premises] at hPrem
      | conjLeft2 A B => simp [G1nnfRule.premises] at hPrem
      | disjRight1 A B => simp [G1nnfRule.premises] at hPrem
      | disjRight2 A B => simp [G1nnfRule.premises] at hPrem
      | allLeft x A t => simp [G1nnfRule.premises] at hPrem
      | allRight x A y => simp [G1nnfRule.premises] at hPrem
      | exLeft x A y => simp [G1nnfRule.premises] at hPrem
      | exRight x A t => simp [G1nnfRule.premises] at hPrem


end LCS.CutElim.Hauptsatz

end

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

namespace LCS.CutElim.Hauptsatz

namespace G1nnfDeductionTree



end G1nnfDeductionTree

end LCS.CutElim.Hauptsatz

end

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

namespace LCS.CutElim.Hauptsatz

namespace G1nnfProofTree

proof_of cutRank_eq_zero_iff_hasNoCut :=   by
    induction T with
    | axiom_ rule Γ Δ hAxiom hAC =>
      cases rule <;> try (simp [G1nnfRule.premises] at hAxiom) <;>
        simp_all [cutRank, hasNoCut, G1nnfRule.cutFormula, G1nnfRule.premises]
    | onePremise rule Γ Δ hPrem hAC sub ih =>
      cases rule <;> try (simp [G1nnfRule.premises] at hPrem) <;>
        simp_all [cutRank, hasNoCut, G1nnfRule.cutFormula, G1nnfRule.premises]
    | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
      cases rule <;>
        simp_all [cutRank, hasNoCut, G1nnfRule.cutFormula, G1nnfRule.premises]


end G1nnfProofTree

end LCS.CutElim.Hauptsatz

end

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

namespace LCS.CutElim.Hauptsatz

namespace G1nnfRule

helper /-- Regression: universal-right side conditions on an antecedent extended
by `C` force the eigenvariable to be absent from `FV(C)`. -/
theorem CutElim.Hauptsatz.G1nnfRule.sideConditions_allRight_insert_left_fresh {L : Language}
    (x ev : Nat) (A C : FormulaN L)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (hSC :
      SideConditions (.allRight x A ev)
        (LCS.Finset.insert C Gamma) Delta) :
    ev ∉ formulaFVN C := by
-- BEGIN PROOF
  exact hSC.2.2.1 C (LCS.Finset.mem_insert.mpr (Or.inl rfl))

helper /-- Regression: existential-left side conditions on a succedent extended
by `C` force the eigenvariable to be absent from `FV(C)`. -/
theorem CutElim.Hauptsatz.G1nnfRule.sideConditions_exLeft_insert_right_fresh {L : Language}
    (x ev : Nat) (A C : FormulaN L)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (hSC :
      SideConditions (.exLeft x A ev)
        Gamma (LCS.Finset.insert C Delta)) :
    ev ∉ formulaFVN C := by
-- BEGIN PROOF
  exact hSC.2.2.2 C (LCS.Finset.mem_insert.mpr (Or.inl rfl))

end G1nnfRule

end LCS.CutElim.Hauptsatz

end

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

namespace LCS.CutElim.Hauptsatz

helper /-- Adversarial regression for the former unsound constructor path:
the axiom premise `P(v₁) ⇒ P(v₁)` is legal. -/
noncomputable def CutElim.Hauptsatz.g1nnfProofTree_nonfreshAllRight_premise :
    G1nnfProofTree nnfExLang_withoutEquality
      (LCS.Finset.singleton
        (FormulaN.predN (L := nnfExLang) NnfExPred.P (nnfVec1 1)))
      (LCS.Finset.singleton
        (FormulaN.predN (L := nnfExLang) NnfExPred.P (nnfVec1 1))) :=
  .axiom_
    (.axiomPosAtomic
      (FormulaN.predN (L := nnfExLang) NnfExPred.P (nnfVec1 1)) rfl
      LCS.Finset.empty LCS.Finset.empty)
    LCS.Finset.empty LCS.Finset.empty rfl
    (G1nnfRule.applicationConditions_axiomPosAtomic_empty _ rfl)

helper /-- Adversarial regression for the former unsound constructor path:
the next universal-right step from `P(v₁) ⇒ P(v₁)` to
`P(v₁) ⇒ ∀v₀, P(v₀)` is rejected because its required constructor
side-condition evidence is impossible. -/
theorem CutElim.Hauptsatz.g1nnfProofTree_rejects_nonfreshAllRight :
    ¬ G1nnfRule.SideConditions
      (.allRight 0
        (FormulaN.predN (L := nnfExLang) NnfExPred.P (nnfVec1 0)) 1)
      (LCS.Finset.singleton
        (FormulaN.predN (L := nnfExLang) NnfExPred.P (nnfVec1 1)))
      LCS.Finset.empty := by
-- BEGIN PROOF
  apply G1nnfRule.sideConditions_allRight_rejects_nonfresh
  change ∃ j : Fin 1, 1 ∈ termFV (nnfVec1 1 j)
  exact ⟨⟨0, by omega⟩, rfl⟩

helper /-- Adversarial carrier regression: an implication cannot inhabit the first
premise of an internal cut. Consequently no cut on `A → A` can be assembled
from this formerly admissible malformed premise. -/
theorem CutElim.Hauptsatz.g1nnfProofTree_rejects_internal_implication_cut {L : Language} {hL : L.withoutEquality}
    (A : FormulaN L) :
    ¬ Nonempty
      (G1nnfProofTree hL
        (LCS.Finset.singleton A)
        (LCS.Finset.insert (.impl A A) (LCS.Finset.singleton A))) := by
-- BEGIN PROOF
  rintro ⟨T⟩
  exact G1nnfRule.finsetSequent_rejects_implication A T.conclusion_isNNF

helper /-- Adversarial carrier regression: an axiom's application contract checks
the rule's stored conclusion contexts, not merely its ambient parameters.
Thus a stored implication cannot be smuggled through an atomic axiom leaf. -/
theorem CutElim.Hauptsatz.g1nnfProofTree_rejects_nonNNF_stored_axiom_context {L : Language}
    (A : FormulaN L) (hAtom : A.isAtomic = true) :
    ¬ G1nnfRule.ApplicationConditions
      (.axiomPosAtomic A hAtom LCS.Finset.empty
        (LCS.Finset.singleton (.impl A A)))
      LCS.Finset.empty LCS.Finset.empty := by
-- BEGIN PROOF
  intro hAC
  have hImpl : FormulaN.isNNF (.impl A A) :=
    hAC.2.right (LCS.Finset.mem_insert.mpr
      (Or.inr ((LCS.Finset.mem_singleton _ _).mpr rfl)))
  exact hImpl

helper /-- Positive regression: a universal-right node with a legal premise and
explicitly fresh eigenvariable remains constructible. -/
noncomputable def CutElim.Hauptsatz.g1nnfProofTree_accepts_freshAllRight {L : Language} {hL : L.withoutEquality}
    (x ev : Nat) (A : FormulaN L)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (hNNF : A.isNNF)
    (hFreeFor : isFreeForN (.var ev) x A)
    (hFreshPrincipal : ev ∉ formulaFVN (.all x A))
    (hFreshGamma : ∀ F ∈ Gamma, ev ∉ formulaFVN F)
    (hFreshDelta : ∀ F ∈ Delta, ev ∉ formulaFVN F)
    (sub : G1nnfProofTree hL Gamma
      (LCS.Finset.insert (formulaSubstN A (.var ev) x) Delta)) :
    G1nnfProofTree hL Gamma
      (LCS.Finset.insert (.all x A) Delta) := by
-- BEGIN PROOF
  have hBase :
      G1nnfFinsetSequent.IsNNF (Gamma, Delta) :=
    ((G1nnfFinsetSequent.IsNNF.insert_right_iff
      (formulaSubstN A (.var ev) x) Gamma Delta).1
      sub.conclusion_isNNF).2
  exact .onePremise (.allRight x A ev) Gamma Delta rfl
    ⟨G1nnfRule.sideConditions_allRight_of_fresh
        x ev A Gamma Delta hFreeFor hFreshPrincipal hFreshGamma hFreshDelta,
      G1nnfFinsetSequent.IsNNF.insert_right hNNF hBase⟩
    sub

helper /-- Positive regression: an existential-left node with a legal premise and
explicitly fresh eigenvariable remains constructible. -/
noncomputable def CutElim.Hauptsatz.g1nnfProofTree_accepts_freshExLeft {L : Language} {hL : L.withoutEquality}
    (x ev : Nat) (A : FormulaN L)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (hNNF : A.isNNF)
    (hFreeFor : isFreeForN (.var ev) x A)
    (hFreshPrincipal : ev ∉ formulaFVN (.ex x A))
    (hFreshGamma : ∀ F ∈ Gamma, ev ∉ formulaFVN F)
    (hFreshDelta : ∀ F ∈ Delta, ev ∉ formulaFVN F)
    (sub : G1nnfProofTree hL
      (LCS.Finset.insert (formulaSubstN A (.var ev) x) Gamma) Delta) :
    G1nnfProofTree hL
      (LCS.Finset.insert (.ex x A) Gamma) Delta := by
-- BEGIN PROOF
  have hBase :
      G1nnfFinsetSequent.IsNNF (Gamma, Delta) :=
    ((G1nnfFinsetSequent.IsNNF.insert_left_iff
      (formulaSubstN A (.var ev) x) Gamma Delta).1
      sub.conclusion_isNNF).2
  exact .onePremise (.exLeft x A ev) Gamma Delta rfl
    ⟨G1nnfRule.sideConditions_exLeft_of_fresh
        x ev A Gamma Delta hFreeFor hFreshPrincipal hFreshGamma hFreshDelta,
      G1nnfFinsetSequent.IsNNF.insert_left hNNF hBase⟩
    sub

end LCS.CutElim.Hauptsatz

end
