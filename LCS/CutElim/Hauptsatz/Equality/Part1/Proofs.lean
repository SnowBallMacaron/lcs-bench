import LCS.CutElim.Hauptsatz.Equality.Part1

section

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SyntaxN.Substitution LCS.FirstOrder.SyntaxN.Variables

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

open LCS

namespace LCS.CutElim.Hauptsatz.Equality

namespace G1nnfEqAxiom



helper /-- A non-atomic formula can never be used for negation-right closure. -/
theorem G1nnfEqAxiom.wellFormed_negRight_rejects_nonAtomic {L : Language}
    {hL : L.hasEquality = true} (base : G1nnfEqAxiom L hL)
    (A B : FormulaN L) :
    ¬ (G1nnfEqAxiom.negRight base (.conj A B)).WellFormed := by
  simp [WellFormed, FormulaN.isAtomic]

helper /-- Negation-left closure rejects an atom absent from its source succedent. -/
theorem G1nnfEqAxiom.wellFormed_negLeft_rejects_absentSource {L : Language}
    {hL : L.hasEquality = true} (base : G1nnfEqAxiom L hL)
    (A : FormulaN L) (hAbsent : A ∉ base.toSequent.2) :
    ¬ (G1nnfEqAxiom.negLeft base A).WellFormed := by
  intro hWF
  exact hAbsent hWF.2.2.2

helper /-- Negation-right closure rejects an atom absent from its source antecedent. -/
theorem G1nnfEqAxiom.wellFormed_negRight_rejects_absentSource {L : Language}
    {hL : L.hasEquality = true} (base : G1nnfEqAxiom L hL)
    (A : FormulaN L) (hAbsent : A ∉ base.toSequent.1) :
    ¬ (G1nnfEqAxiom.negRight base A).WellFormed := by
  intro hWF
  exact hAbsent hWF.2.2.2

helper /-- Even an occurring positive atom is rejected when it belongs only to an
ambient context rather than to the equality schema's designated atoms. -/
theorem G1nnfEqAxiom.wellFormed_negClosure_rejects_ineligible {L : Language}
    {hL : L.hasEquality = true} (base : G1nnfEqAxiom L hL)
    (A : FormulaN L) (hIneligible : ¬ base.IsEligibleAtom A) :
    ¬ (G1nnfEqAxiom.negLeft base A).WellFormed ∧
      ¬ (G1nnfEqAxiom.negRight base A).WellFormed := by
  constructor <;> intro hWF <;> exact hIneligible hWF.2.1

helper /-- Adversarial regression: an unrelated positive atomic formula contributed
by `Gamma` is present on the negation-right source side, but is not a
designated atom of the reflexivity schema and therefore cannot be moved. -/
theorem G1nnfEqAxiom.wellFormed_refl_rejects_unrelatedContextAtom {L : Language}
    {hL : L.hasEquality = true} (t : Term L) (C : FormulaN L)
    (_hAtomic : C.isAtomic = true) (hDistinct : C ≠ .eq_ hL t t) :
    ¬ (G1nnfEqAxiom.negRight (hL := hL)
      (.refl (hL := hL) t (Finset.singleton C) Finset.empty) C).WellFormed := by
  intro hWF
  exact hDistinct hWF.2.1

helper /-- The dedicated equality-predicate congruence schema has exactly the
textbook sequent. -/
theorem G1nnfEqAxiom.toSequent_eqCong {L : Language} {hL : L.hasEquality = true}
    (s1 s2 t1 t2 : Term L) (Gamma Delta : Finset (FormulaN L)) :
    (G1nnfEqAxiom.eqCong (hL := hL) s1 s2 t1 t2 Gamma Delta).toSequent =
      (Finset.insert (.eq_ hL s1 s2)
        (Finset.union
          (Finset.ofList [.eq_ hL s1 t1, .eq_ hL s2 t2]) Gamma),
       Finset.insert (.eq_ hL t1 t2) Delta) :=
  rfl







helper /-- Concrete legal negation-right closure: move the source equality
`s1 = s2` from equality-predicate congruence to the succedent as its
negation. -/
noncomputable def G1nnfEqAxiom.legalNegRightExample {L : Language}
    (hL : L.hasEquality = true) (s1 s2 t1 t2 : Term L) :
    G1nnfEqAxiom L hL :=
  .negRight
    (.eqCong s1 s2 t1 t2 Finset.empty Finset.empty) (.eq_ hL s1 s2)

helper theorem G1nnfEqAxiom.legalNegRightExample_wellFormed {L : Language}
    (hL : L.hasEquality = true) (s1 s2 t1 t2 : Term L) :
    (legalNegRightExample hL s1 s2 t1 t2).WellFormed := by
  simp [legalNegRightExample, WellFormed, IsEligibleAtom, toSequent,
    FormulaN.isAtomic]

helper theorem G1nnfEqAxiom.legalNegRightExample_toSequent {L : Language}
    (hL : L.hasEquality = true) (s1 s2 t1 t2 : Term L) :
    (legalNegRightExample hL s1 s2 t1 t2).toSequent =
      (Finset.erase
        (Finset.insert (.eq_ hL s1 s2)
          (Finset.ofList [.eq_ hL s1 t1, .eq_ hL s2 t2]))
        (.eq_ hL s1 s2),
       Finset.insert (.neg (.eq_ hL s1 s2))
         (Finset.singleton (.eq_ hL t1 t2))) := by
  rfl

end G1nnfEqAxiom

end LCS.CutElim.Hauptsatz.Equality

end

section

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SyntaxN.Substitution LCS.FirstOrder.SyntaxN.Variables

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

open LCS

namespace LCS.CutElim.Hauptsatz.Equality

proof_of g1nnfEqAxiom_valid := by
  classical
  induction ax with
  | refl t Γ Δ =>
    intro M val _
    exact ⟨.eq_ hL t t, Finset.mem_insert.mpr (Or.inl rfl), rfl⟩
  | funCong f ss ts Γ Δ =>
    intro M val hΓ
    refine ⟨.eq_ hL (.func f ss) (.func f ts),
      Finset.mem_insert.mpr (Or.inl rfl), ?_⟩
    change M.interpFunc f (fun i => termEval M val (ss i)) =
      M.interpFunc f (fun i => termEval M val (ts i))
    congr 1
    funext i
    apply hΓ (.eq_ hL (ss i) (ts i))
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_ofList.mpr
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  | predCong P ss ts Γ Δ =>
    intro M val hΓ
    refine ⟨.predN P ts, Finset.mem_insert.mpr (Or.inl rfl), ?_⟩
    have hP := hΓ (.predN P ss) (Finset.mem_insert.mpr (Or.inl rfl))
    have heq : (fun i => termEval M val (ss i)) =
        (fun i => termEval M val (ts i)) := by
      funext i
      apply hΓ (.eq_ hL (ss i) (ts i))
      apply Finset.mem_insert.mpr
      right
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_ofList.mpr
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    change M.interpPred P (fun i => termEval M val (ts i))
    change M.interpPred P (fun i => termEval M val (ss i)) at hP
    rw [← heq]
    exact hP
  | eqCong s1 s2 t1 t2 Γ Δ =>
    intro M val hΓ
    refine ⟨.eq_ hL t1 t2, Finset.mem_insert.mpr (Or.inl rfl), ?_⟩
    have h1 := hΓ (.eq_ hL s1 t1) (by
      simp [G1nnfEqAxiom.toSequent])
    have h2 := hΓ (.eq_ hL s2 t2) (by
      simp [G1nnfEqAxiom.toSequent])
    have h3 := hΓ (.eq_ hL s1 s2) (Finset.mem_insert.mpr (Or.inl rfl))
    exact h1.symm.trans (h3.trans h2)
  | negLeft base A ih =>
    intro M val hΓ
    simp only [G1nnfEqAxiom.toSequent_negLeft] at hΓ ⊢
    have hnA := hΓ (.neg A) (Finset.mem_insert.mpr (Or.inl rfl))
    obtain ⟨B, hB, hEval⟩ := ih hW.1 M val
      (fun F hF => hΓ F (Finset.mem_insert.mpr (Or.inr hF)))
    refine ⟨B, (Finset.mem_erase A B base.toSequent.2).mpr ⟨hB, ?_⟩, hEval⟩
    intro hBA
    subst B
    exact hnA hEval
  | negRight base A ih =>
    intro M val hΓ
    simp only [G1nnfEqAxiom.toSequent_negRight] at hΓ ⊢
    by_cases hA : formulaEvalN M A val
    · obtain ⟨B, hB, hEval⟩ := ih hW.1 M val (by
        intro F hF
        by_cases hFA : F = A
        · subst F
          exact hA
        · exact hΓ F ((Finset.mem_erase A F base.toSequent.1).mpr ⟨hF, hFA⟩))
      exact ⟨B, Finset.mem_insert.mpr (Or.inr hB), hEval⟩
    · exact ⟨.neg A, Finset.mem_insert.mpr (Or.inl rfl), hA⟩


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

helper /-- Delegation regression: wrapping a base G1nnf rule preserves its side
conditions exactly. -/
theorem G1nnfEqRule.sideConditions_base_iff {L : Language} {hL : L.hasEquality = true}
    (r : G1nnfRule L) (Gamma Delta : Finset (FormulaN L)) :
    SideConditions (hL := hL) (.base r) Gamma Delta ↔
      r.SideConditions Gamma Delta :=
  Iff.rfl

helper /-- Admissibility regression: an equality-axiom wrapper requires exactly the
schema's recursive well-formedness predicate. -/
theorem G1nnfEqRule.sideConditions_eqAxiom_iff {L : Language} {hL : L.hasEquality = true}
    (ax : G1nnfEqAxiom L hL) (Gamma Delta : Finset (FormulaN L)) :
    SideConditions (.eqAxiom ax) Gamma Delta ↔ ax.WellFormed :=
  Iff.rfl







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

proof_of g1nnfEq_soundness := open LCS.FirstOrder.SemanticsN.Substitution in
  by
    classical
    induction T with
    | axiom_ rule Γ Δ hAxiom hAC =>
      cases rule with
      | eqAxiom ax => exact g1nnfEqAxiom_valid ax hAC.1
      | base rule =>
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
        | conjLeft1 A B => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hAxiom
        | conjLeft2 A B => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hAxiom
        | disjRight1 A B => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hAxiom
        | disjRight2 A B => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hAxiom
        | allLeft x A t => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hAxiom
        | allRight x A y => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hAxiom
        | exLeft x A y => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hAxiom
        | exRight x A t => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hAxiom
        | cut A Lam Theta => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hAxiom
        | conjRight A B => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hAxiom
        | disjLeft A B => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hAxiom
    | onePremise rule Γ Δ hPrem hAC sub ih =>
      cases rule with
      | eqAxiom ax => simp [G1nnfEqRule.premises] at hPrem
      | base rule =>
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
        | axiomPosAtomic A hAtom rΓ rΔ => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hPrem
        | axiomNegAtomic A hAtom rΓ rΔ => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hPrem
        | axiomCompLeft A hAtom rΓ rΔ => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hPrem
        | axiomCompRight A hAtom rΓ rΔ => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hPrem
        | cut A Lam Theta => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hPrem
        | conjRight A B => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hPrem
        | disjLeft A B => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hPrem
    | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
      cases rule with
      | eqAxiom ax => simp [G1nnfEqRule.premises] at hPrem
      | base rule =>
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
        | axiomPosAtomic A hAtom rΓ rΔ => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hPrem
        | axiomNegAtomic A hAtom rΓ rΔ => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hPrem
        | axiomCompLeft A hAtom rΓ rΔ => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hPrem
        | axiomCompRight A hAtom rΓ rΔ => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hPrem
        | conjLeft1 A B => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hPrem
        | conjLeft2 A B => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hPrem
        | disjRight1 A B => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hPrem
        | disjRight2 A B => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hPrem
        | allLeft x A t => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hPrem
        | allRight x A y => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hPrem
        | exLeft x A y => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hPrem
        | exRight x A t => simp [G1nnfEqRule.premises, G1nnfRule.premises] at hPrem


helper /-- Adversarial regression: the equality wrapper rejects the same nonfresh
universal-right application as the repaired base G1nnf carrier. -/
theorem g1nnfEqProofTree_rejects_nonfreshAllRight {L : Language}
    (hL : L.hasEquality = true) (x y : Nat) (A C : FormulaN L)
    (Delta : Finset (FormulaN L)) (hyC : y ∈ formulaFVN C) :
    ¬ G1nnfEqRule.SideConditions
      (hL := hL) (.base (.allRight x A y)) (Finset.singleton C) Delta :=
  G1nnfRule.sideConditions_allRight_rejects_nonfresh x y A C Delta hyC

helper /-- Adversarial carrier regression: an equality axiom's application contract
checks the schema's stored ambient contexts. Thus a stored implication cannot
be smuggled through a reflexivity leaf by supplying unrelated rule parameters. -/
theorem g1nnfEqProofTree_rejects_nonNNF_stored_eqAxiom_context {L : Language}
    (hL : L.hasEquality = true) (t : Term L) (A : FormulaN L) :
    ¬ G1nnfEqRule.ApplicationConditions (hL := hL)
      (.eqAxiom
        (.refl (hL := hL) t (Finset.singleton (.impl A A)) Finset.empty))
      Finset.empty Finset.empty := by
-- BEGIN PROOF
  intro hAC
  have hImpl : FormulaN.isNNF (.impl A A) :=
    hAC.2.left ((Finset.mem_singleton _ _).mpr rfl)
  exact hImpl

helper /-- Adversarial carrier regression: an implication cannot inhabit the first
premise of an internal equality-system cut. Consequently no cut on `A → A`
can be assembled from this formerly admissible malformed premise. -/
theorem g1nnfEqProofTree_rejects_internal_implication_cut {L : Language}
    (hL : L.hasEquality = true) (A : FormulaN L) :
    ¬ Nonempty
      (G1nnfEqProofTree hL
        (Finset.singleton A)
        (Finset.insert (.impl A A) (Finset.singleton A))) := by
-- BEGIN PROOF
  rintro ⟨T⟩
  exact G1nnfRule.finsetSequent_rejects_implication A T.conclusion_isNNF

helper /-- Positive regression: a base universal-right node with explicit legal
side-condition evidence remains constructible through the equality wrapper. -/
noncomputable def g1nnfEqProofTree_accepts_freshAllRight {L : Language}
    (hL : L.hasEquality = true) (x y : Nat) (A : FormulaN L)
    (Gamma Delta : Finset (FormulaN L))
    (hNNF : A.isNNF)
    (hFreeFor : isFreeForN (.var y) x A)
    (hFreshPrincipal : y ∉ formulaFVN (.all x A))
    (hFreshGamma : ∀ F ∈ Gamma, y ∉ formulaFVN F)
    (hFreshDelta : ∀ F ∈ Delta, y ∉ formulaFVN F)
    (sub : G1nnfEqProofTree hL Gamma
      (Finset.insert (formulaSubstN A (.var y) x) Delta)) :
    G1nnfEqProofTree hL Gamma (Finset.insert (.all x A) Delta) := by
-- BEGIN PROOF
  have hBase :
      G1nnfFinsetSequent.IsNNF (Gamma, Delta) :=
    ((G1nnfFinsetSequent.IsNNF.insert_right_iff
      (formulaSubstN A (.var y) x) Gamma Delta).1
      sub.conclusion_isNNF).2
  exact .onePremise (.base (.allRight x A y)) Gamma Delta rfl
    ((G1nnfEqRule.applicationConditions_base_iff
      (.allRight x A y) Gamma Delta).2
      ⟨G1nnfRule.sideConditions_allRight_of_fresh
          x y A Gamma Delta hFreeFor hFreshPrincipal hFreshGamma hFreshDelta,
        G1nnfFinsetSequent.IsNNF.insert_right hNNF hBase⟩)
    sub



helper /-- Positive regression: an ordinary base-system atomic axiom remains a
constructible zero-premise leaf through the equality wrapper. -/
noncomputable def g1nnfEqProofTree_accepts_baseAxiom {L : Language}
    (hL : L.hasEquality = true) (A : FormulaN L)
    (hAtom : A.isAtomic = true) (Gamma Delta : Finset (FormulaN L))
    (hNNF : G1nnfFinsetSequent.IsNNF (Gamma, Delta)) :
    G1nnfEqProofTree hL
      (Finset.insert A Gamma) (Finset.insert A Delta) := by
  have hANNNF : FormulaN.isNNF A := by
    cases A with
    | predN _ _ => trivial
    | eq_ _ _ _ => trivial
    | neg _ => simp [FormulaN.isAtomic] at hAtom
    | conj _ _ => simp [FormulaN.isAtomic] at hAtom
    | disj _ _ => simp [FormulaN.isAtomic] at hAtom
    | impl _ _ => simp [FormulaN.isAtomic] at hAtom
    | all _ _ => simp [FormulaN.isAtomic] at hAtom
    | ex _ _ => simp [FormulaN.isAtomic] at hAtom
  exact .axiom_ (.base (.axiomPosAtomic A hAtom Gamma Delta))
    Finset.empty Finset.empty rfl
    ((G1nnfEqRule.applicationConditions_base_iff
      (.axiomPosAtomic A hAtom Gamma Delta)
      Finset.empty Finset.empty).2
      ⟨trivial, G1nnfFinsetSequent.IsNNF.insert_right hANNNF
        (G1nnfFinsetSequent.IsNNF.insert_left hANNNF hNNF)⟩)



end LCS.CutElim.Hauptsatz.Equality

end

section

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SyntaxN.Substitution LCS.FirstOrder.SyntaxN.Variables

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

open LCS

namespace LCS.CutElim.Hauptsatz.Equality

namespace G1nnfEqAxiom

helper /-- Definition 6.4.6 (companion): A G1nnfEqAxiom is a negation
closure if it was obtained by applying negLeft or negRight to an
equality axiom schema. This is a structural classifier only;
`WellFormed` enforces admissibility. Returns True for the negLeft and
negRight constructors and False for the four base schemas. -/
def G1nnfEqAxiom.isNegClosure {L : Language} {hL : L.hasEquality = true} :
    G1nnfEqAxiom L hL → Prop
  | .negLeft _ _ => True
  | .negRight _ _ => True
  | .refl _ _ _ => False
  | .funCong _ _ _ _ _ => False
  | .predCong _ _ _ _ _ => False
  | .eqCong _ _ _ _ _ _ => False

end G1nnfEqAxiom

end LCS.CutElim.Hauptsatz.Equality

end
