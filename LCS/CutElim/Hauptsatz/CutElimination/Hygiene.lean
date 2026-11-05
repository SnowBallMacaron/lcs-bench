import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.Trees
import LCS.CutElim.Hauptsatz.CutElimination.VariableSupport
import LCS.CutElim.Hauptsatz.CutElimination.FormulaRenaming
import LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
import LCS.CutElim.Hauptsatz.CutElimination.Substitution

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz
namespace G1nnfProofTree

private theorem no_ruleEigenlabel_of_zero_premises {L : Language}
    (rule : G1nnfRule L)
    (Γ Δ : LCS.Finset (FormulaN L))
    (hAxiom : (rule.premises Γ Δ).length = 0)
    (ev : Nat)
    (hEv : ruleEigenlabel rule = some ev) :
    False := by
  cases rule <;>
    simp [ruleEigenlabel, G1nnfRule.premises] at hAxiom hEv

private theorem eigenvariables_onePremise_of_ruleEigenlabel
    {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L)
    (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 1)
    (hAC : rule.ApplicationConditions Γ Δ)
    (sub : G1nnfProofTree hL
      ((rule.premises Γ Δ)[0]'(by omega)).1
      ((rule.premises Γ Δ)[0]'(by omega)).2)
    (ev w : Nat) (hLabel : ruleEigenlabel rule = some ev)
    (hw : w = ev) :
    (G1nnfProofTree.onePremise
      rule Γ Δ hPrem hAC sub).eigenvariables w := by
  rw [G1nnfProofTree.eigenvariables_onePremise]
  apply Or.inl
  cases rule <;> simp_all [ruleEigenlabel]

private theorem eigenvariables_twoPremise_of_ruleEigenlabel
    {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L)
    (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 2)
    (hAC : rule.ApplicationConditions Γ Δ)
    (sub1 : G1nnfProofTree hL
      ((rule.premises Γ Δ)[0]'(by omega)).1
      ((rule.premises Γ Δ)[0]'(by omega)).2)
    (sub2 : G1nnfProofTree hL
      ((rule.premises Γ Δ)[1]'(by omega)).1
      ((rule.premises Γ Δ)[1]'(by omega)).2)
    (ev w : Nat) (hLabel : ruleEigenlabel rule = some ev)
    (hw : w = ev) :
    (G1nnfProofTree.twoPremise
      rule Γ Δ hPrem hAC sub1 sub2).eigenvariables w := by
  rw [G1nnfProofTree.eigenvariables_twoPremise]
  apply Or.inl
  cases rule <;> simp_all [ruleEigenlabel]

theorem ruleSubstOk_of_hygiene {L : Language}
    (rule : G1nnfRule L)
    (Γ Δ : LCS.Finset (FormulaN L)) (t : Term L) (y : Nat)
    (hyRoot :
      (∀ A ∈ (rule.conclusion Γ Δ).1,
        FormulaN.notBoundIn y A) ∧
      (∀ A ∈ (rule.conclusion Γ Δ).2,
        FormulaN.notBoundIn y A))
    (htRoot :
      ∀ w, termFV t w →
        (∀ A ∈ (rule.conclusion Γ Δ).1,
          FormulaN.notBoundIn w A) ∧
        (∀ A ∈ (rule.conclusion Γ Δ).2,
          FormulaN.notBoundIn w A))
    (hEigen :
      ∀ ev, ruleEigenlabel rule = some ev →
        y ≠ ev ∧ (∀ w, termFV t w → w ≠ ev)) :
    ruleSubstOk t y rule := by
  cases rule with
  | axiomPosAtomic A hAtom ruleΓ ruleΔ => trivial
  | axiomNegAtomic A hAtom ruleΓ ruleΔ => trivial
  | axiomCompLeft A hAtom ruleΓ ruleΔ => trivial
  | axiomCompRight A hAtom ruleΓ ruleΔ => trivial
  | cut A Lam Theta => trivial
  | conjLeft1 A B => trivial
  | conjLeft2 A B => trivial
  | conjRight A B => trivial
  | disjLeft A B => trivial
  | disjRight1 A B => trivial
  | disjRight2 A B => trivial
  | allLeft x A u =>
      simp only [G1nnfRule.conclusion] at hyRoot htRoot
      have hMem :
          FormulaN.all x A ∈
            LCS.Finset.insert (FormulaN.all x A) Γ :=
        LCS.Finset.mem_insert.mpr (Or.inl rfl)
      have hyPrincipal := hyRoot.1 (.all x A) hMem
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro hyx
        exact hyPrincipal (Or.inr hyx)
      · intro hx
        exact (htRoot x hx).1 (.all x A) hMem (Or.inr rfl)
      · intro hyA
        exact hyPrincipal (Or.inl hyA)
      · apply
          LCS.FirstOrder.Gentzen.Hintikka.isFreeForN_of_bv_disjoint
        intro w hw hwA
        exact (htRoot w hw).1 (.all x A) hMem (Or.inl hwA)
  | allRight x A ev =>
      simp only [G1nnfRule.conclusion] at hyRoot htRoot
      have hMem :
          FormulaN.all x A ∈
            LCS.Finset.insert (FormulaN.all x A) Δ :=
        LCS.Finset.mem_insert.mpr (Or.inl rfl)
      have hyPrincipal := hyRoot.2 (.all x A) hMem
      have hEig := hEigen ev rfl
      refine ⟨?_, ?_, ?_, ?_, hEig.1, hEig.2⟩
      · intro hyx
        exact hyPrincipal (Or.inr hyx)
      · intro hx
        exact (htRoot x hx).2 (.all x A) hMem (Or.inr rfl)
      · intro hyA
        exact hyPrincipal (Or.inl hyA)
      · apply
          LCS.FirstOrder.Gentzen.Hintikka.isFreeForN_of_bv_disjoint
        intro w hw hwA
        exact (htRoot w hw).2 (.all x A) hMem (Or.inl hwA)
  | exLeft x A ev =>
      simp only [G1nnfRule.conclusion] at hyRoot htRoot
      have hMem :
          FormulaN.ex x A ∈
            LCS.Finset.insert (FormulaN.ex x A) Γ :=
        LCS.Finset.mem_insert.mpr (Or.inl rfl)
      have hyPrincipal := hyRoot.1 (.ex x A) hMem
      have hEig := hEigen ev rfl
      refine ⟨?_, ?_, ?_, ?_, hEig.1, hEig.2⟩
      · intro hyx
        exact hyPrincipal (Or.inr hyx)
      · intro hx
        exact (htRoot x hx).1 (.ex x A) hMem (Or.inr rfl)
      · intro hyA
        exact hyPrincipal (Or.inl hyA)
      · apply
          LCS.FirstOrder.Gentzen.Hintikka.isFreeForN_of_bv_disjoint
        intro w hw hwA
        exact (htRoot w hw).1 (.ex x A) hMem (Or.inl hwA)
  | exRight x A u =>
      simp only [G1nnfRule.conclusion] at hyRoot htRoot
      have hMem :
          FormulaN.ex x A ∈
            LCS.Finset.insert (FormulaN.ex x A) Δ :=
        LCS.Finset.mem_insert.mpr (Or.inl rfl)
      have hyPrincipal := hyRoot.2 (.ex x A) hMem
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro hyx
        exact hyPrincipal (Or.inr hyx)
      · intro hx
        exact (htRoot x hx).2 (.ex x A) hMem (Or.inr rfl)
      · intro hyA
        exact hyPrincipal (Or.inl hyA)
      · apply
          LCS.FirstOrder.Gentzen.Hintikka.isFreeForN_of_bv_disjoint
        intro w hw hwA
        exact (htRoot w hw).2 (.ex x A) hMem (Or.inl hwA)

/-- The implementation precondition for direct term substitution follows
from proof-wide binder hygiene and eigenvariable disjointness.  This is the
internal bridge used after the two root-preserving hygiene phases. -/
theorem treeSubstOk_of_hygiene {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (t : Term L) (y : Nat)
    (hyBound : T.notBoundIn y)
    (htBound : ∀ w, termFV t w → T.notBoundIn w)
    (hyEigen : ¬ T.eigenvariables y)
    (htEigen : ∀ w, termFV t w → ¬ T.eigenvariables w) :
    T.treeSubstOk t y := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
      simp only [G1nnfProofTree.treeSubstOk]
      apply ruleSubstOk_of_hygiene rule Γ Δ t y
      · exact
          (G1nnfProofTree.axiom_ (hL := hL) rule Γ Δ hAxiom hAC
            ).notBoundIn_atRoot y hyBound
      · intro w hw
        exact
          (G1nnfProofTree.axiom_ (hL := hL) rule Γ Δ hAxiom hAC
            ).notBoundIn_atRoot w (htBound w hw)
      · intro ev hev
        exact
          (no_ruleEigenlabel_of_zero_premises
            rule Γ Δ hAxiom ev hev).elim
  | onePremise rule Γ Δ hPrem hAC sub ih =>
      simp only [G1nnfProofTree.treeSubstOk]
      refine ⟨?_, ?_⟩
      · apply ruleSubstOk_of_hygiene rule Γ Δ t y
        · exact
            (G1nnfProofTree.onePremise
              rule Γ Δ hPrem hAC sub).notBoundIn_atRoot y hyBound
        · intro w hw
          exact
            (G1nnfProofTree.onePremise
              rule Γ Δ hPrem hAC sub).notBoundIn_atRoot
                w (htBound w hw)
        · intro ev hev
          constructor
          · intro hyev
            apply hyEigen
            exact
              eigenvariables_onePremise_of_ruleEigenlabel
                rule Γ Δ hPrem hAC sub ev y hev hyev
          · intro w hw hwev
            apply htEigen w hw
            exact
              eigenvariables_onePremise_of_ruleEigenlabel
                rule Γ Δ hPrem hAC sub ev w hev hwev
      · apply ih
        · exact
            G1nnfProofTree.notBoundIn_onePremise_subtree
              rule Γ Δ hPrem hAC sub y hyBound
        · intro w hw
          exact
            G1nnfProofTree.notBoundIn_onePremise_subtree
              rule Γ Δ hPrem hAC sub w (htBound w hw)
        · intro hSub
          apply hyEigen
          rw [G1nnfProofTree.eigenvariables_onePremise]
          exact Or.inr hSub
        · intro w hw hSub
          apply htEigen w hw
          rw [G1nnfProofTree.eigenvariables_onePremise]
          exact Or.inr hSub
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
      simp only [G1nnfProofTree.treeSubstOk]
      have hySubs :=
        G1nnfProofTree.notBoundIn_twoPremise_subtrees
          rule Γ Δ hPrem hAC sub1 sub2 y hyBound
      refine ⟨?_, ?_, ?_⟩
      · apply ruleSubstOk_of_hygiene rule Γ Δ t y
        · exact
            (G1nnfProofTree.twoPremise
              rule Γ Δ hPrem hAC sub1 sub2
              ).notBoundIn_atRoot y hyBound
        · intro w hw
          exact
            (G1nnfProofTree.twoPremise
              rule Γ Δ hPrem hAC sub1 sub2
              ).notBoundIn_atRoot w (htBound w hw)
        · intro ev hev
          constructor
          · intro hyev
            apply hyEigen
            exact
              eigenvariables_twoPremise_of_ruleEigenlabel
                rule Γ Δ hPrem hAC sub1 sub2 ev y hev hyev
          · intro w hw hwev
            apply htEigen w hw
            exact
              eigenvariables_twoPremise_of_ruleEigenlabel
                rule Γ Δ hPrem hAC sub1 sub2 ev w hev hwev
      · apply ih1
        · exact hySubs.1
        · intro w hw
          exact
            (G1nnfProofTree.notBoundIn_twoPremise_subtrees
              rule Γ Δ hPrem hAC sub1 sub2 w
                (htBound w hw)).1
        · intro hSub
          apply hyEigen
          rw [G1nnfProofTree.eigenvariables_twoPremise]
          exact Or.inr (Or.inl hSub)
        · intro w hw hSub
          apply htEigen w hw
          rw [G1nnfProofTree.eigenvariables_twoPremise]
          exact Or.inr (Or.inl hSub)
      · apply ih2
        · exact hySubs.2
        · intro w hw
          exact
            (G1nnfProofTree.notBoundIn_twoPremise_subtrees
              rule Γ Δ hPrem hAC sub1 sub2 w
                (htBound w hw)).2
        · intro hSub
          apply hyEigen
          rw [G1nnfProofTree.eigenvariables_twoPremise]
          exact Or.inr (Or.inr hSub)
        · intro w hw hSub
          apply htEigen w hw
          rw [G1nnfProofTree.eigenvariables_twoPremise]
          exact Or.inr (Or.inr hSub)

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

theorem G1nnfProofTree.eigenvariables_onePremise_congr {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L)
    (Γ Δ Γ' Δ' : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 1)
    (hPrem' : (rule.premises Γ' Δ').length = 1)
    (hAC : rule.ApplicationConditions Γ Δ)
    (hAC' : rule.ApplicationConditions Γ' Δ')
    (sub : G1nnfProofTree hL
      ((rule.premises Γ Δ)[0]'(by omega)).1
      ((rule.premises Γ Δ)[0]'(by omega)).2)
    (sub' : G1nnfProofTree hL
      ((rule.premises Γ' Δ')[0]'(by omega)).1
      ((rule.premises Γ' Δ')[0]'(by omega)).2)
    (hSub : ∀ v, sub'.eigenvariables v = sub.eigenvariables v)
    (v : Nat) :
    (G1nnfProofTree.onePremise rule Γ' Δ' hPrem' hAC' sub').eigenvariables v =
      (G1nnfProofTree.onePremise rule Γ Δ hPrem hAC sub).eigenvariables v := by
  rw [G1nnfProofTree.eigenvariables_onePremise,
    G1nnfProofTree.eigenvariables_onePremise, hSub v]

theorem G1nnfProofTree.eigenvariables_twoPremise_congr {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L)
    (Γ Δ Γ' Δ' : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 2)
    (hPrem' : (rule.premises Γ' Δ').length = 2)
    (hAC : rule.ApplicationConditions Γ Δ)
    (hAC' : rule.ApplicationConditions Γ' Δ')
    (sub1 : G1nnfProofTree hL
      ((rule.premises Γ Δ)[0]'(by omega)).1
      ((rule.premises Γ Δ)[0]'(by omega)).2)
    (sub2 : G1nnfProofTree hL
      ((rule.premises Γ Δ)[1]'(by omega)).1
      ((rule.premises Γ Δ)[1]'(by omega)).2)
    (sub1' : G1nnfProofTree hL
      ((rule.premises Γ' Δ')[0]'(by omega)).1
      ((rule.premises Γ' Δ')[0]'(by omega)).2)
    (sub2' : G1nnfProofTree hL
      ((rule.premises Γ' Δ')[1]'(by omega)).1
      ((rule.premises Γ' Δ')[1]'(by omega)).2)
    (hSub1 : ∀ v, sub1'.eigenvariables v = sub1.eigenvariables v)
    (hSub2 : ∀ v, sub2'.eigenvariables v = sub2.eigenvariables v)
    (v : Nat) :
    (G1nnfProofTree.twoPremise rule Γ' Δ' hPrem' hAC'
      sub1' sub2').eigenvariables v =
      (G1nnfProofTree.twoPremise rule Γ Δ hPrem hAC
        sub1 sub2).eigenvariables v := by
  rw [G1nnfProofTree.eigenvariables_twoPremise,
    G1nnfProofTree.eigenvariables_twoPremise, hSub1 v, hSub2 v]

theorem G1nnfProofTree.weakenTreeLeft_preserving_eigenvariables {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hL Γ Δ)
    (A : FormulaN L) (hNNF : A.isNNF)
    (hFV : ∀ v, v ∈ formulaFVN A → ¬ T.eigenvariables v) :
    ∃ T' : G1nnfProofTree hL (LCS.Finset.insert A Γ) Δ,
      ∀ v, T'.eigenvariables v = T.eigenvariables v := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
    let hWeakened :=
      G1nnfRule.applicationConditions_axiom_insert_left
        rule Γ Δ A hAxiom hAC hNNF
    have hSpec := Classical.choose_spec hWeakened
    let core :=
      G1nnfProofTree.axiom_ (hL := hL) (Classical.choose hWeakened)
        Γ Δ hSpec.1 hSpec.2.1
    have hGamma :
        ((Classical.choose hWeakened).conclusion Γ Δ).1 =
          LCS.Finset.insert A (rule.conclusion Γ Δ).1 := by
      simpa using congrArg Prod.fst hSpec.2.2
    have hDelta :
        ((Classical.choose hWeakened).conclusion Γ Δ).2 =
          (rule.conclusion Γ Δ).2 := by
      simpa using congrArg Prod.snd hSpec.2.2
    let T' : G1nnfProofTree hL
        (LCS.Finset.insert A (rule.conclusion Γ Δ).1)
        (rule.conclusion Γ Δ).2 :=
      core.castTree hGamma hDelta
    refine ⟨T', ?_⟩
    intro v
    calc
      T'.eigenvariables v = core.eigenvariables v := by
        simpa only [T'] using
          G1nnfProofTree.castTree_eigenvariables hGamma hDelta core v
      _ = (G1nnfProofTree.axiom_ (hL := hL)
          rule Γ Δ hAxiom hAC).eigenvariables v := rfl
  | onePremise rule Γ Δ hPrem hAC sub ih =>
    have hSubFV :
        ∀ v, v ∈ formulaFVN A → ¬ sub.eigenvariables v := by
      intro v hv hSub
      exact hFV v hv (Or.inr hSub)
    cases rule with
    | conjLeft1 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih hSubFV with ⟨sub', hSubEig⟩
      have hOldLen :
          ((G1nnfRule.conjLeft1 B C).premises Γ Δ).length = 1 := by
        rfl
      have hNewLen :
          ((G1nnfRule.conjLeft1 B C).premises
            (LCS.Finset.insert A Γ) Δ).length = 1 := by
        rfl
      have hSubGamma :
          LCS.Finset.insert A
              (((G1nnfRule.conjLeft1 B C).premises Γ Δ)[0]'(by omega)).1 =
            (((G1nnfRule.conjLeft1 B C).premises
              (LCS.Finset.insert A Γ) Δ)[0]'(by omega)).1 := by
        simpa [G1nnfRule.premises] using
          LCS.Finset.insert_comm A B Γ
      have hSubDelta :
          (((G1nnfRule.conjLeft1 B C).premises Γ Δ)[0]'(by omega)).2 =
            (((G1nnfRule.conjLeft1 B C).premises
              (LCS.Finset.insert A Γ) Δ)[0]'(by omega)).2 := by
        rfl
      let subCast := sub'.castTree hSubGamma hSubDelta
      have hSubCastEig :
          ∀ w, subCast.eigenvariables w = sub.eigenvariables w := by
        intro w
        calc
          subCast.eigenvariables w = sub'.eigenvariables w := by
            exact G1nnfProofTree.castTree_eigenvariables
              hSubGamma hSubDelta sub' w
          _ = sub.eigenvariables w := hSubEig w
      have hAC' :=
        G1nnfRule.applicationConditions_insert_left
          (.conjLeft1 B C) Γ Δ A hAC hNNF trivial
      have hPrem' :
          ((G1nnfRule.conjLeft1 B C).premises
            (LCS.Finset.insert A Γ) Δ).length = 1 := by
        rfl
      let core :=
        G1nnfProofTree.onePremise
          (.conjLeft1 B C) (LCS.Finset.insert A Γ) Δ
          hPrem' hAC' subCast
      have hRootGamma :
          ((G1nnfRule.conjLeft1 B C).conclusion
            (LCS.Finset.insert A Γ) Δ).1 =
            LCS.Finset.insert A
              ((G1nnfRule.conjLeft1 B C).conclusion Γ Δ).1 := by
        simpa [G1nnfRule.conclusion] using
          LCS.Finset.insert_comm (.conj B C) A Γ
      have hRootDelta :
          ((G1nnfRule.conjLeft1 B C).conclusion
            (LCS.Finset.insert A Γ) Δ).2 =
            ((G1nnfRule.conjLeft1 B C).conclusion Γ Δ).2 := by
        rfl
      let T' := core.castTree hRootGamma hRootDelta
      refine ⟨T', ?_⟩
      intro v
      calc
        T'.eigenvariables v = core.eigenvariables v := by
          simpa only [T'] using
            G1nnfProofTree.castTree_eigenvariables
              hRootGamma hRootDelta core v
        _ = _ := by
          dsimp only [core]
          rw [G1nnfProofTree.eigenvariables_onePremise
              (.conjLeft1 B C) (LCS.Finset.insert A Γ) Δ
              hPrem' hAC' subCast v,
            G1nnfProofTree.eigenvariables_onePremise
              (.conjLeft1 B C) Γ Δ hOldLen hAC sub v,
            hSubCastEig v]
    | conjLeft2 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih hSubFV with ⟨sub', hSubEig⟩
      have hOldLen :
          ((G1nnfRule.conjLeft2 B C).premises Γ Δ).length = 1 := by
        rfl
      have hNewLen :
          ((G1nnfRule.conjLeft2 B C).premises
            (LCS.Finset.insert A Γ) Δ).length = 1 := by
        rfl
      have hSubGamma :
          LCS.Finset.insert A
              (((G1nnfRule.conjLeft2 B C).premises Γ Δ)[0]'(by omega)).1 =
            (((G1nnfRule.conjLeft2 B C).premises
              (LCS.Finset.insert A Γ) Δ)[0]'(by omega)).1 := by
        simpa [G1nnfRule.premises] using
          LCS.Finset.insert_comm A C Γ
      have hSubDelta :
          (((G1nnfRule.conjLeft2 B C).premises Γ Δ)[0]'(by omega)).2 =
            (((G1nnfRule.conjLeft2 B C).premises
              (LCS.Finset.insert A Γ) Δ)[0]'(by omega)).2 := by
        rfl
      let subCast := sub'.castTree hSubGamma hSubDelta
      have hSubCastEig :
          ∀ w, subCast.eigenvariables w = sub.eigenvariables w := by
        intro w
        calc
          subCast.eigenvariables w = sub'.eigenvariables w := by
            exact G1nnfProofTree.castTree_eigenvariables
              hSubGamma hSubDelta sub' w
          _ = sub.eigenvariables w := hSubEig w
      have hAC' :=
        G1nnfRule.applicationConditions_insert_left
          (.conjLeft2 B C) Γ Δ A hAC hNNF trivial
      have hPrem' :
          ((G1nnfRule.conjLeft2 B C).premises
            (LCS.Finset.insert A Γ) Δ).length = 1 := by
        rfl
      let core :=
        G1nnfProofTree.onePremise
          (.conjLeft2 B C) (LCS.Finset.insert A Γ) Δ
          hPrem' hAC' subCast
      have hRootGamma :
          ((G1nnfRule.conjLeft2 B C).conclusion
            (LCS.Finset.insert A Γ) Δ).1 =
            LCS.Finset.insert A
              ((G1nnfRule.conjLeft2 B C).conclusion Γ Δ).1 := by
        simpa [G1nnfRule.conclusion] using
          LCS.Finset.insert_comm (.conj B C) A Γ
      have hRootDelta :
          ((G1nnfRule.conjLeft2 B C).conclusion
            (LCS.Finset.insert A Γ) Δ).2 =
            ((G1nnfRule.conjLeft2 B C).conclusion Γ Δ).2 := by
        rfl
      let T' := core.castTree hRootGamma hRootDelta
      refine ⟨T', ?_⟩
      intro v
      calc
        T'.eigenvariables v = core.eigenvariables v := by
          simpa only [T'] using
            G1nnfProofTree.castTree_eigenvariables
              hRootGamma hRootDelta core v
        _ = _ := by
          dsimp only [core]
          rw [G1nnfProofTree.eigenvariables_onePremise
              (.conjLeft2 B C) (LCS.Finset.insert A Γ) Δ
              hPrem' hAC' subCast v,
            G1nnfProofTree.eigenvariables_onePremise
              (.conjLeft2 B C) Γ Δ hOldLen hAC sub v,
            hSubCastEig v]
    | disjRight1 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih hSubFV with ⟨sub', hSubEig⟩
      have hAC' :=
        G1nnfRule.applicationConditions_insert_left
          (.disjRight1 B C) Γ Δ A hAC hNNF trivial
      let T' : G1nnfProofTree hL
          (LCS.Finset.insert A Γ) (LCS.Finset.insert (.disj B C) Δ) :=
        .onePremise (.disjRight1 B C) (LCS.Finset.insert A Γ) Δ
          (by rfl) hAC' sub'
      refine ⟨T', ?_⟩
      intro v
      dsimp only [T']
      apply G1nnfProofTree.eigenvariables_onePremise_congr
      exact hSubEig
    | disjRight2 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih hSubFV with ⟨sub', hSubEig⟩
      have hAC' :=
        G1nnfRule.applicationConditions_insert_left
          (.disjRight2 B C) Γ Δ A hAC hNNF trivial
      let T' : G1nnfProofTree hL
          (LCS.Finset.insert A Γ) (LCS.Finset.insert (.disj B C) Δ) :=
        .onePremise (.disjRight2 B C) (LCS.Finset.insert A Γ) Δ
          (by rfl) hAC' sub'
      refine ⟨T', ?_⟩
      intro v
      dsimp only [T']
      apply G1nnfProofTree.eigenvariables_onePremise_congr
      exact hSubEig
    | allLeft x B t =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih hSubFV with ⟨sub', hSubEig⟩
      have hOldLen :
          ((G1nnfRule.allLeft x B t).premises Γ Δ).length = 1 := by
        rfl
      have hNewLen :
          ((G1nnfRule.allLeft x B t).premises
            (LCS.Finset.insert A Γ) Δ).length = 1 := by
        rfl
      have hSubGamma :
          LCS.Finset.insert A
              (((G1nnfRule.allLeft x B t).premises Γ Δ)[0]'(by omega)).1 =
            (((G1nnfRule.allLeft x B t).premises
              (LCS.Finset.insert A Γ) Δ)[0]'(by omega)).1 := by
        simpa [G1nnfRule.premises] using
          LCS.Finset.insert_comm A (formulaSubstN B t x) Γ
      have hSubDelta :
          (((G1nnfRule.allLeft x B t).premises Γ Δ)[0]'(by omega)).2 =
            (((G1nnfRule.allLeft x B t).premises
              (LCS.Finset.insert A Γ) Δ)[0]'(by omega)).2 := by
        rfl
      let subCast := sub'.castTree hSubGamma hSubDelta
      have hSubCastEig :
          ∀ w, subCast.eigenvariables w = sub.eigenvariables w := by
        intro w
        calc
          subCast.eigenvariables w = sub'.eigenvariables w := by
            exact G1nnfProofTree.castTree_eigenvariables
              hSubGamma hSubDelta sub' w
          _ = sub.eigenvariables w := hSubEig w
      have hAC' :=
        G1nnfRule.applicationConditions_insert_left
          (.allLeft x B t) Γ Δ A hAC hNNF trivial
      have hPrem' :
          ((G1nnfRule.allLeft x B t).premises
            (LCS.Finset.insert A Γ) Δ).length = 1 := by
        rfl
      let core :=
        G1nnfProofTree.onePremise
          (.allLeft x B t) (LCS.Finset.insert A Γ) Δ
          hPrem' hAC' subCast
      have hRootGamma :
          ((G1nnfRule.allLeft x B t).conclusion
            (LCS.Finset.insert A Γ) Δ).1 =
            LCS.Finset.insert A
              ((G1nnfRule.allLeft x B t).conclusion Γ Δ).1 := by
        simpa [G1nnfRule.conclusion] using
          LCS.Finset.insert_comm (.all x B) A Γ
      have hRootDelta :
          ((G1nnfRule.allLeft x B t).conclusion
            (LCS.Finset.insert A Γ) Δ).2 =
            ((G1nnfRule.allLeft x B t).conclusion Γ Δ).2 := by
        rfl
      let T' := core.castTree hRootGamma hRootDelta
      refine ⟨T', ?_⟩
      intro v
      calc
        T'.eigenvariables v = core.eigenvariables v := by
          simpa only [T'] using
            G1nnfProofTree.castTree_eigenvariables
              hRootGamma hRootDelta core v
        _ = _ := by
          dsimp only [core]
          rw [G1nnfProofTree.eigenvariables_onePremise
              (.allLeft x B t) (LCS.Finset.insert A Γ) Δ
              hPrem' hAC' subCast v,
            G1nnfProofTree.eigenvariables_onePremise
              (.allLeft x B t) Γ Δ hOldLen hAC sub v,
            hSubCastEig v]
    | allRight x B y =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih hSubFV with ⟨sub', hSubEig⟩
      have hFresh : y ∉ formulaFVN A := by
        intro hy
        exact hFV y hy (Or.inl rfl)
      have hAC' :=
        G1nnfRule.applicationConditions_insert_left
          (.allRight x B y) Γ Δ A hAC hNNF hFresh
      let T' : G1nnfProofTree hL
          (LCS.Finset.insert A Γ) (LCS.Finset.insert (.all x B) Δ) :=
        .onePremise (.allRight x B y) (LCS.Finset.insert A Γ) Δ
          (by rfl) hAC' sub'
      refine ⟨T', ?_⟩
      intro v
      dsimp only [T']
      apply G1nnfProofTree.eigenvariables_onePremise_congr
      exact hSubEig
    | exLeft x B y =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih hSubFV with ⟨sub', hSubEig⟩
      have hFresh : y ∉ formulaFVN A := by
        intro hy
        exact hFV y hy (Or.inl rfl)
      have hOldLen :
          ((G1nnfRule.exLeft x B y).premises Γ Δ).length = 1 := by
        rfl
      have hNewLen :
          ((G1nnfRule.exLeft x B y).premises
            (LCS.Finset.insert A Γ) Δ).length = 1 := by
        rfl
      have hSubGamma :
          LCS.Finset.insert A
              (((G1nnfRule.exLeft x B y).premises Γ Δ)[0]'(by omega)).1 =
            (((G1nnfRule.exLeft x B y).premises
              (LCS.Finset.insert A Γ) Δ)[0]'(by omega)).1 := by
        simpa [G1nnfRule.premises] using
          LCS.Finset.insert_comm A (formulaSubstN B (.var y) x) Γ
      have hSubDelta :
          (((G1nnfRule.exLeft x B y).premises Γ Δ)[0]'(by omega)).2 =
            (((G1nnfRule.exLeft x B y).premises
              (LCS.Finset.insert A Γ) Δ)[0]'(by omega)).2 := by
        rfl
      let subCast := sub'.castTree hSubGamma hSubDelta
      have hSubCastEig :
          ∀ w, subCast.eigenvariables w = sub.eigenvariables w := by
        intro w
        calc
          subCast.eigenvariables w = sub'.eigenvariables w := by
            exact G1nnfProofTree.castTree_eigenvariables
              hSubGamma hSubDelta sub' w
          _ = sub.eigenvariables w := hSubEig w
      have hAC' :=
        G1nnfRule.applicationConditions_insert_left
          (.exLeft x B y) Γ Δ A hAC hNNF hFresh
      have hPrem' :
          ((G1nnfRule.exLeft x B y).premises
            (LCS.Finset.insert A Γ) Δ).length = 1 := by
        rfl
      let core :=
        G1nnfProofTree.onePremise
          (.exLeft x B y) (LCS.Finset.insert A Γ) Δ
          hPrem' hAC' subCast
      have hRootGamma :
          ((G1nnfRule.exLeft x B y).conclusion
            (LCS.Finset.insert A Γ) Δ).1 =
            LCS.Finset.insert A
              ((G1nnfRule.exLeft x B y).conclusion Γ Δ).1 := by
        simpa [G1nnfRule.conclusion] using
          LCS.Finset.insert_comm (.ex x B) A Γ
      have hRootDelta :
          ((G1nnfRule.exLeft x B y).conclusion
            (LCS.Finset.insert A Γ) Δ).2 =
            ((G1nnfRule.exLeft x B y).conclusion Γ Δ).2 := by
        rfl
      let T' := core.castTree hRootGamma hRootDelta
      refine ⟨T', ?_⟩
      intro v
      calc
        T'.eigenvariables v = core.eigenvariables v := by
          simpa only [T'] using
            G1nnfProofTree.castTree_eigenvariables
              hRootGamma hRootDelta core v
        _ = _ := by
          dsimp only [core]
          rw [G1nnfProofTree.eigenvariables_onePremise
              (.exLeft x B y) (LCS.Finset.insert A Γ) Δ
              hPrem' hAC' subCast v,
            G1nnfProofTree.eigenvariables_onePremise
              (.exLeft x B y) Γ Δ hOldLen hAC sub v,
            hSubCastEig v]
    | exRight x B t =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih hSubFV with ⟨sub', hSubEig⟩
      have hAC' :=
        G1nnfRule.applicationConditions_insert_left
          (.exRight x B t) Γ Δ A hAC hNNF trivial
      let T' : G1nnfProofTree hL
          (LCS.Finset.insert A Γ) (LCS.Finset.insert (.ex x B) Δ) :=
        .onePremise (.exRight x B t) (LCS.Finset.insert A Γ) Δ
          (by rfl) hAC' sub'
      refine ⟨T', ?_⟩
      intro v
      dsimp only [T']
      apply G1nnfProofTree.eigenvariables_onePremise_congr
      exact hSubEig
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | cut _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjRight _ _ => simp [G1nnfRule.premises] at hPrem
    | disjLeft _ _ => simp [G1nnfRule.premises] at hPrem
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
    have hSub1FV :
        ∀ v, v ∈ formulaFVN A → ¬ sub1.eigenvariables v := by
      intro v hv hSub
      exact hFV v hv (Or.inr (Or.inl hSub))
    have hSub2FV :
        ∀ v, v ∈ formulaFVN A → ¬ sub2.eigenvariables v := by
      intro v hv hSub
      exact hFV v hv (Or.inr (Or.inr hSub))
    cases rule with
    | cut B Lam Theta =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih1 hSub1FV with ⟨sub1', hSub1Eig⟩
      have hAC' :=
        G1nnfRule.applicationConditions_insert_left
          (.cut B Lam Theta) Γ Δ A hAC hNNF trivial
      let core : G1nnfProofTree hL
          (LCS.Finset.union (LCS.Finset.insert A Γ) Lam)
          (LCS.Finset.union Δ Theta) :=
        .twoPremise (.cut B Lam Theta) (LCS.Finset.insert A Γ) Δ
          rfl hAC' sub1' sub2
      have hRootGamma :
          LCS.Finset.union (LCS.Finset.insert A Γ) Lam =
            LCS.Finset.insert A (LCS.Finset.union Γ Lam) :=
        (LCS.Finset.insert_union A Γ Lam).symm
      let T' := core.castTree hRootGamma rfl
      refine ⟨T', ?_⟩
      intro v
      calc
        T'.eigenvariables v = core.eigenvariables v :=
          G1nnfProofTree.castTree_eigenvariables hRootGamma rfl core v
        _ = _ := by
          dsimp only [core]
          apply G1nnfProofTree.eigenvariables_twoPremise_congr
          · exact hSub1Eig
          · intro w
            rfl
    | conjRight B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih1 hSub1FV with ⟨sub1', hSub1Eig⟩
      rcases ih2 hSub2FV with ⟨sub2', hSub2Eig⟩
      have hAC' :=
        G1nnfRule.applicationConditions_insert_left
          (.conjRight B C) Γ Δ A hAC hNNF trivial
      let T' : G1nnfProofTree hL
          (LCS.Finset.insert A Γ) (LCS.Finset.insert (.conj B C) Δ) :=
        .twoPremise (.conjRight B C) (LCS.Finset.insert A Γ) Δ
          (by rfl) hAC' sub1' sub2'
      refine ⟨T', ?_⟩
      intro v
      dsimp only [T']
      apply G1nnfProofTree.eigenvariables_twoPremise_congr
      · exact hSub1Eig
      · exact hSub2Eig
    | disjLeft B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih1 hSub1FV with ⟨sub1', hSub1Eig⟩
      rcases ih2 hSub2FV with ⟨sub2', hSub2Eig⟩
      have hOldLen :
          ((G1nnfRule.disjLeft B C).premises Γ Δ).length = 2 := by
        rfl
      have hNewLen :
          ((G1nnfRule.disjLeft B C).premises
            (LCS.Finset.insert A Γ) Δ).length = 2 := by
        rfl
      have hSub1Gamma :
          LCS.Finset.insert A
              (((G1nnfRule.disjLeft B C).premises Γ Δ)[0]'(by omega)).1 =
            (((G1nnfRule.disjLeft B C).premises
              (LCS.Finset.insert A Γ) Δ)[0]'(by omega)).1 := by
        simpa [G1nnfRule.premises] using
          LCS.Finset.insert_comm A B Γ
      have hSub1Delta :
          (((G1nnfRule.disjLeft B C).premises Γ Δ)[0]'(by omega)).2 =
            (((G1nnfRule.disjLeft B C).premises
              (LCS.Finset.insert A Γ) Δ)[0]'(by omega)).2 := by
        rfl
      have hSub2Gamma :
          LCS.Finset.insert A
              (((G1nnfRule.disjLeft B C).premises Γ Δ)[1]'(by omega)).1 =
            (((G1nnfRule.disjLeft B C).premises
              (LCS.Finset.insert A Γ) Δ)[1]'(by omega)).1 := by
        simpa [G1nnfRule.premises] using
          LCS.Finset.insert_comm A C Γ
      have hSub2Delta :
          (((G1nnfRule.disjLeft B C).premises Γ Δ)[1]'(by omega)).2 =
            (((G1nnfRule.disjLeft B C).premises
              (LCS.Finset.insert A Γ) Δ)[1]'(by omega)).2 := by
        rfl
      let sub1Cast := sub1'.castTree hSub1Gamma hSub1Delta
      let sub2Cast := sub2'.castTree hSub2Gamma hSub2Delta
      have hSub1CastEig :
          ∀ w, sub1Cast.eigenvariables w = sub1.eigenvariables w := by
        intro w
        calc
          sub1Cast.eigenvariables w = sub1'.eigenvariables w := by
            exact G1nnfProofTree.castTree_eigenvariables
              hSub1Gamma hSub1Delta sub1' w
          _ = sub1.eigenvariables w := hSub1Eig w
      have hSub2CastEig :
          ∀ w, sub2Cast.eigenvariables w = sub2.eigenvariables w := by
        intro w
        calc
          sub2Cast.eigenvariables w = sub2'.eigenvariables w := by
            exact G1nnfProofTree.castTree_eigenvariables
              hSub2Gamma hSub2Delta sub2' w
          _ = sub2.eigenvariables w := hSub2Eig w
      have hAC' :=
        G1nnfRule.applicationConditions_insert_left
          (.disjLeft B C) Γ Δ A hAC hNNF trivial
      have hPrem' :
          ((G1nnfRule.disjLeft B C).premises
            (LCS.Finset.insert A Γ) Δ).length = 2 := by
        rfl
      let core :=
        G1nnfProofTree.twoPremise
          (.disjLeft B C) (LCS.Finset.insert A Γ) Δ
          hPrem' hAC' sub1Cast sub2Cast
      have hRootGamma :
          ((G1nnfRule.disjLeft B C).conclusion
            (LCS.Finset.insert A Γ) Δ).1 =
            LCS.Finset.insert A
              ((G1nnfRule.disjLeft B C).conclusion Γ Δ).1 := by
        simpa [G1nnfRule.conclusion] using
          LCS.Finset.insert_comm (.disj B C) A Γ
      have hRootDelta :
          ((G1nnfRule.disjLeft B C).conclusion
            (LCS.Finset.insert A Γ) Δ).2 =
            ((G1nnfRule.disjLeft B C).conclusion Γ Δ).2 := by
        rfl
      let T' := core.castTree hRootGamma hRootDelta
      refine ⟨T', ?_⟩
      intro v
      calc
        T'.eigenvariables v = core.eigenvariables v := by
          simpa only [T'] using
            G1nnfProofTree.castTree_eigenvariables
              hRootGamma hRootDelta core v
        _ = _ := by
          dsimp only [core]
          rw [G1nnfProofTree.eigenvariables_twoPremise
              (.disjLeft B C) (LCS.Finset.insert A Γ) Δ
              hPrem' hAC' sub1Cast sub2Cast v,
            G1nnfProofTree.eigenvariables_twoPremise
              (.disjLeft B C) Γ Δ hOldLen hAC sub1 sub2 v,
            hSub1CastEig v, hSub2CastEig v]
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft1 _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft2 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight1 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight2 _ _ => simp [G1nnfRule.premises] at hPrem
    | allLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | allRight _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exRight _ _ _ => simp [G1nnfRule.premises] at hPrem

theorem G1nnfProofTree.weakenTreeRight_preserving_eigenvariables {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hL Γ Δ)
    (A : FormulaN L) (hNNF : A.isNNF)
    (hFV : ∀ v, v ∈ formulaFVN A → ¬ T.eigenvariables v) :
    ∃ T' : G1nnfProofTree hL Γ (LCS.Finset.insert A Δ),
      ∀ v, T'.eigenvariables v = T.eigenvariables v := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
    let hWeakened :=
      G1nnfRule.applicationConditions_axiom_insert_right
        rule Γ Δ A hAxiom hAC hNNF
    have hSpec := Classical.choose_spec hWeakened
    let core :=
      G1nnfProofTree.axiom_ (hL := hL) (Classical.choose hWeakened)
        Γ Δ hSpec.1 hSpec.2.1
    have hGamma :
        ((Classical.choose hWeakened).conclusion Γ Δ).1 =
          (rule.conclusion Γ Δ).1 := by
      simpa using congrArg Prod.fst hSpec.2.2
    have hDelta :
        ((Classical.choose hWeakened).conclusion Γ Δ).2 =
          LCS.Finset.insert A (rule.conclusion Γ Δ).2 := by
      simpa using congrArg Prod.snd hSpec.2.2
    let T' : G1nnfProofTree hL
        (rule.conclusion Γ Δ).1
        (LCS.Finset.insert A (rule.conclusion Γ Δ).2) :=
      core.castTree hGamma hDelta
    refine ⟨T', ?_⟩
    intro v
    calc
      T'.eigenvariables v = core.eigenvariables v := by
        simpa only [T'] using
          G1nnfProofTree.castTree_eigenvariables hGamma hDelta core v
      _ = (G1nnfProofTree.axiom_ (hL := hL)
          rule Γ Δ hAxiom hAC).eigenvariables v := rfl
  | onePremise rule Γ Δ hPrem hAC sub ih =>
    have hSubFV :
        ∀ v, v ∈ formulaFVN A → ¬ sub.eigenvariables v := by
      intro v hv hSub
      exact hFV v hv (Or.inr hSub)
    cases rule with
    | conjLeft1 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih hSubFV with ⟨sub', hSubEig⟩
      have hAC' :=
        G1nnfRule.applicationConditions_insert_right
          (.conjLeft1 B C) Γ Δ A hAC hNNF trivial
      let T' : G1nnfProofTree hL
          (LCS.Finset.insert (.conj B C) Γ) (LCS.Finset.insert A Δ) :=
        .onePremise (.conjLeft1 B C) Γ (LCS.Finset.insert A Δ)
          (by rfl) hAC' sub'
      refine ⟨T', ?_⟩
      intro v
      dsimp only [T']
      apply G1nnfProofTree.eigenvariables_onePremise_congr
      exact hSubEig
    | conjLeft2 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih hSubFV with ⟨sub', hSubEig⟩
      have hAC' :=
        G1nnfRule.applicationConditions_insert_right
          (.conjLeft2 B C) Γ Δ A hAC hNNF trivial
      let T' : G1nnfProofTree hL
          (LCS.Finset.insert (.conj B C) Γ) (LCS.Finset.insert A Δ) :=
        .onePremise (.conjLeft2 B C) Γ (LCS.Finset.insert A Δ)
          (by rfl) hAC' sub'
      refine ⟨T', ?_⟩
      intro v
      dsimp only [T']
      apply G1nnfProofTree.eigenvariables_onePremise_congr
      exact hSubEig
    | disjRight1 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih hSubFV with ⟨sub', hSubEig⟩
      have hOldLen :
          ((G1nnfRule.disjRight1 B C).premises Γ Δ).length = 1 := by
        rfl
      have hNewLen :
          ((G1nnfRule.disjRight1 B C).premises
            Γ (LCS.Finset.insert A Δ)).length = 1 := by
        rfl
      have hSubGamma :
          (((G1nnfRule.disjRight1 B C).premises Γ Δ)[0]'(by omega)).1 =
            (((G1nnfRule.disjRight1 B C).premises
              Γ (LCS.Finset.insert A Δ))[0]'(by omega)).1 := by
        rfl
      have hSubDelta :
          LCS.Finset.insert A
              (((G1nnfRule.disjRight1 B C).premises Γ Δ)[0]'(by omega)).2 =
            (((G1nnfRule.disjRight1 B C).premises
              Γ (LCS.Finset.insert A Δ))[0]'(by omega)).2 := by
        simpa [G1nnfRule.premises] using
          LCS.Finset.insert_comm A B Δ
      let subCast := sub'.castTree hSubGamma hSubDelta
      have hSubCastEig :
          ∀ w, subCast.eigenvariables w = sub.eigenvariables w := by
        intro w
        calc
          subCast.eigenvariables w = sub'.eigenvariables w := by
            exact G1nnfProofTree.castTree_eigenvariables
              hSubGamma hSubDelta sub' w
          _ = sub.eigenvariables w := hSubEig w
      have hAC' :=
        G1nnfRule.applicationConditions_insert_right
          (.disjRight1 B C) Γ Δ A hAC hNNF trivial
      have hPrem' :
          ((G1nnfRule.disjRight1 B C).premises
            Γ (LCS.Finset.insert A Δ)).length = 1 := by
        rfl
      let core :=
        G1nnfProofTree.onePremise
          (.disjRight1 B C) Γ (LCS.Finset.insert A Δ)
          hPrem' hAC' subCast
      have hRootGamma :
          ((G1nnfRule.disjRight1 B C).conclusion
            Γ (LCS.Finset.insert A Δ)).1 =
            ((G1nnfRule.disjRight1 B C).conclusion Γ Δ).1 := by
        rfl
      have hRootDelta :
          ((G1nnfRule.disjRight1 B C).conclusion
            Γ (LCS.Finset.insert A Δ)).2 =
            LCS.Finset.insert A
              ((G1nnfRule.disjRight1 B C).conclusion Γ Δ).2 := by
        simpa [G1nnfRule.conclusion] using
          LCS.Finset.insert_comm (.disj B C) A Δ
      let T' := core.castTree hRootGamma hRootDelta
      refine ⟨T', ?_⟩
      intro v
      calc
        T'.eigenvariables v = core.eigenvariables v := by
          simpa only [T'] using
            G1nnfProofTree.castTree_eigenvariables
              hRootGamma hRootDelta core v
        _ = _ := by
          dsimp only [core]
          rw [G1nnfProofTree.eigenvariables_onePremise
              (.disjRight1 B C) Γ (LCS.Finset.insert A Δ)
              hPrem' hAC' subCast v,
            G1nnfProofTree.eigenvariables_onePremise
              (.disjRight1 B C) Γ Δ hOldLen hAC sub v,
            hSubCastEig v]
    | disjRight2 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih hSubFV with ⟨sub', hSubEig⟩
      have hOldLen :
          ((G1nnfRule.disjRight2 B C).premises Γ Δ).length = 1 := by
        rfl
      have hNewLen :
          ((G1nnfRule.disjRight2 B C).premises
            Γ (LCS.Finset.insert A Δ)).length = 1 := by
        rfl
      have hSubGamma :
          (((G1nnfRule.disjRight2 B C).premises Γ Δ)[0]'(by omega)).1 =
            (((G1nnfRule.disjRight2 B C).premises
              Γ (LCS.Finset.insert A Δ))[0]'(by omega)).1 := by
        rfl
      have hSubDelta :
          LCS.Finset.insert A
              (((G1nnfRule.disjRight2 B C).premises Γ Δ)[0]'(by omega)).2 =
            (((G1nnfRule.disjRight2 B C).premises
              Γ (LCS.Finset.insert A Δ))[0]'(by omega)).2 := by
        simpa [G1nnfRule.premises] using
          LCS.Finset.insert_comm A C Δ
      let subCast := sub'.castTree hSubGamma hSubDelta
      have hSubCastEig :
          ∀ w, subCast.eigenvariables w = sub.eigenvariables w := by
        intro w
        calc
          subCast.eigenvariables w = sub'.eigenvariables w := by
            exact G1nnfProofTree.castTree_eigenvariables
              hSubGamma hSubDelta sub' w
          _ = sub.eigenvariables w := hSubEig w
      have hAC' :=
        G1nnfRule.applicationConditions_insert_right
          (.disjRight2 B C) Γ Δ A hAC hNNF trivial
      have hPrem' :
          ((G1nnfRule.disjRight2 B C).premises
            Γ (LCS.Finset.insert A Δ)).length = 1 := by
        rfl
      let core :=
        G1nnfProofTree.onePremise
          (.disjRight2 B C) Γ (LCS.Finset.insert A Δ)
          hPrem' hAC' subCast
      have hRootGamma :
          ((G1nnfRule.disjRight2 B C).conclusion
            Γ (LCS.Finset.insert A Δ)).1 =
            ((G1nnfRule.disjRight2 B C).conclusion Γ Δ).1 := by
        rfl
      have hRootDelta :
          ((G1nnfRule.disjRight2 B C).conclusion
            Γ (LCS.Finset.insert A Δ)).2 =
            LCS.Finset.insert A
              ((G1nnfRule.disjRight2 B C).conclusion Γ Δ).2 := by
        simpa [G1nnfRule.conclusion] using
          LCS.Finset.insert_comm (.disj B C) A Δ
      let T' := core.castTree hRootGamma hRootDelta
      refine ⟨T', ?_⟩
      intro v
      calc
        T'.eigenvariables v = core.eigenvariables v := by
          simpa only [T'] using
            G1nnfProofTree.castTree_eigenvariables
              hRootGamma hRootDelta core v
        _ = _ := by
          dsimp only [core]
          rw [G1nnfProofTree.eigenvariables_onePremise
              (.disjRight2 B C) Γ (LCS.Finset.insert A Δ)
              hPrem' hAC' subCast v,
            G1nnfProofTree.eigenvariables_onePremise
              (.disjRight2 B C) Γ Δ hOldLen hAC sub v,
            hSubCastEig v]
    | allLeft x B t =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih hSubFV with ⟨sub', hSubEig⟩
      have hAC' :=
        G1nnfRule.applicationConditions_insert_right
          (.allLeft x B t) Γ Δ A hAC hNNF trivial
      let T' : G1nnfProofTree hL
          (LCS.Finset.insert (.all x B) Γ) (LCS.Finset.insert A Δ) :=
        .onePremise (.allLeft x B t) Γ (LCS.Finset.insert A Δ)
          (by rfl) hAC' sub'
      refine ⟨T', ?_⟩
      intro v
      dsimp only [T']
      apply G1nnfProofTree.eigenvariables_onePremise_congr
      exact hSubEig
    | allRight x B y =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih hSubFV with ⟨sub', hSubEig⟩
      have hFresh : y ∉ formulaFVN A := by
        intro hy
        exact hFV y hy (Or.inl rfl)
      have hOldLen :
          ((G1nnfRule.allRight x B y).premises Γ Δ).length = 1 := by
        rfl
      have hNewLen :
          ((G1nnfRule.allRight x B y).premises
            Γ (LCS.Finset.insert A Δ)).length = 1 := by
        rfl
      have hSubGamma :
          (((G1nnfRule.allRight x B y).premises Γ Δ)[0]'(by omega)).1 =
            (((G1nnfRule.allRight x B y).premises
              Γ (LCS.Finset.insert A Δ))[0]'(by omega)).1 := by
        rfl
      have hSubDelta :
          LCS.Finset.insert A
              (((G1nnfRule.allRight x B y).premises Γ Δ)[0]'(by omega)).2 =
            (((G1nnfRule.allRight x B y).premises
              Γ (LCS.Finset.insert A Δ))[0]'(by omega)).2 := by
        simpa [G1nnfRule.premises] using
          LCS.Finset.insert_comm A (formulaSubstN B (.var y) x) Δ
      let subCast := sub'.castTree hSubGamma hSubDelta
      have hSubCastEig :
          ∀ w, subCast.eigenvariables w = sub.eigenvariables w := by
        intro w
        calc
          subCast.eigenvariables w = sub'.eigenvariables w := by
            exact G1nnfProofTree.castTree_eigenvariables
              hSubGamma hSubDelta sub' w
          _ = sub.eigenvariables w := hSubEig w
      have hAC' :=
        G1nnfRule.applicationConditions_insert_right
          (.allRight x B y) Γ Δ A hAC hNNF hFresh
      have hPrem' :
          ((G1nnfRule.allRight x B y).premises
            Γ (LCS.Finset.insert A Δ)).length = 1 := by
        rfl
      let core :=
        G1nnfProofTree.onePremise
          (.allRight x B y) Γ (LCS.Finset.insert A Δ)
          hPrem' hAC' subCast
      have hRootGamma :
          ((G1nnfRule.allRight x B y).conclusion
            Γ (LCS.Finset.insert A Δ)).1 =
            ((G1nnfRule.allRight x B y).conclusion Γ Δ).1 := by
        rfl
      have hRootDelta :
          ((G1nnfRule.allRight x B y).conclusion
            Γ (LCS.Finset.insert A Δ)).2 =
            LCS.Finset.insert A
              ((G1nnfRule.allRight x B y).conclusion Γ Δ).2 := by
        simpa [G1nnfRule.conclusion] using
          LCS.Finset.insert_comm (.all x B) A Δ
      let T' := core.castTree hRootGamma hRootDelta
      refine ⟨T', ?_⟩
      intro v
      calc
        T'.eigenvariables v = core.eigenvariables v := by
          simpa only [T'] using
            G1nnfProofTree.castTree_eigenvariables
              hRootGamma hRootDelta core v
        _ = _ := by
          dsimp only [core]
          rw [G1nnfProofTree.eigenvariables_onePremise
              (.allRight x B y) Γ (LCS.Finset.insert A Δ)
              hPrem' hAC' subCast v,
            G1nnfProofTree.eigenvariables_onePremise
              (.allRight x B y) Γ Δ hOldLen hAC sub v,
            hSubCastEig v]
    | exLeft x B y =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih hSubFV with ⟨sub', hSubEig⟩
      have hFresh : y ∉ formulaFVN A := by
        intro hy
        exact hFV y hy (Or.inl rfl)
      have hAC' :=
        G1nnfRule.applicationConditions_insert_right
          (.exLeft x B y) Γ Δ A hAC hNNF hFresh
      let T' : G1nnfProofTree hL
          (LCS.Finset.insert (.ex x B) Γ) (LCS.Finset.insert A Δ) :=
        .onePremise (.exLeft x B y) Γ (LCS.Finset.insert A Δ)
          (by rfl) hAC' sub'
      refine ⟨T', ?_⟩
      intro v
      dsimp only [T']
      apply G1nnfProofTree.eigenvariables_onePremise_congr
      exact hSubEig
    | exRight x B t =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih hSubFV with ⟨sub', hSubEig⟩
      have hOldLen :
          ((G1nnfRule.exRight x B t).premises Γ Δ).length = 1 := by
        rfl
      have hNewLen :
          ((G1nnfRule.exRight x B t).premises
            Γ (LCS.Finset.insert A Δ)).length = 1 := by
        rfl
      have hSubGamma :
          (((G1nnfRule.exRight x B t).premises Γ Δ)[0]'(by omega)).1 =
            (((G1nnfRule.exRight x B t).premises
              Γ (LCS.Finset.insert A Δ))[0]'(by omega)).1 := by
        rfl
      have hSubDelta :
          LCS.Finset.insert A
              (((G1nnfRule.exRight x B t).premises Γ Δ)[0]'(by omega)).2 =
            (((G1nnfRule.exRight x B t).premises
              Γ (LCS.Finset.insert A Δ))[0]'(by omega)).2 := by
        simpa [G1nnfRule.premises] using
          LCS.Finset.insert_comm A (formulaSubstN B t x) Δ
      let subCast := sub'.castTree hSubGamma hSubDelta
      have hSubCastEig :
          ∀ w, subCast.eigenvariables w = sub.eigenvariables w := by
        intro w
        calc
          subCast.eigenvariables w = sub'.eigenvariables w := by
            exact G1nnfProofTree.castTree_eigenvariables
              hSubGamma hSubDelta sub' w
          _ = sub.eigenvariables w := hSubEig w
      have hAC' :=
        G1nnfRule.applicationConditions_insert_right
          (.exRight x B t) Γ Δ A hAC hNNF trivial
      have hPrem' :
          ((G1nnfRule.exRight x B t).premises
            Γ (LCS.Finset.insert A Δ)).length = 1 := by
        rfl
      let core :=
        G1nnfProofTree.onePremise
          (.exRight x B t) Γ (LCS.Finset.insert A Δ)
          hPrem' hAC' subCast
      have hRootGamma :
          ((G1nnfRule.exRight x B t).conclusion
            Γ (LCS.Finset.insert A Δ)).1 =
            ((G1nnfRule.exRight x B t).conclusion Γ Δ).1 := by
        rfl
      have hRootDelta :
          ((G1nnfRule.exRight x B t).conclusion
            Γ (LCS.Finset.insert A Δ)).2 =
            LCS.Finset.insert A
              ((G1nnfRule.exRight x B t).conclusion Γ Δ).2 := by
        simpa [G1nnfRule.conclusion] using
          LCS.Finset.insert_comm (.ex x B) A Δ
      let T' := core.castTree hRootGamma hRootDelta
      refine ⟨T', ?_⟩
      intro v
      calc
        T'.eigenvariables v = core.eigenvariables v := by
          simpa only [T'] using
            G1nnfProofTree.castTree_eigenvariables
              hRootGamma hRootDelta core v
        _ = _ := by
          dsimp only [core]
          rw [G1nnfProofTree.eigenvariables_onePremise
              (.exRight x B t) Γ (LCS.Finset.insert A Δ)
              hPrem' hAC' subCast v,
            G1nnfProofTree.eigenvariables_onePremise
              (.exRight x B t) Γ Δ hOldLen hAC sub v,
            hSubCastEig v]
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | cut _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjRight _ _ => simp [G1nnfRule.premises] at hPrem
    | disjLeft _ _ => simp [G1nnfRule.premises] at hPrem
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
    have hSub1FV :
        ∀ v, v ∈ formulaFVN A → ¬ sub1.eigenvariables v := by
      intro v hv hSub
      exact hFV v hv (Or.inr (Or.inl hSub))
    have hSub2FV :
        ∀ v, v ∈ formulaFVN A → ¬ sub2.eigenvariables v := by
      intro v hv hSub
      exact hFV v hv (Or.inr (Or.inr hSub))
    cases rule with
    | cut B Lam Theta =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih1 hSub1FV with ⟨sub1', hSub1Eig⟩
      have hSubDelta := LCS.Finset.insert_comm A B Δ
      let sub1Cast := sub1'.castTree rfl hSubDelta
      have hSub1CastEig :
          ∀ w, sub1Cast.eigenvariables w = sub1.eigenvariables w := by
        intro w
        calc
          sub1Cast.eigenvariables w = sub1'.eigenvariables w :=
            G1nnfProofTree.castTree_eigenvariables rfl hSubDelta sub1' w
          _ = sub1.eigenvariables w := hSub1Eig w
      have hAC' :=
        G1nnfRule.applicationConditions_insert_right
          (.cut B Lam Theta) Γ Δ A hAC hNNF trivial
      let core : G1nnfProofTree hL (LCS.Finset.union Γ Lam)
          (LCS.Finset.union (LCS.Finset.insert A Δ) Theta) :=
        .twoPremise (.cut B Lam Theta) Γ (LCS.Finset.insert A Δ)
          rfl hAC' sub1Cast sub2
      have hRootDelta :
          LCS.Finset.union (LCS.Finset.insert A Δ) Theta =
            LCS.Finset.insert A (LCS.Finset.union Δ Theta) :=
        (LCS.Finset.insert_union A Δ Theta).symm
      let T' := core.castTree rfl hRootDelta
      refine ⟨T', ?_⟩
      intro v
      calc
        T'.eigenvariables v = core.eigenvariables v :=
          G1nnfProofTree.castTree_eigenvariables rfl hRootDelta core v
        _ = _ := by
          dsimp only [core]
          apply G1nnfProofTree.eigenvariables_twoPremise_congr
          · exact hSub1CastEig
          · intro w
            rfl
    | conjRight B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih1 hSub1FV with ⟨sub1', hSub1Eig⟩
      rcases ih2 hSub2FV with ⟨sub2', hSub2Eig⟩
      have hOldLen :
          ((G1nnfRule.conjRight B C).premises Γ Δ).length = 2 := by
        rfl
      have hNewLen :
          ((G1nnfRule.conjRight B C).premises
            Γ (LCS.Finset.insert A Δ)).length = 2 := by
        rfl
      have hSub1Gamma :
          (((G1nnfRule.conjRight B C).premises Γ Δ)[0]'(by omega)).1 =
            (((G1nnfRule.conjRight B C).premises
              Γ (LCS.Finset.insert A Δ))[0]'(by omega)).1 := by
        rfl
      have hSub1Delta :
          LCS.Finset.insert A
              (((G1nnfRule.conjRight B C).premises Γ Δ)[0]'(by omega)).2 =
            (((G1nnfRule.conjRight B C).premises
              Γ (LCS.Finset.insert A Δ))[0]'(by omega)).2 := by
        simpa [G1nnfRule.premises] using
          LCS.Finset.insert_comm A B Δ
      have hSub2Gamma :
          (((G1nnfRule.conjRight B C).premises Γ Δ)[1]'(by omega)).1 =
            (((G1nnfRule.conjRight B C).premises
              Γ (LCS.Finset.insert A Δ))[1]'(by omega)).1 := by
        rfl
      have hSub2Delta :
          LCS.Finset.insert A
              (((G1nnfRule.conjRight B C).premises Γ Δ)[1]'(by omega)).2 =
            (((G1nnfRule.conjRight B C).premises
              Γ (LCS.Finset.insert A Δ))[1]'(by omega)).2 := by
        simpa [G1nnfRule.premises] using
          LCS.Finset.insert_comm A C Δ
      let sub1Cast := sub1'.castTree hSub1Gamma hSub1Delta
      let sub2Cast := sub2'.castTree hSub2Gamma hSub2Delta
      have hSub1CastEig :
          ∀ w, sub1Cast.eigenvariables w = sub1.eigenvariables w := by
        intro w
        calc
          sub1Cast.eigenvariables w = sub1'.eigenvariables w := by
            exact G1nnfProofTree.castTree_eigenvariables
              hSub1Gamma hSub1Delta sub1' w
          _ = sub1.eigenvariables w := hSub1Eig w
      have hSub2CastEig :
          ∀ w, sub2Cast.eigenvariables w = sub2.eigenvariables w := by
        intro w
        calc
          sub2Cast.eigenvariables w = sub2'.eigenvariables w := by
            exact G1nnfProofTree.castTree_eigenvariables
              hSub2Gamma hSub2Delta sub2' w
          _ = sub2.eigenvariables w := hSub2Eig w
      have hAC' :=
        G1nnfRule.applicationConditions_insert_right
          (.conjRight B C) Γ Δ A hAC hNNF trivial
      have hPrem' :
          ((G1nnfRule.conjRight B C).premises
            Γ (LCS.Finset.insert A Δ)).length = 2 := by
        rfl
      let core :=
        G1nnfProofTree.twoPremise
          (.conjRight B C) Γ (LCS.Finset.insert A Δ)
          hPrem' hAC' sub1Cast sub2Cast
      have hRootGamma :
          ((G1nnfRule.conjRight B C).conclusion
            Γ (LCS.Finset.insert A Δ)).1 =
            ((G1nnfRule.conjRight B C).conclusion Γ Δ).1 := by
        rfl
      have hRootDelta :
          ((G1nnfRule.conjRight B C).conclusion
            Γ (LCS.Finset.insert A Δ)).2 =
            LCS.Finset.insert A
              ((G1nnfRule.conjRight B C).conclusion Γ Δ).2 := by
        simpa [G1nnfRule.conclusion] using
          LCS.Finset.insert_comm (.conj B C) A Δ
      let T' := core.castTree hRootGamma hRootDelta
      refine ⟨T', ?_⟩
      intro v
      calc
        T'.eigenvariables v = core.eigenvariables v := by
          simpa only [T'] using
            G1nnfProofTree.castTree_eigenvariables
              hRootGamma hRootDelta core v
        _ = _ := by
          dsimp only [core]
          rw [G1nnfProofTree.eigenvariables_twoPremise
              (.conjRight B C) Γ (LCS.Finset.insert A Δ)
              hPrem' hAC' sub1Cast sub2Cast v,
            G1nnfProofTree.eigenvariables_twoPremise
              (.conjRight B C) Γ Δ hOldLen hAC sub1 sub2 v,
            hSub1CastEig v, hSub2CastEig v]
    | disjLeft B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      rcases ih1 hSub1FV with ⟨sub1', hSub1Eig⟩
      rcases ih2 hSub2FV with ⟨sub2', hSub2Eig⟩
      have hAC' :=
        G1nnfRule.applicationConditions_insert_right
          (.disjLeft B C) Γ Δ A hAC hNNF trivial
      let T' : G1nnfProofTree hL
          (LCS.Finset.insert (.disj B C) Γ) (LCS.Finset.insert A Δ) :=
        .twoPremise (.disjLeft B C) Γ (LCS.Finset.insert A Δ)
          (by rfl) hAC' sub1' sub2'
      refine ⟨T', ?_⟩
      intro v
      dsimp only [T']
      apply G1nnfProofTree.eigenvariables_twoPremise_congr
      · exact hSub1Eig
      · exact hSub2Eig
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft1 _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft2 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight1 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight2 _ _ => simp [G1nnfRule.premises] at hPrem
    | allLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | allRight _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exRight _ _ _ => simp [G1nnfRule.premises] at hPrem

end LCS.CutElim.Hauptsatz
end

