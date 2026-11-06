import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.ProofTrees
import LCS.CutElim.Hauptsatz.CutElimination.Eigenvariables

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

theorem LCS.Finset.insert_comm [DecidableEq α] (a b : α) (s : LCS.Finset α) :
    LCS.Finset.insert a (LCS.Finset.insert b s) =
    LCS.Finset.insert b (LCS.Finset.insert a s) := by
-- BEGIN PROOF
  apply LCS.Finset.ext
  intro x
  rw [LCS.Finset.mem_insert, LCS.Finset.mem_insert,
      LCS.Finset.mem_insert, LCS.Finset.mem_insert]
  constructor
  · rintro (rfl | rfl | h) <;> simp_all
  · rintro (rfl | rfl | h) <;> simp_all

/-- Inserting into the first set commutes with taking its union. -/
theorem LCS.Finset.insert_union [DecidableEq α] (a : α) (s t : LCS.Finset α) :
    LCS.Finset.insert a (LCS.Finset.union s t) =
      LCS.Finset.union (LCS.Finset.insert a s) t := by
  apply LCS.Finset.ext
  intro x
  simp only [LCS.Finset.mem_insert, LCS.Finset.mem_union, or_assoc]

namespace G1nnfRule

/-- Extending the antecedent preserves a rule's side conditions provided
the inserted formula avoids the eigenvariable of a universal-right or
existential-left rule. Non-eigenvariable rules need no extra hypothesis. -/
theorem sideConditions_insert_left {L : Language}
    (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
    (C : FormulaN L)
    (hSC : rule.SideConditions Gamma Delta)
    (hFresh :
      match rule with
      | .allRight _ _ ev => ev ∉ formulaFVN C
      | .exLeft _ _ ev => ev ∉ formulaFVN C
      | _ => True) :
    rule.SideConditions (LCS.Finset.insert C Gamma) Delta := by
-- BEGIN PROOF
  cases rule <;>
    simp only [SideConditions] at hSC ⊢ <;>
    simp_all

-- END PROOF
/-- Extending the succedent preserves a rule's side conditions provided
the inserted formula avoids the eigenvariable of a universal-right or
existential-left rule. Non-eigenvariable rules need no extra hypothesis. -/
theorem sideConditions_insert_right {L : Language}
    (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
    (C : FormulaN L)
    (hSC : rule.SideConditions Gamma Delta)
    (hFresh :
      match rule with
      | .allRight _ _ ev => ev ∉ formulaFVN C
      | .exLeft _ _ ev => ev ∉ formulaFVN C
      | _ => True) :
    rule.SideConditions Gamma (LCS.Finset.insert C Delta) := by
-- BEGIN PROOF
  cases rule <;>
    simp only [SideConditions] at hSC ⊢ <;>
    simp_all

-- END PROOF
/-- Extending the antecedent preserves a legal rule application when the
inserted formula is in NNF and avoids the eigenvariable of a universal-right
or existential-left rule. The NNF hypothesis is necessary because the
extended conclusion is itself a G1nnf sequent. -/
theorem applicationConditions_insert_left {L : Language}
    (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
    (C : FormulaN L)
    (hAC : rule.ApplicationConditions Gamma Delta)
    (hNNF : C.isNNF)
    (hFresh :
      match rule with
      | .allRight _ _ ev => ev ∉ formulaFVN C
      | .exLeft _ _ ev => ev ∉ formulaFVN C
      | _ => True) :
    rule.ApplicationConditions (LCS.Finset.insert C Gamma) Delta := by
-- BEGIN PROOF
  cases rule <;>
    refine
      ⟨sideConditions_insert_left _ Gamma Delta C hAC.1 hFresh, ?_⟩ <;>
    simp only [conclusion] at hAC ⊢
  all_goals first
    | exact hAC.2
    | simpa only [LCS.Finset.insert_comm, LCS.Finset.insert_union] using
        G1nnfFinsetSequent.IsNNF.insert_left hNNF hAC.2

-- END PROOF
/-- Extending the succedent preserves a legal rule application when the
inserted formula is in NNF and avoids the eigenvariable of a universal-right
or existential-left rule. The NNF hypothesis is necessary because the
extended conclusion is itself a G1nnf sequent. -/
theorem applicationConditions_insert_right {L : Language}
    (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
    (C : FormulaN L)
    (hAC : rule.ApplicationConditions Gamma Delta)
    (hNNF : C.isNNF)
    (hFresh :
      match rule with
      | .allRight _ _ ev => ev ∉ formulaFVN C
      | .exLeft _ _ ev => ev ∉ formulaFVN C
      | _ => True) :
    rule.ApplicationConditions Gamma (LCS.Finset.insert C Delta) := by
-- BEGIN PROOF
  cases rule <;>
    refine
      ⟨sideConditions_insert_right _ Gamma Delta C hAC.1 hFresh, ?_⟩ <;>
    simp only [conclusion] at hAC ⊢
  all_goals first
    | exact hAC.2
    | simpa only [LCS.Finset.insert_comm, LCS.Finset.insert_union] using
        G1nnfFinsetSequent.IsNNF.insert_right hNNF hAC.2

-- END PROOF
/-- A zero-premise application can be weakened on the left by extending the
context stored inside its axiom rule. The returned conclusion equality records
that the actual axiom conclusion, rather than its ignored ambient contexts, was
extended. -/
theorem applicationConditions_axiom_insert_left {L : Language}
    (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
    (C : FormulaN L)
    (hAxiom : (rule.premises Gamma Delta).length = 0)
    (hAC : rule.ApplicationConditions Gamma Delta)
    (hNNF : C.isNNF) :
    ∃ weakenedRule : G1nnfRule L,
      (weakenedRule.premises Gamma Delta).length = 0 ∧
      weakenedRule.ApplicationConditions Gamma Delta ∧
      weakenedRule.conclusion Gamma Delta =
        (LCS.Finset.insert C (rule.conclusion Gamma Delta).1,
          (rule.conclusion Gamma Delta).2) := by
-- BEGIN PROOF
  cases rule with
  | axiomPosAtomic A hAtom ruleGamma ruleDelta =>
    refine
      ⟨.axiomPosAtomic A hAtom (LCS.Finset.insert C ruleGamma) ruleDelta,
        rfl, ?_, ?_⟩
    · refine ⟨trivial, ?_⟩
      simpa only [conclusion, LCS.Finset.insert_comm] using
        G1nnfFinsetSequent.IsNNF.insert_left hNNF hAC.2
    · simp only [conclusion, LCS.Finset.insert_comm]
  | axiomNegAtomic A hAtom ruleGamma ruleDelta =>
    refine
      ⟨.axiomNegAtomic A hAtom (LCS.Finset.insert C ruleGamma) ruleDelta,
        rfl, ?_, ?_⟩
    · refine ⟨trivial, ?_⟩
      simpa only [conclusion, LCS.Finset.insert_comm] using
        G1nnfFinsetSequent.IsNNF.insert_left hNNF hAC.2
    · simp only [conclusion, LCS.Finset.insert_comm]
  | axiomCompLeft A hAtom ruleGamma ruleDelta =>
    refine
      ⟨.axiomCompLeft A hAtom (LCS.Finset.insert C ruleGamma) ruleDelta,
        rfl, ?_, ?_⟩
    · refine ⟨trivial, ?_⟩
      simpa only [conclusion, LCS.Finset.insert_comm] using
        G1nnfFinsetSequent.IsNNF.insert_left hNNF hAC.2
    · simp only [conclusion, LCS.Finset.insert_comm]
  | axiomCompRight A hAtom ruleGamma ruleDelta =>
    refine
      ⟨.axiomCompRight A hAtom (LCS.Finset.insert C ruleGamma) ruleDelta,
        rfl, ?_, ?_⟩
    · refine ⟨trivial, ?_⟩
      simpa only [conclusion] using
        G1nnfFinsetSequent.IsNNF.insert_left hNNF hAC.2
    · rfl
  | cut _ _ _ => simp [premises] at hAxiom
  | conjLeft1 _ _ => simp [premises] at hAxiom
  | conjLeft2 _ _ => simp [premises] at hAxiom
  | conjRight _ _ => simp [premises] at hAxiom
  | disjLeft _ _ => simp [premises] at hAxiom
  | disjRight1 _ _ => simp [premises] at hAxiom
  | disjRight2 _ _ => simp [premises] at hAxiom
  | allLeft _ _ _ => simp [premises] at hAxiom
  | allRight _ _ _ => simp [premises] at hAxiom
  | exLeft _ _ _ => simp [premises] at hAxiom
  | exRight _ _ _ => simp [premises] at hAxiom

-- END PROOF
/-- A zero-premise application can be weakened on the right by extending the
context stored inside its axiom rule. The returned conclusion equality records
that the actual axiom conclusion, rather than its ignored ambient contexts, was
extended. -/
theorem applicationConditions_axiom_insert_right {L : Language}
    (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
    (C : FormulaN L)
    (hAxiom : (rule.premises Gamma Delta).length = 0)
    (hAC : rule.ApplicationConditions Gamma Delta)
    (hNNF : C.isNNF) :
    ∃ weakenedRule : G1nnfRule L,
      (weakenedRule.premises Gamma Delta).length = 0 ∧
      weakenedRule.ApplicationConditions Gamma Delta ∧
      weakenedRule.conclusion Gamma Delta =
        ((rule.conclusion Gamma Delta).1,
          LCS.Finset.insert C (rule.conclusion Gamma Delta).2) := by
-- BEGIN PROOF
  cases rule with
  | axiomPosAtomic A hAtom ruleGamma ruleDelta =>
    refine
      ⟨.axiomPosAtomic A hAtom ruleGamma (LCS.Finset.insert C ruleDelta),
        rfl, ?_, ?_⟩
    · refine ⟨trivial, ?_⟩
      simpa only [conclusion, LCS.Finset.insert_comm] using
        G1nnfFinsetSequent.IsNNF.insert_right hNNF hAC.2
    · simp only [conclusion, LCS.Finset.insert_comm]
  | axiomNegAtomic A hAtom ruleGamma ruleDelta =>
    refine
      ⟨.axiomNegAtomic A hAtom ruleGamma (LCS.Finset.insert C ruleDelta),
        rfl, ?_, ?_⟩
    · refine ⟨trivial, ?_⟩
      simpa only [conclusion, LCS.Finset.insert_comm] using
        G1nnfFinsetSequent.IsNNF.insert_right hNNF hAC.2
    · simp only [conclusion, LCS.Finset.insert_comm]
  | axiomCompLeft A hAtom ruleGamma ruleDelta =>
    refine
      ⟨.axiomCompLeft A hAtom ruleGamma (LCS.Finset.insert C ruleDelta),
        rfl, ?_, ?_⟩
    · refine ⟨trivial, ?_⟩
      simpa only [conclusion] using
        G1nnfFinsetSequent.IsNNF.insert_right hNNF hAC.2
    · rfl
  | axiomCompRight A hAtom ruleGamma ruleDelta =>
    refine
      ⟨.axiomCompRight A hAtom ruleGamma (LCS.Finset.insert C ruleDelta),
        rfl, ?_, ?_⟩
    · refine ⟨trivial, ?_⟩
      simpa only [conclusion, LCS.Finset.insert_comm] using
        G1nnfFinsetSequent.IsNNF.insert_right hNNF hAC.2
    · simp only [conclusion, LCS.Finset.insert_comm]
  | cut _ _ _ => simp [premises] at hAxiom
  | conjLeft1 _ _ => simp [premises] at hAxiom
  | conjLeft2 _ _ => simp [premises] at hAxiom
  | conjRight _ _ => simp [premises] at hAxiom
  | disjLeft _ _ => simp [premises] at hAxiom
  | disjRight1 _ _ => simp [premises] at hAxiom
  | disjRight2 _ _ => simp [premises] at hAxiom
  | allLeft _ _ _ => simp [premises] at hAxiom
  | allRight _ _ _ => simp [premises] at hAxiom
  | exLeft _ _ _ => simp [premises] at hAxiom
  | exRight _ _ _ => simp [premises] at hAxiom

end G1nnfRule

-- END PROOF
-- END PROOF
-- END PROOF
-- END PROOF
-- END PROOF
-- ===================================================================
-- Weakening: weakenTreeLeft — insert a formula into the antecedent
-- ===================================================================
/-- Internal helper: structural weakening on the left of a G1nnf
proof tree. Given a proof of Γ → Δ, produces a proof of
(insert C Γ) → Δ by pushing `insert C` through each rule's context
parameter and reconciling indices via `insert_comm`. Used as the
underlying construction for the tagged Lem 6.4.5 statement
`g1nnf_weakening_left`. -/
noncomputable def G1nnfProofTree.weakenTreeLeft {L : Language} {hL : L.withoutEquality}
    (C : FormulaN L) (hNNF : C.isNNF) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    (T : G1nnfProofTree hL Γ Δ) →
    (∀ v, v ∈ formulaFVN C → ¬ T.eigenvariables v) →
    G1nnfProofTree hL (LCS.Finset.insert C Γ) Δ
  | _, _, .axiom_ rule Gamma Delta hAxiom hAC, _ => by
    let hWeakened :=
      G1nnfRule.applicationConditions_axiom_insert_left
        rule Gamma Delta C hAxiom hAC hNNF
    let weakenedRule := Classical.choose hWeakened
    have hSpec := Classical.choose_spec hWeakened
    have hTree :=
      G1nnfProofTree.axiom_ (hL := hL) weakenedRule Gamma Delta hSpec.1 hSpec.2.1
    rw [hSpec.2.2] at hTree
    exact hTree
  | _, _, .onePremise rule Gamma Delta hPrem hAC sub, hFV =>
    have hSubFV : ∀ v, v ∈ formulaFVN C → ¬ sub.eigenvariables v := by
      intro v hv hSub
      exact hFV v hv (Or.inr hSub)
    have weakSub := weakenTreeLeft C hNNF sub hSubFV
    by
    cases rule with
    | conjLeft1 A B =>
      show G1nnfProofTree hL (LCS.Finset.insert C (LCS.Finset.insert (.conj A B) Gamma)) Delta
      rw [LCS.Finset.insert_comm C (.conj A B) Gamma]
      refine .onePremise (.conjLeft1 A B) (LCS.Finset.insert C Gamma) Delta
        hPrem
        (G1nnfRule.applicationConditions_insert_left
          (.conjLeft1 A B) Gamma Delta C hAC hNNF trivial) ?_
      show G1nnfProofTree hL (LCS.Finset.insert A (LCS.Finset.insert C Gamma)) Delta
      rw [← LCS.Finset.insert_comm C A Gamma]; exact weakSub
    | conjLeft2 A B =>
      show G1nnfProofTree hL (LCS.Finset.insert C (LCS.Finset.insert (.conj A B) Gamma)) Delta
      rw [LCS.Finset.insert_comm C (.conj A B) Gamma]
      refine .onePremise (.conjLeft2 A B) (LCS.Finset.insert C Gamma) Delta
        hPrem
        (G1nnfRule.applicationConditions_insert_left
          (.conjLeft2 A B) Gamma Delta C hAC hNNF trivial) ?_
      show G1nnfProofTree hL (LCS.Finset.insert B (LCS.Finset.insert C Gamma)) Delta
      rw [← LCS.Finset.insert_comm C B Gamma]; exact weakSub
    | allLeft x A t =>
      show G1nnfProofTree hL (LCS.Finset.insert C (LCS.Finset.insert (.all x A) Gamma)) Delta
      rw [LCS.Finset.insert_comm C (.all x A) Gamma]
      refine .onePremise (.allLeft x A t) (LCS.Finset.insert C Gamma) Delta
        hPrem
        (G1nnfRule.applicationConditions_insert_left
          (.allLeft x A t) Gamma Delta C hAC hNNF trivial) ?_
      show G1nnfProofTree hL (LCS.Finset.insert (formulaSubstN A t x) (LCS.Finset.insert C Gamma)) Delta
      rw [← LCS.Finset.insert_comm C (formulaSubstN A t x) Gamma]; exact weakSub
    | exLeft x A y =>
      have hFresh : y ∉ formulaFVN C := by
        intro hy
        exact hFV y hy (Or.inl rfl)
      have hAC' := G1nnfRule.applicationConditions_insert_left
        (.exLeft x A y) Gamma Delta C hAC hNNF hFresh
      show G1nnfProofTree hL (LCS.Finset.insert C (LCS.Finset.insert (.ex x A) Gamma)) Delta
      rw [LCS.Finset.insert_comm C (.ex x A) Gamma]
      refine .onePremise (.exLeft x A y) (LCS.Finset.insert C Gamma) Delta
        hPrem hAC' ?_
      show G1nnfProofTree hL (LCS.Finset.insert (formulaSubstN A (.var y) x) (LCS.Finset.insert C Gamma)) Delta
      rw [← LCS.Finset.insert_comm C (formulaSubstN A (.var y) x) Gamma]; exact weakSub
    | disjRight1 A B =>
      exact .onePremise (.disjRight1 A B) (LCS.Finset.insert C Gamma) Delta
        hPrem
        (G1nnfRule.applicationConditions_insert_left
          (.disjRight1 A B) Gamma Delta C hAC hNNF trivial) weakSub
    | disjRight2 A B =>
      exact .onePremise (.disjRight2 A B) (LCS.Finset.insert C Gamma) Delta
        hPrem
        (G1nnfRule.applicationConditions_insert_left
          (.disjRight2 A B) Gamma Delta C hAC hNNF trivial) weakSub
    | allRight x A y =>
      have hFresh : y ∉ formulaFVN C := by
        intro hy
        exact hFV y hy (Or.inl rfl)
      have hAC' := G1nnfRule.applicationConditions_insert_left
        (.allRight x A y) Gamma Delta C hAC hNNF hFresh
      exact .onePremise (.allRight x A y) (LCS.Finset.insert C Gamma) Delta
        hPrem hAC' weakSub
    | exRight x A t =>
      exact .onePremise (.exRight x A t) (LCS.Finset.insert C Gamma) Delta
        hPrem
        (G1nnfRule.applicationConditions_insert_left
          (.exRight x A t) Gamma Delta C hAC hNNF trivial) weakSub
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | cut _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjRight _ _ => simp [G1nnfRule.premises] at hPrem
    | disjLeft _ _ => simp [G1nnfRule.premises] at hPrem
  | _, _, .twoPremise rule Gamma Delta hPrem hAC sub1 sub2, hFV =>
    have hSub1FV : ∀ v, v ∈ formulaFVN C → ¬ sub1.eigenvariables v := by
      intro v hv hSub
      exact hFV v hv (Or.inr (Or.inl hSub))
    have hSub2FV : ∀ v, v ∈ formulaFVN C → ¬ sub2.eigenvariables v := by
      intro v hv hSub
      exact hFV v hv (Or.inr (Or.inr hSub))
    have weakSub1 := weakenTreeLeft C hNNF sub1 hSub1FV
    have weakSub2 := weakenTreeLeft C hNNF sub2 hSub2FV
    by
    cases rule with
    | cut A Lam Theta =>
      show G1nnfProofTree hL
        (LCS.Finset.insert C (LCS.Finset.union Gamma Lam))
        (LCS.Finset.union Delta Theta)
      rw [LCS.Finset.insert_union]
      exact .twoPremise (.cut A Lam Theta) (LCS.Finset.insert C Gamma) Delta
        hPrem
        (G1nnfRule.applicationConditions_insert_left
          (.cut A Lam Theta) Gamma Delta C hAC hNNF trivial) weakSub1 sub2
    | conjRight A B =>
      exact .twoPremise (.conjRight A B) (LCS.Finset.insert C Gamma) Delta
        hPrem
        (G1nnfRule.applicationConditions_insert_left
          (.conjRight A B) Gamma Delta C hAC hNNF trivial)
        weakSub1 weakSub2
    | disjLeft A B =>
      show G1nnfProofTree hL (LCS.Finset.insert C (LCS.Finset.insert (.disj A B) Gamma)) Delta
      rw [LCS.Finset.insert_comm C (.disj A B) Gamma]
      refine .twoPremise (.disjLeft A B) (LCS.Finset.insert C Gamma) Delta
        hPrem
        (G1nnfRule.applicationConditions_insert_left
          (.disjLeft A B) Gamma Delta C hAC hNNF trivial) ?_ ?_
      · show G1nnfProofTree hL (LCS.Finset.insert A (LCS.Finset.insert C Gamma)) Delta
        rw [← LCS.Finset.insert_comm C A Gamma]; exact weakSub1
      · show G1nnfProofTree hL (LCS.Finset.insert B (LCS.Finset.insert C Gamma)) Delta
        rw [← LCS.Finset.insert_comm C B Gamma]; exact weakSub2
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

/-- Structural weakening on the right: given a proof of Γ → Δ,
produce a proof of Γ → (insert C Δ). Symmetric to weakenTreeLeft. -/
noncomputable def G1nnfProofTree.weakenTreeRight {L : Language} {hL : L.withoutEquality}
    (C : FormulaN L) (hNNF : C.isNNF) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    (T : G1nnfProofTree hL Γ Δ) →
    (∀ v, v ∈ formulaFVN C → ¬ T.eigenvariables v) →
    G1nnfProofTree hL Γ (LCS.Finset.insert C Δ)
  | _, _, .axiom_ rule Gamma Delta hAxiom hAC, _ => by
    let hWeakened :=
      G1nnfRule.applicationConditions_axiom_insert_right
        rule Gamma Delta C hAxiom hAC hNNF
    let weakenedRule := Classical.choose hWeakened
    have hSpec := Classical.choose_spec hWeakened
    have hTree :=
      G1nnfProofTree.axiom_ (hL := hL) weakenedRule Gamma Delta hSpec.1 hSpec.2.1
    rw [hSpec.2.2] at hTree
    exact hTree
  | _, _, .onePremise rule Gamma Delta hPrem hAC sub, hFV =>
    have hSubFV : ∀ v, v ∈ formulaFVN C → ¬ sub.eigenvariables v := by
      intro v hv hSub
      exact hFV v hv (Or.inr hSub)
    have weakSub := weakenTreeRight C hNNF sub hSubFV
    by
    cases rule with
    | disjRight1 A B =>
      show G1nnfProofTree hL Gamma (LCS.Finset.insert C (LCS.Finset.insert (.disj A B) Delta))
      rw [LCS.Finset.insert_comm C (.disj A B) Delta]
      refine .onePremise (.disjRight1 A B) Gamma (LCS.Finset.insert C Delta)
        hPrem
        (G1nnfRule.applicationConditions_insert_right
          (.disjRight1 A B) Gamma Delta C hAC hNNF trivial) ?_
      show G1nnfProofTree hL Gamma (LCS.Finset.insert A (LCS.Finset.insert C Delta))
      rw [← LCS.Finset.insert_comm C A Delta]; exact weakSub
    | disjRight2 A B =>
      show G1nnfProofTree hL Gamma (LCS.Finset.insert C (LCS.Finset.insert (.disj A B) Delta))
      rw [LCS.Finset.insert_comm C (.disj A B) Delta]
      refine .onePremise (.disjRight2 A B) Gamma (LCS.Finset.insert C Delta)
        hPrem
        (G1nnfRule.applicationConditions_insert_right
          (.disjRight2 A B) Gamma Delta C hAC hNNF trivial) ?_
      show G1nnfProofTree hL Gamma (LCS.Finset.insert B (LCS.Finset.insert C Delta))
      rw [← LCS.Finset.insert_comm C B Delta]; exact weakSub
    | allRight x A y =>
      have hFresh : y ∉ formulaFVN C := by
        intro hy
        exact hFV y hy (Or.inl rfl)
      have hAC' := G1nnfRule.applicationConditions_insert_right
        (.allRight x A y) Gamma Delta C hAC hNNF hFresh
      show G1nnfProofTree hL Gamma (LCS.Finset.insert C (LCS.Finset.insert (.all x A) Delta))
      rw [LCS.Finset.insert_comm C (.all x A) Delta]
      refine .onePremise (.allRight x A y) Gamma (LCS.Finset.insert C Delta)
        hPrem hAC' ?_
      show G1nnfProofTree hL Gamma (LCS.Finset.insert (formulaSubstN A (.var y) x) (LCS.Finset.insert C Delta))
      rw [← LCS.Finset.insert_comm C (formulaSubstN A (.var y) x) Delta]; exact weakSub
    | exRight x A t =>
      show G1nnfProofTree hL Gamma (LCS.Finset.insert C (LCS.Finset.insert (.ex x A) Delta))
      rw [LCS.Finset.insert_comm C (.ex x A) Delta]
      refine .onePremise (.exRight x A t) Gamma (LCS.Finset.insert C Delta)
        hPrem
        (G1nnfRule.applicationConditions_insert_right
          (.exRight x A t) Gamma Delta C hAC hNNF trivial) ?_
      show G1nnfProofTree hL Gamma (LCS.Finset.insert (formulaSubstN A t x) (LCS.Finset.insert C Delta))
      rw [← LCS.Finset.insert_comm C (formulaSubstN A t x) Delta]; exact weakSub
    | conjLeft1 A B =>
      exact .onePremise (.conjLeft1 A B) Gamma (LCS.Finset.insert C Delta)
        hPrem
        (G1nnfRule.applicationConditions_insert_right
          (.conjLeft1 A B) Gamma Delta C hAC hNNF trivial) weakSub
    | conjLeft2 A B =>
      exact .onePremise (.conjLeft2 A B) Gamma (LCS.Finset.insert C Delta)
        hPrem
        (G1nnfRule.applicationConditions_insert_right
          (.conjLeft2 A B) Gamma Delta C hAC hNNF trivial) weakSub
    | allLeft x A t =>
      exact .onePremise (.allLeft x A t) Gamma (LCS.Finset.insert C Delta)
        hPrem
        (G1nnfRule.applicationConditions_insert_right
          (.allLeft x A t) Gamma Delta C hAC hNNF trivial) weakSub
    | exLeft x A y =>
      have hFresh : y ∉ formulaFVN C := by
        intro hy
        exact hFV y hy (Or.inl rfl)
      have hAC' := G1nnfRule.applicationConditions_insert_right
        (.exLeft x A y) Gamma Delta C hAC hNNF hFresh
      exact .onePremise (.exLeft x A y) Gamma (LCS.Finset.insert C Delta)
        hPrem hAC' weakSub
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | cut _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjRight _ _ => simp [G1nnfRule.premises] at hPrem
    | disjLeft _ _ => simp [G1nnfRule.premises] at hPrem
  | _, _, .twoPremise rule Gamma Delta hPrem hAC sub1 sub2, hFV =>
    have hSub1FV : ∀ v, v ∈ formulaFVN C → ¬ sub1.eigenvariables v := by
      intro v hv hSub
      exact hFV v hv (Or.inr (Or.inl hSub))
    have hSub2FV : ∀ v, v ∈ formulaFVN C → ¬ sub2.eigenvariables v := by
      intro v hv hSub
      exact hFV v hv (Or.inr (Or.inr hSub))
    have weakSub1 := weakenTreeRight C hNNF sub1 hSub1FV
    have weakSub2 := weakenTreeRight C hNNF sub2 hSub2FV
    by
    cases rule with
    | cut A Lam Theta =>
      show G1nnfProofTree hL (LCS.Finset.union Gamma Lam)
        (LCS.Finset.insert C (LCS.Finset.union Delta Theta))
      rw [LCS.Finset.insert_union]
      refine .twoPremise (.cut A Lam Theta) Gamma (LCS.Finset.insert C Delta)
        hPrem
        (G1nnfRule.applicationConditions_insert_right
          (.cut A Lam Theta) Gamma Delta C hAC hNNF trivial) ?_ sub2
      show G1nnfProofTree hL Gamma (LCS.Finset.insert A (LCS.Finset.insert C Delta))
      rw [← LCS.Finset.insert_comm C A Delta]; exact weakSub1
    | conjRight A B =>
      show G1nnfProofTree hL Gamma (LCS.Finset.insert C (LCS.Finset.insert (.conj A B) Delta))
      rw [LCS.Finset.insert_comm C (.conj A B) Delta]
      refine .twoPremise (.conjRight A B) Gamma (LCS.Finset.insert C Delta)
        hPrem
        (G1nnfRule.applicationConditions_insert_right
          (.conjRight A B) Gamma Delta C hAC hNNF trivial) ?_ ?_
      · show G1nnfProofTree hL Gamma (LCS.Finset.insert A (LCS.Finset.insert C Delta))
        rw [← LCS.Finset.insert_comm C A Delta]; exact weakSub1
      · show G1nnfProofTree hL Gamma (LCS.Finset.insert B (LCS.Finset.insert C Delta))
        rw [← LCS.Finset.insert_comm C B Delta]; exact weakSub2
    | disjLeft A B =>
      exact .twoPremise (.disjLeft A B) Gamma (LCS.Finset.insert C Delta)
        hPrem
        (G1nnfRule.applicationConditions_insert_right
          (.disjLeft A B) Gamma Delta C hAC hNNF trivial)
        weakSub1 weakSub2
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
