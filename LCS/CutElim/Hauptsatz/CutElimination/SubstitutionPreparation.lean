import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.ProofTrees
import LCS.CutElim.Hauptsatz.CutElimination.CutRank
import LCS.CutElim.Hauptsatz.CutElimination.NotBound
import LCS.CutElim.Hauptsatz.CutElimination.VariableSupport
import LCS.CutElim.Hauptsatz.CutElimination.Eigenvariables
import LCS.CutElim.Hauptsatz.CutElimination.TreeTransport
import LCS.CutElim.Hauptsatz.CutElimination.FormulaSubstitution
import LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
import LCS.CutElim.Hauptsatz.CutElimination.TreeSubstitution

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz
namespace G1nnfProofTree

theorem allFormulae_substTerm {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (t : Term L) (y : Nat)
    (hOk : T.treeSubstOk t y) :
    (T.substTerm t y hOk).allFormulae =
      substFormulaFinset T.allFormulae t y := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
      simp only [G1nnfProofTree.substTerm]
      rw [allFormulae_transport]
      simp only [G1nnfProofTree.allFormulae]
      rw [substRule_conclusion_eq, substFormulaFinset_union]
  | onePremise rule Γ Δ hPrem hAC sub ih =>
      simp only [G1nnfProofTree.substTerm]
      rw [allFormulae_transport]
      simp only [G1nnfProofTree.allFormulae]
      rw [allFormulae_transport, ih, substRule_conclusion_eq,
        substFormulaFinset_union, substFormulaFinset_union]
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
      simp only [G1nnfProofTree.substTerm]
      rw [allFormulae_transport]
      simp only [G1nnfProofTree.allFormulae]
      rw [allFormulae_transport, allFormulae_transport, ih1, ih2,
        substRule_conclusion_eq, substFormulaFinset_union,
        substFormulaFinset_union, substFormulaFinset_union]

theorem substTerm_preserves_notBound {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (t : Term L) (y w : Nat)
    (hOk : T.treeSubstOk t y) (hw : T.notBoundIn w) :
    (T.substTerm t y hOk).notBoundIn w := by
  intro A hA
  rw [allFormulae_substTerm] at hA
  obtain ⟨B, hB, rfl⟩ := LCS.Finset.mem_image.mp hA
  intro hBound
  exact
    hw B hB
      (LCS.FirstOrder.Gentzen.Hintikka.formulaBVN_formulaSubstN
        B t y w hBound)

theorem freeVariable_not_mem_atRoot_of_not_mem_variableSupport
    {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (z : Nat)
    (hz : z ∉ T.variableSupport) :
    (∀ A ∈ Γ, z ∉ formulaFVN A) ∧
    (∀ A ∈ Δ, z ∉ formulaFVN A) := by
  constructor
  · intro A hA hzA
    apply hz
    exact
      T.variableSupport_of_formula_mem_allFormulae A z
        (T.mem_allFormulae_of_mem_left A hA)
        (formulaFVN_mem_formulaVariableSupport A z hzA)
  · intro A hA hzA
    apply hz
    exact
      T.variableSupport_of_formula_mem_allFormulae A z
        (T.mem_allFormulae_of_mem_right A hA)
        (formulaFVN_mem_formulaVariableSupport A z hzA)

structure EigenFresheningResult {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ)
    (v : Nat) (avoid : LCS.Finset Nat) where
  tree : G1nnfProofTree hL Γ Δ
  depth_eq : tree.depth = T.depth
  cutRank_eq : tree.cutRank = T.cutRank
  notBound_avoid :
    ∀ w, w ∈ avoid → tree.notBoundIn w
  eigen_avoid :
    ∀ w, w ∈ avoid → tree.eigenvariables w →
      w ≠ v ∧ T.eigenvariables w

theorem EigenFresheningResult.notEigen_target {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    {T : G1nnfProofTree hL Γ Δ} {v : Nat}
    {avoid : LCS.Finset Nat}
    (R : EigenFresheningResult T v avoid)
    (hv : v ∈ avoid) :
    ¬ R.tree.eigenvariables v := by
  intro hEigen
  exact (R.eigen_avoid v hv hEigen).1 rfl

noncomputable def EigenFresheningResult.rebuildOne
    {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L)
    (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 1)
    (hAC : rule.ApplicationConditions Γ Δ)
    (sub : G1nnfProofTree hL
      ((rule.premises Γ Δ)[0]'(by omega)).1
      ((rule.premises Γ Δ)[0]'(by omega)).2)
    (v : Nat) (avoid : LCS.Finset Nat)
    (hBound :
      ∀ w, w ∈ avoid →
        (G1nnfProofTree.onePremise
          rule Γ Δ hPrem hAC sub).notBoundIn w)
    (R : EigenFresheningResult sub v avoid)
    (hNoRoot : ruleEigenlabel rule ≠ some v) :
    EigenFresheningResult
      (G1nnfProofTree.onePremise rule Γ Δ hPrem hAC sub)
      v avoid := by
  let T' :=
    G1nnfProofTree.onePremise
      rule Γ Δ hPrem hAC R.tree
  refine
    { tree := T'
      depth_eq := ?_
      cutRank_eq := ?_
      notBound_avoid := ?_
      eigen_avoid := ?_ }
  · simp only [T', G1nnfProofTree.depth]
    exact congrArg (· + 1) R.depth_eq
  · simp only [T', G1nnfProofTree.cutRank]
    exact R.cutRank_eq
  · intro w hw A hA
    simp only [T', G1nnfProofTree.allFormulae] at hA
    rcases LCS.Finset.mem_union.mp hA with hRoot | hSub
    · apply hBound w hw A
      exact LCS.Finset.mem_union.mpr (Or.inl hRoot)
    · exact R.notBound_avoid w hw A hSub
  · intro w hw hEigen
    simp only [T', G1nnfProofTree.eigenvariables_onePremise] at hEigen
    rcases hEigen with hRule | hSub
    · have hwv : w ≠ v := by
        intro hwv
        subst w
        exact hNoRoot
          (ruleEigenlabel_eq_some_of_eigenMatch rule v hRule)
      refine ⟨hwv, ?_⟩
      rw [G1nnfProofTree.eigenvariables_onePremise]
      exact Or.inl hRule
    · obtain ⟨hwv, hSubOld⟩ := R.eigen_avoid w hw hSub
      refine ⟨hwv, ?_⟩
      rw [G1nnfProofTree.eigenvariables_onePremise]
      exact Or.inr hSubOld

noncomputable def EigenFresheningResult.rebuildTwo
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
    (v : Nat) (avoid : LCS.Finset Nat)
    (hBound :
      ∀ w, w ∈ avoid →
        (G1nnfProofTree.twoPremise
          rule Γ Δ hPrem hAC sub1 sub2).notBoundIn w)
    (R1 : EigenFresheningResult sub1 v avoid)
    (R2 : EigenFresheningResult sub2 v avoid)
    (hNoRoot : ruleEigenlabel rule ≠ some v) :
    EigenFresheningResult
      (G1nnfProofTree.twoPremise
        rule Γ Δ hPrem hAC sub1 sub2)
      v avoid := by
  let T' :=
    G1nnfProofTree.twoPremise
      rule Γ Δ hPrem hAC R1.tree R2.tree
  refine
    { tree := T'
      depth_eq := ?_
      cutRank_eq := ?_
      notBound_avoid := ?_
      eigen_avoid := ?_ }
  · simp only [T', G1nnfProofTree.depth]
    rw [R1.depth_eq, R2.depth_eq]
  · simp only [T', G1nnfProofTree.cutRank]
    rw [R1.cutRank_eq, R2.cutRank_eq]
  · intro w hw A hA
    simp only [T', G1nnfProofTree.allFormulae] at hA
    rcases LCS.Finset.mem_union.mp hA with hRoot | hSubs
    · apply hBound w hw A
      exact LCS.Finset.mem_union.mpr (Or.inl hRoot)
    · rcases LCS.Finset.mem_union.mp hSubs with hSub1 | hSub2
      · exact R1.notBound_avoid w hw A hSub1
      · exact R2.notBound_avoid w hw A hSub2
  · intro w hw hEigen
    simp only [T', G1nnfProofTree.eigenvariables_twoPremise] at hEigen
    rcases hEigen with hRule | hSubs
    · have hwv : w ≠ v := by
        intro hwv
        subst w
        exact hNoRoot
          (ruleEigenlabel_eq_some_of_eigenMatch rule v hRule)
      refine ⟨hwv, ?_⟩
      rw [G1nnfProofTree.eigenvariables_twoPremise]
      exact Or.inl hRule
    · rcases hSubs with hSub1 | hSub2
      · obtain ⟨hwv, hSubOld⟩ := R1.eigen_avoid w hw hSub1
        refine ⟨hwv, ?_⟩
        rw [G1nnfProofTree.eigenvariables_twoPremise]
        exact Or.inr (Or.inl hSubOld)
      · obtain ⟨hwv, hSubOld⟩ := R2.eigen_avoid w hw hSub2
        refine ⟨hwv, ?_⟩
        rw [G1nnfProofTree.eigenvariables_twoPremise]
        exact Or.inr (Or.inr hSubOld)

inductive EigenRuleAt {L : Language}
    (v : Nat) : G1nnfRule L → Type where
  | allRight (x : Nat) (A : FormulaN L) :
      EigenRuleAt v (.allRight x A v)
  | exLeft (x : Nat) (A : FormulaN L) :
      EigenRuleAt v (.exLeft x A v)

def eigenRuleAt_of_target {L : Language}
    (rule : G1nnfRule L) (v : Nat)
    (hTarget : ruleEigenlabel rule = some v) :
    EigenRuleAt v rule := by
  cases rule with
  | allRight x A ev =>
      simp only [ruleEigenlabel, Option.some.injEq] at hTarget
      subst ev
      exact .allRight x A
  | exLeft x A ev =>
      simp only [ruleEigenlabel, Option.some.injEq] at hTarget
      subst ev
      exact .exLeft x A
  | axiomPosAtomic _ _ _ _ => simp [ruleEigenlabel] at hTarget
  | axiomNegAtomic _ _ _ _ => simp [ruleEigenlabel] at hTarget
  | axiomCompLeft _ _ _ _ => simp [ruleEigenlabel] at hTarget
  | axiomCompRight _ _ _ _ => simp [ruleEigenlabel] at hTarget
  | cut _ _ _ => simp [ruleEigenlabel] at hTarget
  | conjLeft1 _ _ => simp [ruleEigenlabel] at hTarget
  | conjLeft2 _ _ => simp [ruleEigenlabel] at hTarget
  | conjRight _ _ => simp [ruleEigenlabel] at hTarget
  | disjLeft _ _ => simp [ruleEigenlabel] at hTarget
  | disjRight1 _ _ => simp [ruleEigenlabel] at hTarget
  | disjRight2 _ _ => simp [ruleEigenlabel] at hTarget
  | allLeft _ _ _ => simp [ruleEigenlabel] at hTarget
  | exRight _ _ _ => simp [ruleEigenlabel] at hTarget

theorem no_ruleEigenlabel_of_two_premises {L : Language}
    (rule : G1nnfRule L)
    (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 2)
    (v : Nat) :
    ruleEigenlabel rule ≠ some v := by
  intro hTarget
  cases eigenRuleAt_of_target rule v hTarget with
  | allRight x A =>
      simp [G1nnfRule.premises] at hPrem
  | exLeft x A =>
      simp [G1nnfRule.premises] at hPrem

noncomputable def freshenMatchingAllRight {L : Language} {hL : L.withoutEquality}
    (x v : Nat) (A : FormulaN L)
    (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem :
      ((G1nnfRule.allRight x A v).premises Γ Δ).length = 1)
    (hAC :
      (G1nnfRule.allRight x A v).ApplicationConditions Γ Δ)
    (sub : G1nnfProofTree hL
      (((G1nnfRule.allRight x A v).premises Γ Δ)[0]'(by omega)).1
      (((G1nnfRule.allRight x A v).premises Γ Δ)[0]'(by omega)).2)
    (avoid : LCS.Finset Nat) (hv : v ∈ avoid)
    (hBound :
      ∀ w, w ∈ avoid →
        (G1nnfProofTree.onePremise
          (.allRight x A v) Γ Δ hPrem hAC sub).notBoundIn w)
    (R : EigenFresheningResult sub v avoid) :
    EigenFresheningResult
      (G1nnfProofTree.onePremise
        (.allRight x A v) Γ Δ hPrem hAC sub)
      v avoid := by
  have hPremCanon :
      ((G1nnfRule.allRight x A v).premises Γ Δ).length = 1 := by
    rfl
  have hp : hPrem = hPremCanon := Subsingleton.elim _ _
  cases hp
  let extra :=
    LCS.Finset.union avoid
      (G1nnfRule.allRight x A v).variableSupport
  let z := R.tree.freshVariableAvoiding extra
  have hzTree : z ∉ R.tree.variableSupport := by
    simpa only [z] using
      R.tree.freshVariableAvoiding_not_mem_variableSupport extra
  have hzExtra : z ∉ extra := by
    simpa only [z] using
      R.tree.freshVariableAvoiding_not_mem_extra extra
  have hzAvoid : z ∉ avoid := by
    intro hz
    exact hzExtra (LCS.Finset.mem_union.mpr (Or.inl hz))
  have hzRule :
      z ∉ (G1nnfRule.allRight x A v).variableSupport := by
    intro hz
    exact hzExtra (LCS.Finset.mem_union.mpr (Or.inr hz))
  have hzBound : R.tree.notBoundIn z := by
    simpa only [z] using
      R.tree.freshVariableAvoiding_notBoundIn extra
  have hzEigen : ¬ R.tree.eigenvariables z := by
    intro hEigen
    exact hzTree (eigenvariables_mem_variableSupport R.tree z hEigen)
  have hvEigen : ¬ R.tree.eigenvariables v :=
    R.notEigen_target hv
  have hOk : R.tree.treeSubstOk (.var z) v := by
    apply treeSubstOk_of_hygiene
    · exact R.notBound_avoid v hv
    · intro w hw
      change w = z at hw
      subst w
      exact hzBound
    · exact hvEigen
    · intro w hw hEigen
      change w = z at hw
      subst w
      exact hzEigen hEigen
  let S := R.tree.substTerm (.var z) v hOk
  have hSC := hAC.1
  have hΓEq :
      substFormulaFinset Γ (.var z) v = Γ :=
    substFormulaFinset_eq_self_of_not_free
      Γ (.var z) v hSC.2.2.1
  have hΔEq :
      substFormulaFinset Δ (.var z) v = Δ :=
    substFormulaFinset_eq_self_of_not_free
      Δ (.var z) v hSC.2.2.2
  have hvRoot :=
    (G1nnfProofTree.onePremise
      (.allRight x A v) Γ Δ hPrem hAC sub
      ).notBoundIn_atRoot v (hBound v hv)
  have hvPrincipal : FormulaN.notBoundIn v (.all x A) :=
    hvRoot.2 (.all x A)
      (LCS.Finset.mem_insert.mpr (Or.inl rfl))
  have hxv : x ≠ v := by
    intro hxv
    exact hvPrincipal (Or.inr hxv.symm)
  have hvBoundA : v ∉ formulaBVN A :=
    fun h => hvPrincipal (Or.inl h)
  have hvFreeA : v ∉ formulaFVN A := by
    intro h
    exact hSC.2.1 ⟨h, Ne.symm hxv⟩
  have hInstance :
      formulaSubstN
          (formulaSubstN A (.var v) x) (.var z) v =
        formulaSubstN A (.var z) x :=
    formulaSubstN_eigenInstance
      A x v z hxv hvFreeA hvBoundA
  have hPremiseDelta :
      substFormulaFinset
          (LCS.Finset.insert
            (formulaSubstN A (.var v) x) Δ)
          (.var z) v =
        LCS.Finset.insert
          (formulaSubstN A (.var z) x) Δ := by
    rw [substFormulaFinset_insert, hInstance, hΔEq]
  have hPremZ :
      ((G1nnfRule.allRight x A z).premises Γ Δ).length = 1 := by
    rfl
  have hSubGamma :
      substFormulaFinset
          (((G1nnfRule.allRight x A v).premises Γ Δ)[0]'(by omega)).1
          (.var z) v =
        (((G1nnfRule.allRight x A z).premises Γ Δ)[0]'(by omega)).1 := by
    simpa [G1nnfRule.premises] using hΓEq
  have hSubDelta :
      substFormulaFinset
          (((G1nnfRule.allRight x A v).premises Γ Δ)[0]'(by omega)).2
          (.var z) v =
        (((G1nnfRule.allRight x A z).premises Γ Δ)[0]'(by omega)).2 := by
    simpa [G1nnfRule.premises] using hPremiseDelta
  let S' := S.castTree hSubGamma hSubDelta
  have hzA : z ∉ formulaVariableSupport A := by
    intro h
    exact hzRule
      (G1nnfRule.variableSupport_allRight_formula x v A z h)
  have hzBV : z ∉ formulaBVN A :=
    fun h => hzA (formulaBVN_mem_formulaVariableSupport A z h)
  have hFreeZ : isFreeForN (.var z) x A := by
    apply
      LCS.FirstOrder.Gentzen.Hintikka.isFreeForN_of_bv_disjoint
    intro w hw hBoundA
    change w = z at hw
    subst w
    exact hzBV hBoundA
  have hFreshPrincipalZ : z ∉ formulaFVN (.all x A) := by
    intro h
    exact hzA
      (formulaFVN_mem_formulaVariableSupport A z h.1)
  have hFreshChild :=
    freeVariable_not_mem_atRoot_of_not_mem_variableSupport
      R.tree z hzTree
  have hFreshΓZ : ∀ F ∈ Γ, z ∉ formulaFVN F :=
    hFreshChild.1
  have hFreshΔZ : ∀ F ∈ Δ, z ∉ formulaFVN F := by
    intro F hF
    exact hFreshChild.2 F
      (LCS.Finset.mem_insert.mpr (Or.inr hF))
  have hACZ :
      (G1nnfRule.allRight x A z).ApplicationConditions Γ Δ :=
    ⟨G1nnfRule.sideConditions_allRight_of_fresh
        x z A Γ Δ hFreeZ hFreshPrincipalZ hFreshΓZ hFreshΔZ,
      hAC.2⟩
  let T' :=
    G1nnfProofTree.onePremise
      (.allRight x A z) Γ Δ hPremZ hACZ S'
  refine
    { tree := T'
      depth_eq := ?_
      cutRank_eq := ?_
      notBound_avoid := ?_
      eigen_avoid := ?_ }
  · calc
      T'.depth = S'.depth + 1 := rfl
      _ = S.depth + 1 := by
        exact congrArg (· + 1)
          (by
            simpa only [S'] using
              depth_castTree S hSubGamma hSubDelta)
      _ = R.tree.depth + 1 := by
        exact congrArg (· + 1)
          (by
            simpa only [S] using
              R.tree.substTerm_depth v (.var z) hOk)
      _ = sub.depth + 1 := by rw [R.depth_eq]
      _ =
          (G1nnfProofTree.onePremise
            (.allRight x A v) Γ Δ hPrem hAC sub).depth := rfl
  · calc
      T'.cutRank = S'.cutRank := rfl
      _ = S.cutRank := by
        simpa only [S'] using
          cutRank_castTree S hSubGamma hSubDelta
      _ = R.tree.cutRank := by
        simpa only [S] using
          R.tree.substTerm_cutRank v (.var z) hOk
      _ = sub.cutRank := R.cutRank_eq
      _ =
          (G1nnfProofTree.onePremise
            (.allRight x A v) Γ Δ hPrem hAC sub).cutRank := rfl
  · intro w hw F hF
    simp only [T', G1nnfProofTree.allFormulae] at hF
    rcases LCS.Finset.mem_union.mp hF with hRoot | hSub
    · apply hBound w hw F
      exact LCS.Finset.mem_union.mpr (Or.inl hRoot)
    · have hSBound :=
        substTerm_preserves_notBound
          R.tree (.var z) v w hOk (R.notBound_avoid w hw)
      change S.notBoundIn w at hSBound
      have hS'Bound : S'.notBoundIn w :=
        (by
          have hCast :
              S'.notBoundIn w ↔ S.notBoundIn w := by
            simpa only [S'] using
              notBoundIn_cast S hSubGamma hSubDelta w
          exact hCast.2 hSBound)
      exact hS'Bound F hSub
  · intro w hw hEigen
    simp only [T', G1nnfProofTree.eigenvariables_onePremise] at hEigen
    rcases hEigen with hwz | hSub
    · subst w
      exact (hzAvoid hw).elim
    · have hSub' := hSub
      have hCast :
          S'.eigenvariables w = S.eigenvariables w := by
        simpa only [S'] using
          eigenvariables_castTree S hSubGamma hSubDelta w
      rw [hCast] at hSub'
      have hSubst :
          S.eigenvariables w = R.tree.eigenvariables w := by
        simpa only [S] using
          R.tree.substTerm_eigenvariables_eq
            v (.var z) hOk w
      rw [hSubst] at hSub'
      obtain ⟨hwv, hOld⟩ := R.eigen_avoid w hw hSub'
      refine ⟨hwv, ?_⟩
      rw [G1nnfProofTree.eigenvariables_onePremise]
      exact Or.inr hOld

noncomputable def freshenMatchingExLeft {L : Language} {hL : L.withoutEquality}
    (x v : Nat) (A : FormulaN L)
    (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem :
      ((G1nnfRule.exLeft x A v).premises Γ Δ).length = 1)
    (hAC :
      (G1nnfRule.exLeft x A v).ApplicationConditions Γ Δ)
    (sub : G1nnfProofTree hL
      (((G1nnfRule.exLeft x A v).premises Γ Δ)[0]'(by omega)).1
      (((G1nnfRule.exLeft x A v).premises Γ Δ)[0]'(by omega)).2)
    (avoid : LCS.Finset Nat) (hv : v ∈ avoid)
    (hBound :
      ∀ w, w ∈ avoid →
        (G1nnfProofTree.onePremise
          (.exLeft x A v) Γ Δ hPrem hAC sub).notBoundIn w)
    (R : EigenFresheningResult sub v avoid) :
    EigenFresheningResult
      (G1nnfProofTree.onePremise
        (.exLeft x A v) Γ Δ hPrem hAC sub)
      v avoid := by
  have hPremCanon :
      ((G1nnfRule.exLeft x A v).premises Γ Δ).length = 1 := by
    rfl
  have hp : hPrem = hPremCanon := Subsingleton.elim _ _
  cases hp
  let extra :=
    LCS.Finset.union avoid
      (G1nnfRule.exLeft x A v).variableSupport
  let z := R.tree.freshVariableAvoiding extra
  have hzTree : z ∉ R.tree.variableSupport := by
    simpa only [z] using
      R.tree.freshVariableAvoiding_not_mem_variableSupport extra
  have hzExtra : z ∉ extra := by
    simpa only [z] using
      R.tree.freshVariableAvoiding_not_mem_extra extra
  have hzAvoid : z ∉ avoid := by
    intro hz
    exact hzExtra (LCS.Finset.mem_union.mpr (Or.inl hz))
  have hzRule :
      z ∉ (G1nnfRule.exLeft x A v).variableSupport := by
    intro hz
    exact hzExtra (LCS.Finset.mem_union.mpr (Or.inr hz))
  have hzBound : R.tree.notBoundIn z := by
    simpa only [z] using
      R.tree.freshVariableAvoiding_notBoundIn extra
  have hzEigen : ¬ R.tree.eigenvariables z := by
    intro hEigen
    exact hzTree (eigenvariables_mem_variableSupport R.tree z hEigen)
  have hvEigen : ¬ R.tree.eigenvariables v :=
    R.notEigen_target hv
  have hOk : R.tree.treeSubstOk (.var z) v := by
    apply treeSubstOk_of_hygiene
    · exact R.notBound_avoid v hv
    · intro w hw
      change w = z at hw
      subst w
      exact hzBound
    · exact hvEigen
    · intro w hw hEigen
      change w = z at hw
      subst w
      exact hzEigen hEigen
  let S := R.tree.substTerm (.var z) v hOk
  have hSC := hAC.1
  have hΓEq :
      substFormulaFinset Γ (.var z) v = Γ :=
    substFormulaFinset_eq_self_of_not_free
      Γ (.var z) v hSC.2.2.1
  have hΔEq :
      substFormulaFinset Δ (.var z) v = Δ :=
    substFormulaFinset_eq_self_of_not_free
      Δ (.var z) v hSC.2.2.2
  have hvRoot :=
    (G1nnfProofTree.onePremise
      (.exLeft x A v) Γ Δ hPrem hAC sub
      ).notBoundIn_atRoot v (hBound v hv)
  have hvPrincipal : FormulaN.notBoundIn v (.ex x A) :=
    hvRoot.1 (.ex x A)
      (LCS.Finset.mem_insert.mpr (Or.inl rfl))
  have hxv : x ≠ v := by
    intro hxv
    exact hvPrincipal (Or.inr hxv.symm)
  have hvBoundA : v ∉ formulaBVN A :=
    fun h => hvPrincipal (Or.inl h)
  have hvFreeA : v ∉ formulaFVN A := by
    intro h
    exact hSC.2.1 ⟨h, Ne.symm hxv⟩
  have hInstance :
      formulaSubstN
          (formulaSubstN A (.var v) x) (.var z) v =
        formulaSubstN A (.var z) x :=
    formulaSubstN_eigenInstance
      A x v z hxv hvFreeA hvBoundA
  have hPremiseGamma :
      substFormulaFinset
          (LCS.Finset.insert
            (formulaSubstN A (.var v) x) Γ)
          (.var z) v =
        LCS.Finset.insert
          (formulaSubstN A (.var z) x) Γ := by
    rw [substFormulaFinset_insert, hInstance, hΓEq]
  have hPremZ :
      ((G1nnfRule.exLeft x A z).premises Γ Δ).length = 1 := by
    rfl
  have hSubGamma :
      substFormulaFinset
          (((G1nnfRule.exLeft x A v).premises Γ Δ)[0]'(by omega)).1
          (.var z) v =
        (((G1nnfRule.exLeft x A z).premises Γ Δ)[0]'(by omega)).1 := by
    simpa [G1nnfRule.premises] using hPremiseGamma
  have hSubDelta :
      substFormulaFinset
          (((G1nnfRule.exLeft x A v).premises Γ Δ)[0]'(by omega)).2
          (.var z) v =
        (((G1nnfRule.exLeft x A z).premises Γ Δ)[0]'(by omega)).2 := by
    simpa [G1nnfRule.premises] using hΔEq
  let S' := S.castTree hSubGamma hSubDelta
  have hzA : z ∉ formulaVariableSupport A := by
    intro h
    exact hzRule
      (G1nnfRule.variableSupport_exLeft_formula x v A z h)
  have hzBV : z ∉ formulaBVN A :=
    fun h => hzA (formulaBVN_mem_formulaVariableSupport A z h)
  have hFreeZ : isFreeForN (.var z) x A := by
    apply
      LCS.FirstOrder.Gentzen.Hintikka.isFreeForN_of_bv_disjoint
    intro w hw hBoundA
    change w = z at hw
    subst w
    exact hzBV hBoundA
  have hFreshPrincipalZ : z ∉ formulaFVN (.ex x A) := by
    intro h
    exact hzA
      (formulaFVN_mem_formulaVariableSupport A z h.1)
  have hFreshChild :=
    freeVariable_not_mem_atRoot_of_not_mem_variableSupport
      R.tree z hzTree
  have hFreshΓZ : ∀ F ∈ Γ, z ∉ formulaFVN F := by
    intro F hF
    exact hFreshChild.1 F
      (LCS.Finset.mem_insert.mpr (Or.inr hF))
  have hFreshΔZ : ∀ F ∈ Δ, z ∉ formulaFVN F :=
    hFreshChild.2
  have hACZ :
      (G1nnfRule.exLeft x A z).ApplicationConditions Γ Δ :=
    ⟨G1nnfRule.sideConditions_exLeft_of_fresh
        x z A Γ Δ hFreeZ hFreshPrincipalZ hFreshΓZ hFreshΔZ,
      hAC.2⟩
  let T' :=
    G1nnfProofTree.onePremise
      (.exLeft x A z) Γ Δ hPremZ hACZ S'
  refine
    { tree := T'
      depth_eq := ?_
      cutRank_eq := ?_
      notBound_avoid := ?_
      eigen_avoid := ?_ }
  · calc
      T'.depth = S'.depth + 1 := rfl
      _ = S.depth + 1 := by
        exact congrArg (· + 1)
          (by
            simpa only [S'] using
              depth_castTree S hSubGamma hSubDelta)
      _ = R.tree.depth + 1 := by
        exact congrArg (· + 1)
          (by
            simpa only [S] using
              R.tree.substTerm_depth v (.var z) hOk)
      _ = sub.depth + 1 := by rw [R.depth_eq]
      _ =
          (G1nnfProofTree.onePremise
            (.exLeft x A v) Γ Δ hPrem hAC sub).depth := rfl
  · calc
      T'.cutRank = S'.cutRank := rfl
      _ = S.cutRank := by
        simpa only [S'] using
          cutRank_castTree S hSubGamma hSubDelta
      _ = R.tree.cutRank := by
        simpa only [S] using
          R.tree.substTerm_cutRank v (.var z) hOk
      _ = sub.cutRank := R.cutRank_eq
      _ =
          (G1nnfProofTree.onePremise
            (.exLeft x A v) Γ Δ hPrem hAC sub).cutRank := rfl
  · intro w hw F hF
    simp only [T', G1nnfProofTree.allFormulae] at hF
    rcases LCS.Finset.mem_union.mp hF with hRoot | hSub
    · apply hBound w hw F
      exact LCS.Finset.mem_union.mpr (Or.inl hRoot)
    · have hSBound :=
        substTerm_preserves_notBound
          R.tree (.var z) v w hOk (R.notBound_avoid w hw)
      change S.notBoundIn w at hSBound
      have hS'Bound : S'.notBoundIn w :=
        (by
          have hCast :
              S'.notBoundIn w ↔ S.notBoundIn w := by
            simpa only [S'] using
              notBoundIn_cast S hSubGamma hSubDelta w
          exact hCast.2 hSBound)
      exact hS'Bound F hSub
  · intro w hw hEigen
    simp only [T', G1nnfProofTree.eigenvariables_onePremise] at hEigen
    rcases hEigen with hwz | hSub
    · subst w
      exact (hzAvoid hw).elim
    · have hSub' := hSub
      have hCast :
          S'.eigenvariables w = S.eigenvariables w := by
        simpa only [S'] using
          eigenvariables_castTree S hSubGamma hSubDelta w
      rw [hCast] at hSub'
      have hSubst :
          S.eigenvariables w = R.tree.eigenvariables w := by
        simpa only [S] using
          R.tree.substTerm_eigenvariables_eq
            v (.var z) hOk w
      rw [hSubst] at hSub'
      obtain ⟨hwv, hOld⟩ := R.eigen_avoid w hw hSub'
      refine ⟨hwv, ?_⟩
      rw [G1nnfProofTree.eigenvariables_onePremise]
      exact Or.inr hOld

noncomputable def freshenEigenvariable {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ)
    (v : Nat) (avoid : LCS.Finset Nat)
    (hv : v ∈ avoid) :
    (∀ w, w ∈ avoid → T.notBoundIn w) →
      EigenFresheningResult T v avoid := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
      intro hBound
      refine
        { tree := G1nnfProofTree.axiom_ rule Γ Δ hAxiom hAC
          depth_eq := rfl
          cutRank_eq := rfl
          notBound_avoid := hBound
          eigen_avoid := ?_ }
      intro w hw hEigen
      exact hEigen.elim
  | onePremise rule Γ Δ hPrem hAC sub ih =>
      intro hBound
      have hSubBound :
          ∀ w, w ∈ avoid → sub.notBoundIn w := by
        intro w hw
        exact
          G1nnfProofTree.notBoundIn_onePremise_subtree
            rule Γ Δ hPrem hAC sub w (hBound w hw)
      let R := ih hSubBound
      by_cases hTarget : ruleEigenlabel rule = some v
      · cases eigenRuleAt_of_target rule v hTarget with
        | allRight x A =>
          exact
            freshenMatchingAllRight
              x v A Γ Δ hPrem hAC sub avoid hv hBound R
        | exLeft x A =>
          exact
            freshenMatchingExLeft
              x v A Γ Δ hPrem hAC sub avoid hv hBound R
      · exact
          EigenFresheningResult.rebuildOne
            rule Γ Δ hPrem hAC sub v avoid hBound R hTarget
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
      intro hBound
      have hSubsBound :
          ∀ w, w ∈ avoid →
            sub1.notBoundIn w ∧ sub2.notBoundIn w := by
        intro w hw
        exact
          G1nnfProofTree.notBoundIn_twoPremise_subtrees
            rule Γ Δ hPrem hAC sub1 sub2 w (hBound w hw)
      let R1 :=
        ih1 (fun w hw => (hSubsBound w hw).1)
      let R2 :=
        ih2 (fun w hw => (hSubsBound w hw).2)
      exact
        EigenFresheningResult.rebuildTwo
          rule Γ Δ hPrem hAC sub1 sub2 v avoid hBound R1 R2
          (no_ruleEigenlabel_of_two_premises
            rule Γ Δ hPrem v)

/-! ### Finite two-phase substitution preparation

The first pass removes every forbidden label from bound positions, including
hidden cut formulae and stored rule data.  The second pass changes only
conflicting eigenlabels.  Both passes keep the indexed root fixed. -/
theorem termFV_of_mem_termVarIndicesList {L : Language}
    (t : Term L) (v : Nat) :
    v ∈ termVarIndicesList t → termFV t v := by
  induction t with
  | var x =>
      intro hv
      change v = x
      simpa [termVarIndicesList] using hv
  | const c =>
      intro hv
      simpa [termVarIndicesList] using hv
  | func f ts ih =>
      intro hv
      simp only [termVarIndicesList] at hv
      rcases
          (mem_foldl_append_termVariableIndices v ts
            (List.ofFn fun i : Fin (L.funArity f) => i) []).1 hv with
        hEmpty | ⟨i, hi, hvi⟩
      · exact (List.not_mem_nil hEmpty).elim
      · exact ⟨i, ih i hvi⟩

theorem mem_termVarIndicesList_of_termFV {L : Language}
    (t : Term L) (v : Nat) (hv : termFV t v) :
    v ∈ termVarIndicesList t := by
  have hSupport := termFV_mem_termVariableSupport t v hv
  simpa only [termVariableSupport, LCS.Finset.mem_ofList] using hSupport

theorem substitutionTargets_notBound_atRoot {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (t : Term L) (y : Nat)
    (hy : T.notBoundIn y)
    (hFree : freeForAtRoot T t y) :
    ∀ w, w ∈ y :: termVarIndicesList t →
      (∀ A ∈ Γ, FormulaN.notBoundIn w A) ∧
      (∀ A ∈ Δ, FormulaN.notBoundIn w A) := by
  intro w hw
  rcases List.mem_cons.mp hw with hwy | hw
  · subst w
    exact T.notBoundIn_atRoot y hy
  · have hwFV : termFV t w :=
      termFV_of_mem_termVarIndicesList t w hw
    have hyRoot := T.notBoundIn_atRoot y hy
    constructor
    · intro A hA
      exact
        FormulaN.notBoundIn_and_freeFor_termFV_not_bound
          A t y w (hyRoot.1 A hA) (hFree.1 A hA) hwFV
    · intro A hA
      exact
        FormulaN.notBoundIn_and_freeFor_termFV_not_bound
          A t y w (hyRoot.2 A hA) (hFree.2 A hA) hwFV

structure BoundHygieneResult {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (targets : List Nat) where
  tree : G1nnfProofTree hL Γ Δ
  depth_eq : tree.depth = T.depth
  cutRank_eq : tree.cutRank = T.cutRank
  eigenvariables_eq :
    ∀ w, tree.eigenvariables w = T.eigenvariables w
  notBound_targets :
    ∀ w, w ∈ targets → tree.notBoundIn w

noncomputable def hygienizeBoundVariables {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (targets : List Nat)
    (hRoot :
      ∀ w, w ∈ targets →
        (∀ A ∈ Γ, FormulaN.notBoundIn w A) ∧
        (∀ A ∈ Δ, FormulaN.notBoundIn w A)) :
    BoundHygieneResult T targets := by
  induction targets generalizing T with
  | nil =>
      refine
        { tree := T
          depth_eq := rfl
          cutRank_eq := rfl
          eigenvariables_eq := fun _ => rfl
          notBound_targets := ?_ }
      intro w hw
      exact (List.not_mem_nil hw).elim
  | cons v targets ih =>
      have hTailRoot :
          ∀ w, w ∈ targets →
            (∀ A ∈ Γ, FormulaN.notBoundIn w A) ∧
            (∀ A ∈ Δ, FormulaN.notBoundIn w A) := by
        intro w hw
        exact hRoot w (List.mem_cons.mpr (Or.inr hw))
      let R := ih T hTailRoot
      let extra := LCS.Finset.ofList (v :: targets)
      let z := R.tree.freshVariableAvoiding extra
      have hzTree : z ∉ R.tree.variableSupport := by
        simpa only [z] using
          R.tree.freshVariableAvoiding_not_mem_variableSupport extra
      have hzExtra : z ∉ extra := by
        simpa only [z] using
          R.tree.freshVariableAvoiding_not_mem_extra extra
      have hvz : v ≠ z := by
        intro hvz
        have hvMem : v ∈ extra := by
          simpa only [extra, LCS.Finset.mem_ofList] using
            (List.mem_cons.mpr (Or.inl rfl) :
              v ∈ v :: targets)
        exact hzExtra (hvz ▸ hvMem)
      have hRootV :
          (∀ A ∈ Γ, FormulaN.notBoundIn v A) ∧
          (∀ A ∈ Δ, FormulaN.notBoundIn v A) :=
        hRoot v (List.mem_cons.mpr (Or.inl rfl))
      let T' :=
        R.tree.alphaRenameBoundAtRoot
          v z hvz hzTree hRootV
      refine
        { tree := T'
          depth_eq := ?_
          cutRank_eq := ?_
          eigenvariables_eq := ?_
          notBound_targets := ?_ }
      · calc
          T'.depth = R.tree.depth := by
            simpa only [T'] using
              R.tree.alphaRenameBoundAtRoot_depth
                v z hvz hzTree hRootV
          _ = T.depth := R.depth_eq
      · calc
          T'.cutRank = R.tree.cutRank := by
            simpa only [T'] using
              R.tree.alphaRenameBoundAtRoot_cutRank
                v z hvz hzTree hRootV
          _ = T.cutRank := R.cutRank_eq
      · intro w
        calc
          T'.eigenvariables w = R.tree.eigenvariables w := by
            simpa only [T'] using
              R.tree.alphaRenameBoundAtRoot_eigenvariables_eq
                v z hvz hzTree hRootV w
          _ = T.eigenvariables w := R.eigenvariables_eq w
      · intro w hw
        rcases List.mem_cons.mp hw with hwv | hwTail
        · subst w
          simpa only [T'] using
            R.tree.alphaRenameBoundAtRoot_notBound_target
              v z hvz hzTree hRootV
        · have hwz : w ≠ z := by
            intro hwz
            have hwMem : w ∈ extra := by
              simpa only [extra, LCS.Finset.mem_ofList] using
                (List.mem_cons.mpr (Or.inr hwTail) :
                  w ∈ v :: targets)
            exact hzExtra (hwz ▸ hwMem)
          simpa only [T'] using
            R.tree.alphaRenameBoundAtRoot_preserves_notBound
              v z w hvz hzTree hRootV hwz
                (R.notBound_targets w hwTail)

structure EigenHygieneResult {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (targets : List Nat)
    (avoid : LCS.Finset Nat) where
  tree : G1nnfProofTree hL Γ Δ
  depth_eq : tree.depth = T.depth
  cutRank_eq : tree.cutRank = T.cutRank
  notBound_avoid :
    ∀ w, w ∈ avoid → tree.notBoundIn w
  notEigen_targets :
    ∀ w, w ∈ targets → ¬ tree.eigenvariables w
  eigenvariables_from_original :
    ∀ w, w ∈ avoid → tree.eigenvariables w →
      T.eigenvariables w

noncomputable def hygienizeEigenvariables {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (targets : List Nat)
    (avoid : LCS.Finset Nat)
    (hTargets : ∀ w, w ∈ targets → w ∈ avoid)
    (hBound : ∀ w, w ∈ avoid → T.notBoundIn w) :
    EigenHygieneResult T targets avoid := by
  induction targets generalizing T with
  | nil =>
      refine
        { tree := T
          depth_eq := rfl
          cutRank_eq := rfl
          notBound_avoid := hBound
          notEigen_targets := ?_
          eigenvariables_from_original := ?_ }
      · intro w hw
        exact (List.not_mem_nil hw).elim
      · intro w hw hEigen
        exact hEigen
  | cons v targets ih =>
      have hv : v ∈ avoid :=
        hTargets v (List.mem_cons.mpr (Or.inl rfl))
      let R := T.freshenEigenvariable v avoid hv hBound
      have hTailTargets :
          ∀ w, w ∈ targets → w ∈ avoid := by
        intro w hw
        exact hTargets w (List.mem_cons.mpr (Or.inr hw))
      let Q :=
        ih R.tree hTailTargets R.notBound_avoid
      refine
        { tree := Q.tree
          depth_eq := ?_
          cutRank_eq := ?_
          notBound_avoid := Q.notBound_avoid
          notEigen_targets := ?_
          eigenvariables_from_original := ?_ }
      · exact Q.depth_eq.trans R.depth_eq
      · exact Q.cutRank_eq.trans R.cutRank_eq
      · intro w hw
        rcases List.mem_cons.mp hw with hwv | hwTail
        · intro hEigen
          have hR :
              R.tree.eigenvariables w :=
            Q.eigenvariables_from_original w
              (hTargets w
                (List.mem_cons.mpr (Or.inl hwv))) hEigen
          subst w
          exact R.notEigen_target hv hR
        · exact Q.notEigen_targets w hwTail
      · intro w hw hEigen
        have hR :
            R.tree.eigenvariables w :=
          Q.eigenvariables_from_original w hw hEigen
        exact (R.eigen_avoid w hw hR).2

structure SubstitutionPreparation {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (t : Term L) (y : Nat) where
  tree : G1nnfProofTree hL Γ Δ
  depth_eq : tree.depth = T.depth
  cutRank_eq : tree.cutRank = T.cutRank
  treeSubstOk : tree.treeSubstOk t y

/-- Internal realization of Gallier's root-only substitution hypotheses.
The returned tree has the same indexed conclusion, depth, and cut rank, but
its hidden binders and eigenlabels have been made safe for direct
substitution. -/
noncomputable def prepareSubstitution {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (t : Term L) (y : Nat)
    (hy : T.notBoundIn y)
    (hFree : freeForAtRoot T t y) :
    SubstitutionPreparation T t y := by
  let targets := y :: termVarIndicesList t
  let avoid := LCS.Finset.ofList targets
  have hRoot :
      ∀ w, w ∈ targets →
        (∀ A ∈ Γ, FormulaN.notBoundIn w A) ∧
        (∀ A ∈ Δ, FormulaN.notBoundIn w A) := by
    intro w hw
    apply substitutionTargets_notBound_atRoot T t y hy hFree
    simpa only [targets] using hw
  let B := hygienizeBoundVariables T targets hRoot
  have hTargetsAvoid :
      ∀ w, w ∈ targets → w ∈ avoid := by
    intro w hw
    simpa only [avoid, LCS.Finset.mem_ofList] using hw
  have hBound :
      ∀ w, w ∈ avoid → B.tree.notBoundIn w := by
    intro w hw
    apply B.notBound_targets w
    simpa only [avoid, LCS.Finset.mem_ofList] using hw
  let E :=
    hygienizeEigenvariables
      B.tree targets avoid hTargetsAvoid hBound
  have hyTarget : y ∈ targets := by
    simp [targets]
  have hyAvoid : y ∈ avoid :=
    hTargetsAvoid y hyTarget
  have hyBound : E.tree.notBoundIn y :=
    E.notBound_avoid y hyAvoid
  have htBound :
      ∀ w, termFV t w → E.tree.notBoundIn w := by
    intro w hw
    have hwTarget : w ∈ targets := by
      simp only [targets, List.mem_cons]
      exact Or.inr (mem_termVarIndicesList_of_termFV t w hw)
    exact E.notBound_avoid w (hTargetsAvoid w hwTarget)
  have hyEigen : ¬ E.tree.eigenvariables y :=
    E.notEigen_targets y hyTarget
  have htEigen :
      ∀ w, termFV t w → ¬ E.tree.eigenvariables w := by
    intro w hw
    have hwTarget : w ∈ targets := by
      simp only [targets, List.mem_cons]
      exact Or.inr (mem_termVarIndicesList_of_termFV t w hw)
    exact E.notEigen_targets w hwTarget
  refine
    { tree := E.tree
      depth_eq := ?_
      cutRank_eq := ?_
      treeSubstOk :=
        treeSubstOk_of_hygiene
          E.tree t y hyBound htBound hyEigen htEigen }
  · exact E.depth_eq.trans B.depth_eq
  · exact E.cutRank_eq.trans B.cutRank_eq

end G1nnfProofTree
end LCS.CutElim.Hauptsatz
end
