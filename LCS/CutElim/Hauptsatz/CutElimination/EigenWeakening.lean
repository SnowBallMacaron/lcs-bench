import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.Trees
import LCS.CutElim.Hauptsatz.CutElimination.VariableSupport
import LCS.CutElim.Hauptsatz.CutElimination.FormulaRenaming
import LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
import LCS.CutElim.Hauptsatz.CutElimination.Substitution
import LCS.CutElim.Hauptsatz.CutElimination.Hygiene

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

/-- Repeated two-sided weakening over finite lists. The resulting proof tree
has the list insertions in its type indices, and weakening preserves the
original tree's eigenvariables pointwise. -/
theorem G1nnfProofTree.weakenTreeLists {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hL Γ Δ)
    (left right : List (FormulaN L))
    (hNNFLeft : ∀ A ∈ left, A.isNNF)
    (hNNFRight : ∀ A ∈ right, A.isNNF)
    (hFVLeft :
      ∀ A ∈ left, ∀ v, v ∈ formulaFVN A → ¬ T.eigenvariables v)
    (hFVRight :
      ∀ A ∈ right, ∀ v, v ∈ formulaFVN A → ¬ T.eigenvariables v) :
    ∃ T' : G1nnfProofTree hL
        (left.foldr LCS.Finset.insert Γ)
        (right.foldr LCS.Finset.insert Δ),
      ∀ v, T'.eigenvariables v = T.eigenvariables v := by
  have weakenLeftList :
      ∀ (xs : List (FormulaN L))
        {Γ₀ Δ₀ : LCS.Finset (FormulaN L)}
        (S : G1nnfProofTree hL Γ₀ Δ₀),
        (∀ A ∈ xs, A.isNNF) →
        (∀ A ∈ xs, ∀ v, v ∈ formulaFVN A → ¬ S.eigenvariables v) →
        ∃ S' : G1nnfProofTree hL (xs.foldr LCS.Finset.insert Γ₀) Δ₀,
          ∀ v, S'.eigenvariables v = S.eigenvariables v := by
    intro xs
    induction xs with
    | nil =>
      intro Γ₀ Δ₀ S _ _
      exact ⟨S, fun _ => rfl⟩
    | cons A rest ih =>
      intro Γ₀ Δ₀ S hNNFs hFVs
      have hNNFA : A.isNNF :=
        hNNFs A (List.mem_cons.mpr (Or.inl rfl))
      have hNNFRest : ∀ B ∈ rest, B.isNNF := by
        intro B hB
        exact hNNFs B (List.mem_cons.mpr (Or.inr hB))
      have hFVRest :
          ∀ B ∈ rest, ∀ v, v ∈ formulaFVN B →
            ¬ S.eigenvariables v := by
        intro B hB
        exact hFVs B (List.mem_cons.mpr (Or.inr hB))
      obtain ⟨Srest, hEigRest⟩ :=
        ih S hNNFRest hFVRest
      have hFVA :
          ∀ v, v ∈ formulaFVN A → ¬ Srest.eigenvariables v := by
        intro v hv hEigen
        rw [hEigRest v] at hEigen
        exact hFVs A (List.mem_cons.mpr (Or.inl rfl)) v hv hEigen
      obtain ⟨S', hEigA⟩ :=
        Srest.weakenTreeLeft_preserving_eigenvariables A hNNFA hFVA
      exact ⟨S', fun v => (hEigA v).trans (hEigRest v)⟩
  obtain ⟨Tleft, hEigLeft⟩ :=
    weakenLeftList left T hNNFLeft hFVLeft
  have hFVRight' :
      ∀ A ∈ right, ∀ v, v ∈ formulaFVN A →
        ¬ Tleft.eigenvariables v := by
    intro A hA v hv hEigen
    rw [hEigLeft v] at hEigen
    exact hFVRight A hA v hv hEigen
  have weakenRightList :
      ∀ (xs : List (FormulaN L))
        {Γ₀ Δ₀ : LCS.Finset (FormulaN L)}
        (S : G1nnfProofTree hL Γ₀ Δ₀),
        (∀ A ∈ xs, A.isNNF) →
        (∀ A ∈ xs, ∀ v, v ∈ formulaFVN A → ¬ S.eigenvariables v) →
        ∃ S' : G1nnfProofTree hL Γ₀ (xs.foldr LCS.Finset.insert Δ₀),
          ∀ v, S'.eigenvariables v = S.eigenvariables v := by
    intro xs
    induction xs with
    | nil =>
      intro Γ₀ Δ₀ S _ _
      exact ⟨S, fun _ => rfl⟩
    | cons A rest ih =>
      intro Γ₀ Δ₀ S hNNFs hFVs
      have hNNFA : A.isNNF :=
        hNNFs A (List.mem_cons.mpr (Or.inl rfl))
      have hNNFRest : ∀ B ∈ rest, B.isNNF := by
        intro B hB
        exact hNNFs B (List.mem_cons.mpr (Or.inr hB))
      have hFVRest :
          ∀ B ∈ rest, ∀ v, v ∈ formulaFVN B →
            ¬ S.eigenvariables v := by
        intro B hB
        exact hFVs B (List.mem_cons.mpr (Or.inr hB))
      obtain ⟨Srest, hEigRest⟩ :=
        ih S hNNFRest hFVRest
      have hFVA :
          ∀ v, v ∈ formulaFVN A → ¬ Srest.eigenvariables v := by
        intro v hv hEigen
        rw [hEigRest v] at hEigen
        exact hFVs A (List.mem_cons.mpr (Or.inl rfl)) v hv hEigen
      obtain ⟨S', hEigA⟩ :=
        Srest.weakenTreeRight_preserving_eigenvariables A hNNFA hFVA
      exact ⟨S', fun v => (hEigA v).trans (hEigRest v)⟩
  obtain ⟨Tboth, hEigRight⟩ :=
    weakenRightList right Tleft hNNFRight hFVRight'
  exact ⟨Tboth, fun v => (hEigRight v).trans (hEigLeft v)⟩

theorem G1nnfProofTree.substTerm_depth {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (y : Nat) (t : Term L)
    (hOk : T.treeSubstOk t y) :
    (T.substTerm t y hOk).depth = T.depth := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
    simp only [G1nnfProofTree.substTerm]
    rw [G1nnfProofTree.depth_cast]
    rfl
  | onePremise rule Γ Δ hPrem hAC sub ih =>
    simp only [G1nnfProofTree.substTerm]
    rw [G1nnfProofTree.depth_cast]
    simp only [G1nnfProofTree.depth]
    rw [G1nnfProofTree.depth_cast, ih]
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
    simp only [G1nnfProofTree.substTerm]
    rw [G1nnfProofTree.depth_cast]
    simp only [G1nnfProofTree.depth]
    rw [G1nnfProofTree.depth_cast, G1nnfProofTree.depth_cast, ih1, ih2]

theorem G1nnfProofTree.substTerm_cutRank {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (y : Nat) (t : Term L)
    (hOk : T.treeSubstOk t y) :
    (T.substTerm t y hOk).cutRank = T.cutRank := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
    simp only [G1nnfProofTree.substTerm]
    rw [G1nnfProofTree.cutRank_cast]
    rfl
  | onePremise rule Γ Δ hPrem hAC sub ih =>
    simp only [G1nnfProofTree.substTerm]
    rw [G1nnfProofTree.cutRank_cast]
    simp only [G1nnfProofTree.cutRank]
    rw [G1nnfProofTree.cutRank_cast, ih]
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
    simp only [G1nnfProofTree.substTerm]
    rw [G1nnfProofTree.cutRank_cast]
    simp only [G1nnfProofTree.cutRank]
    rw [substRule_cutFormula, G1nnfProofTree.cutRank_cast,
      G1nnfProofTree.cutRank_cast, ih1, ih2]
    cases hCut : rule.cutFormula with
    | none => rfl
    | some A => simp [degree_formulaSubstN]

theorem G1nnfProofTree.substTerm_eigenvariables_eq {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (y : Nat) (t : Term L)
    (hOk : T.treeSubstOk t y) (v : Nat) :
    (T.substTerm t y hOk).eigenvariables v = T.eigenvariables v := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
    simp only [G1nnfProofTree.substTerm]
    rw [G1nnfProofTree.eigenvariables_cast]
    rfl
  | onePremise rule Γ Δ hPrem hAC sub ih =>
    simp only [G1nnfProofTree.substTerm]
    rw [G1nnfProofTree.eigenvariables_cast]
    rw [G1nnfProofTree.eigenvariables_onePremise,
      G1nnfProofTree.eigenvariables_onePremise,
      G1nnfProofTree.eigenvariables_cast, ih]
    cases rule with
    | allRight x A ev => simp only [substRule]; by_cases h : y != x <;> simp [h]
    | exLeft x A ev => simp only [substRule]; by_cases h : y != x <;> simp [h]
    | allLeft x A u => simp only [substRule]; by_cases h : y != x <;> simp [h]
    | exRight x A u => simp only [substRule]; by_cases h : y != x <;> simp [h]
    | axiomPosAtomic _ _ _ _ => rfl
    | axiomNegAtomic _ _ _ _ => rfl
    | axiomCompLeft _ _ _ _ => rfl
    | axiomCompRight _ _ _ _ => rfl
    | cut _ _ _ => rfl
    | conjLeft1 _ _ => rfl
    | conjLeft2 _ _ => rfl
    | conjRight _ _ => rfl
    | disjLeft _ _ => rfl
    | disjRight1 _ _ => rfl
    | disjRight2 _ _ => rfl
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
    simp only [G1nnfProofTree.substTerm]
    rw [G1nnfProofTree.eigenvariables_cast]
    rw [G1nnfProofTree.eigenvariables_twoPremise,
      G1nnfProofTree.eigenvariables_twoPremise,
      G1nnfProofTree.eigenvariables_cast,
      G1nnfProofTree.eigenvariables_cast, ih1, ih2]
    cases rule with
    | allRight x A ev => simp only [substRule]; by_cases h : y != x <;> simp [h]
    | exLeft x A ev => simp only [substRule]; by_cases h : y != x <;> simp [h]
    | allLeft x A u => simp only [substRule]; by_cases h : y != x <;> simp [h]
    | exRight x A u => simp only [substRule]; by_cases h : y != x <;> simp [h]
    | axiomPosAtomic _ _ _ _ => rfl
    | axiomNegAtomic _ _ _ _ => rfl
    | axiomCompLeft _ _ _ _ => rfl
    | axiomCompRight _ _ _ _ => rfl
    | cut _ _ _ => rfl
    | conjLeft1 _ _ => rfl
    | conjLeft2 _ _ => rfl
    | conjRight _ _ => rfl
    | disjLeft _ _ => rfl
    | disjRight1 _ _ => rfl
    | disjRight2 _ _ => rfl

theorem G1nnfProofTree.treeSubstOk_eigenvariables_disjoint {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (y : Nat) (t : Term L)
    (hOk : T.treeSubstOk t y) :
    (¬ T.eigenvariables y)
    ∧ (∀ v, termFV t v → ¬ T.eigenvariables v) := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
    exact ⟨False.elim, fun _ _ => False.elim⟩
  | onePremise rule Γ Δ hPrem hAC sub ih =>
    cases rule <;>
      simp_all [G1nnfRule.premises, G1nnfProofTree.treeSubstOk,
        G1nnfProofTree.eigenvariables_onePremise, ruleSubstOk]
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
    cases rule <;>
      simp_all [G1nnfRule.premises, G1nnfProofTree.treeSubstOk,
        G1nnfProofTree.eigenvariables_twoPremise, ruleSubstOk]

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

private theorem allFormulae_substTerm {L : Language} {hL : L.withoutEquality}
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

private theorem substTerm_preserves_notBound {L : Language} {hL : L.withoutEquality}
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

private theorem freeVariable_not_mem_atRoot_of_not_mem_variableSupport
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

/-- A variable `z` absent from the whole variable support of `T` is free
for `y` in every root formula, since `z` is bound in none of them. -/
theorem freeForAtRoot_var_of_not_mem_variableSupport
    {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (y z : Nat)
    (hz : z ∉ T.variableSupport) :
    freeForAtRoot T (.var z) y := by
  constructor
  · intro A hA
    apply LCS.FirstOrder.Gentzen.Hintikka.isFreeForN_of_bv_disjoint
    intro w hw hBoundA
    change w = z at hw
    subst w
    exact hz
      (T.variableSupport_of_formula_mem_allFormulae A z
        (T.mem_allFormulae_of_mem_left A hA)
        (formulaBVN_mem_formulaVariableSupport A z hBoundA))
  · intro A hA
    apply LCS.FirstOrder.Gentzen.Hintikka.isFreeForN_of_bv_disjoint
    intro w hw hBoundA
    change w = z at hw
    subst w
    exact hz
      (T.variableSupport_of_formula_mem_allFormulae A z
        (T.mem_allFormulae_of_mem_right A hA)
        (formulaBVN_mem_formulaVariableSupport A z hBoundA))

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

private inductive EigenRuleAt {L : Language}
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

end G1nnfProofTree
end LCS.CutElim.Hauptsatz
end

