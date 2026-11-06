import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.ProofTrees
import LCS.CutElim.Hauptsatz.CutElimination.CutRank
import LCS.CutElim.Hauptsatz.CutElimination.NotBound
import LCS.CutElim.Hauptsatz.CutElimination.VariableSupport
import LCS.CutElim.Hauptsatz.CutElimination.Eigenvariables
import LCS.CutElim.Hauptsatz.CutElimination.FormulaSubstitution
import LCS.CutElim.Hauptsatz.CutElimination.TreeSubstitution
import Attach
import LCS.CutElim.Hauptsatz.CutElimination.SubstitutionPreservation.ProofsStamp

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

open G1nnfProofTree in
/-- Definition 6.4.5 (companion): Variable substitution on a rule, including
its eigenvariable label. An eigenvariable equal to `y` becomes `z`; all
formulae, instantiation terms, and stored contexts are substituted as in
`substRule`. Bound-variable labels are unchanged. -/
@[blueprint "chap6__definition_6_4_5"]
noncomputable def substRuleRename {L : Language} (z y : Nat) :
    G1nnfRule L → G1nnfRule L
  | .allRight x A ev =>
    .allRight x (if y != x then formulaSubstN A (.var z) y else A)
      (if ev = y then z else ev)
  | .exLeft x A ev =>
    .exLeft x (if y != x then formulaSubstN A (.var z) y else A)
      (if ev = y then z else ev)
  | rule => substRule (.var z) y rule

/-- Renaming eigenvariable labels leaves the substituted conclusion intact. -/
theorem substRuleRename_conclusion_eq {L : Language}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L)) (z y : Nat) :
    (substRuleRename z y rule).conclusion
      (substFormulaFinset Γ (.var z) y) (substFormulaFinset Δ (.var z) y) =
    (substFormulaFinset (rule.conclusion Γ Δ).1 (.var z) y,
     substFormulaFinset (rule.conclusion Γ Δ).2 (.var z) y) := by
  rw [← substRule_conclusion_eq rule Γ Δ (.var z) y]
  cases rule <;> simp [substRuleRename, substRule, G1nnfRule.conclusion]
  all_goals split <;> rfl

/-- Variable renaming preserves the number of rule premises. -/
theorem substRuleRename_premises_length {L : Language}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L)) (z y : Nat) :
    ((substRuleRename z y rule).premises
      (substFormulaFinset Γ (.var z) y) (substFormulaFinset Δ (.var z) y)).length =
    (rule.premises Γ Δ).length := by
  cases rule <;> try rfl
  case allLeft x A t =>
    exact substRule_premises_length (.allLeft x A t) Γ Δ (.var z) y
  case exRight x A t =>
    exact substRule_premises_length (.exRight x A t) Γ Δ (.var z) y

theorem substRuleRename_eq_substRule_of_not_eigen {L : Language}
    (rule : G1nnfRule L) (z y : Nat)
    (h : G1nnfProofTree.ruleEigenlabel rule ≠ some y) :
    substRuleRename z y rule = substRule (.var z) y rule := by
  cases rule <;> simp_all [G1nnfProofTree.ruleEigenlabel, substRuleRename, substRule]
  all_goals split <;> rfl

theorem ruleSubstOk_var_of_not_eigen {L : Language}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L)) (z y : Nat)
    (hyRoot :
      (∀ A ∈ (rule.conclusion Γ Δ).1, FormulaN.notBoundIn y A) ∧
      (∀ A ∈ (rule.conclusion Γ Δ).2, FormulaN.notBoundIn y A))
    (hzRoot :
      (∀ A ∈ (rule.conclusion Γ Δ).1, z ∉ formulaVariableSupport A) ∧
      (∀ A ∈ (rule.conclusion Γ Δ).2, z ∉ formulaVariableSupport A))
    (hzRule : z ∉ rule.variableSupport)
    (h : G1nnfProofTree.ruleEigenlabel rule ≠ some y) :
    ruleSubstOk (.var z) y rule := by
  apply G1nnfProofTree.ruleSubstOk_of_hygiene rule Γ Δ (.var z) y hyRoot
  · intro w hw
    change w = z at hw
    subst w
    exact ⟨fun A hA hBV => hzRoot.1 A hA (formulaBVN_mem_formulaVariableSupport A z hBV),
      fun A hA hBV => hzRoot.2 A hA (formulaBVN_mem_formulaVariableSupport A z hBV)⟩
  · intro ev hev
    refine ⟨fun hy => h (hy ▸ hev), ?_⟩
    intro w hw hwev
    change w = z at hw
    subst w
    apply hzRule
    subst ev
    apply G1nnfProofTree.ruleEigenvariable_mem_variableSupport rule z
    cases rule <;> simp_all [G1nnfProofTree.ruleEigenlabel]

/-- Variable renaming preserves rule side conditions when `y` is not bound
in the conclusion and `z` is fresh for its formulae and stored rule data.
The old eigenvariable is allowed to equal `y`. -/
theorem substRuleRename_sideConditions {L : Language}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L)) (z y : Nat)
    (hSC : rule.SideConditions Γ Δ)
    (hyRoot :
      (∀ A ∈ (rule.conclusion Γ Δ).1, FormulaN.notBoundIn y A) ∧
      (∀ A ∈ (rule.conclusion Γ Δ).2, FormulaN.notBoundIn y A))
    (hzRoot :
      (∀ A ∈ (rule.conclusion Γ Δ).1, z ∉ formulaVariableSupport A) ∧
      (∀ A ∈ (rule.conclusion Γ Δ).2, z ∉ formulaVariableSupport A))
    (hzRule : z ∉ rule.variableSupport) :
    (substRuleRename z y rule).SideConditions
      (substFormulaFinset Γ (.var z) y) (substFormulaFinset Δ (.var z) y) := by
  by_cases h : G1nnfProofTree.ruleEigenlabel rule = some y
  · cases rule <;> try (simp [G1nnfProofTree.ruleEigenlabel] at h)
    case allRight x A ev =>
      have hev : ev = y := h
      subst ev
      obtain ⟨hFree, hPrincipal, hΓ, hΔ⟩ := hSC
      have hyPrincipal := hyRoot.2 (.all x A)
        (LCS.Finset.mem_insert.mpr (Or.inl rfl))
      have hyx : y ≠ x := fun hxy => hyPrincipal (Or.inr hxy)
      have hyA : y ∉ formulaFVN A := fun hA => hPrincipal ⟨hA, hyx⟩
      have hId := formulaSubstN_eq_self_of_not_free A (.var z) y hyA
      have hΓId := substFormulaFinset_eq_self_of_not_free Γ (.var z) y hΓ
      have hΔId := substFormulaFinset_eq_self_of_not_free Δ (.var z) y hΔ
      have hzA : z ∉ formulaVariableSupport A := fun hz =>
        hzRule (G1nnfRule.variableSupport_allRight_formula x y A z hz)
      have hFreeZ : isFreeForN (.var z) x A := by
        apply LCS.FirstOrder.Gentzen.Hintikka.isFreeForN_of_bv_disjoint
        intro w hw hwA
        change w = z at hw
        subst w
        exact hzA (formulaBVN_mem_formulaVariableSupport A z hwA)
      simp only [substRuleRename, bne_iff_ne.mpr hyx, ↓reduceIte, hId, hΓId, hΔId,
        G1nnfRule.SideConditions]
      refine ⟨hFreeZ, ?_, ?_, ?_⟩
      · exact fun hz => hzRoot.2 (.all x A)
          (LCS.Finset.mem_insert.mpr (Or.inl rfl))
          (formulaFVN_mem_formulaVariableSupport (.all x A) z hz)
      · exact fun F hF hz => hzRoot.1 F hF
          (formulaFVN_mem_formulaVariableSupport F z hz)
      · exact fun F hF hz => hzRoot.2 F (LCS.Finset.mem_insert.mpr (Or.inr hF))
          (formulaFVN_mem_formulaVariableSupport F z hz)
    case exLeft x A ev =>
      have hev : ev = y := h
      subst ev
      obtain ⟨hFree, hPrincipal, hΓ, hΔ⟩ := hSC
      have hyPrincipal := hyRoot.1 (.ex x A)
        (LCS.Finset.mem_insert.mpr (Or.inl rfl))
      have hyx : y ≠ x := fun hxy => hyPrincipal (Or.inr hxy)
      have hyA : y ∉ formulaFVN A := fun hA => hPrincipal ⟨hA, hyx⟩
      have hId := formulaSubstN_eq_self_of_not_free A (.var z) y hyA
      have hΓId := substFormulaFinset_eq_self_of_not_free Γ (.var z) y hΓ
      have hΔId := substFormulaFinset_eq_self_of_not_free Δ (.var z) y hΔ
      have hzA : z ∉ formulaVariableSupport A := fun hz =>
        hzRule (G1nnfRule.variableSupport_exLeft_formula x y A z hz)
      have hFreeZ : isFreeForN (.var z) x A := by
        apply LCS.FirstOrder.Gentzen.Hintikka.isFreeForN_of_bv_disjoint
        intro w hw hwA
        change w = z at hw
        subst w
        exact hzA (formulaBVN_mem_formulaVariableSupport A z hwA)
      simp only [substRuleRename, bne_iff_ne.mpr hyx, ↓reduceIte, hId, hΓId, hΔId,
        G1nnfRule.SideConditions]
      refine ⟨hFreeZ, ?_, ?_, ?_⟩
      · exact fun hz => hzRoot.1 (.ex x A)
          (LCS.Finset.mem_insert.mpr (Or.inl rfl))
          (formulaFVN_mem_formulaVariableSupport (.ex x A) z hz)
      · exact fun F hF hz => hzRoot.1 F (LCS.Finset.mem_insert.mpr (Or.inr hF))
          (formulaFVN_mem_formulaVariableSupport F z hz)
      · exact fun F hF hz => hzRoot.2 F hF
          (formulaFVN_mem_formulaVariableSupport F z hz)
  · rw [substRuleRename_eq_substRule_of_not_eigen rule z y h]
    exact substRule_sideConditions rule Γ Δ (.var z) y hSC
      (ruleSubstOk_var_of_not_eigen rule Γ Δ z y hyRoot hzRoot hzRule h)

/-- Variable renaming preserves the complete rule-application contract. -/
theorem substRuleRename_applicationConditions {L : Language}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L)) (z y : Nat)
    (hAC : rule.ApplicationConditions Γ Δ)
    (hyRoot :
      (∀ A ∈ (rule.conclusion Γ Δ).1, FormulaN.notBoundIn y A) ∧
      (∀ A ∈ (rule.conclusion Γ Δ).2, FormulaN.notBoundIn y A))
    (hzRoot :
      (∀ A ∈ (rule.conclusion Γ Δ).1, z ∉ formulaVariableSupport A) ∧
      (∀ A ∈ (rule.conclusion Γ Δ).2, z ∉ formulaVariableSupport A))
    (hzRule : z ∉ rule.variableSupport) :
    (substRuleRename z y rule).ApplicationConditions
      (substFormulaFinset Γ (.var z) y) (substFormulaFinset Δ (.var z) y) := by
  refine ⟨substRuleRename_sideConditions rule Γ Δ z y hAC.1 hyRoot hzRoot hzRule, ?_⟩
  rw [substRuleRename_conclusion_eq]
  exact ⟨substFormulaFinset_isNNF _ (.var z) y hAC.2.1,
    substFormulaFinset_isNNF _ (.var z) y hAC.2.2⟩

/-- Rule premises commute with variable renaming, including the case in
which the eigenvariable label itself is renamed. -/
theorem substRuleRename_premises_eq {L : Language}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L)) (z y : Nat)
    (hyRoot :
      (∀ A ∈ (rule.conclusion Γ Δ).1, FormulaN.notBoundIn y A) ∧
      (∀ A ∈ (rule.conclusion Γ Δ).2, FormulaN.notBoundIn y A))
    (hzRoot :
      (∀ A ∈ (rule.conclusion Γ Δ).1, z ∉ formulaVariableSupport A) ∧
      (∀ A ∈ (rule.conclusion Γ Δ).2, z ∉ formulaVariableSupport A))
    (hzRule : z ∉ rule.variableSupport) :
    (substRuleRename z y rule).premises
      (substFormulaFinset Γ (.var z) y) (substFormulaFinset Δ (.var z) y) =
    (rule.premises Γ Δ).map (fun p =>
      (substFormulaFinset p.1 (.var z) y, substFormulaFinset p.2 (.var z) y)) := by
  by_cases h : G1nnfProofTree.ruleEigenlabel rule = some y
  · cases rule <;> try (simp [G1nnfProofTree.ruleEigenlabel] at h)
    case allRight x A ev =>
      have hev : ev = y := h
      subst ev
      have hyPrincipal := hyRoot.2 (.all x A)
        (LCS.Finset.mem_insert.mpr (Or.inl rfl))
      have hyx : y ≠ x := fun hxy => hyPrincipal (Or.inr hxy)
      have hyA : y ∉ formulaBVN A := fun hy => hyPrincipal (Or.inl hy)
      have hzA : z ∉ formulaVariableSupport A := fun hz =>
        hzRule (G1nnfRule.variableSupport_allRight_formula x y A z hz)
      have hxz : ¬ termFV (.var z : Term L) x := by
        intro hx
        change x = z at hx
        exact hzRule (hx ▸ G1nnfRule.variableSupport_allRight_binder x y A)
      have hFree : isFreeForN (.var z) y A := by
        apply LCS.FirstOrder.Gentzen.Hintikka.isFreeForN_of_bv_disjoint
        intro w hw hwA
        change w = z at hw
        subst w
        exact hzA (formulaBVN_mem_formulaVariableSupport A z hwA)
      have hComp := formulaSubstN_composition A (.var z) (.var y) x y hyx hxz hyA hFree
      simp only [termSubst, ↓reduceIte] at hComp
      simp [substRuleRename, hyx, G1nnfRule.premises, substFormulaFinset_insert, hComp]
    case exLeft x A ev =>
      have hev : ev = y := h
      subst ev
      have hyPrincipal := hyRoot.1 (.ex x A)
        (LCS.Finset.mem_insert.mpr (Or.inl rfl))
      have hyx : y ≠ x := fun hxy => hyPrincipal (Or.inr hxy)
      have hyA : y ∉ formulaBVN A := fun hy => hyPrincipal (Or.inl hy)
      have hzA : z ∉ formulaVariableSupport A := fun hz =>
        hzRule (G1nnfRule.variableSupport_exLeft_formula x y A z hz)
      have hxz : ¬ termFV (.var z : Term L) x := by
        intro hx
        change x = z at hx
        exact hzRule (hx ▸ G1nnfRule.variableSupport_exLeft_binder x y A)
      have hFree : isFreeForN (.var z) y A := by
        apply LCS.FirstOrder.Gentzen.Hintikka.isFreeForN_of_bv_disjoint
        intro w hw hwA
        change w = z at hw
        subst w
        exact hzA (formulaBVN_mem_formulaVariableSupport A z hwA)
      have hComp := formulaSubstN_composition A (.var z) (.var y) x y hyx hxz hyA hFree
      simp only [termSubst, ↓reduceIte] at hComp
      simp [substRuleRename, hyx, G1nnfRule.premises, substFormulaFinset_insert, hComp]
  · rw [substRuleRename_eq_substRule_of_not_eigen rule z y h]
    exact substRule_premises_eq rule Γ Δ (.var z) y
      (ruleSubstOk_var_of_not_eigen rule Γ Δ z y hyRoot hzRoot hzRule h)

/-- Pointwise premise transport for variable renaming. -/
theorem substRuleRename_premises_nth_eq {L : Language}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L)) (z y n : Nat)
    (hn : n < (rule.premises Γ Δ).length)
    (hyRoot :
      (∀ A ∈ (rule.conclusion Γ Δ).1, FormulaN.notBoundIn y A) ∧
      (∀ A ∈ (rule.conclusion Γ Δ).2, FormulaN.notBoundIn y A))
    (hzRoot :
      (∀ A ∈ (rule.conclusion Γ Δ).1, z ∉ formulaVariableSupport A) ∧
      (∀ A ∈ (rule.conclusion Γ Δ).2, z ∉ formulaVariableSupport A))
    (hzRule : z ∉ rule.variableSupport) :
    ((substRuleRename z y rule).premises
      (substFormulaFinset Γ (.var z) y) (substFormulaFinset Δ (.var z) y))[n]'
      (by rw [substRuleRename_premises_length]; exact hn) =
    (substFormulaFinset ((rule.premises Γ Δ)[n]).1 (.var z) y,
     substFormulaFinset ((rule.premises Γ Δ)[n]).2 (.var z) y) := by
  have hEq := substRuleRename_premises_eq rule Γ Δ z y hyRoot hzRoot hzRule
  simp [hEq]

namespace G1nnfDeductionTree

/-- Definition 6.4.5 (finite helper): all variables occurring in a deduction
 tree's sequents or stored rule data, including binders, eigenvariable labels,
 instantiation terms, cut formulae, and stored contexts. -/
@[blueprint "chap6__definition_6_4_5"]
noncomputable def variableSupport {L : Language} {hL : L.withoutEquality} :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G1nnfDeductionTree hL Γ Δ → LCS.Finset Nat
  | Γ, Δ, .leaf _ _ _ => formulaFinsetVariableSupport (LCS.Finset.union Γ Δ)
  | _, _, .onePremise rule Γ Δ _ _ sub =>
    LCS.Finset.union
      (formulaFinsetVariableSupport (LCS.Finset.union
        (rule.conclusion Γ Δ).1 (rule.conclusion Γ Δ).2))
      (LCS.Finset.union rule.variableSupport sub.variableSupport)
  | _, _, .twoPremise rule Γ Δ _ _ sub1 sub2 =>
    LCS.Finset.union
      (formulaFinsetVariableSupport (LCS.Finset.union
        (rule.conclusion Γ Δ).1 (rule.conclusion Γ Δ).2))
      (LCS.Finset.union rule.variableSupport
        (LCS.Finset.union sub1.variableSupport sub2.variableSupport))

/-- Non-binding throughout a deduction tree implies non-binding at its root. -/
theorem notBoundIn_atRoot {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfDeductionTree hL Γ Δ)
    (y : Nat) (hy : T.notBoundIn y) :
    (∀ A ∈ Γ, FormulaN.notBoundIn y A) ∧
    (∀ A ∈ Δ, FormulaN.notBoundIn y A) := by
  have hRoot : ∀ A ∈ LCS.Finset.union Γ Δ, A ∈ T.allFormulae := by
    cases T with
    | leaf Γ Δ hNNF => exact fun A hA => hA
    | onePremise rule Γ Δ hPrem hAC sub =>
      exact fun A hA => LCS.Finset.mem_union.mpr (Or.inl hA)
    | twoPremise rule Γ Δ hPrem hAC sub1 sub2 =>
      exact fun A hA => LCS.Finset.mem_union.mpr (Or.inl hA)
  exact ⟨fun A hA => hy A (hRoot A (LCS.Finset.mem_union.mpr (Or.inl hA))),
    fun A hA => hy A (hRoot A (LCS.Finset.mem_union.mpr (Or.inr hA)))⟩

/-- Tree-wide freshness implies absence from every formula at the root. -/
theorem fresh_atRoot {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfDeductionTree hL Γ Δ)
    (z : Nat) (hz : z ∉ T.variableSupport) :
    (∀ A ∈ Γ, z ∉ formulaVariableSupport A) ∧
    (∀ A ∈ Δ, z ∉ formulaVariableSupport A) := by
  have hRoot : z ∉ formulaFinsetVariableSupport (LCS.Finset.union Γ Δ) := by
    cases T with
    | leaf Γ Δ hNNF => exact hz
    | onePremise rule Γ Δ hPrem hAC sub =>
      exact fun hv => hz (LCS.Finset.mem_union.mpr (Or.inl hv))
    | twoPremise rule Γ Δ hPrem hAC sub1 sub2 =>
      exact fun hv => hz (LCS.Finset.mem_union.mpr (Or.inl hv))
  exact ⟨fun A hA hv => hRoot (formulaVariableSupport_subset_finsetSupport _ A z
      (LCS.Finset.mem_union.mpr (Or.inl hA)) hv),
    fun A hA hv => hRoot (formulaVariableSupport_subset_finsetSupport _ A z
      (LCS.Finset.mem_union.mpr (Or.inr hA)) hv)⟩

/-- Transport a deduction tree across equal conclusion indices. -/
noncomputable def castTree {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (T : G1nnfDeductionTree hL Γ Δ) (hΓ : Γ = Γ') (hΔ : Δ = Δ') :
    G1nnfDeductionTree hL Γ' Δ' := hΓ ▸ hΔ ▸ T

/-- Transporting root indices preserves whether a deduction tree is a proof. -/
theorem isProof_castTree {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (T : G1nnfDeductionTree hL Γ Δ) (hΓ : Γ = Γ') (hΔ : Δ = Δ') :
    (T.castTree hΓ hΔ).isProof = T.isProof := by
  subst Γ'
  subst Δ'
  rfl

/-- Definition 6.4.5: `T[z/y]` substitutes `z` for `y` in every sequent
of the deduction tree. The source variable is not bound in the tree and
the target variable does not occur in it. Matching eigenvariable labels
are renamed by `substRuleRename`. Free leaves remain free leaves. -/
@[blueprint "chap6__definition_6_4_5" (main := true)]
noncomputable def substituteVar {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfDeductionTree hL Γ Δ)
    (z y : Nat) : T.notBoundIn y → z ∉ T.variableSupport →
    G1nnfDeductionTree hL (substFormulaFinset Γ (.var z) y)
      (substFormulaFinset Δ (.var z) y) := by
  induction T with
  | leaf Γ Δ hNNF =>
    intro _ _
    exact .leaf _ _ ⟨substFormulaFinset_isNNF Γ (.var z) y hNNF.1,
      substFormulaFinset_isNNF Δ (.var z) y hNNF.2⟩
  | onePremise rule Γ Δ hPrem hAC sub ih =>
    intro hy hz
    have hyRoot := (G1nnfDeductionTree.onePremise rule Γ Δ hPrem hAC sub).notBoundIn_atRoot y hy
    have hzRoot := (G1nnfDeductionTree.onePremise rule Γ Δ hPrem hAC sub).fresh_atRoot z hz
    have hzParts : z ∉ rule.variableSupport ∧ z ∉ sub.variableSupport := by
      simp only [variableSupport, LCS.Finset.mem_union, not_or] at hz
      exact hz.2
    have hySub : sub.notBoundIn y := fun A hA =>
      hy A (LCS.Finset.mem_union.mpr (Or.inr hA))
    let subNew := ih hySub hzParts.2
    have hLen : ((substRuleRename z y rule).premises
        (substFormulaFinset Γ (.var z) y) (substFormulaFinset Δ (.var z) y)).length = 1 :=
      (substRuleRename_premises_length rule Γ Δ z y).trans hPrem
    have hAC' := substRuleRename_applicationConditions rule Γ Δ z y hAC hyRoot hzRoot hzParts.1
    have hP := substRuleRename_premises_nth_eq rule Γ Δ z y 0 (by omega)
      hyRoot hzRoot hzParts.1
    let subCast := subNew.castTree
      (congrArg Prod.fst hP).symm (congrArg Prod.snd hP).symm
    let core := G1nnfDeductionTree.onePremise (substRuleRename z y rule)
      (substFormulaFinset Γ (.var z) y) (substFormulaFinset Δ (.var z) y)
      hLen hAC' subCast
    have hConc := substRuleRename_conclusion_eq rule Γ Δ z y
    exact core.castTree (congrArg Prod.fst hConc) (congrArg Prod.snd hConc)
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
    intro hy hz
    have hyRoot := (G1nnfDeductionTree.twoPremise rule Γ Δ hPrem hAC sub1 sub2).notBoundIn_atRoot y hy
    have hzRoot := (G1nnfDeductionTree.twoPremise rule Γ Δ hPrem hAC sub1 sub2).fresh_atRoot z hz
    have hzParts : z ∉ rule.variableSupport ∧
        (z ∉ sub1.variableSupport ∧ z ∉ sub2.variableSupport) := by
      simp only [variableSupport, LCS.Finset.mem_union, not_or] at hz
      exact hz.2
    have hzSubs := hzParts.2
    have hySub1 : sub1.notBoundIn y := fun A hA =>
      hy A (LCS.Finset.mem_union.mpr (Or.inr (LCS.Finset.mem_union.mpr (Or.inl hA))))
    have hySub2 : sub2.notBoundIn y := fun A hA =>
      hy A (LCS.Finset.mem_union.mpr (Or.inr (LCS.Finset.mem_union.mpr (Or.inr hA))))
    let subNew1 := ih1 hySub1 hzSubs.1
    let subNew2 := ih2 hySub2 hzSubs.2
    have hLen : ((substRuleRename z y rule).premises
        (substFormulaFinset Γ (.var z) y) (substFormulaFinset Δ (.var z) y)).length = 2 :=
      (substRuleRename_premises_length rule Γ Δ z y).trans hPrem
    have hAC' := substRuleRename_applicationConditions rule Γ Δ z y hAC hyRoot hzRoot hzParts.1
    have hP1 := substRuleRename_premises_nth_eq rule Γ Δ z y 0 (by omega)
      hyRoot hzRoot hzParts.1
    let subCast1 := subNew1.castTree
      (congrArg Prod.fst hP1).symm (congrArg Prod.snd hP1).symm
    have hP2 := substRuleRename_premises_nth_eq rule Γ Δ z y 1 (by omega)
      hyRoot hzRoot hzParts.1
    let subCast2 := subNew2.castTree
      (congrArg Prod.fst hP2).symm (congrArg Prod.snd hP2).symm
    let core := G1nnfDeductionTree.twoPremise (substRuleRename z y rule)
      (substFormulaFinset Γ (.var z) y) (substFormulaFinset Δ (.var z) y)
      hLen hAC' subCast1 subCast2
    have hConc := substRuleRename_conclusion_eq rule Γ Δ z y
    exact core.castTree (congrArg Prod.fst hConc) (congrArg Prod.snd hConc)

/-- Variable renaming under Definition 6.4.5 preserves proof trees:
all axiom leaves remain axiom leaves. -/
theorem substituteVar_isProof {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfDeductionTree hL Γ Δ)
    (z y : Nat) : ∀ (hy : T.notBoundIn y) (hz : z ∉ T.variableSupport),
    T.isProof → (T.substituteVar z y hy hz).isProof := by
  induction T with
  | leaf Γ Δ hNNF =>
    intro hy hz hProof
    obtain ⟨rule, hArity, hAC, hConc⟩ := hProof
    have hOk : ruleSubstOk (.var z) y rule := by
      cases rule <;> simp [G1nnfRule.premises] at hArity <;> trivial
    change ∃ rule' : G1nnfRule L, (rule'.premises _ _).length = 0 ∧
      rule'.ApplicationConditions _ _ ∧ rule'.conclusion _ _ = _
    refine ⟨substRule (.var z) y rule, ?_, ?_, ?_⟩
    · rw [substRule_premises_length]
      exact hArity
    · exact substRule_applicationConditions rule Γ Δ (.var z) y hAC hOk
    · rw [substRule_conclusion_eq, hConc]
  | onePremise rule Γ Δ hPrem hAC sub ih =>
    intro hy hz hProof
    simp only [substituteVar, isProof_castTree, isProof]
    exact ih _ _ hProof
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
    intro hy hz hProof
    simp only [substituteVar, isProof_castTree, isProof]
    exact ⟨ih1 _ _ hProof.1, ih2 _ _ hProof.2⟩

end G1nnfDeductionTree

/-- Definition 6.4.5 (rule companion): substitute in rule data. An
instantiation witness is substituted when the resulting term is free for the
binder in the substituted body; otherwise its original value is retained.
Under the free-occurrence proviso, the latter case has no effect on the
principal premise formula. Eigenvariable labels remain unchanged. -/
@[blueprint "chap6__definition_6_4_5"]
noncomputable def substRuleOfFreeOccurrences {L : Language} (t : Term L) (y : Nat)
    (rule : G1nnfRule L) : G1nnfRule L := by
  classical
  exact match rule with
  | .allLeft x A u =>
    let B := if y != x then formulaSubstN A t y else A
    .allLeft x B (if isFreeForN (termSubst u t y) x B then termSubst u t y else u)
  | .exRight x A u =>
    let B := if y != x then formulaSubstN A t y else A
    .exRight x B (if isFreeForN (termSubst u t y) x B then termSubst u t y else u)
  | _ => substRule t y rule

/-- Rule transport for the free-occurrence reading of term substitution:
both the conclusion and every premise are substituted, with legality retained. -/
theorem substRuleOfFreeOccurrences_spec {L : Language}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L)) (t : Term L) (y : Nat)
    (hAC : rule.ApplicationConditions Γ Δ)
    (hBound : ∀ s ∈ rule.conclusion Γ Δ :: rule.premises Γ Δ,
      ∀ A ∈ LCS.Finset.union s.1 s.2, FormulaN.notBoundIn y A)
    (hFree : ∀ s ∈ rule.conclusion Γ Δ :: rule.premises Γ Δ,
      ∀ A ∈ LCS.Finset.union s.1 s.2, formulaFVN A y → isFreeForN t y A)
    (hEigen : ∀ ev, (match rule with
      | .allRight _ _ w => ev = w
      | .exLeft _ _ w => ev = w
      | _ => False) → y ≠ ev ∧ ¬ termFV t ev) :
    let r := substRuleOfFreeOccurrences t y rule
    r.ApplicationConditions (substFormulaFinset Γ t y) (substFormulaFinset Δ t y) ∧
    r.conclusion (substFormulaFinset Γ t y) (substFormulaFinset Δ t y) =
      (substFormulaFinset (rule.conclusion Γ Δ).1 t y,
       substFormulaFinset (rule.conclusion Γ Δ).2 t y) ∧
    r.premises (substFormulaFinset Γ t y) (substFormulaFinset Δ t y) =
      (rule.premises Γ Δ).map (fun s =>
        (substFormulaFinset s.1 t y, substFormulaFinset s.2 t y)) := by
  -- REPAIR(T6-27): proof pending
  sorry

namespace G1nnfDeductionTree

/-- Definition 6.4.5: eigenvariables label universal-right and
existential-left inferences throughout a deduction tree. Free leaves have none. -/
@[blueprint "chap6__definition_6_4_5"]
def eigenvariables {L : Language} {hL : L.withoutEquality} :
    {Γ Δ : LCS.Finset (FormulaN L)} → G1nnfDeductionTree hL Γ Δ → Set Nat
  | _, _, .leaf _ _ _ => fun _ => False
  | _, _, .onePremise rule _ _ _ _ sub => fun v =>
    (match rule with
      | .allRight _ _ ev => v = ev
      | .exLeft _ _ ev => v = ev
      | _ => False) ∨ sub.eigenvariables v
  | _, _, .twoPremise rule _ _ _ _ sub1 sub2 => fun v =>
    (match rule with
      | .allRight _ _ ev => v = ev
      | .exLeft _ _ ev => v = ev
      | _ => False) ∨ sub1.eigenvariables v ∨ sub2.eigenvariables v

/-- Definition 6.4.5: `t` is free for `y` in each formula of the tree
in which `y` occurs free. -/
@[blueprint "chap6__definition_6_4_5"]
noncomputable def freeForOccurrences {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfDeductionTree hL Γ Δ)
    (t : Term L) (y : Nat) : Prop :=
  ∀ A ∈ T.allFormulae, formulaFVN A y → isFreeForN t y A

/-- Every formula at the root of a deduction tree occurs in the tree. -/
theorem mem_allFormulae_atRoot {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfDeductionTree hL Γ Δ)
    (A : FormulaN L) (hA : A ∈ LCS.Finset.union Γ Δ) : A ∈ T.allFormulae := by
  cases T <;> simp only [allFormulae]
  · exact hA
  · exact LCS.Finset.mem_union.mpr (Or.inl hA)
  · exact LCS.Finset.mem_union.mpr (Or.inl hA)

/-- Definition 6.4.5: replace `y` by `t` in every sequent of a deduction
tree. The source variable is not bound, the term is free for it wherever it
occurs free, and neither `y` nor any variable of `t` is an eigenvariable.
The construction preserves the branching structure and substitutes free leaves. -/
@[blueprint "chap6__definition_6_4_5" (main := true)]
noncomputable def substTerm {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfDeductionTree hL Γ Δ)
    (t : Term L) (y : Nat) :
    T.notBoundIn y → T.freeForOccurrences t y →
    (¬ T.eigenvariables y) → (∀ v, termFV t v → ¬ T.eigenvariables v) →
    G1nnfDeductionTree hL (substFormulaFinset Γ t y) (substFormulaFinset Δ t y) := by
  induction T with
  | leaf Γ Δ hNNF =>
    intro _ _ _ _
    exact .leaf _ _ ⟨substFormulaFinset_isNNF Γ t y hNNF.1,
      substFormulaFinset_isNNF Δ t y hNNF.2⟩
  | onePremise rule Γ Δ hPrem hAC sub ih =>
    intro hy hFree hyEigen htEigen
    let T := G1nnfDeductionTree.onePremise rule Γ Δ hPrem hAC sub
    have hMem : ∀ s ∈ rule.conclusion Γ Δ :: rule.premises Γ Δ,
        ∀ A ∈ LCS.Finset.union s.1 s.2, A ∈ T.allFormulae := by
      intro s hs A hA
      rcases List.mem_cons.mp hs with rfl | hs
      · exact T.mem_allFormulae_atRoot A hA
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
        have hi0 : i = 0 := by omega
        subst i
        exact LCS.Finset.mem_union.mpr (Or.inr (sub.mem_allFormulae_atRoot A hA))
    have hSpec := substRuleOfFreeOccurrences_spec rule Γ Δ t y hAC
      (fun s hs A hA => hy A (hMem s hs A hA))
      (fun s hs A hA => hFree A (hMem s hs A hA)) (by
        intro ev hev
        constructor
        · intro hye; subst ev
          exact hyEigen (Or.inl (by cases rule <;> exact hev))
        · intro htv
          exact htEigen ev htv (Or.inl (by cases rule <;> exact hev)))
    have hLen : ((substRuleOfFreeOccurrences t y rule).premises
        (substFormulaFinset Γ t y) (substFormulaFinset Δ t y)).length = 1 := by
      rw [hSpec.2.2, List.length_map, hPrem]
    let subNew0 := ih
      (fun A hA => hy A (LCS.Finset.mem_union.mpr (Or.inr (hA))))
      (fun A hA => hFree A (LCS.Finset.mem_union.mpr (Or.inr (hA))))
      (fun hE => hyEigen (Or.inr (hE)))
      (fun v hv hE => htEigen v hv (Or.inr (hE)))
    have hPEq0 : ((substRuleOfFreeOccurrences t y rule).premises
        (substFormulaFinset Γ t y) (substFormulaFinset Δ t y))[0]'(by omega) =
        (substFormulaFinset ((rule.premises Γ Δ)[0]'(by omega)).1 t y,
         substFormulaFinset ((rule.premises Γ Δ)[0]'(by omega)).2 t y) := by
      simp only [hSpec.2.2, List.getElem_map]
    let subCast0 := subNew0.castTree
      (congrArg Prod.fst hPEq0).symm (congrArg Prod.snd hPEq0).symm
    let core := G1nnfDeductionTree.onePremise (substRuleOfFreeOccurrences t y rule)
      (substFormulaFinset Γ t y) (substFormulaFinset Δ t y)
      hLen hSpec.1 subCast0
    exact core.castTree (congrArg Prod.fst hSpec.2.1) (congrArg Prod.snd hSpec.2.1)
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
    intro hy hFree hyEigen htEigen
    let T := G1nnfDeductionTree.twoPremise rule Γ Δ hPrem hAC sub1 sub2
    have hMem : ∀ s ∈ rule.conclusion Γ Δ :: rule.premises Γ Δ,
        ∀ A ∈ LCS.Finset.union s.1 s.2, A ∈ T.allFormulae := by
      intro s hs A hA
      rcases List.mem_cons.mp hs with rfl | hs
      · exact T.mem_allFormulae_atRoot A hA
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
        have hiCases : i = 0 ∨ i = 1 := by omega
        rcases hiCases with rfl | rfl
        · exact LCS.Finset.mem_union.mpr (Or.inr (LCS.Finset.mem_union.mpr (Or.inl (sub1.mem_allFormulae_atRoot A hA))))
        · exact LCS.Finset.mem_union.mpr (Or.inr (LCS.Finset.mem_union.mpr (Or.inr (sub2.mem_allFormulae_atRoot A hA))))
    have hSpec := substRuleOfFreeOccurrences_spec rule Γ Δ t y hAC
      (fun s hs A hA => hy A (hMem s hs A hA))
      (fun s hs A hA => hFree A (hMem s hs A hA)) (by
        intro ev hev
        constructor
        · intro hye; subst ev
          exact hyEigen (Or.inl (by cases rule <;> exact hev))
        · intro htv
          exact htEigen ev htv (Or.inl (by cases rule <;> exact hev)))
    have hLen : ((substRuleOfFreeOccurrences t y rule).premises
        (substFormulaFinset Γ t y) (substFormulaFinset Δ t y)).length = 2 := by
      rw [hSpec.2.2, List.length_map, hPrem]
    let subNew0 := ih1
      (fun A hA => hy A (LCS.Finset.mem_union.mpr (Or.inr (LCS.Finset.mem_union.mpr (Or.inl hA)))))
      (fun A hA => hFree A (LCS.Finset.mem_union.mpr (Or.inr (LCS.Finset.mem_union.mpr (Or.inl hA)))))
      (fun hE => hyEigen (Or.inr (Or.inl hE)))
      (fun v hv hE => htEigen v hv (Or.inr (Or.inl hE)))
    have hPEq0 : ((substRuleOfFreeOccurrences t y rule).premises
        (substFormulaFinset Γ t y) (substFormulaFinset Δ t y))[0]'(by omega) =
        (substFormulaFinset ((rule.premises Γ Δ)[0]'(by omega)).1 t y,
         substFormulaFinset ((rule.premises Γ Δ)[0]'(by omega)).2 t y) := by
      simp only [hSpec.2.2, List.getElem_map]
    let subCast0 := subNew0.castTree
      (congrArg Prod.fst hPEq0).symm (congrArg Prod.snd hPEq0).symm
    let subNew1 := ih2
      (fun A hA => hy A (LCS.Finset.mem_union.mpr (Or.inr (LCS.Finset.mem_union.mpr (Or.inr hA)))))
      (fun A hA => hFree A (LCS.Finset.mem_union.mpr (Or.inr (LCS.Finset.mem_union.mpr (Or.inr hA)))))
      (fun hE => hyEigen (Or.inr (Or.inr hE)))
      (fun v hv hE => htEigen v hv (Or.inr (Or.inr hE)))
    have hPEq1 : ((substRuleOfFreeOccurrences t y rule).premises
        (substFormulaFinset Γ t y) (substFormulaFinset Δ t y))[1]'(by omega) =
        (substFormulaFinset ((rule.premises Γ Δ)[1]'(by omega)).1 t y,
         substFormulaFinset ((rule.premises Γ Δ)[1]'(by omega)).2 t y) := by
      simp only [hSpec.2.2, List.getElem_map]
    let subCast1 := subNew1.castTree
      (congrArg Prod.fst hPEq1).symm (congrArg Prod.snd hPEq1).symm
    let core := G1nnfDeductionTree.twoPremise (substRuleOfFreeOccurrences t y rule)
      (substFormulaFinset Γ t y) (substFormulaFinset Δ t y)
      hLen hSpec.1 subCast0 subCast1
    exact core.castTree (congrArg Prod.fst hSpec.2.1) (congrArg Prod.snd hSpec.2.1)

end G1nnfDeductionTree

/-- A proof tree's underlying deduction tree has only axiom leaves. -/
theorem G1nnfProofTree.forgetProofTree_isProof {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hL Γ Δ) :
    T.forgetProofTree.isProof := by
  induction T with
  | axiom_ rule Γ Δ hPrem hAC =>
    refine ⟨rule, ?_, ?_, ?_⟩ <;>
      cases rule <;> simp_all [G1nnfRule.premises, G1nnfRule.conclusion,
        G1nnfRule.ApplicationConditions, G1nnfRule.SideConditions]
  | onePremise rule Γ Δ hPrem hAC sub ih => exact ih
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 => exact ⟨ih1, ih2⟩

/-- Lemma 6.4.3(ii): term substitution under the source provisos preserves
axiom leaves, hence takes proofs to proofs. -/
theorem G1nnfDeductionTree.substTerm_isProof {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfDeductionTree hL Γ Δ)
    (t : Term L) (y : Nat) : ∀ (hy : T.notBoundIn y)
      (hf : T.freeForOccurrences t y) (he : ¬ T.eigenvariables y)
      (ht : ∀ v, termFV t v → ¬ T.eigenvariables v),
    T.isProof → (T.substTerm t y hy hf he ht).isProof := by
  induction T with
  | leaf Γ Δ hNNF =>
    intro hy hf he ht hProof
    obtain ⟨rule, hArity, hAC, hConc⟩ := hProof
    have hOk : ruleSubstOk t y rule := by
      cases rule <;> simp [G1nnfRule.premises] at hArity <;> trivial
    change ∃ rule' : G1nnfRule L, (rule'.premises _ _).length = 0 ∧
      rule'.ApplicationConditions _ _ ∧ rule'.conclusion _ _ = _
    refine ⟨substRule t y rule, ?_, ?_, ?_⟩
    · rw [substRule_premises_length]; exact hArity
    · exact substRule_applicationConditions rule Γ Δ t y hAC hOk
    · rw [substRule_conclusion_eq, hConc]
  | onePremise rule Γ Δ hPrem hAC sub ih =>
    intro hy hf he ht hProof
    simp only [G1nnfDeductionTree.substTerm, G1nnfDeductionTree.isProof_castTree,
      G1nnfDeductionTree.isProof]
    exact ih _ _ _ _ hProof
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
    intro hy hf he ht hProof
    simp only [G1nnfDeductionTree.substTerm, G1nnfDeductionTree.isProof_castTree,
      G1nnfDeductionTree.isProof]
    exact ⟨ih1 _ _ _ _ hProof.1, ih2 _ _ _ _ hProof.2⟩

/-- Lemma 6.4.3: substituting a fresh variable, or an admissible term,
in the underlying deduction tree of a proof gives a proof of the substituted
sequent with the same depth and cut rank. The term proviso concerns exactly
those formulas in which the source variable occurs free. -/
@[attach_debt, blueprint "chap6__lemma_6_4_3" (main := true)]
theorem g1nnf_term_subst_preservation {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hL Γ Δ) (y : Nat)
    (hNotBound : T.forgetProofTree.notBoundIn y) :
    (∀ z (hz : z ∉ T.forgetProofTree.variableSupport),
      let D := T.forgetProofTree.substituteVar z y hNotBound hz
      ∃ hD : D.isProof, (D.toProofTree hD).depth = T.depth ∧
        (D.toProofTree hD).cutRank = T.cutRank) ∧
    (∀ t (hf : T.forgetProofTree.freeForOccurrences t y)
      (he : ¬ T.forgetProofTree.eigenvariables y)
      (ht : ∀ v, termFV t v → ¬ T.forgetProofTree.eigenvariables v),
      let D := T.forgetProofTree.substTerm t y hNotBound hf he ht
      ∃ hD : D.isProof, (D.toProofTree hD).depth = T.depth ∧
        (D.toProofTree hD).cutRank = T.cutRank) 

end LCS.CutElim.Hauptsatz
end
