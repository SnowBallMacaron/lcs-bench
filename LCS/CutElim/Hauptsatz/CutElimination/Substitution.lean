import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.Trees
import LCS.CutElim.Hauptsatz.CutElimination.VariableSupport
import LCS.CutElim.Hauptsatz.CutElimination.FormulaRenaming
import LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

/-- Internal substitution helper: the direct per-rule preconditions needed
by `substRule`. This implementation bundle is deliberately stronger and more
local than Gallier's public hypotheses (`G1nnfProofTree.notBoundIn`,
`freeForAtRoot`, and `G1nnfProofTree.freeForEverywhere`). In particular, it
must not be used as the public contract of Lemma 6.4.4. -/
def ruleSubstOk {L : Language} (t : Term L) (y : Nat) (rule : G1nnfRule L) : Prop :=
  match rule with
  | .allLeft x A _ =>
    y ≠ x ∧ ¬ termFV t x ∧ ¬ formulaBVN A y ∧ isFreeForN t y A
  | .allRight x A ev =>
    y ≠ x ∧ ¬ termFV t x ∧ ¬ formulaBVN A y ∧ isFreeForN t y A ∧ y ≠ ev
      ∧ (∀ v, termFV t v → v ≠ ev)
  | .exLeft x A ev =>
    y ≠ x ∧ ¬ termFV t x ∧ ¬ formulaBVN A y ∧ isFreeForN t y A ∧ y ≠ ev
      ∧ (∀ v, termFV t v → v ≠ ev)
  | .exRight x A _ =>
    y ≠ x ∧ ¬ termFV t x ∧ ¬ formulaBVN A y ∧ isFreeForN t y A
  | _ => True

-- ===================================================================
-- G1nnfRule.SideConditions transport through rule substitution
-- ===================================================================

/-- Regression: `ruleSubstOk` rejects a universal-right substitution term
that contains the rule's eigenvariable. -/
theorem ruleSubstOk_allRight_rejects_eigenvariable_in_term {L : Language}
    (t : Term L) (x y ev : Nat) (A : FormulaN L)
    (hEv : ev ∈ termFV t) :
    ¬ ruleSubstOk t y (.allRight x A ev) := by
-- BEGIN PROOF
  intro hOk
  rcases hOk with ⟨_, _, _, _, _, hFresh⟩
  exact (hFresh ev hEv) rfl
-- END PROOF

/-- Rule substitution preserves side conditions when the original rule has
its side conditions and satisfies the existing per-rule substitution
admissibility bundle `ruleSubstOk`. In the eigenvariable cases, that bundle
ensures substitution cannot introduce the eigenvariable through `t`. -/
theorem substRule_sideConditions {L : Language}
    (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
    (t : Term L) (y : Nat)
    (hSC : G1nnfRule.SideConditions rule Gamma Delta)
    (hOk : ruleSubstOk t y rule) :
    G1nnfRule.SideConditions (substRule t y rule)
      (substFormulaFinset Gamma t y)
      (substFormulaFinset Delta t y) := by
-- BEGIN PROOF
  cases rule with
  | axiomPosAtomic _ _ _ _ =>
    trivial
  | axiomNegAtomic _ _ _ _ =>
    trivial
  | axiomCompLeft _ _ _ _ =>
    trivial
  | axiomCompRight _ _ _ _ =>
    trivial
  | cut _ _ _ =>
    trivial
  | conjLeft1 _ _ =>
    trivial
  | conjLeft2 _ _ =>
    trivial
  | conjRight _ _ =>
    trivial
  | disjLeft _ _ =>
    trivial
  | disjRight1 _ _ =>
    trivial
  | disjRight2 _ _ =>
    trivial
  | allLeft x A u =>
    simp only [G1nnfRule.SideConditions] at hSC
    simp only [ruleSubstOk] at hOk
    rcases hOk with ⟨hyx, _, hyBV, ht⟩
    have hyxB : (y != x) = true := bne_iff_ne.mpr hyx
    simp only [substRule, hyxB, ↓reduceIte, G1nnfRule.SideConditions]
    exact isFreeForN_termSubst_formulaSubstN A u t x y hSC ht hyBV
  | allRight x A ev =>
    simp only [G1nnfRule.SideConditions] at hSC
    simp only [ruleSubstOk] at hOk
    rcases hSC with ⟨hFree, hPrincipal, hGamma, hDelta⟩
    rcases hOk with ⟨hyx, _, hyBV, ht, hyEv, hFreshT⟩
    have hyxB : (y != x) = true := bne_iff_ne.mpr hyx
    have hEvT : ev ∉ termFV t := by
      intro h
      exact (hFreshT ev h) rfl
    have hFreeSubst :
        isFreeForN (.var ev) x (formulaSubstN A t y) := by
      have h := isFreeForN_termSubst_formulaSubstN
        A (.var ev) t x y hFree ht hyBV
      simpa [termSubst, Ne.symm hyEv] using h
    have hPrincipalSubst :
        ev ∉ formulaFVN (.all x (formulaSubstN A t y)) := by
      have h := formulaFVN_formulaSubstN_not_mem
        (.all x A) t y ev hPrincipal hEvT
      simpa [formulaSubstN, hyx] using h
    have hGammaSubst :
        ∀ F ∈ substFormulaFinset Gamma t y, ev ∉ formulaFVN F :=
      substFormulaFinset_fresh Gamma t y ev hGamma hEvT
    have hDeltaSubst :
        ∀ F ∈ substFormulaFinset Delta t y, ev ∉ formulaFVN F :=
      substFormulaFinset_fresh Delta t y ev hDelta hEvT
    simp only [substRule, hyxB, ↓reduceIte, G1nnfRule.SideConditions]
    exact
      ⟨hFreeSubst, hPrincipalSubst, hGammaSubst, hDeltaSubst⟩
  | exLeft x A ev =>
    simp only [G1nnfRule.SideConditions] at hSC
    simp only [ruleSubstOk] at hOk
    rcases hSC with ⟨hFree, hPrincipal, hGamma, hDelta⟩
    rcases hOk with ⟨hyx, _, hyBV, ht, hyEv, hFreshT⟩
    have hyxB : (y != x) = true := bne_iff_ne.mpr hyx
    have hEvT : ev ∉ termFV t := by
      intro h
      exact (hFreshT ev h) rfl
    have hFreeSubst :
        isFreeForN (.var ev) x (formulaSubstN A t y) := by
      have h := isFreeForN_termSubst_formulaSubstN
        A (.var ev) t x y hFree ht hyBV
      simpa [termSubst, Ne.symm hyEv] using h
    have hPrincipalSubst :
        ev ∉ formulaFVN (.ex x (formulaSubstN A t y)) := by
      have h := formulaFVN_formulaSubstN_not_mem
        (.ex x A) t y ev hPrincipal hEvT
      simpa [formulaSubstN, hyx] using h
    have hGammaSubst :
        ∀ F ∈ substFormulaFinset Gamma t y, ev ∉ formulaFVN F :=
      substFormulaFinset_fresh Gamma t y ev hGamma hEvT
    have hDeltaSubst :
        ∀ F ∈ substFormulaFinset Delta t y, ev ∉ formulaFVN F :=
      substFormulaFinset_fresh Delta t y ev hDelta hEvT
    simp only [substRule, hyxB, ↓reduceIte, G1nnfRule.SideConditions]
    exact
      ⟨hFreeSubst, hPrincipalSubst, hGammaSubst, hDeltaSubst⟩
  | exRight x A u =>
    simp only [G1nnfRule.SideConditions] at hSC
    simp only [ruleSubstOk] at hOk
    rcases hOk with ⟨hyx, _, hyBV, ht⟩
    have hyxB : (y != x) = true := bne_iff_ne.mpr hyx
    simp only [substRule, hyxB, ↓reduceIte, G1nnfRule.SideConditions]
    exact isFreeForN_termSubst_formulaSubstN A u t x y hSC ht hyBV
-- END PROOF

/-- Rule substitution preserves the complete G1nnf application contract:
the rule-specific side conditions and the NNF invariant on its conclusion. -/
theorem substRule_applicationConditions {L : Language}
    (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
    (t : Term L) (y : Nat)
    (hAC : G1nnfRule.ApplicationConditions rule Gamma Delta)
    (hOk : ruleSubstOk t y rule) :
    G1nnfRule.ApplicationConditions (substRule t y rule)
      (substFormulaFinset Gamma t y)
      (substFormulaFinset Delta t y) := by
-- BEGIN PROOF
  refine ⟨substRule_sideConditions rule Gamma Delta t y hAC.1 hOk, ?_⟩
  rw [substRule_conclusion_eq]
  exact
    ⟨substFormulaFinset_isNNF (rule.conclusion Gamma Delta).1 t y hAC.2.1,
     substFormulaFinset_isNNF (rule.conclusion Gamma Delta).2 t y hAC.2.2⟩
-- END PROOF

-- ===================================================================
-- substRule_premises_eq: premises commute with substFormulaFinset
-- ===================================================================

theorem substRule_premises_eq {L : Language}
    (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
    (t : Term L) (y : Nat)
    (hOk : ruleSubstOk t y rule) :
    (substRule t y rule).premises
        (substFormulaFinset Gamma t y) (substFormulaFinset Delta t y)
    = (rule.premises Gamma Delta).map (fun p =>
        (substFormulaFinset p.1 t y, substFormulaFinset p.2 t y)) := by
-- BEGIN PROOF
  cases rule with
  | axiomPosAtomic _ _ _ _ => rfl
  | axiomNegAtomic _ _ _ _ => rfl
  | axiomCompLeft _ _ _ _ => rfl
  | axiomCompRight _ _ _ _ => rfl
  | cut _ _ _ =>
    simp [substRule, G1nnfRule.premises, substFormulaFinset_insert]
  | conjLeft1 _ _ =>
    simp [substRule, G1nnfRule.premises, substFormulaFinset_insert]
  | conjLeft2 _ _ =>
    simp [substRule, G1nnfRule.premises, substFormulaFinset_insert]
  | conjRight _ _ =>
    simp [substRule, G1nnfRule.premises, substFormulaFinset_insert]
  | disjLeft _ _ =>
    simp [substRule, G1nnfRule.premises, substFormulaFinset_insert]
  | disjRight1 _ _ =>
    simp [substRule, G1nnfRule.premises, substFormulaFinset_insert]
  | disjRight2 _ _ =>
    simp [substRule, G1nnfRule.premises, substFormulaFinset_insert]
  | allLeft x A u =>
    simp only [ruleSubstOk] at hOk
    rcases hOk with ⟨hyx, hxt, hyA, hFree⟩
    have hyxB : (y != x) = true := bne_iff_ne.mpr hyx
    simp [substRule, hyxB, G1nnfRule.premises,
      substFormulaFinset_insert,
      formulaSubstN_composition A t u x y hyx hxt hyA hFree]
  | allRight x A ev =>
    simp only [ruleSubstOk] at hOk
    rcases hOk with ⟨hyx, hxt, hyA, hFree, hyEv, _⟩
    have hyxB : (y != x) = true := bne_iff_ne.mpr hyx
    have hComp :
        formulaSubstN (formulaSubstN A (.var ev) x) t y =
          formulaSubstN (formulaSubstN A t y) (.var ev) x := by
      simpa [termSubst, Ne.symm hyEv] using
        (formulaSubstN_composition A t (.var ev) x y
          hyx hxt hyA hFree)
    simp [substRule, hyxB, G1nnfRule.premises,
      substFormulaFinset_insert, hComp]
  | exLeft x A ev =>
    simp only [ruleSubstOk] at hOk
    rcases hOk with ⟨hyx, hxt, hyA, hFree, hyEv, _⟩
    have hyxB : (y != x) = true := bne_iff_ne.mpr hyx
    have hComp :
        formulaSubstN (formulaSubstN A (.var ev) x) t y =
          formulaSubstN (formulaSubstN A t y) (.var ev) x := by
      simpa [termSubst, Ne.symm hyEv] using
        (formulaSubstN_composition A t (.var ev) x y
          hyx hxt hyA hFree)
    simp [substRule, hyxB, G1nnfRule.premises,
      substFormulaFinset_insert, hComp]
  | exRight x A u =>
    simp only [ruleSubstOk] at hOk
    rcases hOk with ⟨hyx, hxt, hyA, hFree⟩
    have hyxB : (y != x) = true := bne_iff_ne.mpr hyx
    simp [substRule, hyxB, G1nnfRule.premises,
      substFormulaFinset_insert,
      formulaSubstN_composition A t u x y hyx hxt hyA hFree]

/-- Definition 6.4.5 (required helper): Pointwise version of
`substRule_premises_eq`: the `n`-th premise of `substRule t y rule` on
substituted contexts equals the substitution of the `n`-th original
premise. Used in the body of `G1nnfProofTree.substTerm` to index the
substituted subtree into the rule's `i`-th premise position. -/
theorem substRule_premises_nth_eq {L : Language}
    (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
    (t : Term L) (y : Nat) (n : Nat)
    (hn : n < (rule.premises Gamma Delta).length)
    (hOk : ruleSubstOk t y rule) :
    ((substRule t y rule).premises
        (substFormulaFinset Gamma t y) (substFormulaFinset Delta t y))[n]'
        (by rw [substRule_premises_length]; exact hn)
    = (substFormulaFinset ((rule.premises Gamma Delta)[n]).1 t y,
       substFormulaFinset ((rule.premises Gamma Delta)[n]).2 t y) := by
-- BEGIN PROOF
  have hEq := substRule_premises_eq rule Gamma Delta t y hOk
  have : ((substRule t y rule).premises
        (substFormulaFinset Gamma t y) (substFormulaFinset Delta t y))[n]'
        (by rw [substRule_premises_length]; exact hn)
    = ((rule.premises Gamma Delta).map (fun p =>
          (substFormulaFinset p.1 t y, substFormulaFinset p.2 t y)))[n]'
            (by rw [List.length_map]; exact hn) := by
    simp [hEq]
  rw [this, List.getElem_map]

-- ===================================================================
-- Definition 6.4.5 (companion): G1nnfProofTree.treeSubstOk
-- ===================================================================

/-- Internal substitution helper: the recursive closure of `ruleSubstOk`.
This remains the admissibility witness consumed by the direct `substRule`
implementation. It is not Gallier's public substitution contract and will be
bridged from the exact proof-wide predicates by the hygienization layer. -/
def G1nnfProofTree.treeSubstOk {L : Language} {hL : L.withoutEquality} :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G1nnfProofTree hL Γ Δ → Term L → Nat → Prop
  | _, _, .axiom_ rule _ _ _ _, t, y => ruleSubstOk t y rule
  | _, _, .onePremise rule _ _ _ _ sub, t, y =>
    ruleSubstOk t y rule ∧ sub.treeSubstOk t y
  | _, _, .twoPremise rule _ _ _ _ sub1 sub2, t, y =>
    ruleSubstOk t y rule ∧ sub1.treeSubstOk t y ∧ sub2.treeSubstOk t y

-- ===================================================================
-- Definition 6.4.5: G1nnfProofTree.substTerm (indexed by Finset)
-- ===================================================================

/-- Definition 6.4.5: `T[t/y]` substitutes term `t` for `y` in the
proof tree T, producing a tree indexed by the substituted Finsets.
With Finset indices the composition identity is handled by
`substFormulaFinset_insert` (= `image_insert`), which is the
extensional analogue of the list-level `substFormulaList_append`+
`substFormulaList_singleton`. -/
noncomputable def G1nnfProofTree.substTerm {L : Language} {hL : L.withoutEquality} :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    (T : G1nnfProofTree hL Γ Δ) → (t : Term L) → (y : Nat) →
    T.treeSubstOk t y →
    G1nnfProofTree hL (substFormulaFinset Γ t y)
                   (substFormulaFinset Δ t y)
  | _, _, .axiom_ rule Γ Δ hAxiom hAC, t, y, hOk =>
      have hEq1 : ((substRule t y rule).conclusion
            (substFormulaFinset Γ t y) (substFormulaFinset Δ t y)).1
        = substFormulaFinset (rule.conclusion Γ Δ).1 t y := by
        rw [substRule_conclusion_eq]
      have hEq2 : ((substRule t y rule).conclusion
            (substFormulaFinset Γ t y) (substFormulaFinset Δ t y)).2
        = substFormulaFinset (rule.conclusion Γ Δ).2 t y := by
        rw [substRule_conclusion_eq]
      have hPremLen : ((substRule t y rule).premises
          (substFormulaFinset Γ t y) (substFormulaFinset Δ t y)).length = 0 := by
        rw [substRule_premises_length]; exact hAxiom
      have hAC' : (substRule t y rule).ApplicationConditions
          (substFormulaFinset Γ t y) (substFormulaFinset Δ t y) :=
        substRule_applicationConditions rule Γ Δ t y hAC hOk
      hEq1 ▸ hEq2 ▸ (.axiom_ (substRule t y rule)
            (substFormulaFinset Γ t y)
            (substFormulaFinset Δ t y)
            hPremLen hAC')
  | _, _, .onePremise rule Γ Δ hPrem hAC sub, t, y, hOk =>
      let hOkR := hOk.1
      let hOkS := hOk.2
      let subNew := sub.substTerm t y hOkS
      have hEq1 : ((substRule t y rule).conclusion
            (substFormulaFinset Γ t y) (substFormulaFinset Δ t y)).1
        = substFormulaFinset (rule.conclusion Γ Δ).1 t y := by
        rw [substRule_conclusion_eq]
      have hEq2 : ((substRule t y rule).conclusion
            (substFormulaFinset Γ t y) (substFormulaFinset Δ t y)).2
        = substFormulaFinset (rule.conclusion Γ Δ).2 t y := by
        rw [substRule_conclusion_eq]
      have hPremLen : ((substRule t y rule).premises
          (substFormulaFinset Γ t y) (substFormulaFinset Δ t y)).length = 1 := by
        rw [substRule_premises_length]; exact hPrem
      have hAC' : (substRule t y rule).ApplicationConditions
          (substFormulaFinset Γ t y) (substFormulaFinset Δ t y) :=
        substRule_applicationConditions rule Γ Δ t y hAC hOkR
      have hPrem0 : 0 < (rule.premises Γ Δ).length := by rw [hPrem]; omega
      have hPremEq := substRule_premises_nth_eq rule Γ Δ t y 0 hPrem0 hOkR
      have h1 : (((substRule t y rule).premises
            (substFormulaFinset Γ t y) (substFormulaFinset Δ t y))[0]'(by omega)).1
        = substFormulaFinset ((rule.premises Γ Δ)[0]'hPrem0).1 t y := by
        rw [hPremEq]
      have h2 : (((substRule t y rule).premises
            (substFormulaFinset Γ t y) (substFormulaFinset Δ t y))[0]'(by omega)).2
        = substFormulaFinset ((rule.premises Γ Δ)[0]'hPrem0).2 t y := by
        rw [hPremEq]
      have subCast : G1nnfProofTree hL
          (((substRule t y rule).premises
            (substFormulaFinset Γ t y) (substFormulaFinset Δ t y))[0]'(by omega)).1
          (((substRule t y rule).premises
            (substFormulaFinset Γ t y) (substFormulaFinset Δ t y))[0]'(by omega)).2 :=
        h1 ▸ h2 ▸ subNew
      hEq1 ▸ hEq2 ▸ (.onePremise (substRule t y rule)
            (substFormulaFinset Γ t y)
            (substFormulaFinset Δ t y)
            hPremLen hAC' subCast)
  | _, _, .twoPremise rule Γ Δ hPrem hAC sub1 sub2, t, y, hOk =>
      let hOkR := hOk.1
      let hOkS1 := hOk.2.1
      let hOkS2 := hOk.2.2
      let subNew1 := sub1.substTerm t y hOkS1
      let subNew2 := sub2.substTerm t y hOkS2
      have hEq1 : ((substRule t y rule).conclusion
            (substFormulaFinset Γ t y) (substFormulaFinset Δ t y)).1
        = substFormulaFinset (rule.conclusion Γ Δ).1 t y := by
        rw [substRule_conclusion_eq]
      have hEq2 : ((substRule t y rule).conclusion
            (substFormulaFinset Γ t y) (substFormulaFinset Δ t y)).2
        = substFormulaFinset (rule.conclusion Γ Δ).2 t y := by
        rw [substRule_conclusion_eq]
      have hPremLen : ((substRule t y rule).premises
          (substFormulaFinset Γ t y) (substFormulaFinset Δ t y)).length = 2 := by
        rw [substRule_premises_length]; exact hPrem
      have hAC' : (substRule t y rule).ApplicationConditions
          (substFormulaFinset Γ t y) (substFormulaFinset Δ t y) :=
        substRule_applicationConditions rule Γ Δ t y hAC hOkR
      have hPrem0 : 0 < (rule.premises Γ Δ).length := by rw [hPrem]; omega
      have hPrem1 : 1 < (rule.premises Γ Δ).length := by rw [hPrem]; omega
      have hPremEq0 := substRule_premises_nth_eq rule Γ Δ t y 0 hPrem0 hOkR
      have hPremEq1 := substRule_premises_nth_eq rule Γ Δ t y 1 hPrem1 hOkR
      have h1_0 : (((substRule t y rule).premises
            (substFormulaFinset Γ t y) (substFormulaFinset Δ t y))[0]'(by omega)).1
        = substFormulaFinset ((rule.premises Γ Δ)[0]'hPrem0).1 t y := by
        rw [hPremEq0]
      have h2_0 : (((substRule t y rule).premises
            (substFormulaFinset Γ t y) (substFormulaFinset Δ t y))[0]'(by omega)).2
        = substFormulaFinset ((rule.premises Γ Δ)[0]'hPrem0).2 t y := by
        rw [hPremEq0]
      have h1_1 : (((substRule t y rule).premises
            (substFormulaFinset Γ t y) (substFormulaFinset Δ t y))[1]'(by omega)).1
        = substFormulaFinset ((rule.premises Γ Δ)[1]'hPrem1).1 t y := by
        rw [hPremEq1]
      have h2_1 : (((substRule t y rule).premises
            (substFormulaFinset Γ t y) (substFormulaFinset Δ t y))[1]'(by omega)).2
        = substFormulaFinset ((rule.premises Γ Δ)[1]'hPrem1).2 t y := by
        rw [hPremEq1]
      have sub1Cast : G1nnfProofTree hL
          (((substRule t y rule).premises
            (substFormulaFinset Γ t y) (substFormulaFinset Δ t y))[0]'(by omega)).1
          (((substRule t y rule).premises
            (substFormulaFinset Γ t y) (substFormulaFinset Δ t y))[0]'(by omega)).2 :=
        h1_0 ▸ h2_0 ▸ subNew1
      have sub2Cast : G1nnfProofTree hL
          (((substRule t y rule).premises
            (substFormulaFinset Γ t y) (substFormulaFinset Δ t y))[1]'(by omega)).1
          (((substRule t y rule).premises
            (substFormulaFinset Γ t y) (substFormulaFinset Δ t y))[1]'(by omega)).2 :=
        h1_1 ▸ h2_1 ▸ subNew2
      hEq1 ▸ hEq2 ▸ (.twoPremise (substRule t y rule)
            (substFormulaFinset Γ t y)
            (substFormulaFinset Δ t y)
            hPremLen hAC' sub1Cast sub2Cast)

-- ===================================================================
-- Definition 6.4.5 (companion): G1nnfDeductionTree.treeSubstOk
-- ===================================================================

/-- Internal deduction-tree counterpart of `G1nnfProofTree.treeSubstOk`.
At each rule node it records the direct `ruleSubstOk` obligations required by
the current structural substitution implementation; leaves have no such
obligation. This implementation predicate is not the textbook contract. -/
def G1nnfDeductionTree.treeSubstOk {L : Language} {hL : L.withoutEquality} :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G1nnfDeductionTree hL Γ Δ → Term L → Nat → Prop
  | _, _, .leaf _ _ _, _, _ => True
  | _, _, .onePremise rule _ _ _ _ sub, t, y =>
      ruleSubstOk t y rule ∧ sub.treeSubstOk t y
  | _, _, .twoPremise rule _ _ _ _ sub1 sub2, t, y =>
      ruleSubstOk t y rule ∧ sub1.treeSubstOk t y ∧ sub2.treeSubstOk t y

/-- Internal variable substitution retaining the direct `treeSubstOk`
contract and unchanged eigenvariable labels. -/
noncomputable def G1nnfDeductionTree.substituteVarOfTreeSubstOk {L : Language} {hL : L.withoutEquality} :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    (T : G1nnfDeductionTree hL Γ Δ) → (y z : Nat) →
    T.treeSubstOk (Term.var z) y →
    G1nnfDeductionTree hL (substFormulaFinset Γ (Term.var z) y)
                       (substFormulaFinset Δ (Term.var z) y)
  | _, _, .leaf Γ Δ hNNF, y, z, _ =>
      .leaf (substFormulaFinset Γ (Term.var z) y)
            (substFormulaFinset Δ (Term.var z) y)
            ⟨substFormulaFinset_isNNF Γ (Term.var z) y hNNF.1,
             substFormulaFinset_isNNF Δ (Term.var z) y hNNF.2⟩
  | _, _, .onePremise rule Γ Δ hPrem hAC sub, y, z, hOk =>
      let hOkR := hOk.1
      let hOkS := hOk.2
      let subNew := sub.substituteVarOfTreeSubstOk y z hOkS
      have hEq1 : ((substRule (Term.var z) y rule).conclusion
            (substFormulaFinset Γ (Term.var z) y)
            (substFormulaFinset Δ (Term.var z) y)).1
        = substFormulaFinset (rule.conclusion Γ Δ).1 (Term.var z) y := by
        rw [substRule_conclusion_eq]
      have hEq2 : ((substRule (Term.var z) y rule).conclusion
            (substFormulaFinset Γ (Term.var z) y)
            (substFormulaFinset Δ (Term.var z) y)).2
        = substFormulaFinset (rule.conclusion Γ Δ).2 (Term.var z) y := by
        rw [substRule_conclusion_eq]
      have hPremLen : ((substRule (Term.var z) y rule).premises
          (substFormulaFinset Γ (Term.var z) y)
          (substFormulaFinset Δ (Term.var z) y)).length = 1 := by
        rw [substRule_premises_length]; exact hPrem
      have hAC' : (substRule (Term.var z) y rule).ApplicationConditions
          (substFormulaFinset Γ (Term.var z) y)
          (substFormulaFinset Δ (Term.var z) y) :=
        substRule_applicationConditions rule Γ Δ (Term.var z) y hAC hOkR
      have hPrem0 : 0 < (rule.premises Γ Δ).length := by rw [hPrem]; omega
      have hPremEq := substRule_premises_nth_eq rule Γ Δ (Term.var z) y 0 hPrem0 hOkR
      have h1 : (((substRule (Term.var z) y rule).premises
            (substFormulaFinset Γ (Term.var z) y)
            (substFormulaFinset Δ (Term.var z) y))[0]'(by omega)).1
        = substFormulaFinset ((rule.premises Γ Δ)[0]'hPrem0).1 (Term.var z) y := by
        rw [hPremEq]
      have h2 : (((substRule (Term.var z) y rule).premises
            (substFormulaFinset Γ (Term.var z) y)
            (substFormulaFinset Δ (Term.var z) y))[0]'(by omega)).2
        = substFormulaFinset ((rule.premises Γ Δ)[0]'hPrem0).2 (Term.var z) y := by
        rw [hPremEq]
      have subCast : G1nnfDeductionTree hL
          (((substRule (Term.var z) y rule).premises
            (substFormulaFinset Γ (Term.var z) y)
            (substFormulaFinset Δ (Term.var z) y))[0]'(by omega)).1
          (((substRule (Term.var z) y rule).premises
            (substFormulaFinset Γ (Term.var z) y)
            (substFormulaFinset Δ (Term.var z) y))[0]'(by omega)).2 :=
        h1 ▸ h2 ▸ subNew
      hEq1 ▸ hEq2 ▸ (.onePremise (substRule (Term.var z) y rule)
            (substFormulaFinset Γ (Term.var z) y)
            (substFormulaFinset Δ (Term.var z) y)
            hPremLen hAC' subCast)
  | _, _, .twoPremise rule Γ Δ hPrem hAC sub1 sub2, y, z, hOk =>
      let hOkR := hOk.1
      let hOkS1 := hOk.2.1
      let hOkS2 := hOk.2.2
      let subNew1 := sub1.substituteVarOfTreeSubstOk y z hOkS1
      let subNew2 := sub2.substituteVarOfTreeSubstOk y z hOkS2
      have hEq1 : ((substRule (Term.var z) y rule).conclusion
            (substFormulaFinset Γ (Term.var z) y)
            (substFormulaFinset Δ (Term.var z) y)).1
        = substFormulaFinset (rule.conclusion Γ Δ).1 (Term.var z) y := by
        rw [substRule_conclusion_eq]
      have hEq2 : ((substRule (Term.var z) y rule).conclusion
            (substFormulaFinset Γ (Term.var z) y)
            (substFormulaFinset Δ (Term.var z) y)).2
        = substFormulaFinset (rule.conclusion Γ Δ).2 (Term.var z) y := by
        rw [substRule_conclusion_eq]
      have hPremLen : ((substRule (Term.var z) y rule).premises
          (substFormulaFinset Γ (Term.var z) y)
          (substFormulaFinset Δ (Term.var z) y)).length = 2 := by
        rw [substRule_premises_length]; exact hPrem
      have hAC' : (substRule (Term.var z) y rule).ApplicationConditions
          (substFormulaFinset Γ (Term.var z) y)
          (substFormulaFinset Δ (Term.var z) y) :=
        substRule_applicationConditions rule Γ Δ (Term.var z) y hAC hOkR
      have hPrem0 : 0 < (rule.premises Γ Δ).length := by rw [hPrem]; omega
      have hPrem1 : 1 < (rule.premises Γ Δ).length := by rw [hPrem]; omega
      have hPremEq0 := substRule_premises_nth_eq rule Γ Δ (Term.var z) y 0 hPrem0 hOkR
      have hPremEq1 := substRule_premises_nth_eq rule Γ Δ (Term.var z) y 1 hPrem1 hOkR
      have h1_0 : (((substRule (Term.var z) y rule).premises
            (substFormulaFinset Γ (Term.var z) y)
            (substFormulaFinset Δ (Term.var z) y))[0]'(by omega)).1
        = substFormulaFinset ((rule.premises Γ Δ)[0]'hPrem0).1 (Term.var z) y := by
        rw [hPremEq0]
      have h2_0 : (((substRule (Term.var z) y rule).premises
            (substFormulaFinset Γ (Term.var z) y)
            (substFormulaFinset Δ (Term.var z) y))[0]'(by omega)).2
        = substFormulaFinset ((rule.premises Γ Δ)[0]'hPrem0).2 (Term.var z) y := by
        rw [hPremEq0]
      have h1_1 : (((substRule (Term.var z) y rule).premises
            (substFormulaFinset Γ (Term.var z) y)
            (substFormulaFinset Δ (Term.var z) y))[1]'(by omega)).1
        = substFormulaFinset ((rule.premises Γ Δ)[1]'hPrem1).1 (Term.var z) y := by
        rw [hPremEq1]
      have h2_1 : (((substRule (Term.var z) y rule).premises
            (substFormulaFinset Γ (Term.var z) y)
            (substFormulaFinset Δ (Term.var z) y))[1]'(by omega)).2
        = substFormulaFinset ((rule.premises Γ Δ)[1]'hPrem1).2 (Term.var z) y := by
        rw [hPremEq1]
      have sub1Cast : G1nnfDeductionTree hL
          (((substRule (Term.var z) y rule).premises
            (substFormulaFinset Γ (Term.var z) y)
            (substFormulaFinset Δ (Term.var z) y))[0]'(by omega)).1
          (((substRule (Term.var z) y rule).premises
            (substFormulaFinset Γ (Term.var z) y)
            (substFormulaFinset Δ (Term.var z) y))[0]'(by omega)).2 :=
        h1_0 ▸ h2_0 ▸ subNew1
      have sub2Cast : G1nnfDeductionTree hL
          (((substRule (Term.var z) y rule).premises
            (substFormulaFinset Γ (Term.var z) y)
            (substFormulaFinset Δ (Term.var z) y))[1]'(by omega)).1
          (((substRule (Term.var z) y rule).premises
            (substFormulaFinset Γ (Term.var z) y)
            (substFormulaFinset Δ (Term.var z) y))[1]'(by omega)).2 :=
        h1_1 ▸ h2_1 ▸ subNew2
      hEq1 ▸ hEq2 ▸ (.twoPremise (substRule (Term.var z) y rule)
            (substFormulaFinset Γ (Term.var z) y)
            (substFormulaFinset Δ (Term.var z) y)
            hPremLen hAC' sub1Cast sub2Cast)

theorem G1nnfProofTree.depth_cast {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (T : G1nnfProofTree hL Γ Δ) :
    (hΓ ▸ hΔ ▸ T).depth = T.depth := by
  subst Γ'
  subst Δ'
  rfl

theorem G1nnfProofTree.cutRank_cast {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (T : G1nnfProofTree hL Γ Δ) :
    (hΓ ▸ hΔ ▸ T).cutRank = T.cutRank := by
  subst Γ'
  subst Δ'
  rfl

theorem G1nnfProofTree.eigenvariables_cast {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (T : G1nnfProofTree hL Γ Δ)
    (v : Nat) :
    (hΓ ▸ hΔ ▸ T).eigenvariables v = T.eigenvariables v := by
  subst Γ'
  subst Δ'
  rfl

noncomputable def G1nnfProofTree.castTree {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (T : G1nnfProofTree hL Γ Δ) :
    G1nnfProofTree hL Γ' Δ' :=
  hΓ ▸ hΔ ▸ T

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

theorem allFormulae_transport {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (T : G1nnfProofTree hL Γ Δ) :
    (hΓ ▸ hΔ ▸ T).allFormulae = T.allFormulae := by
  subst Γ'
  subst Δ'
  rfl

theorem allFormulae_cast {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (T : G1nnfProofTree hL Γ Δ) :
    (T.castTree hΓ hΔ).allFormulae = T.allFormulae := by
  unfold G1nnfProofTree.castTree
  exact allFormulae_transport hΓ hΔ T

theorem depth_castTree {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ)
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') :
    (T.castTree hΓ hΔ).depth = T.depth := by
  unfold G1nnfProofTree.castTree
  exact G1nnfProofTree.depth_cast hΓ hΔ T

theorem cutRank_castTree {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ)
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') :
    (T.castTree hΓ hΔ).cutRank = T.cutRank := by
  unfold G1nnfProofTree.castTree
  exact G1nnfProofTree.cutRank_cast hΓ hΔ T

theorem eigenvariables_castTree {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ)
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (w : Nat) :
    (T.castTree hΓ hΔ).eigenvariables w =
      T.eigenvariables w := by
  unfold G1nnfProofTree.castTree
  exact G1nnfProofTree.eigenvariables_cast hΓ hΔ T w

private theorem alphaRenameBoundTree_depth {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (v z : Nat)
    (hvz : v ≠ z) (hz : z ∉ T.variableSupport) :
    (T.alphaRenameBoundTree v z hvz hz).depth = T.depth := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
      simp only [alphaRenameBoundTree]
      rw [G1nnfProofTree.depth_cast]
      rfl
  | onePremise rule Γ Δ hPrem hAC sub ih =>
      simp only [alphaRenameBoundTree]
      rw [G1nnfProofTree.depth_cast]
      simp only [G1nnfProofTree.depth]
      rw [G1nnfProofTree.depth_cast, ih]
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
      simp only [alphaRenameBoundTree]
      rw [G1nnfProofTree.depth_cast]
      simp only [G1nnfProofTree.depth]
      rw [G1nnfProofTree.depth_cast, G1nnfProofTree.depth_cast,
        ih1, ih2]

private theorem alphaRenameBoundTree_cutRank {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (v z : Nat)
    (hvz : v ≠ z) (hz : z ∉ T.variableSupport) :
    (T.alphaRenameBoundTree v z hvz hz).cutRank = T.cutRank := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
      simp only [alphaRenameBoundTree]
      rw [G1nnfProofTree.cutRank_cast]
      rfl
  | onePremise rule Γ Δ hPrem hAC sub ih =>
      simp only [alphaRenameBoundTree]
      rw [G1nnfProofTree.cutRank_cast]
      simp only [G1nnfProofTree.cutRank]
      rw [G1nnfProofTree.cutRank_cast, ih]
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
      simp only [alphaRenameBoundTree]
      rw [G1nnfProofTree.cutRank_cast]
      simp only [G1nnfProofTree.cutRank]
      rw [alphaRenameBoundRule_cutFormula,
        G1nnfProofTree.cutRank_cast,
        G1nnfProofTree.cutRank_cast, ih1, ih2]
      cases hCut : rule.cutFormula with
      | none => rfl
      | some A =>
          simp only [Option.map, alphaRenameBound_degree]

private theorem allFormulae_alphaRenameBoundTree {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (v z : Nat)
    (hvz : v ≠ z) (hz : z ∉ T.variableSupport) :
    (T.alphaRenameBoundTree v z hvz hz).allFormulae =
      alphaRenameFormulaFinset T.allFormulae v z := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
      simp only [alphaRenameBoundTree]
      rw [allFormulae_transport]
      simp only [G1nnfProofTree.allFormulae]
      rw [alphaRenameBoundRule_conclusion_eq,
        alphaRenameFormulaFinset_union]
  | onePremise rule Γ Δ hPrem hAC sub ih =>
      simp only [alphaRenameBoundTree]
      rw [allFormulae_transport]
      simp only [G1nnfProofTree.allFormulae]
      rw [allFormulae_transport, ih,
        alphaRenameBoundRule_conclusion_eq,
        alphaRenameFormulaFinset_union,
        alphaRenameFormulaFinset_union]
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
      simp only [alphaRenameBoundTree]
      rw [allFormulae_transport]
      simp only [G1nnfProofTree.allFormulae]
      rw [allFormulae_transport, allFormulae_transport, ih1, ih2,
        alphaRenameBoundRule_conclusion_eq,
        alphaRenameFormulaFinset_union,
        alphaRenameFormulaFinset_union,
        alphaRenameFormulaFinset_union]

private theorem alphaRenameBoundTree_notBound_target {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (v z : Nat)
    (hvz : v ≠ z) (hz : z ∉ T.variableSupport) :
    (T.alphaRenameBoundTree v z hvz hz).notBoundIn v := by
  intro A hA
  rw [allFormulae_alphaRenameBoundTree] at hA
  obtain ⟨B, _, rfl⟩ := LCS.Finset.mem_image.mp hA
  exact alphaRenameBound_removes_binder B v z hvz

private theorem alphaRenameBoundTree_preserves_notBound {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (v z w : Nat)
    (hvz : v ≠ z) (hz : z ∉ T.variableSupport)
    (hwz : w ≠ z) (hw : T.notBoundIn w) :
    (T.alphaRenameBoundTree v z hvz hz).notBoundIn w := by
  intro A hA
  rw [allFormulae_alphaRenameBoundTree] at hA
  obtain ⟨B, hB, rfl⟩ := LCS.Finset.mem_image.mp hA
  exact alphaRenameBound_preserves_binder_absence
    B v z w hwz (hw B hB)

theorem notBoundIn_cast {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ)
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (w : Nat) :
    (T.castTree hΓ hΔ).notBoundIn w ↔ T.notBoundIn w := by
  subst Γ'
  subst Δ'
  rfl

/-- Root-exact wrapper for one bound-label hygiene step.  Its root remains
definitionally indexed by the original sequent because the public
non-binding hypothesis makes the alpha map the identity there. -/
noncomputable def alphaRenameBoundAtRoot {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (v z : Nat)
    (hvz : v ≠ z) (hz : z ∉ T.variableSupport)
    (hRoot :
      (∀ A ∈ Γ, FormulaN.notBoundIn v A) ∧
      (∀ A ∈ Δ, FormulaN.notBoundIn v A)) :
    G1nnfProofTree hL Γ Δ :=
  (T.alphaRenameBoundTree v z hvz hz).castTree
    (alphaRenameFormulaFinset_eq_self_of_not_bound
      Γ v z hRoot.1)
    (alphaRenameFormulaFinset_eq_self_of_not_bound
      Δ v z hRoot.2)

theorem alphaRenameBoundAtRoot_depth {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (v z : Nat)
    (hvz : v ≠ z) (hz : z ∉ T.variableSupport)
    (hRoot :
      (∀ A ∈ Γ, FormulaN.notBoundIn v A) ∧
      (∀ A ∈ Δ, FormulaN.notBoundIn v A)) :
    (T.alphaRenameBoundAtRoot v z hvz hz hRoot).depth =
      T.depth := by
  rw [alphaRenameBoundAtRoot, depth_castTree,
    T.alphaRenameBoundTree_depth v z hvz hz]

theorem alphaRenameBoundAtRoot_cutRank {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (v z : Nat)
    (hvz : v ≠ z) (hz : z ∉ T.variableSupport)
    (hRoot :
      (∀ A ∈ Γ, FormulaN.notBoundIn v A) ∧
      (∀ A ∈ Δ, FormulaN.notBoundIn v A)) :
    (T.alphaRenameBoundAtRoot v z hvz hz hRoot).cutRank =
      T.cutRank := by
  rw [alphaRenameBoundAtRoot, cutRank_castTree,
    T.alphaRenameBoundTree_cutRank v z hvz hz]

theorem alphaRenameBoundAtRoot_notBound_target {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (v z : Nat)
    (hvz : v ≠ z) (hz : z ∉ T.variableSupport)
    (hRoot :
      (∀ A ∈ Γ, FormulaN.notBoundIn v A) ∧
      (∀ A ∈ Δ, FormulaN.notBoundIn v A)) :
    (T.alphaRenameBoundAtRoot v z hvz hz hRoot).notBoundIn v := by
  apply
    (notBoundIn_cast
      (T.alphaRenameBoundTree v z hvz hz)
      (alphaRenameFormulaFinset_eq_self_of_not_bound
        Γ v z hRoot.1)
      (alphaRenameFormulaFinset_eq_self_of_not_bound
        Δ v z hRoot.2) v).2
  exact T.alphaRenameBoundTree_notBound_target v z hvz hz

theorem alphaRenameBoundAtRoot_preserves_notBound {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (v z w : Nat)
    (hvz : v ≠ z) (hz : z ∉ T.variableSupport)
    (hRoot :
      (∀ A ∈ Γ, FormulaN.notBoundIn v A) ∧
      (∀ A ∈ Δ, FormulaN.notBoundIn v A))
    (hwz : w ≠ z) (hw : T.notBoundIn w) :
    (T.alphaRenameBoundAtRoot v z hvz hz hRoot).notBoundIn w := by
  apply
    (notBoundIn_cast
      (T.alphaRenameBoundTree v z hvz hz)
      (alphaRenameFormulaFinset_eq_self_of_not_bound
        Γ v z hRoot.1)
      (alphaRenameFormulaFinset_eq_self_of_not_bound
        Δ v z hRoot.2) w).2
  exact
    T.alphaRenameBoundTree_preserves_notBound
      v z w hvz hz hwz hw

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

private theorem finiteSet_of_finset {α : Type}
    (s : LCS.Finset α) : Set.Finite (fun a => a ∈ s) :=
  ⟨s.toList, fun a => (LCS.Finset.mem_toList s a).symm⟩

private theorem finiteSet_of_finset_cover {α : Type}
    {S : Set α} (s : LCS.Finset α)
    (hS : ∀ a, S a → a ∈ s) : Set.Finite S :=
  Set.Finite.subset (finiteSet_of_finset s) hS

private noncomputable def finsetOfFiniteSet {α : Type}
    [DecidableEq α] (S : Set α) (hS : Set.Finite S) : LCS.Finset α :=
  LCS.Finset.ofList (Classical.choose hS)

private theorem mem_finsetOfFiniteSet {α : Type}
    [DecidableEq α] (S : Set α) (hS : Set.Finite S) (a : α) :
    a ∈ finsetOfFiniteSet S hS ↔ S a := by
  rw [finsetOfFiniteSet, LCS.Finset.mem_ofList]
  exact (Classical.choose_spec hS a).symm

private theorem mem_insert_represents_left {α : Type}
    [DecidableEq α] {S : Set α} {s : LCS.Finset α}
    (a : α) (hs : ∀ x, x ∈ s ↔ S x) (x : α) :
    x ∈ LCS.Finset.insert a s ↔ x = a ∨ S x := by
  rw [LCS.Finset.mem_insert, hs x]

private theorem mem_insert_represents_right {α : Type}
    [DecidableEq α] {S : Set α} {s : LCS.Finset α}
    (a : α) (hs : ∀ x, x ∈ s ↔ S x) (x : α) :
    x ∈ LCS.Finset.insert a s ↔ S x ∨ x = a := by
  rw [LCS.Finset.mem_insert, hs x, or_comm]

theorem finset_insert_eq_self_of_mem {α : Type}
    [DecidableEq α] {a : α} {s : LCS.Finset α}
    (ha : a ∈ s) : LCS.Finset.insert a s = s := by
  apply LCS.Finset.ext
  intro x
  rw [LCS.Finset.mem_insert]
  constructor
  · rintro (rfl | hx)
    · exact ha
    · exact hx
  · exact Or.inr

/-- A finite set-level G1nnf derivation gives an indexed proof tree for
any Finset representatives of its endpoint sets.  Finiteness is recovered
from the supplied representatives at each recursive step.  No proof-tree
weakening is used: each rule is rebuilt with an exact representative of
its ambient set, which is essential for preserving eigenvariable side
conditions. -/
theorem g1nnfProofTree_of_setDerivable
    {L : Language} {hL : L.withoutEquality}
    {S T : Set (FormulaN L)}
    (hDer : G1nnfSetDerivable S T)
    {Γ Δ : LCS.Finset (FormulaN L)}
    (hΓ : ∀ F, F ∈ Γ ↔ S F)
    (hΔ : ∀ F, F ∈ Δ ↔ T F)
    (hNNF : G1nnfFinsetSequent.IsNNF (Γ, Δ)) :
    Nonempty (G1nnfProofTree hL Γ Δ) := by
  induction hDer generalizing Γ Δ with
  | axiomPos A hAtom S T hS hT =>
      have hAΓ : A ∈ Γ := (hΓ A).2 hS
      have hAΔ : A ∈ Δ := (hΔ A).2 hT
      have hANNF : A.isNNF := hNNF.1 A hAΓ
      have hΓeq : LCS.Finset.insert A Γ = Γ :=
        finset_insert_eq_self_of_mem hAΓ
      have hΔeq : LCS.Finset.insert A Δ = Δ :=
        finset_insert_eq_self_of_mem hAΔ
      let tree :=
        G1nnfProofTree.axiom_ (hL := hL)
          (.axiomPosAtomic A hAtom Γ Δ) Γ Δ rfl
          ⟨trivial,
            G1nnfFinsetSequent.IsNNF.insert_right hANNF
              (G1nnfFinsetSequent.IsNNF.insert_left hANNF hNNF)⟩
      exact ⟨tree.castTree hΓeq hΔeq⟩
  | axiomNeg A hAtom S T hS hT =>
      have hAΓ : FormulaN.neg A ∈ Γ := (hΓ (FormulaN.neg A)).2 hS
      have hAΔ : FormulaN.neg A ∈ Δ := (hΔ (FormulaN.neg A)).2 hT
      have hANNF : (FormulaN.neg A).isNNF := hNNF.1 _ hAΓ
      have hΓeq : LCS.Finset.insert (FormulaN.neg A) Γ = Γ :=
        finset_insert_eq_self_of_mem hAΓ
      have hΔeq : LCS.Finset.insert (FormulaN.neg A) Δ = Δ :=
        finset_insert_eq_self_of_mem hAΔ
      let tree :=
        G1nnfProofTree.axiom_ (hL := hL)
          (.axiomNegAtomic A hAtom Γ Δ) Γ Δ rfl
          ⟨trivial,
            G1nnfFinsetSequent.IsNNF.insert_right hANNF
              (G1nnfFinsetSequent.IsNNF.insert_left hANNF hNNF)⟩
      exact ⟨tree.castTree hΓeq hΔeq⟩
  | axiomCompL A hAtom S T hA hNA =>
      have hAΓ : A ∈ Γ := (hΓ A).2 hA
      have hNAΓ : FormulaN.neg A ∈ Γ := (hΓ (FormulaN.neg A)).2 hNA
      have hANNF : A.isNNF := hNNF.1 A hAΓ
      have hNANNF : (FormulaN.neg A).isNNF := hNNF.1 _ hNAΓ
      have hNAeq : LCS.Finset.insert (FormulaN.neg A) Γ = Γ :=
        finset_insert_eq_self_of_mem hNAΓ
      have hΓeq :
          LCS.Finset.insert A (LCS.Finset.insert (FormulaN.neg A) Γ) = Γ := by
        rw [hNAeq]
        exact finset_insert_eq_self_of_mem hAΓ
      let tree :=
        G1nnfProofTree.axiom_ (hL := hL)
          (.axiomCompLeft A hAtom Γ Δ) Γ Δ rfl
          ⟨trivial,
            G1nnfFinsetSequent.IsNNF.insert_left hANNF
              (G1nnfFinsetSequent.IsNNF.insert_left hNANNF hNNF)⟩
      exact ⟨tree.castTree hΓeq rfl⟩
  | axiomCompR A hAtom S T hA hNA =>
      have hAΔ : A ∈ Δ := (hΔ A).2 hA
      have hNAΔ : FormulaN.neg A ∈ Δ := (hΔ (FormulaN.neg A)).2 hNA
      have hANNF : A.isNNF := hNNF.2 A hAΔ
      have hNANNF : (FormulaN.neg A).isNNF := hNNF.2 _ hNAΔ
      have hNAeq : LCS.Finset.insert (FormulaN.neg A) Δ = Δ :=
        finset_insert_eq_self_of_mem hNAΔ
      have hΔeq :
          LCS.Finset.insert A (LCS.Finset.insert (FormulaN.neg A) Δ) = Δ := by
        rw [hNAeq]
        exact finset_insert_eq_self_of_mem hAΔ
      let tree :=
        G1nnfProofTree.axiom_ (hL := hL)
          (.axiomCompRight A hAtom Γ Δ) Γ Δ rfl
          ⟨trivial,
            G1nnfFinsetSequent.IsNNF.insert_right hANNF
              (G1nnfFinsetSequent.IsNNF.insert_right hNANNF hNNF)⟩
      exact ⟨tree.castTree rfl hΔeq⟩
  | cut A S T hANNF h1 h2 ih1 ih2 =>
      obtain ⟨sub1⟩ :=
        ih1 hΓ (mem_insert_represents_right A hΔ)
          (G1nnfFinsetSequent.IsNNF.insert_right hANNF hNNF)
      obtain ⟨sub2⟩ :=
        ih2 (mem_insert_represents_left A hΓ) hΔ
          (G1nnfFinsetSequent.IsNNF.insert_left hANNF hNNF)
      have hConc := G1nnfRule.cut_shared_conclusion A Γ Δ
      have hAC : G1nnfRule.ApplicationConditions (.cut A Γ Δ) Γ Δ := by
        refine ⟨trivial, ?_⟩
        simpa only [hConc] using hNNF
      let tree :=
        G1nnfProofTree.twoPremise (.cut A Γ Δ) Γ Δ rfl hAC sub1 sub2
      exact ⟨tree.castTree (congrArg Prod.fst hConc) (congrArg Prod.snd hConc)⟩
  | conjR A B S T h1 h2 ih1 ih2 =>
      have hTFinite : Set.Finite T :=
        finiteSet_of_finset_cover Δ
          (fun F hFT => (hΔ F).2 (Or.inl hFT))
      let Δ₀ := finsetOfFiniteSet T hTFinite
      have hΔ₀ : ∀ F, F ∈ Δ₀ ↔ T F :=
        mem_finsetOfFiniteSet T hTFinite
      have hBaseNNF : G1nnfFinsetSequent.IsNNF (Γ, Δ₀) := by
        refine ⟨hNNF.1, ?_⟩
        intro F hF
        exact hNNF.2 F ((hΔ F).2 (Or.inl ((hΔ₀ F).1 hF)))
      have hConjNNF : (FormulaN.conj A B).isNNF :=
        hNNF.2 _ ((hΔ _).2 (Or.inr rfl))
      obtain ⟨sub1⟩ :=
        ih1 hΓ (mem_insert_represents_right A hΔ₀)
          (G1nnfFinsetSequent.IsNNF.insert_right hConjNNF.1 hBaseNNF)
      obtain ⟨sub2⟩ :=
        ih2 hΓ (mem_insert_represents_right B hΔ₀)
          (G1nnfFinsetSequent.IsNNF.insert_right hConjNNF.2 hBaseNNF)
      let tree :=
        G1nnfProofTree.twoPremise (.conjRight A B) Γ Δ₀ rfl
          ⟨trivial,
            G1nnfFinsetSequent.IsNNF.insert_right hConjNNF hBaseNNF⟩
          sub1 sub2
      have hΔeq : LCS.Finset.insert (FormulaN.conj A B) Δ₀ = Δ :=
        LCS.Finset.ext (fun F =>
          (mem_insert_represents_right (FormulaN.conj A B) hΔ₀ F).trans
            (hΔ F).symm)
      exact ⟨tree.castTree rfl hΔeq⟩
  | conjL1 A B S T h ih =>
      have hSFinite : Set.Finite S :=
        finiteSet_of_finset_cover Γ
          (fun F hFS => (hΓ F).2 (Or.inr hFS))
      let Γ₀ := finsetOfFiniteSet S hSFinite
      have hΓ₀ : ∀ F, F ∈ Γ₀ ↔ S F :=
        mem_finsetOfFiniteSet S hSFinite
      have hBaseNNF : G1nnfFinsetSequent.IsNNF (Γ₀, Δ) := by
        refine ⟨?_, hNNF.2⟩
        intro F hF
        exact hNNF.1 F ((hΓ F).2 (Or.inr ((hΓ₀ F).1 hF)))
      have hConjNNF : (FormulaN.conj A B).isNNF :=
        hNNF.1 _ ((hΓ _).2 (Or.inl rfl))
      obtain ⟨sub⟩ :=
        ih (mem_insert_represents_left A hΓ₀) hΔ
          (G1nnfFinsetSequent.IsNNF.insert_left hConjNNF.1 hBaseNNF)
      let tree :=
        G1nnfProofTree.onePremise (.conjLeft1 A B) Γ₀ Δ rfl
          ⟨trivial,
            G1nnfFinsetSequent.IsNNF.insert_left hConjNNF hBaseNNF⟩ sub
      have hΓeq : LCS.Finset.insert (FormulaN.conj A B) Γ₀ = Γ :=
        LCS.Finset.ext (fun F =>
          (mem_insert_represents_left (FormulaN.conj A B) hΓ₀ F).trans
            (hΓ F).symm)
      exact ⟨tree.castTree hΓeq rfl⟩
  | conjL2 A B S T h ih =>
      have hSFinite : Set.Finite S :=
        finiteSet_of_finset_cover Γ
          (fun F hFS => (hΓ F).2 (Or.inr hFS))
      let Γ₀ := finsetOfFiniteSet S hSFinite
      have hΓ₀ : ∀ F, F ∈ Γ₀ ↔ S F :=
        mem_finsetOfFiniteSet S hSFinite
      have hBaseNNF : G1nnfFinsetSequent.IsNNF (Γ₀, Δ) := by
        refine ⟨?_, hNNF.2⟩
        intro F hF
        exact hNNF.1 F ((hΓ F).2 (Or.inr ((hΓ₀ F).1 hF)))
      have hConjNNF : (FormulaN.conj A B).isNNF :=
        hNNF.1 _ ((hΓ _).2 (Or.inl rfl))
      obtain ⟨sub⟩ :=
        ih (mem_insert_represents_left B hΓ₀) hΔ
          (G1nnfFinsetSequent.IsNNF.insert_left hConjNNF.2 hBaseNNF)
      let tree :=
        G1nnfProofTree.onePremise (.conjLeft2 A B) Γ₀ Δ rfl
          ⟨trivial,
            G1nnfFinsetSequent.IsNNF.insert_left hConjNNF hBaseNNF⟩ sub
      have hΓeq : LCS.Finset.insert (FormulaN.conj A B) Γ₀ = Γ :=
        LCS.Finset.ext (fun F =>
          (mem_insert_represents_left (FormulaN.conj A B) hΓ₀ F).trans
            (hΓ F).symm)
      exact ⟨tree.castTree hΓeq rfl⟩
  | disjL A B S T h1 h2 ih1 ih2 =>
      have hSFinite : Set.Finite S :=
        finiteSet_of_finset_cover Γ
          (fun F hFS => (hΓ F).2 (Or.inr hFS))
      let Γ₀ := finsetOfFiniteSet S hSFinite
      have hΓ₀ : ∀ F, F ∈ Γ₀ ↔ S F :=
        mem_finsetOfFiniteSet S hSFinite
      have hBaseNNF : G1nnfFinsetSequent.IsNNF (Γ₀, Δ) := by
        refine ⟨?_, hNNF.2⟩
        intro F hF
        exact hNNF.1 F ((hΓ F).2 (Or.inr ((hΓ₀ F).1 hF)))
      have hDisjNNF : (FormulaN.disj A B).isNNF :=
        hNNF.1 _ ((hΓ _).2 (Or.inl rfl))
      obtain ⟨sub1⟩ :=
        ih1 (mem_insert_represents_left A hΓ₀) hΔ
          (G1nnfFinsetSequent.IsNNF.insert_left hDisjNNF.1 hBaseNNF)
      obtain ⟨sub2⟩ :=
        ih2 (mem_insert_represents_left B hΓ₀) hΔ
          (G1nnfFinsetSequent.IsNNF.insert_left hDisjNNF.2 hBaseNNF)
      let tree :=
        G1nnfProofTree.twoPremise (.disjLeft A B) Γ₀ Δ rfl
          ⟨trivial,
            G1nnfFinsetSequent.IsNNF.insert_left hDisjNNF hBaseNNF⟩
          sub1 sub2
      have hΓeq : LCS.Finset.insert (FormulaN.disj A B) Γ₀ = Γ :=
        LCS.Finset.ext (fun F =>
          (mem_insert_represents_left (FormulaN.disj A B) hΓ₀ F).trans
            (hΓ F).symm)
      exact ⟨tree.castTree hΓeq rfl⟩
  | disjR1 A B S T h ih =>
      have hTFinite : Set.Finite T :=
        finiteSet_of_finset_cover Δ
          (fun F hFT => (hΔ F).2 (Or.inl hFT))
      let Δ₀ := finsetOfFiniteSet T hTFinite
      have hΔ₀ : ∀ F, F ∈ Δ₀ ↔ T F :=
        mem_finsetOfFiniteSet T hTFinite
      have hBaseNNF : G1nnfFinsetSequent.IsNNF (Γ, Δ₀) := by
        refine ⟨hNNF.1, ?_⟩
        intro F hF
        exact hNNF.2 F ((hΔ F).2 (Or.inl ((hΔ₀ F).1 hF)))
      have hDisjNNF : (FormulaN.disj A B).isNNF :=
        hNNF.2 _ ((hΔ _).2 (Or.inr rfl))
      obtain ⟨sub⟩ :=
        ih hΓ (mem_insert_represents_right A hΔ₀)
          (G1nnfFinsetSequent.IsNNF.insert_right hDisjNNF.1 hBaseNNF)
      let tree :=
        G1nnfProofTree.onePremise (.disjRight1 A B) Γ Δ₀ rfl
          ⟨trivial,
            G1nnfFinsetSequent.IsNNF.insert_right hDisjNNF hBaseNNF⟩ sub
      have hΔeq : LCS.Finset.insert (FormulaN.disj A B) Δ₀ = Δ :=
        LCS.Finset.ext (fun F =>
          (mem_insert_represents_right (FormulaN.disj A B) hΔ₀ F).trans
            (hΔ F).symm)
      exact ⟨tree.castTree rfl hΔeq⟩
  | disjR2 A B S T h ih =>
      have hTFinite : Set.Finite T :=
        finiteSet_of_finset_cover Δ
          (fun F hFT => (hΔ F).2 (Or.inl hFT))
      let Δ₀ := finsetOfFiniteSet T hTFinite
      have hΔ₀ : ∀ F, F ∈ Δ₀ ↔ T F :=
        mem_finsetOfFiniteSet T hTFinite
      have hBaseNNF : G1nnfFinsetSequent.IsNNF (Γ, Δ₀) := by
        refine ⟨hNNF.1, ?_⟩
        intro F hF
        exact hNNF.2 F ((hΔ F).2 (Or.inl ((hΔ₀ F).1 hF)))
      have hDisjNNF : (FormulaN.disj A B).isNNF :=
        hNNF.2 _ ((hΔ _).2 (Or.inr rfl))
      obtain ⟨sub⟩ :=
        ih hΓ (mem_insert_represents_right B hΔ₀)
          (G1nnfFinsetSequent.IsNNF.insert_right hDisjNNF.2 hBaseNNF)
      let tree :=
        G1nnfProofTree.onePremise (.disjRight2 A B) Γ Δ₀ rfl
          ⟨trivial,
            G1nnfFinsetSequent.IsNNF.insert_right hDisjNNF hBaseNNF⟩ sub
      have hΔeq : LCS.Finset.insert (FormulaN.disj A B) Δ₀ = Δ :=
        LCS.Finset.ext (fun F =>
          (mem_insert_represents_right (FormulaN.disj A B) hΔ₀ F).trans
            (hΔ F).symm)
      exact ⟨tree.castTree rfl hΔeq⟩
  | allL x A t S T hFreeFor h ih =>
      have hSFinite : Set.Finite S :=
        finiteSet_of_finset_cover Γ
          (fun F hFS => (hΓ F).2 (Or.inr hFS))
      let Γ₀ := finsetOfFiniteSet S hSFinite
      have hΓ₀ : ∀ F, F ∈ Γ₀ ↔ S F :=
        mem_finsetOfFiniteSet S hSFinite
      have hBaseNNF : G1nnfFinsetSequent.IsNNF (Γ₀, Δ) := by
        refine ⟨?_, hNNF.2⟩
        intro F hF
        exact hNNF.1 F ((hΓ F).2 (Or.inr ((hΓ₀ F).1 hF)))
      have hAllNNF : (FormulaN.all x A).isNNF :=
        hNNF.1 _ ((hΓ _).2 (Or.inl rfl))
      have hSubstNNF : (formulaSubstN A t x).isNNF :=
        isNNF_formulaSubstN A t x hAllNNF
      obtain ⟨sub⟩ :=
        ih (mem_insert_represents_left (formulaSubstN A t x) hΓ₀) hΔ
          (G1nnfFinsetSequent.IsNNF.insert_left hSubstNNF hBaseNNF)
      let tree :=
        G1nnfProofTree.onePremise (.allLeft x A t) Γ₀ Δ rfl
          ⟨hFreeFor,
            G1nnfFinsetSequent.IsNNF.insert_left hAllNNF hBaseNNF⟩ sub
      have hΓeq : LCS.Finset.insert (FormulaN.all x A) Γ₀ = Γ :=
        LCS.Finset.ext (fun F =>
          (mem_insert_represents_left (FormulaN.all x A) hΓ₀ F).trans
            (hΓ F).symm)
      exact ⟨tree.castTree hΓeq rfl⟩
  | allR x A y S T hFreeFor hFreshS hFreshT hFreshAll h ih =>
      have hTFinite : Set.Finite T :=
        finiteSet_of_finset_cover Δ
          (fun F hFT => (hΔ F).2 (Or.inl hFT))
      let Δ₀ := finsetOfFiniteSet T hTFinite
      have hΔ₀ : ∀ F, F ∈ Δ₀ ↔ T F :=
        mem_finsetOfFiniteSet T hTFinite
      have hBaseNNF : G1nnfFinsetSequent.IsNNF (Γ, Δ₀) := by
        refine ⟨hNNF.1, ?_⟩
        intro F hF
        exact hNNF.2 F ((hΔ F).2 (Or.inl ((hΔ₀ F).1 hF)))
      have hAllNNF : (FormulaN.all x A).isNNF :=
        hNNF.2 _ ((hΔ _).2 (Or.inr rfl))
      have hSubstNNF : (formulaSubstN A (.var y) x).isNNF :=
        isNNF_formulaSubstN A (.var y) x hAllNNF
      obtain ⟨sub⟩ :=
        ih hΓ
          (mem_insert_represents_right (formulaSubstN A (.var y) x) hΔ₀)
          (G1nnfFinsetSequent.IsNNF.insert_right hSubstNNF hBaseNNF)
      let tree :=
        G1nnfProofTree.onePremise (.allRight x A y) Γ Δ₀ rfl
          ⟨⟨hFreeFor, hFreshAll,
              fun F hF => hFreshS F ((hΓ F).1 hF),
              fun F hF => hFreshT F ((hΔ₀ F).1 hF)⟩,
            G1nnfFinsetSequent.IsNNF.insert_right hAllNNF hBaseNNF⟩ sub
      have hΔeq : LCS.Finset.insert (FormulaN.all x A) Δ₀ = Δ :=
        LCS.Finset.ext (fun F =>
          (mem_insert_represents_right (FormulaN.all x A) hΔ₀ F).trans
            (hΔ F).symm)
      exact ⟨tree.castTree rfl hΔeq⟩
  | exL x A y S T hFreeFor hFreshS hFreshT hFreshEx h ih =>
      have hSFinite : Set.Finite S :=
        finiteSet_of_finset_cover Γ
          (fun F hFS => (hΓ F).2 (Or.inr hFS))
      let Γ₀ := finsetOfFiniteSet S hSFinite
      have hΓ₀ : ∀ F, F ∈ Γ₀ ↔ S F :=
        mem_finsetOfFiniteSet S hSFinite
      have hBaseNNF : G1nnfFinsetSequent.IsNNF (Γ₀, Δ) := by
        refine ⟨?_, hNNF.2⟩
        intro F hF
        exact hNNF.1 F ((hΓ F).2 (Or.inr ((hΓ₀ F).1 hF)))
      have hExNNF : (FormulaN.ex x A).isNNF :=
        hNNF.1 _ ((hΓ _).2 (Or.inl rfl))
      have hSubstNNF : (formulaSubstN A (.var y) x).isNNF :=
        isNNF_formulaSubstN A (.var y) x hExNNF
      obtain ⟨sub⟩ :=
        ih
          (mem_insert_represents_left (formulaSubstN A (.var y) x) hΓ₀) hΔ
          (G1nnfFinsetSequent.IsNNF.insert_left hSubstNNF hBaseNNF)
      let tree :=
        G1nnfProofTree.onePremise (.exLeft x A y) Γ₀ Δ rfl
          ⟨⟨hFreeFor, hFreshEx,
              fun F hF => hFreshS F ((hΓ₀ F).1 hF),
              fun F hF => hFreshT F ((hΔ F).1 hF)⟩,
            G1nnfFinsetSequent.IsNNF.insert_left hExNNF hBaseNNF⟩ sub
      have hΓeq : LCS.Finset.insert (FormulaN.ex x A) Γ₀ = Γ :=
        LCS.Finset.ext (fun F =>
          (mem_insert_represents_left (FormulaN.ex x A) hΓ₀ F).trans
            (hΓ F).symm)
      exact ⟨tree.castTree hΓeq rfl⟩
  | exR x A t S T hFreeFor h ih =>
      have hTFinite : Set.Finite T :=
        finiteSet_of_finset_cover Δ
          (fun F hFT => (hΔ F).2 (Or.inl hFT))
      let Δ₀ := finsetOfFiniteSet T hTFinite
      have hΔ₀ : ∀ F, F ∈ Δ₀ ↔ T F :=
        mem_finsetOfFiniteSet T hTFinite
      have hBaseNNF : G1nnfFinsetSequent.IsNNF (Γ, Δ₀) := by
        refine ⟨hNNF.1, ?_⟩
        intro F hF
        exact hNNF.2 F ((hΔ F).2 (Or.inl ((hΔ₀ F).1 hF)))
      have hExNNF : (FormulaN.ex x A).isNNF :=
        hNNF.2 _ ((hΔ _).2 (Or.inr rfl))
      have hSubstNNF : (formulaSubstN A t x).isNNF :=
        isNNF_formulaSubstN A t x hExNNF
      obtain ⟨sub⟩ :=
        ih hΓ
          (mem_insert_represents_right (formulaSubstN A t x) hΔ₀)
          (G1nnfFinsetSequent.IsNNF.insert_right hSubstNNF hBaseNNF)
      let tree :=
        G1nnfProofTree.onePremise (.exRight x A t) Γ Δ₀ rfl
          ⟨hFreeFor,
            G1nnfFinsetSequent.IsNNF.insert_right hExNNF hBaseNNF⟩ sub
      have hΔeq : LCS.Finset.insert (FormulaN.ex x A) Δ₀ = Δ :=
        LCS.Finset.ext (fun F =>
          (mem_insert_represents_right (FormulaN.ex x A) hΔ₀ F).trans
            (hΔ F).symm)
      exact ⟨tree.castTree rfl hΔeq⟩

theorem G1nnfProofTree.castTree_eigenvariables {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (T : G1nnfProofTree hL Γ Δ) (v : Nat) :
    (T.castTree hΓ hΔ).eigenvariables v = T.eigenvariables v := by
  exact G1nnfProofTree.eigenvariables_cast hΓ hΔ T v

theorem G1nnfProofTree.eigenvariables_onePremise {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 1)
    (hAC : rule.ApplicationConditions Γ Δ)
    (sub : G1nnfProofTree hL
      ((rule.premises Γ Δ)[0]'(by omega)).1
      ((rule.premises Γ Δ)[0]'(by omega)).2)
    (v : Nat) :
    (G1nnfProofTree.onePremise rule Γ Δ hPrem hAC sub).eigenvariables v =
      ((match rule with
        | .allRight _ _ ev => v = ev
        | .exLeft _ _ ev => v = ev
        | _ => False) ∨ sub.eigenvariables v) := by
  cases rule <;> first | rfl | omega

theorem G1nnfProofTree.eigenvariables_twoPremise {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 2)
    (hAC : rule.ApplicationConditions Γ Δ)
    (sub1 : G1nnfProofTree hL
      ((rule.premises Γ Δ)[0]'(by omega)).1
      ((rule.premises Γ Δ)[0]'(by omega)).2)
    (sub2 : G1nnfProofTree hL
      ((rule.premises Γ Δ)[1]'(by omega)).1
      ((rule.premises Γ Δ)[1]'(by omega)).2)
    (v : Nat) :
    (G1nnfProofTree.twoPremise rule Γ Δ hPrem hAC sub1 sub2).eigenvariables v =
      ((match rule with
        | .allRight _ _ ev => v = ev
        | .exLeft _ _ ev => v = ev
        | _ => False) ∨ sub1.eigenvariables v ∨ sub2.eigenvariables v) := by
  cases rule <;> first | rfl | omega

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

theorem ruleEigenvariable_mem_variableSupport {L : Language}
    (rule : G1nnfRule L) (w : Nat)
    (hw :
      match rule with
      | .allRight _ _ ev => w = ev
      | .exLeft _ _ ev => w = ev
      | _ => False) :
    w ∈ rule.variableSupport := by
  cases rule <;>
    simp_all [G1nnfRule.variableSupport, LCS.Finset.mem_insert]

theorem eigenvariables_mem_variableSupport {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (w : Nat) :
    T.eigenvariables w → w ∈ T.variableSupport := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
      intro hw
      exact hw.elim
  | onePremise rule Γ Δ hPrem hAC sub ih =>
      intro hw
      rw [G1nnfProofTree.eigenvariables_onePremise] at hw
      rcases hw with hRule | hSub
      · exact
          G1nnfProofTree.variableSupport_onePremise_of_rule
            rule Γ Δ hPrem hAC sub w
              (ruleEigenvariable_mem_variableSupport rule w hRule)
      · exact
          G1nnfProofTree.variableSupport_onePremise_of_subtree
            rule Γ Δ hPrem hAC sub w (ih hSub)
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
      intro hw
      rw [G1nnfProofTree.eigenvariables_twoPremise] at hw
      rcases hw with hRule | hSubs
      · exact
          G1nnfProofTree.variableSupport_twoPremise_of_rule
            rule Γ Δ hPrem hAC sub1 sub2 w
              (ruleEigenvariable_mem_variableSupport rule w hRule)
      · rcases hSubs with hSub1 | hSub2
        · exact
            G1nnfProofTree.variableSupport_twoPremise_of_left_subtree
              rule Γ Δ hPrem hAC sub1 sub2 w (ih1 hSub1)
        · exact
            G1nnfProofTree.variableSupport_twoPremise_of_right_subtree
              rule Γ Δ hPrem hAC sub1 sub2 w (ih2 hSub2)

private theorem alphaRenameBoundTree_eigenvariables_eq {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (v z : Nat)
    (hvz : v ≠ z) (hz : z ∉ T.variableSupport) (w : Nat) :
    (T.alphaRenameBoundTree v z hvz hz).eigenvariables w =
      T.eigenvariables w := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
      simp only [alphaRenameBoundTree]
      rw [G1nnfProofTree.eigenvariables_cast]
      rfl
  | onePremise rule Γ Δ hPrem hAC sub ih =>
      simp only [alphaRenameBoundTree]
      rw [G1nnfProofTree.eigenvariables_cast]
      rw [G1nnfProofTree.eigenvariables_onePremise,
        G1nnfProofTree.eigenvariables_onePremise,
        G1nnfProofTree.eigenvariables_cast, ih]
      cases rule <;> rfl
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
      simp only [alphaRenameBoundTree]
      rw [G1nnfProofTree.eigenvariables_cast]
      rw [G1nnfProofTree.eigenvariables_twoPremise,
        G1nnfProofTree.eigenvariables_twoPremise,
        G1nnfProofTree.eigenvariables_cast,
        G1nnfProofTree.eigenvariables_cast, ih1, ih2]
      cases rule <;> rfl

theorem alphaRenameBoundAtRoot_eigenvariables_eq {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (v z : Nat)
    (hvz : v ≠ z) (hz : z ∉ T.variableSupport)
    (hRoot :
      (∀ A ∈ Γ, FormulaN.notBoundIn v A) ∧
      (∀ A ∈ Δ, FormulaN.notBoundIn v A))
    (w : Nat) :
    (T.alphaRenameBoundAtRoot v z hvz hz hRoot).eigenvariables w =
      T.eigenvariables w := by
  rw [alphaRenameBoundAtRoot, eigenvariables_castTree,
    T.alphaRenameBoundTree_eigenvariables_eq v z hvz hz w]

def ruleEigenlabel {L : Language} :
    G1nnfRule L → Option Nat
  | .allRight _ _ ev => some ev
  | .exLeft _ _ ev => some ev
  | _ => none

theorem ruleEigenlabel_eq_some_of_eigenMatch {L : Language}
    (rule : G1nnfRule L) (w : Nat)
    (hw :
      match rule with
      | .allRight _ _ ev => w = ev
      | .exLeft _ _ ev => w = ev
      | _ => False) :
    ruleEigenlabel rule = some w := by
  cases rule <;> simp_all [ruleEigenlabel]

end G1nnfProofTree
end LCS.CutElim.Hauptsatz
end

