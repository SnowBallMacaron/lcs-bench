import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.ProofTrees
import LCS.CutElim.Hauptsatz.CutElimination.CutRank
import LCS.CutElim.Hauptsatz.CutElimination.NotBound
import LCS.CutElim.Hauptsatz.CutElimination.Eigenvariables
import LCS.CutElim.Hauptsatz.CutElimination.TreeTransport
import LCS.CutElim.Hauptsatz.CutElimination.FormulaSubstitution

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
