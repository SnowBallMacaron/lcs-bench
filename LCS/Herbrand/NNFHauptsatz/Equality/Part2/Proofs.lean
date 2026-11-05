import LCS.Herbrand.NNFHauptsatz.Equality.Part2

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.Herbrand.NNFHauptsatz

open LCS.Herbrand.NNFHauptsatz.Theorem

open LCS.Herbrand.SharpenedHauptsatz

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Equality

namespace LCS.Herbrand.NNFHauptsatz.Equality

open LCS.Herbrand.NNFHauptsatz.G2nnfEqRule

open LCS.Herbrand.NNFHauptsatz.G2nnfEqProofTree

helper /-- Theorem 7.4.2 (companion def): There is an occurrence of `mid` in `T`
whose occurrence-indexed root-to-node path contains only G2nnf=
quantifier-for-subformulae inferences. -/
def AllRulesQuantifierToMid_G2nnfEq {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (mid : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfEqProofTree hL Γ Δ → Prop
  | _, _, T =>
    ∃ occurrence : G2nnfEqProofTree.NodeOccurrence T mid.1 mid.2,
      AllRulesQuantifierOnPath_G2nnfEq occurrence.path

helper /-- Positive regression: a single occurrence satisfying both the upper and
lower conditions constructs a G2nnf= midsequent witness. -/
theorem isMidsequent_G2nnfEq_of_sharedOccurrence {L : Language}
    {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfEqProofTree hL Γ Δ}
    {mid : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)}
    (occurrence : G2nnfEqProofTree.NodeOccurrence T mid.1 mid.2)
    (hQF :
      (∀ A, Membership.mem mid.1 A →
        FirstOrder.SemanticsN.isQuantifierFree A) ∧
      (∀ A, Membership.mem mid.2 A →
        FirstOrder.SemanticsN.isQuantifierFree A))
    (hAbove : allRulesSatisfy (fun rule =>
      rule.isPropositionalOnly ∨ rule.isWeakening ∨
      rule.isInessentialCut) occurrence.node)
    (hBelow : AllRulesQuantifierOnPath_G2nnfEq occurrence.path) :
    IsMidsequent_G2nnfEq T mid :=
  ⟨hQF, ⟨occurrence, hAbove, hBelow⟩⟩

helper /-- Adversarial regression: two distinct occurrences with the same sequent
index cannot contribute the upper and lower conditions separately.  If these
are the only occurrences and each fails the other condition, the
shared-occurrence predicate is rejected. -/
theorem isMidsequent_G2nnfEq_rejects_duplicateSequentSplice {L : Language}
    {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfEqProofTree hL Γ Δ}
    {mid : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)}
    (upper lower : G2nnfEqProofTree.NodeOccurrence T mid.1 mid.2)
    (hDistinct : upper ≠ lower)
    (hOnly : ∀ occurrence :
      G2nnfEqProofTree.NodeOccurrence T mid.1 mid.2,
      occurrence = upper ∨ occurrence = lower)
    (hUpper : allRulesSatisfy (fun rule =>
      rule.isPropositionalOnly ∨ rule.isWeakening ∨
      rule.isInessentialCut) upper.node)
    (hUpperNotLower :
      ¬ AllRulesQuantifierOnPath_G2nnfEq upper.path)
    (hLower : AllRulesQuantifierOnPath_G2nnfEq lower.path)
    (hLowerNotUpper : ¬ allRulesSatisfy (fun rule =>
      rule.isPropositionalOnly ∨ rule.isWeakening ∨
      rule.isInessentialCut) lower.node) :
    upper ≠ lower ∧
      (allRulesSatisfy (fun rule =>
        rule.isPropositionalOnly ∨ rule.isWeakening ∨
        rule.isInessentialCut) upper.node ∧
       AllRulesQuantifierOnPath_G2nnfEq lower.path) ∧
      ¬ IsMidsequent_G2nnfEq T mid := by
  refine ⟨hDistinct, ⟨hUpper, hLower⟩, ?_⟩
  intro hMid
  rcases hMid.midOccurrence with ⟨occurrence, hAbove, hBelow⟩
  rcases hOnly occurrence with hEq | hEq
  · subst occurrence
    exact hUpperNotLower hBelow
  · subst occurrence
    exact hLowerNotUpper hAbove

proof_of g2nnfEq_permutability := by
  -- BEGIN PROOF
    -- REPAIR(T7-49): proof pending
    sorry


proof_of sharpenedHauptsatz_G2nnfEq := by
  -- BEGIN PROOF
    -- REPAIR(T7-49): proof pending
    sorry


helper /-- Definition 7.4.4 (soundness): every legal G2nnf= proof has a valid
end sequent in every structure and assignment. Equality in `formulaEvalN`
is identity of the interpreted terms. The tree carries the NNF, rectification
and inference side conditions, including guarded equality-axiom admission. -/
theorem g2nnfEq_tree_soundness {L : Language} (hL : L.hasEquality = true)
    [DecidableEq (FormulaN L)] {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfEqProofTree hL Γ Δ) : Soundness.setSequentValid Γ Δ := by
  intro M s hΓ
  have hNotFals : ¬ Soundness.setSequentFalsifiableIn M Γ Δ := by
    clear hΓ
    induction T with
    | leaf _ _ h _ _ => exact h.elim
    | extraAxiom Γ Δ hExtra _ _ =>
      rcases hExtra with ⟨ax, hWF, hSeq⟩
      have hValid := g1nnfEqAxiom_valid ax hWF
      rw [hSeq] at hValid
      rintro ⟨val, hLeft, hRight⟩
      obtain ⟨A, hA, hEval⟩ := hValid M val hLeft
      exact hRight A hA hEval
    | axiom_ rule _ hAxiom hSC =>
      intro hFals
      obtain ⟨prem, hMem, _⟩ :=
        Soundness.g2nnf_core_rule_falsification_preservation M rule hSC hFals
      exact Soundness.list_len_zero_not_mem _ hAxiom prem hMem
    | onePremise rule _ hPrem hSC sub ih =>
      intro hFals
      obtain ⟨prem, hMem, hPremFals⟩ :=
        Soundness.g2nnf_core_rule_falsification_preservation M rule hSC hFals
      have hEq := Soundness.list_len_one_eq_zero _ hPrem prem hMem
      rw [hEq] at hPremFals
      exact ih hPremFals
    | twoPremise rule _ hPrem hSC sub₁ sub₂ ih₁ ih₂ =>
      intro hFals
      obtain ⟨prem, hMem, hPremFals⟩ :=
        Soundness.g2nnf_core_rule_falsification_preservation M rule hSC hFals
      rcases Soundness.list_len_two_eq_zero_or_one _ hPrem prem hMem with h₁ | h₂
      · rw [h₁] at hPremFals
        exact ih₁ hPremFals
      · rw [h₂] at hPremFals
        exact ih₂ hPremFals
  exact Classical.byContradiction fun hNoRight =>
    hNotFals ⟨s, hΓ, fun A hA hEval => hNoRight ⟨A, hA, hEval⟩⟩

proof_of g2nnfEq_provable_implies_valid := by
  rintro ⟨T⟩
  exact g2nnfEq_tree_soundness hL T


end LCS.Herbrand.NNFHauptsatz.Equality

end
