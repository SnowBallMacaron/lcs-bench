import LCS.Herbrand.NNFHauptsatz.Theorem.Midsequents

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.Herbrand.NNFHauptsatz

open LCS.Herbrand.NNFHauptsatz.Soundness

open LCS.Herbrand.SharpenedHauptsatz

open LCS.Herbrand.SharpenedHauptsatz.Permutability

open LCS.Herbrand.SharpenedHauptsatz.Theorem

open LCS.Herbrand.PrenexForm

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

open LCS.CutElim.LK

namespace LCS.Herbrand.NNFHauptsatz.Theorem

open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree

open LCS.Herbrand.NNFHauptsatz.G2nnfRule

namespace G2nnfLocalExchangeOrderCertificate

helper /-- Exact body path to the reused source quantifier frontier, definitionally
factored through the generated required-lineage lower node. -/
def Theorem.G2nnfLocalExchangeOrderCertificate.sourceFrontierPathFromQuantifierPremise {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T output : G2nnfProofTree hL Γroot Δroot}
    {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    (certificate :
      G2nnfLocalExchangeOrderCertificate (output := output) redex) :
    RootToNodePath certificate.quantifierPremise
      certificate.targetLowerOccurrence.quantifierFrontier :=
  certificate.lowerPathFromQuantifierPremise.trans
    certificate.sourceFrontierPathFromLower

helper /-- Exact ambient path to the generated lower node, factoring through the
moved quantifier and its premise. -/
def Theorem.G2nnfLocalExchangeOrderCertificate.targetLowerPath {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T output : G2nnfProofTree hL Γroot Δroot}
    {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    (certificate :
      G2nnfLocalExchangeOrderCertificate (output := output) redex) :
    RootToNodePath output certificate.targetLowerOccurrence.node :=
  certificate.quantifierPath.trans
    (certificate.quantifierPremiseFrontier.path.trans
      certificate.lowerPathFromQuantifierPremise)

end G2nnfLocalExchangeOrderCertificate

end LCS.Herbrand.NNFHauptsatz.Theorem

end

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.Herbrand.NNFHauptsatz

open LCS.Herbrand.NNFHauptsatz.Soundness

open LCS.Herbrand.SharpenedHauptsatz

open LCS.Herbrand.SharpenedHauptsatz.Permutability

open LCS.Herbrand.SharpenedHauptsatz.Theorem

open LCS.Herbrand.PrenexForm

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

open LCS.CutElim.LK

namespace LCS.Herbrand.NNFHauptsatz.Theorem

open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree

open LCS.Herbrand.NNFHauptsatz.G2nnfRule

namespace G2nnfLocalExchangeAt

helper /-- Same-index preservation is enforced by the result type itself. -/
theorem Theorem.G2nnfLocalExchangeAt.sameConclusion {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T output : G2nnfProofTree hL Γroot Δroot}
    {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    (_exchange : G2nnfLocalExchangeAt redex output) :
    output.conclusion = T.conclusion :=
  rfl

helper /-- The exact structural exchange preserves cut-freedom whenever its source
is cut-free. -/
theorem Theorem.G2nnfLocalExchangeAt.cutFree {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T output : G2nnfProofTree hL Γroot Δroot}
    {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    (exchange : G2nnfLocalExchangeAt redex output) :
    T.isCutFree → output.isCutFree := by
  cases exchange with
  | rebuild _ _ _ preservesCutFree _ => exact preservesCutFree

helper /-- Pure-variable preservation uses source cut-freedom as well as source
purity; the former is needed for the bound-variable trace argument in the
case proof. -/
theorem Theorem.G2nnfLocalExchangeAt.pure {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T output : G2nnfProofTree hL Γroot Δroot}
    {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    (exchange : G2nnfLocalExchangeAt redex output) :
    T.isCutFree → IsPureVariableProofG2nnf T →
      IsPureVariableProofG2nnf output := by
  cases exchange with
  | rebuild _ _ _ _ preservesPure => exact preservesPure

helper /-- Extract the exact moved-quantifier/lower-descendant order certificate in
the ambient rebuilt proof. -/
def Theorem.G2nnfLocalExchangeAt.orderCertificate {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {T output : G2nnfProofTree hL Γroot Δroot}
    {R₁ R₂ : G2nnfRuleCore L}
    {redex : G2nnfPermutableOccurrence T R₁ R₂}
    (exchange : G2nnfLocalExchangeAt redex output) :
    G2nnfLocalExchangeOrderCertificate (output := output) redex :=
  match exchange with
  | .rebuild _ replacement kernel _ _ =>
    { targetPrincipal := kernel.targetPrincipal
      principalCorrespondence := kernel.principalCorrespondence
      Γquant := redex.lowerOccurrence.Γ
      Δquant := redex.lowerOccurrence.Δ
      quantifierNode := replacement
      quantifierGamma := kernel.quantifierGamma
      quantifierDelta := kernel.quantifierDelta
      quantifierApplication := kernel.quantifierApplication
      quantifierPath :=
        redex.lowerOccurrence.path.replacementPath replacement
      Γbody := kernel.Γbody
      Δbody := kernel.Δbody
      quantifierPremise := kernel.body
      quantifierPremiseFrontier := kernel.quantifierPremise
      bodyShape := kernel.bodyShape
      simulationPosition := kernel.simulationPosition
      otherFrontierMultiplicity := kernel.otherFrontierMultiplicity }

end G2nnfLocalExchangeAt

end LCS.Herbrand.NNFHauptsatz.Theorem

end

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.Herbrand.NNFHauptsatz

open LCS.Herbrand.NNFHauptsatz.Soundness

open LCS.Herbrand.SharpenedHauptsatz

open LCS.Herbrand.SharpenedHauptsatz.Permutability

open LCS.Herbrand.SharpenedHauptsatz.Theorem

open LCS.Herbrand.PrenexForm

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

open LCS.CutElim.LK

namespace LCS.Herbrand.NNFHauptsatz.Theorem

open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree

open LCS.Herbrand.NNFHauptsatz.G2nnfRule

helper /-- Lemma 7.4.2 (companion def): Predicate asserting that a given G2nnf
rule appears at some node in a proof tree. -/
def Theorem.RuleAppearsInTree {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (r : G2nnfRule L hL) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → Prop
  | _, _, .leaf _ _ h _ _ => h.elim
  | _, _, .extraAxiom _ _ h _ _ => h.elim
  | _, _, .axiom_ rule _ _ _ => r.val = rule
  | _, _, .onePremise rule _ _ _ sub =>
    r.val = rule ∨ RuleAppearsInTree r sub
  | _, _, .twoPremise rule _ _ _ sub1 sub2 =>
    r.val = rule ∨ RuleAppearsInTree r sub1 ∨
    RuleAppearsInTree r sub2

helper /-- Lemma 7.4.2 (companion def): Predicate asserting that rule R1 appears strictly below rule R2 in a proof tree T. That is, R1 is closer to the root than R2, and there is a root-to-leaf path containing both with R1 encountered before R2. -/
def Theorem.RuleAppearsBelow {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (R₁ R₂ : G2nnfRule L hL) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → Prop
  | _, _, .leaf _ _ h _ _ => h.elim
  | _, _, .extraAxiom _ _ h _ _ => h.elim
  | _, _, .axiom_ _ _ _ _ => False
  | _, _, .onePremise rule _ _ _ sub =>
    (rule = R₁.val ∧ RuleAppearsInTree R₂ sub) ∨
    RuleAppearsBelow R₁ R₂ sub
  | _, _, .twoPremise rule _ _ _ sub1 sub2 =>
    (rule = R₁.val ∧
      (RuleAppearsInTree R₂ sub1 ∨
       RuleAppearsInTree R₂ sub2)) ∨
    RuleAppearsBelow R₁ R₂ sub1 ∨
    RuleAppearsBelow R₁ R₂ sub2

helper /-- Theorem 7.4.1 (companion def): Predicate asserting that every rule applied in a G2nnf proof tree is a quantifier-for-subformulae rule (not a propositional, weakening, or structural rule). Used for the lower part of the midsequent splitting. -/
def Theorem.AllRulesQuantifier {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)] :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → Prop
  | _, _, .leaf _ _ h _ _ => h.elim
  | _, _, .extraAxiom _ _ h _ _ => h.elim
  | _, _, .axiom_ _ _ _ _ => True
  | _, _, .onePremise rule _ _ _ sub =>
    rule.isQuantifierRule ∧ AllRulesQuantifier (hL := hL) sub
  | _, _, .twoPremise rule _ _ _ sub1 sub2 =>
    rule.isQuantifierRule ∧
    AllRulesQuantifier (hL := hL) sub1 ∧
    AllRulesQuantifier (hL := hL) sub2























helper /-- Theorem 7.4.1 (companion def): There is an occurrence of `mid` in `T`
whose occurrence-indexed root-to-node path contains only
quantifier-for-subformulae inferences. -/
def Theorem.AllRulesQuantifierToMid {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (mid : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → Prop
  | _, _, T =>
    ∃ occurrence : NodeOccurrence T mid.1 mid.2,
      AllRulesQuantifierOnPath occurrence.path

helper /-- Positive regression: a single occurrence satisfying both the upper and
lower conditions constructs a G2nnf midsequent witness. -/
theorem Theorem.isMidsequentG2nnf_of_sharedOccurrence {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γ Δ}
    {mid : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)}
    (occurrence : NodeOccurrence T mid.1 mid.2)
    (hQF :
      (∀ A, Membership.mem mid.1 A →
        FirstOrder.SemanticsN.isQuantifierFree A) ∧
      (∀ A, Membership.mem mid.2 A →
        FirstOrder.SemanticsN.isQuantifierFree A))
    (hAbove : AllRulesPropOrWeakening (hL := hL) occurrence.node)
    (hBelow : AllRulesQuantifierOnPath occurrence.path) :
    IsMidsequentG2nnf T mid :=
  ⟨hQF, ⟨occurrence, hAbove, hBelow⟩⟩



helper /-- Adversarial regression: even when two distinct occurrences have the same
sequent index, an upper witness from one occurrence cannot be spliced with a
lower-path witness from the other.  If these are the only occurrences of that
sequent and each fails the complementary condition, the shared-occurrence
predicate is rejected. -/
theorem Theorem.isMidsequentG2nnf_rejects_duplicateSequentSplice {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γ Δ}
    {mid : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)}
    (upper lower : NodeOccurrence T mid.1 mid.2)
    (hDistinct : upper ≠ lower)
    (hOnly : ∀ occurrence : NodeOccurrence T mid.1 mid.2,
      occurrence = upper ∨ occurrence = lower)
    (hUpper : AllRulesPropOrWeakening (hL := hL) upper.node)
    (hUpperNotLower : ¬ AllRulesQuantifierOnPath upper.path)
    (hLower : AllRulesQuantifierOnPath lower.path)
    (hLowerNotUpper : ¬ AllRulesPropOrWeakening (hL := hL) lower.node) :
    upper ≠ lower ∧
      (AllRulesPropOrWeakening (hL := hL) upper.node ∧
       AllRulesQuantifierOnPath lower.path) ∧
      ¬ IsMidsequentG2nnf T mid := by
  refine ⟨hDistinct, ⟨hUpper, hLower⟩, ?_⟩
  intro hMid
  rcases hMid.midOccurrence with ⟨occurrence, hAbove, hBelow⟩
  rcases hOnly occurrence with hEq | hEq
  · subst occurrence
    exact hUpperNotLower hBelow
  · subst occurrence
    exact hLowerNotUpper hAbove

proof_of nnfHauptsatzExFinalAntecedent_equiv := open LCS.Herbrand.NNFHauptsatz.Theorem.Midsequents.Proofs.Theorem in
  by
    simp only [nnfHauptsatzExMidsequent, nnfHauptsatzExFinalSequent,
      List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    change ((formulaEvalN M nnfHauptEx_Pa s ∨ formulaEvalN M nnfHauptEx_Qa s ∨
        formulaEvalN M nnfHauptEx_Rfa s) ∧
      (formulaEvalN M nnfHauptEx_Pa s ∨ formulaEvalN M nnfHauptEx_Qa s ∨
        formulaEvalN M nnfHauptEx_Rfb s)) ↔
      ((formulaEvalN M nnfHauptEx_Pa s ∨ formulaEvalN M nnfHauptEx_Qa s) ∨
        (formulaEvalN M nnfHauptEx_Rfa s ∧ formulaEvalN M nnfHauptEx_Rfb s))
    constructor
    · rintro ⟨hA, hB⟩
      rcases hA with hP | hQ | hRa
      · exact Or.inl (Or.inl hP)
      · exact Or.inl (Or.inr hQ)
      · rcases hB with hP | hQ | hRb
        · exact Or.inl (Or.inl hP)
        · exact Or.inl (Or.inr hQ)
        · exact Or.inr ⟨hRa, hRb⟩
    · rintro ((hP | hQ) | ⟨hRa, hRb⟩)
      · exact ⟨Or.inl hP, Or.inl hP⟩
      · exact ⟨Or.inr (Or.inl hQ), Or.inr (Or.inl hQ)⟩
      · exact ⟨Or.inr (Or.inr hRa), Or.inr (Or.inr hRb)⟩


proof_of nnfHauptsatzExFinalSequent_equiv := open LCS.Herbrand.NNFHauptsatz.Theorem.Midsequents.Proofs.Theorem in
  by
    constructor
    · intro h hFinal
      exact h ((nnfHauptsatzExFinalAntecedent_equiv M s).mpr hFinal)
    · intro h hMid
      exact h ((nnfHauptsatzExFinalAntecedent_equiv M s).mp hMid)








end LCS.Herbrand.NNFHauptsatz.Theorem

end

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.Herbrand.NNFHauptsatz

open LCS.Herbrand.NNFHauptsatz.Soundness

open LCS.Herbrand.SharpenedHauptsatz

open LCS.Herbrand.SharpenedHauptsatz.Permutability

open LCS.Herbrand.SharpenedHauptsatz.Theorem

open LCS.Herbrand.PrenexForm

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

open LCS.CutElim.LK

namespace LCS.Herbrand.NNFHauptsatz.Theorem

open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree

open LCS.Herbrand.NNFHauptsatz.G2nnfRule

noncomputable section















end

end LCS.Herbrand.NNFHauptsatz.Theorem

end
