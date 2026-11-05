import LCS.Herbrand.NNFHauptsatz.Equality.Part1

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

namespace LCS.Herbrand.NNFHauptsatz.G2nnfEqProofTree



helper /-- Adversarial occurrence-identity regression for G2nnf=: even when the same
proof-tree value, with the same sequent index, is reused as both premises, its
left and right occurrences remain distinct because their paths record
different premise choices. -/
theorem G2nnfEqProofTree.duplicateEqualSequentOccurrences_distinct {L : Language}
    {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    (A : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L))
    (hConjRect : isRectified (.conj A A))
    (sub : G2nnfEqProofTree hL Gamma
      (LCS.Finset.insert A Delta)) :
    let root : G2nnfEqProofTree hL Gamma
        (LCS.Finset.insert (.conj A A) Delta) :=
      .twoPremise (.conjRight A A Gamma Delta) trivial
        rfl
        (conjRightSideConditions A Gamma Delta hConjRect sub) sub sub
    let left : NodeOccurrence root Gamma
        (LCS.Finset.insert A Delta) :=
      ⟨sub, .leftPremise (.conjRight A A Gamma Delta) trivial
        rfl
        (conjRightSideConditions A Gamma Delta hConjRect sub)
        sub sub (.root sub)⟩
    let right : NodeOccurrence root Gamma
        (LCS.Finset.insert A Delta) :=
      ⟨sub, .rightPremise (.conjRight A A Gamma Delta) trivial
        rfl
        (conjRightSideConditions A Gamma Delta hConjRect sub)
        sub sub (.root sub)⟩
    left ≠ right := by
  dsimp only
  intro h
  cases h

end LCS.Herbrand.NNFHauptsatz.G2nnfEqProofTree

end

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

helper /-- Positive G2nnf= occurrence regression: a variable that occurs inside
the exact sole-premise subtree is permitted when the inference conclusion is
variable-free.  The result records the concrete inside occurrence and the
accepted occurrence-sensitive condition together. -/
theorem Equality.variableConfinedToExactPremiseOccurrenceEq_accepted
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (y : Nat) (rule : G2nnfRuleCore L)
    (hAdmit : True)
    (hPrem : rule.premises.length = 1)
    (hSC : rule.SideConditions)
    (sub : G2nnfEqProofTree hL
      (rule.premises[0]'(by omega)).1
      (rule.premises[0]'(by omega)).2)
    (f : FormulaN L) (hf : g2nnfEqProofTreeContainsFormula sub f)
    (hy : Membership.mem (formulaAllVariables f) y)
    (hConclusion : g2nnfEqSequentVariableFree y
      rule.conclusion.1
      rule.conclusion.2) :
    let root :=
      G2nnfDeductionTreeCore.onePremise rule hAdmit hPrem hSC sub
    let occurrence : NodeOccurrence root _ _ :=
      ⟨sub, .onePremise rule hAdmit hPrem hSC sub (.root sub)⟩
    g2nnfEqProofTreeContainsFormula sub f ∧
    Membership.mem (formulaAllVariables f) y ∧
    g2nnfEqEigenvariableOccursOnlyInSubtree y occurrence := by
  dsimp only
  exact ⟨hf, hy, hConclusion, trivial⟩

helper /-- Nested-quantifier regression for G2nnf=: a base `allSubRight` reached
below other inferences uses the path composed from the fixed whole tree
`outer` to its exact premise occurrence. -/
theorem Equality.nestedAllSubRightEqUsesWholeTreeOccurrence
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (A B : FormulaN L) (occurrence : MaxQuantifierOccurrence A)
    (x y : Nat)
    (hSelected : occurrence.selected = FormulaN.all x B)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (hPrem :
      (G2nnfRuleCore.allSubRight A occurrence x B y hSelected Gamma Delta).premises.length = 1)
    (hSC : G2nnfRuleCore.SideConditions
      (.allSubRight A occurrence x B y hSelected Gamma Delta))
    (sub : G2nnfEqProofTree hL
      (((G2nnfRuleCore.allSubRight A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1
      (((G2nnfRuleCore.allSubRight A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).2)
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    (outer : G2nnfEqProofTree hL Γroot Δroot)
    (path : G2nnfEqProofTree.RootToNodePath outer
      (.onePremise
        (.allSubRight A occurrence x B y hSelected Gamma Delta) trivial
        hPrem hSC sub)) :
    isPureVariableProof_G2nnfEqAux outer
        (.onePremise
          (.allSubRight A occurrence x B y hSelected Gamma Delta) trivial
          hPrem hSC sub) path →
      g2nnfEqEigenvariableOccursOnlyInSubtree y
        (⟨sub, path.trans
          (.onePremise
            (.allSubRight A occurrence x B y hSelected Gamma Delta)
            trivial
            hPrem hSC sub (.root sub))⟩ :
          G2nnfEqProofTree.NodeOccurrence outer _ _) := by
  intro hPure
  exact hPure.1.2

helper /-- Lemma 7.4.3 (companion def): Predicate asserting that a given G2nnf=
rule appears at some node in a proof tree. At an equality-axiom leaf,
the requested schema must be well formed and have exactly that leaf's sequent;
ordinary inference nodes retain their complete stored-context rule. -/
def Equality.RuleAppearsInTree_G2nnfEq {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (r : G2nnfEqRule L hL) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfEqProofTree hL Γ Δ → Prop
  | _, _, .leaf _ _ hOpen _ _ => hOpen.elim
  | Γ, Δ, .extraAxiom _ _ _ _ _ =>
    match r with
    | .eqAxiom ax => ax.WellFormed ∧ ax.toSequent = (Γ, Δ)
    | .base _ => False
  | _, _, .axiom_ rule _ _ _ => r = .base rule
  | _, _, .onePremise rule _ _ _ sub =>
    r = .base rule ∨ RuleAppearsInTree_G2nnfEq r sub
  | _, _, .twoPremise rule _ _ _ sub1 sub2 =>
    r = .base rule ∨ RuleAppearsInTree_G2nnfEq r sub1 ∨
    RuleAppearsInTree_G2nnfEq r sub2

helper /-- Lemma 7.4.3 (companion def): Predicate asserting that rule R1 appears strictly below rule R2 in a G2nnf= proof tree T. That is, R1 is closer to the root than R2, and there is a root-to-leaf path containing both with R1 encountered before R2. -/
def Equality.RuleAppearsBelow_G2nnfEq {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (R₁ R₂ : G2nnfEqRule L hL) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfEqProofTree hL Γ Δ → Prop
  | _, _, .leaf _ _ hOpen _ _ => hOpen.elim
  | _, _, .extraAxiom _ _ _ _ _ => False
  | _, _, .axiom_ _ _ _ _ => False
  | _, _, .onePremise rule _ _ _ sub =>
    ((G2nnfEqRule.base rule) = R₁ ∧ RuleAppearsInTree_G2nnfEq R₂ sub) ∨
    RuleAppearsBelow_G2nnfEq R₁ R₂ sub
  | _, _, .twoPremise rule _ _ _ sub1 sub2 =>
    ((G2nnfEqRule.base rule) = R₁ ∧
      (RuleAppearsInTree_G2nnfEq R₂ sub1 ∨
       RuleAppearsInTree_G2nnfEq R₂ sub2)) ∨
    RuleAppearsBelow_G2nnfEq R₁ R₂ sub1 ∨
    RuleAppearsBelow_G2nnfEq R₁ R₂ sub2

end LCS.Herbrand.NNFHauptsatz.Equality

end
