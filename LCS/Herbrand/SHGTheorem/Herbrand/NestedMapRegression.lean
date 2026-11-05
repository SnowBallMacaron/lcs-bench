import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.SyntaxAllocation
import LCS.Herbrand.SHGTheorem.Herbrand.OccurrenceLineage
import LCS.Herbrand.SHGTheorem.Herbrand.CanonicalMapRegression

section
namespace LCS.Herbrand.SHGTheorem.Herbrand
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.Equality
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.Herbrand.PrenexForm
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
namespace OrderedEigenvarCompositionRegression
open CanonicalEigenvarMapRegression
noncomputable section

/-- A cycle is rejected; in particular the first forward edge cannot
be justified by a later cell. -/
theorem cyclicDependency_rejected :
    ¬ EigenvarSkolemMapRangeAvoidsDomain spec cyclicDependencyMap
      [7, 8] := by
  intro h
  exact h 7 (.var 8) (by simp [cyclicDependencyMap])
    8 (by simp) (by rfl)

def rootOccurrence : G2nnfEqExSubLeftOccurrence exTree where
  ambient := exAmbient
  maxOccurrence := exMaxOccurrence
  boundVar := 1
  body := proofAtom
  eigenvariable := 7
  hSelected := rfl
  gamma := LCS.Finset.empty
  delta := delta
  hPrem := exRule_onePremise
  hSC := exRule_sideConditions
  premise := leaf
  path := .root exTree

def foreignCellMap : EigenvarSkolemMap spec :=
  fun y => if y = 42 then some exactTerm else none

private theorem rootOccurrence_strictAncestors_empty :
    g2nnfEqStrictExSubLeftAncestorEigenvariables rootOccurrence.path =
      [] := by
  rfl

/-- A map cell from outside the exact root-to-occurrence branch cannot
enter the ancestor map. At a root occurrence the strict ancestor set
is empty. -/
theorem unrelatedBranchCellG2_rejected :
    ¬ IsG2nnfEqStrictAncestorEigenvarMap spec legalMap rootOccurrence
      foreignCellMap := by
  intro h
  have h42 := (h 42 exactTerm).mp (by simp [foreignCellMap])
  rw [rootOccurrence_strictAncestors_empty] at h42
  exact (List.not_mem_nil (a := 42) h42.1).elim

noncomputable def rootOccurrenceEq :
    G2nnfEqExSubLeftOccurrence exTreeEq where
  ambient := exAmbient
  maxOccurrence := exMaxOccurrence
  boundVar := 1
  body := proofAtom
  eigenvariable := 7
  hSelected := rfl
  gamma := LCS.Finset.empty
  delta := delta
  hPrem := exRule_onePremise
  hSC := exRule_sideConditions
  premise := leafEq
  path := .root exTreeEq

private theorem rootOccurrenceEq_strictAncestors_empty :
    g2nnfEqStrictExSubLeftAncestorEigenvariables
      rootOccurrenceEq.path = [] := by
  rfl

/-- Equality-system mirror: a non-ancestor branch cell is likewise
excluded from the exact ancestor map. -/
theorem unrelatedBranchCellG2Eq_rejected :
    ¬ IsG2nnfEqStrictAncestorEigenvarMap spec legalMap
      rootOccurrenceEq foreignCellMap := by
  intro h
  have h42 := (h 42 exactTerm).mp (by simp [foreignCellMap])
  rw [rootOccurrenceEq_strictAncestors_empty] at h42
  exact (List.not_mem_nil (a := 42) h42.1).elim

end
end OrderedEigenvarCompositionRegression
end LCS.Herbrand.SHGTheorem.Herbrand
end

section
namespace LCS.Herbrand.SHGTheorem.Herbrand
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.Equality
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.Herbrand.PrenexForm
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
namespace NestedCanonicalMapRegression
open CanonicalEigenvarMapRegression
noncomputable section

def atom : FormulaN language :=
  .eq_ rfl (.var 1) (.var 2)

def innerExistential : FormulaN language :=
  .ex 2 atom

def universalBody : FormulaN language :=
  .all 1 innerExistential

def nestedSource : FormulaN language :=
  .ex 0 universalBody

private theorem nestedSource_rectified :
    LCS.FirstOrder.Semantics.Subformulae.isRectified nestedSource := by
  simp [nestedSource, universalBody, innerExistential, atom,
    LCS.FirstOrder.Semantics.Subformulae.isRectified,
    LCS.FirstOrder.Semantics.Subformulae.boundVarsFresh,
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
    formulaFVN, formulaBVN, termFV]

def nestedSpec : SkolemSpec language where
  source := nestedSource
  hNNF := by
    simp [nestedSource, universalBody, innerExistential, atom,
      FormulaN.isNNF]
  hRect := nestedSource_rectified
  hSentence := by
    unfold FormulaN.isClosed
    funext x
    apply propext
    change
      (((((x = 1 ∨ x = 2) ∧ x ≠ 2) ∧ x ≠ 1) ∧ x ≠ 0) ↔
        False)
    constructor
    · rintro ⟨⟨⟨hx, hx2⟩, hx1⟩, _⟩
      rcases hx with h1 | h2
      · exact hx1 h1
      · exact hx2 h2
    · exact False.elim

def outerIndex : Fin nestedSpec.n := ⟨0, by decide⟩

def innerIndex : Fin nestedSpec.n := ⟨1, by decide⟩

def afterOuter : FormulaN language :=
  formulaSubstN universalBody (.var 7) 0

def afterUniversalShown : FormulaN language :=
  .ex 2 (.eq_ rfl (.var 7) (.var 2))

def afterUniversal : FormulaN language :=
  formulaSubstN innerExistential (.var 7) 1

def leafAtom : FormulaN language :=
  .eq_ rfl (.var 7) (.var 8)

def leafFormula : FormulaN language :=
  formulaSubstN (.eq_ rfl (.var 7) (.var 2)) (.var 8) 2

private theorem afterOuter_eq :
    afterOuter = universalBody := by
  simp [afterOuter, nestedSource, universalBody, innerExistential,
    atom, formulaSubstN, termSubst]

private theorem afterUniversal_eq :
    afterUniversal = afterUniversalShown := by
  simp [universalBody, innerExistential, atom,
    afterUniversal, afterUniversalShown, formulaSubstN, termSubst]

theorem leafFormula_eq :
    leafFormula = leafAtom := by
  simp [leafFormula, afterUniversalShown, leafAtom,
    formulaSubstN, termSubst]

theorem leafFormula_rectified :
    isRectified leafFormula :=
  AllRectified.isRectified_of_isQuantifierFree leafFormula (by
    rw [leafFormula_eq]
    simp [leafAtom, isQuantifierFree])

private theorem afterOuter_rectified :
    isRectified afterOuter := by
  rw [afterOuter_eq]
  simp [universalBody, innerExistential, atom, isRectified,
    boundVarsFresh, distinctQuantifierBindings, formulaFVN, formulaBVN,
    termFV]

private theorem afterUniversal_rectified :
    isRectified afterUniversal := by
  rw [afterUniversal_eq]
  simp [afterUniversalShown, isRectified, boundVarsFresh,
    distinctQuantifierBindings, formulaFVN, formulaBVN, termFV]

def outerMaxOccurrence : MaxQuantifierOccurrence nestedSource :=
  .ex 0 universalBody

def universalMaxOccurrence : MaxQuantifierOccurrence afterOuter :=
  .all 1 innerExistential

def innerMaxOccurrence : MaxQuantifierOccurrence afterUniversal :=
  .ex 2 (.eq_ rfl (.var 7) (.var 2))

def closingAtom : FormulaN language :=
  .eq_ rfl (.var 3) (.var 3)

private theorem closingAtom_rectified :
    isRectified closingAtom :=
  AllRectified.isRectified_of_isQuantifierFree closingAtom (by
    simp [closingAtom, isQuantifierFree])

def gamma : LCS.Finset (FormulaN language) :=
  LCS.Finset.singleton closingAtom

def delta : LCS.Finset (FormulaN language) :=
  LCS.Finset.singleton closingAtom

def outerRule : G2nnfRuleCore language :=
  .exSubLeft nestedSource outerMaxOccurrence 0 universalBody 7 rfl gamma delta

theorem outerRule_onePremise :
    outerRule.premises.length = 1 := rfl

theorem outerRule_sideConditions :
    G2nnfRuleCore.SideConditions outerRule := by
  constructor
  ·
    simp [outerRule, G2nnfRuleCore.LogicalSideConditions,
      gamma, delta, closingAtom, nestedSource, universalBody, innerExistential, atom, afterOuter_eq, afterUniversal_eq, afterUniversalShown, isFreeForN, formulaFVN, termFV]
  ·
    simp [outerRule, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises,
      AllNNF, gamma, delta, closingAtom, nestedSource, universalBody, innerExistential, atom, afterOuter_eq, afterUniversal_eq, afterUniversalShown, FormulaN.isNNF, outerMaxOccurrence,
      universalMaxOccurrence, innerMaxOccurrence, MaxQuantifierOccurrence.replace,
      formulaSubstN, termSubst]
  ·
    simp [outerRule, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises,
      AllNNF, gamma, delta, closingAtom, nestedSource, universalBody, innerExistential, atom, afterOuter_eq, afterUniversal_eq, afterUniversalShown, FormulaN.isNNF, outerMaxOccurrence,
      universalMaxOccurrence, innerMaxOccurrence, MaxQuantifierOccurrence.replace,
      formulaSubstN, termSubst]
  · exact AllRectified.insert_left nestedSource_rectified
      (allRectified_singletons closingAtom_rectified closingAtom_rectified)


def universalRule : G2nnfRuleCore language :=
  .allSubLeft afterOuter universalMaxOccurrence 1
    innerExistential (.var 7) rfl gamma delta

private theorem universalRule_onePremise :
    universalRule.premises.length = 1 := rfl

private theorem universalRule_sideConditions :
    G2nnfRuleCore.SideConditions universalRule := by
  constructor
  ·
    simp [universalRule, G2nnfRuleCore.LogicalSideConditions,
      gamma, delta, closingAtom, nestedSource, universalBody, innerExistential, atom, afterOuter_eq, afterUniversal_eq, afterUniversalShown, isFreeForN, formulaFVN, termFV]
  ·
    simp [universalRule, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises,
      AllNNF, gamma, delta, closingAtom, nestedSource, universalBody, innerExistential, atom, afterOuter_eq, afterUniversal_eq, afterUniversalShown, FormulaN.isNNF, outerMaxOccurrence,
      universalMaxOccurrence, innerMaxOccurrence, MaxQuantifierOccurrence.replace,
      formulaSubstN, termSubst]
  ·
    simp [universalRule, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises,
      AllNNF, gamma, delta, closingAtom, nestedSource, universalBody, innerExistential, atom, afterOuter_eq, afterUniversal_eq, afterUniversalShown, FormulaN.isNNF, outerMaxOccurrence,
      universalMaxOccurrence, innerMaxOccurrence, MaxQuantifierOccurrence.replace,
      formulaSubstN, termSubst]
  · exact AllRectified.insert_left afterOuter_rectified
      (allRectified_singletons closingAtom_rectified closingAtom_rectified)


def innerRule : G2nnfRuleCore language :=
  .exSubLeft afterUniversal innerMaxOccurrence 2
    (.eq_ rfl (.var 7) (.var 2)) 8 rfl gamma delta

theorem innerRule_onePremise :
    innerRule.premises.length = 1 := rfl

theorem innerRule_sideConditions :
    G2nnfRuleCore.SideConditions innerRule := by
  constructor
  ·
    simp [innerRule, G2nnfRuleCore.LogicalSideConditions,
      gamma, delta, closingAtom, nestedSource, universalBody, innerExistential, atom, afterOuter_eq, afterUniversal_eq, afterUniversalShown, isFreeForN, formulaFVN, termFV]
  ·
    simp [innerRule, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises,
      AllNNF, gamma, delta, closingAtom, nestedSource, universalBody, innerExistential, atom, afterOuter_eq, afterUniversal_eq, afterUniversalShown, FormulaN.isNNF, outerMaxOccurrence,
      universalMaxOccurrence, innerMaxOccurrence, MaxQuantifierOccurrence.replace,
      formulaSubstN, termSubst]
  ·
    simp [innerRule, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises,
      AllNNF, gamma, delta, closingAtom, nestedSource, universalBody, innerExistential, atom, afterOuter_eq, afterUniversal_eq, afterUniversalShown, FormulaN.isNNF, outerMaxOccurrence,
      universalMaxOccurrence, innerMaxOccurrence, MaxQuantifierOccurrence.replace,
      formulaSubstN, termSubst]
  · exact AllRectified.insert_left afterUniversal_rectified
      (allRectified_singletons closingAtom_rectified closingAtom_rectified)

private theorem leafIndex :
    LCS.Finset.insert closingAtom
        (LCS.Finset.singleton leafFormula) =
      LCS.Finset.insert leafFormula
        (LCS.Finset.singleton closingAtom) := by
  apply LCS.Finset.ext
  intro F
  simp only [LCS.Finset.mem_insert, LCS.Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h

/-- Regression helper transporting an equality-system tree along equality of its
antecedent index. -/
def transportTreeAntecedent
    {Γ Γ' Δ : LCS.Finset (FormulaN language)}
    (h : Γ = Γ') (T : G2nnfEqProofTree rfl Γ Δ) :
    G2nnfEqProofTree rfl Γ' Δ :=
  h ▸ T

private theorem rawLeaf_sideConditions
    (hAtom : closingAtom.isAtomic = true) :
    G2nnfRuleCore.SideConditions
      (.axiomPosId closingAtom hAtom
        (LCS.Finset.singleton leafFormula) LCS.Finset.empty) := by
  constructor
  · trivial
  · simp [G2nnfRuleCore.conclusion, AllNNF, closingAtom,
      leafFormula_eq, leafAtom, FormulaN.isNNF]
    exact fun _ h => (LCS.Finset.not_mem_empty h).elim
  · simp [G2nnfRuleCore.premises]
  · apply AllRectified.insert_left closingAtom_rectified
    exact allRectified_singletons leafFormula_rectified closingAtom_rectified

def rawLeaf : G2nnfEqProofTree rfl
    (LCS.Finset.insert closingAtom
      (LCS.Finset.singleton leafFormula))
    delta :=
  .axiom_
    (.axiomPosId closingAtom
      (by simp [closingAtom, FormulaN.isAtomic])
      (LCS.Finset.singleton leafFormula) LCS.Finset.empty)
    trivial rfl
    (rawLeaf_sideConditions
      (by simp [closingAtom, FormulaN.isAtomic]))

def leaf : G2nnfEqProofTree rfl
    (LCS.Finset.insert leafFormula gamma) delta :=
  transportTreeAntecedent leafIndex rawLeaf

def innerTree : G2nnfEqProofTree rfl
    (LCS.Finset.insert afterUniversal gamma) delta :=
  .onePremise innerRule trivial innerRule_onePremise
    innerRule_sideConditions leaf

def universalTree : G2nnfEqProofTree rfl
    (LCS.Finset.insert afterOuter gamma) delta :=
  .onePremise universalRule trivial universalRule_onePremise
    universalRule_sideConditions innerTree

def tree : G2nnfEqProofTree rfl
    (LCS.Finset.insert nestedSource gamma) delta :=
  .onePremise outerRule trivial outerRule_onePremise
    outerRule_sideConditions universalTree

def outerOccurrence : G2nnfEqExSubLeftOccurrence tree where
  ambient := nestedSource
  maxOccurrence := outerMaxOccurrence
  boundVar := 0
  body := universalBody
  eigenvariable := 7
  hSelected := rfl
  gamma := gamma
  delta := delta
  hPrem := outerRule_onePremise
  hSC := outerRule_sideConditions
  premise := universalTree
  path := .root tree

def innerOccurrencePath :
    G2nnfEqProofTree.RootToNodePath tree innerTree :=
  .onePremise outerRule trivial outerRule_onePremise
    outerRule_sideConditions universalTree
    (.onePremise universalRule trivial universalRule_onePremise
      universalRule_sideConditions innerTree (.root innerTree))

def innerOccurrence : G2nnfEqExSubLeftOccurrence tree where
  ambient := afterUniversal
  maxOccurrence := innerMaxOccurrence
  boundVar := 2
  body := .eq_ rfl (.var 7) (.var 2)
  eigenvariable := 8
  hSelected := rfl
  gamma := gamma
  delta := delta
  hPrem := innerRule_onePremise
  hSC := innerRule_sideConditions
  premise := leaf
  path := innerOccurrencePath

def outerSourceAddress : FormulaOccurrenceAddress := []

def innerSourceAddress : FormulaOccurrenceAddress :=
  [.quantifierBody, .quantifierBody]

def targetAddress : FormulaOccurrenceAddress := []

theorem outerLineage_exact :
    g2nnfEqFormulaOccurrenceLineage outerOccurrence.path
      ⟨nestedSource, outerSourceAddress⟩
      ⟨nestedSource, targetAddress⟩ [] := by
  exact ⟨rfl, rfl⟩

theorem innerLineage_exact :
    g2nnfEqFormulaOccurrenceLineage innerOccurrence.path
      ⟨nestedSource, innerSourceAddress⟩
      ⟨afterUniversal, targetAddress⟩
      [(0, .var 7), (1, .var 7)] := by
  change g2nnfEqFormulaOccurrenceLineage innerOccurrencePath
    ⟨nestedSource, innerSourceAddress⟩
    ⟨afterUniversal, targetAddress⟩
    [(0, .var 7), (1, .var 7)]
  unfold innerOccurrencePath
  simp only [g2nnfEqFormulaOccurrenceLineage]
  refine ⟨⟨afterOuter, [.quantifierBody]⟩,
    some (0, .var 7), [(1, .var 7)], ?_, ?_, rfl⟩
  · unfold outerRule g2nnfFormulaOccurrenceStep
    right
    left
    refine ⟨[], [.quantifierBody], ?_, ?_, rfl, rfl, ?_, ?_,
      rfl, rfl⟩
    · simp [g2nnfLeftPremiseContext, g2nnfRuleSideContexts, gamma, nestedSource, closingAtom]
    · simp [g2nnfLeftPremiseContext, g2nnfRuleSideContexts, gamma, nestedSource, universalBody,
        innerExistential, atom, closingAtom,
        outerMaxOccurrence, MaxQuantifierOccurrence.replace,
        formulaSubstN, termSubst]
    · rfl
    · simpa [outerMaxOccurrence,
        maxQuantifierOccurrenceFormulaAddress] using
        formulaAt_maxQuantifierOccurrenceFormulaAddress
          outerMaxOccurrence
  · refine ⟨⟨afterUniversal, []⟩, some (1, .var 7), [], ?_,
      ?_, rfl⟩
    · unfold universalRule g2nnfFormulaOccurrenceStep
      right
      left
      refine ⟨[], [], ?_, ?_, rfl, rfl, ?_, ?_, rfl, rfl⟩
      · simp [g2nnfLeftPremiseContext, g2nnfRuleSideContexts, gamma, afterOuter_eq, universalBody, closingAtom]
      · simp [g2nnfLeftPremiseContext, g2nnfRuleSideContexts, gamma, afterOuter_eq, universalBody,
          innerExistential, atom, closingAtom,
          universalMaxOccurrence, MaxQuantifierOccurrence.replace,
          formulaSubstN, termSubst]
      · rfl
      · simpa [universalMaxOccurrence,
          maxQuantifierOccurrenceFormulaAddress] using
          formulaAt_maxQuantifierOccurrenceFormulaAddress
            universalMaxOccurrence
    · exact ⟨rfl, rfl⟩

private theorem outerAddressStep_rejected
    (next : FormulaOccurrenceFocus language)
    (head : Option (Nat × Term language)) :
    ¬ g2nnfFormulaOccurrenceStep outerRule .only
      ⟨nestedSource, outerSourceAddress⟩ next head := by
  simp [g2nnfFormulaOccurrenceStep, focusIsStrictContext,
    g2nnfLeftPremiseContext, g2nnfRuleSideContexts,
    g2nnfLeftPrincipal?, g2nnfLeftPremiseInserted?, outerRule,
    gamma, closingAtom, outerSourceAddress,
    outerMaxOccurrence, MaxQuantifierOccurrence.replace,
    addressAtOrBelowExactMaxQuantifier,
    maxQuantifierOccurrenceFormulaAddress,
    formulaAtOccurrenceAddress,
    nestedSource, universalBody, innerExistential, atom,
    formulaSubstN, termSubst]

theorem outerBinding_exact :
    G2nnfEqExactAllocationBinding nestedSpec outerOccurrence
      outerIndex [] := by
  unfold G2nnfEqExactAllocationBinding
  refine ⟨by simp [nestedSpec], ?_, ?_⟩
  · simp [outerOccurrence, gamma, nestedSource, closingAtom]
  refine ⟨outerSourceAddress, targetAddress, ?_, ?_,
    outerLineage_exact, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · simpa [outerOccurrence, targetAddress, outerMaxOccurrence,
      maxQuantifierOccurrenceFormulaAddress] using
      formulaAt_maxQuantifierOccurrenceFormulaAddress
        outerMaxOccurrence
  · intro j otherSourceAddress otherSubstitutions hAddress _
      hLineage
    rcases j with ⟨j, hj⟩
    change j < 2 at hj
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · rfl
    · have hOtherRev :
          innerSourceAddress = otherSourceAddress := by
        simpa [skolemOccurrenceAddress?, nestedSpec,
          existentialOccurrenceAddresses, nestedSource,
          universalBody, innerExistential, atom,
          innerSourceAddress] using hAddress
      have hOther :
          otherSourceAddress = innerSourceAddress :=
        hOtherRev.symm
      subst otherSourceAddress
      change g2nnfEqFormulaOccurrenceLineage (.root tree)
        ⟨nestedSource, innerSourceAddress⟩
        ⟨nestedSource, targetAddress⟩ otherSubstitutions at hLineage
      simp [g2nnfEqFormulaOccurrenceLineage, innerSourceAddress,
        targetAddress] at hLineage
  · decide

theorem innerBinding_exact :
    G2nnfEqExactAllocationBinding nestedSpec innerOccurrence
      innerIndex [(0, .var 7), (1, .var 7)] := by
  unfold G2nnfEqExactAllocationBinding
  refine ⟨by simp [nestedSpec], ?_, ?_⟩
  · simp [innerOccurrence, gamma, afterUniversal_eq,
      afterUniversalShown, closingAtom]
  refine ⟨innerSourceAddress, targetAddress, ?_, ?_,
    innerLineage_exact, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · simpa [innerOccurrence, targetAddress, innerMaxOccurrence,
      maxQuantifierOccurrenceFormulaAddress] using
      formulaAt_maxQuantifierOccurrenceFormulaAddress innerMaxOccurrence
  · intro j otherSourceAddress otherSubstitutions hAddress _
      hLineage
    rcases j with ⟨j, hj⟩
    change j < 2 at hj
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · have hOther :
          otherSourceAddress = outerSourceAddress := by
        simpa [skolemOccurrenceAddress?, nestedSpec,
          existentialOccurrenceAddresses, nestedSource,
          universalBody, innerExistential, atom,
          outerSourceAddress] using hAddress
      subst otherSourceAddress
      change g2nnfEqFormulaOccurrenceLineage innerOccurrencePath
        ⟨nestedSource, outerSourceAddress⟩
        ⟨afterUniversal, targetAddress⟩
        otherSubstitutions at hLineage
      unfold innerOccurrencePath at hLineage
      simp only [g2nnfEqFormulaOccurrenceLineage] at hLineage
      rcases hLineage with
        ⟨next, head, tail, hStep, _, _⟩
      exact False.elim ((outerAddressStep_rejected next head) hStep)
    · rfl
  · decide

private theorem transportedAxiomOccurrencesAux_empty
    (rule : G2nnfRuleCore language)
    (hAxiom : rule.premises.length = 0)
    (hSC : G2nnfRuleCore.SideConditions rule)
    {Γ' Γroot Δroot : LCS.Finset (FormulaN language)}
    (h : rule.conclusion.1 = Γ')
    (root : G2nnfEqProofTree rfl Γroot Δroot)
    (path : G2nnfEqProofTree.RootToNodePath root
      (transportTreeAntecedent h
        (G2nnfDeductionTreeCore.axiom_ rule trivial hAxiom hSC))) :
    g2nnfEqExSubLeftOccurrencesAux root
      (transportTreeAntecedent h
        (G2nnfDeductionTreeCore.axiom_ rule trivial hAxiom hSC))
      path = [] := by
  subst Γ'
  rfl

private theorem leafOccurrencesAux_empty
    {Γroot Δroot : LCS.Finset (FormulaN language)}
    (root : G2nnfEqProofTree rfl Γroot Δroot)
    (path : G2nnfEqProofTree.RootToNodePath root leaf) :
    g2nnfEqExSubLeftOccurrencesAux root leaf path = [] := by
  unfold leaf rawLeaf
  exact transportedAxiomOccurrencesAux_empty
    (.axiomPosId closingAtom
      (by simp [closingAtom, FormulaN.isAtomic])
      (LCS.Finset.singleton leafFormula) LCS.Finset.empty)
    rfl
    (rawLeaf_sideConditions
      (by simp [closingAtom, FormulaN.isAtomic]))
    leafIndex root path

theorem occurrences_exact :
    g2nnfEqExSubLeftOccurrences tree =
      [outerOccurrence, innerOccurrence] := by
  simp [g2nnfEqExSubLeftOccurrences,
    g2nnfEqExSubLeftOccurrencesAux, tree, universalTree, innerTree,
    leaf, rawLeaf, transportTreeAntecedent, outerRule,
    universalRule, innerRule, outerOccurrence, innerOccurrence,
    innerOccurrencePath, G2nnfEqProofTree.RootToNodePath.trans]
  constructor
  · congr 1 <;> apply proof_irrelheq
  · apply leafOccurrencesAux_empty

def outerTerm : Term nestedSpec.language :=
  g2nnfReplayedSkolemTerm nestedSpec [] outerIndex

def innerTerm : Term nestedSpec.language :=
  g2nnfReplayedSkolemTerm nestedSpec
    [(0, .var 7), (1, .var 7)] innerIndex

def rawMap : EigenvarSkolemMap nestedSpec :=
  fun y =>
    if y = 7 then some outerTerm
    else if y = 8 then some innerTerm
    else none

def outerAncestorMap : EigenvarSkolemMap nestedSpec :=
  fun y => if y = 7 then some outerTerm else none

def normalizedInnerTerm : Term nestedSpec.language :=
  applyEigenvarSkolemMapTerm nestedSpec outerAncestorMap innerTerm

def normalizedMap : EigenvarSkolemMap nestedSpec :=
  fun y =>
    if y = 7 then some outerTerm
    else if y = 8 then some normalizedInnerTerm
    else none

private theorem outerAncestors_empty :
    g2nnfEqStrictExSubLeftAncestorEigenvariables
      outerOccurrence.path = [] := by
  rfl

private theorem innerAncestors_exact :
    g2nnfEqStrictExSubLeftAncestorEigenvariables
      innerOccurrence.path = [7] := by
  rfl

private theorem occurrences_nodup :
    [outerOccurrence, innerOccurrence].Nodup := by
  simp
  intro hEq
  have hEigen := congrArg
    (fun occ : G2nnfEqExSubLeftOccurrence tree =>
      occ.eigenvariable) hEq
  simp [outerOccurrence, innerOccurrence] at hEigen

private theorem ordered_normalization :
    IsCanonicalEigenvarMapG2nnfEqOrderedAux nestedSpec normalizedMap []
      [outerOccurrence, innerOccurrence] := by
  refine ⟨?_, outerIndex, [], (fun _ => none),
    outerBinding_exact, ?_, ?_, ?_⟩
  · rw [outerAncestors_empty]
    simp
  · unfold IsG2nnfEqStrictAncestorEigenvarMap
    rw [outerAncestors_empty]
    simp
  · simp [normalizedMap, outerOccurrence, outerTerm, g2nnfEqReplayedSkolemTerm]
  · refine ⟨?_, innerIndex, [(0, .var 7), (1, .var 7)],
      outerAncestorMap, innerBinding_exact, ?_, ?_, ?_⟩
    · rw [innerAncestors_exact]
      simp [outerOccurrence]
    · unfold IsG2nnfEqStrictAncestorEigenvarMap
      rw [innerAncestors_exact]
      intro y t
      by_cases hy : y = 7 <;>
        simp [outerAncestorMap, normalizedMap, hy]
    · simp [normalizedMap, innerOccurrence, normalizedInnerTerm,
        innerTerm, g2nnfEqReplayedSkolemTerm]
    · change [8, 7].Nodup
      decide

private theorem normalizedMap_domain :
    ∀ y, (∃ t, normalizedMap y = some t) ↔ y ∈ [7, 8] := by
  intro y
  constructor
  · rintro ⟨t, ht⟩
    by_cases hy7 : y = 7
    · subst y
      simp
    · by_cases hy8 : y = 8
      · subst y
        simp
      · simp [normalizedMap, hy7, hy8] at ht
  · intro hy
    simp at hy
    rcases hy with rfl | rfl
    · exact ⟨outerTerm, by simp [normalizedMap]⟩
    · exact ⟨normalizedInnerTerm, by simp [normalizedMap]⟩

private theorem outerTerm_closed (z : Nat) :
    ¬ Membership.mem (termFV outerTerm) z := by
  have hRank : nestedSpec.skolemRank outerIndex = 0 := by decide
  simp [outerTerm, g2nnfReplayedSkolemTerm, hRank, termFV]

private theorem normalizedInnerTerm_closed (z : Nat) :
    ¬ Membership.mem (termFV normalizedInnerTerm) z := by
  simp [normalizedInnerTerm, innerTerm, outerAncestorMap,
    applyEigenvarSkolemMapTerm, g2nnfReplayedSkolemTerm,
    g2nnfReplayedSkolemArgument, nestedSpec, innerIndex,
    SkolemSpec.skolemScope,
    SkolemSpec.allocation, SkolemSpec.allocations,
    existentialDescriptors, existentialDescriptorsAux,
    universalScopeAux, nestedSource, universalBody, innerExistential,
    atom, replayQuantifierSubstitutionsTerm, termSubst,
    liftEigenvarBaseTerm, termFV]
  intro h
  rcases h with ⟨⟨j, hj⟩, hz⟩
  change j < 1 at hj
  have hj0 : j = 0 := by omega
  subst j
  change z ∈ termFV outerTerm at hz
  exact outerTerm_closed z hz

private theorem normalizedMap_range :
    EigenvarSkolemMapRangeAvoidsDomain nestedSpec normalizedMap [7, 8] := by
  intro y t hyt z _
  by_cases hy7 : y = 7
  · subst y
    simp [normalizedMap] at hyt
    subst t
    exact outerTerm_closed z
  · by_cases hy8 : y = 8
    · subst y
      simp [normalizedMap] at hyt
      subst t
      exact normalizedInnerTerm_closed z
    · simp [normalizedMap, hy7, hy8] at hyt

private theorem normalizedMap_closed :
    ∀ y t, normalizedMap y = some t →
      ∀ z, ¬ Membership.mem (termFV t) z := by
  intro y t hyt z
  by_cases hy7 : y = 7
  · subst y
    simp [normalizedMap] at hyt
    subst t
    exact outerTerm_closed z
  · by_cases hy8 : y = 8
    · subst y
      simp [normalizedMap] at hyt
      subst t
      exact normalizedInnerTerm_closed z
    · simp [normalizedMap, hy7, hy8] at hyt

private theorem term_freeFor_of_closed
    (eigenvarMap : EigenvarSkolemMap nestedSpec)
    (hClosed : ∀ y t, eigenvarMap y = some t →
      ∀ z, ¬ Membership.mem (termFV t) z)
    (bound : List Nat) (t : Term language) :
    EigenvarSkolemMapFreeForTermAt nestedSpec eigenvarMap bound t := by
  induction t with
  | var y =>
    intro mapped hMapped z _
    exact hClosed y mapped hMapped z
  | const => trivial
  | func f ts ih =>
    intro i
    exact ih i

private theorem mask_closed
    (eigenvarMap : EigenvarSkolemMap nestedSpec)
    (hClosed : ∀ y t, eigenvarMap y = some t →
      ∀ z, ¬ Membership.mem (termFV t) z)
    (x : Nat) :
    ∀ y t, maskEigenvarSkolemMap nestedSpec x eigenvarMap y = some t →
      ∀ z, ¬ Membership.mem (termFV t) z := by
  intro y t hMapped z
  unfold maskEigenvarSkolemMap at hMapped
  by_cases hyx : y = x
  · simp [hyx] at hMapped
  · simp [hyx] at hMapped
    exact hClosed y t hMapped z

private theorem formula_freeFor_of_closed
    (eigenvarMap : EigenvarSkolemMap nestedSpec)
    (hClosed : ∀ y t, eigenvarMap y = some t →
      ∀ z, ¬ Membership.mem (termFV t) z)
    (bound : List Nat) (A : FormulaN language) :
    EigenvarSkolemMapFreeForFormulaAt nestedSpec bound eigenvarMap A := by
  induction A generalizing bound eigenvarMap with
  | predN P ts =>
    intro i
    exact term_freeFor_of_closed eigenvarMap hClosed bound (ts i)
  | eq_ h t₁ t₂ =>
    exact ⟨term_freeFor_of_closed eigenvarMap hClosed bound t₁,
      term_freeFor_of_closed eigenvarMap hClosed bound t₂⟩
  | conj A B ihA ihB =>
    exact ⟨ihA eigenvarMap hClosed bound,
      ihB eigenvarMap hClosed bound⟩
  | disj A B ihA ihB =>
    exact ⟨ihA eigenvarMap hClosed bound,
      ihB eigenvarMap hClosed bound⟩
  | impl A B ihA ihB =>
    exact ⟨ihA eigenvarMap hClosed bound,
      ihB eigenvarMap hClosed bound⟩
  | neg A ih =>
    exact ih eigenvarMap hClosed bound
  | all x A ih =>
    exact ih (maskEigenvarSkolemMap nestedSpec x eigenvarMap)
      (mask_closed eigenvarMap hClosed x) (x :: bound)
  | ex x A ih =>
    exact ih (maskEigenvarSkolemMap nestedSpec x eigenvarMap)
      (mask_closed eigenvarMap hClosed x) (x :: bound)

private theorem finset_freeFor_of_closed
    (S : LCS.Finset (FormulaN language)) :
    EigenvarSkolemMapFreeForFinset nestedSpec normalizedMap S := by
  intro A _
  exact formula_freeFor_of_closed normalizedMap normalizedMap_closed [] A

private theorem anyTree_freeFor
    {Γ Δ : LCS.Finset (FormulaN language)}
    (T : G2nnfEqProofTree rfl Γ Δ) :
    EigenvarSkolemMapFreeForG2nnfEqTree nestedSpec normalizedMap T := by
  induction T with
  | leaf _ _ hOpen _ _ => exact hOpen.elim
  | extraAxiom _ _ _ _ _ =>
    exact ⟨finset_freeFor_of_closed _, finset_freeFor_of_closed _⟩
  | axiom_ rule hAdmit hAx hSC =>
    exact ⟨finset_freeFor_of_closed _, finset_freeFor_of_closed _⟩
  | onePremise rule hAdmit hPrem hSC sub ih =>
    exact ⟨finset_freeFor_of_closed _, finset_freeFor_of_closed _, ih⟩
  | twoPremise rule hAdmit hPrem hSC sub₁ sub₂ ih₁ ih₂ =>
    exact ⟨finset_freeFor_of_closed _, finset_freeFor_of_closed _,
      ih₁, ih₂⟩

private theorem tree_freeFor :
    EigenvarSkolemMapFreeForG2nnfEqTree nestedSpec normalizedMap tree :=
  anyTree_freeFor tree

theorem normalizedMap_canonical :
    IsCanonicalEigenvarMapG2nnfEq tree nestedSpec normalizedMap := by
  unfold IsCanonicalEigenvarMapG2nnfEq
  rw [occurrences_exact]
  exact ⟨occurrences_nodup,
    by simp [outerOccurrence, innerOccurrence],
    ordered_normalization, normalizedMap_domain,
    normalizedMap_range, tree_freeFor⟩

theorem rawMap_rejected :
    ¬ IsCanonicalEigenvarMapG2nnfEq tree nestedSpec rawMap := by
  intro h
  unfold IsCanonicalEigenvarMapG2nnfEq at h
  rw [occurrences_exact] at h
  have hRange := h.2.2.2.2.1
  have hAvoid :=
    hRange 8 innerTerm (by simp [rawMap]) 7
      (by simp [outerOccurrence, innerOccurrence])
  apply hAvoid
  simp [innerTerm, g2nnfReplayedSkolemTerm,
    g2nnfReplayedSkolemArgument, nestedSpec, innerIndex,
    SkolemSpec.skolemScope,
    SkolemSpec.allocation, SkolemSpec.allocations,
    existentialDescriptors, existentialDescriptorsAux,
    universalScopeAux, nestedSource, universalBody, innerExistential,
    atom, replayQuantifierSubstitutionsTerm, termSubst,
    liftEigenvarBaseTerm, termFV]
  exact ⟨(⟨0, by decide⟩ : Fin 1), rfl⟩

theorem application_fullyComposed :
    applyEigenvarSubstTerm nestedSpec normalizedMap (.var 8) =
      normalizedInnerTerm := by
  simp [applyEigenvarSubstTerm, normalizedMap]

theorem application_avoids_domain :
    ¬ Membership.mem
        (termFV
          (applyEigenvarSubstTerm nestedSpec normalizedMap (.var 8))) 7 ∧
      ¬ Membership.mem
        (termFV
          (applyEigenvarSubstTerm nestedSpec normalizedMap (.var 8))) 8 := by
  rw [application_fullyComposed]
  exact ⟨normalizedInnerTerm_closed 7, normalizedInnerTerm_closed 8⟩

/-- Regression helper transporting a G2Eq tree along equality of its
antecedent index. -/
def transportEqTreeAntecedent
    {Γ Γ' Δ : LCS.Finset (FormulaN language)}
    (h : Γ = Γ')
    (T : G2nnfEqProofTree (L := language) rfl Γ Δ) :
    G2nnfEqProofTree (L := language) rfl Γ' Δ :=
  h ▸ T

def rawLeafEq : G2nnfEqProofTree (L := language) rfl
    (LCS.Finset.insert closingAtom
      (LCS.Finset.singleton leafFormula))
    delta :=
  .axiom_
    (.axiomPosId closingAtom
      (by simp [closingAtom, FormulaN.isAtomic])
      (LCS.Finset.singleton leafFormula) LCS.Finset.empty)
    trivial rfl
    (rawLeaf_sideConditions
      (by simp [closingAtom, FormulaN.isAtomic]))

def leafEq : G2nnfEqProofTree (L := language) rfl
    (LCS.Finset.insert leafFormula gamma) delta :=
  transportEqTreeAntecedent leafIndex rawLeafEq

def innerTreeEq : G2nnfEqProofTree (L := language) rfl
    (LCS.Finset.insert afterUniversal gamma) delta :=
  .onePremise innerRule trivial innerRule_onePremise
    innerRule_sideConditions leafEq

def universalTreeEq : G2nnfEqProofTree (L := language) rfl
    (LCS.Finset.insert afterOuter gamma) delta :=
  .onePremise universalRule trivial
    universalRule_onePremise universalRule_sideConditions innerTreeEq

def treeEq : G2nnfEqProofTree (L := language) rfl
    (LCS.Finset.insert nestedSource gamma) delta :=
  .onePremise outerRule trivial outerRule_onePremise
    outerRule_sideConditions universalTreeEq

def outerOccurrenceEq : G2nnfEqExSubLeftOccurrence treeEq where
  ambient := nestedSource
  maxOccurrence := outerMaxOccurrence
  boundVar := 0
  body := universalBody
  eigenvariable := 7
  hSelected := rfl
  gamma := gamma
  delta := delta
  hPrem := outerRule_onePremise
  hSC := outerRule_sideConditions
  premise := universalTreeEq
  path := .root treeEq

def innerOccurrencePathEq :
    G2nnfEqProofTree.RootToNodePath treeEq innerTreeEq :=
  .onePremise outerRule trivial outerRule_onePremise
    outerRule_sideConditions universalTreeEq
    (.onePremise universalRule trivial
      universalRule_onePremise universalRule_sideConditions
      innerTreeEq (.root innerTreeEq))

def innerOccurrenceEq : G2nnfEqExSubLeftOccurrence treeEq where
  ambient := afterUniversal
  maxOccurrence := innerMaxOccurrence
  boundVar := 2
  body := .eq_ rfl (.var 7) (.var 2)
  eigenvariable := 8
  hSelected := rfl
  gamma := gamma
  delta := delta
  hPrem := innerRule_onePremise
  hSC := innerRule_sideConditions
  premise := leafEq
  path := innerOccurrencePathEq

private theorem outerLineageEq_exact :
    g2nnfEqFormulaOccurrenceLineage outerOccurrenceEq.path
      ⟨nestedSource, outerSourceAddress⟩
      ⟨nestedSource, targetAddress⟩ [] := by
  exact ⟨rfl, rfl⟩

private theorem innerLineageEq_exact :
    g2nnfEqFormulaOccurrenceLineage innerOccurrenceEq.path
      ⟨nestedSource, innerSourceAddress⟩
      ⟨afterUniversal, targetAddress⟩
      [(0, .var 7), (1, .var 7)] := by
  change g2nnfEqFormulaOccurrenceLineage innerOccurrencePathEq
    ⟨nestedSource, innerSourceAddress⟩
    ⟨afterUniversal, targetAddress⟩
    [(0, .var 7), (1, .var 7)]
  unfold innerOccurrencePathEq
  simp only [g2nnfEqFormulaOccurrenceLineage]
  refine ⟨⟨afterOuter, [.quantifierBody]⟩,
    some (0, .var 7), [(1, .var 7)], ?_, ?_, rfl⟩
  · unfold outerRule g2nnfFormulaOccurrenceStep
    right
    left
    refine ⟨[], [.quantifierBody], ?_, ?_, rfl, rfl, ?_, ?_,
      rfl, rfl⟩
    · simp [g2nnfLeftPremiseContext, g2nnfRuleSideContexts,
        gamma, nestedSource, closingAtom]
    · simp [g2nnfLeftPremiseContext, g2nnfRuleSideContexts,
        gamma, nestedSource, universalBody,
        innerExistential, atom, closingAtom,
        outerMaxOccurrence, MaxQuantifierOccurrence.replace,
        formulaSubstN, termSubst]
    · rfl
    · simpa [outerMaxOccurrence,
        maxQuantifierOccurrenceFormulaAddress] using
        formulaAt_maxQuantifierOccurrenceFormulaAddress
          outerMaxOccurrence
  · refine ⟨⟨afterUniversal, []⟩, some (1, .var 7), [], ?_,
      ?_, rfl⟩
    · unfold universalRule g2nnfFormulaOccurrenceStep
      right
      left
      refine ⟨[], [], ?_, ?_, rfl, rfl, ?_, ?_, rfl, rfl⟩
      · simp [g2nnfLeftPremiseContext, g2nnfRuleSideContexts,
          gamma, afterOuter_eq, universalBody, closingAtom]
      · simp [g2nnfLeftPremiseContext, g2nnfRuleSideContexts,
          gamma, afterOuter_eq, universalBody,
          innerExistential, atom, closingAtom,
          universalMaxOccurrence, MaxQuantifierOccurrence.replace,
          formulaSubstN, termSubst]
      · rfl
      · simpa [universalMaxOccurrence,
          maxQuantifierOccurrenceFormulaAddress] using
          formulaAt_maxQuantifierOccurrenceFormulaAddress
            universalMaxOccurrence
    · exact ⟨rfl, rfl⟩

private theorem outerBindingEq_exact :
    G2nnfEqExactAllocationBinding nestedSpec outerOccurrenceEq
      outerIndex [] := by
  unfold G2nnfEqExactAllocationBinding
  refine ⟨by simp [nestedSpec], ?_, ?_⟩
  · simp [outerOccurrenceEq, gamma, nestedSource, closingAtom]
  refine ⟨outerSourceAddress, targetAddress, ?_, ?_,
    outerLineageEq_exact, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · simpa [outerOccurrenceEq, targetAddress, outerMaxOccurrence,
      maxQuantifierOccurrenceFormulaAddress] using
      formulaAt_maxQuantifierOccurrenceFormulaAddress
        outerMaxOccurrence
  · intro j otherSourceAddress otherSubstitutions hAddress _
      hLineage
    rcases j with ⟨j, hj⟩
    change j < 2 at hj
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · rfl
    · have hOtherRev :
          innerSourceAddress = otherSourceAddress := by
        simpa [skolemOccurrenceAddress?, nestedSpec,
          existentialOccurrenceAddresses, nestedSource,
          universalBody, innerExistential, atom,
          innerSourceAddress] using hAddress
      have hOther :
          otherSourceAddress = innerSourceAddress :=
        hOtherRev.symm
      subst otherSourceAddress
      change g2nnfEqFormulaOccurrenceLineage (.root treeEq)
        ⟨nestedSource, innerSourceAddress⟩
        ⟨nestedSource, targetAddress⟩ otherSubstitutions at hLineage
      simp [g2nnfEqFormulaOccurrenceLineage, innerSourceAddress,
        targetAddress] at hLineage
  · decide

private theorem innerBindingEq_exact :
    G2nnfEqExactAllocationBinding nestedSpec innerOccurrenceEq
      innerIndex [(0, .var 7), (1, .var 7)] := by
  unfold G2nnfEqExactAllocationBinding
  refine ⟨by simp [nestedSpec], ?_, ?_⟩
  · simp [innerOccurrenceEq, gamma, afterUniversal_eq,
      afterUniversalShown, closingAtom]
  refine ⟨innerSourceAddress, targetAddress, ?_, ?_,
    innerLineageEq_exact, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · simpa [innerOccurrenceEq, targetAddress, innerMaxOccurrence,
      maxQuantifierOccurrenceFormulaAddress] using
      formulaAt_maxQuantifierOccurrenceFormulaAddress innerMaxOccurrence
  · intro j otherSourceAddress otherSubstitutions hAddress _
      hLineage
    rcases j with ⟨j, hj⟩
    change j < 2 at hj
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · have hOther :
          otherSourceAddress = outerSourceAddress := by
        simpa [skolemOccurrenceAddress?, nestedSpec,
          existentialOccurrenceAddresses, nestedSource,
          universalBody, innerExistential, atom,
          outerSourceAddress] using hAddress
      subst otherSourceAddress
      change g2nnfEqFormulaOccurrenceLineage innerOccurrencePathEq
        ⟨nestedSource, outerSourceAddress⟩
        ⟨afterUniversal, targetAddress⟩
        otherSubstitutions at hLineage
      unfold innerOccurrencePathEq at hLineage
      simp only [g2nnfEqFormulaOccurrenceLineage] at hLineage
      rcases hLineage with
        ⟨next, head, tail, hStep, _, _⟩
      exact False.elim ((outerAddressStep_rejected next head) hStep)
    · rfl
  · decide

private theorem transportedEqAxiomOccurrencesAux_empty
    (rule : G2nnfRuleCore language)
    (hAxiom : rule.premises.length = 0)
    (hSC : G2nnfRuleCore.SideConditions rule)
    {Γ' Γroot Δroot : LCS.Finset (FormulaN language)}
    (h : rule.conclusion.1 = Γ')
    (root : G2nnfEqProofTree (L := language) rfl Γroot Δroot)
    (path : G2nnfEqProofTree.RootToNodePath root
      (transportEqTreeAntecedent h
        (G2nnfDeductionTreeCore.axiom_ rule trivial hAxiom hSC))) :
    g2nnfEqExSubLeftOccurrencesAux root
      (transportEqTreeAntecedent h
        (G2nnfDeductionTreeCore.axiom_ rule trivial hAxiom hSC))
      path = [] := by
  subst Γ'
  rfl

private theorem leafEqOccurrencesAux_empty
    {Γroot Δroot : LCS.Finset (FormulaN language)}
    (root : G2nnfEqProofTree (L := language) rfl Γroot Δroot)
    (path : G2nnfEqProofTree.RootToNodePath root leafEq) :
    g2nnfEqExSubLeftOccurrencesAux root leafEq path = [] := by
  unfold leafEq rawLeafEq
  exact transportedEqAxiomOccurrencesAux_empty
    (.axiomPosId closingAtom
      (by simp [closingAtom, FormulaN.isAtomic])
      (LCS.Finset.singleton leafFormula) LCS.Finset.empty)
    rfl
    (rawLeaf_sideConditions
      (by simp [closingAtom, FormulaN.isAtomic]))
    leafIndex root path

private theorem occurrencesEq_exact :
    g2nnfEqExSubLeftOccurrences treeEq =
      [outerOccurrenceEq, innerOccurrenceEq] := by
  simp [g2nnfEqExSubLeftOccurrences,
    g2nnfEqExSubLeftOccurrencesAux, treeEq, universalTreeEq,
    innerTreeEq, leafEq, rawLeafEq, transportEqTreeAntecedent,
    outerRule, universalRule, innerRule, outerOccurrenceEq,
    innerOccurrenceEq, innerOccurrencePathEq,
    G2nnfEqProofTree.RootToNodePath.trans]
  constructor
  · congr 1 <;> apply proof_irrelheq
  · apply leafEqOccurrencesAux_empty

private theorem outerAncestorsEq_empty :
    g2nnfEqStrictExSubLeftAncestorEigenvariables
      outerOccurrenceEq.path = [] := by
  rfl

private theorem innerAncestorsEq_exact :
    g2nnfEqStrictExSubLeftAncestorEigenvariables
      innerOccurrenceEq.path = [7] := by
  rfl

private theorem occurrencesEq_nodup :
    [outerOccurrenceEq, innerOccurrenceEq].Nodup := by
  simp
  intro hEq
  have hEigen := congrArg
    (fun occ : G2nnfEqExSubLeftOccurrence treeEq =>
      occ.eigenvariable) hEq
  simp [outerOccurrenceEq, innerOccurrenceEq] at hEigen

private theorem orderedEq_normalization :
    IsCanonicalEigenvarMapG2nnfEqOrderedAux nestedSpec
      normalizedMap [] [outerOccurrenceEq, innerOccurrenceEq] := by
  change _ ∧ ∃ i substitutions ancestorMap, _
  refine ⟨?_, outerIndex, [], (fun _ => none),
    outerBindingEq_exact, ?_, ?_, ?_⟩
  · rw [outerAncestorsEq_empty]
    simp
  · unfold IsG2nnfEqStrictAncestorEigenvarMap
    rw [outerAncestorsEq_empty]
    simp
  · simp [normalizedMap, outerOccurrenceEq, outerTerm,
      g2nnfEqReplayedSkolemTerm]
  · refine ⟨?_, innerIndex, [(0, .var 7), (1, .var 7)],
      outerAncestorMap, innerBindingEq_exact, ?_, ?_, ?_⟩
    · rw [innerAncestorsEq_exact]
      simp [outerOccurrenceEq]
    · unfold IsG2nnfEqStrictAncestorEigenvarMap
      rw [innerAncestorsEq_exact]
      intro y t
      by_cases hy : y = 7 <;>
        simp [outerAncestorMap, normalizedMap, hy]
    · simp [normalizedMap, innerOccurrenceEq, normalizedInnerTerm,
        innerTerm, g2nnfEqReplayedSkolemTerm]
    · change [8, 7].Nodup
      decide

private theorem anyEqTree_freeFor
    {Γ Δ : LCS.Finset (FormulaN language)}
    (T : G2nnfEqProofTree (L := language) rfl Γ Δ) :
    EigenvarSkolemMapFreeForG2nnfEqTree
      nestedSpec normalizedMap T := by
  induction T with
  | leaf _ _ hOpen _ _ => exact hOpen.elim
  | extraAxiom _ _ _ _ _ =>
    exact ⟨finset_freeFor_of_closed _, finset_freeFor_of_closed _⟩
  | axiom_ rule hAdmit hAx hSC =>
    exact ⟨finset_freeFor_of_closed _, finset_freeFor_of_closed _⟩
  | onePremise rule hAdmit hPrem hSC sub ih =>
    exact ⟨finset_freeFor_of_closed _, finset_freeFor_of_closed _, ih⟩
  | twoPremise rule hAdmit hPrem hSC sub₁ sub₂ ih₁ ih₂ =>
    exact ⟨finset_freeFor_of_closed _, finset_freeFor_of_closed _,
      ih₁, ih₂⟩

private theorem treeEq_freeFor :
    EigenvarSkolemMapFreeForG2nnfEqTree
      nestedSpec normalizedMap treeEq :=
  anyEqTree_freeFor treeEq

theorem normalizedMapEq_canonical :
    IsCanonicalEigenvarMapG2nnfEq treeEq nestedSpec normalizedMap := by
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  rw [occurrencesEq_exact]
  exact ⟨occurrencesEq_nodup,
    by simp [outerOccurrenceEq, innerOccurrenceEq],
    orderedEq_normalization, normalizedMap_domain,
    normalizedMap_range, treeEq_freeFor⟩

theorem rawMapEq_rejected :
    ¬ IsCanonicalEigenvarMapG2nnfEq treeEq nestedSpec rawMap := by
  intro h
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at h
  rw [occurrencesEq_exact] at h
  have hRange := h.2.2.2.2.1
  have hAvoid :=
    hRange 8 innerTerm (by simp [rawMap]) 7
      (by simp [outerOccurrenceEq, innerOccurrenceEq])
  apply hAvoid
  simp [innerTerm, g2nnfReplayedSkolemTerm,
    g2nnfReplayedSkolemArgument, nestedSpec, innerIndex,
    SkolemSpec.skolemScope,
    SkolemSpec.allocation, SkolemSpec.allocations,
    existentialDescriptors, existentialDescriptorsAux,
    universalScopeAux, nestedSource, universalBody, innerExistential,
    atom, replayQuantifierSubstitutionsTerm, termSubst,
    liftEigenvarBaseTerm, termFV]
  exact ⟨(⟨0, by decide⟩ : Fin 1), rfl⟩

end
end NestedCanonicalMapRegression
end LCS.Herbrand.SHGTheorem.Herbrand
end

