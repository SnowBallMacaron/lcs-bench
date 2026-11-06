import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
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

theorem nestedSource_rectified :
    LCS.FirstOrder.Semantics.Subformulae.isRectified nestedSource := by
  simp [nestedSource, universalBody, innerExistential, atom,
    LCS.FirstOrder.Semantics.Subformulae.isRectified,
    LCS.FirstOrder.Semantics.Subformulae.boundVarsFresh,
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
    formulaFVN, formulaBVN, termFV]

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

theorem afterOuter_eq :
    afterOuter = universalBody := by
  simp [afterOuter, nestedSource, universalBody, innerExistential,
    atom, formulaSubstN, termSubst]

theorem afterUniversal_eq :
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

theorem afterOuter_rectified :
    isRectified afterOuter := by
  rw [afterOuter_eq]
  simp [universalBody, innerExistential, atom, isRectified,
    boundVarsFresh, distinctQuantifierBindings, formulaFVN, formulaBVN,
    termFV]

theorem afterUniversal_rectified :
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

theorem closingAtom_rectified :
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

theorem universalRule_onePremise :
    universalRule.premises.length = 1 := rfl

theorem universalRule_sideConditions :
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

theorem leafIndex :
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

theorem rawLeaf_sideConditions
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

end
end NestedCanonicalMapRegression
end LCS.Herbrand.SHGTheorem.Herbrand
end
