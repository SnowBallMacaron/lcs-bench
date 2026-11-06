import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.SequentEncodings
import LCS.Herbrand.SHGTheorem.Herbrand.CanonicalEigenvarMap

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
namespace CanonicalEigenvarMapRegression
noncomputable section

inductive Func : Type where
  | g
  deriving DecidableEq

/-- Equality atoms expose both scope variables, while the unary base
function `g` provides an adversarial non-Skolem head. -/
def language : Language where
  funSymbols := Func
  funArity := fun | .g => 1
  constSymbols := Empty
  predSymbols := Empty
  predArity := Empty.elim
  hasEquality := true

def allocatedBody : FormulaN language :=
  .eq_ rfl (.var 0) (.var 2)

def allocatedExistential : FormulaN language :=
  .ex 1 allocatedBody

def innerUniversalBody : FormulaN language :=
  allocatedExistential

def outerUniversalBody : FormulaN language :=
  .all 2 innerUniversalBody

def source : FormulaN language :=
  .all 0 outerUniversalBody

/-- Result after replaying the outer `0 ↦ 9` substitution. -/
def afterOuterSubstitution : FormulaN language :=
  .all 2 (.ex 1 (.eq_ rfl (.var 9) (.var 2)))

/-- Exact existential formula at the proof occurrence after replaying
both outer substitutions `0 ↦ 9` and `2 ↦ 8`. -/
def proofExistential : FormulaN language :=
  .ex 1 (.eq_ rfl (.var 9) (.var 8))

def proofAtom : FormulaN language :=
  .eq_ rfl (.var 9) (.var 8)

private theorem source_rectified :
    LCS.FirstOrder.Semantics.Subformulae.isRectified source := by
  simp [source, outerUniversalBody, innerUniversalBody,
    allocatedExistential, allocatedBody,
    LCS.FirstOrder.Semantics.Subformulae.isRectified,
    LCS.FirstOrder.Semantics.Subformulae.boundVarsFresh,
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
    formulaFVN, formulaBVN, termFV]

/-- The ambient formula produced by replacing the root occurrence in the
outer rule. -/
def innerAmbient : FormulaN language :=
  formulaSubstN outerUniversalBody (.var 9) 0

def innerRuleBody : FormulaN language :=
  .ex 1 (.eq_ rfl (.var 9) (.var 2))

/-- The ambient formula produced by replacing the root occurrence in the
inner universal rule. -/
def exAmbient : FormulaN language :=
  formulaSubstN innerRuleBody (.var 8) 2

/-- The premise formula produced by replacing the root occurrence in the
target existential rule. -/
def leafFormula : FormulaN language :=
  formulaSubstN proofAtom (.var 7) 1

private theorem innerAmbient_eq :
    innerAmbient = afterOuterSubstitution := by
  simp [innerAmbient, source, outerUniversalBody, innerUniversalBody,
    allocatedExistential, allocatedBody, afterOuterSubstitution,
    formulaSubstN, termSubst]

private theorem exAmbient_eq :
    exAmbient = proofExistential := by
  simp [afterOuterSubstitution, innerRuleBody, proofExistential,
    exAmbient, formulaSubstN, termSubst]

theorem leafFormula_eq :
    leafFormula = proofAtom := by
  simp [leafFormula, proofExistential, proofAtom,
    formulaSubstN, termSubst]

private theorem proofAtom_rectified :
    isRectified proofAtom :=
  AllRectified.isRectified_of_isQuantifierFree proofAtom (by
    simp [proofAtom, isQuantifierFree])

theorem leafFormula_rectified :
    isRectified leafFormula := by
  rw [leafFormula_eq]
  exact proofAtom_rectified

private theorem exAmbient_rectified :
    isRectified exAmbient := by
  rw [exAmbient_eq]
  simp [proofExistential, proofAtom, isRectified, boundVarsFresh,
    distinctQuantifierBindings, formulaFVN, formulaBVN, termFV]

private theorem innerAmbient_rectified :
    isRectified innerAmbient := by
  rw [innerAmbient_eq]
  simp [afterOuterSubstitution, isRectified, boundVarsFresh,
    distinctQuantifierBindings, formulaFVN, formulaBVN, termFV]

def outerMaxOccurrence : MaxQuantifierOccurrence source :=
  .all 0 outerUniversalBody

def innerMaxOccurrence : MaxQuantifierOccurrence innerAmbient :=
  .all 2 innerRuleBody

def exMaxOccurrence : MaxQuantifierOccurrence exAmbient :=
  .ex 1 proofAtom

def delta : LCS.Finset (FormulaN language) :=
  LCS.Finset.singleton leafFormula

def exRule : G2nnfRuleCore language :=
  .exSubLeft exAmbient exMaxOccurrence 1 proofAtom 7 rfl LCS.Finset.empty delta

theorem exRule_onePremise :
    exRule.premises.length = 1 := rfl

theorem exRule_sideConditions :
    G2nnfRuleCore.SideConditions exRule := by
  constructor
  · simp [exRule, G2nnfRuleCore.LogicalSideConditions, proofAtom,
      isFreeForN, exAmbient_eq, proofExistential, delta, leafFormula_eq,
      formulaFVN, termFV]
    exact fun _ h => (LCS.Finset.not_mem_empty h).elim
  · simp [exRule, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises,
      AllNNF, delta, leafFormula_eq, proofAtom, exAmbient_eq, proofExistential, exMaxOccurrence,
      FormulaN.isNNF, MaxQuantifierOccurrence.replace, formulaSubstN,
      termSubst]
    exact fun _ h => (LCS.Finset.not_mem_empty h).elim
  · simp [exRule, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises,
      AllNNF, delta, leafFormula_eq, proofAtom, exAmbient_eq, proofExistential, exMaxOccurrence,
      FormulaN.isNNF, MaxQuantifierOccurrence.replace, formulaSubstN,
      termSubst]
    exact fun _ h => (LCS.Finset.not_mem_empty h).elim
  · exact AllRectified.insert_left exAmbient_rectified
      (AllRectified.insert_right leafFormula_rectified AllRectified.empty)

def leaf : G2nnfEqProofTree rfl
    (LCS.Finset.singleton leafFormula)
    (LCS.Finset.singleton leafFormula) :=
  .axiom_
    (.axiomPosId leafFormula
      (by rw [leafFormula_eq]; simp [proofAtom, FormulaN.isAtomic])
      LCS.Finset.empty LCS.Finset.empty)
    trivial rfl
    { logical := trivial
      conclusionNNF := by
        simp [G2nnfRuleCore.conclusion, AllNNF, LCS.Finset.mem_insert,
          leafFormula_eq, proofAtom, FormulaN.isNNF]
        exact fun _ h => (LCS.Finset.not_mem_empty h).elim
      premisesNNF := by simp [G2nnfRuleCore.premises]
      conclusionRectified :=
        AllRectified.insert_left leafFormula_rectified
          (AllRectified.insert_right leafFormula_rectified AllRectified.empty) }

def exTree : G2nnfEqProofTree rfl
    (LCS.Finset.singleton exAmbient) delta :=
  .onePremise exRule trivial exRule_onePremise
    exRule_sideConditions leaf

def innerRule : G2nnfRuleCore language :=
  .allSubLeft innerAmbient innerMaxOccurrence 2
    innerRuleBody (.var 8) rfl LCS.Finset.empty delta

theorem innerRule_onePremise :
    innerRule.premises.length = 1 := rfl

theorem innerRule_sideConditions :
    G2nnfRuleCore.SideConditions innerRule := by
  constructor
  ·
    change (2 = 1) ∨ ((1 ≠ 8) ∧ True)
    simp
  · simp [innerRule, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises,
      AllNNF, delta, leafFormula_eq, proofAtom, innerAmbient_eq, afterOuterSubstitution, innerMaxOccurrence, innerRuleBody,
      FormulaN.isNNF, MaxQuantifierOccurrence.replace, formulaSubstN,
      termSubst]
    exact fun _ h => (LCS.Finset.not_mem_empty h).elim
  · simp [innerRule, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises,
      AllNNF, delta, leafFormula_eq, proofAtom, innerAmbient_eq, afterOuterSubstitution, innerMaxOccurrence, innerRuleBody,
      FormulaN.isNNF, MaxQuantifierOccurrence.replace, formulaSubstN,
      termSubst]
    exact fun _ h => (LCS.Finset.not_mem_empty h).elim
  · exact AllRectified.insert_left innerAmbient_rectified
      (AllRectified.insert_right leafFormula_rectified AllRectified.empty)

def innerTree : G2nnfEqProofTree rfl
    (LCS.Finset.singleton innerAmbient) delta :=
  .onePremise innerRule trivial innerRule_onePremise
    innerRule_sideConditions exTree

def outerRule : G2nnfRuleCore language :=
  .allSubLeft source outerMaxOccurrence 0 outerUniversalBody (.var 9) rfl LCS.Finset.empty delta

theorem outerRule_onePremise :
    outerRule.premises.length = 1 := rfl

theorem outerRule_sideConditions :
    G2nnfRuleCore.SideConditions outerRule := by
  constructor
  ·
    change (0 = 2) ∨ ((2 ≠ 9) ∧ ((0 = 1) ∨ ((1 ≠ 9) ∧ True)))
    simp
  · simp [outerRule, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises,
      AllNNF, delta, leafFormula_eq, proofAtom, source, outerUniversalBody, innerUniversalBody, allocatedExistential, allocatedBody, outerMaxOccurrence,
      FormulaN.isNNF, MaxQuantifierOccurrence.replace, formulaSubstN,
      termSubst]
    exact fun _ h => (LCS.Finset.not_mem_empty h).elim
  · simp [outerRule, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises,
      AllNNF, delta, leafFormula_eq, proofAtom, source, outerUniversalBody, innerUniversalBody, allocatedExistential, allocatedBody, outerMaxOccurrence,
      FormulaN.isNNF, MaxQuantifierOccurrence.replace, formulaSubstN,
      termSubst]
    exact fun _ h => (LCS.Finset.not_mem_empty h).elim
  · exact AllRectified.insert_left source_rectified
      (AllRectified.insert_right leafFormula_rectified AllRectified.empty)

-- Separately named equality witnesses for the same Core proof skeleton.

-- Permanent adversarial regression: all rules are quantifier rules
-- and `spec.source` is retained in every antecedent context, but the
-- transformed principal is unrelated. The former path-wide replay
-- accepted its substitution solely because it shared bound-variable
-- number `0` with the source allocation.

end
end CanonicalEigenvarMapRegression
end LCS.Herbrand.SHGTheorem.Herbrand
end
