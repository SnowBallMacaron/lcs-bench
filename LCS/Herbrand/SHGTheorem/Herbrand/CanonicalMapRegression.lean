import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.SyntaxAllocation
import LCS.Herbrand.SHGTheorem.Herbrand.OccurrenceLineage

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

/-- Replay is deliberately polarity-neutral and covers all four
quantifier-for-subformulae rules. -/
theorem allFourQuantifierRulesReplay {L : Language}
    (B : FormulaN L) (x y : Nat) (t : Term L)
    (Gamma Delta : LCS.Finset (FormulaN L)) :
    quantifierRuleSubstitution?
        (.allSubLeft (.all x B) (.all x B) x B t rfl Gamma Delta) =
        some (x, t) ∧
    quantifierRuleSubstitution?
        (.allSubRight (.all x B) (.all x B) x B y rfl Gamma Delta) =
        some (x, .var y) ∧
    quantifierRuleSubstitution?
        (.exSubLeft (.ex x B) (.ex x B) x B y rfl Gamma Delta) =
        some (x, .var y) ∧
    quantifierRuleSubstitution?
        (.exSubRight (.ex x B) (.ex x B) x B t rfl Gamma Delta) =
        some (x, t) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The equality replay surface mirrors the base G2nnf rules exactly. -/
theorem allFourQuantifierRulesReplayEq {L : Language}
    {hL : L.hasEquality = true}
    (B : FormulaN L) (x y : Nat) (t : Term L)
    (Gamma Delta : LCS.Finset (FormulaN L)) :
    quantifierEqRuleSubstitution?
        (hL := hL)
        (.base (.allSubLeft (.all x B) (.all x B) x B t rfl Gamma Delta)) =
        some (x, t) ∧
    quantifierEqRuleSubstitution?
        (hL := hL)
        (.base (.allSubRight (.all x B) (.all x B) x B y rfl Gamma Delta)) =
        some (x, .var y) ∧
    quantifierEqRuleSubstitution?
        (hL := hL)
        (.base (.exSubLeft (.ex x B) (.ex x B) x B y rfl Gamma Delta)) =
        some (x, .var y) ∧
    quantifierEqRuleSubstitution?
        (hL := hL)
        (.base (.exSubRight (.ex x B) (.ex x B) x B t rfl Gamma Delta)) =
        some (x, t) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

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

def spec : SkolemSpec language where
  source := source
  hNNF := by
    simp [source, outerUniversalBody, innerUniversalBody,
      allocatedExistential, allocatedBody, FormulaN.isNNF]
  hRect := source_rectified
  hSentence := by
    unfold FormulaN.isClosed
    funext x
    apply propext
    change
      ((((x = 0 ∨ x = 2) ∧ x ≠ 1) ∧ x ≠ 2) ∧ x ≠ 0) ↔ False
    constructor
    · rintro ⟨⟨⟨hx, _⟩, hx2⟩, hx0⟩
      rcases hx with h0 | h2
      · exact hx0 h0
      · exact hx2 h2
    · exact False.elim

def index : Fin spec.n := ⟨0, by decide⟩

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

def outerTree : G2nnfEqProofTree rfl
    (LCS.Finset.singleton source) delta :=
  .onePremise outerRule trivial outerRule_onePremise
    outerRule_sideConditions innerTree

def occurrencePath :
    G2nnfEqProofTree.RootToNodePath outerTree exTree :=
  .onePremise outerRule trivial outerRule_onePremise
    outerRule_sideConditions innerTree
    (.onePremise innerRule trivial innerRule_onePremise
      innerRule_sideConditions exTree (.root exTree))

def occurrence : G2nnfEqExSubLeftOccurrence outerTree where
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
  path := occurrencePath

/-- The enumerator preserves the exact nested premise path. -/
theorem occurrences_exact :
    g2nnfEqExSubLeftOccurrences outerTree = [occurrence] := by
  simp [g2nnfEqExSubLeftOccurrences, g2nnfEqExSubLeftOccurrencesAux,
    outerTree, innerTree, exTree, leaf, outerRule, innerRule, exRule,
    occurrence, occurrencePath,
    G2nnfEqProofTree.RootToNodePath.trans]
  rfl

/-- Direct allocation equality is too strict after outer
substitution: the source cell still contains variables `0,2`, whereas
the proof occurrence contains the replayed variables `9,8`. -/
theorem directAllocationEquality_rejected :
    (spec.allocation index).1 ≠ proofExistential := by
  simp [spec, index, SkolemSpec.allocation, SkolemSpec.allocations,
    existentialDescriptors, existentialDescriptorsAux,
    universalScopeAux, source, outerUniversalBody, innerUniversalBody,
    allocatedExistential, allocatedBody, proofExistential]
  intro h
  cases h

/-- Replaying the exact source allocation along the occurrence path
does produce the proof occurrence. -/
theorem outerSubstitutionReplay_exact :
    replayG2nnfEqPathFormula occurrence.path
      (spec.allocation index).1 = proofExistential := by
  simp [occurrence, occurrencePath, replayG2nnfEqPathFormula,
    g2nnfEqPathQuantifierSubstitutions,
    replayQuantifierSubstitutionsFormula,
    quantifierRuleSubstitution?, outerRule, innerRule, spec, index,
    SkolemSpec.allocation, SkolemSpec.allocations, existentialDescriptors,
    existentialDescriptorsAux, universalScopeAux, source,
    outerUniversalBody, innerUniversalBody, allocatedExistential,
    allocatedBody, proofExistential, formulaSubstN, termSubst]
  rfl

def sourceAllocationAddress : FormulaOccurrenceAddress :=
  [.quantifierBody, .quantifierBody]

def targetAllocationAddress : FormulaOccurrenceAddress := []

theorem occurrence_lineage_exact :
    g2nnfEqFormulaOccurrenceLineage occurrence.path
      ⟨source, sourceAllocationAddress⟩
      ⟨exAmbient, targetAllocationAddress⟩
      [(0, .var 9), (2, .var 8)] := by
  change g2nnfEqFormulaOccurrenceLineage occurrencePath
    ⟨source, sourceAllocationAddress⟩
    ⟨exAmbient, targetAllocationAddress⟩
    [(0, .var 9), (2, .var 8)]
  unfold occurrencePath
  simp only [g2nnfEqFormulaOccurrenceLineage]
  refine ⟨⟨innerAmbient, [.quantifierBody]⟩,
    some (0, .var 9), [(2, .var 8)], ?_, ?_, rfl⟩
  · unfold outerRule g2nnfFormulaOccurrenceStep
    right
    left
    refine ⟨[], [.quantifierBody], LCS.Finset.not_mem_empty,
      LCS.Finset.not_mem_empty, rfl, ?_, rfl,
      ?_, rfl, rfl⟩
    · rfl
    · simpa [outerMaxOccurrence,
        maxQuantifierOccurrenceFormulaAddress] using
        formulaAt_maxQuantifierOccurrenceFormulaAddress
          outerMaxOccurrence
  · refine ⟨⟨exAmbient, []⟩, some (2, .var 8), [], ?_, ?_, rfl⟩
    · unfold innerRule g2nnfFormulaOccurrenceStep
      right
      left
      refine ⟨[], [], LCS.Finset.not_mem_empty,
        LCS.Finset.not_mem_empty, rfl, rfl, ?_, ?_, rfl, rfl⟩
      · rfl
      · simpa [innerMaxOccurrence,
          maxQuantifierOccurrenceFormulaAddress] using
          formulaAt_maxQuantifierOccurrenceFormulaAddress
            innerMaxOccurrence
    · exact ⟨rfl, rfl⟩

theorem occurrence_exactBinding :
    G2nnfEqExactAllocationBinding spec occurrence index
      [(0, .var 9), (2, .var 8)] := by
  unfold G2nnfEqExactAllocationBinding
  refine ⟨by simp [spec], ?_, ?_⟩
  · exact LCS.Finset.not_mem_empty
  refine ⟨sourceAllocationAddress, targetAllocationAddress, ?_, ?_,
    occurrence_lineage_exact, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · simpa [occurrence, targetAllocationAddress, exMaxOccurrence,
      maxQuantifierOccurrenceFormulaAddress] using
      formulaAt_maxQuantifierOccurrenceFormulaAddress exMaxOccurrence
  · intro j _ _ _ _ _
    apply Fin.eq_of_val_eq
    have hj := j.isLt
    change j.val < 1 at hj
    change j.val = 0
    omega
  · decide

def exactTerm : Term spec.language :=
  g2nnfReplayedSkolemTerm spec
    [(0, .var 9), (2, .var 8)] index

def legalMap : EigenvarSkolemMap spec :=
  fun y => if y = 7 then some exactTerm else none

private theorem occurrence_strictAncestors_empty :
    g2nnfEqStrictExSubLeftAncestorEigenvariables occurrence.path = [] := by
  rfl

private theorem exactTerm_not_free_seven :
    ¬ Membership.mem (termFV exactTerm) 7 := by
  simp [exactTerm, g2nnfReplayedSkolemTerm,
    g2nnfReplayedSkolemArgument, spec, index,
    SkolemSpec.skolemRank, SkolemSpec.skolemScope,
    SkolemSpec.allocation, SkolemSpec.allocations,
    existentialDescriptors, existentialDescriptorsAux,
    universalScopeAux, source, outerUniversalBody, innerUniversalBody,
    allocatedExistential, allocatedBody,
    replayQuantifierSubstitutionsTerm, termSubst,
    liftEigenvarBaseTerm, termFV]
  intro h
  rcases h with ⟨j, hj⟩
  rcases j with ⟨j, hjlt⟩
  change j < 2 at hjlt
  have hjCases : j = 0 ∨ j = 1 := by omega
  rcases hjCases with rfl | rfl <;>
    simp at hj <;> cases hj

/-- At least one complete legal case is accepted: the only map cell
is the exact fresh function for `index` with the two ordered
path-derived arguments. -/
theorem legalExactAllocatedSymbol_accepted :
    IsCanonicalEigenvarMapG2nnfEq outerTree spec legalMap := by
  unfold IsCanonicalEigenvarMapG2nnfEq
  rw [occurrences_exact]
  refine ⟨by simp, by simp [occurrence], ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, index, [(0, .var 9), (2, .var 8)],
      (fun _ => none), occurrence_exactBinding, ?_, ?_, ?_⟩
    · rw [occurrence_strictAncestors_empty]
      simp
    · unfold IsG2nnfEqStrictAncestorEigenvarMap
      rw [occurrence_strictAncestors_empty]
      simp
    · simp [legalMap, exactTerm, occurrence, g2nnfEqReplayedSkolemTerm]
    · change [7].Nodup
      decide
  · intro y
    constructor
    · rintro ⟨t, ht⟩
      by_cases hy : y = 7
      · subst y
        simp [occurrence]
      · simp [legalMap, hy] at ht
    · intro hy
      have : y = 7 := by simpa [occurrence] using hy
      subst y
      exact ⟨exactTerm, by simp [legalMap]⟩
  · intro y t hyt z hz
    have hz7 : z = 7 := by simpa [occurrence] using hz
    subst z
    by_cases hy : y = 7
    · subst y
      simp [legalMap] at hyt
      subst t
      exact exactTerm_not_free_seven
    · simp [legalMap, hy] at hyt
  · simp [EigenvarSkolemMapFreeForG2nnfEqTree,
      EigenvarSkolemMapFreeForFinset,
      EigenvarSkolemMapFreeForFormula,
      EigenvarSkolemMapFreeForFormulaAt,
      EigenvarSkolemMapFreeForTermAt, outerTree, innerTree, exTree,
      leaf, outerRule, innerRule, exRule, G2nnfRuleCore.conclusion, legalMap,
      maskEigenvarSkolemMap, formulaAtOccurrenceAddress,
      source, outerUniversalBody, innerUniversalBody,
      allocatedExistential, allocatedBody, innerAmbient,
      afterOuterSubstitution, innerRuleBody, exAmbient,
      proofExistential, proofAtom, leafFormula, delta,
      outerMaxOccurrence, innerMaxOccurrence, exMaxOccurrence,
      MaxQuantifierOccurrence.replace, formulaSubstN, termSubst, termFV]
    intro A hA
    exact (LCS.Finset.not_mem_empty hA).elim

/-- A base-language function head is rejected: the exact term head is
the fresh allocated function, distinct from a caller-selected `Sum.inl g`. -/
def arbitraryBaseHeadTerm : Term spec.language :=
  .func (Sum.inl .g) (fun _ => .var 9)

def termFunctionHead? {L : Language} :
    Term L → Option L.funSymbols
  | .func f _ => some f
  | _ => none

theorem arbitraryBaseFunctionHead_rejected :
    arbitraryBaseHeadTerm ≠ exactTerm := by
  intro h
  have hHead := congrArg termFunctionHead? h
  change some (Sum.inl Func.g : spec.language.funSymbols) =
    some (Sum.inr ⟨index, by decide⟩) at hHead
  cases Option.some.inj hHead

/-- Distinct allocation indices always give distinct exact terms, whether
their ranks select constants or functions, independently of argument syntax. -/
theorem wrongAllocationIndex_rejected {L : Language}
    (S : SkolemSpec L)
    (substitutions : List (Nat × Term L))
    (i j : Fin S.n) (hij : i ≠ j) :
    g2nnfReplayedSkolemTerm S substitutions i ≠
      g2nnfReplayedSkolemTerm S substitutions j := by
  intro h
  unfold g2nnfReplayedSkolemTerm at h
  split at h <;> split at h
  · have hIndex := congrArg Subtype.val (Sum.inr.inj (Term.const.inj h))
    exact hij hIndex
  · cases h
  · cases h
  · have hHead := congrArg termFunctionHead? h
    simp only [termFunctionHead?] at hHead
    exact hij (congrArg Subtype.val (Sum.inr.inj (Option.some.inj hHead)))

def wrongOrderedTerm : Term spec.language :=
  .func (Sum.inr ⟨index, by decide⟩) (fun
    | ⟨0, _⟩ => .var 8
    | ⟨1, _⟩ => .var 9)

def firstFunctionArgument? {L : Language} (t : Term L) :
    Option (Term L) :=
  match t with
  | .func f args =>
    if h : 0 < L.funArity f then some (args ⟨0, h⟩) else none
  | _ => none

/-- The exact ordered scope arguments cannot be reversed. -/
theorem wrongArgumentOrder_rejected :
    wrongOrderedTerm ≠ exactTerm := by
  intro h
  have hArg := congrArg firstFunctionArgument? h
  simp [wrongOrderedTerm, exactTerm, g2nnfReplayedSkolemTerm,
    g2nnfReplayedSkolemArgument, firstFunctionArgument?,
    liftEigenvarBaseTerm, replayG2nnfPathTerm,
    g2nnfPathQuantifierSubstitutions,
    replayQuantifierSubstitutionsTerm, occurrence, occurrencePath,
    quantifierRuleSubstitution?, outerRule, innerRule, spec, index,
    source, outerUniversalBody, innerUniversalBody,
    allocatedExistential, allocatedBody,
    SkolemSpec.language, SkolemLanguage, SkolemSpec.skolemRank,
    SkolemSpec.skolemScope, SkolemSpec.allocation,
    SkolemSpec.allocations, existentialDescriptors,
    existentialDescriptorsAux, universalScopeAux, termSubst] at hArg
  change some (Term.var 8 : Term spec.language) = some (Term.var 9) at hArg
  cases hArg

def occurrenceRootOnlyPath :
    G2nnfEqProofTree.RootToNodePath exTree exTree :=
  .root exTree

def wrongPathTerm : Term spec.language :=
  g2nnfReplayedSkolemTerm spec [] index

/-- Using only the target node as a root loses both outer
substitutions and therefore produces arguments `(0,2)`, not `(9,8)`. -/
theorem wrongPath_rejected :
    wrongPathTerm ≠ exactTerm := by
  intro h
  have hArg := congrArg firstFunctionArgument? h
  simp [wrongPathTerm, exactTerm, g2nnfReplayedSkolemTerm,
    g2nnfReplayedSkolemArgument, firstFunctionArgument?,
    liftEigenvarBaseTerm,
    replayQuantifierSubstitutionsTerm, occurrenceRootOnlyPath,
    occurrence, occurrencePath, spec, index, source, outerUniversalBody,
    innerUniversalBody, allocatedExistential, allocatedBody,
    SkolemSpec.language, SkolemLanguage,
    SkolemSpec.skolemRank, SkolemSpec.skolemScope,
    SkolemSpec.allocation, SkolemSpec.allocations,
    existentialDescriptors, existentialDescriptorsAux,
    universalScopeAux, termSubst] at hArg
  change some (Term.var 0 : Term spec.language) = some (Term.var 9) at hArg
  cases hArg

def extraDomainMap : EigenvarSkolemMap spec :=
  fun y => if y = 42 then some (.var 42) else legalMap y

/-- A `some` cell outside the exact `∃:left` eigenvariable domain is
rejected. -/
theorem wrongMapDomain_rejected :
    ¬ IsCanonicalEigenvarMapG2nnfEq outerTree spec extraDomainMap := by
  intro h
  unfold IsCanonicalEigenvarMapG2nnfEq at h
  rw [occurrences_exact] at h
  have h42 := (h.2.2.2.1 42).mp
    (show ∃ t, extraDomainMap 42 = some t from
      ⟨.var 42, by simp [extraDomainMap]⟩)
  simp [occurrence] at h42

/-- An exact occurrence whose eigenvariable is missing from the map
domain is likewise rejected. -/
theorem missingMapDomain_rejected :
    ¬ IsCanonicalEigenvarMapG2nnfEq outerTree spec (fun _ => none) := by
  intro h
  unfold IsCanonicalEigenvarMapG2nnfEq at h
  rw [occurrences_exact] at h
  have h7 := (h.2.2.2.1 7).mpr (by simp [occurrence])
  rcases h7 with ⟨t, ht⟩
  cases ht

def duplicateTree : G2nnfEqProofTree rfl
    (LCS.Finset.singleton source)
    (LCS.Finset.singleton (.conj leafFormula leafFormula)) :=
  .twoPremise (.conjRight leafFormula leafFormula
      (LCS.Finset.singleton source) LCS.Finset.empty)
    trivial rfl
    { logical := trivial
      conclusionNNF := by
        simp [G2nnfRuleCore.conclusion, AllNNF, source, outerUniversalBody,
          innerUniversalBody, allocatedExistential, allocatedBody,
          leafFormula_eq, proofAtom, FormulaN.isNNF]
        exact fun _ h => (LCS.Finset.not_mem_empty h).elim
      premisesNNF := by
        intro seq hseq
        simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil,
          or_false, or_self] at hseq
        subst seq
        exact outerTree.allNNF
      conclusionRectified := by
        apply allRectified_singletons source_rectified
        apply AllRectified.isRectified_of_isQuantifierFree
        constructor <;> rw [leafFormula_eq] <;> simp [proofAtom, isQuantifierFree] }
    outerTree outerTree

/-- Reusing the identical proof subtree in both premise positions
creates two distinct path occurrences with the same eigenvariable.
The required eigenvariable `Nodup` condition rejects this occurrence
confusion instead of silently identifying the two paths. -/
theorem duplicateIdenticalSyntaxOccurrence_rejected
    (eigenvarMap : EigenvarSkolemMap spec) :
    ¬ IsCanonicalEigenvarMapG2nnfEq duplicateTree spec eigenvarMap := by
  intro h
  unfold IsCanonicalEigenvarMapG2nnfEq at h
  have hNodup := h.2.1
  have hNotNodup :
      ¬ (List.map (fun occ => occ.eigenvariable)
        (g2nnfEqExSubLeftOccurrences duplicateTree)).Nodup := by
    simp [duplicateTree, g2nnfEqExSubLeftOccurrences,
      g2nnfEqExSubLeftOccurrencesAux, outerTree, innerTree, exTree,
      outerRule, innerRule, exRule]
  exact hNotNodup hNodup

/-- Applying the map beneath a binder masks that bound variable, even
when the same number is a mapped eigenvariable outside the binder. -/
theorem binderMasking_exact :
    applyEigenvarSubstFormula spec legalMap
      (.all 7 (.eq_ rfl (.var 7) (.var 6)))
      (by
        simp [EigenvarSkolemMapFreeForFormula,
          EigenvarSkolemMapFreeForFormulaAt,
          EigenvarSkolemMapFreeForTermAt,
          maskEigenvarSkolemMap, legalMap]) =
    .all 7
      (.eq_ rfl (.var 7) (.var 6)) := by
  simp [applyEigenvarSubstFormula, EigenvarSubstitution.applyFormulaRaw,
    applyEigenvarSubstTerm,
    maskEigenvarSkolemMap, legalMap]

/-- A range variable of an exact Skolem term may not be captured by
an unrelated binder at the formula occurrence where the map is
applied. This is the capture attack that domain masking alone misses. -/
def binderRangeCaptureFormula : FormulaN language :=
  .all 9 (.eq_ rfl (.var 7) (.var 7))

private theorem exactTerm_hasFreeVariableNine :
    Membership.mem (termFV exactTerm) 9 := by
  simp [exactTerm, g2nnfReplayedSkolemTerm,
    g2nnfReplayedSkolemArgument, spec, index,
    SkolemSpec.skolemRank, SkolemSpec.skolemScope,
    SkolemSpec.allocation, SkolemSpec.allocations,
    existentialDescriptors, existentialDescriptorsAux,
    universalScopeAux, source, outerUniversalBody,
    innerUniversalBody, allocatedExistential, allocatedBody,
    replayQuantifierSubstitutionsTerm, termSubst,
    liftEigenvarBaseTerm, termFV]
  refine ⟨(⟨0, by decide⟩ : Fin 2), ?_⟩
  rfl

theorem binderRangeCapture_rejected :
    ¬ EigenvarSkolemMapFreeForFormula spec legalMap
      binderRangeCaptureFormula := by
  intro hFree
  change EigenvarSkolemMapFreeForFormulaAt spec [] legalMap
    (.all 9 (.eq_ rfl (.var 7) (.var 7))) at hFree
  simp only [EigenvarSkolemMapFreeForFormulaAt] at hFree
  have hLeft := hFree.1
  unfold EigenvarSkolemMapFreeForTermAt at hLeft
  have hAvoidsNine :=
    hLeft exactTerm (by
      simp [maskEigenvarSkolemMap, legalMap]) 9 (by simp)
  exact hAvoidsNine exactTerm_hasFreeVariableNine

-- Separately named equality witnesses for the same Core proof skeleton.

def leafEq : G2nnfEqProofTree rfl
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

def exTreeEq : G2nnfEqProofTree (L := language) rfl
    (LCS.Finset.singleton exAmbient) delta :=
  .onePremise exRule trivial exRule_onePremise
    exRule_sideConditions leafEq

def innerTreeEq : G2nnfEqProofTree (L := language) rfl
    (LCS.Finset.singleton innerAmbient) delta :=
  .onePremise innerRule trivial
    innerRule_onePremise
    innerRule_sideConditions exTreeEq

def outerTreeEq : G2nnfEqProofTree (L := language) rfl
    (LCS.Finset.singleton source) delta :=
  .onePremise outerRule trivial
    outerRule_onePremise
    outerRule_sideConditions innerTreeEq

noncomputable def occurrencePathEq :
    G2nnfEqProofTree.RootToNodePath outerTreeEq exTreeEq :=
  .onePremise outerRule trivial
    outerRule_onePremise
    outerRule_sideConditions innerTreeEq
    (.onePremise innerRule trivial
      innerRule_onePremise
      innerRule_sideConditions exTreeEq (.root exTreeEq))

noncomputable def occurrenceEq :
    G2nnfEqExSubLeftOccurrence outerTreeEq where
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
  path := occurrencePathEq

/-- The equality occurrence package is inhabited only through the
required existential-left Core inference. -/
theorem equalityBaseExSubLeftOccurrence_accepted :
    Nonempty (G2nnfEqExSubLeftOccurrence outerTreeEq) :=
  ⟨occurrenceEq⟩

-- Permanent adversarial regression: all rules are quantifier rules
-- and `spec.source` is retained in every antecedent context, but the
-- transformed principal is unrelated. The former path-wide replay
-- accepted its substitution solely because it shared bound-variable
-- number `0` with the source allocation.

def unrelatedReplayPrincipal : FormulaN language :=
  .all 0 afterOuterSubstitution

def unrelatedReplayOuterAmbient : FormulaN language :=
  formulaSubstN afterOuterSubstitution (.var 9) 0

def unrelatedReplayInnerAmbient : FormulaN language :=
  formulaSubstN innerRuleBody (.var 8) 2

def unrelatedReplayLeafFormula : FormulaN language :=
  formulaSubstN proofAtom (.var 7) 1

private theorem unrelatedReplayOuterAmbient_eq :
    unrelatedReplayOuterAmbient = afterOuterSubstitution := by
  simp [unrelatedReplayOuterAmbient, unrelatedReplayPrincipal,
    afterOuterSubstitution, formulaSubstN, termSubst]

private theorem unrelatedReplayInnerAmbient_eq :
    unrelatedReplayInnerAmbient = proofExistential := by
  simp [afterOuterSubstitution, innerRuleBody, proofExistential,
    unrelatedReplayInnerAmbient, formulaSubstN, termSubst]

private theorem unrelatedReplayLeafFormula_eq :
    unrelatedReplayLeafFormula = proofAtom := by
  simp [unrelatedReplayLeafFormula, proofExistential, proofAtom,
    formulaSubstN, termSubst]

private theorem unrelatedReplayPrincipal_rectified :
    isRectified unrelatedReplayPrincipal := by
  simp [unrelatedReplayPrincipal, afterOuterSubstitution, isRectified,
    boundVarsFresh, distinctQuantifierBindings, formulaFVN, formulaBVN,
    termFV]

private theorem unrelatedReplayOuterAmbient_rectified :
    isRectified unrelatedReplayOuterAmbient := by
  rw [unrelatedReplayOuterAmbient_eq]
  simp [afterOuterSubstitution, isRectified, boundVarsFresh,
    distinctQuantifierBindings, formulaFVN, formulaBVN, termFV]

private theorem unrelatedReplayInnerAmbient_rectified :
    isRectified unrelatedReplayInnerAmbient := by
  rw [unrelatedReplayInnerAmbient_eq]
  simp [proofExistential, proofAtom, isRectified, boundVarsFresh,
    distinctQuantifierBindings, formulaFVN, formulaBVN, termFV]

private theorem unrelatedReplayLeafFormula_rectified :
    isRectified unrelatedReplayLeafFormula := by
  rw [unrelatedReplayLeafFormula_eq]
  exact proofAtom_rectified

def unrelatedReplayOuterMaxOccurrence :
    MaxQuantifierOccurrence unrelatedReplayPrincipal :=
  .all 0 afterOuterSubstitution

def unrelatedReplayInnerMaxOccurrence :
    MaxQuantifierOccurrence unrelatedReplayOuterAmbient :=
  .all 2 innerRuleBody

def unrelatedReplayExMaxOccurrence :
    MaxQuantifierOccurrence unrelatedReplayInnerAmbient :=
  .ex 1 proofAtom

def unrelatedReplayDelta : LCS.Finset (FormulaN language) :=
  LCS.Finset.singleton unrelatedReplayLeafFormula

def unrelatedReplayContext : LCS.Finset (FormulaN language) :=
  LCS.Finset.singleton source

def unrelatedReplayOuterRule : G2nnfRuleCore language :=
  .allSubLeft unrelatedReplayPrincipal
    unrelatedReplayOuterMaxOccurrence 0
    afterOuterSubstitution (.var 9) rfl unrelatedReplayContext unrelatedReplayDelta

private theorem unrelatedReplayOuterRule_onePremise :
    unrelatedReplayOuterRule.premises.length = 1 := rfl

private theorem unrelatedReplayOuterRule_sideConditions :
    G2nnfRuleCore.SideConditions unrelatedReplayOuterRule := by
  constructor
  ·
    change (0 = 2) ∨ ((2 ≠ 9) ∧ ((0 = 1) ∨ ((1 ≠ 9) ∧ True)))
    simp
  ·
    simp [unrelatedReplayOuterRule, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises,
      AllNNF, unrelatedReplayContext, unrelatedReplayDelta,
      unrelatedReplayPrincipal, unrelatedReplayOuterAmbient_eq,
      unrelatedReplayInnerAmbient_eq, unrelatedReplayLeafFormula_eq,
      source, outerUniversalBody, innerUniversalBody, allocatedExistential,
      allocatedBody, afterOuterSubstitution, proofExistential, proofAtom,
      unrelatedReplayOuterMaxOccurrence, unrelatedReplayInnerMaxOccurrence,
      unrelatedReplayExMaxOccurrence, innerRuleBody, FormulaN.isNNF,
      MaxQuantifierOccurrence.replace, formulaSubstN, termSubst]
  ·
    simp [unrelatedReplayOuterRule, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises,
      AllNNF, unrelatedReplayContext, unrelatedReplayDelta,
      unrelatedReplayPrincipal, unrelatedReplayOuterAmbient_eq,
      unrelatedReplayInnerAmbient_eq, unrelatedReplayLeafFormula_eq,
      source, outerUniversalBody, innerUniversalBody, allocatedExistential,
      allocatedBody, afterOuterSubstitution, proofExistential, proofAtom,
      unrelatedReplayOuterMaxOccurrence, unrelatedReplayInnerMaxOccurrence,
      unrelatedReplayExMaxOccurrence, innerRuleBody, FormulaN.isNNF,
      MaxQuantifierOccurrence.replace, formulaSubstN, termSubst]
  · exact AllRectified.insert_left unrelatedReplayPrincipal_rectified
      (allRectified_singletons source_rectified unrelatedReplayLeafFormula_rectified)


def unrelatedReplayInnerRule : G2nnfRuleCore language :=
  .allSubLeft unrelatedReplayOuterAmbient
    unrelatedReplayInnerMaxOccurrence 2
    innerRuleBody (.var 8) rfl unrelatedReplayContext unrelatedReplayDelta

private theorem unrelatedReplayInnerRule_onePremise :
    unrelatedReplayInnerRule.premises.length = 1 := rfl

private theorem unrelatedReplayInnerRule_sideConditions :
    G2nnfRuleCore.SideConditions unrelatedReplayInnerRule := by
  constructor
  ·
    change (2 = 1) ∨ ((1 ≠ 8) ∧ True)
    simp
  ·
    simp [unrelatedReplayInnerRule, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises,
      AllNNF, unrelatedReplayContext, unrelatedReplayDelta,
      unrelatedReplayPrincipal, unrelatedReplayOuterAmbient_eq,
      unrelatedReplayInnerAmbient_eq, unrelatedReplayLeafFormula_eq,
      source, outerUniversalBody, innerUniversalBody, allocatedExistential,
      allocatedBody, afterOuterSubstitution, proofExistential, proofAtom,
      unrelatedReplayOuterMaxOccurrence, unrelatedReplayInnerMaxOccurrence,
      unrelatedReplayExMaxOccurrence, innerRuleBody, FormulaN.isNNF,
      MaxQuantifierOccurrence.replace, formulaSubstN, termSubst]
  ·
    simp [unrelatedReplayInnerRule, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises,
      AllNNF, unrelatedReplayContext, unrelatedReplayDelta,
      unrelatedReplayPrincipal, unrelatedReplayOuterAmbient_eq,
      unrelatedReplayInnerAmbient_eq, unrelatedReplayLeafFormula_eq,
      source, outerUniversalBody, innerUniversalBody, allocatedExistential,
      allocatedBody, afterOuterSubstitution, proofExistential, proofAtom,
      unrelatedReplayOuterMaxOccurrence, unrelatedReplayInnerMaxOccurrence,
      unrelatedReplayExMaxOccurrence, innerRuleBody, FormulaN.isNNF,
      MaxQuantifierOccurrence.replace, formulaSubstN, termSubst]
  · exact AllRectified.insert_left unrelatedReplayOuterAmbient_rectified
      (allRectified_singletons source_rectified unrelatedReplayLeafFormula_rectified)


def unrelatedReplayExRule : G2nnfRuleCore language :=
  .exSubLeft unrelatedReplayInnerAmbient
    unrelatedReplayExMaxOccurrence 1 proofAtom 7 rfl unrelatedReplayContext unrelatedReplayDelta

private theorem unrelatedReplayExRule_onePremise :
    unrelatedReplayExRule.premises.length = 1 := rfl

private theorem unrelatedReplayExRule_sideConditions :
    G2nnfRuleCore.SideConditions unrelatedReplayExRule := by
  constructor
  ·
    simp [unrelatedReplayExRule, G2nnfRuleCore.LogicalSideConditions,
      unrelatedReplayContext, unrelatedReplayDelta, unrelatedReplayInnerAmbient_eq,
      unrelatedReplayLeafFormula_eq, source, outerUniversalBody, innerUniversalBody,
      allocatedExistential, allocatedBody, proofExistential, proofAtom,
      isFreeForN, formulaFVN, termFV]
  ·
    simp [unrelatedReplayExRule, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises,
      AllNNF, unrelatedReplayContext, unrelatedReplayDelta,
      unrelatedReplayPrincipal, unrelatedReplayOuterAmbient_eq,
      unrelatedReplayInnerAmbient_eq, unrelatedReplayLeafFormula_eq,
      source, outerUniversalBody, innerUniversalBody, allocatedExistential,
      allocatedBody, afterOuterSubstitution, proofExistential, proofAtom,
      unrelatedReplayOuterMaxOccurrence, unrelatedReplayInnerMaxOccurrence,
      unrelatedReplayExMaxOccurrence, innerRuleBody, FormulaN.isNNF,
      MaxQuantifierOccurrence.replace, formulaSubstN, termSubst]
  ·
    simp [unrelatedReplayExRule, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises,
      AllNNF, unrelatedReplayContext, unrelatedReplayDelta,
      unrelatedReplayPrincipal, unrelatedReplayOuterAmbient_eq,
      unrelatedReplayInnerAmbient_eq, unrelatedReplayLeafFormula_eq,
      source, outerUniversalBody, innerUniversalBody, allocatedExistential,
      allocatedBody, afterOuterSubstitution, proofExistential, proofAtom,
      unrelatedReplayOuterMaxOccurrence, unrelatedReplayInnerMaxOccurrence,
      unrelatedReplayExMaxOccurrence, innerRuleBody, FormulaN.isNNF,
      MaxQuantifierOccurrence.replace, formulaSubstN, termSubst]
  · exact AllRectified.insert_left unrelatedReplayInnerAmbient_rectified
      (allRectified_singletons source_rectified unrelatedReplayLeafFormula_rectified)

def unrelatedReplayLeaf : G2nnfEqProofTree (L := language) rfl
    (LCS.Finset.insert unrelatedReplayLeafFormula unrelatedReplayContext)
    unrelatedReplayDelta :=
  .axiom_ (.axiomPosId unrelatedReplayLeafFormula
      (by rw [unrelatedReplayLeafFormula_eq]; simp [proofAtom, FormulaN.isAtomic])
      unrelatedReplayContext LCS.Finset.empty) trivial rfl
    { logical := trivial
      conclusionNNF := by
        simp [G2nnfRuleCore.conclusion, AllNNF, unrelatedReplayContext,
          unrelatedReplayLeafFormula_eq, proofAtom, source, outerUniversalBody,
          innerUniversalBody, allocatedExistential, allocatedBody, FormulaN.isNNF]
        exact fun _ h => (LCS.Finset.not_mem_empty h).elim
      premisesNNF := by simp [G2nnfRuleCore.premises]
      conclusionRectified := by
        apply AllRectified.insert_left unrelatedReplayLeafFormula_rectified
        apply AllRectified.insert_right unrelatedReplayLeafFormula_rectified
        rw [unrelatedReplayContext, ← finset_insert_empty_eq_singleton source]
        exact AllRectified.insert_left source_rectified AllRectified.empty }

def unrelatedReplayExTree : G2nnfEqProofTree rfl
    (LCS.Finset.insert unrelatedReplayInnerAmbient
      unrelatedReplayContext)
    unrelatedReplayDelta :=
  .onePremise unrelatedReplayExRule trivial unrelatedReplayExRule_onePremise
    unrelatedReplayExRule_sideConditions unrelatedReplayLeaf

def unrelatedReplayInnerTree : G2nnfEqProofTree rfl
    (LCS.Finset.insert unrelatedReplayOuterAmbient
      unrelatedReplayContext)
    unrelatedReplayDelta :=
  .onePremise unrelatedReplayInnerRule trivial unrelatedReplayInnerRule_onePremise
    unrelatedReplayInnerRule_sideConditions unrelatedReplayExTree

def unrelatedReplayTree : G2nnfEqProofTree rfl
    (LCS.Finset.insert unrelatedReplayPrincipal
      unrelatedReplayContext)
    unrelatedReplayDelta :=
  .onePremise unrelatedReplayOuterRule trivial unrelatedReplayOuterRule_onePremise
    unrelatedReplayOuterRule_sideConditions unrelatedReplayInnerTree

def unrelatedReplayOccurrencePath :
    G2nnfEqProofTree.RootToNodePath
      unrelatedReplayTree unrelatedReplayExTree :=
  .onePremise unrelatedReplayOuterRule trivial unrelatedReplayOuterRule_onePremise
    unrelatedReplayOuterRule_sideConditions unrelatedReplayInnerTree
    (.onePremise unrelatedReplayInnerRule trivial unrelatedReplayInnerRule_onePremise
      unrelatedReplayInnerRule_sideConditions unrelatedReplayExTree
      (.root unrelatedReplayExTree))

def unrelatedReplayOccurrence :
    G2nnfEqExSubLeftOccurrence unrelatedReplayTree where
  ambient := unrelatedReplayInnerAmbient
  maxOccurrence := unrelatedReplayExMaxOccurrence
  boundVar := 1
  body := proofAtom
  eigenvariable := 7
  hSelected := rfl
  gamma := unrelatedReplayContext
  delta := unrelatedReplayDelta
  hPrem := unrelatedReplayExRule_onePremise
  hSC := unrelatedReplayExRule_sideConditions
  premise := unrelatedReplayLeaf
  path := unrelatedReplayOccurrencePath

theorem unrelatedReplaySource_retainedAtRoot :
    source ∈
      (LCS.Finset.insert unrelatedReplayPrincipal
        unrelatedReplayContext) := by
  simp [unrelatedReplayContext]

/-- This records the exact old failure mode: branch-wide replay still
forges the source allocation into the unrelated proof occurrence. -/
theorem unrelatedReplayPath_branchWideReplay_forgesLink :
    replayG2nnfEqPathFormula unrelatedReplayOccurrence.path
      (spec.allocation index).1 = proofExistential := by
  simp [unrelatedReplayOccurrence, unrelatedReplayOccurrencePath,
    replayG2nnfEqPathFormula, g2nnfEqPathQuantifierSubstitutions,
    replayQuantifierSubstitutionsFormula,
    quantifierRuleSubstitution?, unrelatedReplayOuterRule,
    unrelatedReplayInnerRule, spec, index,
    SkolemSpec.allocation, SkolemSpec.allocations,
    existentialDescriptors, existentialDescriptorsAux,
    universalScopeAux, source, outerUniversalBody,
    innerUniversalBody, allocatedExistential, allocatedBody,
    proofExistential, formulaSubstN, termSubst]
  rfl

theorem unrelatedReplayOccurrences_exact :
    g2nnfEqExSubLeftOccurrences unrelatedReplayTree =
      [unrelatedReplayOccurrence] := by
  simp [g2nnfEqExSubLeftOccurrences, g2nnfEqExSubLeftOccurrencesAux,
    unrelatedReplayTree, unrelatedReplayInnerTree,
    unrelatedReplayExTree, unrelatedReplayLeaf,
    unrelatedReplayOuterRule, unrelatedReplayInnerRule,
    unrelatedReplayExRule, unrelatedReplayOccurrence,
    unrelatedReplayOccurrencePath,
    G2nnfEqProofTree.RootToNodePath.trans]
  rfl

/-- Every inference in the equality proof has no cut formula. -/
theorem unrelatedReplayTree_isCutFree :
    allRulesSatisfy (fun rule => rule.cutFormula = none) unrelatedReplayTree := by
  exact ⟨rfl, rfl, rfl, trivial⟩

theorem unrelatedReplayPrincipal_isNotSource :
    unrelatedReplayPrincipal ≠ source := by
  simp [unrelatedReplayPrincipal, afterOuterSubstitution, source,
    outerUniversalBody, innerUniversalBody, allocatedExistential,
    allocatedBody]
  intro h
  cases h

private theorem unrelatedReplayOuter_sourceStep_exact
    (address : FormulaOccurrenceAddress)
    (next : FormulaOccurrenceFocus language)
    (head : Option (Nat × Term language))
    (hStep : g2nnfFormulaOccurrenceStep unrelatedReplayOuterRule
      .only ⟨source, address⟩ next head) :
    next = ⟨source, address⟩ ∧ head = none := by
  have hNe : FormulaN.eq_ (L := language) rfl (Term.var 0) (Term.var 2) ≠
      FormulaN.eq_ rfl (Term.var 9) (Term.var 2) := by
    intro h
    cases h
  simpa [hNe, Ne.symm hNe, g2nnfFormulaOccurrenceStep, focusIsStrictContext,
    g2nnfLeftPremiseContext, g2nnfRuleSideContexts, g2nnfLeftPrincipal?, g2nnfLeftPremiseInserted?,
    unrelatedReplayOuterRule, unrelatedReplayContext,
    unrelatedReplayOuterMaxOccurrence,
    unrelatedReplayPrincipal, unrelatedReplayOuterAmbient_eq,
    afterOuterSubstitution, source, outerUniversalBody,
    innerUniversalBody, allocatedExistential, allocatedBody,
    MaxQuantifierOccurrence.replace, formulaSubstN, termSubst] using hStep

private theorem unrelatedReplayInner_sourceStep_exact
    (address : FormulaOccurrenceAddress)
    (next : FormulaOccurrenceFocus language)
    (head : Option (Nat × Term language))
    (hStep : g2nnfFormulaOccurrenceStep unrelatedReplayInnerRule
      .only ⟨source, address⟩ next head) :
    next = ⟨source, address⟩ ∧ head = none := by
  simpa [g2nnfFormulaOccurrenceStep, focusIsStrictContext,
    g2nnfLeftPremiseContext, g2nnfRuleSideContexts, g2nnfLeftPrincipal?, g2nnfLeftPremiseInserted?,
    unrelatedReplayInnerRule, unrelatedReplayContext,
    unrelatedReplayInnerMaxOccurrence,
    unrelatedReplayOuterAmbient_eq,
    unrelatedReplayInnerAmbient_eq, afterOuterSubstitution,
    innerRuleBody, proofExistential, proofAtom, source,
    outerUniversalBody, innerUniversalBody, allocatedExistential,
    allocatedBody, MaxQuantifierOccurrence.replace,
    formulaSubstN, termSubst]
    using hStep

private theorem unrelatedReplayLineage_fromSource_rejected
    (sourceAddress targetAddress : FormulaOccurrenceAddress)
    (substitutions : List (Nat × Term language)) :
    ¬ g2nnfEqFormulaOccurrenceLineage unrelatedReplayOccurrence.path
      ⟨source, sourceAddress⟩
      ⟨unrelatedReplayOccurrence.ambient, targetAddress⟩
      substitutions := by
  intro hLineage
  unfold unrelatedReplayOccurrence at hLineage
  unfold unrelatedReplayOccurrencePath at hLineage
  simp only [g2nnfEqFormulaOccurrenceLineage] at hLineage
  rcases hLineage with
    ⟨nextOuter, headOuter, tailOuter, hOuter, hRest, _⟩
  have ⟨hNextOuter, _⟩ :=
    unrelatedReplayOuter_sourceStep_exact
      sourceAddress nextOuter headOuter hOuter
  subst nextOuter
  rcases hRest with
    ⟨nextInner, headInner, tailInner, hInner, hRoot, _⟩
  have ⟨hNextInner, _⟩ :=
    unrelatedReplayInner_sourceStep_exact
      sourceAddress nextInner headInner hInner
  subst nextInner
  have hFocus := hRoot.1
  have hAmbient := congrArg FormulaOccurrenceFocus.ambient hFocus
  exact (by
    simpa [unrelatedReplayInnerAmbient_eq, source,
      outerUniversalBody, innerUniversalBody,
      allocatedExistential, allocatedBody, proofExistential,
      proofAtom] using hAmbient)

theorem unrelatedPrincipalG2_exactBinding_rejected
    (i : Fin spec.n) (substitutions : List (Nat × Term language)) :
    ¬ G2nnfEqExactAllocationBinding spec unrelatedReplayOccurrence
      i substitutions := by
  intro hBinding
  rcases hBinding with
    ⟨_, _, sourceAddress, targetAddress, _, _, hLineage, _⟩
  exact unrelatedReplayLineage_fromSource_rejected
    sourceAddress targetAddress substitutions
    (by simpa [spec] using hLineage)

def unrelatedReplayMap : EigenvarSkolemMap spec :=
  fun y => if y = 7 then some exactTerm else none

theorem unrelatedPrincipalG2_canonicalMap_rejected :
    ¬ IsCanonicalEigenvarMapG2nnfEq
      unrelatedReplayTree spec unrelatedReplayMap := by
  intro hCanonical
  unfold IsCanonicalEigenvarMapG2nnfEq at hCanonical
  rw [unrelatedReplayOccurrences_exact] at hCanonical
  have hOrdered := hCanonical.2.2.1
  simp only [IsCanonicalEigenvarMapG2nnfEqOrderedAux] at hOrdered
  rcases hOrdered.2 with
    ⟨i, substitutions, _, hBinding, _⟩
  exact unrelatedPrincipalG2_exactBinding_rejected
    i substitutions hBinding

def unrelatedReplayLeafEq : G2nnfEqProofTree (L := language) rfl
    (LCS.Finset.insert unrelatedReplayLeafFormula unrelatedReplayContext)
    unrelatedReplayDelta :=
  .axiom_ (.axiomPosId unrelatedReplayLeafFormula
      (by rw [unrelatedReplayLeafFormula_eq]; simp [proofAtom, FormulaN.isAtomic])
      unrelatedReplayContext LCS.Finset.empty) trivial rfl
    { logical := trivial
      conclusionNNF := by
        simp [G2nnfRuleCore.conclusion, AllNNF, unrelatedReplayContext,
          unrelatedReplayLeafFormula_eq, proofAtom, source, outerUniversalBody,
          innerUniversalBody, allocatedExistential, allocatedBody, FormulaN.isNNF]
        exact fun _ h => (LCS.Finset.not_mem_empty h).elim
      premisesNNF := by simp [G2nnfRuleCore.premises]
      conclusionRectified := by
        apply AllRectified.insert_left unrelatedReplayLeafFormula_rectified
        apply AllRectified.insert_right unrelatedReplayLeafFormula_rectified
        rw [unrelatedReplayContext, ← finset_insert_empty_eq_singleton source]
        exact AllRectified.insert_left source_rectified AllRectified.empty }

def unrelatedReplayExTreeEq : G2nnfEqProofTree (L := language) rfl
    (LCS.Finset.insert unrelatedReplayInnerAmbient
      unrelatedReplayContext)
    unrelatedReplayDelta :=
  .onePremise unrelatedReplayExRule trivial unrelatedReplayExRule_onePremise
    unrelatedReplayExRule_sideConditions unrelatedReplayLeafEq

def unrelatedReplayInnerTreeEq :
    G2nnfEqProofTree (L := language) rfl
      (LCS.Finset.insert unrelatedReplayOuterAmbient
        unrelatedReplayContext)
      unrelatedReplayDelta :=
  .onePremise unrelatedReplayInnerRule trivial unrelatedReplayInnerRule_onePremise
    unrelatedReplayInnerRule_sideConditions unrelatedReplayExTreeEq

def unrelatedReplayTreeEq : G2nnfEqProofTree (L := language) rfl
    (LCS.Finset.insert unrelatedReplayPrincipal
      unrelatedReplayContext)
    unrelatedReplayDelta :=
  .onePremise unrelatedReplayOuterRule trivial unrelatedReplayOuterRule_onePremise
    unrelatedReplayOuterRule_sideConditions
      unrelatedReplayInnerTreeEq

noncomputable def unrelatedReplayOccurrencePathEq :
    G2nnfEqProofTree.RootToNodePath
      unrelatedReplayTreeEq unrelatedReplayExTreeEq :=
  .onePremise unrelatedReplayOuterRule trivial unrelatedReplayOuterRule_onePremise
    unrelatedReplayOuterRule_sideConditions
      unrelatedReplayInnerTreeEq
    (.onePremise unrelatedReplayInnerRule trivial unrelatedReplayInnerRule_onePremise
      unrelatedReplayInnerRule_sideConditions unrelatedReplayExTreeEq
      (.root unrelatedReplayExTreeEq))

noncomputable def unrelatedReplayOccurrenceEq :
    G2nnfEqExSubLeftOccurrence unrelatedReplayTreeEq where
  ambient := unrelatedReplayInnerAmbient
  maxOccurrence := unrelatedReplayExMaxOccurrence
  boundVar := 1
  body := proofAtom
  eigenvariable := 7
  hSelected := rfl
  gamma := unrelatedReplayContext
  delta := unrelatedReplayDelta
  hPrem := unrelatedReplayExRule_onePremise
  hSC := unrelatedReplayExRule_sideConditions
  premise := unrelatedReplayLeafEq
  path := unrelatedReplayOccurrencePathEq

theorem unrelatedReplayPathEq_branchWideReplay_forgesLink :
    replayG2nnfEqPathFormula unrelatedReplayOccurrenceEq.path
      (spec.allocation index).1 = proofExistential := by
  simp [unrelatedReplayOccurrenceEq,
    unrelatedReplayOccurrencePathEq,
    replayG2nnfEqPathFormula,
    g2nnfEqPathQuantifierSubstitutions,
    replayQuantifierSubstitutionsFormula,
    quantifierEqRuleSubstitution?, quantifierRuleSubstitution?,
    unrelatedReplayOuterRule, unrelatedReplayInnerRule,
    spec, index, SkolemSpec.allocation, SkolemSpec.allocations,
    existentialDescriptors, existentialDescriptorsAux,
    universalScopeAux, source, outerUniversalBody,
    innerUniversalBody, allocatedExistential, allocatedBody,
    proofExistential, formulaSubstN, termSubst]
  rfl

/-- The equality attack uses the same Core all-quantifier normal-form
skeleton; equality axioms play no role. -/
theorem unrelatedReplayTreeEq_baseQuantifierSkeleton :
    unrelatedReplayOuterRule.isQuantifierRuleBool = true ∧
      unrelatedReplayInnerRule.isQuantifierRuleBool = true ∧
      unrelatedReplayExRule.isQuantifierRuleBool = true := by
  simp [unrelatedReplayOuterRule, unrelatedReplayInnerRule,
    unrelatedReplayExRule, G2nnfRuleCore.isQuantifierRuleBool]

theorem unrelatedReplayOccurrencesEq_exact :
    g2nnfEqExSubLeftOccurrences unrelatedReplayTreeEq =
      [unrelatedReplayOccurrenceEq] := by
  simp [g2nnfEqExSubLeftOccurrences,
    g2nnfEqExSubLeftOccurrencesAux, unrelatedReplayTreeEq,
    unrelatedReplayInnerTreeEq, unrelatedReplayExTreeEq,
    unrelatedReplayLeafEq, unrelatedReplayOuterRule,
    unrelatedReplayInnerRule, unrelatedReplayExRule,
    unrelatedReplayOccurrenceEq, unrelatedReplayOccurrencePathEq,
    G2nnfEqProofTree.RootToNodePath.trans]
  rfl

private theorem unrelatedReplayLineageEq_fromSource_rejected
    (sourceAddress targetAddress : FormulaOccurrenceAddress)
    (substitutions : List (Nat × Term language)) :
    ¬ g2nnfEqFormulaOccurrenceLineage
      unrelatedReplayOccurrenceEq.path
      ⟨source, sourceAddress⟩
      ⟨unrelatedReplayOccurrenceEq.ambient, targetAddress⟩
      substitutions := by
  intro hLineage
  unfold unrelatedReplayOccurrenceEq at hLineage
  unfold unrelatedReplayOccurrencePathEq at hLineage
  simp only [g2nnfEqFormulaOccurrenceLineage] at hLineage
  rcases hLineage with
    ⟨nextOuter, headOuter, tailOuter, hOuter, hRest, _⟩
  have ⟨hNextOuter, _⟩ :=
    unrelatedReplayOuter_sourceStep_exact
      sourceAddress nextOuter headOuter hOuter
  subst nextOuter
  rcases hRest with
    ⟨nextInner, headInner, tailInner, hInner, hRoot, _⟩
  have ⟨hNextInner, _⟩ :=
    unrelatedReplayInner_sourceStep_exact
      sourceAddress nextInner headInner hInner
  subst nextInner
  have hFocus := hRoot.1
  have hAmbient := congrArg FormulaOccurrenceFocus.ambient hFocus
  exact (by
    simpa [unrelatedReplayInnerAmbient_eq, source,
      outerUniversalBody, innerUniversalBody,
      allocatedExistential, allocatedBody, proofExistential,
      proofAtom] using hAmbient)

theorem unrelatedPrincipalG2Eq_exactBinding_rejected
    (i : Fin spec.n) (substitutions : List (Nat × Term language)) :
    ¬ G2nnfEqExactAllocationBinding spec
      unrelatedReplayOccurrenceEq i substitutions := by
  intro hBinding
  rcases hBinding with
    ⟨_, _, sourceAddress, targetAddress, _, _, hLineage, _⟩
  exact unrelatedReplayLineageEq_fromSource_rejected
    sourceAddress targetAddress substitutions
    (by simpa [spec] using hLineage)

theorem unrelatedPrincipalG2Eq_canonicalMap_rejected :
    ¬ IsCanonicalEigenvarMapG2nnfEq
      unrelatedReplayTreeEq spec unrelatedReplayMap := by
  intro hCanonical
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hCanonical
  rw [unrelatedReplayOccurrencesEq_exact] at hCanonical
  have hOrdered := hCanonical.2.2.1
  simp only [IsCanonicalEigenvarMapG2nnfEqOrderedAux] at hOrdered
  rcases hOrdered.2 with
    ⟨i, substitutions, _, hBinding, _⟩
  exact unrelatedPrincipalG2Eq_exactBinding_rejected
    i substitutions hBinding

end
end CanonicalEigenvarMapRegression
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
namespace OrderedEigenvarCompositionRegression
open CanonicalEigenvarMapRegression
noncomputable section

def unaryTerm (t : Term spec.language) : Term spec.language :=
  .func (Sum.inl .g) (fun _ => t)

@[simp]
theorem unaryTerm_mem_termFV (t : Term spec.language) (z : Nat) :
    Membership.mem (termFV (unaryTerm t)) z ↔
      Membership.mem (termFV t) z := by
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨⟨0, by decide⟩, h⟩

def firstFinalTerm : Term spec.language :=
  unaryTerm (.var 42)

def firstPrefixMap : EigenvarSkolemMap spec :=
  fun y => if y = 7 then some firstFinalTerm else none

def secondRawTerm : Term spec.language :=
  unaryTerm (.var 7)

def secondFinalTerm : Term spec.language :=
  applyEigenvarSkolemMapTerm spec firstPrefixMap secondRawTerm

def secondPrefixMap : EigenvarSkolemMap spec :=
  fun y =>
    if y = 7 then some firstFinalTerm
    else if y = 8 then some secondFinalTerm
    else none

def thirdRawTerm : Term spec.language :=
  unaryTerm (.var 8)

def thirdFinalTerm : Term spec.language :=
  applyEigenvarSkolemMapTerm spec secondPrefixMap thirdRawTerm

def threeLevelMap : EigenvarSkolemMap spec :=
  fun y =>
    if y = 7 then some firstFinalTerm
    else if y = 8 then some secondFinalTerm
    else if y = 9 then some thirdFinalTerm
    else none

/-- Three outer-to-inner cells compose transitively: the third final
range contains the second final range, which already contains the
first, rather than either mapped eigenvariable. -/
theorem threeLevelChain_fullyComposed :
    thirdFinalTerm =
      unaryTerm (unaryTerm (unaryTerm (.var 42))) := by
  simp [thirdFinalTerm, thirdRawTerm, secondPrefixMap,
    secondFinalTerm, secondRawTerm, firstPrefixMap, firstFinalTerm,
    unaryTerm, applyEigenvarSkolemMapTerm]

/-- One-level public application returns the already-composed third
range. -/
theorem threeLevelChain_oneLevelApplication :
    applyEigenvarSubstTerm spec threeLevelMap (.var 9) =
      unaryTerm (unaryTerm (unaryTerm (.var 42))) := by
  rw [show applyEigenvarSubstTerm spec threeLevelMap (.var 9) =
      thirdFinalTerm by simp [applyEigenvarSubstTerm, threeLevelMap]]
  exact threeLevelChain_fullyComposed

/-- The result of the three-level application contains none of the
canonical-domain variables. The unrelated free variable `42` remains,
showing this is not a closed-term requirement. -/
theorem threeLevelChain_applicationAvoidsDomain
    (z : Nat) (hz : z ∈ [7, 8, 9]) :
    ¬ Membership.mem
      (termFV (applyEigenvarSubstTerm spec threeLevelMap (.var 9))) z := by
  rw [threeLevelChain_oneLevelApplication]
  simp at hz
  rcases hz with rfl | rfl | rfl
  · simp only [unaryTerm_mem_termFV, termFV]
    change 7 ≠ 42
    omega
  · simp only [unaryTerm_mem_termFV, termFV]
    change 8 ≠ 42
    omega
  · simp only [unaryTerm_mem_termFV, termFV]
    change 9 ≠ 42
    omega

def forwardDependencyMap : EigenvarSkolemMap spec :=
  fun y =>
    if y = 7 then some (.var 8)
    else if y = 8 then some firstFinalTerm
    else none

/-- A forward dependency survives normalization and is therefore
rejected by the final domain/range invariant. -/
theorem forwardDependency_rejected :
    ¬ EigenvarSkolemMapRangeAvoidsDomain spec forwardDependencyMap
      [7, 8] := by
  intro h
  exact h 7 (.var 8) (by simp [forwardDependencyMap])
    8 (by simp) (by rfl)

def cyclicDependencyMap : EigenvarSkolemMap spec :=
  fun y =>
    if y = 7 then some (.var 8)
    else if y = 8 then some (.var 7)
    else none

end
end OrderedEigenvarCompositionRegression
end LCS.Herbrand.SHGTheorem.Herbrand
end

