import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.SyntaxAllocation
import LCS.Herbrand.SHGTheorem.Herbrand.OccurrenceLineage
import LCS.Herbrand.SHGTheorem.Herbrand.CanonicalMapRegression
import LCS.Herbrand.SHGTheorem.Herbrand.NestedMapRegression
import LCS.Herbrand.SHGTheorem.Herbrand.Alteration
import LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination
import LCS.Herbrand.SHGTheorem.Herbrand.ClosedSubstitution
import LCS.Herbrand.SHGTheorem.Herbrand.ScopeAndPurity
import LCS.Herbrand.SHGTheorem.Herbrand.Provenance
import LCS.Herbrand.SHGTheorem.Herbrand.LowerTrace

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

/-- Certified nonempty equality-system result for one exact lower path. -/
private noncomputable def buildClosedG2nnfEqLowerStates
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    {Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    (root : G2nnfEqProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot)
    {node : G2nnfEqProofTree hL Γnode Δnode}
    (path : G2nnfEqProofTree.RootToNodePath root node)
    (hQuantifier :
      AllRulesQuantifierOnPath_G2nnfEq path)
    (hPure : IsPureVariableProof_G2nnfEq root) :
    ClosedG2nnfEqLowerStateFamily
      spec seed root node path := by
  let initial :=
    ClosedG2nnfEqLowerState.initial spec seed root hPure
  have result :=
    buildClosedG2nnfEqLowerStateAux
      spec seed root initial path hQuantifier
  simpa [initial, ClosedG2nnfEqLowerState.initial,
    G2nnfEqProofTree.RootToNodePath.trans] using result

/-- Helper: Every NNF Skolem normal form formula has at least one
c-instance. For atoms, the identity is a c-instance; for connectives,
c-instances of subformulae combine; for universal quantifiers, the
provided closed seed supplies a nonempty instantiation list. -/
theorem skolem_nnf_has_cinstance {L : Language}
    (B : FormulaN L) (hNNF : FormulaN.isNNF B)
    (hSkolem : isSkolemNormalForm B)
    (seed : {t : Term L // Term.isClosed t}) :
    ∃ D, isCInstanceOf D B := by
-- BEGIN PROOF
  have construct :
      ∀ (m : Nat) (B : FormulaN L),
        formulaQuantCount B = m →
        isSkolemNormalFormShape B →
        ∃ D, isCInstanceOf D B := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
        intro B hCount hShape
        cases B with
        | predN P args =>
            exact ⟨.predN P args,
              literal_self_cinstance (.predN P args) (Or.inl rfl)⟩
        | eq_ hEq lhs rhs =>
            exact ⟨.eq_ hEq lhs rhs,
              literal_self_cinstance (.eq_ hEq lhs rhs) (Or.inl rfl)⟩
        | neg A =>
            exact ⟨.neg A,
              literal_self_cinstance (.neg A)
                (Or.inr ⟨A, rfl, hShape⟩)⟩
        | conj A C =>
            have hA_lt : formulaQuantCount A < m := by
              simp [formulaQuantCount] at hCount
              omega
            have hC_lt : formulaQuantCount C < m := by
              simp [formulaQuantCount] at hCount
              omega
            obtain ⟨H, hH⟩ :=
              ih (formulaQuantCount A) hA_lt A rfl hShape.1
            obtain ⟨K, hK⟩ :=
              ih (formulaQuantCount C) hC_lt C rfl hShape.2
            obtain ⟨ciH, hHSource, hHFormula, hHWF⟩ := hH
            obtain ⟨ciK, hKSource, hKFormula, hKWF⟩ := hK
            refine ⟨.conj H K,
              ⟨CInstance.connective true A C ciH ciK, rfl, ?_, ?_⟩⟩
            · simp only [CInstance.toFormula]
              rw [hHFormula, hKFormula]
            · exact ⟨hHSource, hKSource, hHWF, hKWF⟩
        | disj A C =>
            have hA_lt : formulaQuantCount A < m := by
              simp [formulaQuantCount] at hCount
              omega
            have hC_lt : formulaQuantCount C < m := by
              simp [formulaQuantCount] at hCount
              omega
            obtain ⟨H, hH⟩ :=
              ih (formulaQuantCount A) hA_lt A rfl hShape.1
            obtain ⟨K, hK⟩ :=
              ih (formulaQuantCount C) hC_lt C rfl hShape.2
            obtain ⟨ciH, hHSource, hHFormula, hHWF⟩ := hH
            obtain ⟨ciK, hKSource, hKFormula, hKWF⟩ := hK
            refine ⟨.disj H K,
              ⟨CInstance.connective false A C ciH ciK, rfl, ?_, ?_⟩⟩
            · simp only [CInstance.toFormula]
              rw [hHFormula, hKFormula]
            · exact ⟨hHSource, hKSource, hHWF, hKWF⟩
        | impl _ _ =>
            exact hShape.elim
        | all x C =>
            let Csub := formulaSubstN C seed.1 x
            have hCsubCount :
                formulaQuantCount Csub = formulaQuantCount C := by
              exact formulaSubst_quantCount C seed.1 x
            have hCsub_lt : formulaQuantCount Csub < m := by
              rw [hCsubCount]
              simp [formulaQuantCount] at hCount
              omega
            have hCsubShape : isSkolemNormalFormShape Csub :=
              isSkolemNormalFormShape_formulaSubstN C seed.1 x hShape
            obtain ⟨H, hH⟩ :=
              ih (formulaQuantCount Csub) hCsub_lt Csub rfl hCsubShape
            obtain ⟨ciH, hHSource, hHFormula, hHWF⟩ := hH
            refine ⟨H,
              ⟨CInstance.forallInst x C seed.1 ciH [] []
                  seed.2 (by intro t ht; simp at ht),
                rfl, ?_, ?_⟩⟩
            · simpa [CInstance.toFormula] using hHFormula
            · exact ⟨by simpa [Csub] using hHSource, hHWF, trivial⟩
        | ex _ _ =>
            exact hShape.elim
  exact construct (formulaQuantCount B) B rfl hSkolem.1

-- ===================================================================
-- Lemma 7.6.2 (companion theorem): iteratedCInstanceCombination
-- ===================================================================

/-- Lemma 7.6.2 (companion theorem): Iterated application of
Lemma 7.6.1 to a structurally nonempty c-instance enumeration.
Given `head :: tail`, applying `g2nnfCInstanceCombination` once per tail
element produces a single c-instance `D` of `B` such that
`D → listConj head tail` is provable. This requires that `B` is in
Skolem normal form (hence in NNF). -/
theorem iteratedCInstanceCombination {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (B : FormulaN L)
    (hNNF : FormulaN.isNNF B)
    (hSkolem : isSkolemNormalForm B)
    (head : FormulaN L)
    (tail : List (FormulaN L))
    (hHead : isCInstanceOf head B)
    (hTail : ∀ C, C ∈ tail → isCInstanceOf C B) :
    ∃ D, isCInstanceOf D B ∧
      Nonempty (G2nnfProofTree hNoEq
        ({D} : LCS.Finset (FormulaN L))
        ({listConj head tail} : LCS.Finset (FormulaN L))) := by
-- BEGIN PROOF
  induction tail generalizing head with
  | nil =>
      refine ⟨head, hHead, ?_⟩
      exact g2nnf_identity_qf (hL := hNoEq) head
        (isCInstanceOf_isNNF head B hHead)
        (isCInstanceOf_isQuantifierFree head B hHead)
  | cons next rest ih =>
      have hNext : isCInstanceOf next B :=
        hTail next List.mem_cons_self
      have hRest :
          ∀ C, C ∈ rest → isCInstanceOf C B := by
        intro C hC
        exact hTail C (List.mem_cons.mpr (Or.inr hC))
      obtain ⟨tailInstance, hTailInstance, ⟨tailTree⟩⟩ :=
        ih next hNext hRest
      obtain ⟨D, hD, ⟨combinationTree⟩⟩ :=
        g2nnfCInstanceCombination (hNoEq := hNoEq) B hNNF hSkolem
          head tailInstance hHead hTailInstance
      obtain ⟨headIdentity⟩ := g2nnf_identity_qf (hL := hNoEq) head
        (isCInstanceOf_isNNF head B hHead)
        (isCInstanceOf_isQuantifierFree head B hHead)
      have hCombinationRect :
          isRectified (.conj head tailInstance) :=
        (G2nnfProofTree.allRectified (hL := hNoEq) combinationTree).2
          (.conj head tailInstance)
          ((LCS.Finset.mem_singleton
            (FormulaN.conj head tailInstance)
            (FormulaN.conj head tailInstance)).mpr rfl)
      have hListRect :
          isRectified (listConj next rest) :=
        (G2nnfProofTree.allRectified (hL := hNoEq) tailTree).2 (listConj next rest)
          ((LCS.Finset.mem_singleton
            (listConj next rest) (listConj next rest)).mpr rfl)
      have hTargetRect :
          isRectified (.conj head (listConj next rest)) :=
        AllRectified.isRectified_of_isQuantifierFree _
          (listConj_isQuantifierFree head (next :: rest)
            (isCInstanceOf_isQuantifierFree head B hHead)
            (fun C hC =>
              isCInstanceOf_isQuantifierFree C B
                (hTail C hC)))
      have hCombinationNNF : (FormulaN.conj head tailInstance).isNNF :=
        (G2nnfDeductionTreeCore.allNNF combinationTree).2 _
          ((LCS.Finset.mem_singleton _ _).mpr rfl)
      have hListNNF : (listConj next rest).isNNF :=
        (G2nnfDeductionTreeCore.allNNF tailTree).2 _
          ((LCS.Finset.mem_singleton _ _).mpr rfl)
      have leftProjection :
          G2nnfProofTree hNoEq
            ({FormulaN.conj head tailInstance} :
              LCS.Finset (FormulaN L))
            ({head} : LCS.Finset (FormulaN L)) :=
        g2nnfConjProjLeft (hNoEq := hNoEq) head tailInstance
          hCombinationNNF hCombinationRect headIdentity
      have rightProjection :
          G2nnfProofTree hNoEq
            ({FormulaN.conj head tailInstance} :
              LCS.Finset (FormulaN L))
            ({listConj next rest} :
              LCS.Finset (FormulaN L)) :=
        .onePremise
          (.conjLeft2 head tailInstance ∅ {listConj next rest}) trivial rfl
          ⟨trivial, allNNF_singletons hCombinationNNF hListNNF,
            (by intro seq h
                simp only [G2nnfRuleCore.premises, List.mem_cons,
                  List.not_mem_nil, or_false] at h
                subst seq; exact G2nnfDeductionTreeCore.allNNF tailTree),
            allRectified_singletons hCombinationRect hListRect⟩
          tailTree
      have conjunctionMap :
          G2nnfProofTree hNoEq
            ({FormulaN.conj head tailInstance} :
              LCS.Finset (FormulaN L))
            ({FormulaN.conj head (listConj next rest)} :
              LCS.Finset (FormulaN L)) :=
        .twoPremise
          (.conjRight head (listConj next rest)
            {FormulaN.conj head tailInstance} ∅) trivial rfl
          ⟨trivial,
            allNNF_singletons hCombinationNNF ⟨hCombinationNNF.1, hListNNF⟩,
            (by intro seq h
                simp only [G2nnfRuleCore.premises, List.mem_cons,
                  List.not_mem_nil, or_false] at h
                rcases h with rfl | rfl
                exact G2nnfDeductionTreeCore.allNNF leftProjection
                exact G2nnfDeductionTreeCore.allNNF rightProjection),
            allRectified_singletons hCombinationRect hTargetRect⟩
          leftProjection rightProjection
      refine ⟨D, hD, ?_⟩
      exact ⟨g2nnfCompose (hL := hNoEq) D
        (FormulaN.conj head tailInstance)
        (FormulaN.conj head (listConj next rest))
        combinationTree conjunctionMap⟩

-- ===================================================================
-- Lemma 7.6.2 (companion theorem): emptySuccedentFromImpl
-- ===================================================================

/-- Lemma 7.6.2 (companion theorem): The final NNF derivation step.
If `D → conj` and `conj →` are provable, cut on `conj` to derive
`D →`. Empty succedents are the proof-theoretic representation of
the corresponding negations; no raw negation of a compound formula
is inserted into a G2nnf sequent. -/
theorem emptySuccedentFromImpl {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (D conj : FormulaN L)
    (hImpl : Nonempty (G2nnfProofTree hNoEq
      ({D} : LCS.Finset (FormulaN L))
      ({conj} : LCS.Finset (FormulaN L))))
    (hConj : Nonempty (G2nnfProofTree hNoEq
      ({conj} : LCS.Finset (FormulaN L))
      (∅ : LCS.Finset (FormulaN L)))) :
    Nonempty (G2nnfProofTree hNoEq
      ({D} : LCS.Finset (FormulaN L))
      (∅ : LCS.Finset (FormulaN L))) := by
-- BEGIN PROOF
  obtain ⟨implTree⟩ := hImpl
  obtain ⟨conjTree⟩ := hConj
  have result := g2nnfCut (hL := hNoEq) (Γ := {D}) (Δ := ∅) (Λ := ∅) (Θ := ∅)
    conj implTree conjTree
  have hLeft : LCS.Finset.union ({D} : LCS.Finset (FormulaN L)) ∅ = {D} := by
    apply LCS.Finset.ext
    intro F
    simp [LCS.Finset.mem_union, LCS.Finset.mem_empty]
  have hRight : LCS.Finset.union (∅ : LCS.Finset (FormulaN L))
      (∅ : LCS.Finset (FormulaN L)) = (∅ : LCS.Finset (FormulaN L)) := by
    apply LCS.Finset.ext
    intro F
    simp [LCS.Finset.mem_union, LCS.Finset.mem_empty]
  rw [hLeft, hRight] at result
  exact ⟨result⟩

-- ===================================================================
-- Helper: Skolem form is in Skolem normal form
-- ===================================================================

/-- Helper (Def 7.6.2 auxiliary metric): Counts `.ex` nodes in a `FormulaN`.
Used to phrase the Skolem-allocation side-condition
`i + countExN A ≤ S.n` which captures "the spec allocates at least one
Skolem symbol per existential subformula of the formula being
transformed, given that `i` symbols have already been consumed". Since
`formulaSubstN` substitutes terms (containing no quantifiers) it
preserves `countExN`, and `liftFormulaSkolem` also preserves it — these
facts let the side-condition propagate through `skolemFormAux`. -/
def countExN {L : Language} : FormulaN L → Nat
  | .predN _ _ => 0
  | .eq_ _ _ _ => 0
  | .neg A => countExN A
  | .conj A B => countExN A + countExN B
  | .disj A B => countExN A + countExN B
  | .impl A B => countExN A + countExN B
  | .all _ B => countExN B
  | .ex _ B => 1 + countExN B

/-- Helper: term-substitution preserves `countExN` (substitution replaces
variables with terms, and terms contain no quantifiers). -/
theorem formulaSubstN_countExN {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) :
    countExN (formulaSubstN A t x) = countExN A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg _ ih => simp [formulaSubstN, countExN, ih]
  | conj A B ihA ihB => simp [formulaSubstN, countExN, ihA, ihB]
  | disj A B ihA ihB => simp [formulaSubstN, countExN, ihA, ihB]
  | impl A B ihA ihB => simp [formulaSubstN, countExN, ihA, ihB]
  | all y B ih =>
    simp [formulaSubstN, countExN]
    try split <;> simp [countExN, ih]
  | ex y B ih =>
    simp [formulaSubstN, countExN]
    try split <;> simp [countExN, ih]

/-- Helper: lifting a formula into the Skolem-extended language preserves
`countExN`. The lift rewraps constant and function symbols at the term
level; the formula structure (quantifiers, connectives) is
untouched. -/
theorem liftFormulaSkolem_countExN {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat} (A : FormulaN L) :
    countExN (liftFormulaSkolem (skolemRank := skolemRank) A) = countExN A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg _ ih => simp [liftFormulaSkolem, countExN, ih]
  | conj _ _ ihA ihB => simp [liftFormulaSkolem, countExN, ihA, ihB]
  | disj _ _ ihA ihB => simp [liftFormulaSkolem, countExN, ihA, ihB]
  | impl _ _ ihA ihB => simp [liftFormulaSkolem, countExN, ihA, ihB]
  | all _ _ ih => simp [liftFormulaSkolem, countExN, ih]
  | ex _ _ ih => simp [liftFormulaSkolem, countExN, ih]

/-- Helper: lifting a formula into the Skolem-extended language preserves
NNF. Term-level rewrapping does not disturb the formula-level shape, so
the clauses defining `isNNF` (atomic, neg-atomic, conj, disj, all, ex)
each match before and after the lift. -/
theorem liftFormulaSkolem_isNNF {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat} (A : FormulaN L) :
    A.isNNF → (liftFormulaSkolem (skolemRank := skolemRank) A).isNNF := by
-- BEGIN PROOF
  intro h
  induction A with
  | predN _ _ => exact trivial
  | eq_ _ _ _ => exact trivial
  | neg B _ =>
    cases B with
    | predN _ _ => exact trivial
    | eq_ _ _ _ => exact trivial
    | _ => exact h.elim
  | conj _ _ ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | disj _ _ ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | impl _ _ _ _ => exact h.elim
  | all _ _ ih => exact ih h
  | ex _ _ ih => exact ih h

/-- Every free variable of an exact Skolem term is one of the variables
in that allocation's ordered universal scope. -/
theorem exactSkolemTerm_fv {L : Language} (S : SkolemSpec L)
    (i : Fin S.n) :
    ∀ y ∈ termFV (exactSkolemTerm S i), y ∈ S.skolemScope i := by
  intro y hy
  unfold exactSkolemTerm at hy
  split at hy
  · exact hy.elim
  · change ∃ k, _ at hy
    obtain ⟨k, hk⟩ := hy
    change y = (S.skolemScope i).get k at hk
    rw [hk]
    exact List.get_mem _ _

/-- The exact allocation traversal preserves NNF and eliminates every
existential on any successful descriptor-count-sized run. -/
theorem skolemFormExactAux_shape_nnf {L : Language}
    (S : SkolemSpec L) :
    ∀ (m : Nat) (A : FormulaN S.language) (scope : List Nat)
      (indices : List (Fin S.n)) (B : FormulaN S.language) (used : Nat),
      formulaQuantCount A = m →
      FormulaN.isNNF A →
      indices.length = skolemDescriptorCount A →
      skolemFormExactAux S A scope indices = some (B, used) →
      FormulaN.isNNF B ∧ isSkolemNormalFormShape B := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro A scope indices Out used hCount hNNF hLength hRun
    match A, hCount, hNNF, hLength with
    | .predN P ts, _, _, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.predN P ts) scope [] =
            some (.predN P ts, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact ⟨trivial, trivial⟩
    | .eq_ h t₁ t₂, _, _, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.eq_ h t₁ t₂) scope [] =
            some (.eq_ h t₁ t₂, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact ⟨trivial, trivial⟩
    | .neg B, _, hNNF, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.neg B) scope [] =
            some (.neg B, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      cases B with
      | predN _ _ =>
        exact ⟨trivial, by
          simp [isSkolemNormalFormShape, FormulaN.isAtomic]⟩
      | eq_ _ _ _ =>
        exact ⟨trivial, by
          simp [isSkolemNormalFormShape, FormulaN.isAtomic]⟩
      | _ => exact hNNF.elim
    | .conj A B, hCount, hNNF, hLength =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qA : formulaQuantCount A < m := by omega
      have qB : formulaQuantCount B < m := by omega
      have hALe : skolemDescriptorCount A ≤ indices.length := by
        rw [hLength]
        exact Nat.le_add_right _ _
      have hLeftLength :
          (indices.take (skolemDescriptorCount A)).length =
            skolemDescriptorCount A :=
        List.length_take_of_le hALe
      have hRightLength :
          (indices.drop (skolemDescriptorCount A)).length =
            skolemDescriptorCount B := by
        rw [List.length_drop, hLength]
        simp [skolemDescriptorCount]
      obtain ⟨A', hA'⟩ :=
        skolemFormExactAux_result S _ A scope
          (indices.take (skolemDescriptorCount A)) rfl hLeftLength
      obtain ⟨B', hB'⟩ :=
        skolemFormExactAux_result S _ B scope
          (indices.drop (skolemDescriptorCount A)) rfl hRightLength
      have hPropA :=
        ih _ qA A scope (indices.take (skolemDescriptorCount A))
          A' _ rfl hNNF.1 hLeftLength hA'
      have hPropB :=
        ih _ qB B scope (indices.drop (skolemDescriptorCount A))
          B' _ rfl hNNF.2 hRightLength hB'
      have hCanonical :
          skolemFormExactAux S (.conj A B) scope indices =
            some (.conj A' B',
              skolemDescriptorCount A + skolemDescriptorCount B) := by
        simp [skolemFormExactAux, hA', hB']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact ⟨⟨hPropA.1, hPropB.1⟩, ⟨hPropA.2, hPropB.2⟩⟩
    | .disj A B, hCount, hNNF, hLength =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qA : formulaQuantCount A < m := by omega
      have qB : formulaQuantCount B < m := by omega
      have hALe : skolemDescriptorCount A ≤ indices.length := by
        rw [hLength]
        exact Nat.le_add_right _ _
      have hLeftLength :
          (indices.take (skolemDescriptorCount A)).length =
            skolemDescriptorCount A :=
        List.length_take_of_le hALe
      have hRightLength :
          (indices.drop (skolemDescriptorCount A)).length =
            skolemDescriptorCount B := by
        rw [List.length_drop, hLength]
        simp [skolemDescriptorCount]
      obtain ⟨A', hA'⟩ :=
        skolemFormExactAux_result S _ A scope
          (indices.take (skolemDescriptorCount A)) rfl hLeftLength
      obtain ⟨B', hB'⟩ :=
        skolemFormExactAux_result S _ B scope
          (indices.drop (skolemDescriptorCount A)) rfl hRightLength
      have hPropA :=
        ih _ qA A scope (indices.take (skolemDescriptorCount A))
          A' _ rfl hNNF.1 hLeftLength hA'
      have hPropB :=
        ih _ qB B scope (indices.drop (skolemDescriptorCount A))
          B' _ rfl hNNF.2 hRightLength hB'
      have hCanonical :
          skolemFormExactAux S (.disj A B) scope indices =
            some (.disj A' B',
              skolemDescriptorCount A + skolemDescriptorCount B) := by
        simp [skolemFormExactAux, hA', hB']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact ⟨⟨hPropA.1, hPropB.1⟩, ⟨hPropA.2, hPropB.2⟩⟩
    | .impl _ _, _, hNNF, _ => exact hNNF.elim
    | .all x B, hCount, hNNF, hLength =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qB : formulaQuantCount B < m := by omega
      have hBodyLength :
          indices.length = skolemDescriptorCount B := by
        simpa [skolemDescriptorCount] using hLength
      obtain ⟨B', hB'⟩ :=
        skolemFormExactAux_result S _ B (scope ++ [x])
          indices rfl hBodyLength
      have hPropB :=
        ih _ qB B (scope ++ [x]) indices B' _
          rfl hNNF hBodyLength hB'
      have hCanonical :
          skolemFormExactAux S (.all x B) scope indices =
            some (.all x B', skolemDescriptorCount B) := by
        simp [skolemFormExactAux, hB']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact hPropB
    | .ex x B, hCount, hNNF, hLength =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      cases indices with
      | nil =>
        simp [skolemDescriptorCount] at hLength
        omega
      | cons i rest =>
        have hRestLength :
            rest.length = skolemDescriptorCount B := by
          simp [skolemDescriptorCount] at hLength
          omega
        let BSub := formulaSubstN B (exactSkolemTerm S i) x
        have qBSub : formulaQuantCount BSub < m := by
          simp only [BSub]
          rw [formulaSubst_quantCount]
          omega
        have hNNFSub : FormulaN.isNNF BSub :=
          isNNF_formulaSubstN B _ _ hNNF
        have hSubLength :
            rest.length = skolemDescriptorCount BSub := by
          rw [formulaSubstN_descriptorCount]
          exact hRestLength
        obtain ⟨B', hB'⟩ :=
          skolemFormExactAux_result S _ BSub scope rest rfl hSubLength
        have hPropB :=
          ih _ qBSub BSub scope rest B' _
            rfl hNNFSub hSubLength hB'
        have hCanonical :
            skolemFormExactAux S (.ex x B) scope (i :: rest) =
              some (B', skolemDescriptorCount BSub + 1) := by
          simp [skolemFormExactAux, skolemSubst, BSub, hB']
        have hOut := skolemFormExactAux_formula_unique hCanonical hRun
        subst Out
        exact hPropB

/-- On an allocation-aligned run, every free variable of the exact
traversal's output belongs to the current universal scope, provided
the same is true of the input. The scope-alignment hypothesis is what
connects each consumed index to its exact descriptor occurrence. -/
theorem skolemFormExactAux_fv_bound {L : Language}
    (S : SkolemSpec L) :
    ∀ (m : Nat) (A : FormulaN S.language) (scope : List Nat)
      (indices : List (Fin S.n)) (B : FormulaN S.language) (used : Nat),
      formulaQuantCount A = m →
      FormulaN.isNNF A →
      indices.length = skolemDescriptorCount A →
      indices.map S.skolemScope = existentialScopesAux A scope →
      skolemFormExactAux S A scope indices = some (B, used) →
      (∀ y ∈ formulaFVN A, y ∈ scope) →
      ∀ y ∈ formulaFVN B, y ∈ scope := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro A scope indices Out used hCount hNNF hLength hScopes hRun hFV
    match A, hCount, hNNF, hLength with
    | .predN P ts, _, _, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.predN P ts) scope [] =
            some (.predN P ts, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact hFV
    | .eq_ h t₁ t₂, _, _, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.eq_ h t₁ t₂) scope [] =
            some (.eq_ h t₁ t₂, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact hFV
    | .neg C, _, hNNF, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.neg C) scope [] =
            some (.neg C, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact hFV
    | .conj C D, hCount, hNNF, hLength =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qC : formulaQuantCount C < m := by omega
      have qD : formulaQuantCount D < m := by omega
      have hCLe : skolemDescriptorCount C ≤ indices.length := by
        rw [hLength]
        exact Nat.le_add_right _ _
      have hLeftLength :
          (indices.take (skolemDescriptorCount C)).length =
            skolemDescriptorCount C :=
        List.length_take_of_le hCLe
      have hRightLength :
          (indices.drop (skolemDescriptorCount C)).length =
            skolemDescriptorCount D := by
        rw [List.length_drop, hLength]
        simp [skolemDescriptorCount]
      have hLeftScopes :
          (indices.take (skolemDescriptorCount C)).map S.skolemScope =
            existentialScopesAux C scope := by
        calc
          _ = (indices.map S.skolemScope).take
                (skolemDescriptorCount C) := List.map_take
          _ = (existentialScopesAux C scope ++
                existentialScopesAux D scope).take
                (skolemDescriptorCount C) := by
              rw [hScopes]
              rfl
          _ = existentialScopesAux C scope := by
              rw [← existentialScopesAux_length C scope]
              exact List.take_left
      have hRightScopes :
          (indices.drop (skolemDescriptorCount C)).map S.skolemScope =
            existentialScopesAux D scope := by
        calc
          _ = (indices.map S.skolemScope).drop
                (skolemDescriptorCount C) := List.map_drop
          _ = (existentialScopesAux C scope ++
                existentialScopesAux D scope).drop
                (skolemDescriptorCount C) := by
              rw [hScopes]
              rfl
          _ = existentialScopesAux D scope := by
              rw [← existentialScopesAux_length C scope]
              exact List.drop_left
      obtain ⟨C', hC'⟩ :=
        skolemFormExactAux_result S _ C scope
          (indices.take (skolemDescriptorCount C)) rfl hLeftLength
      obtain ⟨D', hD'⟩ :=
        skolemFormExactAux_result S _ D scope
          (indices.drop (skolemDescriptorCount C)) rfl hRightLength
      have hFVC : ∀ y ∈ formulaFVN C, y ∈ scope := by
        intro y hy
        exact hFV y (Or.inl hy)
      have hFVD : ∀ y ∈ formulaFVN D, y ∈ scope := by
        intro y hy
        exact hFV y (Or.inr hy)
      have hPropC :=
        ih _ qC C scope (indices.take (skolemDescriptorCount C))
          C' _ rfl hNNF.1 hLeftLength hLeftScopes hC' hFVC
      have hPropD :=
        ih _ qD D scope (indices.drop (skolemDescriptorCount C))
          D' _ rfl hNNF.2 hRightLength hRightScopes hD' hFVD
      have hCanonical :
          skolemFormExactAux S (.conj C D) scope indices =
            some (.conj C' D',
              skolemDescriptorCount C + skolemDescriptorCount D) := by
        simp [skolemFormExactAux, hC', hD']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      intro y hy
      rcases hy with hy | hy
      · exact hPropC y hy
      · exact hPropD y hy
    | .disj C D, hCount, hNNF, hLength =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qC : formulaQuantCount C < m := by omega
      have qD : formulaQuantCount D < m := by omega
      have hCLe : skolemDescriptorCount C ≤ indices.length := by
        rw [hLength]
        exact Nat.le_add_right _ _
      have hLeftLength :
          (indices.take (skolemDescriptorCount C)).length =
            skolemDescriptorCount C :=
        List.length_take_of_le hCLe
      have hRightLength :
          (indices.drop (skolemDescriptorCount C)).length =
            skolemDescriptorCount D := by
        rw [List.length_drop, hLength]
        simp [skolemDescriptorCount]
      have hLeftScopes :
          (indices.take (skolemDescriptorCount C)).map S.skolemScope =
            existentialScopesAux C scope := by
        calc
          _ = (indices.map S.skolemScope).take
                (skolemDescriptorCount C) := List.map_take
          _ = (existentialScopesAux C scope ++
                existentialScopesAux D scope).take
                (skolemDescriptorCount C) := by
              rw [hScopes]
              rfl
          _ = existentialScopesAux C scope := by
              rw [← existentialScopesAux_length C scope]
              exact List.take_left
      have hRightScopes :
          (indices.drop (skolemDescriptorCount C)).map S.skolemScope =
            existentialScopesAux D scope := by
        calc
          _ = (indices.map S.skolemScope).drop
                (skolemDescriptorCount C) := List.map_drop
          _ = (existentialScopesAux C scope ++
                existentialScopesAux D scope).drop
                (skolemDescriptorCount C) := by
              rw [hScopes]
              rfl
          _ = existentialScopesAux D scope := by
              rw [← existentialScopesAux_length C scope]
              exact List.drop_left
      obtain ⟨C', hC'⟩ :=
        skolemFormExactAux_result S _ C scope
          (indices.take (skolemDescriptorCount C)) rfl hLeftLength
      obtain ⟨D', hD'⟩ :=
        skolemFormExactAux_result S _ D scope
          (indices.drop (skolemDescriptorCount C)) rfl hRightLength
      have hFVC : ∀ y ∈ formulaFVN C, y ∈ scope := by
        intro y hy
        exact hFV y (Or.inl hy)
      have hFVD : ∀ y ∈ formulaFVN D, y ∈ scope := by
        intro y hy
        exact hFV y (Or.inr hy)
      have hPropC :=
        ih _ qC C scope (indices.take (skolemDescriptorCount C))
          C' _ rfl hNNF.1 hLeftLength hLeftScopes hC' hFVC
      have hPropD :=
        ih _ qD D scope (indices.drop (skolemDescriptorCount C))
          D' _ rfl hNNF.2 hRightLength hRightScopes hD' hFVD
      have hCanonical :
          skolemFormExactAux S (.disj C D) scope indices =
            some (.disj C' D',
              skolemDescriptorCount C + skolemDescriptorCount D) := by
        simp [skolemFormExactAux, hC', hD']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      intro y hy
      rcases hy with hy | hy
      · exact hPropC y hy
      · exact hPropD y hy
    | .impl _ _, _, hNNF, _ => exact hNNF.elim
    | .all x C, hCount, hNNF, hLength =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qC : formulaQuantCount C < m := by omega
      have hBodyLength :
          indices.length = skolemDescriptorCount C := by
        simpa [skolemDescriptorCount] using hLength
      have hBodyScopes :
          indices.map S.skolemScope =
            existentialScopesAux C (scope ++ [x]) := by
        simpa [existentialScopesAux] using hScopes
      obtain ⟨C', hC'⟩ :=
        skolemFormExactAux_result S _ C (scope ++ [x])
          indices rfl hBodyLength
      have hFVC : ∀ y ∈ formulaFVN C, y ∈ scope ++ [x] := by
        intro y hy
        by_cases hyx : y = x
        · subst y
          simp
        · apply List.mem_append.mpr
          apply Or.inl
          apply hFV y
          exact ⟨hy, fun hxy => hyx hxy⟩
      have hPropC :=
        ih _ qC C (scope ++ [x]) indices C' _
          rfl hNNF hBodyLength hBodyScopes hC' hFVC
      have hCanonical :
          skolemFormExactAux S (.all x C) scope indices =
            some (.all x C', skolemDescriptorCount C) := by
        simp [skolemFormExactAux, hC']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      intro y hy
      obtain ⟨hyC, hyNe⟩ := hy
      rcases List.mem_append.mp (hPropC y hyC) with hyScope | hyLast
      · exact hyScope
      · have hyEq : y = x := List.mem_singleton.mp hyLast
        exact absurd hyEq hyNe
    | .ex x C, hCount, hNNF, hLength =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      cases indices with
      | nil =>
        simp [skolemDescriptorCount] at hLength
        omega
      | cons i rest =>
        have hRestLength :
            rest.length = skolemDescriptorCount C := by
          simp [skolemDescriptorCount] at hLength
          omega
        have hScopesAt := hScopes
        simp only [List.map_cons, existentialScopesAux] at hScopesAt
        have hHeadScope : S.skolemScope i = scope :=
          (List.cons.inj hScopesAt).1
        have hRestScopes :
            rest.map S.skolemScope = existentialScopesAux C scope :=
          (List.cons.inj hScopesAt).2
        let CSub := formulaSubstN C (exactSkolemTerm S i) x
        have qCSub : formulaQuantCount CSub < m := by
          simp only [CSub]
          rw [formulaSubst_quantCount]
          omega
        have hNNFSub : FormulaN.isNNF CSub :=
          isNNF_formulaSubstN C _ _ hNNF
        have hSubLength :
            rest.length = skolemDescriptorCount CSub := by
          rw [formulaSubstN_descriptorCount]
          exact hRestLength
        have hSubScopes :
            rest.map S.skolemScope =
              existentialScopesAux CSub scope := by
          rw [existentialScopesAux_formulaSubstN]
          exact hRestScopes
        obtain ⟨C', hC'⟩ :=
          skolemFormExactAux_result S _ CSub scope rest rfl hSubLength
        have hFVSub : ∀ y ∈ formulaFVN CSub, y ∈ scope := by
          intro y hy
          rcases LCS.FirstOrder.Gentzen.Hintikka.formulaFVN_formulaSubstN
              C (exactSkolemTerm S i) x y hy with
            ⟨hyC, hyNe⟩ | hyTerm
          · exact hFV y ⟨hyC, hyNe⟩
          · rw [← hHeadScope]
            exact exactSkolemTerm_fv S i y hyTerm
        have hPropC :=
          ih _ qCSub CSub scope rest C' _
            rfl hNNFSub hSubLength hSubScopes hC' hFVSub
        have hCanonical :
            skolemFormExactAux S (.ex x C) scope (i :: rest) =
              some (C', skolemDescriptorCount CSub + 1) := by
          simp [skolemFormExactAux, skolemSubst, CSub, hC']
        have hOut := skolemFormExactAux_formula_unique hCanonical hRun
        subst Out
        exact hPropC

/-- Exact Skolemization never introduces a bound variable. Every
bound variable in a successful output was already bound in the input. -/
theorem skolemFormExactAux_bv_bound {L : Language}
    (S : SkolemSpec L) :
    ∀ (m : Nat) (A : FormulaN S.language) (scope : List Nat)
      (indices : List (Fin S.n)) (B : FormulaN S.language) (used : Nat),
      formulaQuantCount A = m →
      FormulaN.isNNF A →
      indices.length = skolemDescriptorCount A →
      skolemFormExactAux S A scope indices = some (B, used) →
      ∀ y ∈ formulaBVN B, y ∈ formulaBVN A := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro A scope indices Out used hCount hNNF hLength hRun
    match A, hCount, hNNF, hLength with
    | .predN P ts, _, _, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.predN P ts) scope [] =
            some (.predN P ts, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact fun _ hy => hy
    | .eq_ h t₁ t₂, _, _, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.eq_ h t₁ t₂) scope [] =
            some (.eq_ h t₁ t₂, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact fun _ hy => hy
    | .neg C, _, hNNF, hLength =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.neg C) scope [] =
            some (.neg C, 0) := by
        simp [skolemFormExactAux]
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact fun _ hy => hy
    | .conj C D, hCount, hNNF, hLength =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qC : formulaQuantCount C < m := by omega
      have qD : formulaQuantCount D < m := by omega
      have hCLe : skolemDescriptorCount C ≤ indices.length := by
        rw [hLength]
        exact Nat.le_add_right _ _
      have hLeftLength :
          (indices.take (skolemDescriptorCount C)).length =
            skolemDescriptorCount C :=
        List.length_take_of_le hCLe
      have hRightLength :
          (indices.drop (skolemDescriptorCount C)).length =
            skolemDescriptorCount D := by
        rw [List.length_drop, hLength]
        simp [skolemDescriptorCount]
      obtain ⟨C', hC'⟩ :=
        skolemFormExactAux_result S _ C scope
          (indices.take (skolemDescriptorCount C)) rfl hLeftLength
      obtain ⟨D', hD'⟩ :=
        skolemFormExactAux_result S _ D scope
          (indices.drop (skolemDescriptorCount C)) rfl hRightLength
      have hPropC :=
        ih _ qC C scope (indices.take (skolemDescriptorCount C))
          C' _ rfl hNNF.1 hLeftLength hC'
      have hPropD :=
        ih _ qD D scope (indices.drop (skolemDescriptorCount C))
          D' _ rfl hNNF.2 hRightLength hD'
      have hCanonical :
          skolemFormExactAux S (.conj C D) scope indices =
            some (.conj C' D',
              skolemDescriptorCount C + skolemDescriptorCount D) := by
        simp [skolemFormExactAux, hC', hD']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      intro y hy
      rcases hy with hy | hy
      · exact Or.inl (hPropC y hy)
      · exact Or.inr (hPropD y hy)
    | .disj C D, hCount, hNNF, hLength =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qC : formulaQuantCount C < m := by omega
      have qD : formulaQuantCount D < m := by omega
      have hCLe : skolemDescriptorCount C ≤ indices.length := by
        rw [hLength]
        exact Nat.le_add_right _ _
      have hLeftLength :
          (indices.take (skolemDescriptorCount C)).length =
            skolemDescriptorCount C :=
        List.length_take_of_le hCLe
      have hRightLength :
          (indices.drop (skolemDescriptorCount C)).length =
            skolemDescriptorCount D := by
        rw [List.length_drop, hLength]
        simp [skolemDescriptorCount]
      obtain ⟨C', hC'⟩ :=
        skolemFormExactAux_result S _ C scope
          (indices.take (skolemDescriptorCount C)) rfl hLeftLength
      obtain ⟨D', hD'⟩ :=
        skolemFormExactAux_result S _ D scope
          (indices.drop (skolemDescriptorCount C)) rfl hRightLength
      have hPropC :=
        ih _ qC C scope (indices.take (skolemDescriptorCount C))
          C' _ rfl hNNF.1 hLeftLength hC'
      have hPropD :=
        ih _ qD D scope (indices.drop (skolemDescriptorCount C))
          D' _ rfl hNNF.2 hRightLength hD'
      have hCanonical :
          skolemFormExactAux S (.disj C D) scope indices =
            some (.disj C' D',
              skolemDescriptorCount C + skolemDescriptorCount D) := by
        simp [skolemFormExactAux, hC', hD']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      intro y hy
      rcases hy with hy | hy
      · exact Or.inl (hPropC y hy)
      · exact Or.inr (hPropD y hy)
    | .impl _ _, _, hNNF, _ => exact hNNF.elim
    | .all x C, hCount, hNNF, hLength =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qC : formulaQuantCount C < m := by omega
      have hBodyLength :
          indices.length = skolemDescriptorCount C := by
        simpa [skolemDescriptorCount] using hLength
      obtain ⟨C', hC'⟩ :=
        skolemFormExactAux_result S _ C (scope ++ [x])
          indices rfl hBodyLength
      have hPropC :=
        ih _ qC C (scope ++ [x]) indices C' _
          rfl hNNF hBodyLength hC'
      have hCanonical :
          skolemFormExactAux S (.all x C) scope indices =
            some (.all x C', skolemDescriptorCount C) := by
        simp [skolemFormExactAux, hC']
      have hOut := skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      intro y hy
      rcases hy with hy | hy
      · exact Or.inl (hPropC y hy)
      · exact Or.inr hy
    | .ex x C, hCount, hNNF, hLength =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      cases indices with
      | nil =>
        simp [skolemDescriptorCount] at hLength
        omega
      | cons i rest =>
        have hRestLength :
            rest.length = skolemDescriptorCount C := by
          simp [skolemDescriptorCount] at hLength
          omega
        let CSub := formulaSubstN C (exactSkolemTerm S i) x
        have qCSub : formulaQuantCount CSub < m := by
          simp only [CSub]
          rw [formulaSubst_quantCount]
          omega
        have hNNFSub : FormulaN.isNNF CSub :=
          isNNF_formulaSubstN C _ _ hNNF
        have hSubLength :
            rest.length = skolemDescriptorCount CSub := by
          rw [formulaSubstN_descriptorCount]
          exact hRestLength
        obtain ⟨C', hC'⟩ :=
          skolemFormExactAux_result S _ CSub scope rest rfl hSubLength
        have hPropC :=
          ih _ qCSub CSub scope rest C' _
            rfl hNNFSub hSubLength hC'
        have hCanonical :
            skolemFormExactAux S (.ex x C) scope (i :: rest) =
              some (C', skolemDescriptorCount CSub + 1) := by
          simp [skolemFormExactAux, skolemSubst, CSub, hC']
        have hOut := skolemFormExactAux_formula_unique hCanonical hRun
        subst Out
        intro y hy
        apply Or.inl
        rw [← LCS.CutElim.Interpolation.formulaBV_formulaSubst
          C (exactSkolemTerm S i) x]
        exact hPropC y hy

/-- Core preservation lemma for `skolemFormAux`: starting from an
NNF input `A` with a sufficient Skolem-symbol allocation
(`i + countExN A ≤ S.n`), the output is NNF, has Skolem-normal-form
shape (no `.ex` remaining), and the returned counter is exactly
`i + countExN A` (every existential consumed one symbol). Strong
induction on `formulaQuantCount A`, matching each clause of
`skolemFormAux`. The allocation side-condition ensures the `.ex`
branch always takes its `i < S.n` path, so no `.ex` leaks into the
output. -/
theorem skolemFormAux_shape_nnf_counter {L : Language} (S : SkolemSpec L) :
    ∀ (m : Nat) (A : FormulaN S.language) (scope : List Nat) (i : Nat),
      formulaQuantCount A = m →
      FormulaN.isNNF A →
      i + countExN A ≤ S.n →
      FormulaN.isNNF (skolemFormAux S A scope i).1 ∧
      isSkolemNormalFormShape (skolemFormAux S A scope i).1 ∧
      (skolemFormAux S A scope i).2 = i + countExN A := by
-- BEGIN PROOF
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro A scope i hCount hNNF hAlloc
    unfold skolemFormAux
    match A, hCount, hNNF, hAlloc with
    | .predN _ _, _, _, _ =>
      exact ⟨trivial, trivial, by simp [countExN]⟩
    | .eq_ _ _ _, _, _, _ =>
      exact ⟨trivial, trivial, by simp [countExN]⟩
    | .neg B, _, hNNF, _ =>
      cases B with
      | predN _ _ =>
        refine ⟨trivial, ?_, by simp [countExN]⟩
        simp [isSkolemNormalFormShape, FormulaN.isAtomic]
      | eq_ _ _ _ =>
        refine ⟨trivial, ?_, by simp [countExN]⟩
        simp [isSkolemNormalFormShape, FormulaN.isAtomic]
      | _ => exact hNNF.elim
    | .conj B C, hCount, hNNF, hAlloc =>
      have hB : FormulaN.isNNF B := hNNF.1
      have hC : FormulaN.isNNF C := hNNF.2
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have hAllocAt := hAlloc
      simp [countExN] at hAllocAt
      have qB : formulaQuantCount B < m := by omega
      have qC : formulaQuantCount C < m := by omega
      have hAllocB : i + countExN B ≤ S.n := by omega
      have ihB := ih _ qB B scope i rfl hB hAllocB
      simp only
      generalize hBres : skolemFormAux S B scope i = Bres at ihB
      obtain ⟨B', i'⟩ := Bres
      have hi' : i' = i + countExN B := ihB.2.2
      have hAllocC : i' + countExN C ≤ S.n := by rw [hi']; omega
      have ihC := ih _ qC C scope i' rfl hC hAllocC
      generalize hCres : skolemFormAux S C scope i' = Cres at ihC
      obtain ⟨C', i''⟩ := Cres
      have hi'' : i'' = i' + countExN C := ihC.2.2
      exact ⟨⟨ihB.1, ihC.1⟩, ⟨ihB.2.1, ihC.2.1⟩,
        by simp [countExN]; omega⟩
    | .disj B C, hCount, hNNF, hAlloc =>
      have hB : FormulaN.isNNF B := hNNF.1
      have hC : FormulaN.isNNF C := hNNF.2
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have hAllocAt := hAlloc
      simp [countExN] at hAllocAt
      have qB : formulaQuantCount B < m := by omega
      have qC : formulaQuantCount C < m := by omega
      have hAllocB : i + countExN B ≤ S.n := by omega
      have ihB := ih _ qB B scope i rfl hB hAllocB
      simp only
      generalize hBres : skolemFormAux S B scope i = Bres at ihB
      obtain ⟨B', i'⟩ := Bres
      have hi' : i' = i + countExN B := ihB.2.2
      have hAllocC : i' + countExN C ≤ S.n := by rw [hi']; omega
      have ihC := ih _ qC C scope i' rfl hC hAllocC
      generalize hCres : skolemFormAux S C scope i' = Cres at ihC
      obtain ⟨C', i''⟩ := Cres
      have hi'' : i'' = i' + countExN C := ihC.2.2
      exact ⟨⟨ihB.1, ihC.1⟩, ⟨ihB.2.1, ihC.2.1⟩,
        by simp [countExN]; omega⟩
    | .impl _ _, _, hNNF, _ => exact hNNF.elim
    | .all x B, hCount, hNNF, hAlloc =>
      have hB : FormulaN.isNNF B := hNNF
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have hAllocAt := hAlloc
      simp [countExN] at hAllocAt
      have qB : formulaQuantCount B < m := by omega
      have hAllocB : i + countExN B ≤ S.n := by
        simp [countExN] at hAlloc; omega
      have ihB := ih _ qB B (scope ++ [x]) i rfl hB hAllocB
      simp only
      generalize hBres : skolemFormAux S B (scope ++ [x]) i = Bres at ihB
      obtain ⟨B', i'⟩ := Bres
      exact ⟨ihB.1, ihB.2.1, by simp [countExN]; exact ihB.2.2⟩
    | .ex x B, hCount, hNNF, hAlloc =>
      have hB : FormulaN.isNNF B := hNNF
      -- Allocation guarantees `i < S.n`.
      have hlt : i < S.n := by
        have := hAlloc
        simp [countExN] at this
        omega
      simp only [hlt, ↓reduceDIte]
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      -- Introduce the Skolem term as a definitional abbreviation via `let`.
      let skolemTerm : Term S.language :=
        if hRank : S.skolemRank ⟨i, hlt⟩ = 0 then
          Term.const (.inr ⟨⟨i, hlt⟩, hRank⟩)
        else
          Term.func (.inr ⟨⟨i, hlt⟩, Nat.pos_of_ne_zero hRank⟩) fun k =>
            match hLen : scope.length with
            | 0 => Term.var x
            | _ + 1 =>
              Term.var (scope.get ⟨k.val % scope.length, by
                rw [hLen]; exact Nat.mod_lt _ (by omega)⟩)
      have qBsub : formulaQuantCount (formulaSubstN B skolemTerm x) < m := by
        rw [formulaSubst_quantCount]; omega
      have hB_subNNF : FormulaN.isNNF (formulaSubstN B skolemTerm x) :=
        isNNF_formulaSubstN B _ _ hB
      have hAllocB_sub :
          (i + 1) + countExN (formulaSubstN B skolemTerm x) ≤ S.n := by
        rw [formulaSubstN_countExN]
        simp [countExN] at hAlloc; omega
      have ihBsub := ih _ qBsub _ scope (i + 1) rfl hB_subNNF hAllocB_sub
      have hsnd :
          (skolemFormAux S (formulaSubstN B skolemTerm x) scope (i + 1)).2
            = i + countExN (FormulaN.ex x B) := by
        rw [ihBsub.2.2, formulaSubstN_countExN]
        simp [countExN]; omega
      exact ⟨ihBsub.1, ihBsub.2.1, hsnd⟩

/-- Helper: lifting a term into the Skolem-extended language preserves
its free-variable set. The lift embeds constant and function symbols
and leaves variables unchanged. -/
theorem liftTermSkolem_termFV {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat} (t : Term L) :
    termFV (liftTermSkolem (skolemRank := skolemRank) t) = termFV t := by
-- BEGIN PROOF
  induction t with
  | var _ => rfl
  | const _ => rfl
  | func f ts ih =>
    simp only [liftTermSkolem, termFV]
    ext y
    show (∃ j, termFV (liftTermSkolem (ts j)) y) ↔ (∃ j, termFV (ts j) y)
    exact ⟨fun ⟨j, hj⟩ => ⟨j, (ih j) ▸ hj⟩,
           fun ⟨j, hj⟩ => ⟨j, (ih j).symm ▸ hj⟩⟩

/-- Helper: lifting a formula into the Skolem-extended language preserves
its free-variable set. The lift embeds constant and function symbols
at the term level; quantifier/propositional structure is
untouched, and term-level free variables propagate unchanged via
`liftTermSkolem_termFV`. -/
theorem liftFormulaSkolem_formulaFVN {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat} (A : FormulaN L) :
    formulaFVN (liftFormulaSkolem (skolemRank := skolemRank) A) = formulaFVN A := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    simp only [liftFormulaSkolem, formulaFVN]
    ext y
    show (∃ j, termFV (liftTermSkolem (ts j)) y) ↔ (∃ j, termFV (ts j) y)
    exact ⟨fun ⟨j, hj⟩ => ⟨j, (liftTermSkolem_termFV (ts j)) ▸ hj⟩,
           fun ⟨j, hj⟩ => ⟨j, (liftTermSkolem_termFV (ts j)).symm ▸ hj⟩⟩
  | eq_ _ t1 t2 =>
    simp only [liftFormulaSkolem, formulaFVN,
      liftTermSkolem_termFV]
  | neg _ ih => simp only [liftFormulaSkolem, formulaFVN, ih]
  | conj _ _ ihA ihB => simp only [liftFormulaSkolem, formulaFVN, ihA, ihB]
  | disj _ _ ihA ihB => simp only [liftFormulaSkolem, formulaFVN, ihA, ihB]
  | impl _ _ ihA ihB => simp only [liftFormulaSkolem, formulaFVN, ihA, ihB]
  | all _ _ ih => simp only [liftFormulaSkolem, formulaFVN, ih]
  | ex _ _ ih => simp only [liftFormulaSkolem, formulaFVN, ih]

/-- Helper: lifting a formula into the Skolem-extended language preserves
its bound-variable set. The lift does not add/remove quantifiers, and
BV is defined purely in terms of `.all`/`.ex` binders. -/
theorem liftFormulaSkolem_formulaBVN {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat} (A : FormulaN L) :
    formulaBVN (liftFormulaSkolem (skolemRank := skolemRank) A) = formulaBVN A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg _ ih => simp only [liftFormulaSkolem, formulaBVN, ih]
  | conj _ _ ihA ihB => simp only [liftFormulaSkolem, formulaBVN, ihA, ihB]
  | disj _ _ ihA ihB => simp only [liftFormulaSkolem, formulaBVN, ihA, ihB]
  | impl _ _ ihA ihB => simp only [liftFormulaSkolem, formulaBVN, ihA, ihB]
  | all _ _ ih => simp only [liftFormulaSkolem, formulaBVN, ih]
  | ex _ _ ih => simp only [liftFormulaSkolem, formulaBVN, ih]

/-- Helper: lifting preserves `boundVarsFresh` (FV(A) and BV(A) disjoint).
Both FV and BV are preserved under the lift, so disjointness transfers. -/
theorem liftFormulaSkolem_boundVarsFresh {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat} (A : FormulaN L)
    (h : LCS.FirstOrder.Semantics.Subformulae.boundVarsFresh A) :
    LCS.FirstOrder.Semantics.Subformulae.boundVarsFresh
      (liftFormulaSkolem (skolemRank := skolemRank) A) := by
-- BEGIN PROOF
  intro x ⟨hFV, hBV⟩
  rw [liftFormulaSkolem_formulaFVN] at hFV
  rw [liftFormulaSkolem_formulaBVN] at hBV
  exact h x ⟨hFV, hBV⟩

end LCS.Herbrand.SHGTheorem.Herbrand
end

