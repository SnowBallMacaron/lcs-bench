import LCS.Herbrand.SharpenedHauptsatz.Theorem.Part1

section

namespace LCS.Herbrand.SharpenedHauptsatz.Theorem

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Gentzen

open LCS.CutElim.LK

open LCS.CutElim.LKe

open LCS.CutElim.LKe.Equivalence

open LCS.Herbrand.SharpenedHauptsatz

open LCS.Herbrand.SharpenedHauptsatz.Permutability

open LCS.Herbrand.PrenexForm

helper /-- Theorem 7.3.1 (companion def): The local m measure at a selected
quantifier inference occurrence in LK. It counts propositional-logical rules
strictly below that occurrence, toward the root. Its address distinguishes
repeated copies of the same subtree. The selected inference contributes zero;
cuts contribute zero. -/
def ruleMeasureM {L : Language} {s : Sequent L}
    (T : FOLKProofTree s) (R : LKInferenceOccurrence T) (n : Nat) : Prop :=
  R.rule.isQuantifier ∧ countBelow T R.address = some n
where
  /-- Count strict ancestors on the specified path; invalid addresses fail. -/
  countBelow : {s : Sequent L} → FOLKProofTree s → List Nat → Option Nat
    | _, _, [] => some 0
    | _, .onePremise r t, 0 :: p =>
      let weight := match r with
        | .andLeftL .. | .andLeftR .. | .orRightL .. | .orRightR ..
        | .implRight .. | .negLeft .. | .negRight .. => 1
        | _ => 0
      (countBelow t p).map (fun n => weight + n)
    | _, .twoPremise r t _, 0 :: p =>
      let weight := match r with
        | .andRight .. | .orLeft .. | .implLeft .. => 1
        | .cut .. => 0
      (countBelow t p).map (fun n => weight + n)
    | _, .twoPremise r _ t, 1 :: p =>
      let weight := match r with
        | .andRight .. | .orLeft .. | .implLeft .. => 1
        | .cut .. => 0
      (countBelow t p).map (fun n => weight + n)
    | _, _, _ => none

helper /-- Theorem 7.3.1 (companion def): The local n measure at a selected
quantifier inference occurrence in LK. It counts weakening rules
strictly below that occurrence, toward the root. Its address distinguishes
repeated copies of the same subtree. The selected inference contributes zero;
cuts contribute zero. -/
def ruleMeasureN {L : Language} {s : Sequent L}
    (T : FOLKProofTree s) (R : LKInferenceOccurrence T) (n : Nat) : Prop :=
  R.rule.isQuantifier ∧ countBelow T R.address = some n
where
  /-- Count strict ancestors on the specified path; invalid addresses fail. -/
  countBelow : {s : Sequent L} → FOLKProofTree s → List Nat → Option Nat
    | _, _, [] => some 0
    | _, .onePremise r t, 0 :: p =>
      let weight := match r with
        | .weakenLeft .. | .weakenRight .. => 1
        | _ => 0
      (countBelow t p).map (fun n => weight + n)
    | _, .twoPremise r t _, 0 :: p =>
      countBelow t p
    | _, .twoPremise r _ t, 1 :: p =>
      countBelow t p
    | _, _, _ => none

helper /-- Theorem 7.3.1 (companion def): The local m measure at a selected
quantifier inference occurrence in LKₑ. It counts propositional-logical rules
strictly below that occurrence, toward the root. Its address distinguishes
repeated copies of the same subtree. The selected inference contributes zero;
cuts contribute zero. -/
def ruleMeasureMLKe {L : Language} {s : Sequent L}
    (T : LKeProofTree s) (R : LKeInferenceOccurrence T) (n : Nat) : Prop :=
  R.rule.isQuantifier ∧ countBelow T R.address = some n
where
  /-- Count strict ancestors on the specified path; invalid addresses fail. -/
  countBelow : {s : Sequent L} → LKeProofTree s → List Nat → Option Nat
    | _, _, [] => some 0
    | _, .onePremise r t, 0 :: p =>
      let weight := match r with
        | .andLeftL .. | .andLeftR .. | .orRightL .. | .orRightR ..
        | .implRight .. | .negLeft .. | .negRight .. => 1
        | _ => 0
      (countBelow t p).map (fun n => weight + n)
    | _, .twoPremise r t _, 0 :: p =>
      let weight := match r with
        | .andRight .. | .orLeft .. | .implLeft .. => 1
        | .cut .. => 0
      (countBelow t p).map (fun n => weight + n)
    | _, .twoPremise r _ t, 1 :: p =>
      let weight := match r with
        | .andRight .. | .orLeft .. | .implLeft .. => 1
        | .cut .. => 0
      (countBelow t p).map (fun n => weight + n)
    | _, _, _ => none

helper /-- Theorem 7.3.1 (companion def): The local n measure at a selected
quantifier inference occurrence in LKₑ. It counts weakening rules
strictly below that occurrence, toward the root. Its address distinguishes
repeated copies of the same subtree. The selected inference contributes zero;
cuts contribute zero. -/
def ruleMeasureNLKe {L : Language} {s : Sequent L}
    (T : LKeProofTree s) (R : LKeInferenceOccurrence T) (n : Nat) : Prop :=
  R.rule.isQuantifier ∧ countBelow T R.address = some n
where
  /-- Count strict ancestors on the specified path; invalid addresses fail. -/
  countBelow : {s : Sequent L} → LKeProofTree s → List Nat → Option Nat
    | _, _, [] => some 0
    | _, .onePremise r t, 0 :: p =>
      let weight := match r with
        | .weakenLeft .. | .weakenRight .. => 1
        | _ => 0
      (countBelow t p).map (fun n => weight + n)
    | _, .twoPremise r t _, 0 :: p =>
      countBelow t p
    | _, .twoPremise r _ t, 1 :: p =>
      countBelow t p
    | _, _, _ => none



helper /-- Theorem 7.3.1 (companion def): Number of weakening occurrences, used to
express the source's possible n increase with additional weakenings. -/
def numWeakeningRulesLKe {L : Language} : {s : Sequent L} → LKeProofTree s → Nat
  | _, .axiom_ _ _ => 0
  | _, .eqAxiom _ _ => 0
  | _, .onePremise rule t =>
    match rule with
    | .weakenLeft .. | .weakenRight .. => 1 + numWeakeningRulesLKe t
    | _ => numWeakeningRulesLKe t
  | _, .twoPremise _ t₁ t₂ => numWeakeningRulesLKe t₁ + numWeakeningRulesLKe t₂

helper /-- Theorem 7.3.1 (companion theorem): The positive-m case admits a prescribed local permutation with m decreased by exactly one. No upper bound on the new n is asserted. -/
theorem mPhase_progressLK {L : Language} {s : Sequent L}
    (T : FOLKProofTree s) (hprepared : PhasePreparedLK T) (hpos : 0 < proofMeasureM T) :
    ∃ T' : FOLKProofTree s, MPhaseStepLK T T' ∧ proofMeasureM T' = proofMeasureM T - 1 := by
-- BEGIN PROOF
  -- REPAIR(T7-85): proof pending
  sorry

helper /-- Theorem 7.3.1 (companion theorem): Once m is zero, a prescribed weakening-phase step preserves m=0 and decreases n by exactly one. -/
theorem nPhase_progressLK {L : Language} {s : Sequent L}
    (T : FOLKProofTree s) (hprepared : PhasePreparedLK T)
    (hm : proofMeasureM T = 0) (hn : 0 < proofMeasureN T) :
    ∃ T' : FOLKProofTree s, NPhaseStepLK T T' ∧
      proofMeasureM T' = 0 ∧ proofMeasureN T' = proofMeasureN T - 1 := by
-- BEGIN PROOF
  -- REPAIR(T7-85): proof pending
  sorry

helper /-- Theorem 7.3.1 (companion theorem): There are source-prepared input/output proofs for which the positive-m permutation introduces additional weakenings and increases n, while m decreases by one. -/
theorem mPhase_canIncreaseNLK :
    ∃ (L : Language) (s : Sequent L) (T T' : FOLKProofTree s),
      MPhaseStepLK T T' ∧ proofMeasureM T' = proofMeasureM T - 1 ∧
      proofMeasureN T < proofMeasureN T' ∧ numWeakeningRulesLK T < numWeakeningRulesLK T' := by
-- BEGIN PROOF
  -- REPAIR(T7-85): proof pending
  sorry

helper /-- Theorem 7.3.1 (companion theorem): Every source-prepared proof reaches both zero measures after finitely many prescribed phase steps, in exactly the same end sequent. This is an existence claim; the later matrix cleanup is separate. -/
theorem phase_reaches_zeroLK {L : Language} {s : Sequent L}
    (T : FOLKProofTree s) (hprepared : PhasePreparedLK T) :
    ∃ T' : FOLKProofTree s, PhaseReachableLK T T' ∧ PhasePreparedLK T' ∧
      proofMeasureM T' = 0 ∧ proofMeasureN T' = 0 := by
-- BEGIN PROOF
  -- REPAIR(T7-85): proof pending
  sorry

helper /-- Theorem 7.3.1 (companion theorem): The positive-m case admits a prescribed local permutation with m decreased by exactly one. No upper bound on the new n is asserted. -/
theorem mPhase_progressLKe {L : Language} {s : Sequent L}
    (T : LKeProofTree s) (hprepared : PhasePreparedLKe T) (hpos : 0 < proofMeasureMLKe T) :
    ∃ T' : LKeProofTree s, MPhaseStepLKe T T' ∧ proofMeasureMLKe T' = proofMeasureMLKe T - 1 := by
-- BEGIN PROOF
  -- REPAIR(T7-85): proof pending
  sorry

helper /-- Theorem 7.3.1 (companion theorem): Once m is zero, a prescribed weakening-phase step preserves m=0 and decreases n by exactly one. -/
theorem nPhase_progressLKe {L : Language} {s : Sequent L}
    (T : LKeProofTree s) (hprepared : PhasePreparedLKe T)
    (hm : proofMeasureMLKe T = 0) (hn : 0 < proofMeasureNLKe T) :
    ∃ T' : LKeProofTree s, NPhaseStepLKe T T' ∧
      proofMeasureMLKe T' = 0 ∧ proofMeasureNLKe T' = proofMeasureNLKe T - 1 := by
-- BEGIN PROOF
  -- REPAIR(T7-85): proof pending
  sorry

helper /-- Theorem 7.3.1 (companion theorem): There are source-prepared input/output proofs for which the positive-m permutation introduces additional weakenings and increases n, while m decreases by one. -/
theorem mPhase_canIncreaseNLKe :
    ∃ (L : Language) (s : Sequent L) (T T' : LKeProofTree s),
      MPhaseStepLKe T T' ∧ proofMeasureMLKe T' = proofMeasureMLKe T - 1 ∧
      proofMeasureNLKe T < proofMeasureNLKe T' ∧ numWeakeningRulesLKe T < numWeakeningRulesLKe T' := by
-- BEGIN PROOF
  -- REPAIR(T7-85): proof pending
  sorry

helper /-- Theorem 7.3.1 (companion theorem): Every source-prepared proof reaches both zero measures after finitely many prescribed phase steps, in exactly the same end sequent. This is an existence claim; the later matrix cleanup is separate. -/
theorem phase_reaches_zeroLKe {L : Language} {s : Sequent L}
    (T : LKeProofTree s) (hprepared : PhasePreparedLKe T) :
    ∃ T' : LKeProofTree s, PhaseReachableLKe T T' ∧ PhasePreparedLKe T' ∧
      proofMeasureMLKe T' = 0 ∧ proofMeasureNLKe T' = 0 := by
-- BEGIN PROOF
  -- REPAIR(T7-85): proof pending
  sorry

proof_of permutationExampleIntermediateMeasures := by
  -- BEGIN PROOF
    exact ⟨rfl, rfl⟩


helper /-- Example 7.3.3 (companion): A separate cleaned normal proof with a
quantifier-free or-left conclusion. This is distinct from the printed raw
separation stage, which retains the existential context formulas. -/
def cleanedPermutationExampleTree : FOLKProofTree permutationExampleSequent :=
  let fa : Term permExLang := Term.func PermExFunc.f
    (fun _ => Term.const PermExConst.a)
  let ga : Term permExLang := Term.func PermExFunc.g
    (fun _ => Term.const PermExConst.a)
  let pfa : FormulaN permExLang :=
    FormulaN.predN PermExPred.P (fun _ => fa)
  let rga : FormulaN permExLang :=
    FormulaN.predN PermExPred.R (fun _ => ga)
  let pBodyX : FormulaN permExLang :=
    FormulaN.predN PermExPred.P (fun _ => Term.var 0)
  let rBodyY : FormulaN permExLang :=
    FormulaN.predN PermExPred.R (fun _ => Term.var 1)
  let exPx : FormulaN permExLang := FormulaN.ex 0 pBodyX
  let exRy : FormulaN permExLang := FormulaN.ex 1 rBodyY
  let pfaOrRga : FormulaN permExLang := FormulaN.disj pfa rga
  -- Left leaf: P(f(a)) -> P(f(a)) axiom
  let leftAxSeq : Sequent permExLang :=
    { antecedent := [pfa], succedent := [pfa] }
  let tLeftAx : FOLKProofTree leftAxSeq :=
    FOLKProofTree.axiom_ leftAxSeq ⟨pfa, rfl, rfl⟩
  -- weaken-right: [pfa] -> [pfa] ==> [pfa] -> [pfa, rga]
  let leftWeakRule : FOLKStep1
      (Sequent.mk [pfa] [pfa])
      (Sequent.mk [pfa] ([pfa] ++ [rga])) :=
    FOLKStep1.weakenRight rga [pfa] [pfa]
  let tLeftWeak : FOLKProofTree
      (Sequent.mk [pfa] ([pfa] ++ [rga])) :=
    FOLKProofTree.onePremise leftWeakRule tLeftAx
  -- Right leaf: R(g(a)) -> R(g(a)) axiom
  let rightAxSeq : Sequent permExLang :=
    { antecedent := [rga], succedent := [rga] }
  let tRightAx : FOLKProofTree rightAxSeq :=
    FOLKProofTree.axiom_ rightAxSeq ⟨rga, rfl, rfl⟩
  -- weaken-right: [rga] -> [rga] ==> [rga] -> [rga, pfa]
  let rightWeakRule : FOLKStep1
      (Sequent.mk [rga] [rga])
      (Sequent.mk [rga] ([rga] ++ [pfa])) :=
    FOLKStep1.weakenRight pfa [rga] [rga]
  let tRightWeak : FOLKProofTree
      (Sequent.mk [rga] ([rga] ++ [pfa])) :=
    FOLKProofTree.onePremise rightWeakRule tRightAx
  -- exchange-right: [rga] -> [rga, pfa] ==> [rga] -> [pfa, rga]
  let rightExchRule : FOLKStep1
      (Sequent.mk [rga] ([] ++ [rga, pfa] ++ []))
      (Sequent.mk [rga] ([] ++ [pfa, rga] ++ [])) :=
    FOLKStep1.exchangeRight [rga] [] rga pfa []
  let tRightExch : FOLKProofTree
      (Sequent.mk [rga] ([] ++ [pfa, rga] ++ [])) :=
    FOLKProofTree.onePremise rightExchRule tRightWeak
  -- or-left: [pfa] -> [pfa, rga] and [rga] -> [pfa, rga]
  --          ==> [pfaOrRga] -> [pfa, rga]
  let orLeftRule : FOLKStep2
      (Sequent.mk (pfa :: []) [pfa, rga])
      (Sequent.mk (rga :: []) [pfa, rga])
      (Sequent.mk (pfaOrRga :: []) [pfa, rga]) :=
    FOLKStep2.orLeft pfa rga [] [pfa, rga]
  let tOrLeft : FOLKProofTree
      (Sequent.mk [pfaOrRga] [pfa, rga]) :=
    FOLKProofTree.twoPremise orLeftRule tLeftWeak tRightExch
  -- Indexing note: under `FOLKStep1.exRight`, the existentially-bound
  -- formula must sit at the END of the succedent (shape `Δ ++ [A[t/x]]`
  -- ⟹ `Δ ++ [∃x.A]`). The source file's unindexed `exPxConc = [exPx, rga]`
  -- and `permutationExampleSequent = [exPx, exRy]` naming therefore
  -- requires a pair of exchanges around each exRight so that `pfa` and
  -- then `rga` can each be rewritten at the tail position. The tree
  -- structure is unchanged — only the ordering of logical+exchange
  -- applications reflects the indexed API's explicit positional
  -- requirement.
  -- Step 1: exchange [pfa, rga] -> [rga, pfa] so pfa sits at the tail
  let reorder1 : FOLKStep1
      (Sequent.mk [pfaOrRga] ([] ++ [pfa, rga] ++ []))
      (Sequent.mk [pfaOrRga] ([] ++ [rga, pfa] ++ [])) :=
    FOLKStep1.exchangeRight [pfaOrRga] [] pfa rga []
  let tReorder1 : FOLKProofTree
      (Sequent.mk [pfaOrRga] ([] ++ [rga, pfa] ++ [])) :=
    FOLKProofTree.onePremise reorder1 tOrLeft
  -- exists-right at pfa: produces [pfaOrRga] -> [rga, exPx]
  let exPxRule : FOLKStep1
      (Sequent.mk [pfaOrRga] ([rga] ++ [formulaSubstN pBodyX fa 0]))
      (Sequent.mk [pfaOrRga] ([rga] ++ [exPx])) :=
    FOLKStep1.exRight fa 0 pBodyX [pfaOrRga] [rga] (by trivial)
  let tExPx : FOLKProofTree
      (Sequent.mk [pfaOrRga] ([rga] ++ [exPx])) :=
    FOLKProofTree.onePremise exPxRule tReorder1
  -- exchange: [pfaOrRga] -> [rga, exPx] ==> [pfaOrRga] -> [exPx, rga]
  let reorder2 : FOLKStep1
      (Sequent.mk [pfaOrRga] ([] ++ [rga, exPx] ++ []))
      (Sequent.mk [pfaOrRga] ([] ++ [exPx, rga] ++ [])) :=
    FOLKStep1.exchangeRight [pfaOrRga] [] rga exPx []
  let tReorder2 : FOLKProofTree
      (Sequent.mk [pfaOrRga] ([] ++ [exPx, rga] ++ [])) :=
    FOLKProofTree.onePremise reorder2 tExPx
  -- exists-right at rga: produces [pfaOrRga] -> [exPx, exRy]
  let exRyRule : FOLKStep1
      (Sequent.mk [pfaOrRga] ([exPx] ++ [formulaSubstN rBodyY ga 1]))
      (Sequent.mk [pfaOrRga] ([exPx] ++ [exRy])) :=
    FOLKStep1.exRight ga 1 rBodyY [pfaOrRga] [exPx] (by trivial)
  FOLKProofTree.onePremise exRyRule tReorder2

end LCS.Herbrand.SharpenedHauptsatz.Theorem

end
