import LCS.Item
import LCS.Util
import LCS.Herbrand.SharpenedHauptsatz
import LCS.Herbrand.SharpenedHauptsatz.Permutability
import LCS.Herbrand.PrenexForm
import LCS.Herbrand.SharpenedHauptsatz.Theorem.Part1
import Attach
import LCS.Herbrand.SharpenedHauptsatz.Theorem.Part2.ProofsStamp

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

/-- Example 7.3.3 (companion): Both measures vanish at the printed raw
separation stage, independently of the later quantified-weakening cleanup. -/
@[blueprint "chap7__example_7_3_3"]
theorem permutationExampleFinalMeasures :
    proofMeasureM permutedExampleTree = 0 ∧ proofMeasureN permutedExampleTree = 0 

/-- Example 7.3.3 (companion): Fixed first-exchange frontier: the entire
unchanged left branch and the original right identity axiom. Structural rules
between this frontier and the selected rules belong to the local segment. -/
@[blueprint "chap7__example_7_3_3"]
def permutationFirstInputs : List (Σ c : Sequent permExLang, FOLKProofTree c) :=
  [(lkSubtreeAt permutationExampleTree [0]).get (by decide),
   ⟨⟨[permExRga], [permExRga]⟩, .axiom_ _ ⟨permExRga, rfl, rfl⟩⟩]

/-- Example 7.3.3 (companion): Source segment of the first exchange. -/
@[blueprint "chap7__example_7_3_3"]
def permutationFirstBefore : LKLocalFragment permutationFirstInputs permutationExampleSequent :=
  let fa : Term permExLang := .func .f (fun _ => .const .a)
  let ga : Term permExLang := .func .g (fun _ => .const .a)
  let pfa : FormulaN permExLang := .predN .P (fun _ => fa)
  let rga : FormulaN permExLang := .predN .R (fun _ => ga)
  let px : FormulaN permExLang := .predN .P (fun _ => .var 0)
  let ry : FormulaN permExLang := .predN .R (fun _ => .var 1)
  let exPx := FormulaN.ex 0 px
  let exRy := FormulaN.ex 1 ry
  .two (.orLeft pfa rga [] [exPx, exRy]) (LKLocalFragment.input (inputs := permutationFirstInputs) ⟨0, by decide⟩)
    (.one (.exRight ga 1 ry [rga] [exPx] (by trivial))
      (.one (.exchangeRight [rga] [] rga exPx [])
        (.one (.weakenRight exPx [rga] [rga])
          (LKLocalFragment.input (inputs := permutationFirstInputs) ⟨1, by decide⟩))))

/-- Example 7.3.3 (companion): Replacement segment of the first exchange,
retaining the ordered frontier and introducing the printed weakenings. -/
@[blueprint "chap7__example_7_3_3"]
def permutationFirstAfter : LKLocalFragment permutationFirstInputs permutationExampleSequent :=
  .one (.contractRight permExExistsR [.disj permExPfa permExRga] [permExExistsP])
    (.one (FOLKStep1.exRight (L := permExLang) (.func .g (fun _ => .const .a)) 1
        (.predN .R (fun _ => .var 1)) [.disj permExPfa permExRga]
        [permExExistsP, permExExistsR] (by trivial))
      (.two (.orLeft permExPfa permExRga []
          [permExExistsP, permExExistsR, permExRga])
        (.one (.weakenRight permExRga [permExPfa] [permExExistsP, permExExistsR]) (LKLocalFragment.input (inputs := permutationFirstInputs) ⟨0, by decide⟩)) (.one (.exchangeRight [permExRga] [permExExistsP] permExRga permExExistsR [])
    (.one (.exchangeRight [permExRga] [] permExRga permExExistsP [permExExistsR])
      (.one (.weakenRight permExExistsR [permExRga] [permExRga, permExExistsP])
        (.one (.weakenRight permExExistsP [permExRga] [permExRga])
          (LKLocalFragment.input (inputs := permutationFirstInputs) ⟨1, by decide⟩)))))))

/-- Example 7.3.3 (companion): Fixed second-exchange frontier: the original
left identity axiom and the entire unchanged intermediate right subtree T₂. -/
@[blueprint "chap7__example_7_3_3"]
def permutationSecondInputs : List (Σ c : Sequent permExLang, FOLKProofTree c) :=
  [⟨⟨[permExPfa], [permExPfa]⟩, .axiom_ _ ⟨permExPfa, rfl, rfl⟩⟩,
   ⟨_, permutationExampleIntermediateT2⟩]

/-- Example 7.3.3 (companion): Source segment of the second exchange,
ending at the actual intermediate or-left occurrence. -/
@[blueprint "chap7__example_7_3_3"]
def permutationSecondBefore : LKLocalFragment permutationSecondInputs
    ⟨[.disj permExPfa permExRga], [permExExistsP, permExExistsR, permExRga]⟩ :=
  .two (.orLeft permExPfa permExRga [] [permExExistsP, permExExistsR, permExRga])
    (.one (.weakenRight permExRga [permExPfa] [permExExistsP, permExExistsR])
    (.one (.exchangeRight [permExPfa] [] permExExistsR permExExistsP [])
      (.one (FOLKStep1.exRight (L := permExLang) (.func .f (fun _ => .const .a)) 0
          (.predN .P (fun _ => .var 0)) [permExPfa] [permExExistsR] (by trivial))
        (.one (.exchangeRight [permExPfa] [] permExPfa permExExistsR [])
          (.one (.weakenRight permExExistsR [permExPfa] [permExPfa])
            (LKLocalFragment.input (inputs := permutationSecondInputs) ⟨0, by decide⟩)))))) (LKLocalFragment.input (inputs := permutationSecondInputs) ⟨1, by decide⟩)

/-- Example 7.3.3 (companion): Replacement segment of the second exchange,
with the same frontier and S₀; ∃x-right is below or-left, followed by contraction. -/
@[blueprint "chap7__example_7_3_3"]
def permutationSecondAfter : LKLocalFragment permutationSecondInputs
    ⟨[.disj permExPfa permExRga], [permExExistsP, permExExistsR, permExRga]⟩ :=
  let Γ := [FormulaN.disj permExPfa permExRga]
  let core : LKLocalFragment permutationSecondInputs
      ⟨Γ, [permExExistsP, permExExistsR, permExRga, permExPfa]⟩ := LKLocalFragment.two
    (.orLeft permExPfa permExRga [] [permExExistsP, permExExistsR, permExRga, permExPfa])
    (.one (.exchangeRight [permExPfa] [permExExistsP, permExExistsR] permExPfa permExRga [])
    (.one (.exchangeRight [permExPfa] [permExExistsP] permExPfa permExExistsR [permExRga])
      (.one (.exchangeRight [permExPfa] [] permExPfa permExExistsP [permExExistsR, permExRga])
        (.one (.weakenRight permExRga [permExPfa] [permExPfa, permExExistsP, permExExistsR])
          (.one (.weakenRight permExExistsR [permExPfa] [permExPfa, permExExistsP])
            (.one (.weakenRight permExExistsP [permExPfa] [permExPfa])
              (LKLocalFragment.input (inputs := permutationSecondInputs) ⟨0, by decide⟩))))))) (.one (.weakenRight permExPfa [permExRga] [permExExistsP, permExExistsR, permExRga]) (LKLocalFragment.input (inputs := permutationSecondInputs) ⟨1, by decide⟩))
  let quantified := LKLocalFragment.one
    (FOLKStep1.exRight (L := permExLang) (.func .f (fun _ => .const .a)) 0
      (.predN .P (fun _ => .var 0)) Γ [permExExistsP, permExExistsR, permExRga] (by trivial)) core
  let contractP := LKLocalFragment.one
    (.exchangeRight Γ [permExExistsP] permExRga permExExistsR [])
    (.one (.exchangeRight Γ [] permExRga permExExistsP [permExExistsR])
      (.one (.exchangeRight Γ [permExRga] permExExistsR permExExistsP [])
        (.one (.contractRight permExExistsP Γ [permExRga, permExExistsR])
          (.one (.exchangeRight Γ [permExRga] permExExistsP permExExistsR [permExExistsP])
            (.one (.exchangeRight Γ [] permExExistsP permExRga [permExExistsR, permExExistsP])
              (.one (.exchangeRight Γ [permExExistsP] permExExistsR permExRga [permExExistsP]) quantified))))))
  contractP

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 7.3.3 (companion): Every additional rule in the first
replacement segment is structural; the two selected occurrences are excluded. -/
theorem permutationFirstOtherStructural :
    ∀ p rule, permutationFirstAfter.inferenceAt p = some rule →
      p ≠ [0] → p ≠ [0,0] → rule.isStructural := by
-- BEGIN PROOF
  intro p rule h hfirst hsecond
  rcases p with _ | ⟨i, p⟩
  · dsimp only [permutationFirstAfter, LKLocalFragment.inferenceAt] at h
    cases h
    trivial
  · rcases i with _ | i
    · rcases p with _ | ⟨i, p⟩
      · exact (hfirst rfl).elim
      · rcases i with _ | i
        · rcases p with _ | ⟨i, p⟩
          · exact (hsecond rfl).elim
          · rcases i with _ | i
            · rcases p with _ | ⟨i, p⟩
              · dsimp only [permutationFirstAfter, LKLocalFragment.inferenceAt] at h
                cases h
                trivial
              · rcases i with _ | i
                · change none = some rule at h
                  cases h
                · change none = some rule at h
                  cases h
            · rcases i with _ | i
              · rcases p with _ | ⟨i, p⟩
                · dsimp only [permutationFirstAfter, LKLocalFragment.inferenceAt] at h
                  cases h
                  trivial
                · rcases i with _ | i
                  · rcases p with _ | ⟨i, p⟩
                    · dsimp only [permutationFirstAfter, LKLocalFragment.inferenceAt] at h
                      cases h
                      trivial
                    · rcases i with _ | i
                      · rcases p with _ | ⟨i, p⟩
                        · dsimp only [permutationFirstAfter, LKLocalFragment.inferenceAt] at h
                          cases h
                          trivial
                        · rcases i with _ | i
                          · rcases p with _ | ⟨i, p⟩
                            · dsimp only [permutationFirstAfter, LKLocalFragment.inferenceAt] at h
                              cases h
                              trivial
                            · rcases i with _ | i
                              · change none = some rule at h
                                cases h
                              · change none = some rule at h
                                cases h
                          · change none = some rule at h
                            cases h
                      · change none = some rule at h
                        cases h
                  · change none = some rule at h
                    cases h
              · change none = some rule at h
                cases h
        · change none = some rule at h
          cases h
    · change none = some rule at h
      cases h

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 7.3.3 (companion): Every additional rule in the second
replacement segment is structural; the two selected occurrences are excluded. -/
theorem permutationSecondOtherStructural :
    ∀ p rule, permutationSecondAfter.inferenceAt p = some rule →
      p ≠ [0,0,0,0,0,0,0] → p ≠ [0,0,0,0,0,0,0,0] → rule.isStructural := by
-- BEGIN PROOF
  intro p rule h hfirst hsecond
  rcases p with _ | ⟨i, p⟩
  · dsimp only [permutationSecondAfter, LKLocalFragment.inferenceAt] at h
    cases h
    trivial
  · rcases i with _ | i
    · rcases p with _ | ⟨i, p⟩
      · dsimp only [permutationSecondAfter, LKLocalFragment.inferenceAt] at h
        cases h
        trivial
      · rcases i with _ | i
        · rcases p with _ | ⟨i, p⟩
          · dsimp only [permutationSecondAfter, LKLocalFragment.inferenceAt] at h
            cases h
            trivial
          · rcases i with _ | i
            · rcases p with _ | ⟨i, p⟩
              · dsimp only [permutationSecondAfter, LKLocalFragment.inferenceAt] at h
                cases h
                trivial
              · rcases i with _ | i
                · rcases p with _ | ⟨i, p⟩
                  · dsimp only [permutationSecondAfter, LKLocalFragment.inferenceAt] at h
                    cases h
                    trivial
                  · rcases i with _ | i
                    · rcases p with _ | ⟨i, p⟩
                      · dsimp only [permutationSecondAfter, LKLocalFragment.inferenceAt] at h
                        cases h
                        trivial
                      · rcases i with _ | i
                        · rcases p with _ | ⟨i, p⟩
                          · dsimp only [permutationSecondAfter, LKLocalFragment.inferenceAt] at h
                            cases h
                            trivial
                          · rcases i with _ | i
                            · rcases p with _ | ⟨i, p⟩
                              · exact (hfirst rfl).elim
                              · rcases i with _ | i
                                · rcases p with _ | ⟨i, p⟩
                                  · exact (hsecond rfl).elim
                                  · rcases i with _ | i
                                    · rcases p with _ | ⟨i, p⟩
                                      · dsimp only [permutationSecondAfter, LKLocalFragment.inferenceAt] at h
                                        cases h
                                        trivial
                                      · rcases i with _ | i
                                        · rcases p with _ | ⟨i, p⟩
                                          · dsimp only [permutationSecondAfter, LKLocalFragment.inferenceAt] at h
                                            cases h
                                            trivial
                                          · rcases i with _ | i
                                            · rcases p with _ | ⟨i, p⟩
                                              · dsimp only [permutationSecondAfter, LKLocalFragment.inferenceAt] at h
                                                cases h
                                                trivial
                                              · rcases i with _ | i
                                                · rcases p with _ | ⟨i, p⟩
                                                  · dsimp only [permutationSecondAfter, LKLocalFragment.inferenceAt] at h
                                                    cases h
                                                    trivial
                                                  · rcases i with _ | i
                                                    · rcases p with _ | ⟨i, p⟩
                                                      · dsimp only [permutationSecondAfter, LKLocalFragment.inferenceAt] at h
                                                        cases h
                                                        trivial
                                                      · rcases i with _ | i
                                                        · rcases p with _ | ⟨i, p⟩
                                                          · dsimp only [permutationSecondAfter, LKLocalFragment.inferenceAt] at h
                                                            cases h
                                                            trivial
                                                          · rcases i with _ | i
                                                            · change none = some rule at h
                                                              cases h
                                                            · change none = some rule at h
                                                              cases h
                                                        · change none = some rule at h
                                                          cases h
                                                    · change none = some rule at h
                                                      cases h
                                                · change none = some rule at h
                                                  cases h
                                            · change none = some rule at h
                                              cases h
                                        · change none = some rule at h
                                          cases h
                                    · rcases i with _ | i
                                      · rcases p with _ | ⟨i, p⟩
                                        · dsimp only [permutationSecondAfter, LKLocalFragment.inferenceAt] at h
                                          cases h
                                          trivial
                                        · rcases i with _ | i
                                          · change none = some rule at h
                                            cases h
                                          · change none = some rule at h
                                            cases h
                                      · change none = some rule at h
                                        cases h
                                · change none = some rule at h
                                  cases h
                            · change none = some rule at h
                              cases h
                        · change none = some rule at h
                          cases h
                    · change none = some rule at h
                      cases h
                · change none = some rule at h
                  cases h
            · change none = some rule at h
              cases h
        · change none = some rule at h
          cases h
    · change none = some rule at h
      cases h

/-- Example 7.3.3 (companion): First actual local exchange, using the
fixed source frontier and the root continuation. Rule schemas/payloads are
retained while the selected ∃y-right moves below or-left. -/
@[blueprint "chap7__example_7_3_3"]
def permutationFirstExchange :
    LKLocalReplacement permutationExampleTree [] permutationFirstBefore.plug
      permutationFirstInputs
      ((lkInferenceAt permutationExampleTree [1]).get (by decide))
      ((lkInferenceAt permutationExampleTree []).get (by decide)) where
  continuation := .hole
  atAddress := rfl
  sourceFixed := rfl
  replacement := permutationFirstAfter
  inputOrder := rfl
  firstAddress := [0]
  secondAddress := [0,0]
  firstRule := (permutationFirstAfter.inferenceAt [0]).get (by decide)
  secondRule := (permutationFirstAfter.inferenceAt [0,0]).get (by decide)
  firstAt := rfl
  secondAt := rfl
  firstSchema := rfl
  secondSchema := rfl
  firstPayload := rfl
  secondPayload := rfl
  distinct := by decide
  reversed := by simp [premiseAddressDescendant]
  otherStructural := permutationFirstOtherStructural

/-- Example 7.3.3 (companion): Second actual local exchange at [0,0].
The outside ∃y-right/contraction continuation remains exactly fixed. -/
@[blueprint "chap7__example_7_3_3"]
def permutationSecondExchange :
    LKLocalReplacement permutationExampleIntermediateTree [0,0] permutationSecondBefore.plug
      permutationSecondInputs
      ((lkInferenceAt permutationExampleIntermediateTree [0,0,0,0,0]).get (by decide))
      ((lkInferenceAt permutationExampleIntermediateTree [0,0]).get (by decide)) where
  continuation := .one (.contractRight permExExistsR [.disj permExPfa permExRga] [permExExistsP])
    (.one (FOLKStep1.exRight (L := permExLang) (.func .g (fun _ => .const .a)) 1
      (.predN .R (fun _ => .var 1)) [.disj permExPfa permExRga]
      [permExExistsP, permExExistsR] (by trivial)) .hole)
  atAddress := rfl
  sourceFixed := rfl
  replacement := permutationSecondAfter
  inputOrder := rfl
  firstAddress := [0,0,0,0,0,0,0]
  secondAddress := [0,0,0,0,0,0,0,0]
  firstRule := (permutationSecondAfter.inferenceAt [0,0,0,0,0,0,0]).get (by decide)
  secondRule := (permutationSecondAfter.inferenceAt [0,0,0,0,0,0,0,0]).get (by decide)
  firstAt := rfl
  secondAt := rfl
  firstSchema := rfl
  secondSchema := rfl
  firstPayload := rfl
  secondPayload := rfl
  distinct := by decide
  reversed := by simp [premiseAddressDescendant]
  otherStructural := permutationSecondOtherStructural



-- ===================================================================
-- Example 7.3.3 (companion theorem): permutationExampleMeasureM
-- ===================================================================

/-- Example 7.3.3 (companion theorem): Verifies that the proof measure m(T) = 2 for the initial proof tree permutationExampleTree. The tree has two exists-right inferences above the or-left propositional inference, so each contributes m(R) = 1 to the sum. -/
@[blueprint "chap7__example_7_3_3"]
theorem permutationExampleMeasureM :
    proofMeasureM permutationExampleTree = 2 

-- ===================================================================
-- Example 7.3.3 (companion theorem): permutationExampleMeasureN
-- ===================================================================

/-- Example 7.3.3 (companion theorem): Initially n(T)=0: each weakening
is above its branch's exists-right, so neither quantifier has a weakening below. -/
@[blueprint "chap7__example_7_3_3"]
theorem permutationExampleMeasureN :
    proofMeasureN permutationExampleTree = 0 

-- ===================================================================
-- Example 7.3.4 (companion def): midseqExLang
-- ===================================================================

/-- Example 7.3.4 (companion def): An equality-free language with binary predicates P and Q, no function or constant symbols. Used for the midsequent example demonstrating Theorem 7.3.1. -/
@[blueprint "chap7__example_7_3_4"]
def midseqExLang : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := Empty
  predSymbols := MidseqExPred
  predArity := fun _ => 2
  hasEquality := false

-- ===================================================================
-- Example 7.3.4 (companion def): midseqExMkP
-- ===================================================================

/-- Example 7.3.4 (companion def): Helper to construct P(a,b) formulas in the midseqExLang language, used for building proof tree witnesses. -/
@[blueprint "chap7__example_7_3_4"]
def midseqExMkP (a b : Term midseqExLang) : FormulaN midseqExLang :=
  FormulaN.predN MidseqExPred.P (vec2 a b)

-- ===================================================================
-- Example 7.3.4 (companion def): midseqExMkQ
-- ===================================================================

/-- Example 7.3.4 (companion def): Helper to construct Q(a,b) formulas in the midseqExLang language, used for building proof tree witnesses. -/
@[blueprint "chap7__example_7_3_4"]
def midseqExMkQ (a b : Term midseqExLang) : FormulaN midseqExLang :=
  FormulaN.predN MidseqExPred.Q (vec2 a b)

-- ===================================================================
-- Example 7.3.4 (companion def): midsequentExampleSequent
-- ===================================================================

/-- Example 7.3.4 (companion def): The sequent -> exists x forall y not P(x,y), exists y_1 forall z not Q(y_1,z), forall x_1 exists y_2 exists z_1(P(x_1,y_2) and Q(y_2,z_1)). Variables: x=0, y=1, y_1=2, z=3, x_1=4, y_2=5, z_1=6. -/
@[blueprint "chap7__example_7_3_4"]
def midsequentExampleSequent : Sequent midseqExLang :=
  -- exists x forall y not P(x, y)
  let f1 := FormulaN.ex 0
    (FormulaN.all 1
      (FormulaN.neg (midseqExMkP (Term.var 0) (Term.var 1))))
  -- exists y_1 forall z not Q(y_1, z)
  let f2 := FormulaN.ex 2
    (FormulaN.all 3
      (FormulaN.neg (midseqExMkQ (Term.var 2) (Term.var 3))))
  -- forall x_1 exists y_2 exists z_1(P(x_1, y_2) and Q(y_2, z_1))
  let f3 := FormulaN.all 4
    (FormulaN.ex 5
      (FormulaN.ex 6
        (FormulaN.conj
          (midseqExMkP (Term.var 4) (Term.var 5))
          (midseqExMkQ (Term.var 5) (Term.var 6)))))
  { antecedent := []
    succedent := [f1, f2, f3] }

-- ===================================================================
-- Example 7.3.4 (companion def): midsequentExampleEquivFormula
-- ===================================================================

/-- Example 7.3.4 (companion def): The formula A = exists x forall y not P(x,y) or exists y_1 forall z not Q(y_1,z) or forall x_1 exists y_2 exists z_1(P(x_1,y_2) and Q(y_2,z_1)) whose validity is equivalent to the validity of the example sequent. Formed as the disjunction of the succedent formulae. -/
@[blueprint "chap7__example_7_3_4"]
def midsequentExampleEquivFormula : FormulaN midseqExLang :=
  let f1 := FormulaN.ex 0
    (FormulaN.all 1
      (FormulaN.neg (midseqExMkP (Term.var 0) (Term.var 1))))
  let f2 := FormulaN.ex 2
    (FormulaN.all 3
      (FormulaN.neg (midseqExMkQ (Term.var 2) (Term.var 3))))
  let f3 := FormulaN.all 4
    (FormulaN.ex 5
      (FormulaN.ex 6
        (FormulaN.conj
          (midseqExMkP (Term.var 4) (Term.var 5))
          (midseqExMkQ (Term.var 5) (Term.var 6)))))
  FormulaN.disj f1 (FormulaN.disj f2 f3)

-- ===================================================================
-- Example 7.3.4 (companion def): midsequentExampleMidseq
-- ===================================================================

/-- Example 7.3.4 (companion def): The midsequent -> not P(x_1, y), not Q(y, z), P(x_1, y) and Q(y, z), which is quantifier-free and satisfies the conditions of Theorem 7.3.1. Variables: x_1=4, y=1, z=3. Using eigenvariables from the quantifier stripping. The midsequent uses the variables that appear after all quantifiers are stripped by the forall-right and exists-right rules in the lower part of the proof. -/
@[blueprint "chap7__example_7_3_4"]
def midsequentExampleMidseq : Sequent midseqExLang :=
  let x1 : Term midseqExLang := Term.var 4
  let y : Term midseqExLang := Term.var 1
  let z : Term midseqExLang := Term.var 3
  { antecedent := []
    succedent :=
      [ FormulaN.neg (midseqExMkP x1 y)
      , FormulaN.neg (midseqExMkQ y z)
      , FormulaN.conj (midseqExMkP x1 y) (midseqExMkQ y z) ] }

-- ===================================================================
-- Example 7.3.4 (companion def): midsequentExampleUpperTree
-- ===================================================================

/-- Example 7.3.4 (companion): The printed upper proof, from the P and Q
identity axioms through weakening and conjunction. Negation-right moves Q
first and P second, with exchanges restoring each printed sequent order. -/
@[blueprint "chap7__example_7_3_4"]
def midsequentExampleUpperTree :
    FOLKProofTree (L := midseqExLang) midsequentExampleMidseq :=
  let x1 : Term midseqExLang := Term.var 4
  let y : Term midseqExLang := Term.var 1
  let z : Term midseqExLang := Term.var 3
  let p : FormulaN midseqExLang := midseqExMkP x1 y
  let q : FormulaN midseqExLang := midseqExMkQ y z
  -- P axiom: [p] -> [p]
  let pAxSeq : Sequent midseqExLang :=
    { antecedent := [p], succedent := [p] }
  let tPAx : FOLKProofTree pAxSeq :=
    FOLKProofTree.axiom_ pAxSeq ⟨p, rfl, rfl⟩
  -- weaken-left q: [p] -> [p] ==> [q, p] -> [p]
  let pWeakRule : FOLKStep1
      (Sequent.mk [p] [p])
      (Sequent.mk (q :: [p]) [p]) :=
    FOLKStep1.weakenLeft q [p] [p]
  let tPAxWeak : FOLKProofTree
      (Sequent.mk [q, p] [p]) :=
    FOLKProofTree.onePremise pWeakRule tPAx
  -- exchange-left: [q, p] -> [p] ==> [p, q] -> [p]
  let pExchRule : FOLKStep1
      (Sequent.mk ([] ++ [q, p] ++ []) [p])
      (Sequent.mk ([] ++ [p, q] ++ []) [p]) :=
    FOLKStep1.exchangeLeft [] q p [] [p]
  let tPAxExch : FOLKProofTree
      (Sequent.mk ([] ++ [p, q] ++ []) [p]) :=
    FOLKProofTree.onePremise pExchRule tPAxWeak
  -- Q axiom: [q] -> [q]
  let qAxSeq : Sequent midseqExLang :=
    { antecedent := [q], succedent := [q] }
  let tQAx : FOLKProofTree qAxSeq :=
    FOLKProofTree.axiom_ qAxSeq ⟨q, rfl, rfl⟩
  -- weaken-left p: [q] -> [q] ==> [p, q] -> [q]
  let qWeakRule : FOLKStep1
      (Sequent.mk [q] [q])
      (Sequent.mk (p :: [q]) [q]) :=
    FOLKStep1.weakenLeft p [q] [q]
  let tQAxWeak : FOLKProofTree
      (Sequent.mk [p, q] [q]) :=
    FOLKProofTree.onePremise qWeakRule tQAx
  -- and-right: [p, q] -> [p] and [p, q] -> [q] ==> [p, q] -> [p /\ q]
  let andRule : FOLKStep2
      (Sequent.mk [p, q] ([] ++ [p]))
      (Sequent.mk [p, q] ([] ++ [q]))
      (Sequent.mk [p, q] ([] ++ [FormulaN.conj p q])) :=
    FOLKStep2.andRight p q [p, q] []
  let tAnd : FOLKProofTree
      (Sequent.mk [p, q] ([] ++ [FormulaN.conj p q])) :=
    FOLKProofTree.twoPremise andRule tPAxExch tQAxWeak
  -- Expose Q at the head, then move its negation to the printed position.
  let tNegQ := FOLKProofTree.onePremise
    (.exchangeRight [p] [] (.conj p q) (.neg q) [])
    (.onePremise (.negRight q [p] [.conj p q])
      (.onePremise (.exchangeLeft [] p q [] [.conj p q]) tAnd))
  -- Move P second and restore the named midsequent order.
  .onePremise (.exchangeRight [] [] (.neg q) (.neg p) [.conj p q])
    (.onePremise (.exchangeRight [] [.neg q] (.conj p q) (.neg p) [])
      (.onePremise (.negRight p [] [.neg q, .conj p q]) tNegQ))

end LCS.Herbrand.SharpenedHauptsatz.Theorem
end

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
open LCS.FirstOrder.SyntaxN.Variables

/-- Example 7.3.4: The exact connected printed proof. Above the named
midsequent Q-negation precedes P-negation. Below it the seven quantifier steps
are ∃z₁, ∃y₂, ∀z, ∃y₁, ∀y, ∃x, ∀x₁, with the displayed variables
x=0,y=1,y₁=2,z=3,x₁=4,y₂=5,z₁=6. Exchanges expose the selected succedent
formula at the last position and restore the printed order. Every free-for
and whole-conclusion eigenvariable condition is proved. -/
@[blueprint "chap7__example_7_3_4" (main := true)]
def midsequentExampleTree :
    FOLKProofTree (L := midseqExLang) midsequentExampleSequent := by
  have midseqExSubstP (a b t : Term midseqExLang) (x : Nat) :
      formulaSubstN (midseqExMkP a b) t x =
        midseqExMkP (termSubst a t x) (termSubst b t x) := by
    apply congrArg (FormulaN.predN (L := midseqExLang) MidseqExPred.P)
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
  have midseqExSubstQ (a b t : Term midseqExLang) (x : Nat) :
      formulaSubstN (midseqExMkQ a b) t x =
        midseqExMkQ (termSubst a t x) (termSubst b t x) := by
    apply congrArg (FormulaN.predN (L := midseqExLang) MidseqExPred.Q)
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
  let np := FormulaN.neg (midseqExMkP (.var 4) (.var 1))
  let nq := FormulaN.neg (midseqExMkQ (.var 1) (.var 3))
  let c0 := FormulaN.conj (midseqExMkP (.var 4) (.var 1)) (midseqExMkQ (.var 1) (.var 3))
  let c1 := FormulaN.ex 6
    (.conj (midseqExMkP (.var 4) (.var 1)) (midseqExMkQ (.var 1) (.var 6)))
  let c2 := FormulaN.ex 5 (.ex 6
    (.conj (midseqExMkP (.var 4) (.var 5)) (midseqExMkQ (.var 5) (.var 6))))
  let aq := FormulaN.all 3 (FormulaN.neg (midseqExMkQ (.var 1) (.var 3)))
  let eq := FormulaN.ex 2 (.all 3 (FormulaN.neg (midseqExMkQ (.var 2) (.var 3))))
  let ap := FormulaN.all 1 (FormulaN.neg (midseqExMkP (.var 4) (.var 1)))
  let ep := FormulaN.ex 0 (.all 1 (FormulaN.neg (midseqExMkP (.var 0) (.var 1))))
  have finTwo (R : Fin 2 → Prop) : (∃ i, R i) ↔ R 0 ∨ R 1 := by
    constructor
    · rintro ⟨⟨i, hi⟩, h⟩
      match i, hi with
      | 0, _ => exact Or.inl h
      | 1, _ => exact Or.inr h
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  have finTwoAll (R : Fin 2 → Prop) : (∀ i, R i) ↔ R 0 ∧ R 1 := by
    constructor
    · intro h
      exact ⟨h 0, h 1⟩
    · rintro ⟨h0, h1⟩ ⟨i, hi⟩
      match i, hi with
      | 0, _ => exact h0
      | 1, _ => exact h1
  have fresh3 : ∀ F ∈ ([] : List (FormulaN midseqExLang)) ++ ([np, c2] ++ [aq]),
      3 ∉ formulaFVN F := by
    intro F hF
    simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl
    all_goals simp [np, c2, aq, formulaFVN, midseqExMkP, midseqExMkQ,
      Membership.mem, Set.iUnion, Set.union, Set.diff, Set.singleton, termFV, vec2, midseqExLang, finTwo, finTwoAll]
  have fresh1 : ∀ F ∈ ([] : List (FormulaN midseqExLang)) ++ ([eq, c2] ++ [ap]),
      1 ∉ formulaFVN F := by
    intro F hF
    simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl
    all_goals simp [eq, c2, ap, formulaFVN, midseqExMkP, midseqExMkQ,
      Membership.mem, Set.iUnion, Set.union, Set.diff, Set.singleton, termFV, vec2, midseqExLang, finTwo, finTwoAll]
  have fresh4 : ∀ F ∈ ([] : List (FormulaN midseqExLang)) ++ ([ep, eq] ++ [.all 4 c2]),
      4 ∉ formulaFVN F := by
    intro F hF
    simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl
    all_goals simp [ep, eq, c2, formulaFVN, midseqExMkP, midseqExMkQ,
      Membership.mem, Set.iUnion, Set.union, Set.diff, Set.singleton, termFV, vec2, midseqExLang, finTwo, finTwoAll]
  let r1 : FOLKStep1 ⟨[], [np, nq, c0]⟩ ⟨[], [np, nq, c1]⟩ := by
    simpa [c0, c1, formulaSubstN, midseqExSubstP, midseqExSubstQ, termSubst] using
      (FOLKStep1.exRight (L := midseqExLang) (.var 3) 6
        (.conj (midseqExMkP (.var 4) (.var 1)) (midseqExMkQ (.var 1) (.var 6)))
        [] [np, nq] (by simp [c2, isFreeForN, midseqExMkP, midseqExMkQ, termFV, Membership.mem, Set.singleton]))
  let t1 := FOLKProofTree.onePremise r1 midsequentExampleUpperTree
  let r2 : FOLKStep1 ⟨[], [np, nq, c1]⟩ ⟨[], [np, nq, c2]⟩ := by
    simpa [c1, c2, formulaSubstN, midseqExSubstP, midseqExSubstQ, termSubst] using
      (FOLKStep1.exRight (L := midseqExLang) (.var 1) 5
        (.ex 6 (.conj (midseqExMkP (.var 4) (.var 5)) (midseqExMkQ (.var 5) (.var 6))))
        [] [np, nq] (by simp [c2, isFreeForN, midseqExMkP, midseqExMkQ, termFV, Membership.mem, Set.singleton]))
  let t2 := FOLKProofTree.onePremise r2 t1
  let r3 : FOLKStep1 ⟨[], [np, c2, nq]⟩ ⟨[], [np, c2, aq]⟩ := by
    simpa [nq, aq, formulaSubstN, midseqExSubstQ, termSubst] using
      (FOLKStep1.allRight (L := midseqExLang) 3 3
        (.neg (midseqExMkQ (.var 1) (.var 3))) [] [np, c2] fresh3 (by simp [c2, isFreeForN, midseqExMkP, midseqExMkQ, termFV, Membership.mem, Set.singleton]))
  let t3 := FOLKProofTree.onePremise (.exchangeRight [] [np] c2 aq [])
    (.onePremise r3 (.onePremise (.exchangeRight [] [np] nq c2 []) t2))
  let r4 : FOLKStep1 ⟨[], [np, c2, aq]⟩ ⟨[], [np, c2, eq]⟩ := by
    simpa [aq, eq, formulaSubstN, midseqExSubstQ, termSubst] using
      (FOLKStep1.exRight (L := midseqExLang) (.var 1) 2
        (.all 3 (.neg (midseqExMkQ (.var 2) (.var 3)))) [] [np, c2] (by simp [c2, isFreeForN, midseqExMkP, midseqExMkQ, termFV, Membership.mem, Set.singleton]))
  let t4 := FOLKProofTree.onePremise (.exchangeRight [] [np] c2 eq [])
    (.onePremise r4 (.onePremise (.exchangeRight [] [np] aq c2 []) t3))
  let r5 : FOLKStep1 ⟨[], [eq, c2, np]⟩ ⟨[], [eq, c2, ap]⟩ := by
    simpa [np, ap, formulaSubstN, midseqExSubstP, termSubst] using
      (FOLKStep1.allRight (L := midseqExLang) 1 1
        (.neg (midseqExMkP (.var 4) (.var 1))) [] [eq, c2] fresh1 (by simp [c2, isFreeForN, midseqExMkP, midseqExMkQ, termFV, Membership.mem, Set.singleton]))
  let t5 := FOLKProofTree.onePremise (.exchangeRight [] [] eq ap [c2])
    (.onePremise (.exchangeRight [] [eq] c2 ap [])
      (.onePremise r5 (.onePremise (.exchangeRight [] [eq] np c2 [])
        (.onePremise (.exchangeRight [] [] np eq [c2]) t4))))
  let r6 : FOLKStep1 ⟨[], [eq, c2, ap]⟩ ⟨[], [eq, c2, ep]⟩ := by
    simpa [ap, ep, formulaSubstN, midseqExSubstP, termSubst] using
      (FOLKStep1.exRight (L := midseqExLang) (.var 4) 0
        (.all 1 (.neg (midseqExMkP (.var 0) (.var 1)))) [] [eq, c2] (by simp [c2, isFreeForN, midseqExMkP, midseqExMkQ, termFV, Membership.mem, Set.singleton]))
  let t6 := FOLKProofTree.onePremise (.exchangeRight [] [] eq ep [c2])
    (.onePremise (.exchangeRight [] [eq] c2 ep [])
      (.onePremise r6 (.onePremise (.exchangeRight [] [eq] ap c2 [])
        (.onePremise (.exchangeRight [] [] ap eq [c2]) t5))))
  let r7 : FOLKStep1 ⟨[], [ep, eq, c2]⟩ ⟨[], [ep, eq, .all 4 c2]⟩ := by
    simpa [c2, formulaSubstN, midseqExSubstP, midseqExSubstQ, termSubst] using
      (FOLKStep1.allRight (L := midseqExLang) 4 4 c2 [] [ep, eq] fresh4 (by simp [c2, isFreeForN, midseqExMkP, midseqExMkQ, termFV, Membership.mem, Set.singleton]))
  exact FOLKProofTree.onePremise r7 t6

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 7.3.4 (companion): The actual named upper proof occurs at the
selected node after all seven quantifier steps and twelve exchanges. -/
theorem midsequentExampleNode :
    lkSubtreeAt midsequentExampleTree (List.replicate 19 0) =
      some ⟨midsequentExampleMidseq, midsequentExampleUpperTree⟩ := by
-- BEGIN PROOF
  rfl

/-- Example 7.3.4 (companion): Fresh representative's midsequent, with
x₁,y,z replaced locally by 9,8,7; all original binders 0–6 stay fixed. -/
@[blueprint "chap7__example_7_3_4"]
def midsequentRenamedMidseq : Sequent midseqExLang :=
  let x1 : Term midseqExLang := Term.var 9
  let y : Term midseqExLang := Term.var 8
  let z : Term midseqExLang := Term.var 7
  { antecedent := []
    succedent :=
      [ FormulaN.neg (midseqExMkP x1 y)
      , FormulaN.neg (midseqExMkQ y z)
      , FormulaN.conj (midseqExMkP x1 y) (midseqExMkQ y z) ] }

/-- Example 7.3.4 (companion): The same upper rule tree over the fresh
atoms P(9,8) and Q(8,7), with Q-negation before P-negation. -/
@[blueprint "chap7__example_7_3_4"]
def midsequentRenamedUpperTree :
    FOLKProofTree (L := midseqExLang) midsequentRenamedMidseq :=
  let x1 : Term midseqExLang := Term.var 9
  let y : Term midseqExLang := Term.var 8
  let z : Term midseqExLang := Term.var 7
  let p : FormulaN midseqExLang := midseqExMkP x1 y
  let q : FormulaN midseqExLang := midseqExMkQ y z
  -- P axiom: [p] -> [p]
  let pAxSeq : Sequent midseqExLang :=
    { antecedent := [p], succedent := [p] }
  let tPAx : FOLKProofTree pAxSeq :=
    FOLKProofTree.axiom_ pAxSeq ⟨p, rfl, rfl⟩
  -- weaken-left q: [p] -> [p] ==> [q, p] -> [p]
  let pWeakRule : FOLKStep1
      (Sequent.mk [p] [p])
      (Sequent.mk (q :: [p]) [p]) :=
    FOLKStep1.weakenLeft q [p] [p]
  let tPAxWeak : FOLKProofTree
      (Sequent.mk [q, p] [p]) :=
    FOLKProofTree.onePremise pWeakRule tPAx
  -- exchange-left: [q, p] -> [p] ==> [p, q] -> [p]
  let pExchRule : FOLKStep1
      (Sequent.mk ([] ++ [q, p] ++ []) [p])
      (Sequent.mk ([] ++ [p, q] ++ []) [p]) :=
    FOLKStep1.exchangeLeft [] q p [] [p]
  let tPAxExch : FOLKProofTree
      (Sequent.mk ([] ++ [p, q] ++ []) [p]) :=
    FOLKProofTree.onePremise pExchRule tPAxWeak
  -- Q axiom: [q] -> [q]
  let qAxSeq : Sequent midseqExLang :=
    { antecedent := [q], succedent := [q] }
  let tQAx : FOLKProofTree qAxSeq :=
    FOLKProofTree.axiom_ qAxSeq ⟨q, rfl, rfl⟩
  -- weaken-left p: [q] -> [q] ==> [p, q] -> [q]
  let qWeakRule : FOLKStep1
      (Sequent.mk [q] [q])
      (Sequent.mk (p :: [q]) [q]) :=
    FOLKStep1.weakenLeft p [q] [q]
  let tQAxWeak : FOLKProofTree
      (Sequent.mk [p, q] [q]) :=
    FOLKProofTree.onePremise qWeakRule tQAx
  -- and-right: [p, q] -> [p] and [p, q] -> [q] ==> [p, q] -> [p /\ q]
  let andRule : FOLKStep2
      (Sequent.mk [p, q] ([] ++ [p]))
      (Sequent.mk [p, q] ([] ++ [q]))
      (Sequent.mk [p, q] ([] ++ [FormulaN.conj p q])) :=
    FOLKStep2.andRight p q [p, q] []
  let tAnd : FOLKProofTree
      (Sequent.mk [p, q] ([] ++ [FormulaN.conj p q])) :=
    FOLKProofTree.twoPremise andRule tPAxExch tQAxWeak
  -- Expose Q at the head, then move its negation to the printed position.
  let tNegQ := FOLKProofTree.onePremise
    (.exchangeRight [p] [] (.conj p q) (.neg q) [])
    (.onePremise (.negRight q [p] [.conj p q])
      (.onePremise (.exchangeLeft [] p q [] [.conj p q]) tAnd))
  -- Move P second and restore the named midsequent order.
  .onePremise (.exchangeRight [] [] (.neg q) (.neg p) [.conj p q])
    (.onePremise (.exchangeRight [] [.neg q] (.conj p q) (.neg p) [])
      (.onePremise (.negRight p [] [.neg q, .conj p q]) tNegQ))

/-- Example 7.3.4 (companion): Explicit fresh representative of the
connected proof. Its eigenvariables are 7,8,9, distinct from all source names
0–6. Binder names and the original end sequent remain unchanged. -/
@[blueprint "chap7__example_7_3_4"]
def midsequentRenamedTree :
    FOLKProofTree (L := midseqExLang) midsequentExampleSequent := by
  have midseqExSubstP (a b t : Term midseqExLang) (x : Nat) :
      formulaSubstN (midseqExMkP a b) t x =
        midseqExMkP (termSubst a t x) (termSubst b t x) := by
    apply congrArg (FormulaN.predN (L := midseqExLang) MidseqExPred.P)
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
  have midseqExSubstQ (a b t : Term midseqExLang) (x : Nat) :
      formulaSubstN (midseqExMkQ a b) t x =
        midseqExMkQ (termSubst a t x) (termSubst b t x) := by
    apply congrArg (FormulaN.predN (L := midseqExLang) MidseqExPred.Q)
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
  let np := FormulaN.neg (midseqExMkP (.var 9) (.var 8))
  let nq := FormulaN.neg (midseqExMkQ (.var 8) (.var 7))
  let c0 := FormulaN.conj (midseqExMkP (.var 9) (.var 8)) (midseqExMkQ (.var 8) (.var 7))
  let c1 := FormulaN.ex 6
    (.conj (midseqExMkP (.var 9) (.var 8)) (midseqExMkQ (.var 8) (.var 6)))
  let c2 := FormulaN.ex 5 (.ex 6
    (.conj (midseqExMkP (.var 9) (.var 5)) (midseqExMkQ (.var 5) (.var 6))))
  let aq := FormulaN.all 3 (FormulaN.neg (midseqExMkQ (.var 8) (.var 3)))
  let eq := FormulaN.ex 2 (.all 3 (FormulaN.neg (midseqExMkQ (.var 2) (.var 3))))
  let ap := FormulaN.all 1 (FormulaN.neg (midseqExMkP (.var 9) (.var 1)))
  let ep := FormulaN.ex 0 (.all 1 (FormulaN.neg (midseqExMkP (.var 0) (.var 1))))
  let cf := FormulaN.ex 5 (.ex 6
    (.conj (midseqExMkP (.var 4) (.var 5)) (midseqExMkQ (.var 5) (.var 6))))
  have finTwo (R : Fin 2 → Prop) : (∃ i, R i) ↔ R 0 ∨ R 1 := by
    constructor
    · rintro ⟨⟨i, hi⟩, h⟩
      match i, hi with
      | 0, _ => exact Or.inl h
      | 1, _ => exact Or.inr h
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  have finTwoAll (R : Fin 2 → Prop) : (∀ i, R i) ↔ R 0 ∧ R 1 := by
    constructor
    · intro h
      exact ⟨h 0, h 1⟩
    · rintro ⟨h0, h1⟩ ⟨i, hi⟩
      match i, hi with
      | 0, _ => exact h0
      | 1, _ => exact h1
  have fresh3 : ∀ F ∈ ([] : List (FormulaN midseqExLang)) ++ ([np, c2] ++ [aq]),
      7 ∉ formulaFVN F := by
    intro F hF
    simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl
    all_goals simp [np, c2, aq, formulaFVN, midseqExMkP, midseqExMkQ,
      Membership.mem, Set.iUnion, Set.union, Set.diff, Set.singleton, termFV, vec2, midseqExLang, finTwo, finTwoAll]
  have fresh1 : ∀ F ∈ ([] : List (FormulaN midseqExLang)) ++ ([eq, c2] ++ [ap]),
      8 ∉ formulaFVN F := by
    intro F hF
    simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl
    all_goals simp [eq, c2, ap, formulaFVN, midseqExMkP, midseqExMkQ,
      Membership.mem, Set.iUnion, Set.union, Set.diff, Set.singleton, termFV, vec2, midseqExLang, finTwo, finTwoAll]
  have fresh4 : ∀ F ∈ ([] : List (FormulaN midseqExLang)) ++ ([ep, eq] ++ [.all 4 cf]),
      9 ∉ formulaFVN F := by
    intro F hF
    simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl
    all_goals simp [ep, eq, cf, formulaFVN, midseqExMkP, midseqExMkQ,
      Membership.mem, Set.iUnion, Set.union, Set.diff, Set.singleton, termFV, vec2, midseqExLang, finTwo, finTwoAll]
  let r1 : FOLKStep1 ⟨[], [np, nq, c0]⟩ ⟨[], [np, nq, c1]⟩ := by
    simpa [c0, c1, formulaSubstN, midseqExSubstP, midseqExSubstQ, termSubst] using
      (FOLKStep1.exRight (L := midseqExLang) (.var 7) 6
        (.conj (midseqExMkP (.var 9) (.var 8)) (midseqExMkQ (.var 8) (.var 6)))
        [] [np, nq] (by simp [c2, isFreeForN, midseqExMkP, midseqExMkQ, termFV, Membership.mem, Set.singleton]))
  let t1 := FOLKProofTree.onePremise r1 midsequentRenamedUpperTree
  let r2 : FOLKStep1 ⟨[], [np, nq, c1]⟩ ⟨[], [np, nq, c2]⟩ := by
    simpa [c1, c2, formulaSubstN, midseqExSubstP, midseqExSubstQ, termSubst] using
      (FOLKStep1.exRight (L := midseqExLang) (.var 8) 5
        (.ex 6 (.conj (midseqExMkP (.var 9) (.var 5)) (midseqExMkQ (.var 5) (.var 6))))
        [] [np, nq] (by simp [c2, isFreeForN, midseqExMkP, midseqExMkQ, termFV, Membership.mem, Set.singleton]))
  let t2 := FOLKProofTree.onePremise r2 t1
  let r3 : FOLKStep1 ⟨[], [np, c2, nq]⟩ ⟨[], [np, c2, aq]⟩ := by
    simpa [nq, aq, formulaSubstN, midseqExSubstQ, termSubst] using
      (FOLKStep1.allRight (L := midseqExLang) 7 3
        (.neg (midseqExMkQ (.var 8) (.var 3))) [] [np, c2] fresh3 (by simp [c2, isFreeForN, midseqExMkP, midseqExMkQ, termFV, Membership.mem, Set.singleton]))
  let t3 := FOLKProofTree.onePremise (.exchangeRight [] [np] c2 aq [])
    (.onePremise r3 (.onePremise (.exchangeRight [] [np] nq c2 []) t2))
  let r4 : FOLKStep1 ⟨[], [np, c2, aq]⟩ ⟨[], [np, c2, eq]⟩ := by
    simpa [aq, eq, formulaSubstN, midseqExSubstQ, termSubst] using
      (FOLKStep1.exRight (L := midseqExLang) (.var 8) 2
        (.all 3 (.neg (midseqExMkQ (.var 2) (.var 3)))) [] [np, c2] (by simp [c2, isFreeForN, midseqExMkP, midseqExMkQ, termFV, Membership.mem, Set.singleton]))
  let t4 := FOLKProofTree.onePremise (.exchangeRight [] [np] c2 eq [])
    (.onePremise r4 (.onePremise (.exchangeRight [] [np] aq c2 []) t3))
  let r5 : FOLKStep1 ⟨[], [eq, c2, np]⟩ ⟨[], [eq, c2, ap]⟩ := by
    simpa [np, ap, formulaSubstN, midseqExSubstP, termSubst] using
      (FOLKStep1.allRight (L := midseqExLang) 8 1
        (.neg (midseqExMkP (.var 9) (.var 1))) [] [eq, c2] fresh1 (by simp [c2, isFreeForN, midseqExMkP, midseqExMkQ, termFV, Membership.mem, Set.singleton]))
  let t5 := FOLKProofTree.onePremise (.exchangeRight [] [] eq ap [c2])
    (.onePremise (.exchangeRight [] [eq] c2 ap [])
      (.onePremise r5 (.onePremise (.exchangeRight [] [eq] np c2 [])
        (.onePremise (.exchangeRight [] [] np eq [c2]) t4))))
  let r6 : FOLKStep1 ⟨[], [eq, c2, ap]⟩ ⟨[], [eq, c2, ep]⟩ := by
    simpa [ap, ep, formulaSubstN, midseqExSubstP, termSubst] using
      (FOLKStep1.exRight (L := midseqExLang) (.var 9) 0
        (.all 1 (.neg (midseqExMkP (.var 0) (.var 1)))) [] [eq, c2] (by simp [c2, isFreeForN, midseqExMkP, midseqExMkQ, termFV, Membership.mem, Set.singleton]))
  let t6 := FOLKProofTree.onePremise (.exchangeRight [] [] eq ep [c2])
    (.onePremise (.exchangeRight [] [eq] c2 ep [])
      (.onePremise r6 (.onePremise (.exchangeRight [] [eq] ap c2 [])
        (.onePremise (.exchangeRight [] [] ap eq [c2]) t5))))
  let r7 : FOLKStep1 ⟨[], [ep, eq, c2]⟩ ⟨[], [ep, eq, .all 4 cf]⟩ := by
    simpa [c2, cf, formulaSubstN, midseqExSubstP, midseqExSubstQ, termSubst] using
      (FOLKStep1.allRight (L := midseqExLang) 9 4 cf [] [ep, eq] fresh4 (by simp [cf, isFreeForN, midseqExMkP, midseqExMkQ, termFV, Membership.mem, Set.singleton]))
  exact FOLKProofTree.onePremise r7 t6



-- ===================================================================
-- Example 7.3.4 (companion theorem): midsequentExampleSatisfiesConditions
-- ===================================================================

/-- Example 7.3.4 (companion theorem): The named quantifier-free midsequent
splits the connected displayed proof into its propositional/structural upper
part and quantifier/exchange suffix. The exact named upper subtree is identified
by midsequentExampleNode. The full split certificate is a separate proof obligation. -/
@[attach_debt, blueprint "chap7__example_7_3_4" (main := true)]
theorem midsequentExampleSatisfiesConditions :
    IsMidsequent midsequentExampleTree
      midsequentExampleMidseq 

/-- Example 7.3.4 (companion): Validity of the displayed end sequent is
exactly validity of its displayed right-associated disjunction A. -/
@[blueprint "chap7__example_7_3_4" (main := true)]
theorem midsequentExampleValidity :
    sequentValid midsequentExampleSequent ↔
      universallyValidN midsequentExampleEquivFormula 

/-- Example 7.3.4 (companion): Both the literal and freshly renamed
connected proofs are cut-free. -/
@[blueprint "chap7__example_7_3_4"]
theorem midsequentExampleCutFree :
    midsequentExampleTree.isCutFree ∧ midsequentRenamedTree.isCutFree 



/-- Example 7.3.4 (companion): The explicit 7/8/9 representative is a
fresh, capture-free variable-only replacement with exactly the same ordered
rule tree and end sequent as the literal diagram. -/
theorem midsequentExampleFreshReplacement :
    proofVariableReplacementLK midsequentExampleTree midsequentRenamedTree := by
-- BEGIN PROOF
  -- REPAIR(T7-126): proof pending
  sorry

/-- Example 7.3.4 (companion): The explicitly fresh representative satisfies
all-occurrence purity and has its own named, connected midsequent. This purity
claim is about the 7/8/9 representative, not the literal bound-name reuse. -/
@[attach_debt, blueprint "chap7__example_7_3_4"]
theorem midsequentRenamedPure :
    IsPureVariableProofLK midsequentRenamedTree ∧
      IsMidsequent midsequentRenamedTree midsequentRenamedMidseq 

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 7.3.4 (companion): Successive quantifier choices in backward
construction, omitting the intervening mandatory exchanges. Each entry is the
actual node address, whether the rule is universal-right, and its binder. -/
def midsequentBackwardSchedule : List (List Nat × Bool × Nat) :=
  [([], true, 4), (List.replicate 3 0, false, 0),
   (List.replicate 8 0, true, 1), (List.replicate 12 0, false, 2),
   (List.replicate 15 0, true, 3), (List.replicate 17 0, false, 5),
   (List.replicate 18 0, false, 6)]

/-- Example 7.3.4 (companion): At each listed backward quantifier-choice
state, the recorded rule is the actual legal inference. Whenever a universal
formula is exposed in that state's succedent, universal-right is chosen.
This is a local convention on this concrete construction, not a claim about
completeness or optimality of a general search procedure. -/
theorem midsequentBackwardForallFirst :
    ∀ a universal x, (a, universal, x) ∈ midsequentBackwardSchedule →
      ∃ (p c : Sequent midseqExLang) (r : FOLKStep1 p c),
        lkInferenceAt midsequentExampleTree a = some (.one r) ∧
        (match r with
          | .allRight _ binder .. => universal = true ∧ binder = x
          | .exRight _ binder .. => universal = false ∧ binder = x
          | _ => False) ∧
        ((∃ v A, FormulaN.all v A ∈ c.succedent) → universal = true) := by
-- BEGIN PROOF
  -- REPAIR(T7-126): proof pending
  sorry

-- ===================================================================
-- Theorem 7.3.1: sharpenedHauptsatz_LK
-- ===================================================================

/-- Theorem 7.3.1: Over a language without equality, an LK-provable prenex
sequent satisfying the chapter's sequent-wide free/bound variable convention
has a cut-free pure-variable proof of the same sequent with a midsequent.
The convention is imposed on the end/input sequent. Purity uses actual
node occurrences, and the midsequent selects one node shared by the upper
and lower phases: its formulae are quantifier-free, its upper rules are
structural or propositional (or atomic cuts), and its lower rules are
quantifier, contraction, or exchange rules. The lower phase may be empty. -/
@[attach_debt, blueprint "chap7__theorem_7_3_1" (main := true)]
theorem sharpenedHauptsatz_LK {L : Language}
    (hL : L.withoutEquality) (seq : Sequent L)
    (hCross : Hintikka.crossNoFreeBound seq)
    (hAllPrenex : allSequentFormulaeArePrenex seq)
    (hprov : folkProvable seq) :
    ∃ (t : FOLKProofTree seq) (mid : Sequent L),
      t.isCutFree ∧
      IsPureVariableProofLK t ∧
      IsMidsequent t mid 

-- ===================================================================
-- Theorem 7.3.1 (companion theorem): sharpenedHauptsatz_LKe
-- ===================================================================

/-- Theorem 7.3.1 (companion LKₑ variant): An LKₑ-provable prenex sequent
satisfying the chapter's sequent-wide free/bound variable convention has a
pure-variable proof of the same sequent without essential cuts and with a
midsequent. The convention is imposed on the end/input sequent. The genuine
LKₑ proof uses occurrence-based purity and a single selected midsequent node;
atomic cuts are permitted in the upper phase, and the lower phase may be empty. -/
@[attach_debt, blueprint "chap7__theorem_7_3_1" (main := true)]
theorem sharpenedHauptsatz_LKe {L : Language}
    (seq : Sequent L)
    (hCross : Hintikka.crossNoFreeBound seq)
    (hAllPrenex : allSequentFormulaeArePrenex seq)
    (hprov : lkeProvable seq) :
    ∃ (t : LKeProofTree seq) (mid : Sequent L),
      IsPureVariableProofLKe t ∧
      IsMidsequentLKe t mid ∧
      noEssentialCuts t 

end LCS.Herbrand.SharpenedHauptsatz.Theorem
end

