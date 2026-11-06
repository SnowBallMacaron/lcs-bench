import LCS.Item
import LCS.Util
import LCS.Herbrand.SharpenedHauptsatz
import LCS.Herbrand.SharpenedHauptsatz.Permutability
import LCS.Herbrand.PrenexForm
import LCS.Herbrand.SharpenedHauptsatz.Theorem.SharpenedHauptsatz
import Attach
import LCS.Herbrand.SharpenedHauptsatz.Theorem.PermutationExample.ProofsStamp

/-! # Herbrand.SharpenedHauptsatz.Theorem.PermutationExample
    Chapter 7, Section 3.3: Example 7.3.3. A proof of
    P(f(a)) v R(g(a)) -> Ex P(x), Ey R(y) with m(T) = 2 and n(T) = 0, and the
    successive permutations of the exists-right inferences with the or-left
    inference that reach a proof with m(T) = 0 and n(T) = 0.

    Source: Logic for Computer Science, Gallier 2015
-/

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

/-- Example 7.3.3 (companion type): Predicate symbols for the permutation example. P and R are unary predicates used in the sequent P(f(a)) or R(g(a)) -> exists x P(x), exists y R(y). -/
@[blueprint "chap7__example_7_3_3"]
inductive PermExPred : Type where
  /-- Unary predicate P -/
  | P : PermExPred
  /-- Unary predicate R -/
  | R : PermExPred

-- ===================================================================
-- Example 7.3.3 (companion type): PermExFunc
-- ===================================================================

/-- Example 7.3.3 (companion type): Function symbols for the permutation example. f and g are unary functions used in the sequent P(f(a)) or R(g(a)) -> exists x P(x), exists y R(y). -/
@[blueprint "chap7__example_7_3_3"]
inductive PermExFunc : Type where
  /-- Unary function f -/
  | f : PermExFunc
  /-- Unary function g -/
  | g : PermExFunc

-- ===================================================================
-- Example 7.3.3 (companion type): PermExConst
-- ===================================================================

/-- Example 7.3.3 (companion type): Constant symbols for the permutation example. The constant a is used in the terms f(a) and g(a). -/
@[blueprint "chap7__example_7_3_3"]
inductive PermExConst : Type where
  /-- Constant a -/
  | a : PermExConst

-- ===================================================================
-- Example 7.3.3 (companion def): permExLang
-- ===================================================================

/-- Example 7.3.3 (companion def): An equality-free language with unary predicates P, R; unary functions f, g; and constant a. Used for the permutation example sequent P(f(a)) or R(g(a)) -> exists x P(x), exists y R(y). -/
@[blueprint "chap7__example_7_3_3"]
def permExLang : Language where
  funSymbols := PermExFunc
  funArity := fun _ => 1
  constSymbols := PermExConst
  predSymbols := PermExPred
  predArity := fun _ => 1
  hasEquality := false

-- ===================================================================
-- Example 7.3.3 (companion def): permutationExampleSequent
-- ===================================================================

/-- Example 7.3.3 (companion def): The sequent P(f(a)) or R(g(a)) -> exists x P(x), exists y R(y). Variables: x = 0, y = 1. -/
@[blueprint "chap7__example_7_3_3"]
def permutationExampleSequent : Sequent permExLang :=
  let fa := Term.func PermExFunc.f
    (fun _ => Term.const PermExConst.a)
  let ga := Term.func PermExFunc.g
    (fun _ => Term.const PermExConst.a)
  let pfa := FormulaN.predN PermExPred.P (fun _ => fa)
  let rga := FormulaN.predN PermExPred.R (fun _ => ga)
  let pfaOrRga := FormulaN.disj pfa rga
  let exPx := FormulaN.ex 0
    (FormulaN.predN PermExPred.P (fun _ => Term.var 0))
  let exRy := FormulaN.ex 1
    (FormulaN.predN PermExPred.R (fun _ => Term.var 1))
  { antecedent := [pfaOrRga]
    succedent := [exPx, exRy] }

-- ===================================================================
-- Example 7.3.3: permutationExampleTree
-- ===================================================================

/-- Example 7.3.3: The printed initial tree T, with both weakenings above
the exists-right inferences, and both quantifier inferences above or-left.
Explicit exchanges place each selected formula last for the indexed exRight
rule and restore the printed succedent. Thus m(T)=2 and n(T)=0. -/
@[blueprint "chap7__example_7_3_3" (main := true)]
def permutationExampleTree : FOLKProofTree permutationExampleSequent :=
  let fa : Term permExLang := .func .f (fun _ => .const .a)
  let ga : Term permExLang := .func .g (fun _ => .const .a)
  let pfa : FormulaN permExLang := .predN .P (fun _ => fa)
  let rga : FormulaN permExLang := .predN .R (fun _ => ga)
  let px : FormulaN permExLang := .predN .P (fun _ => .var 0)
  let ry : FormulaN permExLang := .predN .R (fun _ => .var 1)
  let exPx := FormulaN.ex 0 px
  let exRy := FormulaN.ex 1 ry
  .twoPremise (.orLeft pfa rga [] [exPx, exRy])
    (.onePremise (.exchangeRight [pfa] [] exRy exPx [])
      (.onePremise (.exRight fa 0 px [pfa] [exRy] (by trivial))
        (.onePremise (.exchangeRight [pfa] [] pfa exRy [])
          (.onePremise (.weakenRight exRy [pfa] [pfa])
            (.axiom_ ⟨[pfa], [pfa]⟩ ⟨pfa, rfl, rfl⟩)))))
    (.onePremise (.exRight ga 1 ry [rga] [exPx] (by trivial))
      (.onePremise (.exchangeRight [rga] [] rga exPx [])
        (.onePremise (.weakenRight exPx [rga] [rga])
          (.axiom_ ⟨[rga], [rga]⟩ ⟨rga, rfl, rfl⟩))))

/-- Example 7.3.3 (companion): The displayed atom P(f(a)). -/
@[blueprint "chap7__example_7_3_3"]
def permExPfa : FormulaN permExLang :=
  .predN .P (fun _ => .func .f (fun _ => .const .a))

/-- Example 7.3.3 (companion): The displayed atom R(g(a)). -/
@[blueprint "chap7__example_7_3_3"]
def permExRga : FormulaN permExLang :=
  .predN .R (fun _ => .func .g (fun _ => .const .a))

/-- Example 7.3.3 (companion): The displayed existential ∃xP(x), x=0. -/
@[blueprint "chap7__example_7_3_3"]
def permExExistsP : FormulaN permExLang :=
  .ex 0 (.predN .P (fun _ => .var 0))

/-- Example 7.3.3 (companion): The displayed existential ∃yR(y), y=1. -/
@[blueprint "chap7__example_7_3_3"]
def permExExistsR : FormulaN permExLang :=
  .ex 1 (.predN .R (fun _ => .var 1))

/-- Example 7.3.3 (companion): Intermediate-stage T₁. The original left
branch retains its ∃x-right inference and receives the displayed weakening by
R(g(a)) below it. The earlier weakening by ∃yR(y) remains above that inference. -/
@[blueprint "chap7__example_7_3_3"]
def permutationExampleIntermediateT1 :
    FOLKProofTree ⟨[permExPfa], [permExExistsP, permExExistsR, permExRga]⟩ :=
  .onePremise (.weakenRight permExRga [permExPfa] [permExExistsP, permExExistsR])
    (.onePremise (.exchangeRight [permExPfa] [] permExExistsR permExExistsP [])
      (.onePremise (FOLKStep1.exRight (L := permExLang) (.func .f (fun _ => .const .a)) 0
          (.predN .P (fun _ => .var 0)) [permExPfa] [permExExistsR] (by trivial))
        (.onePremise (.exchangeRight [permExPfa] [] permExPfa permExExistsR [])
          (.onePremise (.weakenRight permExExistsR [permExPfa] [permExPfa])
            (.axiom_ ⟨[permExPfa], [permExPfa]⟩ ⟨permExPfa, rfl, rfl⟩)))))

/-- Example 7.3.3 (companion): Intermediate-stage T₂. Starting with the
right identity axiom, retain the first weakening by ∃xP(x), add ∃yR(y), and
exchange to the exact printed succedent ∃xP(x), ∃yR(y), R(g(a)). -/
@[blueprint "chap7__example_7_3_3"]
def permutationExampleIntermediateT2 :
    FOLKProofTree ⟨[permExRga], [permExExistsP, permExExistsR, permExRga]⟩ :=
  .onePremise (.exchangeRight [permExRga] [permExExistsP] permExRga permExExistsR [])
    (.onePremise (.exchangeRight [permExRga] [] permExRga permExExistsP [permExExistsR])
      (.onePremise (.weakenRight permExExistsR [permExRga] [permExRga, permExExistsP])
        (.onePremise (.weakenRight permExExistsP [permExRga] [permExRga])
          (.axiom_ ⟨[permExRga], [permExRga]⟩ ⟨permExRga, rfl, rfl⟩))))

/-- Example 7.3.3 (companion): The displayed intermediate whole tree after
moving the right ∃y-right below or-left. The printed T₁/T₂ conclude the two
or-left premises; ∃y-right produces a duplicate ∃yR(y), then contraction
restores the original end sequent. Its measures are (m,n)=(1,1). -/
@[blueprint "chap7__example_7_3_3"]
def permutationExampleIntermediateTree : FOLKProofTree permutationExampleSequent :=
  .onePremise (.contractRight permExExistsR [.disj permExPfa permExRga] [permExExistsP])
    (.onePremise (FOLKStep1.exRight (L := permExLang) (.func .g (fun _ => .const .a)) 1
        (.predN .R (fun _ => .var 1)) [.disj permExPfa permExRga]
        [permExExistsP, permExExistsR] (by trivial))
      (.twoPremise (.orLeft permExPfa permExRga []
          [permExExistsP, permExExistsR, permExRga])
        permutationExampleIntermediateT1 permutationExampleIntermediateT2))

-- ===================================================================
-- Example 7.3.3 (companion def): permutedExampleTree
-- ===================================================================



/-- Example 7.3.3 (companion): Printed final-stage T₁, with weakenings by
∃xP(x), ∃yR(y), and R(g(a)), followed by exchanges placing P(f(a)) last. -/
@[blueprint "chap7__example_7_3_3"]
def permutationExampleFinalT1 : FOLKProofTree
    ⟨[permExPfa], [permExExistsP, permExExistsR, permExRga, permExPfa]⟩ :=
  .onePremise (.exchangeRight [permExPfa] [permExExistsP, permExExistsR] permExPfa permExRga [])
    (.onePremise (.exchangeRight [permExPfa] [permExExistsP] permExPfa permExExistsR [permExRga])
      (.onePremise (.exchangeRight [permExPfa] [] permExPfa permExExistsP [permExExistsR, permExRga])
        (.onePremise (.weakenRight permExRga [permExPfa] [permExPfa, permExExistsP, permExExistsR])
          (.onePremise (.weakenRight permExExistsR [permExPfa] [permExPfa, permExExistsP])
            (.onePremise (.weakenRight permExExistsP [permExPfa] [permExPfa])
              (.axiom_ ⟨[permExPfa], [permExPfa]⟩ ⟨permExPfa, rfl, rfl⟩))))))

/-- Example 7.3.3 (companion): Printed final-stage T₂ retains the intermediate
right subtree and weakens by P(f(a)) at the end. -/
@[blueprint "chap7__example_7_3_3"]
def permutationExampleFinalT2 : FOLKProofTree
    ⟨[permExRga], [permExExistsP, permExExistsR, permExRga, permExPfa]⟩ :=
  .onePremise (.weakenRight permExPfa [permExRga] [permExExistsP, permExExistsR, permExRga])
    permutationExampleIntermediateT2

/-- Example 7.3.3 (companion): The printed final tree. Both existential
context formulas remain at or-left. The ∃x-right step creates a duplicate
∃xP(x), removed by exchanges/contraction; ∃y-right then creates a duplicate
∃yR(y), removed by contraction. This raw separation stage is not the cleaned
quantifier-free midsequent proof. -/
@[blueprint "chap7__example_7_3_3" (main := true)]
def permutedExampleTree : FOLKProofTree permutationExampleSequent :=
  let Γ := [FormulaN.disj permExPfa permExRga]
  let core := FOLKProofTree.twoPremise
    (.orLeft permExPfa permExRga [] [permExExistsP, permExExistsR, permExRga, permExPfa])
    permutationExampleFinalT1 permutationExampleFinalT2
  let quantified := FOLKProofTree.onePremise
    (FOLKStep1.exRight (L := permExLang) (.func .f (fun _ => .const .a)) 0
      (.predN .P (fun _ => .var 0)) Γ [permExExistsP, permExExistsR, permExRga] (by trivial)) core
  let contractP := FOLKProofTree.onePremise
    (.exchangeRight Γ [permExExistsP] permExRga permExExistsR [])
    (.onePremise (.exchangeRight Γ [] permExRga permExExistsP [permExExistsR])
      (.onePremise (.exchangeRight Γ [permExRga] permExExistsR permExExistsP [])
        (.onePremise (.contractRight permExExistsP Γ [permExRga, permExExistsR])
          (.onePremise (.exchangeRight Γ [permExRga] permExExistsP permExExistsR [permExExistsP])
            (.onePremise (.exchangeRight Γ [] permExExistsP permExRga [permExExistsR, permExExistsP])
              (.onePremise (.exchangeRight Γ [permExExistsP] permExExistsR permExRga [permExExistsP]) quantified))))))
  .onePremise (.contractRight permExExistsR Γ [permExExistsP])
    (.onePremise (FOLKStep1.exRight (L := permExLang) (.func .g (fun _ => .const .a)) 1
      (.predN .R (fun _ => .var 1)) Γ [permExExistsP, permExExistsR] (by trivial)) contractP)

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

end LCS.Herbrand.SharpenedHauptsatz.Theorem
