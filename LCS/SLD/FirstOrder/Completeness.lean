import LCS.Item
import LCS.Util
import LCS.SLD.Propositional
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import LCS.FOResolution.Method
import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.Method.Completeness
import LCS.Herbrand.SHGTheorem.Main
import LCS.SLD.FirstOrder.HornClauses
import LCS.SLD.FirstOrder.SLDRefutations
import LCS.SLD.FirstOrder.Lifting
import LCS.SLD.FirstOrder.HornEncoding
import LCS.SLD.FirstOrder.GroundInstanceSemantics
import LCS.SLD.FirstOrder.PropositionalReflection
import Attach
import LCS.SLD.FirstOrder.Completeness.ProofsStamp

/-! # Completeness of SLD-resolution for Horn clauses (Theorem 9.4.1)

Section 9.4.2: a finite unsatisfiable set of Horn clauses over a language without equality has an SLD-refutation, with any atom of the goal selectable first. -/

section
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.Completeness
namespace GroundUnsatContractRegression
open LCS.FirstOrder.SyntaxN.Variables

-- ATTACH-BLOCKER: unsupported untagged inductive
inductive AdvPred where
  | p | q
  deriving DecidableEq

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
def advLang : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := Empty
  predSymbols := AdvPred
  predArity := fun _ => 0
  hasEquality := false

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
def p : FOAtom advLang rfl :=
  .predN AdvPred.p (fun i => Fin.elim0 i)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
def q : FOAtom advLang rfl :=
  .predN AdvPred.q (fun i => Fin.elim0 i)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
def D : List (FOHornClause advLang (by all_goals rfl)) := [FOHornClause.fact p rfl]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
def goals : List (FOHornClause advLang (by all_goals rfl)) := [FOHornClause.goal (LCS.Finset.singleton q) rfl,
  FOHornClause.goal (LCS.Finset.singleton p) rfl]

end GroundUnsatContractRegression

/-- Theorem 9.4.1: an equality-free finite unsatisfiable Horn set has an
    SLD-refutation starting at a negative clause in that same set. Every atom
    of the chosen successful initial goal can be selected first (SQ20). -/
@[attach_debt, blueprint "chap9__theorem_9_4_1" (main := true)]
theorem foSLDResolution_complete
    {L : Language} (hNoEq : L.withoutEquality) (Afalsum : FormulaN L)
    (S D goals : List (FOHornClause L hNoEq))
    (hS : S = D ++ goals)
    (hD : ∀ c ∈ D, c.isDefinite)
    (hGoals : ∀ c ∈ goals, ¬ c.isDefinite)
    (hUnsat : FOHornClauseSet.isUnsatisfiable hNoEq Afalsum S) :
    ∃ initGoal ∈ goals,
      Nonempty (FOSLDDerivation hNoEq (fun c => c ∈ D) [initGoal] ∅) ∧
      ∀ Bi ∈ initGoal.body,
        ∃ d : FOSLDDerivation hNoEq (fun c => c ∈ D) [initGoal] ∅,
          FOSLDDerivation.firstSelectedAtom hNoEq d = some Bi

end LCS.SLD.FirstOrder
end
