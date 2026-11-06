import LCS.Item
import LCS.Util
import LCS.FOResolution.Method.SeparatingPairs
import Attach
import LCS.SLD.FirstOrder.SLDDerivations.ProofsStamp

noncomputable section
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN
open LCS.FOResolution.ClauseForm LCS.FOResolution.Unification LCS.FOResolution.Method

@[blueprint "chap9__definition_9_4_1"]
noncomputable instance {L : Language} : DecidableEq (FOAtomCore L) :=
  fun a b => Classical.propDecidable (a = b)

@[simp] theorem finset_toList_singleton {α : Type} (a : α) :
    (LCS.Finset.singleton a).toList = [a] := by
  have hp : (LCS.Finset.singleton a).toList.Perm [a] :=
    Quotient.exact (LCS.Finset.toList_ofList_eq (LCS.Finset.singleton a))
  exact List.perm_singleton.mp hp

@[simp] theorem finset_toList_empty {α : Type} :
    (∅ : LCS.Finset α).toList = [] := by
  have hp : (∅ : LCS.Finset α).toList.Perm [] :=
    Quotient.exact (LCS.Finset.toList_ofList_eq (∅ : LCS.Finset α))
  exact List.perm_nil.mp hp

-- ===================================================================
-- Definition 9.4.1: First-order Horn clause in PROLOG notation
-- ===================================================================

/-- Horn clauses with finite sets of body atoms (SQ16). -/
@[blueprint "chap9__theorem_9_4_1"]
inductive FOHornClauseCore (L : Language) : Type where
  | rule : FOAtomCore L → LCS.Finset (FOAtomCore L) → FOHornClauseCore L
  | fact : FOAtomCore L → FOHornClauseCore L
  | goal : LCS.Finset (FOAtomCore L) → FOHornClauseCore L

namespace FOHornClauseCore

def isDefinite {L : Language} : FOHornClauseCore L → Prop
  | .rule _ _ | .fact _ => True
  | .goal _ => False

def headFOAtom {L : Language} : FOHornClauseCore L → Option (FOAtomCore L)
  | .rule head _ | .fact head => some head
  | .goal _ => none

/-- The extensional body; a fact has empty body (SQ16). -/
@[blueprint "chap9__definition_9_4_1"]
def body {L : Language} : FOHornClauseCore L → LCS.Finset (FOAtomCore L)
  | .rule _ body | .goal body => body
  | .fact _ => ∅

/-- An enumeration for the list-based first-order clause interface. -/
def bodyFOAtoms {L : Language} (c : FOHornClauseCore L) : List (FOAtomCore L) :=
  c.body.toList

def toFOClause {L : Language} : FOHornClauseCore L → FOClauseCore L
  | .rule head body => body.toList.map FOLiteralCore.neg ++ [FOLiteralCore.pos head]
  | .fact head => [FOLiteralCore.pos head]
  | .goal body => body.toList.map FOLiteralCore.neg

/-- Substitution image collapses coincident body atoms (SQ16). -/
def subst {L : Language} (σ : Nat → Term L) : FOHornClauseCore L → FOHornClauseCore L
  | .rule head body => .rule (head.mapTerms (fun t => termSubstAll t σ))
      (body.image (fun a => a.mapTerms (fun t => termSubstAll t σ)))
  | .fact head => .fact (head.mapTerms (fun t => termSubstAll t σ))
  | .goal body => .goal (body.image (fun a => a.mapTerms (fun t => termSubstAll t σ)))
end FOHornClauseCore

/-- Predicate-argument equations, with the chapter 8 global MGU factorization. -/
def atomUnifPairsCore {L : Language} (reference atom : FOAtomCore L) :
    Option (List (Term L × Term L)) := by
  classical
  exact match reference, atom with
    | .predN P referenceArgs, .predN Q args =>
        if h : P = Q then
          some (List.ofFn (fun i =>
            (referenceArgs i, args (i.cast (congrArg L.predArity h)))))
        else none
    | _, _ => none

def IsAtomMGUCore {L : Language} (reference atom : FOAtomCore L)
    (σ : Nat → Term L) : Prop :=
  ∃ pairs, atomUnifPairsCore reference atom = some pairs ∧ IsPairwiseMGU σ pairs

/-- Local separating renamings with support contained in the input clauses (SQ22). -/
def IsSeparatingPairCore {L : Language} (ρ ρ' : Nat → Term L)
    (A A' : FOClauseCore L) : Prop :=
  substIsVarOnSet ρ A.vars ∧ substIsVarOnSet ρ' A'.vars ∧
  substInjectiveOnSet ρ A.vars ∧ substInjectiveOnSet ρ' A'.vars ∧
  Set.inter (substRangeOnSet ρ A.vars) (substRangeOnSet ρ' A'.vars) = Set.empty ∧
  (∀ x, ¬ A.vars x → ρ x = Term.var x) ∧
  (∀ x, ¬ A'.vars x → ρ' x = Term.var x)

/-- Finite SLD-derivations over an arbitrary ambient program (SQ17).
    Ordered clause uses and renamings belong to steps; goals are finite sets. -/
inductive FOSLDDerivationCore {L : Language}
    (D : Set (FOHornClauseCore L)) (goals : List (FOHornClauseCore L)) :
    LCS.Finset (FOAtomCore L) → Type where
  | init (goal : FOHornClauseCore L) (hGoal : goal ∈ goals) :
      FOSLDDerivationCore D goals (LCS.Finset.ofList goal.bodyFOAtoms)
  | step {prevGoal : LCS.Finset (FOAtomCore L)}
      (prev : FOSLDDerivationCore D goals prevGoal)
      (clause : FOHornClauseCore L) (hClause : clause ∈ D)
      (hDef : clause.isDefinite) (Ak headA : FOAtomCore L)
      (hAk : Ak ∈ prevGoal) (hHead : clause.headFOAtom = some headA)
      (rho sigma : Nat → Term L)
      (hMGU : IsAtomMGUCore Ak (headA.mapTerms (fun t => termSubstAll t rho)) sigma)
      (hSep : IsSeparatingPairCore Term.var rho
        (prevGoal.toList.map FOLiteralCore.neg) clause.toFOClause) :
      FOSLDDerivationCore D goals
        (((prevGoal.erase Ak).union
          (LCS.Finset.ofList (clause.bodyFOAtoms.map
            (fun a => a.mapTerms (fun t => termSubstAll t rho))))).image
          (fun a => a.mapTerms (fun t => termSubstAll t sigma)))

end LCS.SLD.FirstOrder
end
