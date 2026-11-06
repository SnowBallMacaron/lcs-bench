import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import Attach
import LCS.Propositional.Systems.G.Search.Expansion
import LCS.Propositional.Systems.G.Search.Procedure.ProofsStamp

/-! # Procedure search (Definition 3.4.6) and its termination

Rounds of expansion steps, the complexity of propositions and sequents, the
decrease of complexity in every round (first part of Theorem 3.4.1), and
procedure search, defined by well-founded recursion on that measure.
-/
section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
variable {mode : SearchMode}

-- ========= Complexity measures (needed by search fuel) =========

/-- Definition 3.4.6 (required helper): The complexity of a proposition is the
    number of logical connectives occurring in it, used as the per-formula
    component of the termination measure for `search`. -/
@[blueprint "chap3__definition_3_4_6"]
def formulaComplexity : PropFormulaNormalized → Nat
  | .var _ => 0
  | .neg A => 1 + formulaComplexity A
  | .conj A B => 1 + formulaComplexity A + formulaComplexity B
  | .disj A B => 1 + formulaComplexity A + formulaComplexity B
  | .impl A B => 1 + formulaComplexity A + formulaComplexity B

/-- Definition 3.4.6 (required helper): The complexity of a sequent is the
    sum of the complexities of all propositions in the sequent, used as the
    termination measure inside `search`'s body (Lean's termination checker
    requires the measure to be in-scope at the def-site). The textbook
    introduces complexity in Thm 3.4.1's proof but our Lean encoding lifts
    it to Def 3.4.6's termination position. -/
@[blueprint "chap3__definition_3_4_6"]
def sequentComplexity (s : Sequent) : Nat :=
  (s.antecedent.map formulaComplexity).foldl (· + ·) 0 +
  (s.succedent.map formulaComplexity).foldl (· + ·) 0

-- ========= Definition 3.4.6: searchRound and search =========

/-- Definition 3.4.6 (companion): Collects all unfinished leaves from a
    deduction tree (leaves that are not finished). -/
@[blueprint "chap3__definition_3_4_6"]
def unfinishedLeaves (mode : SearchMode) {s : Sequent} (dt : DeductionTree s) : List Sequent :=
  dt.leaves.filter (fun s => !isFinishedLeafBool mode s)

/-- Definition 3.4.6: Expand each leaf of the input tree once. Each
    expansion follows that leaf's frozen formula schedule. -/
@[blueprint "chap3__definition_3_4_6"]
def searchRound (mode : SearchMode) {s : Sequent} (dt : DeductionTree s) : DeductionTree s :=
  mapLeaves (expandLeaf mode) dt

/-- Definition 3.4.6 (companion): The maximum sequent complexity among
    all unfinished leaves. This strictly decreases each round of the
    search procedure because every unfinished leaf takes at least one
    rule step, reducing the maximum complexity by at least 1.
    Used as the termination measure for search. -/
@[blueprint "chap3__definition_3_4_6"]
def maxUnfinishedLeafComplexity (mode : SearchMode) {s : Sequent} (dt : DeductionTree s) : Nat :=
  (unfinishedLeaves mode dt |>.map sequentComplexity).foldl max 0

/-- Example 3.4.4 (required helper): Collects all non-axiom leaves from
    a deduction tree. -/
@[blueprint "chap3__example_3_4_4"]
def nonAxiomLeaves {s : Sequent} (dt : DeductionTree s) : List Sequent :=
  dt.leaves.filter (fun s =>
    !(s.antecedent.any (fun A => s.succedent.any (fun B => A == B))))

/-- searchRound strictly decreases maxUnfinishedLeafComplexity when
    the tree has unfinished leaves. This is the key termination argument. -/
@[blueprint "chap3__theorem_3_4_1"]
theorem searchRound_complexity_decrease {c : Sequent} (dt : DeductionTree c)
    (hunf : ¬isFinishedTreeBool mode dt = true) :
    maxUnfinishedLeafComplexity mode (searchRound mode dt) <
      maxUnfinishedLeafComplexity mode dt 

/-- Definition 3.4.6: Procedure search. The input to search is a one-node
    tree labeled with a sequent Γ → Δ; the output is a finished tree T
    called a systematic or atomically closed deduction tree. Implements the while-loop of
    Definition 3.4.6: repeatedly applies searchRound until all leaves
    are finished (isFinishedTree). Terminates because maxUnfinishedLeafComplexity
    strictly decreases each round — each round decomposes at least one
    nonatomic formula in every unfinished leaf.

    The strict decrease theorem supplies the recursive termination proof. -/
@[blueprint "chap3__definition_3_4_6" (main := true)]
def search (mode : SearchMode) {s : Sequent} (dt : DeductionTree s) : DeductionTree s :=
  if _h : isFinishedTreeBool mode dt then dt
  else search mode (searchRound mode dt)
termination_by maxUnfinishedLeafComplexity mode dt
decreasing_by exact searchRound_complexity_decrease dt _h

/-- Definition 3.4.6 (companion): Entry point for the search procedure:
    starts with a one-node tree labeled with the input sequent, then
    applies search to repeatedly expand leaves until all are finished. -/
@[blueprint "chap3__definition_3_4_6"]
def searchStart (mode : SearchMode) (s : Sequent) : DeductionTree s :=
  search mode (DeductionTree.leaf s)

end LCS.Propositional.Systems.G.Search
end
