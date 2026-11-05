import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import Attach
import LCS.Propositional.Systems.G.Search.SearchRounds.ProofsStamp
import LCS.Propositional.Systems.G.Search.LeafExpansion
attach_helper_namespace LCS.Propositional.Systems.G.Search.Proofs

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
variable {mode : SearchMode}

@[blueprint "chap3__definition_3_4_6"]
def selectOffset (offset : Nat) (L : List PropFormulaNormalized) :
    Option (PropFormulaNormalized × Nat) :=
  let i := L.length - (offset + 1)
  L[i]?.map (fun A => (A, i))

@[blueprint "chap3__definition_3_4_6"]
theorem selectOffset_split (offset : Nat) (L : List PropFormulaNormalized)
    (A : PropFormulaNormalized) (i : Nat)
    (h : selectOffset offset L = some (A, i)) :
    L = L.take i ++ [A] ++ L.drop (i + 1) 

/-- A frozen schedule records the side and number of original occurrences
    to the right. The untouched suffix keeps these addresses stable when
    earlier rules insert formulas, including equal formulas. -/
@[blueprint "chap3__definition_3_4_6"]
def expandScheduled (mode : SearchMode) (rightSide : Bool) (offset : Nat) (s : Sequent) :
    DeductionTree s :=
  if isFinishedLeafBool mode s then .leaf s
  else if rightSide then
    expandSelected s none (selectOffset offset s.succedent)
      (by intros; contradiction) (selectOffset_split offset s.succedent)
  else
    expandSelected s (selectOffset offset s.antecedent) none
      (selectOffset_split offset s.antecedent) (by intros; contradiction)

@[blueprint "chap3__definition_3_4_6"]
def expandSchedule (mode : SearchMode) {s : Sequent} (schedule : List (Bool × Nat))
    (tree : DeductionTree s) : DeductionTree s :=
  schedule.foldl (fun dt entry => mapLeaves (expandScheduled mode entry.1 entry.2) dt) tree

@[blueprint "chap3__definition_3_4_6"]
def suffixSchedule (rightSide : Bool) (count : Nat) : List (Bool × Nat) :=
  (List.range count).reverse.map (fun offset => (rightSide, offset))

/-- Definition 3.4.6: Expand every formula present in the original leaf,
    antecedent first and then succedent. Systematic mode stops at axioms;
    atomic mode continues through them. Newly introduced subformulas wait
    for the next round. -/
@[blueprint "chap3__definition_3_4_6"]
def expandLeaf (mode : SearchMode) (s : Sequent) : DeductionTree s :=
  if isFinishedLeafBool mode s then .leaf s
  else
    let remaining := match findFirstNonatomic s.antecedent with
      | some (_, i) => suffixSchedule false (s.antecedent.length - (i + 1)) ++
          suffixSchedule true s.succedent.length
      | none => match findFirstNonatomic s.succedent with
        | some (_, i) => suffixSchedule true (s.succedent.length - (i + 1))
        | none => []
    expandSchedule mode remaining (expandFirstFormula s)

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

-- ========= Example 3.4.4: Search procedure trace =========

/-- Example 3.4.4: The input sequent
    (P and neg Q), (P implies Q), (T implies R), (P and S) -> T,
    using PropFormulaNormalized constructors with var 0 = P, var 1 = Q, var 2 = R,
    var 3 = S, var 4 = T. -/
@[blueprint "chap3__example_3_4_4" (main := true)]
def exSearchTraceSequent : Sequent :=
  let p := PropFormulaNormalized.var 0
  let q := PropFormulaNormalized.var 1
  let r := PropFormulaNormalized.var 2
  let s := PropFormulaNormalized.var 3
  let t := PropFormulaNormalized.var 4
  Sequent.mk
    [.conj p (.neg q), .impl p q, .impl t r, .conj p s]
    [t]

/-- Example 3.4.4 (companion): The deduction tree after the first round
    of the search procedure applied to exSearchTraceSequent. Expands each
    nonatomic formula in the antecedent: (P and neg Q) via andLeft,
    (P implies Q) via implLeft, (T implies R) via implLeft,
    (P and S) via andLeft. -/
@[blueprint "chap3__example_3_4_4"]
def exSearchTraceRound1 : DeductionTree exSearchTraceSequent :=
  searchRound .systematic (DeductionTree.leaf exSearchTraceSequent)

/-- Example 3.4.4 (companion): The finished deduction tree after the
    second round, which expands the remaining nonatomic formula (neg Q)
    via negLeft in each unfinished leaf. All leaves are now finished
    (either axioms or fully atomic). This is the systematic deduction
    tree. -/
@[blueprint "chap3__example_3_4_4"]
def exSearchTraceRound2 : DeductionTree exSearchTraceSequent :=
  searchRound .systematic exSearchTraceRound1

/-- Example 3.4.4: The complete displayed round-1 tree, including
    the unchanged axiom branch Γ → Δ and every internal rule node. -/
@[blueprint "chap3__example_3_4_4"]
def exSearchTraceRound1Displayed : DeductionTree exSearchTraceSequent :=
  let p := PropFormulaNormalized.var 0
  let q := PropFormulaNormalized.var 1
  let r := PropFormulaNormalized.var 2
  let s := PropFormulaNormalized.var 3
  let t := PropFormulaNormalized.var 4
  .onePremise (.andLeft [] [.impl p q, .impl t r, .conj p s] [t] p (.neg q))
    (.twoPremise (.implLeft [p, .neg q] [.impl t r, .conj p s] [t] p q)
      (.leaf ⟨[p, .neg q, .impl t r, .conj p s], [p, t]⟩)
      (.twoPremise (.implLeft [q, p, .neg q] [.conj p s] [t] t r)
        (.onePremise (.andLeft [q, p, .neg q] [] [t, t] p s)
          (.leaf ⟨[q, p, .neg q, p, s], [t, t]⟩))
        (.onePremise (.andLeft [r, q, p, .neg q] [] [t] p s)
          (.leaf ⟨[r, q, p, .neg q, p, s], [t]⟩))))

/-- The search procedure produces the complete round-1 display. -/
@[blueprint "chap3__example_3_4_4"]
theorem exSearchTraceRound1_eq_displayed :
    exSearchTraceRound1 = exSearchTraceRound1Displayed

/-- Example 3.4.4: The complete displayed round-2 tree, including
    the unchanged axiom branch Γ → Δ and every internal rule node. -/
@[blueprint "chap3__example_3_4_4"]
def exSearchTraceRound2Displayed : DeductionTree exSearchTraceSequent :=
  let p := PropFormulaNormalized.var 0
  let q := PropFormulaNormalized.var 1
  let r := PropFormulaNormalized.var 2
  let s := PropFormulaNormalized.var 3
  let t := PropFormulaNormalized.var 4
  .onePremise (.andLeft [] [.impl p q, .impl t r, .conj p s] [t] p (.neg q))
    (.twoPremise (.implLeft [p, .neg q] [.impl t r, .conj p s] [t] p q)
      (.leaf ⟨[p, .neg q, .impl t r, .conj p s], [p, t]⟩)
      (.twoPremise (.implLeft [q, p, .neg q] [.conj p s] [t] t r)
        (.onePremise (.andLeft [q, p, .neg q] [] [t, t] p s)
          (.onePremise (.negLeft [q, p] [p, s] [t, t] q)
            (.leaf ⟨[q, p, p, s], [q, t, t]⟩)))
        (.onePremise (.andLeft [r, q, p, .neg q] [] [t] p s)
          (.onePremise (.negLeft [r, q, p] [p, s] [t] q)
            (.leaf ⟨[r, q, p, p, s], [q, t]⟩)))))

/-- The search procedure produces the complete round-2 display. -/
@[blueprint "chap3__example_3_4_4"]
theorem exSearchTraceRound2_eq_displayed :
    exSearchTraceRound2 = exSearchTraceRound2Displayed

-- ========= Theorem 3.4.1: Helper definitions =========

/-- Theorem 3.4.1 (required helper): A deduction tree is a proof tree if
    all its leaves are axiom sequents (sequents where antecedent and
    succedent share a common proposition). -/
@[blueprint "chap3__theorem_3_4_1"]
def isProofTree {s : Sequent} (dt : DeductionTree s) : Prop :=
  ∀ s ∈ dt.leaves, isAxiom s

/-- Example 3.4.4 (required helper): Collects all non-axiom leaves from
    a deduction tree. -/
@[blueprint "chap3__example_3_4_4"]
def nonAxiomLeaves {s : Sequent} (dt : DeductionTree s) : List Sequent :=
  dt.leaves.filter (fun s =>
    !(s.antecedent.any (fun A => s.succedent.any (fun B => A == B))))

/-- Lemma 3.4.1 (required helper): A valuation v falsifies a sequent
    A1,...,Am -> B1,...,Bn if v makes all Ai true and all Bj false.
    Unlike sequentFalsifiable, this is parametric in v. -/
@[blueprint "chap3__lemma_3_4_1"]
def sequentFalsifiedBy (s : Sequent) (v : Valuation) : Prop :=
  (∀ A ∈ s.antecedent, evalExtN v A = BoolVal.T) ∧
  (∀ B ∈ s.succedent, evalExtN v B = BoolVal.F)

end LCS.Propositional.Systems.G.Search
end

