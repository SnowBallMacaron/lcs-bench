import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import Attach
import LCS.Propositional.Systems.G.Search.Validity.ProofsStamp
import LCS.Propositional.Systems.G.Search.LeafExpansion
import LCS.Propositional.Systems.G.Search.SearchRounds
attach_helper_namespace LCS.Propositional.Systems.G.Search.Proofs

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
variable {mode : SearchMode}

/-- Theorem 3.4.1 (required helper): A deduction tree is well-formed when
    at each internal node the rule's premise sequents match the children's
    root sequents, and there exists a corresponding constrained Gentzen
    step (GentzenStep1 for one-premise, GentzenStep2 for two-premise nodes).
    Under the indexed `DeductionTree : Sequent → Type`, the premise/conclusion
    match is automatic: the child's type index IS the rule's premise. WFTree
    remains an inductive family (not an `abbrev` for `True`) so the later
    falsification-propagation theorems can still pattern-match on tree shape. -/
@[blueprint "chap3__theorem_3_4_1"]
inductive WFTree : {s : Sequent} → DeductionTree s → Prop where
  | leaf (s : Sequent) : WFTree (DeductionTree.leaf s)
  | step1 {prem conc : Sequent} {child : DeductionTree prem}
      (rule : GentzenStep1 prem conc)
      (hchild : WFTree child) :
      WFTree (DeductionTree.onePremise rule child)
  | step2 {p1 p2 conc : Sequent} {c1 : DeductionTree p1} {c2 : DeductionTree p2}
      (rule : GentzenStep2 p1 p2 conc)
      (hw1 : WFTree c1) (hw2 : WFTree c2) :
      WFTree (DeductionTree.twoPremise rule c1 c2)

-- Helper: BoolVal case analysis


-- Helper: extract components from evalExtN of compound formulas










-- Composing parts into compound evaluations






















-- Disjunction for impl T case


-- Disjunction for disj T case


-- Conjunction for conj F case


-- Forward falsification: conclusion falsified by v → premise falsified by v

-- Forward falsification for two-premise rules: at least one premise is falsified

-- Backward falsification: premise falsified → conclusion falsified (one-premise)

-- Backward falsification for two-premise rules


-- Main theorem: falsification propagation
/-- Theorem 3.4.1 (required companion): For every well-formed deduction
    tree, a valuation falsifies the root sequent if and only if it
    falsifies some leaf sequent. The WFTree hypothesis ensures each
    internal node applies a valid Gentzen rule connecting its children. -/
@[blueprint "chap3__theorem_3_4_1"]
theorem deductionTree_falsification_iff (v : Valuation)
    {s : Sequent} (dt : DeductionTree s) (hwf : WFTree dt) :
    sequentFalsifiedBy dt.conclusion v ↔
    ∃ s ∈ dt.leaves, sequentFalsifiedBy s v 

-- Helper: BoolVal.T and BoolVal.F are the only values


-- Helper: completeness by strong induction on complexity


/-- Theorem 3.4.1 (companion): Completeness of G'. Every valid sequent is
    provable in G'. This is the faithful formalization of the textbook's
    completeness theorem for G'. -/
@[blueprint "chap3__theorem_3_4_1"]
theorem completeness_G (s : Sequent) (hv : sequentValid s) :
    sequentProvable s 

/-- Theorem 3.4.1 (companion): Validity is equivalent to provability.
    The forward direction uses completeness_G; the backward direction
    uses soundness_G. -/
@[blueprint "chap3__theorem_3_4_1"]
theorem search_valid_iff_proofTree (s : Sequent) :
    sequentValid s ↔ sequentProvable s 

-- ========= Theorem 3.4.1: Decidability of sequent validity =========

/-- Theorem 3.4.1 (required helper): Collect all variable indices
    occurring in a formula. -/
@[blueprint "chap3__theorem_3_4_1"]
def formulaVarIndices : PropFormulaNormalized → List Nat
  | .var n => [n]
  | .neg A => formulaVarIndices A
  | .conj A B => formulaVarIndices A ++ formulaVarIndices B
  | .disj A B => formulaVarIndices A ++ formulaVarIndices B
  | .impl A B => formulaVarIndices A ++ formulaVarIndices B

/-- Theorem 3.4.1 (required helper): Collect all variable indices
    occurring in a sequent. -/
@[blueprint "chap3__theorem_3_4_1"]
def sequentVarIndices (s : Sequent) : List Nat :=
  ((s.antecedent ++ s.succedent).flatMap formulaVarIndices).eraseDups

/-- Theorem 3.4.1 (required helper): Generate all valuations over a
    given list of variable indices. Each valuation assigns T or F to
    the listed variables, and F to all others. -/
@[blueprint "chap3__theorem_3_4_1"]
def allValuations (vars : List Nat) : List Valuation :=
  match vars with
  | [] => [fun _ => BoolVal.F]
  | n :: ns =>
    let rest := allValuations ns
    rest.flatMap (fun v => [fun m => if m == n then BoolVal.T else v m,
                             fun m => if m == n then BoolVal.F else v m])

/-- Theorem 3.4.1 (required helper): Check whether a sequent is valid
    under a given valuation (returns Bool). -/
@[blueprint "chap3__theorem_3_4_1"]
def checkSequentValidFor (s : Sequent) (v : Valuation) : Bool :=
  if s.antecedent.all (fun A => evalExtN v A == BoolVal.T)
  then s.succedent.any (fun B => evalExtN v B == BoolVal.T)
  else true

/-- Theorem 3.4.1 (required helper): Check whether a sequent is valid
    by checking all valuations over its variable indices. -/
@[blueprint "chap3__theorem_3_4_1"]
def checkSequentValid (s : Sequent) : Bool :=
  (allValuations (sequentVarIndices s)).all (checkSequentValidFor s)

end LCS.Propositional.Systems.G.Search
end

