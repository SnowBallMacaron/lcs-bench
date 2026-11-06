import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import Attach
import LCS.Propositional.Systems.G.Search.FalsificationPropagation.ProofsStamp

/-! # Falsification through deduction trees (Lemma 3.4.1 and the claim of Theorem 3.4.1)

Per-valuation falsification for every rule of G' (Lemma 3.4.1), and the
claim in the proof of Theorem 3.4.1: a valuation falsifies the root of a
deduction tree iff it falsifies some leaf.
-/
section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
variable {mode : SearchMode}

/-- Lemma 3.4.1 (required helper): A valuation v falsifies a sequent
    A1,...,Am -> B1,...,Bn if v makes all Ai true and all Bj false.
    Unlike sequentFalsifiable, this is parametric in v. -/
@[blueprint "chap3__lemma_3_4_1"]
def sequentFalsifiedBy (s : Sequent) (v : Valuation) : Prop :=
  (∀ A ∈ s.antecedent, evalExtN v A = BoolVal.T) ∧
  (∀ B ∈ s.succedent, evalExtN v B = BoolVal.F)

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

-- ========= Lemma 3.4.1: Per-valuation rule falsification =========

/-- Lemma 3.4.1: For each G' one-premise rule and any valuation `v`,
    `v` falsifies the conclusion iff `v` falsifies the premise. The
    textbook lemma is one uniform "conclusion falsifiable iff some
    premise falsifiable" statement over ALL G' rules; we split it by
    premise-count because `GentzenStep1` and `GentzenStep2` have
    different arities. This is the one-premise half; see
    `rule_falsification_step2_iff` for the two-premise half. -/
@[blueprint "chap3__lemma_3_4_1" (main := true)]
theorem rule_falsification_step1_iff {prem conc : Sequent}
    (rule : GentzenStep1 prem conc) (v : Valuation) :
    sequentFalsifiedBy conc v ↔ sequentFalsifiedBy prem v 

/-- Lemma 3.4.1: For each G' two-premise rule and any valuation `v`,
    `v` falsifies the conclusion iff `v` falsifies at least one premise.
    Two-premise half of Lemma 3.4.1; see `rule_falsification_step1_iff`
    for the one-premise half. -/
@[blueprint "chap3__lemma_3_4_1" (main := true)]
theorem rule_falsification_step2_iff {p1 p2 conc : Sequent}
    (rule : GentzenStep2 p1 p2 conc) (v : Valuation) :
    sequentFalsifiedBy conc v ↔
    (sequentFalsifiedBy p1 v ∨ sequentFalsifiedBy p2 v) 

end LCS.Propositional.Systems.G.Search
end
