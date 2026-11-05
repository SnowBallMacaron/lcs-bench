import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.CutElim.Hauptsatz.Equality
import Attach
import LCS.Herbrand.NNFHauptsatz.Equality.Part1.ProofsStamp

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality
namespace LCS.Herbrand.NNFHauptsatz.G2nnfEqRule

/-- Definition 7.4.4 (companion def): Returns True for the four quantifier-for-subformulae rules of G2nnf= (allSubLeft, allSubRight, exSubLeft, exSubRight). Returns False for other base G2nnf rules and for equality axioms. -/
@[blueprint "chap7__definition_7_4_4"]
def isQuantifierRule {L : Language} {hL : L.hasEquality = true} :
    G2nnfEqRule L hL → Prop
  | .base (.allSubLeft _ _ _ _ _ _ _ _) => True
  | .base (.allSubRight _ _ _ _ _ _ _ _) => True
  | .base (.exSubLeft _ _ _ _ _ _ _ _) => True
  | .base (.exSubRight _ _ _ _ _ _ _ _) => True
  | _ => False

-- ===================================================================
-- Definition 7.4.4 (companion def): G2nnfEqRule.isPropositionalOrInessentialCut
-- ===================================================================

/-- Definition 7.4.4 (companion def): Returns True for base G2nnf rules that are propositional (conjunction, disjunction) or inessential cuts. Inessential cuts are cuts whose cut formula is an equality literal s = t or ¬(s = t) — per textbook Def 6.4.9, atomic predicate cuts P(s₁,...,sₙ) where P ≠ = are ESSENTIAL. Returns False for quantifier rules, weakening rules, axioms, and equality axiom schemas. -/
@[blueprint "chap7__lemma_7_4_3"]
def isPropositionalOrInessentialCut {L : Language} {hL : L.hasEquality = true} :
    G2nnfEqRule L hL → Prop
  | .base (.conjLeft1 _ _ _ _) => True
  | .base (.conjLeft2 _ _ _ _) => True
  | .base (.conjRight _ _ _ _) => True
  | .base (.disjLeft _ _ _ _) => True
  | .base (.disjRight1 _ _ _ _) => True
  | .base (.disjRight2 _ _ _ _) => True
  | .base (.cut A _ _ _ _) =>
    -- Textbook Def 6.4.9: inessential cut restricts the cut formula
    -- to a literal s = t or ¬(s = t) over the equality predicate
    -- ONLY. Atomic predicate cuts P(s₁,...,sₙ) with P ≠ = are
    -- ESSENTIAL.
    match A with
    | .eq_ _ _ _ => True
    | .neg (.eq_ _ _ _) => True
    | _ => False
  | _ => False

-- ===================================================================
-- Definition 7.4.4 (companion def): G2nnfEqRule.isWeakening
-- ===================================================================

/-- Definition 7.4.4 (companion def): Returns True for base G2nnf weakening rules (weakLeft, weakRight). Returns False for all other rules. -/
@[blueprint "chap7__definition_7_4_4"]
def isWeakening {L : Language} {hL : L.hasEquality = true} :
    G2nnfEqRule L hL → Prop
  | .base (.weakLeft _ _ _) => True
  | .base (.weakRight _ _ _) => True
  | _ => False

-- ===================================================================
-- Theorem 7.4.2 (companion def): G2nnfEqRule.isInessentialCut
-- ===================================================================

/-- Theorem 7.4.2 (companion def): Returns True for base G2nnf cut rules whose cut formula is an equality literal s = t or ¬(s = t). Textbook Def 6.4.9 explicitly excludes atomic predicate cuts P(s₁,...,sₙ) where P ≠ = — those are ESSENTIAL cuts. -/
@[blueprint "chap7__theorem_7_4_2"]
def isInessentialCut {L : Language} {hL : L.hasEquality = true} :
    G2nnfEqRule L hL → Prop
  | .base (.cut A _ _ _ _) =>
    -- Textbook Def 6.4.9: inessential cut restricts the cut formula
    -- to a literal s = t or ¬(s = t) over the equality predicate
    -- ONLY. Atomic predicate cuts P(s₁,...,sₙ) with P ≠ = are
    -- ESSENTIAL.
    match A with
    | .eq_ _ _ _ => True
    | .neg (.eq_ _ _ _) => True
    | _ => False
  | _ => False

-- ===================================================================
-- Theorem 7.4.2 (companion def): G2nnfEqRule.isPropositionalOnly
-- ===================================================================

/-- Theorem 7.4.2 (companion def): Returns True for base G2nnf rules that are purely propositional (conjunction, disjunction) without counting inessential cuts. Used to distinguish the propositional permutation case from the inessential cut case. -/
@[blueprint "chap7__theorem_7_4_2"]
def isPropositionalOnly {L : Language} {hL : L.hasEquality = true} :
    G2nnfEqRule L hL → Prop
  | .base (.conjLeft1 _ _ _ _) => True
  | .base (.conjLeft2 _ _ _ _) => True
  | .base (.conjRight _ _ _ _) => True
  | .base (.disjLeft _ _ _ _) => True
  | .base (.disjRight1 _ _ _ _) => True
  | .base (.disjRight2 _ _ _ _) => True
  | _ => False

-- ===================================================================
-- Theorem 7.4.2 (helper): G2nnfEqRule.isQuantifierRuleBool
-- ===================================================================

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Theorem 7.4.2 (companion def): Returns true if a G2nnf= rule is a quantifier-for-subformulae rule (decidable Bool version). Used for if-then-else branching in proof tree analysis. -/
def isQuantifierRuleBool {L : Language} {hL : L.hasEquality = true} :
    G2nnfEqRule L hL → Bool
  | .base (.allSubLeft _ _ _ _ _ _ _ _) => true
  | .base (.allSubRight _ _ _ _ _ _ _ _) => true
  | .base (.exSubLeft _ _ _ _ _ _ _ _) => true
  | .base (.exSubRight _ _ _ _ _ _ _ _) => true
  | _ => false

end LCS.Herbrand.NNFHauptsatz.G2nnfEqRule
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality
namespace LCS.Herbrand.NNFHauptsatz.G2nnfEqProofTree

-- retained: used by LCS.Herbrand.SharpenedHauptsatz.Theorem.Part1
/-- Theorem 7.4.2 (companion def): Structural subtree containment
(reflexive-transitive), retained for callers that only need containment.
Equal subtrees at different positions are not occurrence identifiers, so
`IsMidsequent_G2nnfEq` below uses `RootToNodePath` instead. -/
def isSubtree {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {ΓSub ΔSub : LCS.Finset (FormulaN L)}
    (tSub : G2nnfEqProofTree hL ΓSub ΔSub) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfEqProofTree hL Γ Δ → Prop
  | _, _, .leaf _ _ h _ _ => h.elim
  | _, _, .extraAxiom Gamma Delta hAx hNNF hRect =>
    HEq tSub (.extraAxiom Gamma Delta hAx hNNF hRect : G2nnfEqProofTree hL Gamma Delta)
  | _, _, .axiom_ rule hAdmit hAx hSC =>
    HEq tSub (.axiom_ rule hAdmit hAx hSC : G2nnfEqProofTree hL _ _)
  | _, _, .onePremise rule hAdmit hPrem hSC sub =>
    HEq tSub (.onePremise rule hAdmit hPrem hSC sub : G2nnfEqProofTree hL _ _) ∨
    isSubtree tSub sub
  | _, _, .twoPremise rule hAdmit hPrem hSC sub1 sub2 =>
    HEq tSub (.twoPremise rule hAdmit hPrem hSC sub1 sub2 : G2nnfEqProofTree hL _ _) ∨
    isSubtree tSub sub1 ∨ isSubtree tSub sub2

-- ===================================================================
-- Theorem 7.4.2 (helper): occurrence-indexed root-to-node paths
-- ===================================================================

/-- Theorem 7.4.2 (companion type): An occurrence-sensitive path from the
root of a G2nnf= proof tree to one particular node.  Premise choices are
stored in the path constructors, so structurally equal subtrees at different
positions remain different occurrences. -/
@[blueprint "chap7__theorem_7_4_2"]
inductive RootToNodePath {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] :
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)} →
    G2nnfEqProofTree hL Γroot Δroot →
    G2nnfEqProofTree hL Γnode Δnode → Type where
  /-- The empty path identifies the root occurrence itself. -/
  | root {Γ Δ : LCS.Finset (FormulaN L)}
      (T : G2nnfEqProofTree hL Γ Δ) :
      RootToNodePath T T
  /-- Descend through the sole premise of a one-premise inference. -/
  | onePremise (rule : G2nnfRuleCore L)
      (hAdmit : True)
      (hPrem : rule.premises.length = 1)
      (hSC : rule.SideConditions)
      (sub : G2nnfEqProofTree hL
        (rule.premises[0]'(by omega)).1
        (rule.premises[0]'(by omega)).2)
      {Γnode Δnode : LCS.Finset (FormulaN L)}
      {node : G2nnfEqProofTree hL Γnode Δnode}
      (path : RootToNodePath sub node) :
      RootToNodePath
        (G2nnfDeductionTreeCore.onePremise rule hAdmit hPrem hSC sub) node
  /-- Descend through the left premise of a two-premise inference. -/
  | leftPremise (rule : G2nnfRuleCore L)
      (hAdmit : True)
      (hPrem : rule.premises.length = 2)
      (hSC : rule.SideConditions)
      (sub1 : G2nnfEqProofTree hL
        (rule.premises[0]'(by omega)).1
        (rule.premises[0]'(by omega)).2)
      (sub2 : G2nnfEqProofTree hL
        (rule.premises[1]'(by omega)).1
        (rule.premises[1]'(by omega)).2)
      {Γnode Δnode : LCS.Finset (FormulaN L)}
      {node : G2nnfEqProofTree hL Γnode Δnode}
      (path : RootToNodePath sub1 node) :
      RootToNodePath
        (G2nnfDeductionTreeCore.twoPremise
          rule hAdmit hPrem hSC sub1 sub2) node
  /-- Descend through the right premise of a two-premise inference. -/
  | rightPremise (rule : G2nnfRuleCore L)
      (hAdmit : True)
      (hPrem : rule.premises.length = 2)
      (hSC : rule.SideConditions)
      (sub1 : G2nnfEqProofTree hL
        (rule.premises[0]'(by omega)).1
        (rule.premises[0]'(by omega)).2)
      (sub2 : G2nnfEqProofTree hL
        (rule.premises[1]'(by omega)).1
        (rule.premises[1]'(by omega)).2)
      {Γnode Δnode : LCS.Finset (FormulaN L)}
      {node : G2nnfEqProofTree hL Γnode Δnode}
      (path : RootToNodePath sub2 node) :
      RootToNodePath
        (G2nnfDeductionTreeCore.twoPremise
          rule hAdmit hPrem hSC sub1 sub2) node

/-- Theorem 7.4.2 (companion structure): A node occurrence in a fixed G2nnf=
proof tree, identified by its root-to-node path. -/
@[blueprint "chap7__theorem_7_4_2"]
structure NodeOccurrence {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    (root : G2nnfEqProofTree hL Γroot Δroot)
    (Γnode Δnode : LCS.Finset (FormulaN L)) where
  node : G2nnfEqProofTree hL Γnode Δnode
  path : RootToNodePath root node

/-- Compose two occurrence-sensitive G2nnf= root-to-node paths while
preserving every recorded premise choice. -/
@[blueprint "chap7__theorem_7_4_2"]
def RootToNodePath.trans {L : Language}
    {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γmid Δmid Γnode Δnode :
      LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL Γroot Δroot}
    {mid : G2nnfEqProofTree hL Γmid Δmid}
    {node : G2nnfEqProofTree hL Γnode Δnode}
    (first : RootToNodePath root mid)
    (second : RootToNodePath mid node) :
    RootToNodePath root node :=
  match first with
  | .root _ => second
  | .onePremise rule hAdmit hPrem hSC sub path =>
    .onePremise rule hAdmit hPrem hSC sub (path.trans second)
  | .leftPremise rule hAdmit hPrem hSC sub1 sub2 path =>
    .leftPremise rule hAdmit hPrem hSC sub1 sub2
      (path.trans second)
  | .rightPremise rule hAdmit hPrem hSC sub1 sub2 path =>
    .rightPremise rule hAdmit hPrem hSC sub1 sub2
      (path.trans second)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Replace the exact target occurrence of a root-to-node path by another
tree with the same sequent index.  Every outer application and every
off-path sibling is reused definitionally. -/
def RootToNodePath.replace {L : Language} {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL Γroot Δroot}
    {node : G2nnfEqProofTree hL Γnode Δnode}
    (path : RootToNodePath root node)
    (replacement : G2nnfEqProofTree hL Γnode Δnode) :
    G2nnfEqProofTree hL Γroot Δroot :=
  match path with
  | .root _ => replacement
  | .onePremise rule hAdmit hPrem hSC sub rest =>
    .onePremise rule hAdmit hPrem hSC
      (rest.replace replacement)
  | .leftPremise rule hAdmit hPrem hSC sub1 sub2 rest =>
    .twoPremise rule hAdmit hPrem hSC
      (rest.replace replacement) sub2
  | .rightPremise rule hAdmit hPrem hSC sub1 sub2 rest =>
    .twoPremise rule hAdmit hPrem hSC
      sub1 (rest.replace replacement)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem conjRightSideConditions {L : Language}
    {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    (A : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L))
    (hRect : isRectified (.conj A A))
    (sub : G2nnfEqProofTree hL Gamma (LCS.Finset.insert A Delta)) :
    (G2nnfRuleCore.conjRight A A Gamma Delta).SideConditions := by
  have hn := G2nnfDeductionTreeCore.allNNF sub
  refine ⟨trivial, ⟨hn.1, ?_⟩, ?_,
    AllRectified.insert_right hRect (AllRectified.of_insert_right sub.allRectified)⟩
  · intro F h
    rcases LCS.Finset.mem_insert.mp h with rfl | h
    · have ha := hn.2 A (LCS.Finset.mem_insert.mpr (Or.inl rfl))
      exact ⟨ha, ha⟩
    · exact hn.2 F (LCS.Finset.mem_insert.mpr (Or.inr h))
  · intro seq h
    simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false, or_self] at h
    subst seq
    exact hn



end LCS.Herbrand.NNFHauptsatz.G2nnfEqProofTree
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality
namespace LCS.Herbrand.NNFHauptsatz.Equality
open LCS.Herbrand.NNFHauptsatz.G2nnfEqRule
open LCS.Herbrand.NNFHauptsatz.G2nnfEqProofTree

/-- Lemma 7.4.3 (companion def): Predicate asserting that a formula `f` appears in some sequent (antecedent or succedent) of a G2nnf= proof tree. Since G2nnf= sequents are `LCS.Finset (FormulaN L)`, we express tree-containment as a Prop rather than producing a concrete list. The recursion walks the whole tree: at each node, `f` may occur in the current node's conclusion sequent `(Γ, Δ)` (the TYPE INDEX: a stored Core conclusion or canonical equality-axiom sequent) or in any sub-proof. We pattern-match on the IMPLICIT TYPE INDEX `{Γ Δ}` so `Γ Δ` denote the actual conclusion sequent of this node, with ordinary inference contexts stored inside the Core rule. -/
@[blueprint "chap7__lemma_7_4_3"]
def g2nnfEqProofTreeContainsFormula {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (tree : G2nnfEqProofTree hL Γ Δ) (f : FormulaN L) : Prop :=
  match tree with
  | .leaf _ _ h _ _ => h.elim
  | .extraAxiom _ _ _ _ _ => f ∈ Γ ∨ f ∈ Δ
  | .axiom_ _ _ _ _ => f ∈ Γ ∨ f ∈ Δ
  | .onePremise _ _ _ _ sub =>
    f ∈ Γ ∨ f ∈ Δ ∨ g2nnfEqProofTreeContainsFormula sub f
  | .twoPremise _ _ _ _ sub1 sub2 =>
    f ∈ Γ ∨ f ∈ Δ ∨
    g2nnfEqProofTreeContainsFormula sub1 f ∨
    g2nnfEqProofTreeContainsFormula sub2 f

-- ===================================================================
-- Lemma 7.4.3 (companion def): g2nnfEqNoFreeBoundOverlap
-- ===================================================================

/-- Lemma 7.4.3 (companion def): Predicate asserting that variable `y` does not occur both free and bound in any single formula of the G2nnf= proof tree, checked globally over the entire tree via `g2nnfEqProofTreeContainsFormula`. -/
@[blueprint "chap7__lemma_7_4_3"]
def g2nnfEqNoFreeBoundOverlap {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (y : Nat) (tree : G2nnfEqProofTree hL Γ Δ) : Prop :=
  ∀ (f : FormulaN L),
    g2nnfEqProofTreeContainsFormula tree f →
    ¬ (Membership.mem (formulaFVN f) y ∧
       Membership.mem (formulaBVN f) y)

-- ===================================================================
-- Lemma 7.4.3 (companion def): g2nnfEqEigenvariableOccursOnlyInSubtree
-- ===================================================================

/-- Lemma 7.4.3 (companion def): Every formula occurrence in one G2nnf=
sequent is free of `y`, whether `y` would occur free or bound in that
formula. -/
@[blueprint "chap7__lemma_7_4_3"]
def g2nnfEqSequentVariableFree {L : Language}
    [DecidableEq (FormulaN L)]
    (y : Nat) (Γ Δ : LCS.Finset (FormulaN L)) : Prop :=
  ∀ f : FormulaN L, f ∈ Γ ∨ f ∈ Δ →
    ¬ Membership.mem (formulaAllVariables f) y

/-- Lemma 7.4.3 (companion def): Every formula occurrence at every node of a
G2nnf= proof tree is free of `y`.  The recursive definition checks node
occurrences directly instead of collecting formula values into a set. -/
@[blueprint "chap7__lemma_7_4_3"]
def g2nnfEqProofTreeVariableFree {L : Language}
    {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    (y : Nat) {Γ Δ : LCS.Finset (FormulaN L)}
    (tree : G2nnfEqProofTree hL Γ Δ) : Prop :=
  match tree with
  | .leaf _ _ h _ _ => h.elim
  | .extraAxiom _ _ _ _ _ => g2nnfEqSequentVariableFree y Γ Δ
  | .axiom_ _ _ _ _ =>
    g2nnfEqSequentVariableFree y Γ Δ
  | .onePremise _ _ _ _ sub =>
    g2nnfEqSequentVariableFree y Γ Δ ∧
    g2nnfEqProofTreeVariableFree y sub
  | .twoPremise _ _ _ _ sub1 sub2 =>
    g2nnfEqSequentVariableFree y Γ Δ ∧
    g2nnfEqProofTreeVariableFree y sub1 ∧
    g2nnfEqProofTreeVariableFree y sub2

/-- Lemma 7.4.3 (companion def): Along an exact path to an exempt premise
occurrence, `y` is absent from every ancestor sequent and every off-path
sibling subtree.  Reaching `.root` exempts precisely that target occurrence
and its descendants. -/
@[blueprint "chap7__lemma_7_4_3"]
def g2nnfEqVariableOccursOnlyAlongPath {L : Language}
    {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    (y : Nat) :
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)} →
    {root : G2nnfEqProofTree hL Γroot Δroot} →
    {node : G2nnfEqProofTree hL Γnode Δnode} →
    G2nnfEqProofTree.RootToNodePath root node → Prop
  | _, _, _, _, _, _, .root _ => True
  | _, _, _, _, _, _,
      .onePremise rule hAdmit _ _ _ path =>
    g2nnfEqSequentVariableFree y
      rule.conclusion.1
      rule.conclusion.2 ∧
    g2nnfEqVariableOccursOnlyAlongPath y path
  | _, _, _, _, _, _,
      .leftPremise rule hAdmit _ _ _ sub2 path =>
    g2nnfEqSequentVariableFree y
      rule.conclusion.1
      rule.conclusion.2 ∧
    g2nnfEqProofTreeVariableFree y sub2 ∧
    g2nnfEqVariableOccursOnlyAlongPath y path
  | _, _, _, _, _, _,
      .rightPremise rule hAdmit _ _ sub1 _ path =>
    g2nnfEqSequentVariableFree y
      rule.conclusion.1
      rule.conclusion.2 ∧
    g2nnfEqProofTreeVariableFree y sub1 ∧
    g2nnfEqVariableOccursOnlyAlongPath y path

/-- Lemma 7.4.3 (companion def): Predicate asserting that variable `y` only
occurs inside one exact subtree occurrence of the ambient G2nnf= proof tree.
The `NodeOccurrence` path identifies the premise position of the
eigenvariable-introducing inference.  Formula occurrences in ancestor
sequents and off-path sibling subtrees must be `y`-free; only the target
occurrence and its descendants are exempt.  No formula, sequent, or subtree
equality is used to identify occurrences. -/
@[blueprint "chap7__lemma_7_4_3"]
def g2nnfEqEigenvariableOccursOnlyInSubtree {L : Language}
    {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot ΓSub ΔSub : LCS.Finset (FormulaN L)}
    {T : G2nnfEqProofTree hL Γroot Δroot}
    (y : Nat) (occurrence : NodeOccurrence T ΓSub ΔSub) : Prop :=
  g2nnfEqVariableOccursOnlyAlongPath y occurrence.path

-- ATTACH-BLOCKER: scoped helper requires manual relocation
set_option backward.isDefEq.respectTransparency false in
/-- Occurrence-sensitivity regression for G2nnf=: the same axiom subtree is
reused in both premises and contains the same `y`-containing formulae as the
root.  The former formula-value subtraction condition accepts this tree,
while the occurrence-sensitive condition rejects the distinct right-premise
and root occurrences. -/
theorem duplicateVariableFormulaOutsideOccurrenceEq_rejected
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (A : FormulaN L) (hAtom : A.isAtomic) (y : Nat)
    (hy : Membership.mem (formulaAllVariables A) y) :
    let Γ : LCS.Finset (FormulaN L) :=
      LCS.Finset.insert A ∅
    let Δ : LCS.Finset (FormulaN L) :=
      LCS.Finset.singleton (.conj A A)
    let hAqf : isQuantifierFree A :=
      AllRectified.isQuantifierFree_of_isAtomic A hAtom
    let hConjQf : isQuantifierFree (.conj A A) := ⟨hAqf, hAqf⟩
    let hSubRect : AllRectified (Γ, LCS.Finset.insert A Δ) :=
      AllRectified.of_allQuantifierFree _ ⟨
        (by
          intro F hF
          rcases LCS.Finset.mem_insert.mp hF with rfl | hF
          · exact hAqf
          · exact (LCS.Finset.not_mem_empty hF).elim),
        (by
          intro F hF
          rcases LCS.Finset.mem_insert.mp hF with rfl | hF
          · exact hAqf
          · rw [LCS.Finset.mem_singleton] at hF
            subst F
            exact hConjQf)⟩
    let hRootRect :
        AllRectified (Γ, LCS.Finset.insert (.conj A A) Δ) :=
      AllRectified.of_allQuantifierFree _ ⟨
        (by
          intro F hF
          rcases LCS.Finset.mem_insert.mp hF with rfl | hF
          · exact hAqf
          · exact (LCS.Finset.not_mem_empty hF).elim),
        (by
          intro F hF
          rcases LCS.Finset.mem_insert.mp hF with rfl | hF
          · exact hConjQf
          · rw [LCS.Finset.mem_singleton] at hF
            subst F
            exact hConjQf)⟩
    let hAnnf : A.isNNF := by
      cases A with
      | predN _ _ => trivial
      | eq_ _ _ _ => trivial
      | neg _ | conj _ _ | disj _ _ | impl _ _ | all _ _ | ex _ _ =>
        exact Bool.noConfusion hAtom
    let hSubNNF : AllNNF (Γ, LCS.Finset.insert A Δ) :=
      ⟨(by intro F h; rcases LCS.Finset.mem_insert.mp h with rfl | h
           exact hAnnf
           exact (LCS.Finset.not_mem_empty h).elim),
        (by intro F h; rcases LCS.Finset.mem_insert.mp h with rfl | h
            exact hAnnf
            rw [LCS.Finset.mem_singleton] at h; subst F; exact ⟨hAnnf, hAnnf⟩)⟩
    let hSubSC : (G2nnfRuleCore.axiomPosId A hAtom ∅ Δ).SideConditions :=
      ⟨trivial, hSubNNF, (by intro seq h; cases h), hSubRect⟩
    let sub : G2nnfEqProofTree hL Γ (LCS.Finset.insert A Δ) :=
      .axiom_ (.axiomPosId A hAtom ∅ Δ) trivial rfl hSubSC
    let hRootSC := G2nnfEqProofTree.conjRightSideConditions A Γ Δ
      (AllRectified.isRectified_of_isQuantifierFree _ hConjQf) sub
    let root : G2nnfEqProofTree hL Γ (LCS.Finset.insert (.conj A A) Δ) :=
      .twoPremise (.conjRight A A Γ Δ) trivial rfl hRootSC sub sub
    let left : NodeOccurrence root Γ (LCS.Finset.insert A Δ) :=
      ⟨sub, .leftPremise (.conjRight A A Γ Δ) trivial rfl hRootSC sub sub (.root sub)⟩
    (∀ f : FormulaN L,
      g2nnfEqProofTreeContainsFormula root f →
      ¬ g2nnfEqProofTreeContainsFormula sub f →
      ¬ Membership.mem (formulaAllVariables f) y) ∧
    ¬ g2nnfEqEigenvariableOccursOnlyInSubtree y left := by
  dsimp only
  constructor
  · intro f hRoot hNotSub
    apply False.elim
    apply hNotSub
    simp only [g2nnfEqProofTreeContainsFormula] at hRoot ⊢
    rcases hRoot with hΓ | hΔ | hSub | hSub
    · exact Or.inl hΓ
    · exact Or.inr (LCS.Finset.mem_insert.mpr
        (Or.inr ((LCS.Finset.mem_singleton f (.conj A A)).mpr
          ((LCS.Finset.mem_insert.mp hΔ).elim id
            (fun h => (LCS.Finset.mem_singleton f (.conj A A)).mp h)))))
    · exact hSub
    · exact hSub
  · intro hOnly
    exact hOnly.1 A
      (Or.inl (LCS.Finset.mem_insert.mpr (Or.inl rfl))) hy



-- ===================================================================
-- Theorem 7.4.2 (required def): IsPureVariableProof_G2nnfEq
-- ===================================================================

/-- Theorem 7.4.2 (companion def): The occurrence-aware form of the
pure-variable predicate for G2nnf=.  The `outer` proof tree stays fixed while
the recursive `current` tree is accompanied by its exact root-to-node path in
`outer`.  At an eigenvariable-introducing base rule, extending that path
through the sole premise identifies the precise exempt premise occurrence. -/
@[blueprint "chap7__theorem_7_4_2"]
noncomputable def isPureVariableProof_G2nnfEqAux
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    (outer : G2nnfEqProofTree hL Γroot Δroot) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    (current : G2nnfEqProofTree hL Γ Δ) →
    G2nnfEqProofTree.RootToNodePath outer current → Prop
  | _, _, .leaf _ _ hOpen _ _, _ => hOpen.elim
  | _, _, .extraAxiom _ _ _ _ _, _ => True
  | _, _, .axiom_ _ _ _ _, _ => True
  | _, _, .onePremise rule hAdmit hPrem hSC sub, path =>
    let subPath : G2nnfEqProofTree.RootToNodePath outer sub :=
      path.trans
        (.onePremise rule hAdmit hPrem hSC sub (.root sub))
    let subOccurrence :
        G2nnfEqProofTree.NodeOccurrence outer _ _ := ⟨sub, subPath⟩
    (match rule with
     | .allSubRight _ _ _ _ y _ _ _ =>
       g2nnfEqNoFreeBoundOverlap y outer ∧
       g2nnfEqEigenvariableOccursOnlyInSubtree y subOccurrence
     | .exSubLeft _ _ _ _ y _ _ _ =>
       g2nnfEqNoFreeBoundOverlap y outer ∧
       g2nnfEqEigenvariableOccursOnlyInSubtree y subOccurrence
     | _ => True) ∧
    isPureVariableProof_G2nnfEqAux outer sub subPath
  | _, _, .twoPremise rule hAdmit hPrem hSC sub1 sub2, path =>
    let leftPath : G2nnfEqProofTree.RootToNodePath outer sub1 :=
      path.trans
        (.leftPremise rule hAdmit hPrem hSC sub1 sub2 (.root sub1))
    let rightPath : G2nnfEqProofTree.RootToNodePath outer sub2 :=
      path.trans
        (.rightPremise rule hAdmit hPrem hSC sub1 sub2 (.root sub2))
    isPureVariableProof_G2nnfEqAux outer sub1 leftPath ∧
    isPureVariableProof_G2nnfEqAux outer sub2 rightPath



/-- Theorem 7.4.2 (required def): Predicate asserting that a G2nnf= proof
tree is pure-variable (adapted from Definition 7.3.1 for G2nnf=).  The root
occurrence starts the recursion; every descent extends its path while
retaining the same outer tree, so nested eigenvariable rules are checked
against exact premise occurrences in the whole proof tree. -/
@[blueprint "chap7__theorem_7_4_2"]
noncomputable def IsPureVariableProof_G2nnfEq
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfEqProofTree hL Γ Δ) : Prop :=
  isPureVariableProof_G2nnfEqAux T T (.root T)

-- ===================================================================
-- Lemma 7.4.3 (helper): RuleAppearsInTree_G2nnfEq
-- ===================================================================



-- ===================================================================
-- Lemma 7.4.3 (helper): RuleAppearsBelow_G2nnfEq
-- ===================================================================



-- ===================================================================
-- Theorem 7.4.2 (helper): allRulesSatisfy
-- ===================================================================

/-- Theorem 7.4.2 (companion def): Predicate asserting that every rule in a G2nnf= proof tree satisfies the given predicate P. Used to state that all rules above the midsequent are propositional, weakening, or inessential cuts. -/
@[blueprint "chap7__theorem_7_4_2"]
def allRulesSatisfy {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (P : G2nnfEqRule L hL → Prop) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfEqProofTree hL Γ Δ → Prop
  | _, _, .leaf _ _ hOpen _ _ => hOpen.elim
  | _, _, .extraAxiom _ _ _ _ _ => True
  | _, _, .axiom_ _ _ _ _ => True
  | _, _, .onePremise rule _ _ _ sub =>
    P (.base rule) ∧ allRulesSatisfy P sub
  | _, _, .twoPremise rule _ _ _ sub1 sub2 =>
    P (.base rule) ∧ allRulesSatisfy P sub1 ∧
    allRulesSatisfy P sub2

/-- Exact one-premise applications for the equality calculus. -/
@[blueprint "chap7__lemma_7_4_3"]
inductive G2nnfEqOnePremiseApplication {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] (rule : G2nnfRuleCore L) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfEqProofTree hL Γ Δ → Type where
  | of (hAdmit : True)
      (hPrem : (rule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions rule)
      (sub : G2nnfEqProofTree hL
        ((rule.premises)[0]'(by omega)).1
        ((rule.premises)[0]'(by omega)).2) :
      G2nnfEqOnePremiseApplication rule
        (.onePremise rule hAdmit hPrem hSC sub)


/-- Exact source premise of a selected quantifier application. -/
@[blueprint "chap7__lemma_7_4_3"]
inductive G2nnfEqOnePremiseFrontier {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] {rule : G2nnfRuleCore L} :
    {Γnode Δnode : LCS.Finset (FormulaN L)} →
    {node : G2nnfEqProofTree hL Γnode Δnode} →
    G2nnfEqOnePremiseApplication rule node →
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfEqProofTree hL Γ Δ → Type where
  | of (hAdmit : True)
      (hPrem : (rule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions rule)
      (sub : G2nnfEqProofTree hL
        ((rule.premises)[0]'(by omega)).1
        ((rule.premises)[0]'(by omega)).2) :
      G2nnfEqOnePremiseFrontier
        (G2nnfEqOnePremiseApplication.of hAdmit hPrem hSC sub) sub


/-- The selected path contains only weakening steps, with no binary step. -/
@[blueprint "chap7__lemma_7_4_3"]
inductive G2nnfEqWeakeningOnlyPath {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] :
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)} →
    {root : G2nnfEqProofTree hL Γroot Δroot} →
    {node : G2nnfEqProofTree hL Γnode Δnode} →
    (path : G2nnfEqProofTree.RootToNodePath root node) → Type where
  | root {Γ Δ : LCS.Finset (FormulaN L)}
      (T : G2nnfEqProofTree hL Γ Δ) :
      G2nnfEqWeakeningOnlyPath (.root T)
  | onePremise (rule : G2nnfRuleCore L)
      (hAdmit : True)
      (hPrem : (rule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions rule)
      (sub : G2nnfEqProofTree hL
        ((rule.premises)[0]'(by omega)).1
        ((rule.premises)[0]'(by omega)).2)
      {Γnode Δnode : LCS.Finset (FormulaN L)}
      {node : G2nnfEqProofTree hL Γnode Δnode}
      {path : G2nnfEqProofTree.RootToNodePath sub node}
      (hWeak : rule.isWeakening)
      (rest : G2nnfEqWeakeningOnlyPath path) :
      G2nnfEqWeakeningOnlyPath
        (.onePremise rule hAdmit hPrem hSC sub path)


/-- An exact one/left/right lower-premise occurrence and its outside path. -/
@[blueprint "chap7__lemma_7_4_3"]
inductive G2nnfEqSelectedPremiseOccurrence {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    (root : G2nnfEqProofTree hL Γroot Δroot) (R₂ : G2nnfRuleCore L) :
    {Γprem Δprem : LCS.Finset (FormulaN L)} →
    G2nnfEqProofTree hL Γprem Δprem → Type where
  | one (hAdmit : True)
      (hPrem : (R₂.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions R₂)
      (sub : G2nnfEqProofTree hL
        ((R₂.premises)[0]'(by omega)).1
        ((R₂.premises)[0]'(by omega)).2)
      (path : G2nnfEqProofTree.RootToNodePath root
        (.onePremise R₂ hAdmit hPrem hSC sub)) :
      G2nnfEqSelectedPremiseOccurrence root R₂ sub
  | left (hAdmit : True)
      (hPrem : (R₂.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions R₂)
      (sub1 : G2nnfEqProofTree hL
        ((R₂.premises)[0]'(by omega)).1
        ((R₂.premises)[0]'(by omega)).2)
      (sub2 : G2nnfEqProofTree hL
        ((R₂.premises)[1]'(by omega)).1
        ((R₂.premises)[1]'(by omega)).2)
      (path : G2nnfEqProofTree.RootToNodePath root
        (.twoPremise R₂ hAdmit hPrem hSC sub1 sub2)) :
      G2nnfEqSelectedPremiseOccurrence root R₂ sub1
  | right (hAdmit : True)
      (hPrem : (R₂.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions R₂)
      (sub1 : G2nnfEqProofTree hL
        ((R₂.premises)[0]'(by omega)).1
        ((R₂.premises)[0]'(by omega)).2)
      (sub2 : G2nnfEqProofTree hL
        ((R₂.premises)[1]'(by omega)).1
        ((R₂.premises)[1]'(by omega)).2)
      (path : G2nnfEqProofTree.RootToNodePath root
        (.twoPremise R₂ hAdmit hPrem hSC sub1 sub2)) :
      G2nnfEqSelectedPremiseOccurrence root R₂ sub2


/-- The exact other sibling of a binary lower application; none for unary rules. -/
@[blueprint "chap7__lemma_7_4_3"]
inductive G2nnfEqOtherPremiseFrontier {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL Γroot Δroot} {R₂ : G2nnfRuleCore L} :
    {Γselected Δselected : LCS.Finset (FormulaN L)} →
    {selectedTree : G2nnfEqProofTree hL Γselected Δselected} →
    G2nnfEqSelectedPremiseOccurrence root R₂ selectedTree →
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfEqProofTree hL Γ Δ → Type where
  | ofLeft (hAdmit : True)
      (hPrem : (R₂.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions R₂)
      (sub1 : G2nnfEqProofTree hL
        ((R₂.premises)[0]'(by omega)).1
        ((R₂.premises)[0]'(by omega)).2)
      (sub2 : G2nnfEqProofTree hL
        ((R₂.premises)[1]'(by omega)).1
        ((R₂.premises)[1]'(by omega)).2)
      (path : G2nnfEqProofTree.RootToNodePath root
        (.twoPremise R₂ hAdmit hPrem hSC sub1 sub2)) :
      G2nnfEqOtherPremiseFrontier
        (G2nnfEqSelectedPremiseOccurrence.left
          hAdmit hPrem hSC sub1 sub2 path) sub2
  | ofRight (hAdmit : True)
      (hPrem : (R₂.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions R₂)
      (sub1 : G2nnfEqProofTree hL
        ((R₂.premises)[0]'(by omega)).1
        ((R₂.premises)[0]'(by omega)).2)
      (sub2 : G2nnfEqProofTree hL
        ((R₂.premises)[1]'(by omega)).1
        ((R₂.premises)[1]'(by omega)).2)
      (path : G2nnfEqProofTree.RootToNodePath root
        (.twoPremise R₂ hAdmit hPrem hSC sub1 sub2)) :
      G2nnfEqOtherPremiseFrontier
        (G2nnfEqSelectedPremiseOccurrence.right
          hAdmit hPrem hSC sub1 sub2 path) sub1

end LCS.Herbrand.NNFHauptsatz.Equality
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Equality
namespace LCS.Herbrand.NNFHauptsatz.Equality
open LCS.Herbrand.NNFHauptsatz.G2nnfEqRule
open LCS.Herbrand.NNFHauptsatz.G2nnfEqProofTree
namespace G2nnfEqSelectedPremiseOccurrence

@[blueprint "chap7__lemma_7_4_3"]
def choice {L : Language} {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    {Γ Δ Γp Δp : LCS.Finset (FormulaN L)} {T : G2nnfEqProofTree hL Γ Δ}
    {r : G2nnfRuleCore L} {sub : G2nnfEqProofTree hL Γp Δp} :
    G2nnfEqSelectedPremiseOccurrence T r sub → G2nnfPremiseChoice
  | .one .. => .only
  | .left .. => .left
  | .right .. => .right

@[blueprint "chap7__lemma_7_4_3"]
def otherPremiseCount {L : Language} {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    {Γ Δ Γp Δp : LCS.Finset (FormulaN L)} {T : G2nnfEqProofTree hL Γ Δ}
    {r : G2nnfRuleCore L} {sub : G2nnfEqProofTree hL Γp Δp}
    (selected : G2nnfEqSelectedPremiseOccurrence T r sub) : Nat :=
  match selected.choice with | .only => 0 | _ => 1

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
def node {L : Language} {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    {Γ Δ Γp Δp : LCS.Finset (FormulaN L)} {T : G2nnfEqProofTree hL Γ Δ}
    {r : G2nnfRuleCore L} {sub : G2nnfEqProofTree hL Γp Δp} :
    G2nnfEqSelectedPremiseOccurrence T r sub →
      G2nnfEqProofTree hL r.conclusion.1 r.conclusion.2
  | .one ha hp hs sub _ => .onePremise r ha hp hs sub
  | .left ha hp hs sub₁ sub₂ _ => .twoPremise r ha hp hs sub₁ sub₂
  | .right ha hp hs sub₁ sub₂ _ => .twoPremise r ha hp hs sub₁ sub₂

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
def path {L : Language} {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    {Γ Δ Γp Δp : LCS.Finset (FormulaN L)} {T : G2nnfEqProofTree hL Γ Δ}
    {r : G2nnfRuleCore L} {sub : G2nnfEqProofTree hL Γp Δp}
    (selected : G2nnfEqSelectedPremiseOccurrence T r sub) :
    G2nnfEqProofTree.RootToNodePath T selected.node :=
  match selected with
  | .one _ _ _ _ path => path
  | .left _ _ _ _ _ path => path
  | .right _ _ _ _ _ path => path

end G2nnfEqSelectedPremiseOccurrence
end LCS.Herbrand.NNFHauptsatz.Equality
end

