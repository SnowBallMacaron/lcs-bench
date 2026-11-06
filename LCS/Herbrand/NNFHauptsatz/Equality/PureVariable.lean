import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.CutElim.Hauptsatz.Equality
import LCS.Herbrand.NNFHauptsatz.Equality.RootToNodePaths
import Attach
import LCS.Herbrand.NNFHauptsatz.Equality.PureVariable.ProofsStamp

/-! # Herbrand.NNFHauptsatz.Equality.PureVariable

Lemma 7.4.3 and Theorem 7.4.2: pure-variable G2nnf= proofs.
-/

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
end LCS.Herbrand.NNFHauptsatz.Equality
end
