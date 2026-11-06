import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.NNFHauptsatz.Renaming
import LCS.Herbrand.NNFHauptsatz.Soundness
import LCS.Herbrand.SharpenedHauptsatz
import LCS.Herbrand.SharpenedHauptsatz.Permutability
import LCS.Herbrand.SharpenedHauptsatz.Theorem
import LCS.Herbrand.PrenexForm
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination
import Attach
import LCS.Herbrand.NNFHauptsatz.Theorem.RootToNodePaths.ProofsStamp

/-! # Herbrand.NNFHauptsatz.Theorem.RootToNodePaths

Root-to-node paths and node occurrences in G2nnf proof trees (the branches traced
from the root in the proof of Theorem 7.4.1).
-/

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Soundness
open LCS.Herbrand.SharpenedHauptsatz
open LCS.Herbrand.SharpenedHauptsatz.Permutability
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.Herbrand.PrenexForm
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS.CutElim.LK
namespace LCS.Herbrand.NNFHauptsatz.G2nnfProofTree

-- ===================================================================
-- Theorem 7.4.1 (helper): occurrence-indexed root-to-node paths
-- ===================================================================

/-- Theorem 7.4.1 (companion type): An occurrence-sensitive path from the
root of a G2nnf proof tree to one particular node.  The target proof tree is
carried as an index, while the constructors record whether each descent uses
the sole premise, the left premise, or the right premise.  Consequently two
structurally equal subtrees at different positions still have distinct path
values. -/
@[blueprint "chap7__theorem_7_4_1"]
inductive RootToNodePath {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)] :
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γroot Δroot →
    G2nnfProofTree hL Γnode Δnode → Type where
  /-- The empty path identifies the root occurrence itself. -/
  | root {Γ Δ : LCS.Finset (FormulaN L)}
      (T : G2nnfProofTree hL Γ Δ) :
      RootToNodePath T T
  /-- Descend through the sole premise of a one-premise inference. -/
  | onePremise (rule : G2nnfRuleCore L)
      (hAdmit : rule.BareAtomicAxiom)
      (hPrem : (rule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions rule)
      (sub : G2nnfProofTree hL
        ((rule.premises)[0]'(by omega)).1
        ((rule.premises)[0]'(by omega)).2)
      {Γnode Δnode : LCS.Finset (FormulaN L)}
      {node : G2nnfProofTree hL Γnode Δnode}
      (path : RootToNodePath sub node) :
      RootToNodePath
        (G2nnfDeductionTreeCore.onePremise rule hAdmit hPrem hSC sub) node
  /-- Descend through the left premise of a two-premise inference. -/
  | leftPremise (rule : G2nnfRuleCore L)
      (hAdmit : rule.BareAtomicAxiom)
      (hPrem : (rule.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions rule)
      (sub1 : G2nnfProofTree hL
        ((rule.premises)[0]'(by omega)).1
        ((rule.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((rule.premises)[1]'(by omega)).1
        ((rule.premises)[1]'(by omega)).2)
      {Γnode Δnode : LCS.Finset (FormulaN L)}
      {node : G2nnfProofTree hL Γnode Δnode}
      (path : RootToNodePath sub1 node) :
      RootToNodePath
        (G2nnfDeductionTreeCore.twoPremise rule hAdmit hPrem hSC sub1 sub2) node
  /-- Descend through the right premise of a two-premise inference. -/
  | rightPremise (rule : G2nnfRuleCore L)
      (hAdmit : rule.BareAtomicAxiom)
      (hPrem : (rule.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions rule)
      (sub1 : G2nnfProofTree hL
        ((rule.premises)[0]'(by omega)).1
        ((rule.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((rule.premises)[1]'(by omega)).1
        ((rule.premises)[1]'(by omega)).2)
      {Γnode Δnode : LCS.Finset (FormulaN L)}
      {node : G2nnfProofTree hL Γnode Δnode}
      (path : RootToNodePath sub2 node) :
      RootToNodePath
        (G2nnfDeductionTreeCore.twoPremise rule hAdmit hPrem hSC sub1 sub2) node

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Transport only the root indices of an exact path. -/
noncomputable def RootToNodePath.castRoot
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaRoot' DeltaRoot'
      GammaNode DeltaNode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    {node : G2nnfProofTree hL GammaNode DeltaNode}
    (hGamma : GammaRoot = GammaRoot')
    (hDelta : DeltaRoot = DeltaRoot')
    (path : RootToNodePath root node) :
    RootToNodePath (root.castTree hGamma hDelta) node := by
  subst GammaRoot'
  subst DeltaRoot'
  exact path

/-- Theorem 7.4.1 (companion structure): A node occurrence in a fixed G2nnf
proof tree.  The path, rather than structural equality of the target subtree,
identifies the occurrence. -/
@[blueprint "chap7__theorem_7_4_1"]
structure NodeOccurrence {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    (root : G2nnfProofTree hL Γroot Δroot)
    (Γnode Δnode : LCS.Finset (FormulaN L)) where
  node : G2nnfProofTree hL Γnode Δnode
  path : RootToNodePath root node

/-- Compose two occurrence-sensitive root-to-node paths.  Composition
preserves every premise choice recorded by both paths. -/
@[blueprint "chap7__theorem_7_4_1"]
def RootToNodePath.trans {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γmid Δmid Γnode Δnode :
      LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot}
    {mid : G2nnfProofTree hL Γmid Δmid}
    {node : G2nnfProofTree hL Γnode Δnode}
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
def RootToNodePath.replace {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot}
    {node : G2nnfProofTree hL Γnode Δnode}
    (path : RootToNodePath root node)
    (replacement : G2nnfProofTree hL Γnode Δnode) :
    G2nnfProofTree hL Γroot Δroot :=
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

end LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
end
