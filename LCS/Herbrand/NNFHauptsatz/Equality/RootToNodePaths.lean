import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.CutElim.Hauptsatz.Equality
import Attach
import LCS.Herbrand.NNFHauptsatz.Equality.RootToNodePaths.ProofsStamp

/-! # Herbrand.NNFHauptsatz.Equality.RootToNodePaths

Root-to-node paths and node occurrences in G2nnf= proof trees.
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
namespace LCS.Herbrand.NNFHauptsatz.G2nnfEqProofTree

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

end LCS.Herbrand.NNFHauptsatz.G2nnfEqProofTree
end
