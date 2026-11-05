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
import LCS.Herbrand.NNFHauptsatz.Theorem.VariableSupport
import Attach
import LCS.Herbrand.NNFHauptsatz.Theorem.Paths.ProofsStamp

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

-- ATTACH-BLOCKER: private declaration
private theorem freshAlphaRenaming_fixes_left_root
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta)
    (avoid : LCS.Finset Nat) :
    formulaFinsetVarMapN (T.freshAlphaRenaming avoid) Gamma = Gamma := by
  apply formulaFinsetVarMapN_eq_self_of_fixed
  intro A hA x hx
  apply T.freshAlphaRenaming_fixed_root avoid x
  apply LCS.Finset.mem_union.mpr
  apply Or.inl
  exact formulaVariableSupport_subset_finsetSupport Gamma A x hA
    ((mem_formulaVariableSupport_iff_formulaAllVariables A x).mpr hx)

-- ATTACH-BLOCKER: private declaration
private theorem freshAlphaRenaming_fixes_right_root
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta)
    (avoid : LCS.Finset Nat) :
    formulaFinsetVarMapN (T.freshAlphaRenaming avoid) Delta = Delta := by
  apply formulaFinsetVarMapN_eq_self_of_fixed
  intro A hA x hx
  apply T.freshAlphaRenaming_fixed_root avoid x
  apply LCS.Finset.mem_union.mpr
  apply Or.inr
  exact formulaVariableSupport_subset_finsetSupport Delta A x hA
    ((mem_formulaVariableSupport_iff_formulaAllVariables A x).mpr hx)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Canonical alpha-renamed copy with exactly the same indexed root sequent. -/
noncomputable def freshAlphaCopy
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta)
    (avoid : LCS.Finset Nat) :
    G2nnfProofTree hL Gamma Delta :=
  (T.varMap (T.freshAlphaRenaming avoid)
      (T.freshAlphaRenaming_injective avoid)).castTree
    (T.freshAlphaRenaming_fixes_left_root avoid)
    (T.freshAlphaRenaming_fixes_right_root avoid)

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- Type-valued certificate tying a copy to one exact source and the
canonical avoidance parameter.  Its sole constructor prevents an arbitrary
same-index tree from masquerading as an alpha copy. -/
inductive FreshAlphaCopyCertificate
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (source : G2nnfProofTree hL Gamma Delta)
    (avoid : LCS.Finset Nat) :
    G2nnfProofTree hL Gamma Delta → Type where
  | canonical :
      FreshAlphaCopyCertificate source avoid
        (source.freshAlphaCopy avoid)







-- ===================================================================
-- Theorem 7.4.1 (helper): G2nnfProofTree.isSubtree
-- ===================================================================

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Theorem 7.4.1 (companion def): Structural subtree containment
(reflexive-transitive), retained for callers that only need containment.
Because equal subtrees can occur at different positions, the midsequent
predicate below deliberately uses `RootToNodePath` instead: its premise-choice
constructors identify an occurrence rather than merely a subtree value. -/
def isSubtree {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {ΓSub ΔSub : LCS.Finset (FormulaN L)}
    (tSub : G2nnfProofTree hL ΓSub ΔSub) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → Prop
  | _, _, .leaf _ _ h _ _ => h.elim
  | _, _, .extraAxiom _ _ h _ _ => h.elim
  | _, _, .axiom_ rule hAdmit hAx hSC =>
    HEq tSub (G2nnfDeductionTreeCore.axiom_ (extraAxiom := fun _ => False)
      (openLeaf := fun _ => False) rule hAdmit hAx hSC)
  | _, _, .onePremise rule hAdmit hPrem hSC sub =>
    HEq tSub (G2nnfDeductionTreeCore.onePremise rule hAdmit hPrem hSC sub) ∨
    isSubtree (hL := hL) tSub sub
  | _, _, .twoPremise rule hAdmit hPrem hSC sub1 sub2 =>
    HEq tSub (G2nnfDeductionTreeCore.twoPremise rule hAdmit hPrem hSC sub1 sub2) ∨
    isSubtree (hL := hL) tSub sub1 ∨ isSubtree (hL := hL) tSub sub2

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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Transporting root indices is injective on exact occurrence paths. -/
theorem RootToNodePath.castRoot_injective
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaRoot' DeltaRoot'
      GammaNode DeltaNode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    {node : G2nnfProofTree hL GammaNode DeltaNode}
    (hGamma : GammaRoot = GammaRoot')
    (hDelta : DeltaRoot = DeltaRoot') :
    Function.Injective
      (fun path : RootToNodePath root node =>
        path.castRoot hGamma hDelta) := by
  subst GammaRoot'
  subst DeltaRoot'
  intro first second h
  exact h

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Transport only the target indices of an exact path. -/
noncomputable def RootToNodePath.castTarget
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaNode DeltaNode
      GammaNode' DeltaNode' : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    {node : G2nnfProofTree hL GammaNode DeltaNode}
    (hGamma : GammaNode = GammaNode')
    (hDelta : DeltaNode = DeltaNode')
    (path : RootToNodePath root node) :
    RootToNodePath root (node.castTree hGamma hDelta) := by
  subst GammaNode'
  subst DeltaNode'
  exact path

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Constructor-for-constructor path transport through uniform injective
renaming.  Sole, left, and right premise choices are never identified. -/
noncomputable def RootToNodePath.varMap
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    {GammaRoot DeltaRoot GammaNode DeltaNode :
      LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    {node : G2nnfProofTree hL GammaNode DeltaNode}
    (path : RootToNodePath root node) :
    RootToNodePath (root.varMap ρ hρ) (node.varMap ρ hρ) :=
  match path with
  | .root T =>
      .root (T.varMap ρ hρ)
  | .onePremise rule hAdmit hPrem hSC sub path => by
      let subNew := sub.varMap ρ hρ
      have hConclusion :=
        G2nnfRuleCore.conclusion_varMap ρ rule
      have hEq1 :
          ((rule.varMap ρ).conclusion).1 =
            formulaFinsetVarMapN ρ (rule.conclusion).1 :=
        congrArg Prod.fst hConclusion
      have hEq2 :
          ((rule.varMap ρ).conclusion).2 =
            formulaFinsetVarMapN ρ (rule.conclusion).2 :=
        congrArg Prod.snd hConclusion
      have hPrem' :
          ((rule.varMap ρ).premises).length = 1 := by
        rw [G2nnfRuleCore.premises_length_varMap ρ hρ]
        exact hPrem
      have hSC' :=
        G2nnfRuleCore.sideConditions_varMap ρ hρ rule hSC
      have hPrem0 : 0 < (rule.premises).length := by
        rw [hPrem]
        omega
      have hPremEq :=
        G2nnfRuleCore.premises_nth_varMap
          ρ hρ rule 0 hPrem0
      have h1 :
          (((rule.varMap ρ).premises)[0]'(by omega)).1 =
            formulaFinsetVarMapN ρ
              ((rule.premises)[0]'hPrem0).1 := by
        simpa [g2nnfSequentVarMap] using congrArg Prod.fst hPremEq
      have h2 :
          (((rule.varMap ρ).premises)[0]'(by omega)).2 =
            formulaFinsetVarMapN ρ
              ((rule.premises)[0]'hPrem0).2 := by
        simpa [g2nnfSequentVarMap] using congrArg Prod.snd hPremEq
      let subCast :
          G2nnfProofTree hL
            (((rule.varMap ρ).premises)[0]'(by omega)).1
            (((rule.varMap ρ).premises)[0]'(by omega)).2 :=
        subNew.castTree h1.symm h2.symm
      have rest :
          RootToNodePath subCast (node.varMap ρ hρ) :=
        by
          simpa only [subCast, subNew] using
            (path.varMap ρ hρ).castRoot h1.symm h2.symm
      have mapped :
          RootToNodePath
            (G2nnfProofTree.castTree (hL := hL) hEq1 hEq2
              (G2nnfDeductionTreeCore.onePremise (rule.varMap ρ)
              (G2nnfRuleCore.bareAtomicAxiom_varMap ρ rule hAdmit)
              hPrem' hSC' subCast))
            (node.varMap ρ hρ) :=
        (RootToNodePath.onePremise (rule.varMap ρ)
          (G2nnfRuleCore.bareAtomicAxiom_varMap ρ rule hAdmit)
          hPrem' hSC' subCast rest).castRoot hEq1 hEq2
      simpa only [G2nnfProofTree.varMap, subCast, subNew] using mapped
  | .leftPremise rule hAdmit hPrem hSC sub1 sub2 path => by
      let subNew1 := sub1.varMap ρ hρ
      let subNew2 := sub2.varMap ρ hρ
      have hConclusion :=
        G2nnfRuleCore.conclusion_varMap ρ rule
      have hEq1 :
          ((rule.varMap ρ).conclusion).1 =
            formulaFinsetVarMapN ρ (rule.conclusion).1 :=
        congrArg Prod.fst hConclusion
      have hEq2 :
          ((rule.varMap ρ).conclusion).2 =
            formulaFinsetVarMapN ρ (rule.conclusion).2 :=
        congrArg Prod.snd hConclusion
      have hPrem' :
          ((rule.varMap ρ).premises).length = 2 := by
        rw [G2nnfRuleCore.premises_length_varMap ρ hρ]
        exact hPrem
      have hSC' :=
        G2nnfRuleCore.sideConditions_varMap ρ hρ rule hSC
      have hPrem0 : 0 < (rule.premises).length := by
        rw [hPrem]
        omega
      have hPrem1 : 1 < (rule.premises).length := by
        rw [hPrem]
        omega
      have hPremEq0 :=
        G2nnfRuleCore.premises_nth_varMap
          ρ hρ rule 0 hPrem0
      have hPremEq1 :=
        G2nnfRuleCore.premises_nth_varMap
          ρ hρ rule 1 hPrem1
      have h1_0 :
          (((rule.varMap ρ).premises)[0]'(by omega)).1 =
            formulaFinsetVarMapN ρ
              ((rule.premises)[0]'hPrem0).1 := by
        simpa [g2nnfSequentVarMap] using congrArg Prod.fst hPremEq0
      have h2_0 :
          (((rule.varMap ρ).premises)[0]'(by omega)).2 =
            formulaFinsetVarMapN ρ
              ((rule.premises)[0]'hPrem0).2 := by
        simpa [g2nnfSequentVarMap] using congrArg Prod.snd hPremEq0
      have h1_1 :
          (((rule.varMap ρ).premises)[1]'(by omega)).1 =
            formulaFinsetVarMapN ρ
              ((rule.premises)[1]'hPrem1).1 := by
        simpa [g2nnfSequentVarMap] using congrArg Prod.fst hPremEq1
      have h2_1 :
          (((rule.varMap ρ).premises)[1]'(by omega)).2 =
            formulaFinsetVarMapN ρ
              ((rule.premises)[1]'hPrem1).2 := by
        simpa [g2nnfSequentVarMap] using congrArg Prod.snd hPremEq1
      let subCast1 :
          G2nnfProofTree hL
            (((rule.varMap ρ).premises)[0]'(by omega)).1
            (((rule.varMap ρ).premises)[0]'(by omega)).2 :=
        subNew1.castTree h1_0.symm h2_0.symm
      let subCast2 :
          G2nnfProofTree hL
            (((rule.varMap ρ).premises)[1]'(by omega)).1
            (((rule.varMap ρ).premises)[1]'(by omega)).2 :=
        subNew2.castTree h1_1.symm h2_1.symm
      have rest :
          RootToNodePath subCast1 (node.varMap ρ hρ) :=
        by
          simpa only [subCast1, subNew1] using
            (path.varMap ρ hρ).castRoot h1_0.symm h2_0.symm
      have mapped :
          RootToNodePath
            (G2nnfProofTree.castTree (hL := hL) hEq1 hEq2
              (G2nnfDeductionTreeCore.twoPremise (rule.varMap ρ)
              (G2nnfRuleCore.bareAtomicAxiom_varMap ρ rule hAdmit)
              hPrem' hSC' subCast1 subCast2))
            (node.varMap ρ hρ) :=
        (RootToNodePath.leftPremise (rule.varMap ρ)
          (G2nnfRuleCore.bareAtomicAxiom_varMap ρ rule hAdmit)
          hPrem' hSC' subCast1 subCast2 rest).castRoot hEq1 hEq2
      simpa only [G2nnfProofTree.varMap, subCast1, subCast2,
        subNew1, subNew2] using mapped
  | .rightPremise rule hAdmit hPrem hSC sub1 sub2 path => by
      let subNew1 := sub1.varMap ρ hρ
      let subNew2 := sub2.varMap ρ hρ
      have hConclusion :=
        G2nnfRuleCore.conclusion_varMap ρ rule
      have hEq1 :
          ((rule.varMap ρ).conclusion).1 =
            formulaFinsetVarMapN ρ (rule.conclusion).1 :=
        congrArg Prod.fst hConclusion
      have hEq2 :
          ((rule.varMap ρ).conclusion).2 =
            formulaFinsetVarMapN ρ (rule.conclusion).2 :=
        congrArg Prod.snd hConclusion
      have hPrem' :
          ((rule.varMap ρ).premises).length = 2 := by
        rw [G2nnfRuleCore.premises_length_varMap ρ hρ]
        exact hPrem
      have hSC' :=
        G2nnfRuleCore.sideConditions_varMap ρ hρ rule hSC
      have hPrem0 : 0 < (rule.premises).length := by
        rw [hPrem]
        omega
      have hPrem1 : 1 < (rule.premises).length := by
        rw [hPrem]
        omega
      have hPremEq0 :=
        G2nnfRuleCore.premises_nth_varMap
          ρ hρ rule 0 hPrem0
      have hPremEq1 :=
        G2nnfRuleCore.premises_nth_varMap
          ρ hρ rule 1 hPrem1
      have h1_0 :
          (((rule.varMap ρ).premises)[0]'(by omega)).1 =
            formulaFinsetVarMapN ρ
              ((rule.premises)[0]'hPrem0).1 := by
        simpa [g2nnfSequentVarMap] using congrArg Prod.fst hPremEq0
      have h2_0 :
          (((rule.varMap ρ).premises)[0]'(by omega)).2 =
            formulaFinsetVarMapN ρ
              ((rule.premises)[0]'hPrem0).2 := by
        simpa [g2nnfSequentVarMap] using congrArg Prod.snd hPremEq0
      have h1_1 :
          (((rule.varMap ρ).premises)[1]'(by omega)).1 =
            formulaFinsetVarMapN ρ
              ((rule.premises)[1]'hPrem1).1 := by
        simpa [g2nnfSequentVarMap] using congrArg Prod.fst hPremEq1
      have h2_1 :
          (((rule.varMap ρ).premises)[1]'(by omega)).2 =
            formulaFinsetVarMapN ρ
              ((rule.premises)[1]'hPrem1).2 := by
        simpa [g2nnfSequentVarMap] using congrArg Prod.snd hPremEq1
      let subCast1 :
          G2nnfProofTree hL
            (((rule.varMap ρ).premises)[0]'(by omega)).1
            (((rule.varMap ρ).premises)[0]'(by omega)).2 :=
        subNew1.castTree h1_0.symm h2_0.symm
      let subCast2 :
          G2nnfProofTree hL
            (((rule.varMap ρ).premises)[1]'(by omega)).1
            (((rule.varMap ρ).premises)[1]'(by omega)).2 :=
        subNew2.castTree h1_1.symm h2_1.symm
      have rest :
          RootToNodePath subCast2 (node.varMap ρ hρ) :=
        by
          simpa only [subCast2, subNew2] using
            (path.varMap ρ hρ).castRoot h1_1.symm h2_1.symm
      have mapped :
          RootToNodePath
            (G2nnfProofTree.castTree (hL := hL) hEq1 hEq2
              (G2nnfDeductionTreeCore.twoPremise (rule.varMap ρ)
              (G2nnfRuleCore.bareAtomicAxiom_varMap ρ rule hAdmit)
              hPrem' hSC' subCast1 subCast2))
            (node.varMap ρ hρ) :=
        (RootToNodePath.rightPremise (rule.varMap ρ)
          (G2nnfRuleCore.bareAtomicAxiom_varMap ρ rule hAdmit)
          hPrem' hSC' subCast1 subCast2 rest).castRoot hEq1 hEq2
      simpa only [G2nnfProofTree.varMap, subCast1, subCast2,
        subNew1, subNew2] using mapped

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The first premise choice of a nonempty exact path.  Distinct numeric
tags make constructor preservation observable through index transports. -/
def RootToNodePath.firstPremiseTag
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaNode DeltaNode :
      LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    {node : G2nnfProofTree hL GammaNode DeltaNode} :
    RootToNodePath root node → Nat
  | .root _ => 0
  | .onePremise _ _ _ _ _ _ => 1
  | .leftPremise _ _ _ _ _ _ _ => 2
  | .rightPremise _ _ _ _ _ _ _ => 3

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Casting only the root indices leaves the first premise choice intact. -/
theorem RootToNodePath.firstPremiseTag_castRoot
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaRoot' DeltaRoot'
      GammaNode DeltaNode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    {node : G2nnfProofTree hL GammaNode DeltaNode}
    (hGamma : GammaRoot = GammaRoot')
    (hDelta : DeltaRoot = DeltaRoot')
    (path : RootToNodePath root node) :
    (path.castRoot hGamma hDelta).firstPremiseTag =
      path.firstPremiseTag := by
  subst GammaRoot'
  subst DeltaRoot'
  rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Equal-valued left and right subtrees remain different occurrences after
path transport. -/
theorem RootToNodePath.varMap_duplicate_left_right_distinct
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (A : FormulaN L)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (hSC : G2nnfRuleCore.SideConditions (.conjRight A A Gamma Delta))
    (sub : G2nnfProofTree hL Gamma (LCS.Finset.insert A Delta)) :
    let root :=
      G2nnfDeductionTreeCore.twoPremise (.conjRight A A Gamma Delta)
        trivial rfl hSC sub sub
    let left : RootToNodePath root sub :=
      .leftPremise (.conjRight A A Gamma Delta) trivial rfl hSC
        sub sub (.root sub)
    let right : RootToNodePath root sub :=
      .rightPremise (.conjRight A A Gamma Delta) trivial rfl hSC
        sub sub (.root sub)
    left.varMap ρ hρ ≠ right.varMap ρ hρ := by
  dsimp only
  intro h
  simp only [RootToNodePath.varMap, id_eq] at h
  have hInner := (RootToNodePath.castRoot_injective _ _) h
  cases hInner

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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Transport a node occurrence through injective uniform renaming. -/
noncomputable def NodeOccurrence.varMap
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    {GammaRoot DeltaRoot GammaNode DeltaNode :
      LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    (occurrence : NodeOccurrence root GammaNode DeltaNode) :
    NodeOccurrence (root.varMap ρ hρ)
      (formulaFinsetVarMapN ρ GammaNode)
      (formulaFinsetVarMapN ρ DeltaNode) :=
  ⟨occurrence.node.varMap ρ hρ, occurrence.path.varMap ρ hρ⟩

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- A source path transported into the canonical whole-tree alpha copy.  The
target is the uniformly renamed source node; it is not an arbitrary
same-index tree. -/
noncomputable def RootToNodePath.freshAlphaCopy
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaNode DeltaNode :
      LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    {node : G2nnfProofTree hL GammaNode DeltaNode}
    (path : RootToNodePath root node)
    (avoid : LCS.Finset Nat) :
    RootToNodePath (root.freshAlphaCopy avoid)
      (node.varMap (root.freshAlphaRenaming avoid)
        (root.freshAlphaRenaming_injective avoid)) := by
  let ρ := root.freshAlphaRenaming avoid
  let hρ := root.freshAlphaRenaming_injective avoid
  have mapped := path.varMap ρ hρ
  have casted :=
    mapped.castRoot
      (root.freshAlphaRenaming_fixes_left_root avoid)
      (root.freshAlphaRenaming_fixes_right_root avoid)
  simpa only [G2nnfProofTree.freshAlphaCopy, ρ, hρ] using casted

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Occurrence-valued counterpart of `RootToNodePath.freshAlphaCopy`. -/
noncomputable def NodeOccurrence.freshAlphaCopy
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaNode DeltaNode :
      LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    (occurrence : NodeOccurrence root GammaNode DeltaNode)
    (avoid : LCS.Finset Nat) :
    NodeOccurrence (root.freshAlphaCopy avoid)
      (formulaFinsetVarMapN (root.freshAlphaRenaming avoid) GammaNode)
      (formulaFinsetVarMapN (root.freshAlphaRenaming avoid) DeltaNode) :=
  ⟨occurrence.node.varMap (root.freshAlphaRenaming avoid)
      (root.freshAlphaRenaming_injective avoid),
    occurrence.path.freshAlphaCopy avoid⟩

-- ATTACH-BLOCKER: private declaration
/-- Explicit reduction at an axiom leaf, avoiding the indexed equation
theorem generator in later simplification. -/
private theorem isCutFree_axiom_
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (rule : G2nnfRuleCore L)
    (hAdmit : rule.BareAtomicAxiom)
    (hAxiom : (rule.premises).length = 0)
    (hSC : G2nnfRuleCore.SideConditions rule) :
    isCutFree (hL := hL)
      (G2nnfDeductionTreeCore.axiom_ (extraAxiom := fun _ => False)
        (openLeaf := fun _ => False) rule hAdmit hAxiom hSC) ↔
      True := by
  rfl

-- ATTACH-BLOCKER: private declaration
/-- Explicit reduction at a one-premise node. -/
private theorem isCutFree_onePremise
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (rule : G2nnfRuleCore L)
    (hAdmit : rule.BareAtomicAxiom)
    (hPrem : (rule.premises).length = 1)
    (hSC : G2nnfRuleCore.SideConditions rule)
    (sub : G2nnfProofTree hL
      ((rule.premises)[0]'(by omega)).1
      ((rule.premises)[0]'(by omega)).2) :
    isCutFree (hL := hL)
      (G2nnfDeductionTreeCore.onePremise
        rule hAdmit hPrem hSC sub) ↔
      (match rule with
       | .cut _ _ _ _ _ => False
       | _ => True) ∧
      sub.isCutFree (hL := hL) := by
  cases rule <;> rfl

-- ATTACH-BLOCKER: private declaration
/-- Explicit reduction at a two-premise node. -/
private theorem isCutFree_twoPremise
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (rule : G2nnfRuleCore L)
    (hAdmit : rule.BareAtomicAxiom)
    (hPrem : (rule.premises).length = 2)
    (hSC : G2nnfRuleCore.SideConditions rule)
    (sub1 : G2nnfProofTree hL
      ((rule.premises)[0]'(by omega)).1
      ((rule.premises)[0]'(by omega)).2)
    (sub2 : G2nnfProofTree hL
      ((rule.premises)[1]'(by omega)).1
      ((rule.premises)[1]'(by omega)).2) :
    isCutFree (hL := hL)
      (G2nnfDeductionTreeCore.twoPremise
        rule hAdmit hPrem hSC sub1 sub2) ↔
      (match rule with
       | .cut _ _ _ _ _ => False
       | _ => True) ∧
      sub1.isCutFree (hL := hL) ∧ sub2.isCutFree (hL := hL) := by
  cases rule <;> rfl

-- ATTACH-BLOCKER: private declaration
/-- Uniform renaming preserves whether the current rule is cut-free. -/
private theorem cutFreeRule_varMap
    {L : Language} (ρ : Nat → Nat) (rule : G2nnfRuleCore L) :
    (match rule.varMap ρ with
      | .cut _ _ _ _ _ => False
      | _ => True) ↔
    (match rule with
      | .cut _ _ _ _ _ => False
      | _ => True) := by
  cases rule <;> rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Index casts preserve cut-freedom exactly. -/
theorem isCutFree_castTree
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta Gamma' Delta' : LCS.Finset (FormulaN L)}
    (hGamma : Gamma = Gamma') (hDelta : Delta = Delta')
    (T : G2nnfProofTree hL Gamma Delta) :
    (T.castTree hGamma hDelta).isCutFree (hL := hL) ↔ T.isCutFree (hL := hL) := by
  subst Gamma'
  subst Delta'
  rfl

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Injective uniform renaming preserves and reflects cut-freedom. -/
theorem isCutFree_varMap_iff
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta) :
    (T.varMap ρ hρ).isCutFree (hL := hL) ↔ T.isCutFree (hL := hL) := by
  induction T with
  | leaf _ _ h _ _ => exact h.elim
  | extraAxiom _ _ h _ _ => exact h.elim
  | axiom_ rule hAdmit hAxiom hSC =>
      simp only [G2nnfProofTree.varMap]
      refine (isCutFree_castTree _ _ _).trans ?_
      simp only [isCutFree_axiom_]
  | onePremise rule hAdmit hPrem hSC sub ih =>
      simp only [G2nnfProofTree.varMap]
      refine (isCutFree_castTree _ _ _).trans ?_
      simp only [isCutFree_castTree,
        isCutFree_onePremise,
        cutFreeRule_varMap, ih]
  | twoPremise rule hAdmit hPrem hSC sub1 sub2 ih1 ih2 =>
      simp only [G2nnfProofTree.varMap]
      refine (isCutFree_castTree _ _ _).trans ?_
      simp only [isCutFree_castTree,
        isCutFree_twoPremise,
        cutFreeRule_varMap, ih1, ih2]





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
/-- A one-premise descent factors into the immediate descent followed by
its remaining path. -/
theorem RootToNodePath.onePremise_eq_immediate_trans
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (rule : G2nnfRuleCore L)
    (hAdmit : rule.BareAtomicAxiom)
    (hPrem : (rule.premises).length = 1)
    (hSC : G2nnfRuleCore.SideConditions rule)
    (sub : G2nnfProofTree hL
      ((rule.premises)[0]'(by omega)).1
      ((rule.premises)[0]'(by omega)).2)
    {GammaNode DeltaNode : LCS.Finset (FormulaN L)}
    {node : G2nnfProofTree hL GammaNode DeltaNode}
    (path : RootToNodePath sub node) :
    RootToNodePath.onePremise
        rule hAdmit hPrem hSC sub path =
      (RootToNodePath.onePremise
        rule hAdmit hPrem hSC sub
        (RootToNodePath.root sub)).trans path := by
  rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Appending the empty target path leaves an exact path unchanged. -/
theorem RootToNodePath.trans_root
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaNode DeltaNode :
      LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    {node : G2nnfProofTree hL GammaNode DeltaNode}
    (path : RootToNodePath root node) :
    path.trans (.root node) = path := by
  induction path with
  | root T => rfl
  | onePremise rule hAdmit hPrem hSC sub rest ih =>
      simp only [RootToNodePath.trans, ih]
  | leftPremise rule hAdmit hPrem hSC sub1 sub2 rest ih =>
      simp only [RootToNodePath.trans, ih]
  | rightPremise rule hAdmit hPrem hSC sub1 sub2 rest ih =>
      simp only [RootToNodePath.trans, ih]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Exact path composition is associative. -/
theorem RootToNodePath.trans_assoc
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaMid₁ DeltaMid₁
      GammaMid₂ DeltaMid₂ GammaNode DeltaNode :
      LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    {mid₁ : G2nnfProofTree hL GammaMid₁ DeltaMid₁}
    {mid₂ : G2nnfProofTree hL GammaMid₂ DeltaMid₂}
    {node : G2nnfProofTree hL GammaNode DeltaNode}
    (first : RootToNodePath root mid₁)
    (second : RootToNodePath mid₁ mid₂)
    (third : RootToNodePath mid₂ node) :
    (first.trans second).trans third =
      first.trans (second.trans third) := by
  induction first with
  | root T => rfl
  | onePremise rule hAdmit hPrem hSC sub rest ih =>
      simp only [RootToNodePath.trans, ih second]
  | leftPremise rule hAdmit hPrem hSC sub1 sub2 rest ih =>
      simp only [RootToNodePath.trans, ih second]
  | rightPremise rule hAdmit hPrem hSC sub1 sub2 rest ih =>
      simp only [RootToNodePath.trans, ih second]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Casting the root of a path commutes with appending a later path. -/
theorem RootToNodePath.castRoot_trans
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaRoot' DeltaRoot'
      GammaMid DeltaMid GammaNode DeltaNode :
      LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    {mid : G2nnfProofTree hL GammaMid DeltaMid}
    {node : G2nnfProofTree hL GammaNode DeltaNode}
    (hGamma : GammaRoot = GammaRoot')
    (hDelta : DeltaRoot = DeltaRoot')
    (first : RootToNodePath root mid)
    (second : RootToNodePath mid node) :
    (first.castRoot hGamma hDelta).trans second =
      (first.trans second).castRoot hGamma hDelta := by
  subst GammaRoot'
  subst DeltaRoot'
  rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Normalize the two zero-step index bridges surrounding one mapped
immediate descent. -/
theorem RootToNodePath.castBridge_trans_castedStep
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaCurrent DeltaCurrent
      GammaCurrent' DeltaCurrent' GammaSub DeltaSub
      GammaSub' DeltaSub' : LCS.Finset (FormulaN L)}
    {outer : G2nnfProofTree hL GammaRoot DeltaRoot}
    (current : G2nnfProofTree hL GammaCurrent DeltaCurrent)
    (sub : G2nnfProofTree hL GammaSub DeltaSub)
    (hCurrentGamma : GammaCurrent = GammaCurrent')
    (hCurrentDelta : DeltaCurrent = DeltaCurrent')
    (hSubGamma : GammaSub = GammaSub')
    (hSubDelta : DeltaSub = DeltaSub')
    (path : RootToNodePath outer
      (current.castTree hCurrentGamma hCurrentDelta))
    (step : RootToNodePath current
      (sub.castTree hSubGamma hSubDelta)) :
    ((path.trans
        ((RootToNodePath.root current).castRoot
          hCurrentGamma hCurrentDelta)).trans step).trans
        ((RootToNodePath.root sub).castRoot hSubGamma hSubDelta) =
      path.trans
        ((step.trans
          ((RootToNodePath.root sub).castRoot hSubGamma hSubDelta)
          ).castRoot hCurrentGamma hCurrentDelta) := by
  cases hCurrentGamma
  cases hCurrentDelta
  cases hSubGamma
  cases hSubDelta
  change RootToNodePath outer current at path
  change RootToNodePath current sub at step
  simpa only [G2nnfProofTree.castTree, RootToNodePath.castRoot,
    RootToNodePath.trans_root]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Path renaming commutes with exact path composition. -/
theorem RootToNodePath.varMap_trans
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    {GammaRoot DeltaRoot GammaMid DeltaMid GammaNode DeltaNode :
      LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    {mid : G2nnfProofTree hL GammaMid DeltaMid}
    {node : G2nnfProofTree hL GammaNode DeltaNode}
    (first : RootToNodePath root mid)
    (second : RootToNodePath mid node) :
    (first.trans second).varMap ρ hρ =
      (first.varMap ρ hρ).trans (second.varMap ρ hρ) := by
  induction first with
  | root T =>
      rfl
  | onePremise rule hAdmit hPrem hSC sub path ih =>
      simp only [RootToNodePath.trans, RootToNodePath.varMap,
        ih second, id_eq, g2nnfSequentVarMap]
      symm
      refine (RootToNodePath.castRoot_trans _ _ _ _).trans ?_
      congr 1
      simp only [RootToNodePath.trans]
      congr 1
      exact RootToNodePath.castRoot_trans _ _ _ _
  | leftPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
      simp only [RootToNodePath.trans, RootToNodePath.varMap,
        ih second, id_eq, g2nnfSequentVarMap]
      symm
      refine (RootToNodePath.castRoot_trans _ _ _ _).trans ?_
      congr 1
      simp only [RootToNodePath.trans]
      congr 1
      exact RootToNodePath.castRoot_trans _ _ _ _
  | rightPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
      simp only [RootToNodePath.trans, RootToNodePath.varMap,
        ih second, id_eq, g2nnfSequentVarMap]
      symm
      refine (RootToNodePath.castRoot_trans _ _ _ _).trans ?_
      congr 1
      simp only [RootToNodePath.trans]
      congr 1
      exact RootToNodePath.castRoot_trans _ _ _ _

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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The rebuilt tree has an exact path to the replacement occurrence.  This
is the target-side zipper used by the local exchange certificate. -/
def RootToNodePath.replacementPath {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot}
    {node : G2nnfProofTree hL Γnode Δnode}
    (path : RootToNodePath root node)
    (replacement : G2nnfProofTree hL Γnode Δnode) :
    RootToNodePath (path.replace replacement) replacement :=
  match Γroot, Δroot, Γnode, Δnode, root, node, path, replacement with
  | _, _, _, _, _, _, .root _, replacement => .root replacement
  | _, _, _, _, _, _, .onePremise rule hAdmit hPrem hSC sub rest, replacement =>
    .onePremise rule hAdmit hPrem hSC
      (rest.replace replacement) (rest.replacementPath replacement)
  | _, _, _, _, _, _, .leftPremise rule hAdmit hPrem hSC sub1 sub2 rest, replacement =>
    .leftPremise rule hAdmit hPrem hSC
      (rest.replace replacement) sub2 (rest.replacementPath replacement)
  | _, _, _, _, _, _, .rightPremise rule hAdmit hPrem hSC sub1 sub2 rest, replacement =>
    .rightPremise rule hAdmit hPrem hSC
      sub1 (rest.replace replacement) (rest.replacementPath replacement)

-- ATTACH-BLOCKER: private declaration
/-- A duplicated conjunction step inherits NNF from its actual premise. -/
private theorem conjRight_sideConditions_of_subtree
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (A : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L))
    (hConjRect : isRectified (.conj A A))
    (sub : G2nnfProofTree hL Gamma (LCS.Finset.insert A Delta)) :
    (G2nnfRuleCore.conjRight A A Gamma Delta).SideConditions := by
  have hNNF := G2nnfDeductionTreeCore.allNNF sub
  refine ⟨trivial, ?_, ?_, AllRectified.insert_right hConjRect
    (AllRectified.of_insert_right (G2nnfProofTree.allRectified (hL := hL) sub))⟩
  · refine ⟨hNNF.1, ?_⟩
    intro F hF
    rcases LCS.Finset.mem_insert.mp hF with rfl | hF
    · have hA := hNNF.2 A (LCS.Finset.mem_insert.mpr (Or.inl rfl))
      exact ⟨hA, hA⟩
    · exact hNNF.2 F (LCS.Finset.mem_insert.mpr (Or.inr hF))
  · intro seq hSeq
    simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil,
      or_false, or_self] at hSeq
    subst seq
    exact hNNF

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Adversarial occurrence-identity regression: the same proof-tree value can
occupy both premises of a node, with the same sequent index, but its left and
right occurrences remain distinct because their paths record different
premise choices. -/
theorem duplicateEqualSequentOccurrences_distinct {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (A : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L))
    (hConjRect : isRectified (.conj A A))
    (sub : G2nnfProofTree hL Gamma (LCS.Finset.insert A Delta)) :
    let root : G2nnfProofTree hL Gamma
        (LCS.Finset.insert (.conj A A) Delta) :=
      .twoPremise (.conjRight A A Gamma Delta) trivial rfl
        (conjRight_sideConditions_of_subtree A Gamma Delta hConjRect sub) sub sub
    let left : NodeOccurrence root Gamma
        (LCS.Finset.insert A Delta) :=
      ⟨sub, .leftPremise (.conjRight A A Gamma Delta) trivial rfl
        (conjRight_sideConditions_of_subtree A Gamma Delta hConjRect sub)
        sub sub (.root sub)⟩
    let right : NodeOccurrence root Gamma
        (LCS.Finset.insert A Delta) :=
      ⟨sub, .rightPremise (.conjRight A A Gamma Delta) trivial rfl
        (conjRight_sideConditions_of_subtree A Gamma Delta hConjRect sub)
        sub sub (.root sub)⟩
    left ≠ right := by
  dsimp only
  intro h
  cases h

end LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
end

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
namespace LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule

/-- Lemma 7.4.2 (companion def): Predicate asserting that a formula `f` appears in some sequent (antecedent or succedent) of a G2nnf proof tree. Used as the G2nnf analog of `proofTreeFormulae` (LK version) — since G2nnf sequents are `LCS.Finset (FormulaN L)` rather than `List (FormulaN L)`, we express tree-containment as a Prop instead of producing a concrete list. The recursion walks the whole tree: at each node, `f` may occur in the current node's conclusion sequent `(Γ, Δ)` (the TYPE INDEX, which is the stored rule's actual conclusion) or in any sub-proof. Indexing note: we pattern-match on the IMPLICIT TYPE INDEX `{Γ Δ}` so that `Γ Δ` here denote the actual conclusion sequent of this node, rather than only the rule's stored side contexts — the rule's conclusion typically inserts the principal formula, so the raw fields miss it. -/
@[blueprint "chap7__lemma_7_4_2"]
def g2nnfProofTreeContainsFormula {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (tree : G2nnfProofTree hL Γ Δ) (f : FormulaN L) : Prop :=
  match tree with
  | .leaf _ _ h _ _ => h.elim
  | .extraAxiom _ _ h _ _ => h.elim
  | .axiom_ _ _ _ _ => f ∈ Γ ∨ f ∈ Δ
  | .onePremise _ _ _ _ sub =>
    f ∈ Γ ∨ f ∈ Δ ∨ g2nnfProofTreeContainsFormula (hL := hL) sub f
  | .twoPremise _ _ _ _ sub1 sub2 =>
    f ∈ Γ ∨ f ∈ Δ ∨
    g2nnfProofTreeContainsFormula (hL := hL) sub1 f ∨
    g2nnfProofTreeContainsFormula (hL := hL) sub2 f

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Purity.Proofs
/-- A formula in either side of the root sequent occurs in the proof tree. -/
theorem g2nnfProofTreeContainsFormula_of_root
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)} (tree : G2nnfProofTree hL Γ Δ)
    (f : FormulaN L) (hf : f ∈ Γ ∨ f ∈ Δ) :
    g2nnfProofTreeContainsFormula tree f := by
  cases tree with
  | leaf _ _ h _ _ => exact h.elim
  | extraAxiom _ _ h _ _ => exact h.elim
  | axiom_ _ _ _ _ => exact hf
  | onePremise _ _ _ _ _ =>
      exact hf.elim Or.inl (fun h => Or.inr (Or.inl h))
  | twoPremise _ _ _ _ _ _ =>
      exact hf.elim Or.inl (fun h => Or.inr (Or.inl h))

-- ===================================================================
-- Lemma 7.4.2 (companion def): g2nnfNoFreeBoundOverlap
-- ===================================================================

/-- Lemma 7.4.2 (companion def): Predicate asserting that variable `y` does not occur both free and bound in any single formula of the G2nnf proof tree. Checked globally over the whole tree via `g2nnfProofTreeContainsFormula`. -/
@[blueprint "chap7__lemma_7_4_2"]
def g2nnfNoFreeBoundOverlap {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (y : Nat) (tree : G2nnfProofTree hL Γ Δ) : Prop :=
  ∀ (f : FormulaN L),
    g2nnfProofTreeContainsFormula tree f →
    ¬ (Membership.mem (formulaFVN f) y ∧
       Membership.mem (formulaBVN f) y)

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Purity
/-- The standing rectification invariant makes the per-formula no-overlap
clause available at every proof-tree node. -/
theorem g2nnfNoFreeBoundOverlap_of_proofTree
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (y : Nat) (tree : G2nnfProofTree hL Gamma Delta) :
    g2nnfNoFreeBoundOverlap y tree := by
  induction tree with
  | leaf _ _ h _ _ => exact h.elim
  | extraAxiom _ _ h _ _ => exact h.elim
  | axiom_ rule hAdmit hAxiom hSC =>
      intro f hf
      simp only [g2nnfProofTreeContainsFormula] at hf
      rcases hf with hf | hf
      · exact (hSC.conclusionRectified.1 f hf).1 y
      · exact (hSC.conclusionRectified.2 f hf).1 y
  | onePremise rule hAdmit hPrem hSC sub ih =>
      intro f hf
      simp only [g2nnfProofTreeContainsFormula] at hf
      rcases hf with hf | hf | hf
      · exact (hSC.conclusionRectified.1 f hf).1 y
      · exact (hSC.conclusionRectified.2 f hf).1 y
      · exact ih f hf
  | twoPremise rule hAdmit hPrem hSC sub1 sub2 ih1 ih2 =>
      intro f hf
      simp only [g2nnfProofTreeContainsFormula] at hf
      rcases hf with hf | hf | hf | hf
      · exact (hSC.conclusionRectified.1 f hf).1 y
      · exact (hSC.conclusionRectified.2 f hf).1 y
      · exact ih1 f hf
      · exact ih2 f hf

-- ===================================================================
-- Lemma 7.4.2 (companion def): g2nnfEigenvariableOccursOnlyInSubtree
-- ===================================================================

/-- Lemma 7.4.2 (companion def): Every formula occurrence in one sequent is
free of `y`, whether `y` would occur free or bound in that formula. -/
@[blueprint "chap7__lemma_7_4_2"]
def g2nnfSequentVariableFree {L : Language}
    [DecidableEq (FormulaN L)]
    (y : Nat) (Γ Δ : LCS.Finset (FormulaN L)) : Prop :=
  ∀ f : FormulaN L, f ∈ Γ ∨ f ∈ Δ →
    ¬ Membership.mem (formulaAllVariables f) y

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Purity
/-- Absence from a sequent is preserved by injective uniform renaming. -/
theorem g2nnfSequentVariableFree_varMap
    {L : Language} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (y : Nat) (Gamma Delta : LCS.Finset (FormulaN L))
    (hFree : g2nnfSequentVariableFree y Gamma Delta) :
    g2nnfSequentVariableFree (ρ y)
      (formulaFinsetVarMapN ρ Gamma)
      (formulaFinsetVarMapN ρ Delta) := by
  intro F hF hy
  rcases hF with hF | hF
  · rcases (mem_formulaFinsetVarMapN_iff ρ Gamma F).mp hF with
      ⟨A, hA, rfl⟩
    exact hFree A (Or.inl hA)
      ((formulaAllVariables_formulaVarMapN_image_iff ρ hρ A y).mp hy)
  · rcases (mem_formulaFinsetVarMapN_iff ρ Delta F).mp hF with
      ⟨A, hA, rfl⟩
    exact hFree A (Or.inr hA)
      ((formulaAllVariables_formulaVarMapN_image_iff ρ hρ A y).mp hy)

/-- Lemma 7.4.2 (companion def): Every formula occurrence at every node of a
G2nnf proof tree is free of `y`.  The recursive definition checks node
occurrences directly instead of collecting formula values into a set. -/
@[blueprint "chap7__lemma_7_4_2"]
def g2nnfProofTreeVariableFree {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] (y : Nat)
    {Γ Δ : LCS.Finset (FormulaN L)}
    (tree : G2nnfProofTree hL Γ Δ) : Prop :=
  match tree with
  | .leaf _ _ h _ _ => h.elim
  | .extraAxiom _ _ h _ _ => h.elim
  | .axiom_ _ _ _ _ =>
    g2nnfSequentVariableFree y Γ Δ
  | .onePremise _ _ _ _ sub =>
    g2nnfSequentVariableFree y Γ Δ ∧
    g2nnfProofTreeVariableFree (hL := hL) y sub
  | .twoPremise _ _ _ _ sub1 sub2 =>
    g2nnfSequentVariableFree y Γ Δ ∧
    g2nnfProofTreeVariableFree (hL := hL) y sub1 ∧
    g2nnfProofTreeVariableFree (hL := hL) y sub2

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Purity
/-- Index transport preserves whole-subtree variable absence exactly. -/
theorem g2nnfProofTreeVariableFree_castTree
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (y : Nat)
    {Gamma Delta Gamma' Delta' : LCS.Finset (FormulaN L)}
    (hGamma : Gamma = Gamma') (hDelta : Delta = Delta')
    (T : G2nnfProofTree hL Gamma Delta) :
    g2nnfProofTreeVariableFree y (T.castTree hGamma hDelta) ↔
      g2nnfProofTreeVariableFree y T := by
  subst Gamma'
  subst Delta'
  rfl

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Purity
/-- Whole-subtree variable absence is preserved by injective uniform
renaming. -/
theorem g2nnfProofTreeVariableFree_varMap
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (y : Nat)
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta)
    (hFree : g2nnfProofTreeVariableFree y T) :
    g2nnfProofTreeVariableFree (ρ y) (T.varMap ρ hρ) := by
  induction T with
  | leaf _ _ h _ _ => exact h.elim
  | extraAxiom _ _ h _ _ => exact h.elim
  | axiom_ rule hAdmit hAxiom hSC =>
      simp only [G2nnfProofTree.varMap]
      apply (g2nnfProofTreeVariableFree_castTree _ _ _ _).mpr
      simp only [g2nnfProofTreeVariableFree]
      rw [G2nnfRuleCore.conclusion_varMap]
      exact g2nnfSequentVariableFree_varMap ρ hρ y _ _ hFree
  | onePremise rule hAdmit hPrem hSC sub ih =>
      simp only [G2nnfProofTree.varMap]
      apply (g2nnfProofTreeVariableFree_castTree _ _ _ _).mpr
      simp only [g2nnfProofTreeVariableFree_castTree,
        g2nnfProofTreeVariableFree]
      constructor
      · rw [G2nnfRuleCore.conclusion_varMap]
        exact g2nnfSequentVariableFree_varMap
          ρ hρ y _ _ hFree.1
      · simpa only [g2nnfProofTreeVariableFree_castTree] using
          ih hFree.2
  | twoPremise rule hAdmit hPrem hSC sub1 sub2 ih1 ih2 =>
      simp only [G2nnfProofTree.varMap]
      apply (g2nnfProofTreeVariableFree_castTree _ _ _ _).mpr
      simp only [g2nnfProofTreeVariableFree_castTree,
        g2nnfProofTreeVariableFree]
      refine ⟨?_, ?_, ?_⟩
      · rw [G2nnfRuleCore.conclusion_varMap]
        exact g2nnfSequentVariableFree_varMap
          ρ hρ y _ _ hFree.1
      · simpa only [g2nnfProofTreeVariableFree_castTree] using
          ih1 hFree.2.1
      · simpa only [g2nnfProofTreeVariableFree_castTree] using
          ih2 hFree.2.2

/-- Lemma 7.4.2 (companion def): Along an exact path to an exempt premise
occurrence, `y` is absent from every ancestor sequent and every off-path
sibling subtree.  Reaching `.root` exempts precisely that target occurrence
and its descendants. -/
@[blueprint "chap7__lemma_7_4_2"]
def g2nnfVariableOccursOnlyAlongPath {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] (y : Nat) :
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)} →
    {root : G2nnfProofTree hL Γroot Δroot} →
    {node : G2nnfProofTree hL Γnode Δnode} →
    RootToNodePath root node → Prop
  | _, _, _, _, _, _, .root _ => True
  | _, _, _, _, _, _,
      .onePremise rule hAdmit _ _ _ path =>
    g2nnfSequentVariableFree y
      (rule.conclusion).1
      (rule.conclusion).2 ∧
    g2nnfVariableOccursOnlyAlongPath y path
  | _, _, _, _, _, _,
      .leftPremise rule hAdmit _ _ _ sub2 path =>
    g2nnfSequentVariableFree y
      (rule.conclusion).1
      (rule.conclusion).2 ∧
    g2nnfProofTreeVariableFree (hL := hL) y sub2 ∧
    g2nnfVariableOccursOnlyAlongPath y path
  | _, _, _, _, _, _,
      .rightPremise rule hAdmit _ _ sub1 _ path =>
    g2nnfSequentVariableFree y
      (rule.conclusion).1
      (rule.conclusion).2 ∧
    g2nnfProofTreeVariableFree (hL := hL) y sub1 ∧
    g2nnfVariableOccursOnlyAlongPath y path

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Purity
/-- Casting only a path's root indices does not change the
outside-occurrence condition. -/
theorem g2nnfVariableOccursOnlyAlongPath_castRoot
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (y : Nat)
    {GammaRoot DeltaRoot GammaRoot' DeltaRoot'
      GammaNode DeltaNode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    {node : G2nnfProofTree hL GammaNode DeltaNode}
    (hGamma : GammaRoot = GammaRoot')
    (hDelta : DeltaRoot = DeltaRoot')
    (path : RootToNodePath root node) :
    g2nnfVariableOccursOnlyAlongPath y
        (path.castRoot hGamma hDelta) ↔
      g2nnfVariableOccursOnlyAlongPath y path := by
  subst GammaRoot'
  subst DeltaRoot'
  rfl

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Purity
/-- A zero-step index bridge at the exempt target does not change exact
outside-occurrence confinement. -/
theorem g2nnfVariableOccursOnlyAlongPath_castBridge_iff
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (y : Nat)
    {GammaRoot DeltaRoot GammaNode DeltaNode
      GammaNode' DeltaNode' : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    (node : G2nnfProofTree hL GammaNode DeltaNode)
    (hGamma : GammaNode = GammaNode')
    (hDelta : DeltaNode = DeltaNode')
    (path : RootToNodePath root (node.castTree hGamma hDelta)) :
    g2nnfVariableOccursOnlyAlongPath y
        (path.trans ((RootToNodePath.root node).castRoot hGamma hDelta)) ↔
      g2nnfVariableOccursOnlyAlongPath y path := by
  cases hGamma
  cases hDelta
  change RootToNodePath root node at path
  simpa only [G2nnfProofTree.castTree, RootToNodePath.castRoot,
    RootToNodePath.trans_root]



-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Purity
/-- Combined confinement normalizer for the parent and child index bridges
around one mapped immediate descent. -/
theorem g2nnfVariableOccursOnlyAlongPath_castedStep_iff
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (y : Nat)
    {GammaRoot DeltaRoot GammaCurrent DeltaCurrent
      GammaCurrent' DeltaCurrent' GammaSub DeltaSub
      GammaSub' DeltaSub' : LCS.Finset (FormulaN L)}
    {outer : G2nnfProofTree hL GammaRoot DeltaRoot}
    (current : G2nnfProofTree hL GammaCurrent DeltaCurrent)
    (sub : G2nnfProofTree hL GammaSub DeltaSub)
    (hCurrentGamma : GammaCurrent = GammaCurrent')
    (hCurrentDelta : DeltaCurrent = DeltaCurrent')
    (hSubGamma : GammaSub = GammaSub')
    (hSubDelta : DeltaSub = DeltaSub')
    (path : RootToNodePath outer
      (current.castTree hCurrentGamma hCurrentDelta))
    (step : RootToNodePath current
      (sub.castTree hSubGamma hSubDelta)) :
    g2nnfVariableOccursOnlyAlongPath y
        (path.trans
          ((step.trans
            ((RootToNodePath.root sub).castRoot hSubGamma hSubDelta)
            ).castRoot hCurrentGamma hCurrentDelta)) ↔
      g2nnfVariableOccursOnlyAlongPath y
        ((path.trans
          ((RootToNodePath.root current).castRoot
            hCurrentGamma hCurrentDelta)).trans step) := by
  rw [← RootToNodePath.castBridge_trans_castedStep
    current sub hCurrentGamma hCurrentDelta hSubGamma hSubDelta
    path step]
  exact g2nnfVariableOccursOnlyAlongPath_castBridge_iff
    y sub hSubGamma hSubDelta
      ((path.trans
        ((RootToNodePath.root current).castRoot
          hCurrentGamma hCurrentDelta)).trans step)

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Purity
/-- The exact outside-occurrence condition is preserved under
constructor-for-constructor path renaming. -/
theorem g2nnfVariableOccursOnlyAlongPath_varMap
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    (y : Nat)
    {GammaRoot DeltaRoot GammaNode DeltaNode :
      LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    {node : G2nnfProofTree hL GammaNode DeltaNode}
    (path : RootToNodePath root node)
    (hOnly : g2nnfVariableOccursOnlyAlongPath y path) :
    g2nnfVariableOccursOnlyAlongPath (ρ y) (path.varMap ρ hρ) := by
  induction path with
  | root T =>
      simp only [RootToNodePath.varMap, id_eq,
        g2nnfVariableOccursOnlyAlongPath]
  | onePremise rule hAdmit hPrem hSC sub path ih =>
      have hSeq :=
        g2nnfSequentVariableFree_varMap ρ hρ y
          (rule.conclusion).1
          (rule.conclusion).2 hOnly.1
      have hRest := ih hOnly.2
      have hSeq' :
          g2nnfSequentVariableFree (ρ y)
            ((rule.varMap ρ).conclusion).1
            ((rule.varMap ρ).conclusion).2 := by
        rw [G2nnfRuleCore.conclusion_varMap]
        exact hSeq
      simp only [RootToNodePath.varMap, id_eq]
      apply
        (g2nnfVariableOccursOnlyAlongPath_castRoot
          (ρ y) _ _ _).2
      refine ⟨hSeq', ?_⟩
      exact
        (g2nnfVariableOccursOnlyAlongPath_castRoot
          (ρ y) _ _ _).2 hRest
  | leftPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
      have hSeq :=
        g2nnfSequentVariableFree_varMap ρ hρ y
          (rule.conclusion).1
          (rule.conclusion).2 hOnly.1
      have hSibling :=
        g2nnfProofTreeVariableFree_varMap
          ρ hρ y sub2 hOnly.2.1
      have hRest := ih hOnly.2.2
      have hSeq' :
          g2nnfSequentVariableFree (ρ y)
            ((rule.varMap ρ).conclusion).1
            ((rule.varMap ρ).conclusion).2 := by
        rw [G2nnfRuleCore.conclusion_varMap]
        exact hSeq
      simp only [RootToNodePath.varMap, id_eq]
      apply
        (g2nnfVariableOccursOnlyAlongPath_castRoot
          (ρ y) _ _ _).2
      refine ⟨hSeq', ?_, ?_⟩
      · exact
          (g2nnfProofTreeVariableFree_castTree
            (ρ y) _ _ _).2 hSibling
      · exact
          (g2nnfVariableOccursOnlyAlongPath_castRoot
            (ρ y) _ _ _).2 hRest
  | rightPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
      have hSeq :=
        g2nnfSequentVariableFree_varMap ρ hρ y
          (rule.conclusion).1
          (rule.conclusion).2 hOnly.1
      have hSibling :=
        g2nnfProofTreeVariableFree_varMap
          ρ hρ y sub1 hOnly.2.1
      have hRest := ih hOnly.2.2
      have hSeq' :
          g2nnfSequentVariableFree (ρ y)
            ((rule.varMap ρ).conclusion).1
            ((rule.varMap ρ).conclusion).2 := by
        rw [G2nnfRuleCore.conclusion_varMap]
        exact hSeq
      simp only [RootToNodePath.varMap, id_eq]
      apply
        (g2nnfVariableOccursOnlyAlongPath_castRoot
          (ρ y) _ _ _).2
      refine ⟨hSeq', ?_, ?_⟩
      · exact
          (g2nnfProofTreeVariableFree_castTree
            (ρ y) _ _ _).2 hSibling
      · exact
          (g2nnfVariableOccursOnlyAlongPath_castRoot
            (ρ y) _ _ _).2 hRest

/-- Lemma 7.4.2 (companion def): Predicate asserting that variable `y` only
occurs inside one exact subtree occurrence of the ambient G2nnf proof tree.
The `NodeOccurrence` path identifies the premise position of the
eigenvariable-introducing inference.  Formula occurrences in ancestor
sequents and off-path sibling subtrees must be `y`-free; only the target
occurrence and its descendants are exempt.  No formula, sequent, or subtree
equality is used to identify occurrences. -/
@[blueprint "chap7__lemma_7_4_2"]
def g2nnfEigenvariableOccursOnlyInSubtree {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot ΓSub ΔSub : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot}
    (y : Nat) (occurrence : NodeOccurrence T ΓSub ΔSub) : Prop :=
  g2nnfVariableOccursOnlyAlongPath y occurrence.path

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Purity
/-- Exact eigenvariable confinement is preserved by occurrence transport. -/
theorem g2nnfEigenvariableOccursOnlyInSubtree_varMap
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    {GammaRoot DeltaRoot GammaSub DeltaSub :
      LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL GammaRoot DeltaRoot}
    (y : Nat) (occurrence : NodeOccurrence T GammaSub DeltaSub)
    (hOnly : g2nnfEigenvariableOccursOnlyInSubtree y occurrence) :
    g2nnfEigenvariableOccursOnlyInSubtree (ρ y)
      (occurrence.varMap ρ hρ) :=
  g2nnfVariableOccursOnlyAlongPath_varMap
    ρ hρ y occurrence.path hOnly

end LCS.Herbrand.NNFHauptsatz.Theorem
end

