import LCS.Herbrand.NNFHauptsatz.Theorem.Paths

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

helper /-- The canonical copy's complete support is exactly the renamed source
support. -/
theorem G2nnfProofTree.variableSupport_freshAlphaCopy
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : _root_.LCS.Herbrand.NNFHauptsatz.G2nnfProofTree hL Gamma Delta)
    (avoid : LCS.Finset Nat) :
    (T.freshAlphaCopy avoid).variableSupport =
      LCS.Finset.image (T.freshAlphaRenaming avoid) T.variableSupport := by
  rw [freshAlphaCopy, variableSupport_castTree, variableSupport_varMap]

helper /-- Source/copy support overlap is confined to variables of the fixed root.
Total disjointness is intentionally not claimed. -/
theorem G2nnfProofTree.variableSupport_overlap_freshAlphaCopy_subset_root
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : _root_.LCS.Herbrand.NNFHauptsatz.G2nnfProofTree hL Gamma Delta)
    (avoid : LCS.Finset Nat) (v : Nat)
    (hSource : v ∈ T.variableSupport)
    (hCopy : v ∈ (T.freshAlphaCopy avoid).variableSupport) :
    v ∈ T.rootVariableSupport := by
  rw [variableSupport_freshAlphaCopy, LCS.Finset.mem_image] at hCopy
  rcases hCopy with ⟨x, hx, hMap⟩
  by_cases hRoot : x ∈ T.rootVariableSupport
  · rw [T.freshAlphaRenaming_fixed_root avoid x hRoot] at hMap
    simpa [hMap] using hRoot
  · exfalso
    apply T.freshAlphaRenaming_off_root_not_mem_variableSupport
      avoid x hRoot
    rw [hMap]
    exact hSource

helper /-- Copy/avoidance overlap is likewise possible only through fixed root
variables. -/
theorem G2nnfProofTree.avoid_overlap_freshAlphaCopy_subset_root
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : _root_.LCS.Herbrand.NNFHauptsatz.G2nnfProofTree hL Gamma Delta)
    (avoid : LCS.Finset Nat) (v : Nat)
    (hAvoid : v ∈ avoid)
    (hCopy : v ∈ (T.freshAlphaCopy avoid).variableSupport) :
    v ∈ T.rootVariableSupport := by
  rw [variableSupport_freshAlphaCopy, LCS.Finset.mem_image] at hCopy
  rcases hCopy with ⟨x, hx, hMap⟩
  by_cases hRoot : x ∈ T.rootVariableSupport
  · rw [T.freshAlphaRenaming_fixed_root avoid x hRoot] at hMap
    simpa [hMap] using hRoot
  · exfalso
    apply T.freshAlphaRenaming_off_root_not_mem_avoid avoid x hRoot
    rw [hMap]
    exact hAvoid

helper /-- Canonical alpha copying preserves cut-freedom exactly. -/
theorem G2nnfProofTree.isCutFree_freshAlphaCopy_iff
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : _root_.LCS.Herbrand.NNFHauptsatz.G2nnfProofTree hL Gamma Delta)
    (avoid : LCS.Finset Nat) :
    (T.freshAlphaCopy avoid).isCutFree (hL := hL) ↔ T.isCutFree (hL := hL) := by
  rw [freshAlphaCopy, isCutFree_castTree, isCutFree_varMap_iff]

helper /-- Canonical alpha copying preserves structural depth exactly. -/
theorem G2nnfProofTree.depth_freshAlphaCopy
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : _root_.LCS.Herbrand.NNFHauptsatz.G2nnfProofTree hL Gamma Delta)
    (avoid : LCS.Finset Nat) :
    (T.freshAlphaCopy avoid).depth = T.depth := by
  rw [freshAlphaCopy, depth_castTree, depth_varMap]

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















helper /-- A terminal zero-step bridge can be removed below an already composed
path without exposing the dependent indices to associativity rewriting. -/
theorem Theorem.g2nnfVariableOccursOnlyAlongPath_nestedCastBridge_iff
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (y : Nat)
    {GammaRoot DeltaRoot GammaMid DeltaMid GammaNode DeltaNode
      GammaNode' DeltaNode' : LCS.Finset (FormulaN L)}
    {root : _root_.LCS.Herbrand.NNFHauptsatz.G2nnfProofTree hL GammaRoot DeltaRoot}
    {mid : _root_.LCS.Herbrand.NNFHauptsatz.G2nnfProofTree hL GammaMid DeltaMid}
    (node : _root_.LCS.Herbrand.NNFHauptsatz.G2nnfProofTree hL GammaNode DeltaNode)
    (hGamma : GammaNode = GammaNode')
    (hDelta : DeltaNode = DeltaNode')
    (first : RootToNodePath root mid)
    (second : RootToNodePath mid
      (node.castTree hGamma hDelta)) :
    g2nnfVariableOccursOnlyAlongPath y
        (first.trans
          (second.trans
            ((RootToNodePath.root node).castRoot hGamma hDelta))) ↔
      g2nnfVariableOccursOnlyAlongPath y
        (first.trans second) := by
  rw [← RootToNodePath.trans_assoc]
  exact g2nnfVariableOccursOnlyAlongPath_castBridge_iff
    y node hGamma hDelta (first.trans second)







end LCS.Herbrand.NNFHauptsatz.Theorem

end
