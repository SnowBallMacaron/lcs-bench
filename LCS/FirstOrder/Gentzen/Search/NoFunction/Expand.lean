import LCS.Item
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Gentzen.Search.NoFunction.GrowLeft
import LCS.FirstOrder.Gentzen.Search.NoFunction.GrowRight
import Attach
import LCS.FirstOrder.Gentzen.Search.NoFunction.Expand.ProofsStamp

/-! # Procedure expand (Definition 5.4.9)

Expansion of one leaf by grow-left on its antecedent and grow-right on its
succedent, and expansion of every unfinished leaf of a tree in one round.
Source: Logic for Computer Science, Gallier 2015
-/

section
namespace LCS.FirstOrder.Gentzen.Search.NoFunction
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka

/-- Definition 5.4.9 (companion, `expand` at a single leaf, bundled):
    Textbook §5.4.9 lines 111-131: textbook `expand(node, T)` at a
    single leaf — applies grow-left to each antecedent formula, then
    grow-right to each succedent formula, all using the LEAF's own
    label (not the root's).

    Returns a `GrowOut` bundle carrying the expanded subtree +
    preserved `Inv` + monotonic `availNext` + preserved `TreeLeafInv`.
    The initial leaf carries its own branch records; every child produced
    by the folds inherits those records and its branch's updates. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def expandAtLeaf {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq) (leaf : Sequent L)
    (st : SearchState L supply) (records : BranchRecords L) (hInv : SearchState.Inv seq bound st)
    (hLeafFV : LeafFVBelow supply leaf st.availNext)
    (hLeafBV : LeafBVBelow leaf bound)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq) :
    GrowOut supply (L := L) (s := leaf) seq bound st.availNext := by
  let t₀ : SearchTree leaf := SearchTree.leaf leaf records
  let hTLI₀ : TreeLeafInv supply t₀ seq st.availNext := by
    intro l hl
    have hl' : l = leaf := by
      have : l ∈ (GDeductionTreeExt.leaf leaf).leaves := hl
      rw [GDeductionTreeExt.leaves_leaf] at this
      exact List.mem_singleton.mp this
    refine ⟨?_, ?_⟩
    · rw [hl']; exact hLeafFV
    · rw [hl']; exact hLeafBVSub
  let leftOut := foldGrowLeft hNoEq hNoFunc hCNFB leaf.antecedent t₀ st hInv hTLI₀
  let rightOut := foldGrowRight hNoEq hNoFunc hCNFB leaf.succedent
                    leftOut.tree leftOut.state
                    leftOut.state_inv leftOut.tree_leaf_inv
  exact
    { tree := rightOut.tree, state := rightOut.state
      state_inv := rightOut.state_inv
      avail_mono := Nat.le_trans leftOut.avail_mono rightOut.avail_mono
      tree_leaf_inv := rightOut.tree_leaf_inv }

-- ===================================================================
-- expandTree: apply expandAtLeaf to every non-axiom leaf
-- ===================================================================

/-- Definition 5.4.9 (companion, tree-level expand): Apply `expandAtLeaf`
    at every non-axiom leaf of the tree, walking structurally. This
    implements §5.4.9 lines 90-94:
      for each leaf node of T₀ (in lexicographic order of tree addresses) do
        if not finished(node) then expand(node, T) endif
      endfor

    The "not finished" guard is absorbed into `expandAtLeaf`'s per-formula
    folds (atomic formulas no-op; saturated ∀/∃ no-op). The walker's
    axiom-skip handles the axiom case of `finished`. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def expandTree {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq) :
    {s : Sequent L} → (t : SearchTree s) → (st : SearchState L supply) →
    (hInv : SearchState.Inv seq bound st) →
    (hTLI : TreeLeafInv supply t seq st.availNext) →
    GrowOut supply (L := L) (s := s) seq bound st.availNext
  | _, .leaf l records, st, hInv, hTLI => by
      classical
      by_cases hAx : isAxiom l
      · exact
          { tree := SearchTree.leaf l records
            state := st
            state_inv := hInv
            avail_mono := Nat.le_refl _
            tree_leaf_inv := hTLI }
      · have hLeafIn : l ∈ (GDeductionTreeExt.leaf l).leaves := by
          simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves]
        obtain ⟨hFV, hSub⟩ := hTLI l hLeafIn
        let hBV : LeafBVBelow l bound :=
          LeafBVBelow_of_SubsetSeq hSub hInv.bound_above_seq
        exact expandAtLeaf hNoEq hNoFunc hCNFB l st records hInv hFV hBV hSub
  | _, .onePremise rule t, st, hInv, hTLI => by
      have hTLI' : TreeLeafInv supply t seq st.availNext := fun leaf hleaf =>
        hTLI leaf (by simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves]; exact hleaf)
      let out := expandTree hNoEq hNoFunc hCNFB t st hInv hTLI'
      exact
        { tree := SearchTree.onePremise rule out.tree
          state := out.state
          state_inv := out.state_inv
          avail_mono := out.avail_mono
          tree_leaf_inv := by
            intro leaf hleaf
            apply out.tree_leaf_inv leaf
            simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves] at hleaf
            exact hleaf }
  | _, .twoPremise rule t1 t2, st, hInv, hTLI => by
      have hTLI1 : TreeLeafInv supply t1 seq st.availNext := fun leaf hleaf =>
        hTLI leaf (by simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves]; left; exact hleaf)
      have hTLI2 : TreeLeafInv supply t2 seq st.availNext := fun leaf hleaf =>
        hTLI leaf (by simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves]; right; exact hleaf)
      let out1 := expandTree hNoEq hNoFunc hCNFB t1 st hInv hTLI1
      have hTLI2' : TreeLeafInv supply t2 seq out1.state.availNext :=
        TreeLeafInv_mono hTLI2 out1.avail_mono
      let out2 := expandTree hNoEq hNoFunc hCNFB t2 out1.state
                    out1.state_inv hTLI2'
      exact
        { tree := SearchTree.twoPremise rule out1.tree out2.tree
          state := out2.state
          state_inv := out2.state_inv
          avail_mono := Nat.le_trans out1.avail_mono out2.avail_mono
          tree_leaf_inv := by
            intro leaf hleaf
            simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves] at hleaf
            rcases hleaf with h1 | h2
            · have h := out1.tree_leaf_inv leaf h1
              exact ⟨LeafFVBelow_mono h.1 out2.avail_mono, h.2⟩
            · exact out2.tree_leaf_inv leaf h2 }

end LCS.FirstOrder.Gentzen.Search.NoFunction
end
