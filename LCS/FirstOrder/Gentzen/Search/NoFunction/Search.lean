import LCS.Item
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Gentzen.Search.NoFunction.Initialization
import LCS.FirstOrder.Gentzen.Search.NoFunction.Growth
import LCS.FirstOrder.Gentzen.Search.NoFunction.LeafInvariant
import Attach
import LCS.FirstOrder.Gentzen.Search.NoFunction.Search.ProofsStamp

section
namespace LCS.FirstOrder.Gentzen.Search.NoFunction
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka

/-- Definition 5.4.9 (companion, bundled tree-level grow output):
    The bundled output of `growLeftTreeInv` / `growRightTreeInv` —
    tree + state + preservation witnesses needed to compose into
    further iterations.

    Parameterized by the STARTING `availNext` (`availIn`) so the
    monotonicity witness can be propagated by the caller. -/
@[blueprint "chap5__definition_5_4_9"]
structure GrowOut {L : Language} (supply : TermStream L) {s : Sequent L} (seq : Sequent L)
    (bound : Nat) (availIn : Nat) where
  tree : SearchTree s
  state : SearchState L supply
  state_inv : SearchState.Inv seq bound state
  avail_mono : availIn ≤ state.availNext
  tree_leaf_inv : TreeLeafInv supply tree seq state.availNext

/-- Definition 5.4.9 (companion): Extend selected nonaxiom leaves using
    one fixed input state, then activate its head eigenvariable once.
    No eligible leaf means that both tree and state are unchanged. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def growEigenTree {L : Language} {supply : TermStream L} {seq : Sequent L} {bound : Nat}
    (st : SearchState L supply) (hInv : SearchState.Inv seq bound st)
    (selected : Sequent L → Prop)
    (extend : (leaf : Sequent L) → BranchRecords L → selected leaf →
      LeafFVBelow supply leaf st.availNext → LeafBVSubsetSeq leaf seq → SearchTree leaf)
    (hExtend : ∀ leaf records hSel hFV hSub,
      TreeLeafInv supply (extend leaf records hSel hFV hSub) seq (st.availNext + 1))
    {s : Sequent L} (t : SearchTree s) (hTLI : TreeLeafInv supply t seq st.availNext) :
    GrowOut supply (L := L) (s := s) seq bound st.availNext := by
  classical
  by_cases hUsed : ∃ leaf ∈ t.toDeductionTree.leaves, ¬ isAxiom leaf ∧ selected leaf
  · let rec walk : {s : Sequent L} → (t : SearchTree s) →
        TreeLeafInv supply t seq st.availNext →
        { out : SearchTree s // TreeLeafInv supply out seq (st.availNext + 1) }
      | _, .leaf leaf records, hTLI => by
          by_cases hAx : isAxiom leaf
          · exact ⟨.leaf leaf records, TreeLeafInv_mono hTLI (Nat.le_succ _)⟩
          · by_cases hSel : selected leaf
            · have hIn : leaf ∈ (GDeductionTreeExt.leaf leaf).leaves := by simp
              obtain ⟨hFV, hSub⟩ := hTLI leaf hIn
              exact ⟨extend leaf records hSel hFV hSub, hExtend leaf records hSel hFV hSub⟩
            · exact ⟨.leaf leaf records, TreeLeafInv_mono hTLI (Nat.le_succ _)⟩
      | _, .onePremise rule child, hTLI => by
          have hChild : TreeLeafInv supply child seq st.availNext :=
            (TreeLeafInv_onePremise rule child).mp hTLI
          let out := walk child hChild
          exact ⟨.onePremise rule out.val,
            (TreeLeafInv_onePremise rule out.val).mpr out.property⟩
      | _, .twoPremise rule left right, hTLI => by
          obtain ⟨hLeft, hRight⟩ := (TreeLeafInv_twoPremise rule left right).mp hTLI
          let outLeft := walk left hLeft
          let outRight := walk right hRight
          exact ⟨.twoPremise rule outLeft.val outRight.val,
            (TreeLeafInv_twoPremise rule outLeft.val outRight.val).mpr
              ⟨outLeft.property, outRight.property⟩⟩
    let out := walk t hTLI
    exact { tree := out.val
            state := (st.tailAVAIL0).appendTERM1 (Term.var (supply.varAt st.availNext (hInv.available_vars st.availNext)))
            state_inv := SearchState.Inv.tailAppend hInv
            avail_mono := Nat.le_succ _
            tree_leaf_inv := out.property }
  · exact { tree := t, state := st, state_inv := hInv
            avail_mono := Nat.le_refl _, tree_leaf_inv := hTLI }

/-- Definition 5.4.9 (companion, tree-level grow-left): Apply
    `growLeftAtLeaf` to every non-axiom leaf of a tree `t`. At each
    leaf visit, per-leaf invariants are extracted from the tree-level
    `TreeLeafInv`. Axiom leaves are preserved unchanged. State is
    threaded through the walk in leaves-order, matching the §5.4.9
    textbook pseudocode ("extend every nonaxiom leaf of S").

    Returns a bundled `GrowOut` carrying: the new tree, the threaded
    state, `Inv` preservation, `availNext` monotonicity, and
    `TreeLeafInv` preservation at the new `availNext`. The last
    invariant relies on `TreeLeafInv_grow_at_leaf` (proved via case
    analysis over 8 formula constructors using `formulaFVN_formulaSubstN`
    and `formulaBVN_formulaSubstN_subset`).

    For an existential principal formula, all selected leaves use the
    same input head of AVAIL₀, and the global state is updated once when
    at least one nonaxiom leaf is extended. Other connectives thread
    the global state through the recursive walk. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def growLeftTreeInv {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq)
    (A : FormulaN L)
    {s : Sequent L} (t : SearchTree s) (st : SearchState L supply)
    (hInv : SearchState.Inv seq bound st)
    (hTLI : TreeLeafInv supply t seq st.availNext) :
    GrowOut supply (L := L) (s := s) seq bound st.availNext := by
  classical
  match A with
  | .ex x body =>
      exact growEigenTree st hInv
        (fun leaf => FormulaN.ex x body ∈ leaf.antecedent)
        (fun leaf records hSel hFV hSub =>
          (growLeftAtLeaf hNoEq hNoFunc hCNFB (FormulaN.ex x body) leaf
            st records hInv hFV
            (LeafBVBelow_of_SubsetSeq hSub hInv.bound_above_seq) hSub).1)
        (by
          intro leaf records hSel hFV hSub
          have h := TreeLeafInv_grow_at_leaf hNoEq hNoFunc hCNFB
            (FormulaN.ex x body) leaf st records hInv hFV
            (LeafBVBelow_of_SubsetSeq hSub hInv.bound_above_seq) hSub
          simpa only [growLeftAtLeaf, dif_pos hSel,
            SearchState.appendTERM1, SearchState.tailAVAIL0] using h)
        t hTLI
  | _ =>
      let rec walk :
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
            let result := growLeftAtLeaf hNoEq hNoFunc hCNFB A l st records hInv hFV hBV hSub
            exact
              { tree := result.1
                state := result.2
                state_inv := growLeftAtLeaf_preserves_Inv hNoEq
                  hNoFunc hCNFB A l st records hInv hFV hBV hSub
                avail_mono := growLeftAtLeaf_availNext_mono hNoEq
                  hNoFunc hCNFB A l st records hInv hFV hBV hSub
                tree_leaf_inv := TreeLeafInv_grow_at_leaf hNoEq
                  hNoFunc hCNFB A l st records hInv hFV hBV hSub }
      | _, .onePremise rule t, st, hInv, hTLI => by
          have hTLI' : TreeLeafInv supply t seq st.availNext := fun leaf hleaf =>
            hTLI leaf (by simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves]; exact hleaf)
          let out := walk t st hInv hTLI'
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
          let out1 := walk t1 st hInv hTLI1
          have hTLI2' : TreeLeafInv supply t2 seq out1.state.availNext :=
            TreeLeafInv_mono hTLI2 out1.avail_mono
          let out2 := walk t2 out1.state
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
      exact walk t st hInv hTLI

/-- Definition 5.4.9 (companion, tree-level grow-right): Mirror of
    `growLeftTreeInv` for right rules. A universal principal formula uses
    one shared eigenvariable, activated once if a nonaxiom leaf is extended. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def growRightTreeInv {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq)
    (B : FormulaN L)
    {s : Sequent L} (t : SearchTree s) (st : SearchState L supply)
    (hInv : SearchState.Inv seq bound st)
    (hTLI : TreeLeafInv supply t seq st.availNext) :
    GrowOut supply (L := L) (s := s) seq bound st.availNext := by
  classical
  match B with
  | .all x body =>
      exact growEigenTree st hInv
        (fun leaf => FormulaN.all x body ∈ leaf.succedent)
        (fun leaf records hSel hFV hSub =>
          (growRightAtLeaf hNoEq hNoFunc hCNFB (FormulaN.all x body) leaf
            st records hInv hFV
            (LeafBVBelow_of_SubsetSeq hSub hInv.bound_above_seq) hSub).1)
        (by
          intro leaf records hSel hFV hSub
          have h := TreeLeafInv_grow_right_at_leaf hNoEq hNoFunc hCNFB
            (FormulaN.all x body) leaf st records hInv hFV
            (LeafBVBelow_of_SubsetSeq hSub hInv.bound_above_seq) hSub
          simpa only [growRightAtLeaf, dif_pos hSel,
            SearchState.appendTERM1, SearchState.tailAVAIL0] using h)
        t hTLI
  | _ =>
      let rec walk :
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
            let result := growRightAtLeaf hNoEq hNoFunc hCNFB B l st records hInv hFV hBV hSub
            exact
              { tree := result.1
                state := result.2
                state_inv := growRightAtLeaf_preserves_Inv hNoEq
                  hNoFunc hCNFB B l st records hInv hFV hBV hSub
                avail_mono := growRightAtLeaf_availNext_mono hNoEq
                  hNoFunc hCNFB B l st records hInv hFV hBV hSub
                tree_leaf_inv := TreeLeafInv_grow_right_at_leaf hNoEq
                  hNoFunc hCNFB B l st records hInv hFV hBV hSub }
      | _, .onePremise rule t, st, hInv, hTLI => by
          have hTLI' : TreeLeafInv supply t seq st.availNext := fun leaf hleaf =>
            hTLI leaf (by simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves]; exact hleaf)
          let out := walk t st hInv hTLI'
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
          let out1 := walk t1 st hInv hTLI1
          have hTLI2' : TreeLeafInv supply t2 seq out1.state.availNext :=
            TreeLeafInv_mono hTLI2 out1.avail_mono
          let out2 := walk t2 out1.state
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
      exact walk t st hInv hTLI

-- ===================================================================
-- expand: per-leaf grow-left / grow-right (§5.4.9 lines 111-131)
-- ===================================================================

/-- Helper: fold `growLeftTreeInv` over a list of principal formulas,
    threading state and tree across iterations. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def foldGrowLeft {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq) :
    List (FormulaN L) →
    {s : Sequent L} → (t : SearchTree s) → (st : SearchState L supply) →
    (hInv : SearchState.Inv seq bound st) →
    (hTLI : TreeLeafInv supply t seq st.availNext) →
    GrowOut supply (L := L) (s := s) seq bound st.availNext
  | [], _, t, st, hInv, hTLI =>
      { tree := t, state := st, state_inv := hInv
        avail_mono := Nat.le_refl _, tree_leaf_inv := hTLI }
  | A :: As, _, t, st, hInv, hTLI => by
      let out1 := growLeftTreeInv hNoEq hNoFunc hCNFB A t st hInv hTLI
      have hTLI2 : TreeLeafInv supply out1.tree seq out1.state.availNext :=
        out1.tree_leaf_inv
      let out2 := foldGrowLeft hNoEq hNoFunc hCNFB As out1.tree out1.state
                    out1.state_inv hTLI2
      exact
        { tree := out2.tree, state := out2.state
          state_inv := out2.state_inv
          avail_mono := Nat.le_trans out1.avail_mono out2.avail_mono
          tree_leaf_inv := out2.tree_leaf_inv }

/-- Mirror for grow-right. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def foldGrowRight {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq) :
    List (FormulaN L) →
    {s : Sequent L} → (t : SearchTree s) → (st : SearchState L supply) →
    (hInv : SearchState.Inv seq bound st) →
    (hTLI : TreeLeafInv supply t seq st.availNext) →
    GrowOut supply (L := L) (s := s) seq bound st.availNext
  | [], _, t, st, hInv, hTLI =>
      { tree := t, state := st, state_inv := hInv
        avail_mono := Nat.le_refl _, tree_leaf_inv := hTLI }
  | B :: Bs, _, t, st, hInv, hTLI => by
      let out1 := growRightTreeInv hNoEq hNoFunc hCNFB B t st hInv hTLI
      have hTLI2 : TreeLeafInv supply out1.tree seq out1.state.availNext :=
        out1.tree_leaf_inv
      let out2 := foldGrowRight hNoEq hNoFunc hCNFB Bs out1.tree out1.state
                    out1.state_inv hTLI2
      exact
        { tree := out2.tree, state := out2.state
          state_inv := out2.state_inv
          avail_mono := Nat.le_trans out1.avail_mono out2.avail_mono
          tree_leaf_inv := out2.tree_leaf_inv }

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



/-- Definition 5.4.9 (companion, `searchRound`): one iteration of the
    outer while-loop. Per textbook §5.4.9 lines 87-98:

      TERM₁ := TERM₀; T₀ := T;
      for each leaf node of T₀ (in lexicographic order) do
        if not finished(node) then expand(node, T) endif
      endfor;
      TERM₀ := TERM₁

    Implementation: run `expandTree` (which walks the tree applying
    `expandAtLeaf` at each non-axiom leaf), then call `commitRound` to
    commit TERM₀ ← TERM₁ and each leaf's FORM₀ ← FORM₁. Each leaf
    retains its own records while global state is threaded left to right. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def searchRound {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq)
    {s : Sequent L} (t : SearchTree s) (st : SearchState L supply)
    (hInv : SearchState.Inv seq bound st)
    (hTLI : TreeLeafInv supply t seq st.availNext) :
    GrowOut supply (L := L) (s := s) seq bound st.availNext := by
  let out := expandTree hNoEq hNoFunc hCNFB t st hInv hTLI
  let committed := out.state.commitRound out.tree
  let stFinal := committed.2
  have hInvFinal : SearchState.Inv seq bound stFinal :=
    SearchState.commitRound_preserves_Inv out.state_inv out.tree
  exact
    { tree := committed.1, state := stFinal
      state_inv := hInvFinal
      avail_mono := out.avail_mono
      tree_leaf_inv := by
        simpa only [TreeLeafInv, committed, stFinal, SearchState.commitRound,
          SearchTree.toDeductionTree_commitRound]
          using out.tree_leaf_inv }



/-- Definition 5.4.9 (companion): Iterate `searchRound` exactly `k` times.
    The recursion tests only the round budget, not finishedness. Finished
    trees are fixed points of `searchRound` on the underlying deduction
    tree; leaf records are still committed at round boundaries. Each
    result is a finite approximant of the textbook search. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def searchAux {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq) :
    Nat → {s : Sequent L} → (t : SearchTree s) → (st : SearchState L supply) →
    (hInv : SearchState.Inv seq bound st) →
    (hTLI : TreeLeafInv supply t seq st.availNext) →
    GrowOut supply (L := L) (s := s) seq bound st.availNext
  | 0, _, t, st, hInv, hTLI =>
      { tree := t, state := st, state_inv := hInv
        avail_mono := Nat.le_refl _, tree_leaf_inv := hTLI }
  | k + 1, _, t, st, hInv, hTLI => by
      let out := searchRound hNoEq hNoFunc hCNFB t st hInv hTLI
      have hTLI' : TreeLeafInv supply out.tree seq out.state.availNext :=
        out.tree_leaf_inv
      let outRec := searchAux hNoEq hNoFunc hCNFB k out.tree out.state
                      out.state_inv hTLI'
      exact
        { tree := outRec.tree, state := outRec.state
          state_inv := outRec.state_inv
          avail_mono := Nat.le_trans out.avail_mono outRec.avail_mono
          tree_leaf_inv := outRec.tree_leaf_inv }



-- ===================================================================
-- search: the main procedure (Definition 5.4.9)
-- ===================================================================

/-- Definition 5.4.9: The search procedure for a language without equality,
    composed from `SearchState.init` and `searchAux` iterating `searchRound`.
    The initial leaf has empty FORM₀/FORM₁ entries for every global term;
    the result retains the records of each branch.

    Textbook §5.4.9 (full procedure):
      procedure search(Γ → Δ : sequent; var T : tree);
      begin
        let T be the one-node tree labeled with Γ → Δ;
        let TERM₀, AVAIL₀ be initialized per §5.4.7 (initial TERM₀
          and countably-infinite AVAIL₀ stream);
        while not all leaves of T are finished do
          TERM₁ := TERM₀; T₀ := T;
          for each leaf of T₀ (lexicographic order) do
            if not finished(node) then expand(node, T) endif
          endfor;
          TERM₀ := TERM₁
        endwhile;
        if all leaves closed then
          write("T is a proof of Γ → Δ")
        else
          write("Γ → Δ is falsifiable")
        endif
      end

    Lean formalization takes a step bound `k : Nat` (since Thm 5.4.1
    allows for either finite or infinite trees; the step-indexed
    version produces a valid prefix for both). Callers supply the
    §5.4.7 standing assumptions `hNoEq`, `hNoFunc`, and `hCNFB`, together
    with an admissible initialization. `Init.default seq` provides the
    computed canonical choice. -/
@[blueprint "chap5__definition_5_4_9" (main := true)]
noncomputable def search {L : Language} (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    (seq : Sequent L) (hCNFB : crossNoFreeBound seq)
    (initial : Init seq)
    (k : Nat) :
    SearchTree seq × SearchState L initial.avail0 :=
  let st₀ := SearchState.init initial
  let forms : List (List (FormulaN L)) := List.replicate st₀.TERM0.length []
  let records : BranchRecords L := { form0 := forms, form1 := forms }
  let t₀ := SearchTree.leaf seq records
  let hInv₀ := SearchState.init_preserves_Inv initial
  let hTLI₀ : TreeLeafInv initial.avail0 t₀ seq st₀.availNext :=
    TreeLeafInv_init seq st₀.availNext records
      (by intro F hF i hi n _; exact SearchState.init_available_fresh initial F hF i hi n)
  let out := searchAux hNoEq hNoFunc hCNFB (bound := sequentVarBound seq) k t₀ st₀ hInv₀ hTLI₀
  (out.tree, out.state)



-- ===================================================================
-- Theorem 5.4.1 (search-mentioning restatement — §5.4.7 verbatim)
-- ===================================================================

/-- Theorem 5.4.1: For every admissible initialization of an input
    sequent in which no variable occurs both free and bound, over a
    language without function symbols or equality:

    (i) If the sequent is valid, some finite search round is a closed
        proof tree.
    (ii) If the sequent is falsifiable, either some finite search round
         is finished and nonclosed and a finite structure falsifies the
         sequent, or no round is finished and a countably infinite
         structure falsifies the sequent.

    Finishedness uses each leaf's own formula-use records. Proof and
    closedness predicates use the underlying extended G deduction tree.
    Countable infinitude means `isCountableDomain M ∧ ¬ isFiniteDomain M`. -/
@[attach_debt, blueprint "chap5__theorem_5_4_1" (main := true)]
theorem search_halts_with_proof_or_falsifying_model {L : Language}
    (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    (seq : Sequent L) (hCNFB : crossNoFreeBound seq)
    (initial : Init seq) :
    -- Part (i): valid ⇒ search halts with closed proof tree
    (sequentValid seq →
      ∃ k : Nat,
        (search hNoEq hNoFunc seq hCNFB initial k).1.toDeductionTree.isProof) ∧
    -- Part (ii): falsifiable ⇒ finite CE or infinite tree + falsifying model
    (¬ sequentValid seq →
      -- (ii.a) finite counter-example tree with finite-domain falsifying model
      (∃ k : Nat,
        isFinishedTree hNoEq
          (search hNoEq hNoFunc seq hCNFB initial k).1
          (search hNoEq hNoFunc seq hCNFB initial k).2 ∧
        ¬ (search hNoEq hNoFunc seq hCNFB initial k).1.toDeductionTree.isClosed ∧
        ∃ (M : Structure L) (s : Assignment M),
          isFiniteDomain M ∧
          (∀ A ∈ seq.antecedent, formulaEvalN M A s) ∧
          (∀ B ∈ seq.succedent, ¬ formulaEvalN M B s)) ∨
      -- (ii.b) infinite tree with countably infinite falsifying model
      ((∀ k : Nat,
        ¬ isFinishedTree hNoEq
            (search hNoEq hNoFunc seq hCNFB initial k).1
            (search hNoEq hNoFunc seq hCNFB initial k).2) ∧
        ∃ (M : Structure L) (s : Assignment M),
          (isCountableDomain M ∧ ¬ isFiniteDomain M) ∧
          (∀ A ∈ seq.antecedent, formulaEvalN M A s) ∧
          (∀ B ∈ seq.succedent, ¬ formulaEvalN M B s))) 

/-- Theorem 5.4.1 (companion, Corollary — Gödel completeness):
    If a sequent in which no variable occurs both free and bound (over
    a first-order language without function symbols or equality) is
    valid, then it is G-provable (under §5.4.8 standing assumption,
    G-provability means `sequentProvableExt`).

    Textbook §5.4.7 line 384: "As a corollary, we obtain a version of
    Gödel's completeness theorem for first-order languages without
    function symbols or equality. Corollary: If a sequent in which no
    variable occurs both free and bound (over a first-order language
    without function symbols or equality) is valid then it is
    G-provable."

    Choose `Init.default seq` and apply part (i) of
    `search_halts_with_proof_or_falsifying_model`. The resulting closed
    deduction tree yields a `GProofTreeExt seq`, witnessing provability. -/
@[blueprint "chap5__theorem_5_4_1"]
theorem search_goedel_corollary {L : Language}
    (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    (seq : Sequent L) (hCNFB : crossNoFreeBound seq)
    (hValid : sequentValid seq) :
    sequentProvableExt seq 

end LCS.FirstOrder.Gentzen.Search.NoFunction
end

