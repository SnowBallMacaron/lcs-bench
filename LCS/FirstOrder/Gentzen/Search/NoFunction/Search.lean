import LCS.Item
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Gentzen.Search.NoFunction.Expand
import Attach
import LCS.FirstOrder.Gentzen.Search.NoFunction.Search.ProofsStamp

/-! # Procedure search and Theorem 5.4.1 (Section 5.4.7)

The search rounds and procedure search of Definition 5.4.9, renaming apart of the
input sequent (Lemma 5.3.4), Theorem 5.4.1 and its corollary (completeness for
languages without function symbols and without equality).
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

end LCS.FirstOrder.Gentzen.Search.NoFunction

namespace LCS.FirstOrder.Gentzen.Search.NoFunction
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.Hintikka

/-- Definition 5.4.9 (companion): A particular leaf occurrence, addressed
    from the root. Unary children and left children use `false`; right
    children use `true`. The empty address denotes the root leaf. -/
@[blueprint "chap5__definition_5_4_9"]
inductive SearchTree.LeafAt {L : Language} (leaf : Sequent L) (records : BranchRecords L) :
    {s : Sequent L} → SearchTree s → List Bool → Prop where
  | here : LeafAt leaf records (.leaf leaf records) []
  | one {prem conc : Sequent L} (rule : GentzenStep1Ext prem conc)
      {t : SearchTree prem} {p : List Bool} (h : LeafAt leaf records t p) :
      LeafAt leaf records (.onePremise rule t) (false :: p)
  | left {p1 p2 conc : Sequent L} (rule : GentzenStep2Ext p1 p2 conc)
      {t1 : SearchTree p1} (t2 : SearchTree p2) {p : List Bool}
      (h : LeafAt leaf records t1 p) :
      LeafAt leaf records (.twoPremise rule t1 t2) (false :: p)
  | right {p1 p2 conc : Sequent L} (rule : GentzenStep2Ext p1 p2 conc)
      (t1 : SearchTree p1) {t2 : SearchTree p2} {p : List Bool}
      (h : LeafAt leaf records t2 p) :
      LeafAt leaf records (.twoPremise rule t1 t2) (true :: p)

end LCS.FirstOrder.Gentzen.Search.NoFunction
end
