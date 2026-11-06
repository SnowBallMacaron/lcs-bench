import LCS.Item
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Gentzen.Search.NoFunction.FreeSubstitution
import Attach
import LCS.FirstOrder.Gentzen.Search.NoFunction.LeafExtension.ProofsStamp

/-! # Extending the nonaxiom leaves (Definition 5.4.9)

Locating the formula to expand in a leaf sequent, the variable bounds kept at every
leaf, the tree-level leaf invariant, and the one-premise extension by a new variable
shared by grow-left and grow-right.
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

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Growth
/-- Definition 5.4.9 (required helper): If a formula `A` occurs in a
    list of antecedent/succedent formulae, we can split the list as
    `Γ ++ [A] ++ Δ`. Canonical choice of splitting: the leftmost
    occurrence. Used to construct `GentzenStep1Ext` / `GentzenStep2Ext`
    rule witnesses (whose constructors expect explicit `Γ Δ Λ` lists). -/
theorem list_split_mem {α : Type} (l : List α) (a : α) (h : a ∈ l) :
    ∃ pre post : List α, l = pre ++ [a] ++ post := by
-- BEGIN PROOF
  induction l with
  | nil => cases h
  | cons x xs ih =>
    by_cases hxa : x = a
    · exact ⟨[], xs, by simp [hxa]⟩
    · cases h with
      | head _ => exact absurd rfl hxa
      | tail _ h' =>
        obtain ⟨pre, post, heq⟩ := ih h'
        exact ⟨x :: pre, post, by simp [heq]⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (required helper): Classical extraction of the
    split witness from `list_split_mem`. Uses `Classical.choose` — pure
    existential extraction, not a search-procedure oracle. Returned as a
    `Σ`-shaped record so that downstream `let ⟨Γ, Δ, hsplit⟩ := ...`
    destructuring works. -/
noncomputable def splitListAt {α : Type} (l : List α) (a : α) (h : a ∈ l) :
    { p : List α × List α // l = p.1 ++ [a] ++ p.2 } :=
  let pre := (list_split_mem l a h).choose
  let post := (list_split_mem l a h).choose_spec.choose
  ⟨(pre, post), (list_split_mem l a h).choose_spec.choose_spec⟩

-- ===================================================================
-- Leaf-level variable bound: every FV in a leaf sequent is < availNext
-- ===================================================================

/-- Definition 5.4.9 (companion): No free variable of the leaf occurs
    at or after the given position in the availability enumeration. -/
@[blueprint "chap5__definition_5_4_9"]
def LeafFVBelow {L : Language} (supply : TermStream L) (leaf : Sequent L) (bound : Nat) : Prop :=
  ∀ F ∈ leaf.antecedent ++ leaf.succedent,
    ∀ j ∈ formulaFVN F, BeforeCursor supply bound j

/-- Definition 5.4.9 (companion, leaf-level invariant): Every BOUND
    variable occurring in any formula of a leaf sequent has index
    strictly less than a given `bound`. Dual of `LeafFVBelow` for the
    BV side. The bound is the static `bound` parameter of `Inv`; rule applications don't introduce new binders, so BV
    indices stay bounded by the original `bound` forever. -/
@[blueprint "chap5__definition_5_4_9"]
def LeafBVBelow {L : Language} (leaf : Sequent L) (bound : Nat) : Prop :=
  ∀ F ∈ leaf.antecedent ++ leaf.succedent,
    ∀ j ∈ formulaBVN F, j < bound

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Definition 5.4.9 (companion): Advancing the availability cursor
    preserves freshness for a leaf. -/
theorem LeafFVBelow_mono {L : Language} {supply : TermStream L} {leaf : Sequent L} {b b' : Nat}
    (h : LeafFVBelow supply leaf b) (hle : b ≤ b') : LeafFVBelow supply leaf b' := by
-- BEGIN PROOF
  intro F hF j hj
  exact (h F hF j hj).mono hle

-- ===================================================================
-- Subformula / BV-subset invariant (§5.4.9 tree-level preservation)
-- ===================================================================

/-- Definition 5.4.9 (companion, tree-level invariant): Every binder
    occurring in any formula of `leaf` already occurs as a binder in
    some formula of the original sequent `seq`. Formally:

      ∀ F ∈ leaf, ∀ y ∈ BV(F), ∃ G ∈ seq, y ∈ BV(G).

    This is the textbook's implicit invariant ("no rule introduces new
    binders" — every Gentzen rule either decomposes a formula into
    subformulas or substitutes a term for a free variable, both
    operations PRESERVE the set of binders). Preserved under all
    twelve rule applications of `GentzenStep1Ext`/`GentzenStep2Ext`.

    Used to discharge `y ∉ BV(F)` for free-for substitution at deeper
    leaves: combined with `Inv seq bound st` + `crossNoFreeBound seq`,
    gives `y ∉ BV(G)` for every `G ∈ seq`, then the BV-subset lifts
    to `y ∉ BV(F)` for every `F ∈ leaf`. -/
@[blueprint "chap5__definition_5_4_9"]
def LeafBVSubsetSeq {L : Language} (leaf seq : Sequent L) : Prop :=
  ∀ F ∈ leaf.antecedent ++ leaf.succedent,
    ∀ y ∈ formulaBVN F,
      ∃ G ∈ seq.antecedent ++ seq.succedent, y ∈ formulaBVN G

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.4.9 (companion, tree-level invariant): Reflexivity —
    a sequent trivially has its own BVs as a subset of its own BVs. -/
theorem LeafBVSubsetSeq.refl {L : Language} (seq : Sequent L) :
    LeafBVSubsetSeq seq seq := by
-- BEGIN PROOF
  intro F hF y hy
  exact ⟨F, hF, hy⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (companion, discharge): If `LeafBVSubsetSeq leaf seq`
    and `i ∉ BV(G)` for every `G ∈ seq`, then `i ∉ BV(F)` for every
    `F ∈ leaf`. This is how the leaf-level free-for discharge descends
    from the `seq`-level `crossNoFreeBound` / `NoVarAbove` witnesses. -/
theorem notBV_leaf_of_notBV_seq {L : Language} {leaf seq : Sequent L}
    (hSub : LeafBVSubsetSeq leaf seq) {i : Nat}
    (hNotBV : ∀ G ∈ seq.antecedent ++ seq.succedent, i ∉ formulaBVN G)
    (F : FormulaN L) (hF : F ∈ leaf.antecedent ++ leaf.succedent) :
    i ∉ formulaBVN F := by
-- BEGIN PROOF
  intro hiBV
  obtain ⟨G, hG, hiG⟩ := hSub F hF i hiBV
  exact hNotBV G hG hiG

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.LeafInvariant
/-- Definition 5.4.9 (required helper): `formulaBVN (formulaSubstN A t x)
    ⊆ formulaBVN A`. Term substitution cannot introduce new binders
    because `Term L` has no quantifier constructor — terms only
    contribute free variables. Proved by induction on `A`. -/
theorem formulaBVN_formulaSubstN_subset {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) :
    formulaBVN (formulaSubstN A t x) ⊆ formulaBVN A := by
-- BEGIN PROOF
  intro y hy
  induction A with
  | predN _ _ => exact hy
  | eq_ _ _ _ => exact hy
  | neg A ih =>
    show y ∈ formulaBVN A
    exact ih hy
  | conj A B ihA ihB =>
    show y ∈ formulaBVN A ∪ formulaBVN B
    rcases hy with hyA | hyB
    · exact Or.inl (ihA hyA)
    · exact Or.inr (ihB hyB)
  | disj A B ihA ihB =>
    show y ∈ formulaBVN A ∪ formulaBVN B
    rcases hy with hyA | hyB
    · exact Or.inl (ihA hyA)
    · exact Or.inr (ihB hyB)
  | impl A B ihA ihB =>
    show y ∈ formulaBVN A ∪ formulaBVN B
    rcases hy with hyA | hyB
    · exact Or.inl (ihA hyA)
    · exact Or.inr (ihB hyB)
  | all z A ih =>
    -- formulaSubstN (.all z A) t x = if x ≠ z then .all z (formulaSubstN A t x) else .all z A
    show y ∈ formulaBVN A ∪ Set.singleton z
    unfold formulaSubstN at hy
    split at hy
    · -- x ≠ z case: formulaSubstN = .all z (formulaSubstN A t x)
      -- BV = formulaBVN (formulaSubstN A t x) ∪ {z}
      rcases hy with hyA | hyZ
      · exact Or.inl (ih hyA)
      · exact Or.inr hyZ
    · -- x = z case: formulaSubstN = .all z A, so BV = formulaBVN A ∪ {z}
      exact hy
  | ex z A ih =>
    show y ∈ formulaBVN A ∪ Set.singleton z
    unfold formulaSubstN at hy
    split at hy
    · rcases hy with hyA | hyZ
      · exact Or.inl (ih hyA)
      · exact Or.inr hyZ
    · exact hy

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Definition 5.4.9 (companion, leaf-level invariant): `LeafBVBelow`
    for `leaf` follows from `LeafBVSubsetSeq leaf seq` +
    `NoVarAbove seq bound`. Every BV-index in `leaf` is in some BV of
    `seq`, which is `< bound` by `NoVarAbove`. -/
theorem LeafBVBelow_of_SubsetSeq {L : Language} {leaf seq : Sequent L}
    (hSub : LeafBVSubsetSeq leaf seq) {bound : Nat}
    (hNVA : NoVarAbove seq bound) :
    LeafBVBelow leaf bound := by
-- BEGIN PROOF
  intro F hF j hj
  obtain ⟨G, hG, hjG⟩ := hSub F hF j hj
  exact (hNVA G hG).2 j hjG

-- ===================================================================
-- Tree walker: extendAllNonaxiomLeaves (§5.4.9 "extend every nonaxiom leaf")
-- ===================================================================

-- ===================================================================
-- Tree-level leaf invariants (packaged for walker consumption)
-- ===================================================================

/-- Definition 5.4.9 (companion): Every leaf is fresh for the unconsumed
    availability stream, and its bound variables occur among the input's
    bound variables. Leaf annotations do not affect these conditions. -/
@[blueprint "chap5__definition_5_4_9"]
def TreeLeafInv {L : Language} (supply : TermStream L) {s : Sequent L}
    (t : SearchTree s) (seq : Sequent L) (bound : Nat) : Prop :=
  ∀ leaf ∈ t.toDeductionTree.leaves,
    LeafFVBelow supply leaf bound ∧
    LeafBVSubsetSeq leaf seq

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Definition 5.4.9 (companion, tree invariant): `TreeLeafInv` is
    monotone in `bound` — if FV below `b`, then also below any `b' ≥ b`. -/
theorem TreeLeafInv_mono {L : Language} {supply : TermStream L} {s : Sequent L}
    {t : SearchTree s} {seq : Sequent L} {b b' : Nat}
    (h : TreeLeafInv supply t seq b) (hle : b ≤ b') : TreeLeafInv supply t seq b' := by
-- BEGIN PROOF
  intro leaf hleaf
  obtain ⟨hFV, hSub⟩ := h leaf hleaf
  exact ⟨LeafFVBelow_mono hFV hle, hSub⟩

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Definition 5.4.9 (companion): A one-leaf search tree satisfies the
    invariant when the supplied availability tail is fresh for its sequent. -/
theorem TreeLeafInv_init {L : Language} {supply : TermStream L} (seq : Sequent L) (bound : Nat) (records : BranchRecords L)
    (hFresh : LeafFVBelow supply seq bound) :
    TreeLeafInv supply (SearchTree.leaf seq records) seq bound := by
-- BEGIN PROOF
  intro leaf hleaf
  simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves] at hleaf
  refine ⟨?_, ?_⟩
  · intro F hF j hj
    rw [hleaf] at hF
    exact hFresh F hF j hj
  · rw [hleaf]
    exact LeafBVSubsetSeq.refl seq

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Definition 5.4.9 (companion, tree invariant): `TreeLeafInv` on
    `onePremise rule t` reduces to `TreeLeafInv` on `t`, since
    `leaves (onePremise _ t) = leaves t`. -/
theorem TreeLeafInv_onePremise {L : Language} {supply : TermStream L} {prem conc : Sequent L}
    (rule : GentzenStep1Ext prem conc) (t : SearchTree prem)
    {seq : Sequent L} {bound : Nat} :
    TreeLeafInv supply (SearchTree.onePremise rule t) seq bound ↔
      TreeLeafInv supply t seq bound := by
-- BEGIN PROOF
  constructor <;> intro h leaf hleaf
  · exact h leaf (by simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves]; exact hleaf)
  · apply h leaf
    simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves] at hleaf
    exact hleaf

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Definition 5.4.9 (companion, tree invariant): `TreeLeafInv` on
    `twoPremise rule t1 t2` reduces to conjunction on `t1` and `t2`. -/
theorem TreeLeafInv_twoPremise {L : Language} {supply : TermStream L} {p1 p2 conc : Sequent L}
    (rule : GentzenStep2Ext p1 p2 conc) (t1 : SearchTree p1)
    (t2 : SearchTree p2)
    {seq : Sequent L} {bound : Nat} :
    TreeLeafInv supply (SearchTree.twoPremise rule t1 t2) seq bound ↔
      TreeLeafInv supply t1 seq bound ∧ TreeLeafInv supply t2 seq bound := by
-- BEGIN PROOF
  constructor
  · intro h
    refine ⟨fun leaf hleaf => ?_, fun leaf hleaf => ?_⟩
    · apply h leaf; simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves]; left; exact hleaf
    · apply h leaf; simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves]; right; exact hleaf
  · rintro ⟨h1, h2⟩ leaf hleaf
    simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves] at hleaf
    rcases hleaf with h_in1 | h_in2
    · exact h1 leaf h_in1
    · exact h2 leaf h_in2

-- ===================================================================
-- Per-leaf preservation of TreeLeafInv (PROVED — porting from worktree)
-- ===================================================================

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.LeafInvariant
/-- Definition 5.4.9 (required helper): Casting a deduction tree's
    index doesn't change its leaves (they're a polymorphic
    `List (Sequent L)`, not dependent on the type index). Used in
    preservation proofs to strip the `hConc ▸` transport wrapper
    produced by the propositional grow-* primitives. -/
theorem leaves_cast {L : Language} {s1 s2 : Sequent L} (heq : s1 = s2)
    (t : SearchTree s1) : (heq ▸ t).toDeductionTree.leaves = t.toDeductionTree.leaves := by
-- BEGIN PROOF
  subst heq
  rfl

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.LeafInvariant
/-- Every variable of an activated term is absent from the unconsumed
    availability stream. Function terms are excluded by the language hypothesis. -/
theorem termFV_of_tTERM0_lt_availNext {L : Language} {supply : TermStream L}
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat} {st : SearchState L supply}
    (h : SearchState.Inv seq bound st)
    {t : Term L} (ht : t ∈ st.tTERM0) :
    ∀ j ∈ termFV t, BeforeCursor supply st.availNext j := by
-- BEGIN PROOF
  unfold SearchState.tTERM0 at ht
  intro j hj
  match t with
  | .var i =>
    have hji : j = i := hj
    subst hji
    exact h.terms_below_avail _ ht j rfl
  | .const c => exact absurd hj id
  | .func f _ => exact (hNoFunc f).elim

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.LeafInvariant
/-- Definition 5.4.9 (required helper): `leaf.antecedent ++ leaf.succedent`
    membership splits through list append. -/
theorem mem_antSucc_of_mem_antecedent {L : Language}
    {leaf : Sequent L} {F : FormulaN L} (h : F ∈ leaf.antecedent) :
    F ∈ leaf.antecedent ++ leaf.succedent :=
-- BEGIN PROOF
  List.mem_append.mpr (Or.inl h)

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.LeafInvariant
theorem mem_antSucc_of_mem_succedent {L : Language}
    {leaf : Sequent L} {F : FormulaN L} (h : F ∈ leaf.succedent) :
    F ∈ leaf.antecedent ++ leaf.succedent :=
-- BEGIN PROOF
  List.mem_append.mpr (Or.inr h)

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

end LCS.FirstOrder.Gentzen.Search.NoFunction
end
