import LCS.Item
import LCS.Util
import LCS.FirstOrder.Equality
import LCS.FirstOrder.Equality.Search
import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Completeness.InfiniteSearch
import LCS.FirstOrder.Gentzen.Search.NoFunction
import LCS.FirstOrder.Equality.Completeness.Part1

section
namespace LCS.FirstOrder.Equality.Completeness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Completeness.InfiniteSearch
open LCS.FirstOrder.Completeness

/-- Definition 5.6.3 (companion, normalized): At the end of every expansion step,
adds the head of EQ_{j,i} for all i = 0,...,NUMACT to the antecedent
of the given leaf Sequent, where j = eqCyclingIndex(RC). The textbook
(Def 5.6.3) says: 'for i:=0 to NUMACT_0 do Gamma' := Gamma',
head(EQ_{j,i}) endfor'. Returns the augmented Sequent with equality
axiom heads appended after the rightmost antecedent formula, in increasing
index order. Empty EQ lists contribute no formula. -/
noncomputable def injectEqFormulae {L : Language} (st : SearchStateEq L)
    (seq : Sequent L) : Sequent L :=
  let j := eqCyclingIndex st.roundCounter
  let numact := st.numact
  -- Collect the head of EQ_{j,i} for i = 0, ..., numact
  let heads := (List.range (numact + 1)).filterMap fun i =>
    (st.eqListForIndex j i).head?
  { antecedent := seq.antecedent ++ heads
  , succedent := seq.succedent }

-- ===================================================================
-- Definition 5.6.3 (normalized): deleteEqHeads
-- ===================================================================

/-- Definition 5.6.3 (companion, normalized): At the end of each round, deletes
the head formula from each EQ_{j,i} list for i = 0,...,NUMACT0
(the value of NUMACT at round start), where j = eqCyclingIndex(RC).
The textbook (Def 5.6.3) says: 'for i:=0 to NUMACT_0 do EQ_{j,i} :=
tail(EQ_{j,i}) endfor'. Returns the updated SearchStateEq with the
relevant eq1/eq2/eq3 field advanced by one position for each active
index. Mirrors deleteEqListHeads (SearchStateEq) but operates on
SearchStateEq with FormulaN lists. -/
noncomputable def deleteEqHeads {L : Language} (st : SearchStateEq L)
    (numact0 : Nat) : SearchStateEq L :=
  let j := eqCyclingIndex st.roundCounter
  let dropHead (eqFn : Nat → EqFormulaStream L) : Nat → EqFormulaStream L :=
    fun i => if i ≤ numact0 then (eqFn i).tail else eqFn i
  match j with
  | 1 => { st with eq1 := dropHead st.eq1 }
  | 2 => { st with eq2 := dropHead st.eq2 }
  | 3 => { st with eq3 := dropHead st.eq3 }
  | _ => st

-- ===================================================================
-- Definition 5.6.3 (normalized): searchRoundEq
-- ===================================================================

/-- Definition 5.6.3 (companion, normalized): Relation describing one complete
round of the equality search procedure on a list of leaf Sequent.
The textbook search procedure (Def 5.6.3) describes one round as:
1. Snapshot NUMACT0 := NUMACT, compute j = (RC mod 3) + 1.
2. For each non-finished leaf (in lex order): apply base expansion
   (searchClosureStep from Def 5.5.1 for linear type-A/C/D
   decomposition), then inject EQ_{j,i} heads into the antecedent.
3. After all leaves processed: delete EQ_{j,i} heads for
   i = 0..NUMACT0, increment RC.
This relation constrains the output state and results:
- Finished (axiom) leaves are preserved in the results.
- Non-finished leaves are expanded and have EQ heads injected.
- The output state has EQ heads deleted and RC incremented.
The terms and freshVar parameters correspond to the current round's
instantiation terms for type-C/D decomposition. -/
def searchRoundEq {L : Language} (st : SearchStateEq L)
    (leaves : List (Sequent L))
    (terms : List (Term L)) (freshVar : Term L)
    (st' : SearchStateEq L) (results : List (Sequent L)) : Prop :=
  let numact0 := st.numact
  -- Each finished (axiom) leaf is kept unchanged in results
  (∀ leaf ∈ leaves,
    isAxiom leaf → leaf ∈ results) ∧
  -- Each non-finished leaf is expanded via searchClosureStep
  -- (base expand from Def 5.5.1) then has EQ heads injected,
  -- and the result appears in the output list
  (∀ leaf ∈ leaves,
    ¬isAxiom leaf →
    injectEqFormulae st (searchClosureStep leaf terms freshVar) ∈ results) ∧
  -- The output state has EQ heads deleted and RC incremented
  st' = { deleteEqHeads st numact0 with
    roundCounter := st.roundCounter + 1 }

-- ===================================================================
-- Definition 5.6.3 (normalized): branchStepEqN (moved before SearchTreeDataEq)
-- ===================================================================

/-- Definition 5.6.3 (companion, normalized): One branching expansion step with
equality injection. Composes branchStep (which applies linear type-A/C/D
decomposition via searchClosureStep AND adds type-B component selection
based on the branching bit) with injectEqFormulae (which adds EQ heads
to the antecedent).

At depth n, uses terms enumerate 0..n for type-C instantiation,
var(freshBase+n) for type-D witnesses, and the branching bit for type-B
component selection. Then injects EQ_{j,i} heads from the given
SearchStateEq. This is the equality-aware analogue of branchStep. -/
noncomputable def branchStepEqN {L : Language} [Countable (Term L)]
    (prev : Sequent L) (depth : Nat) (freshBase : Nat)
    (bit : Nat) (st : SearchStateEq L)
    (rootSeq : Sequent L) : Sequent L :=
  let branched := branchStep prev depth freshBase bit rootSeq
  injectEqFormulae st branched

-- ===================================================================
-- Definition 5.6.3 (normalized): stateAt (moved before SearchTreeDataEq)
-- ===================================================================

/-- Definition 5.6.3 (normalized, companion): Compute the equality search
state at round n by iterating state updates from initSt.
At each round, EQ heads are deleted (via deleteEqHeads) for the current
NUMACT value, and the round counter is incremented. This models the
textbook's 'for i:=0 to NUMACT0 do ... endfor; RC := RC + 1' at the end
of each round. -/
noncomputable def stateAt {L : Language} (initSt : SearchStateEq L) : Nat → SearchStateEq L
  | 0 => initSt
  | n + 1 =>
    let prev := stateAt initSt n
    { deleteEqHeads prev prev.numact with
      roundCounter := prev.roundCounter + 1 }

-- ===================================================================
-- Definition 5.6.3 (normalized): branchingNodeSeqFEqN (moved before SearchTreeDataEq)
-- ===================================================================

/-- Definition 5.6.3 (companion, normalized): Build the sequent at depth n along a
path described by f : Nat -> Nat, with equality injection at each step.
At each step k, applies branchStepEqN using f(k) as the branching bit
and stateAt(k) for the equality search state.

This is the equality-aware branching analogue of branchingNodeSeqFN
(Hintikka.lean). The path function f determines the type-B branching
choices, while stateAt provides the SearchStateEq at each depth
(determining which EQ heads to inject). -/
noncomputable def branchingNodeSeqFEqN {L : Language} [Countable (Term L)]
    (seq : Sequent L) (freshBase : Nat) (f : Nat → Nat)
    (stateAt : Nat → SearchStateEq L) : Nat → Sequent L
  | 0 => seq
  | n + 1 =>
    let prev := branchingNodeSeqFEqN seq freshBase f stateAt n
    branchStepEqN prev n freshBase (f n) (stateAt n) seq

-- ===================================================================
-- branchingNodeSeqFEqN helper lemmas (moved before SearchTreeDataEq)
-- ===================================================================

/-- Definition 5.6.3 (required helper): branchingNodeSeqFEqN depends only
on f at indices < n: if f and g agree on [0, n), the result is the same.
Used by `buildSearchTreeEq`'s `where path_ant_mono/path_succ_mono`. -/
theorem branchingNodeSeqFEqN_ext {L : Language} [Countable (Term L)]
    (seq : Sequent L) (freshBase : Nat)
    (f g : Nat → Nat)
    (stateAt : Nat → SearchStateEq L) (n : Nat)
    (heq : ∀ i, i < n → f i = g i) :
    branchingNodeSeqFEqN seq freshBase f stateAt n =
    branchingNodeSeqFEqN seq freshBase g stateAt n := by
-- BEGIN PROOF
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [branchingNodeSeqFEqN]
    rw [ih (fun i hi => heq i (by omega))]
    rw [heq k (by omega)]

/-- branchingNodeSeqFEqN with ofFn-based path function equals the
function-based version. Used to connect the node sequent (which uses
addr.getD) with the definitional unfolding (which uses f directly). -/
theorem branchingNodeSeqFEqN_ofFn_eq {L : Language} [Countable (Term L)]
    (seq : Sequent L) (freshBase : Nat)
    (f : Nat → Nat) (stateAtFn : Nat → SearchStateEq L) (n : Nat) :
    branchingNodeSeqFEqN seq freshBase
      (fun i => (List.ofFn (fun j : Fin n => f j)).getD i 0) stateAtFn n =
    branchingNodeSeqFEqN seq freshBase f stateAtFn n := by
-- BEGIN PROOF
  apply branchingNodeSeqFEqN_ext
  intro i hi
  unfold List.getD; simp [hi]

/-- Definition 5.6.3 (required helper): branchStepEqN preserves antecedent
membership. Used in `buildSearchTreeEq`'s path monotonicity invariants. -/
theorem branchStepEqN_ant_mono {L : Language} [Countable (Term L)]
    (prev : Sequent L) (depth freshBase bit : Nat) (st : SearchStateEq L)
    (rootSeq : Sequent L)
    (A : FormulaN L) (hA : A ∈ prev.antecedent) :
    A ∈ (branchStepEqN prev depth freshBase bit st rootSeq).antecedent := by
-- BEGIN PROOF
  unfold branchStepEqN injectEqFormulae
  apply List.mem_append_left
  exact branchStep_ant_mono _ depth freshBase bit rootSeq A hA

/-- Definition 5.6.3 (required helper): branchStepEqN preserves succedent
membership. Used in `buildSearchTreeEq`'s path monotonicity invariants. -/
theorem branchStepEqN_succ_mono {L : Language} [Countable (Term L)]
    (prev : Sequent L) (depth freshBase bit : Nat) (st : SearchStateEq L)
    (rootSeq : Sequent L)
    (B : FormulaN L) (hB : B ∈ prev.succedent) :
    B ∈ (branchStepEqN prev depth freshBase bit st rootSeq).succedent := by
-- BEGIN PROOF
  unfold branchStepEqN injectEqFormulae
  exact branchStep_succ_mono _ depth freshBase bit rootSeq B hB

-- ===================================================================
-- Definition 5.6.3 (normalized): SearchTreeDataEq
-- ===================================================================

/-- Structural data for the legacy equality search: a finitely branching tree,
its node sequents and states, and their local expansion invariants. -/
structure SearchTreeDataEq (L : Language) (hL : L.hasEquality = true)
    [Countable (Term L)] (seq : Sequent L) where
  /-- The tree domain of the search tree -/
  treeDom : LCS.TreeDomain
  /-- The sequent at each tree address -/
  nodeSequent : (addr : TreeAddr) → addr ∈ treeDom.dom → Sequent L
  /-- The equality search state at each tree address -/
  nodeStateEq : (addr : TreeAddr) → addr ∈ treeDom.dom → SearchStateEq L
  /-- Root has the input sequent -/
  root_sequent : nodeSequent [] treeDom.root_mem = seq
  /-- Axiom nodes are leaves: if the sequent at u is an axiom, then
      u has no children in the search tree -/
  axiom_is_leaf : ∀ (u : TreeAddr) (hu : u ∈ treeDom.dom),
    isAxiom (nodeSequent u hu) →
    ¬ ((u ++ [0]) ∈ treeDom.dom)
  /-- The tree is finitely branching -/
  finBranching : treeDom.FinitelyBranching
  /-- Non-axiom nodes have at least one child -/
  non_axiom_has_child : ∀ (u : TreeAddr) (hu : u ∈ treeDom.dom),
    ¬ isAxiom (nodeSequent u hu) →
    (u ++ [0]) ∈ treeDom.dom
  /-- Antecedent monotonicity along paths: parent antecedent ⊆ child antecedent -/
  path_ant_mono : ∀ (u : TreeAddr) (hu : u ∈ treeDom.dom) (i : Nat)
    (hc : (u ++ [i]) ∈ treeDom.dom) (A : FormulaN L),
    A ∈ (nodeSequent u hu).antecedent →
    A ∈ (nodeSequent (u ++ [i]) hc).antecedent
  /-- Succedent monotonicity along paths: parent succedent ⊆ child succedent -/
  path_succ_mono : ∀ (u : TreeAddr) (hu : u ∈ treeDom.dom) (i : Nat)
    (hc : (u ++ [i]) ∈ treeDom.dom) (B : FormulaN L),
    B ∈ (nodeSequent u hu).succedent →
    B ∈ (nodeSequent (u ++ [i]) hc).succedent
  /-- The base for fresh variable generation -/
  freshBase : Nat
  /-- freshBase is large enough to avoid all bound variables in seq -/
  freshBase_bound : ∀ v, ∀ A ∈ (seq.antecedent ++ seq.succedent), v ∈ formulaBVN A → v < freshBase
  /-- Path expansion with equality injection: along any infinite path f,
      the nodeSequent at depth n+1 equals branchStepEqN applied to the
      nodeSequent at depth n with appropriate equality state. -/
  path_expansion : ∀ (f : Nat → Nat) (n : Nat)
    (hPath : ∀ m, (List.ofFn (fun i : Fin m => f i)) ∈ treeDom.dom),
    nodeSequent (List.ofFn (fun i : Fin (n + 1) => f i)) (hPath (n + 1)) =
    branchStepEqN (nodeSequent (List.ofFn (fun i : Fin n => f i)) (hPath n))
      n freshBase (f n) (nodeStateEq (List.ofFn (fun i : Fin n => f i)) (hPath n)) seq

-- ===================================================================
-- Definition 5.6.3 (normalized, helper): pathSignedSet
-- ===================================================================

/-- Definition 5.6.3 (normalized, helper): The signed formula set along
a path f : Nat -> Nat in a SearchTreeDataEq. Collects all signed
formulae from the antecedent (as trueF) and succedent (as falseF) of
every sequent along the path. This avoids repeating the `let S := ...`
definition in every path property theorem. -/
def SearchTreeDataEq.pathSignedSet {L : Language} {hL : L.hasEquality = true} [Countable (Term L)] {seq : Sequent L}
    (w : SearchTreeDataEq L hL seq) (f : Nat → Nat)
    (_hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    Set (SignedFormula L) := fun sf =>
  ∃ n : Nat, ∃ (h : (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom),
    let seq_n := w.nodeSequent (List.ofFn (fun i : Fin n => f i)) h
    (∃ A ∈ seq_n.antecedent, sf = SignedFormula.trueF A) ∨
    (∃ B ∈ seq_n.succedent, sf = SignedFormula.falseF B)

-- ===================================================================
-- Path monotonicity lemmas for SearchTreeDataEq
-- ===================================================================

/-- Multi-step antecedent monotonicity along a path (equality case).
If A is in the antecedent at depth n and n ≤ m, then A is in the
antecedent at depth m, using path_ant_mono at each step. -/
theorem path_ant_mono_le_eq {L : Language} {hL : L.hasEquality = true} [Countable (Term L)] {seq : Sequent L}
    (w : SearchTreeDataEq L hL seq) (f : Nat → Nat)
    (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom)
    {n m : Nat} (h : n ≤ m) (A : FormulaN L)
    (hA : A ∈ (w.nodeSequent _ (hPath n)).antecedent) :
    A ∈ (w.nodeSequent _ (hPath m)).antecedent := by
-- BEGIN PROOF
  induction m with
  | zero => exact Nat.le_zero.mp h ▸ hA
  | succ k ih =>
    by_cases hk : n ≤ k
    · have hAk := ih hk
      have haddr := ofFn_succ_append f k
      have hc := haddr ▸ hPath (k + 1)
      have hAmono := w.path_ant_mono _ (hPath k) (f k) hc A hAk
      have hseq_eq : w.nodeSequent (List.ofFn (fun i : Fin k => f i) ++ [f k]) hc =
          w.nodeSequent (List.ofFn (fun i : Fin (k + 1) => f i)) (hPath (k + 1)) := by
        congr 1; exact haddr.symm
      rw [hseq_eq] at hAmono; exact hAmono
    · cases (show n = k + 1 by omega); exact hA

/-- Multi-step succedent monotonicity along a path (equality case).
Same as path_ant_mono_le_eq but for the succedent. -/
theorem path_succ_mono_le_eq {L : Language} {hL : L.hasEquality = true} [Countable (Term L)] {seq : Sequent L}
    (w : SearchTreeDataEq L hL seq) (f : Nat → Nat)
    (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom)
    {n m : Nat} (h : n ≤ m) (B : FormulaN L)
    (hB : B ∈ (w.nodeSequent _ (hPath n)).succedent) :
    B ∈ (w.nodeSequent _ (hPath m)).succedent := by
-- BEGIN PROOF
  induction m with
  | zero => exact Nat.le_zero.mp h ▸ hB
  | succ k ih =>
    by_cases hk : n ≤ k
    · have hBk := ih hk
      have haddr := ofFn_succ_append f k
      have hc := haddr ▸ hPath (k + 1)
      have hBmono := w.path_succ_mono _ (hPath k) (f k) hc B hBk
      have hseq_eq : w.nodeSequent (List.ofFn (fun i : Fin k => f i) ++ [f k]) hc =
          w.nodeSequent (List.ofFn (fun i : Fin (k + 1) => f i)) (hPath (k + 1)) := by
        congr 1; exact haddr.symm
      rw [hseq_eq] at hBmono; exact hBmono
    · cases (show n = k + 1 by omega); exact hB

-- ===================================================================
-- Theorem 5.6.1 properties: separate sorry'd theorems
-- ===================================================================

/-- Theorem 5.6.1 (companion, H1/H2): Along any infinite path in the equality
search tree, the signed formulae satisfy the propositional Hintikka
conditions: type-A formulae have both components, and type-B formulae
have at least one component. -/
theorem searchTreeEqN_path_hintikka_propositional {L : Language} {hL : L.hasEquality = true} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeDataEq L hL seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    let S := w.pathSignedSet f hPath
    (∀ (a : TypeA L), a.toSigned ∈ S → a.comp1 ∈ S ∧ a.comp2 ∈ S) ∧
    (∀ (b : TypeB L), b.toSigned ∈ S → b.comp1 ∈ S ∨ b.comp2 ∈ S) := by
-- BEGIN PROOF
  intro S
  -- Helper: lift branchStep antecedent membership to branchStepEqN
  have liftAnt : ∀ k (A : FormulaN L),
      A ∈ (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).antecedent →
      A ∈ (w.nodeSequent _ (hPath (k + 1))).antecedent := by
    intro k A hA
    have hexp := w.path_expansion f k hPath
    have hA_eq : A ∈ (branchStepEqN (w.nodeSequent _ (hPath k)) k w.freshBase (f k)
        (w.nodeStateEq _ (hPath k)) seq).antecedent := by
      unfold branchStepEqN injectEqFormulae; apply List.mem_append_left; exact hA
    rw [← hexp] at hA_eq; exact hA_eq
  -- Helper: lift branchStep succedent membership to branchStepEqN
  have liftSucc : ∀ k (B : FormulaN L),
      B ∈ (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).succedent →
      B ∈ (w.nodeSequent _ (hPath (k + 1))).succedent := by
    intro k B hB
    have hexp := w.path_expansion f k hPath
    have hB_eq : B ∈ (branchStepEqN (w.nodeSequent _ (hPath k)) k w.freshBase (f k)
        (w.nodeStateEq _ (hPath k)) seq).succedent := by
      unfold branchStepEqN injectEqFormulae; exact hB
    rw [← hexp] at hB_eq; exact hB_eq
  have freshVar_in : ∀ k, Term.var (w.freshBase + k) ∈
      branchTerms seq k w.freshBase := by
    intro k; simp only [branchTerms]
    exact List.mem_append_right _ (List.Mem.head _)
  constructor
  · -- H1: TypeA decomposition
    intro a ha
    cases a with
    | tConj X Y =>
      obtain ⟨k, _, hAk⟩ := ha
      have hAnt : FormulaN.conj X Y ∈ (w.nodeSequent _ (hPath k)).antecedent := by
        rcases hAk with ⟨A, hA, hAeq⟩ | ⟨B, _, hBeq⟩
        · exact SignedFormula.trueF.inj hAeq ▸ hA
        · exact absurd hBeq (by intro h; cases h)
      have hX := liftAnt k X (branchStep_decompAnt _ k w.freshBase (f k) seq _ _ hAnt (freshVar_in k) X
        (by simp [decomposeAntFormula]))
      have hY := liftAnt k Y (branchStep_decompAnt _ k w.freshBase (f k) seq _ _ hAnt (freshVar_in k) Y
        (by simp [decomposeAntFormula]))
      exact ⟨⟨k + 1, hPath (k + 1), Or.inl ⟨X, hX, rfl⟩⟩,
             ⟨k + 1, hPath (k + 1), Or.inl ⟨Y, hY, rfl⟩⟩⟩
    | fDisj X Y =>
      obtain ⟨k, _, hAk⟩ := ha
      have hSucc : FormulaN.disj X Y ∈ (w.nodeSequent _ (hPath k)).succedent := by
        rcases hAk with ⟨A, _, hAeq⟩ | ⟨B, hB, hBeq⟩
        · exact absurd hAeq (by intro h; cases h)
        · exact SignedFormula.falseF.inj hBeq ▸ hB
      have hX := liftSucc k X (branchStep_decompSucc _ k w.freshBase (f k) seq _ _ hSucc (freshVar_in k) X
        (by simp [decomposeSuccFormula]))
      have hY := liftSucc k Y (branchStep_decompSucc _ k w.freshBase (f k) seq _ _ hSucc (freshVar_in k) Y
        (by simp [decomposeSuccFormula]))
      exact ⟨⟨k + 1, hPath (k + 1), Or.inr ⟨X, hX, rfl⟩⟩,
             ⟨k + 1, hPath (k + 1), Or.inr ⟨Y, hY, rfl⟩⟩⟩
    | fImpl X Y =>
      obtain ⟨k, _, hAk⟩ := ha
      have hSucc : FormulaN.impl X Y ∈ (w.nodeSequent _ (hPath k)).succedent := by
        rcases hAk with ⟨A, _, hAeq⟩ | ⟨B, hB, hBeq⟩
        · exact absurd hAeq (by intro h; cases h)
        · exact SignedFormula.falseF.inj hBeq ▸ hB
      have hX := liftAnt k X (branchStep_decompSuccAnt _ k w.freshBase (f k) seq _ _ hSucc (freshVar_in k) X
        (by simp [decomposeSuccFormula]))
      have hY := liftSucc k Y (branchStep_decompSucc _ k w.freshBase (f k) seq _ _ hSucc (freshVar_in k) Y
        (by simp [decomposeSuccFormula]))
      exact ⟨⟨k + 1, hPath (k + 1), Or.inl ⟨X, hX, rfl⟩⟩,
             ⟨k + 1, hPath (k + 1), Or.inr ⟨Y, hY, rfl⟩⟩⟩
    | tNeg X =>
      obtain ⟨k, _, hAk⟩ := ha
      have hAnt : FormulaN.neg X ∈ (w.nodeSequent _ (hPath k)).antecedent := by
        rcases hAk with ⟨A, hA, hAeq⟩ | ⟨B, _, hBeq⟩
        · exact SignedFormula.trueF.inj hAeq ▸ hA
        · exact absurd hBeq (by intro h; cases h)
      have hX := liftSucc k X (branchStep_decompAntSucc _ k w.freshBase (f k) seq _ _ hAnt (freshVar_in k) X
        (by simp [decomposeAntFormula]))
      exact ⟨⟨k + 1, hPath (k + 1), Or.inr ⟨X, hX, rfl⟩⟩,
             ⟨k + 1, hPath (k + 1), Or.inr ⟨X, hX, rfl⟩⟩⟩
    | fNeg X =>
      obtain ⟨k, _, hAk⟩ := ha
      have hSucc : FormulaN.neg X ∈ (w.nodeSequent _ (hPath k)).succedent := by
        rcases hAk with ⟨A, _, hAeq⟩ | ⟨B, hB, hBeq⟩
        · exact absurd hAeq (by intro h; cases h)
        · exact SignedFormula.falseF.inj hBeq ▸ hB
      have hX := liftAnt k X (branchStep_decompSuccAnt _ k w.freshBase (f k) seq _ _ hSucc (freshVar_in k) X
        (by simp [decomposeSuccFormula]))
      exact ⟨⟨k + 1, hPath (k + 1), Or.inl ⟨X, hX, rfl⟩⟩,
             ⟨k + 1, hPath (k + 1), Or.inl ⟨X, hX, rfl⟩⟩⟩
  · -- H2: TypeB decomposition
    intro b hb
    cases b with
    | tDisj X Y =>
      obtain ⟨k, _, hAk⟩ := hb
      have hAnt : FormulaN.disj X Y ∈ (w.nodeSequent _ (hPath k)).antecedent := by
        rcases hAk with ⟨A, hA, hAeq⟩ | ⟨B, _, hBeq⟩
        · exact SignedFormula.trueF.inj hAeq ▸ hA
        · exact absurd hBeq (by intro h; cases h)
      by_cases hbit : f k = 0
      · have hX := liftAnt k X (by rw [hbit]; exact branchStep_disj_comp0 _ k w.freshBase seq X Y hAnt)
        exact Or.inl ⟨k + 1, hPath (k + 1), Or.inl ⟨X, hX, rfl⟩⟩
      · have hY := liftAnt k Y (branchStep_disj_comp1 _ k w.freshBase (f k) seq X Y hbit hAnt)
        exact Or.inr ⟨k + 1, hPath (k + 1), Or.inl ⟨Y, hY, rfl⟩⟩
    | tImpl X Y =>
      obtain ⟨k, _, hAk⟩ := hb
      have hAnt : FormulaN.impl X Y ∈ (w.nodeSequent _ (hPath k)).antecedent := by
        rcases hAk with ⟨A, hA, hAeq⟩ | ⟨B, _, hBeq⟩
        · exact SignedFormula.trueF.inj hAeq ▸ hA
        · exact absurd hBeq (by intro h; cases h)
      by_cases hbit : f k = 0
      · have hX := liftSucc k X (by rw [hbit]; exact branchStep_impl_comp0 _ k w.freshBase seq X Y hAnt)
        exact Or.inl ⟨k + 1, hPath (k + 1), Or.inr ⟨X, hX, rfl⟩⟩
      · have hY := liftAnt k Y (branchStep_impl_comp1 _ k w.freshBase (f k) seq X Y hbit hAnt)
        exact Or.inr ⟨k + 1, hPath (k + 1), Or.inl ⟨Y, hY, rfl⟩⟩
    | fConj X Y =>
      obtain ⟨k, _, hAk⟩ := hb
      have hSucc : FormulaN.conj X Y ∈ (w.nodeSequent _ (hPath k)).succedent := by
        rcases hAk with ⟨A, _, hAeq⟩ | ⟨B, hB, hBeq⟩
        · exact absurd hAeq (by intro h; cases h)
        · exact SignedFormula.falseF.inj hBeq ▸ hB
      by_cases hbit : f k = 0
      · have hX := liftSucc k X (by rw [hbit]; exact branchStep_conj_succ_comp0 _ k w.freshBase seq X Y hSucc)
        exact Or.inl ⟨k + 1, hPath (k + 1), Or.inr ⟨X, hX, rfl⟩⟩
      · have hY := liftSucc k Y (branchStep_conj_succ_comp1 _ k w.freshBase (f k) seq X Y hbit hSucc)
        exact Or.inr ⟨k + 1, hPath (k + 1), Or.inr ⟨Y, hY, rfl⟩⟩

/-- Theorem 5.6.1 (companion, H0): Along any infinite path in the equality search
tree, no atomic formula and its conjugate are both in the signed set. -/
theorem searchTreeEqN_path_no_complementary_atoms {L : Language} {hL : L.hasEquality = true} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeDataEq L hL seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    let S := w.pathSignedSet f hPath
    ∀ (A : FormulaN L), A.isAtomic = true →
      ¬(SignedFormula.trueF A ∈ S ∧ SignedFormula.falseF A ∈ S) := by
-- BEGIN PROOF
  intro S A _hAt ⟨⟨n, _hn, hAn⟩, ⟨m, _hm, hAm⟩⟩
  have hAnt_n : A ∈ (w.nodeSequent _ (hPath n)).antecedent := by
    rcases hAn with ⟨X, hX, hXeq⟩ | ⟨Y, _hY, hYeq⟩
    · exact SignedFormula.trueF.inj hXeq ▸ hX
    · exact absurd hYeq (by intro h; cases h)
  have hSucc_m : A ∈ (w.nodeSequent _ (hPath m)).succedent := by
    rcases hAm with ⟨X, _hX, hXeq⟩ | ⟨Y, hY, hYeq⟩
    · exact absurd hXeq (by intro h; cases h)
    · exact SignedFormula.falseF.inj hYeq ▸ hY
  let N := max n m
  have hAnt_N := path_ant_mono_le_eq w f hPath (Nat.le_max_left n m) A hAnt_n
  have hSucc_N := path_succ_mono_le_eq w f hPath (Nat.le_max_right n m) A hSucc_m
  have hAx : isAxiom (w.nodeSequent _ (hPath N)) := ⟨A, hAnt_N, hSucc_N⟩
  have hNoChild := w.axiom_is_leaf _ (hPath N) hAx
  have haddr := ofFn_succ_append f N
  have hChild : (List.ofFn (fun i : Fin N => f i)) ++ [f N] ∈ w.treeDom.dom :=
    haddr ▸ hPath (N + 1)
  have hChild0 := dom_child_zero w.treeDom _ (f N) hChild
  exact hNoChild hChild0

/-- Theorem 5.6.1 (companion, H3): Along any infinite path in the equality search
tree, for every type-C formula in S and every term t, C(t) is in S whenever t is free for the bound variable. -/
theorem searchTreeEqN_path_hintikka_typeC {L : Language} {hL : L.hasEquality = true} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeDataEq L hL seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    let S := w.pathSignedSet f hPath
    ∀ (c : TypeC L), c.toSigned ∈ S →
      ∀ (t : Term L), t ∈ safeTermsN seq → ∀ h : isFreeForN t c.var c.body, c.comp t h ∈ S := by
-- BEGIN PROOF
  intro S c hc t ht_safe hfree
  -- Helpers for lifting from branchStep to branchStepEqN (same pattern as H1/H2)
  have liftAnt : ∀ k (A : FormulaN L),
      A ∈ (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).antecedent →
      A ∈ (w.nodeSequent _ (hPath (k + 1))).antecedent := by
    intro k A hA
    have hexp := w.path_expansion f k hPath
    have hA_eq : A ∈ (branchStepEqN (w.nodeSequent _ (hPath k)) k w.freshBase (f k)
        (w.nodeStateEq _ (hPath k)) seq).antecedent := by
      unfold branchStepEqN injectEqFormulae; apply List.mem_append_left; exact hA
    rw [← hexp] at hA_eq; exact hA_eq
  have liftSucc : ∀ k (B : FormulaN L),
      B ∈ (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).succedent →
      B ∈ (w.nodeSequent _ (hPath (k + 1))).succedent := by
    intro k B hB
    have hexp := w.path_expansion f k hPath
    have hB_eq : B ∈ (branchStepEqN (w.nodeSequent _ (hPath k)) k w.freshBase (f k)
        (w.nodeStateEq _ (hPath k)) seq).succedent := by
      unfold branchStepEqN injectEqFormulae; exact hB
    rw [← hexp] at hB_eq; exact hB_eq
  cases c with
  | tAll x A =>
    obtain ⟨k, _, hAk⟩ := hc
    have hAnt : FormulaN.all x A ∈ (w.nodeSequent _ (hPath k)).antecedent := by
      rcases hAk with ⟨A', hA', hAeq⟩ | ⟨B, _, hBeq⟩
      · exact SignedFormula.trueF.inj hAeq ▸ hA'
      · exact absurd hBeq (by intro h; cases h)
    obtain ⟨j, hj⟩ := Countable.enumerate_surj t
    let N := max k j
    have hAnt_N := path_ant_mono_le_eq w f hPath (Nat.le_max_left k j) _ hAnt
    have ht_safe' : Countable.enumerate (α := Term L) j ∈ safeTermsN seq := hj ▸ ht_safe
    open Classical in
    have ht : Countable.enumerate (α := Term L) j ∈ branchTerms seq N w.freshBase := by
      simp only [branchTerms]
      apply List.mem_append_left
      rw [List.mem_filter]
      exact ⟨List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩,
             decide_eq_true_eq.mpr ht_safe'⟩
    have hcomp : formulaSubstN A (Countable.enumerate (α := Term L) j) x ∈
        (decomposeAntFormula (.all x A) (Countable.enumerate j) (Term.var (w.freshBase + N))).1 := by
      simp [decomposeAntFormula]
    have hX := liftAnt N _ (branchStep_decompAnt _ N w.freshBase (f N) seq _ _ hAnt_N ht _ hcomp)
    rw [hj] at hX
    exact ⟨N + 1, hPath (N + 1), Or.inl ⟨formulaSubstN A t x, hX, rfl⟩⟩
  | fEx x A =>
    obtain ⟨k, _, hAk⟩ := hc
    have hSucc : FormulaN.ex x A ∈ (w.nodeSequent _ (hPath k)).succedent := by
      rcases hAk with ⟨A', _, hAeq⟩ | ⟨B, hB, hBeq⟩
      · exact absurd hAeq (by intro h; cases h)
      · exact SignedFormula.falseF.inj hBeq ▸ hB
    obtain ⟨j, hj⟩ := Countable.enumerate_surj t
    let N := max k j
    have hSucc_N := path_succ_mono_le_eq w f hPath (Nat.le_max_left k j) _ hSucc
    have ht_safe' : Countable.enumerate (α := Term L) j ∈ safeTermsN seq := hj ▸ ht_safe
    open Classical in
    have ht : Countable.enumerate (α := Term L) j ∈ branchTerms seq N w.freshBase := by
      simp only [branchTerms]
      apply List.mem_append_left
      rw [List.mem_filter]
      exact ⟨List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩,
             decide_eq_true_eq.mpr ht_safe'⟩
    have hcomp : formulaSubstN A (Countable.enumerate (α := Term L) j) x ∈
        (decomposeSuccFormula (.ex x A) (Countable.enumerate j) (Term.var (w.freshBase + N))).2 := by
      simp [decomposeSuccFormula]
    have hX := liftSucc N _ (branchStep_decompSucc _ N w.freshBase (f N) seq _ _ hSucc_N ht _ hcomp)
    rw [hj] at hX
    exact ⟨N + 1, hPath (N + 1), Or.inr ⟨formulaSubstN A t x, hX, rfl⟩⟩

/-- Type-D expansion along an equality search path has a safe, free-for
variable witness, obtained at a stage beyond the body's bound variables. -/
theorem searchTreeEqN_path_hintikka_typeD_safe {L : Language} {hL : L.hasEquality = true} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeDataEq L hL seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    let S := w.pathSignedSet f hPath
    ∀ (d : TypeD L), d.toSigned ∈ S →
      ∃ (t : Term L), t ∈ safeTermsN seq ∧ ∃ h : isFreeForN t d.var d.body, d.comp t h ∈ S := by
-- BEGIN PROOF
  intro S d hd
  -- Helpers for lifting from branchStep to branchStepEqN
  have liftAnt : ∀ k (A : FormulaN L),
      A ∈ (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).antecedent →
      A ∈ (w.nodeSequent _ (hPath (k + 1))).antecedent := by
    intro k A hA
    have hexp := w.path_expansion f k hPath
    have hA_eq : A ∈ (branchStepEqN (w.nodeSequent _ (hPath k)) k w.freshBase (f k)
        (w.nodeStateEq _ (hPath k)) seq).antecedent := by
      unfold branchStepEqN injectEqFormulae; apply List.mem_append_left; exact hA
    rw [← hexp] at hA_eq; exact hA_eq
  have liftSucc : ∀ k (B : FormulaN L),
      B ∈ (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).succedent →
      B ∈ (w.nodeSequent _ (hPath (k + 1))).succedent := by
    intro k B hB
    have hexp := w.path_expansion f k hPath
    have hB_eq : B ∈ (branchStepEqN (w.nodeSequent _ (hPath k)) k w.freshBase (f k)
        (w.nodeStateEq _ (hPath k)) seq).succedent := by
      unfold branchStepEqN injectEqFormulae; exact hB
    rw [← hexp] at hB_eq; exact hB_eq
  have freshSafe (n : Nat) : Term.var (w.freshBase + n) ∈ safeTermsN seq := by
    intro v hv B hB hbv
    have he : v = w.freshBase + n := hv
    subst v
    have hb := w.freshBase_bound _ B hB hbv
    omega
  cases d with
  | tEx x A =>
    obtain ⟨k, _, hAk⟩ := hd
    have hAnt : FormulaN.ex x A ∈ (w.nodeSequent _ (hPath k)).antecedent := by
      rcases hAk with ⟨A', hA', hAeq⟩ | ⟨B, _, hBeq⟩
      · exact SignedFormula.trueF.inj hAeq ▸ hA'
      · exact absurd hBeq (by intro h; cases h)
    let N := max k (formulaMaxBVN A + 1)
    have hAntN := path_ant_mono_le_eq w f hPath
      (Nat.le_max_left k (formulaMaxBVN A + 1)) _ hAnt
    have hfree : isFreeForN (Term.var (w.freshBase + N)) x A := by
      apply isFreeForN_of_bv_disjoint
      intro v hv hbv
      have he : v = w.freshBase + N := hv
      subst v
      have hb := formulaBVN_lt_formulaMaxBVN A _ hbv
      have hn := Nat.le_max_right k (formulaMaxBVN A + 1)
      omega
    have ht : Term.var (w.freshBase + N) ∈ branchTerms seq N w.freshBase :=
      List.mem_append_right _ (List.Mem.head _)
    have hcomp : formulaSubstN A (Term.var (w.freshBase + N)) x ∈
        (decomposeAntFormula (.ex x A) (Term.var (w.freshBase + N)) (Term.var (w.freshBase + N))).1 := by
      simp [decomposeAntFormula]
    have hX := liftAnt N _ (branchStep_decompAnt _ N w.freshBase (f N) seq _ _ hAntN ht _ hcomp)
    exact ⟨Term.var (w.freshBase + N), freshSafe N, hfree, N + 1, hPath (N + 1), Or.inl ⟨_, hX, rfl⟩⟩
  | fAll x A =>
    obtain ⟨k, _, hAk⟩ := hd
    have hSucc : FormulaN.all x A ∈ (w.nodeSequent _ (hPath k)).succedent := by
      rcases hAk with ⟨A', _, hAeq⟩ | ⟨B, hB, hBeq⟩
      · exact absurd hAeq (by intro h; cases h)
      · exact SignedFormula.falseF.inj hBeq ▸ hB
    let N := max k (formulaMaxBVN A + 1)
    have hSuccN := path_succ_mono_le_eq w f hPath
      (Nat.le_max_left k (formulaMaxBVN A + 1)) _ hSucc
    have hfree : isFreeForN (Term.var (w.freshBase + N)) x A := by
      apply isFreeForN_of_bv_disjoint
      intro v hv hbv
      have he : v = w.freshBase + N := hv
      subst v
      have hb := formulaBVN_lt_formulaMaxBVN A _ hbv
      have hn := Nat.le_max_right k (formulaMaxBVN A + 1)
      omega
    have ht : Term.var (w.freshBase + N) ∈ branchTerms seq N w.freshBase :=
      List.mem_append_right _ (List.Mem.head _)
    have hcomp : formulaSubstN A (Term.var (w.freshBase + N)) x ∈
        (decomposeSuccFormula (.all x A) (Term.var (w.freshBase + N)) (Term.var (w.freshBase + N))).2 := by
      simp [decomposeSuccFormula]
    have hX := liftSucc N _ (branchStep_decompSucc _ N w.freshBase (f N) seq _ _ hSuccN ht _ hcomp)
    exact ⟨Term.var (w.freshBase + N), freshSafe N, hfree, N + 1, hPath (N + 1), Or.inr ⟨_, hX, rfl⟩⟩

/-- Theorem 5.6.1 (companion, H4): Along any infinite path in the equality search
tree, for every type-D formula in S, there exists a term t free for its bound variable such that D(t) is in S. -/
theorem searchTreeEqN_path_hintikka_typeD {L : Language} {hL : L.hasEquality = true} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeDataEq L hL seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    let S := w.pathSignedSet f hPath
    ∀ (d : TypeD L), d.toSigned ∈ S →
      ∃ (t : Term L), ∃ h : isFreeForN t d.var d.body, d.comp t h ∈ S := by
  intro S d hd
  obtain ⟨t, _, hfree, hcomp⟩ := searchTreeEqN_path_hintikka_typeD_safe w f hPath d hd
  exact ⟨t, hfree, hcomp⟩

/-- Theorem 5.6.1 (companion, H5): isFreeFor holds for quantified formulae along
any infinite path in the equality search tree. -/
theorem searchTreeEqN_path_freeFor {L : Language} {hL : L.hasEquality = true} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeDataEq L hL seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    let S := w.pathSignedSet f hPath
    ∀ (x : Nat) (A : FormulaN L) (t : Term L),
      (SignedFormula.trueF (FormulaN.all x A) ∈ S ∨
       SignedFormula.falseF (FormulaN.all x A) ∈ S ∨
       SignedFormula.trueF (FormulaN.ex x A) ∈ S ∨
       SignedFormula.falseF (FormulaN.ex x A) ∈ S) →
      isFreeForN t x A := by
-- BEGIN PROOF
  -- DEBT(free-for condition for arbitrary terms at quantified path formulae not established)
  sorry

/-- Theorem 5.6.1: Every infinite path of the Definition 5.6.3 procedure
has a Hintikka signed set over the term domain of that same run. -/
theorem infinitePath_yields_hintikkaSetEq {L : FirstOrderLanguage}
    {hL : L.hasEquality = true} (run : Search.Run L hL)
    (path : Nat → Nat) (hPath : run.IsInfinitePath path) :
    IsHintikkaSetEq L.toLanguage hL run.termDomain (run.pathSignedSet path) :=
  Search.infinitePath_yields_hintikkaSetEq run path hPath

/-- Theorem 5.6.1, H6(i): Every run-domain term has its reflexivity formula
on every infinite path of the equality-search procedure. -/
theorem searchTreeEqN_path_hintikka_h6i {L : FirstOrderLanguage}
    {hL : L.hasEquality = true} (run : Search.Run L hL)
    (path : Nat → Nat) (hPath : run.IsInfinitePath path) :
    ∀ t ∈ run.termDomain, SignedFormula.trueF (FormulaN.eq_ hL t t) ∈
      run.pathSignedSet path :=
  (infinitePath_yields_hintikkaSetEq run path hPath).h6i

/-- Theorem 5.6.1, H6(ii): Congruence for each path-occurring function and
all run-domain argument tuples occurs on the same infinite search path. -/
theorem searchTreeEqN_path_hintikka_h6ii {L : FirstOrderLanguage}
    {hL : L.hasEquality = true} (run : Search.Run L hL)
    (path : Nat → Nat) (hPath : run.IsInfinitePath path) :
    ∀ (g : L.funSymbols), g ∈ signedSetFunSyms (run.pathSignedSet path) →
      ∀ (ss ts : Fin (L.funArity g) → Term L.toLanguage),
        (∀ i, ss i ∈ run.termDomain) → (∀ i, ts i ∈ run.termDomain) →
        SignedFormula.trueF (eqCongruenceImplFunc L.toLanguage hL g ss ts) ∈
          run.pathSignedSet path :=
  (infinitePath_yields_hintikkaSetEq run path hPath).h6ii

/-- Theorem 5.6.1, H6(iii): Congruence for path predicates
and run-domain argument tuples occurs on the same infinite search path. -/
theorem searchTreeEqN_path_hintikka_h6iii {L : FirstOrderLanguage}
    {hL : L.hasEquality = true} (run : Search.Run L hL)
    (path : Nat → Nat) (hPath : run.IsInfinitePath path) :
    ∀ (P : L.predSymbols), P ∈ signedSetPredSyms (run.pathSignedSet path) →
      ∀ (ss ts : Fin (L.predArity P) → Term L.toLanguage),
        (∀ i, ss i ∈ run.termDomain) → (∀ i, ts i ∈ run.termDomain) →
        SignedFormula.trueF (eqCongruenceImplPred L.toLanguage hL P ss ts) ∈
          run.pathSignedSet path :=
  (infinitePath_yields_hintikkaSetEq run path hPath).h6iii

/-- Theorem 5.6.1 (companion, conversion): When the equality search tree is finite
and the input sequent is valid, it can be converted to a GEqProofTree
proving the sequent. -/
theorem searchTreeEqN_finite_valid_to_proof {L : Language} {hL : L.hasEquality = true} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeDataEq L hL seq) :
    w.treeDom.IsFinite → sequentValid seq →
    sequentProvableEq hL seq :=
by
  -- REPAIR(T116): proof pending
  sorry

-- ===================================================================
-- Definition 5.6.3 (normalized): searchClosureEqStepN
-- ===================================================================

/-- Definition 5.6.3 (companion, normalized): One step of the equality search
closure. Given a Sequent and SearchStateEq, applies the base
searchClosureStep (which handles type-A/C/D linear decomposition
using the given term list and fresh witness), then injectEqFormulae
(which adds the head of EQ_{j,i} for all i = 0,...,NUMACT to the
antecedent, where j = eqCyclingIndex(RC)).

This is the composed single-step expand for the equality search
procedure. The textbook (Def 5.6.3) describes expand as: for each
non-finished leaf, apply base expansion then inject EQ heads. This
definition captures exactly that composition. -/
noncomputable def searchClosureEqStepN {L : Language} [Countable (Term L)]
    (seq : Sequent L) (terms : List (Term L)) (freshVar : Term L)
    (st : SearchStateEq L) : Sequent L :=
  let base := searchClosureStep seq terms freshVar
  injectEqFormulae st base

-- ===================================================================
-- Definition 5.6.3 (normalized): searchClosureEqN
-- ===================================================================

/-- Definition 5.6.3 (companion, normalized): The equality search closure: iterates
searchClosureEqStepN n times from the initial normalized sequent,
threading SearchStateEq state. At step n:
- Type-C formulas are instantiated with terms enumerate 0,...,n
  (ensuring every term eventually gets used for every type-C formula)
- Type-D formulas get Term.var (freshBase + n) as a fresh witness
- EQ_{j,i} heads are injected via the state at step n

The stateAt function provides the SearchStateEq at each step, which
determines which EQ heads to inject (based on RC cycling) and which
lists to consume (via deleteEqHeads). The caller is responsible for
threading the state correctly (deleting EQ heads and incrementing RC
at the end of each round, as per searchRoundEq). -/
noncomputable def searchClosureEqN {L : Language} [Countable (Term L)]
    (seq : Sequent L) (freshBase : Nat)
    (stateAt : Nat → SearchStateEq L) : Nat → Sequent L
  | 0 => seq
  | n + 1 =>
    let prev := searchClosureEqN seq freshBase stateAt n
    let terms := (List.range (n + 1)).map Countable.enumerate
    searchClosureEqStepN prev terms (Term.var (freshBase + n)) (stateAt n)

-- ===================================================================
-- Definition 5.6.3 (normalized): buildSearchTreeEq — Case 1 helpers
-- ===================================================================

/-- Definition 5.6.3 (companion): `prefix_closed` for the singleton tree
domain used in `buildSearchTreeEq` Case 1 (seq is an axiom). -/
theorem buildSearchTreeEq_case1_treeDom_prefix_closed :
    ∀ u v, (u ++ v) ∈ (fun addr : TreeAddr => addr = []) → u ∈ (fun addr : TreeAddr => addr = []) := by
-- BEGIN PROOF
  intro u v h
  have : u ++ v = [] := h
  exact (List.append_eq_nil_iff.mp this).1

/-- Definition 5.6.3 (companion): `left_sibling_closed` for the singleton
tree domain used in `buildSearchTreeEq` Case 1. -/
theorem buildSearchTreeEq_case1_treeDom_left_sibling_closed :
    ∀ u i, (u ++ [i + 1]) ∈ (fun addr : TreeAddr => addr = []) →
      (u ++ [i]) ∈ (fun addr : TreeAddr => addr = []) := by
-- BEGIN PROOF
  intro u i h
  have := List.append_eq_nil_iff.mp (h : u ++ [i + 1] = [])
  exact absurd this.2 (List.cons_ne_nil _ _)

/-- Definition 5.6.3 (companion): The singleton tree domain used in
`buildSearchTreeEq` Case 1 (seq is an axiom). -/
def buildSearchTreeEq_case1_treeDom : LCS.TreeDomain where
  dom := fun addr => addr = []
  root_mem := rfl
  prefix_closed := buildSearchTreeEq_case1_treeDom_prefix_closed
  left_sibling_closed := buildSearchTreeEq_case1_treeDom_left_sibling_closed

/-- Definition 5.6.3 (companion): Case 1 `axiom_is_leaf` — the root `[]`
has no child `[0]`. -/
theorem buildSearchTreeEq_case1_axiom_is_leaf {L : Language}
    (seq : Sequent L) :
    ∀ (u : TreeAddr) (hu : u ∈ buildSearchTreeEq_case1_treeDom.dom),
      isAxiom ((fun _ _ => seq) u hu) →
      ¬ ((u ++ [0]) ∈ buildSearchTreeEq_case1_treeDom.dom) := by
-- BEGIN PROOF
  intro u hu _ hC
  have : u = [] := hu; subst this
  exact List.cons_ne_nil _ _ (hC : [0] = [])

/-- Definition 5.6.3 (companion): Case 1 `finBranching` — the singleton
tree has no children anywhere. -/
theorem buildSearchTreeEq_case1_finBranching :
    buildSearchTreeEq_case1_treeDom.FinitelyBranching := by
-- BEGIN PROOF
  intro u hu
  have : u = [] := hu; subst this
  exact ⟨0, fun _ _ h => List.cons_ne_nil _ _ (h : [_] = [])⟩

/-- Definition 5.6.3 (companion): Case 1 `path_ant_mono` — vacuous since
no child of `[]` is in the tree. -/
theorem buildSearchTreeEq_case1_path_ant_mono {L : Language}
    (seq : Sequent L) :
    ∀ (u : TreeAddr) (hu : u ∈ buildSearchTreeEq_case1_treeDom.dom) (i : Nat)
      (hc : (u ++ [i]) ∈ buildSearchTreeEq_case1_treeDom.dom) (A : FormulaN L),
      A ∈ ((fun _ _ => seq) u hu).antecedent →
      A ∈ ((fun _ _ => seq) (u ++ [i]) hc).antecedent := by
-- BEGIN PROOF
  intro u hu i hc _A _hA
  have : u = [] := hu; subst this
  exact absurd (hc : [i] = []) (List.cons_ne_nil _ _)

/-- Definition 5.6.3 (companion): Case 1 `path_succ_mono` — vacuous. -/
theorem buildSearchTreeEq_case1_path_succ_mono {L : Language}
    (seq : Sequent L) :
    ∀ (u : TreeAddr) (hu : u ∈ buildSearchTreeEq_case1_treeDom.dom) (i : Nat)
      (hc : (u ++ [i]) ∈ buildSearchTreeEq_case1_treeDom.dom) (B : FormulaN L),
      B ∈ ((fun _ _ => seq) u hu).succedent →
      B ∈ ((fun _ _ => seq) (u ++ [i]) hc).succedent := by
-- BEGIN PROOF
  intro u hu i hc _B _hB
  have : u = [] := hu; subst this
  exact absurd (hc : [i] = []) (List.cons_ne_nil _ _)

/-- Definition 5.6.3 (companion): Case 1 `path_expansion` — no infinite
path exists in the singleton tree, so this is vacuous. -/
theorem buildSearchTreeEq_case1_path_expansion {L : Language} (hL : L.hasEquality = true)
    [Countable (Term L)] (seq : Sequent L) :
    ∀ (f : Nat → Nat) (n : Nat)
      (hPath : ∀ m, (List.ofFn (fun i : Fin m => f i)) ∈ buildSearchTreeEq_case1_treeDom.dom),
      ((fun _ _ => seq) (List.ofFn (fun i : Fin (n + 1) => f i)) (hPath (n + 1))) =
      branchStepEqN ((fun _ _ => seq) (List.ofFn (fun i : Fin n => f i)) (hPath n))
        n (seqMaxBVN seq + 1) (f n)
        ((fun _ _ => SearchStateEq.init hL seq [] [] [])
          (List.ofFn (fun i : Fin n => f i)) (hPath n)) seq := by
-- BEGIN PROOF
  intro f n hPath
  -- The only address in dom is []. ofFn(1) = [f 0] ∉ dom, contradicts hPath 1.
  exfalso
  have h1 := hPath 1
  exact List.cons_ne_nil _ _ (h1 : [f 0] = [])

/-- Definition 5.6.3 (companion): Case 1 `path_eq_refl_injection` —
vacuous (no infinite path). -/
theorem buildSearchTreeEq_case1_path_eq_refl_injection {L : Language}
    (hL : L.hasEquality = true)
    [Countable (Term L)] (seq : Sequent L) :
    ∀ (f : Nat → Nat)
      (hPath : ∀ m, (List.ofFn (fun i : Fin m => f i)) ∈ buildSearchTreeEq_case1_treeDom.dom)
      (t : Term L), t ∈ safeTermsN seq →
      ∃ k, FormulaN.eq_ hL t t ∈
        ((fun _ _ => seq) (List.ofFn (fun i : Fin k => f i)) (hPath k)).antecedent := by
-- BEGIN PROOF
  intro f hPath _ _
  exfalso
  have h1 := hPath 1
  exact List.cons_ne_nil _ _ (h1 : [f 0] = [])

-- ===================================================================
-- Definition 5.6.3 (normalized): buildSearchTreeEq — Case 3 helpers
-- ===================================================================

/-- Definition 5.6.3 (companion): Case 3 fresh-variable base — one
more than the maximum bound variable in `seq`. -/
def buildSearchTreeEq_case3_freshBase {L : Language} (seq : Sequent L) : Nat :=
  seqMaxBVN seq + 1

/-- Definition 5.6.3 (companion): Case 3 initial free-variable indices
extracted from `seq`'s antecedent and succedent. -/
def buildSearchTreeEq_case3_fvIndices {L : Language} (seq : Sequent L) : List Nat :=
  (seq.antecedent ++ seq.succedent).flatMap formulaFreeVarIndices

/-- Definition 5.6.3 (companion): Level-0 generators are the input constants
and free variables. If both are absent, include the least absent variable y₀. -/
noncomputable def buildSearchTreeEq_case3_initialTerms {L : Language}
    (seq : Sequent L) : List (Term L) :=
  LCS.FirstOrder.Gentzen.Search.NoFunction.initialTerms seq

/-- Definition 5.6.3 (companion): Initial state with the function and predicate
symbols of the input reduct and lazy EQ lists over the level-0 term closure. -/
noncomputable def buildSearchTreeEq_case3_initSt {L : Language} (hL : L.hasEquality = true)
    (seq : Sequent L) : SearchStateEq L :=
  SearchStateEq.init hL seq
    ((seq.antecedent ++ seq.succedent).flatMap eqFormulaFunSymbols)
    ((seq.antecedent ++ seq.succedent).flatMap eqFormulaPredSymbols)
    (buildSearchTreeEq_case3_initialTerms seq)

/-- Definition 5.6.3 (companion): Case 3 per-depth search state. -/
noncomputable def buildSearchTreeEq_case3_stateAt {L : Language} (hL : L.hasEquality = true)
    (seq : Sequent L) :
    Nat → SearchStateEq L :=
  stateAt (buildSearchTreeEq_case3_initSt hL seq)

/-- Definition 5.6.3 (companion): The sequent obtained by following a binary
address, before restricting the domain at axiom nodes. -/
noncomputable def buildSearchTreeEq_case3_label {L : Language}
    (hL : L.hasEquality = true) [Countable (Term L)]
    (seq : Sequent L) (addr : TreeAddr) : Sequent L :=
  branchingNodeSeqFEqN seq (buildSearchTreeEq_case3_freshBase seq)
    (fun i => addr.getD i 0) (buildSearchTreeEq_case3_stateAt hL seq) addr.length

/-- Definition 5.6.3 (companion): A binary address is admitted exactly when
none of its proper prefixes labels an axiom. The address itself may label one. -/
def buildSearchTreeEq_case3_admissible {L : Language}
    (hL : L.hasEquality = true) [Countable (Term L)]
    (seq : Sequent L) (addr : TreeAddr) : Prop :=
  (∀ j ∈ addr, j < 2) ∧
    ∀ n < addr.length, ¬ isAxiom (buildSearchTreeEq_case3_label hL seq (addr.take n))

/-- Definition 5.6.3 (companion): The root has no proper prefix. -/
theorem buildSearchTreeEq_case3_treeDom_root_mem {L : Language}
    (hL : L.hasEquality = true) [Countable (Term L)] (seq : Sequent L) :
    buildSearchTreeEq_case3_admissible hL seq [] := by
  constructor
  · intro j hj; cases hj
  · intro n hn; simp at hn

/-- Definition 5.6.3 (companion): Admissible addresses are prefix closed. -/
theorem buildSearchTreeEq_case3_treeDom_prefix_closed {L : Language}
    (hL : L.hasEquality = true) [Countable (Term L)] (seq : Sequent L) :
    ∀ u v, buildSearchTreeEq_case3_admissible hL seq (u ++ v) →
      buildSearchTreeEq_case3_admissible hL seq u := by
  intro u v h
  constructor
  · intro j hj; exact h.1 j (List.mem_append_left v hj)
  · intro n hn
    have hp := h.2 n (by simpa using Nat.lt_add_right v.length hn)
    simpa [List.take_append_of_le_length (Nat.le_of_lt hn)] using hp

/-- Definition 5.6.3 (companion): Siblings have the same proper prefixes,
so the domain is left-sibling closed. -/
theorem buildSearchTreeEq_case3_treeDom_left_sibling_closed {L : Language}
    (hL : L.hasEquality = true) [Countable (Term L)] (seq : Sequent L) :
    ∀ u i, buildSearchTreeEq_case3_admissible hL seq (u ++ [i + 1]) →
      buildSearchTreeEq_case3_admissible hL seq (u ++ [i]) := by
  intro u i h
  constructor
  · intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · exact h.1 j (List.mem_append_left _ hj)
    · have hji := List.mem_singleton.mp hj
      have hi := h.1 (i + 1) (List.mem_append_right u (List.Mem.head _))
      omega
  · intro n hn
    have hn' : n ≤ u.length := by
      simp only [List.length_append, List.length_singleton] at hn
      omega
    have hp := h.2 n (by simpa using hn)
    simpa [List.take_append_of_le_length hn'] using hp

/-- Definition 5.6.3 (companion): The binary tree pruned immediately below
axiom nodes, with labels determined by the input sequent. -/
def buildSearchTreeEq_case3_treeDom {L : Language}
    (hL : L.hasEquality = true) [Countable (Term L)] (seq : Sequent L) :
    LCS.TreeDomain where
  dom := buildSearchTreeEq_case3_admissible hL seq
  root_mem := buildSearchTreeEq_case3_treeDom_root_mem hL seq
  prefix_closed := buildSearchTreeEq_case3_treeDom_prefix_closed hL seq
  left_sibling_closed := buildSearchTreeEq_case3_treeDom_left_sibling_closed hL seq

/-- Definition 5.6.3 (companion): The sequent labeling an admitted address. -/
noncomputable def buildSearchTreeEq_case3_nodeSequent {L : Language}
    (hL : L.hasEquality = true)
    [Countable (Term L)] (seq : Sequent L) (addr : TreeAddr)
    (_ : addr ∈ (buildSearchTreeEq_case3_treeDom hL seq).dom) : Sequent L :=
  buildSearchTreeEq_case3_label hL seq addr

/-- Definition 5.6.3 (companion): Case 3 `root_sequent` — the root's
sequent is `seq` by unfolding. -/
theorem buildSearchTreeEq_case3_root_sequent {L : Language} (hL : L.hasEquality = true)
    [Countable (Term L)] (seq : Sequent L) :
    buildSearchTreeEq_case3_nodeSequent hL seq []
      (buildSearchTreeEq_case3_treeDom hL seq).root_mem = seq := by
-- BEGIN PROOF
  simp [buildSearchTreeEq_case3_nodeSequent, buildSearchTreeEq_case3_label,
    branchingNodeSeqFEqN]

/-- Definition 5.6.3 (companion): An axiom node has no child. -/
theorem buildSearchTreeEq_case3_axiom_is_leaf {L : Language} (hL : L.hasEquality = true)
    [Countable (Term L)] (seq : Sequent L) :
    ∀ (u : TreeAddr) (hu : u ∈ (buildSearchTreeEq_case3_treeDom hL seq).dom),
      isAxiom (buildSearchTreeEq_case3_nodeSequent hL seq u hu) →
      ¬ ((u ++ [0]) ∈ (buildSearchTreeEq_case3_treeDom hL seq).dom) := by
  intro u hu hAx hc
  have hn := hc.2 u.length (by simp)
  exact hn (by simpa [List.take_append_length, buildSearchTreeEq_case3_nodeSequent] using hAx)

/-- Definition 5.6.3 (companion): Each node has at most two children. -/
theorem buildSearchTreeEq_case3_finBranching {L : Language}
    (hL : L.hasEquality = true) [Countable (Term L)] (seq : Sequent L) :
    (buildSearchTreeEq_case3_treeDom hL seq).FinitelyBranching := by
  intro u hu
  exact ⟨2, fun i hi habs => by
    have hlt := habs.1 i (List.mem_append_right u (List.Mem.head _))
    omega⟩

/-- Definition 5.6.3 (companion): Every admitted non-axiom node has a child. -/
theorem buildSearchTreeEq_case3_non_axiom_has_child {L : Language}
    (hL : L.hasEquality = true)
    [Countable (Term L)] (seq : Sequent L) :
    ∀ (u : TreeAddr) (hu : u ∈ (buildSearchTreeEq_case3_treeDom hL seq).dom),
      ¬ isAxiom (buildSearchTreeEq_case3_nodeSequent hL seq u hu) →
      (u ++ [0]) ∈ (buildSearchTreeEq_case3_treeDom hL seq).dom := by
  intro u hu hAx
  constructor
  · intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · exact hu.1 j hj
    · have := List.mem_singleton.mp hj; omega
  · intro n hn
    have hn' : n ≤ u.length := by
      simp only [List.length_append, List.length_singleton] at hn
      omega
    rw [List.take_append_of_le_length hn']
    rcases Nat.lt_or_eq_of_le hn' with hn' | rfl
    · exact hu.2 n hn'
    · simpa [buildSearchTreeEq_case3_nodeSequent] using hAx

/-- Definition 5.6.3 (companion): Case 3 `path_ant_mono` — formulae in
the antecedent at depth `u` propagate to depth `u ++ [i]`. -/
theorem buildSearchTreeEq_case3_path_ant_mono {L : Language} (hL : L.hasEquality = true)
    [Countable (Term L)] (seq : Sequent L) :
    ∀ (u : TreeAddr) (hu : u ∈ (buildSearchTreeEq_case3_treeDom hL seq).dom) (i : Nat)
      (hc : (u ++ [i]) ∈ (buildSearchTreeEq_case3_treeDom hL seq).dom) (A : FormulaN L),
      A ∈ (buildSearchTreeEq_case3_nodeSequent hL seq u hu).antecedent →
      A ∈ (buildSearchTreeEq_case3_nodeSequent hL seq (u ++ [i]) hc).antecedent := by
-- BEGIN PROOF
  intro u _hu i _hc A hA
  show A ∈ (branchingNodeSeqFEqN seq (buildSearchTreeEq_case3_freshBase seq)
    (fun m => (u ++ [i]).getD m 0) (buildSearchTreeEq_case3_stateAt hL seq)
    (u ++ [i]).length).antecedent
  rw [show (u ++ [i]).length = u.length + 1 from by simp]
  simp only [branchingNodeSeqFEqN]
  have heq : branchingNodeSeqFEqN seq (buildSearchTreeEq_case3_freshBase seq)
      (fun m => (u ++ [i]).getD m 0) (buildSearchTreeEq_case3_stateAt hL seq) u.length =
    branchingNodeSeqFEqN seq (buildSearchTreeEq_case3_freshBase seq)
      (fun m => u.getD m 0) (buildSearchTreeEq_case3_stateAt hL seq) u.length := by
    apply branchingNodeSeqFEqN_ext
    intro m hm; simp [List.getD, List.getElem?_append_left hm]
  rw [heq]
  exact branchStepEqN_ant_mono _ u.length (buildSearchTreeEq_case3_freshBase seq) _
    (buildSearchTreeEq_case3_stateAt hL seq u.length) seq A hA

/-- Definition 5.6.3 (companion): Case 3 `path_succ_mono`. -/
theorem buildSearchTreeEq_case3_path_succ_mono {L : Language} (hL : L.hasEquality = true)
    [Countable (Term L)] (seq : Sequent L) :
    ∀ (u : TreeAddr) (hu : u ∈ (buildSearchTreeEq_case3_treeDom hL seq).dom) (i : Nat)
      (hc : (u ++ [i]) ∈ (buildSearchTreeEq_case3_treeDom hL seq).dom) (B : FormulaN L),
      B ∈ (buildSearchTreeEq_case3_nodeSequent hL seq u hu).succedent →
      B ∈ (buildSearchTreeEq_case3_nodeSequent hL seq (u ++ [i]) hc).succedent := by
-- BEGIN PROOF
  intro u _hu i _hc B hB
  show B ∈ (branchingNodeSeqFEqN seq (buildSearchTreeEq_case3_freshBase seq)
    (fun m => (u ++ [i]).getD m 0) (buildSearchTreeEq_case3_stateAt hL seq)
    (u ++ [i]).length).succedent
  rw [show (u ++ [i]).length = u.length + 1 from by simp]
  simp only [branchingNodeSeqFEqN]
  have heq : branchingNodeSeqFEqN seq (buildSearchTreeEq_case3_freshBase seq)
      (fun m => (u ++ [i]).getD m 0) (buildSearchTreeEq_case3_stateAt hL seq) u.length =
    branchingNodeSeqFEqN seq (buildSearchTreeEq_case3_freshBase seq)
      (fun m => u.getD m 0) (buildSearchTreeEq_case3_stateAt hL seq) u.length := by
    apply branchingNodeSeqFEqN_ext
    intro m hm; simp [List.getD, List.getElem?_append_left hm]
  rw [heq]
  exact branchStepEqN_succ_mono _ u.length (buildSearchTreeEq_case3_freshBase seq) _
    (buildSearchTreeEq_case3_stateAt hL seq u.length) seq B hB

/-- Definition 5.6.3 (companion): Case 3 `path_expansion`. -/
theorem buildSearchTreeEq_case3_path_expansion {L : Language} (hL : L.hasEquality = true)
    [Countable (Term L)] (seq : Sequent L) :
    ∀ (f : Nat → Nat) (n : Nat)
      (hPath : ∀ m, (List.ofFn (fun i : Fin m => f i)) ∈ (buildSearchTreeEq_case3_treeDom hL seq).dom),
      buildSearchTreeEq_case3_nodeSequent hL seq
        (List.ofFn (fun i : Fin (n + 1) => f i)) (hPath (n + 1)) =
      branchStepEqN (buildSearchTreeEq_case3_nodeSequent hL seq
          (List.ofFn (fun i : Fin n => f i)) (hPath n))
        n (buildSearchTreeEq_case3_freshBase seq) (f n)
        ((fun addr _ => buildSearchTreeEq_case3_stateAt hL seq addr.length)
          (List.ofFn (fun i : Fin n => f i)) (hPath n)) seq := by
-- BEGIN PROOF
  intro f n hPath
  -- DEBT(case-three equality search path expansion equation not established)
  sorry

/-- Definition 5.6.3 (companion): Case 3 `path_eq_refl_injection`. -/
theorem buildSearchTreeEq_case3_path_eq_refl_injection {L : Language}
    (hL : L.hasEquality = true)
    [Countable (Term L)] (seq : Sequent L) :
    ∀ (f : Nat → Nat)
      (hPath : ∀ m, (List.ofFn (fun i : Fin m => f i)) ∈ (buildSearchTreeEq_case3_treeDom hL seq).dom)
      (t : Term L), t ∈ safeTermsN seq →
      ∃ k, FormulaN.eq_ hL t t ∈
        (buildSearchTreeEq_case3_nodeSequent hL seq
          (List.ofFn (fun i : Fin k => f i)) (hPath k)).antecedent := by
-- BEGIN PROOF
  intro f hPath t ht_safe
  -- DEBT(eventual reflexivity injection for each safe term along equality search paths not established)
  sorry

/-- Definition 5.6.3 (companion): If the pruned tree is finite and the
input sequent is valid, the input has a G_= proof. -/
theorem buildSearchTreeEq_case3_provable_if_finite_eq {L : Language}
    (hL : L.hasEquality = true)
    [Countable (Term L)] (seq : Sequent L)
    (hFin : (buildSearchTreeEq_case3_treeDom hL seq).IsFinite) (_ : sequentValid seq) :
    sequentProvableEq hL seq := by
  -- REPAIR(T111): proof pending
  sorry

-- ===================================================================
-- Definition 5.6.3 (normalized): buildSearchTreeEq
-- ===================================================================

/-- Definition 5.6.3 (companion, normalized): Build equality-search tree
data and its structural invariants. An axiom input gives a single leaf;
a non-axiom input gives the binary tree labeled by `branchingNodeSeqFEqN`,
pruned below every axiom node. Path Hintikka properties are stated separately. -/
noncomputable def buildSearchTreeEq {L : Language} (hL : L.hasEquality = true)
    [Countable (Term L)]
    (seq : Sequent L) (hFree : noFreeOccursBound seq) :
    SearchTreeDataEq L hL seq := by
  by_cases hAxiom : isAxiom seq
  · -- CASE 1: seq is an axiom. Single-leaf tree. 0 sorries.
    exact {
      treeDom := buildSearchTreeEq_case1_treeDom
      nodeSequent := fun _ _ => seq
      nodeStateEq := fun _ _ => SearchStateEq.init hL seq [] [] []
      root_sequent := rfl
      axiom_is_leaf := buildSearchTreeEq_case1_axiom_is_leaf seq
      finBranching := buildSearchTreeEq_case1_finBranching
      non_axiom_has_child := fun _ _ h => absurd hAxiom h
      path_ant_mono := buildSearchTreeEq_case1_path_ant_mono seq
      path_succ_mono := buildSearchTreeEq_case1_path_succ_mono seq
      freshBase := seqMaxBVN seq + 1
      freshBase_bound := fun v A hA hv => seqBV_lt_seqMaxBVN seq v A hA hv
      path_expansion := buildSearchTreeEq_case1_path_expansion hL seq }
  · -- CASE 3: seq is NOT an axiom.
    -- BRANCHING tree using branchingNodeSeqFEqN. At each node,
    -- type-A/C/D formulae are decomposed linearly (via
    -- searchClosureEqStepN), type-B formulae create two children
    -- (comp1 at child 0, comp2 at child 1), and equality axiom
    -- instances are injected from EQ_{j,i} via injectEqFormulae.
    exact {
      treeDom := buildSearchTreeEq_case3_treeDom hL seq
      nodeSequent := buildSearchTreeEq_case3_nodeSequent hL seq
      nodeStateEq := fun addr _ =>
        buildSearchTreeEq_case3_stateAt hL seq addr.length
      root_sequent := buildSearchTreeEq_case3_root_sequent hL seq
      axiom_is_leaf := buildSearchTreeEq_case3_axiom_is_leaf hL seq
      finBranching := buildSearchTreeEq_case3_finBranching hL seq
      non_axiom_has_child := buildSearchTreeEq_case3_non_axiom_has_child hL seq
      path_ant_mono := buildSearchTreeEq_case3_path_ant_mono hL seq
      path_succ_mono := buildSearchTreeEq_case3_path_succ_mono hL seq
      freshBase := buildSearchTreeEq_case3_freshBase seq
      freshBase_bound := fun v A hA hv => seqBV_lt_seqMaxBVN seq v A hA hv
      path_expansion := buildSearchTreeEq_case3_path_expansion hL seq
      }

-- ===================================================================
-- Theorem 5.6.1: searchCompletenessEqValid (Part i)
-- ===================================================================

/-- Theorem 5.6.1 (companion, Part i): valid implies G_=-provable.
Since GEqProofTree is now indexed by its conclusion, we return
`Nonempty (GEqProofTree seq)`. -/
theorem searchCompletenessEqValid {L : Language} (hL : L.hasEquality = true)
    [Countable (Term L)]
    (seq : Sequent L)
    (hFree : noFreeOccursBound seq)
    (hValid : sequentValid seq) :
    Nonempty (GEqProofTree hL seq) := by
  -- REPAIR(T116): proof pending
  sorry

-- ===================================================================
-- Theorem 5.6.1 (normalized): goedelExtendedCompletenessGEq
-- ===================================================================

/-- Theorem 5.6.1: Goedel extended completeness theorem for system G_=. A
sequent in which no variable occurs both free and bound is valid if and only if it is G_=-provable. -/
theorem goedelExtendedCompletenessGEq {L : Language} (hL : L.hasEquality = true)
    [Countable (Term L)]
    (seq : Sequent L) (hFree : noFreeOccursBound seq) :
    sequentValid seq ↔ sequentProvableEq hL seq := by
  constructor
  · exact searchCompletenessEqValid hL seq hFree
  · exact soundnessGEq hL seq

-- ===================================================================
-- Theorem 5.6.1 (normalized): eqSearch_valid_yields_provableN
-- ===================================================================

/-- Theorem 5.6.1 (companion, normalized): The equality search procedure on a
valid Sequent produces a G= proof tree. -/
theorem eqSearch_valid_yields_provableN {L : Language} (hL : L.hasEquality = true)
    [Countable (Term L)]
    (seq : Sequent L)
    (hFree : noFreeOccursBound seq)
    (hValid : sequentValid seq) :
    sequentProvableEq hL seq :=
  searchCompletenessEqValid hL seq hFree hValid

end LCS.FirstOrder.Equality.Completeness
end

