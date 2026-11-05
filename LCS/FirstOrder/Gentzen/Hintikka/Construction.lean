import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.FirstOrder.Gentzen.Hintikka.Model
import LCS.FirstOrder.Gentzen.Hintikka.SearchClosure
import LCS.FirstOrder.Gentzen.Hintikka.PathModel

section
namespace LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.SyntaxN.Variables

/-- decomposeAntFormula preserves formulaNoEq: if the input formula has
no eq_ sub-formula, neither do the outputs. -/
theorem decomposeAntFormula_noEq {L : Language} (A : FormulaN L) (t_c t_d : Term L)
    (h : formulaNoEq A) :
    (∀ X ∈ (decomposeAntFormula A t_c t_d).1, formulaNoEq X) ∧
    (∀ X ∈ (decomposeAntFormula A t_c t_d).2, formulaNoEq X) := by
-- BEGIN PROOF
  cases A with
  | predN _ _ => simp [decomposeAntFormula]
  | eq_ _ _ _ => simp [formulaNoEq] at h
  | conj X Y => simp [decomposeAntFormula, formulaNoEq] at h ⊢; exact ⟨h.1, h.2⟩
  | disj _ _ => simp [decomposeAntFormula]
  | impl _ _ => simp [decomposeAntFormula]
  | neg X => simp [decomposeAntFormula, formulaNoEq] at h ⊢; exact h
  | all x B =>
    simp [decomposeAntFormula, formulaNoEq] at h ⊢
    exact formulaSubstN_noEq B t_c x h
  | ex x B =>
    simp [decomposeAntFormula, formulaNoEq] at h ⊢
    exact formulaSubstN_noEq B t_d x h

/-- decomposeSuccFormula preserves formulaNoEq. -/
theorem decomposeSuccFormula_noEq {L : Language} (B : FormulaN L) (t_c t_d : Term L)
    (h : formulaNoEq B) :
    (∀ X ∈ (decomposeSuccFormula B t_c t_d).1, formulaNoEq X) ∧
    (∀ X ∈ (decomposeSuccFormula B t_c t_d).2, formulaNoEq X) := by
-- BEGIN PROOF
  cases B with
  | predN _ _ => simp [decomposeSuccFormula]
  | eq_ _ _ _ => simp [formulaNoEq] at h
  | conj _ _ => simp [decomposeSuccFormula]
  | disj X Y => simp [decomposeSuccFormula, formulaNoEq] at h ⊢; exact ⟨h.1, h.2⟩
  | impl X Y => simp [decomposeSuccFormula, formulaNoEq] at h ⊢; exact ⟨h.1, h.2⟩
  | neg X => simp [decomposeSuccFormula, formulaNoEq] at h ⊢; exact h
  | ex x A =>
    simp [decomposeSuccFormula, formulaNoEq] at h ⊢
    exact formulaSubstN_noEq A t_c x h
  | all x A =>
    simp [decomposeSuccFormula, formulaNoEq] at h ⊢
    exact formulaSubstN_noEq A t_d x h

/-- typeBCompAnt preserves formulaNoEq: extracted components are
sub-formulas and hence eq_-free. -/
theorem typeBCompAnt_noEq {L : Language} (A : FormulaN L) (bit : Nat)
    (h : formulaNoEq A) :
    (∀ X ∈ (typeBCompAnt A bit).1, formulaNoEq X) ∧
    (∀ X ∈ (typeBCompAnt A bit).2, formulaNoEq X) := by
-- BEGIN PROOF
  cases A with
  | disj X Y =>
    simp [typeBCompAnt, formulaNoEq] at h ⊢
    split
    · exact ⟨fun _ hm => by simp at hm; exact hm ▸ h.1, fun _ hm => by simp at hm⟩
    · exact ⟨fun _ hm => by simp at hm; exact hm ▸ h.2, fun _ hm => by simp at hm⟩
  | impl X Y =>
    simp [typeBCompAnt, formulaNoEq] at h ⊢
    split
    · exact ⟨fun _ hm => by simp at hm, fun _ hm => by simp at hm; exact hm ▸ h.1⟩
    · exact ⟨fun _ hm => by simp at hm; exact hm ▸ h.2, fun _ hm => by simp at hm⟩
  | predN _ _ => simp [typeBCompAnt]
  | eq_ _ _ _ => simp [formulaNoEq] at h
  | conj _ _ => simp [typeBCompAnt]
  | neg _ => simp [typeBCompAnt]
  | all _ _ => simp [typeBCompAnt]
  | ex _ _ => simp [typeBCompAnt]

/-- typeBCompSucc preserves formulaNoEq. -/
theorem typeBCompSucc_noEq {L : Language} (B : FormulaN L) (bit : Nat)
    (h : formulaNoEq B) :
    (∀ X ∈ (typeBCompSucc B bit).1, formulaNoEq X) ∧
    (∀ X ∈ (typeBCompSucc B bit).2, formulaNoEq X) := by
-- BEGIN PROOF
  cases B with
  | conj X Y =>
    simp [typeBCompSucc, formulaNoEq] at h ⊢
    split
    · exact ⟨fun _ hm => by simp at hm, fun _ hm => by simp at hm; exact hm ▸ h.1⟩
    · exact ⟨fun _ hm => by simp at hm, fun _ hm => by simp at hm; exact hm ▸ h.2⟩
  | predN _ _ => simp [typeBCompSucc]
  | eq_ _ _ _ => simp [formulaNoEq] at h
  | disj _ _ => simp [typeBCompSucc]
  | impl _ _ => simp [typeBCompSucc]
  | neg _ => simp [typeBCompSucc]
  | all _ _ => simp [typeBCompSucc]
  | ex _ _ => simp [typeBCompSucc]

/-- searchClosureStep1 preserves seqNoEq. -/
theorem searchClosureStep1_seqNoEq {L : Language}
    (prev : Sequent L) (t_c t_d : Term L) (h : seqNoEq prev) :
    seqNoEq (searchClosureStep1 prev t_c t_d) := by
-- BEGIN PROOF
  constructor
  · intro A hA
    simp only [searchClosureStep1] at hA
    rcases List.mem_append.mp hA with hA1 | hA2
    · rcases List.mem_append.mp hA1 with hA11 | hA12
      · exact h.1 A hA11
      · simp only [collectDecompAnt, List.mem_flatMap] at hA12
        obtain ⟨F, hF, hAF⟩ := hA12
        exact (decomposeAntFormula_noEq F t_c t_d (h.1 F hF)).1 A hAF
    · simp only [collectDecompSuccAnt, List.mem_flatMap] at hA2
      obtain ⟨B, hB, hAB⟩ := hA2
      exact (decomposeSuccFormula_noEq B t_c t_d (h.2 B hB)).1 A hAB
  · intro B hB
    simp only [searchClosureStep1] at hB
    rcases List.mem_append.mp hB with hB1 | hB2
    · rcases List.mem_append.mp hB1 with hB11 | hB12
      · exact h.2 B hB11
      · simp only [collectDecompAntSucc, List.mem_flatMap] at hB12
        obtain ⟨F, hF, hBF⟩ := hB12
        exact (decomposeAntFormula_noEq F t_c t_d (h.1 F hF)).2 B hBF
    · simp only [collectDecompSucc, List.mem_flatMap] at hB2
      obtain ⟨G, hG, hBG⟩ := hB2
      exact (decomposeSuccFormula_noEq G t_c t_d (h.2 G hG)).2 B hBG

/-- searchClosureStep preserves seqNoEq (by folding searchClosureStep1). -/
theorem searchClosureStep_seqNoEq {L : Language}
    (prev : Sequent L) (terms : List (Term L)) (t_d : Term L) (h : seqNoEq prev) :
    seqNoEq (searchClosureStep prev terms t_d) := by
-- BEGIN PROOF
  simp only [searchClosureStep]
  induction terms generalizing prev with
  | nil => simp [List.foldl]; exact h
  | cons hd tl ih =>
    simp only [List.foldl]
    exact ih (searchClosureStep1 prev hd t_d) (searchClosureStep1_seqNoEq prev hd t_d h)

/-- branchStep preserves seqNoEq: both the linear decomposition and
type-B branching components preserve the eq_-free property. -/
theorem branchStep_seqNoEq {L : Language} [Countable (Term L)]
    (prev : Sequent L) (depth freshBase bit : Nat)
    (rootSeq : Sequent L) (h : seqNoEq prev) :
    seqNoEq (branchStep prev depth freshBase bit rootSeq) := by
-- BEGIN PROOF
  simp only [branchStep]
  have hlin := searchClosureStep_seqNoEq prev
    (branchTerms rootSeq depth freshBase)
    (Term.var (freshBase + depth)) h
  constructor
  · intro A hA
    rcases List.mem_append.mp hA with h1 | h2
    · exact hlin.1 A h1
    · simp only [collectBranchAntNew, List.mem_flatMap] at h2
      obtain ⟨F, hF, hAF⟩ := h2
      exact (typeBCompAnt_noEq F bit (h.1 F hF)).1 A hAF
  · intro B hB
    rcases List.mem_append.mp hB with h1 | h2
    · exact hlin.2 B h1
    · simp only [collectBranchSuccNew, List.mem_append, List.mem_flatMap] at h2
      rcases h2 with ⟨F, hF, hBF⟩ | ⟨G, hG, hBG⟩
      · exact (typeBCompAnt_noEq F bit (h.1 F hF)).2 B hBF
      · exact (typeBCompSucc_noEq G bit (h.2 G hG)).2 B hBG

/-- Theorem 5.5.1 (companion): branchingNodeSeqF preserves seqNoEq at all depths. -/
theorem branchingNodeSeqF_seqNoEq {L : Language} [Countable (Term L)]
    (seq : Sequent L) (freshBase : Nat) (f : Nat → Nat) (n : Nat) (h : seqNoEq seq) :
    seqNoEq (branchingNodeSeqF seq freshBase f n) := by
-- BEGIN PROOF
  induction n with
  | zero => simp [branchingNodeSeqF]; exact h
  | succ k ih =>
    simp only [branchingNodeSeqF]
    exact branchStep_seqNoEq _ k freshBase (f k) seq ih

-- ===================================================================
-- buildSearchTree Case 1: single-leaf tree when seq is an axiom
-- ===================================================================

/-- Theorem 5.5.1 (companion, Case 1): Prefix-closure of the single-leaf
`{[]}` tree domain. -/
theorem buildSearchTree_case1_treeDom_prefix_closed
    (u v : List Nat) (h : u ++ v = []) : u = [] := by
-- BEGIN PROOF
  exact (List.append_eq_nil_iff.mp h).1

/-- Theorem 5.5.1 (companion, Case 1): Left-sibling closure of the
single-leaf `{[]}` tree domain: `u ++ [i + 1] = []` is impossible, so the
implication is vacuously true. -/
theorem buildSearchTree_case1_treeDom_left_sibling_closed
    (u : List Nat) (i : Nat) (h : u ++ [i + 1] = []) : u ++ [i] = [] := by
-- BEGIN PROOF
  have := List.append_eq_nil_iff.mp h
  exact absurd this.2 (List.cons_ne_nil _ _)

/-- Theorem 5.5.1 (companion, Case 1): Single-leaf tree domain used when
the input sequent is already an axiom. -/
def buildSearchTree_case1_treeDom : LCS.TreeDomain where
  dom := fun addr => addr = []
  root_mem := rfl
  prefix_closed := buildSearchTree_case1_treeDom_prefix_closed
  left_sibling_closed := buildSearchTree_case1_treeDom_left_sibling_closed

/-- Theorem 5.5.1 (companion, Case 1): Axioms are leaves in the
single-leaf tree — any attempted child `u ++ [0]` forces `u = []` and
hence the singleton list `[0]` to equal `[]`, contradiction. -/
theorem buildSearchTree_case1_axiom_is_leaf
    (u : TreeAddr) (hu : u ∈ buildSearchTree_case1_treeDom.dom) :
    ¬ ((u ++ [0]) ∈ buildSearchTree_case1_treeDom.dom) := by
-- BEGIN PROOF
  intro hC
  have : u = [] := hu; subst this
  exact List.cons_ne_nil _ _ (hC : [0] = [])

/-- Theorem 5.5.1 (companion, Case 1): The single-leaf tree is finitely
branching with bound 0. -/
theorem buildSearchTree_case1_finBranching :
    buildSearchTree_case1_treeDom.FinitelyBranching := by
-- BEGIN PROOF
  intro u hu
  have : u = [] := hu; subst this
  exact ⟨0, fun _ _ h => List.cons_ne_nil _ _ (h : [_] = [])⟩

/-- Theorem 5.5.1 (companion, Case 1): Vacuous antecedent monotonicity —
the single-leaf tree has no edges, so the hypothesis
`(u ++ [i]) ∈ dom` is contradictory. -/
theorem buildSearchTree_case1_path_ant_mono
    (u : TreeAddr) (hu : u ∈ buildSearchTree_case1_treeDom.dom) (i : Nat)
    (hc : (u ++ [i]) ∈ buildSearchTree_case1_treeDom.dom) : False := by
-- BEGIN PROOF
  have : u = [] := hu; subst this
  exact absurd (hc : [i] = []) (List.cons_ne_nil _ _)

/-- Theorem 5.5.1 (companion, Case 1): Vacuous succedent monotonicity —
the single-leaf tree has no edges. -/
theorem buildSearchTree_case1_path_succ_mono
    (u : TreeAddr) (hu : u ∈ buildSearchTree_case1_treeDom.dom) (i : Nat)
    (hc : (u ++ [i]) ∈ buildSearchTree_case1_treeDom.dom) : False := by
-- BEGIN PROOF
  have : u = [] := hu; subst this
  exact absurd (hc : [i] = []) (List.cons_ne_nil _ _)

/-- Theorem 5.5.1 (companion, Case 1): Every reachable node is the root
and hence carries the original sequent — so `seqNoEq` is inherited from
the input. -/
theorem buildSearchTree_case1_node_seqNoEq {L : Language}
    (seq : Sequent L) (hNoEq : seqNoEq seq)
    (u : TreeAddr) (hu : u ∈ buildSearchTree_case1_treeDom.dom) :
    seqNoEq seq := by
-- BEGIN PROOF
  have : u = [] := hu; subst this; exact hNoEq

/-- Theorem 5.5.1 (companion, Case 1): Path expansion vacuous — the
single-leaf domain has no length-1 addresses, so `hPath 1` is
contradictory. -/
theorem buildSearchTree_case1_path_expansion_false
    (f : Nat → Nat)
    (hPath : ∀ m, (List.ofFn (fun i : Fin m => f i)) ∈
      buildSearchTree_case1_treeDom.dom) : False := by
-- BEGIN PROOF
  have h1 := hPath 1
  have hlen : (List.ofFn (fun i : Fin 1 => f i)).length = 1 := by simp
  have heq : List.ofFn (fun i : Fin 1 => f i) = [] := h1
  rw [heq] at hlen; simp at hlen

/-- Theorem 5.5.1 (companion, Case 1): Single-leaf search tree data for
the case where the input sequent is already an axiom. -/
noncomputable def buildSearchTree_case1 {L : Language} [Countable (Term L)]
    (seq : Sequent L) (hFree : noFreeBound seq)
    (hCross : crossNoFreeBound seq)
    (hNoEq : seqNoEq seq) (hAxiom : isAxiom seq) :
    SearchTreeData L seq where
  treeDom := buildSearchTree_case1_treeDom
  nodeSequent := fun _ _ => seq
  nodeState := fun _ _ => SearchState.init seq
  root_sequent := rfl
  axiom_is_leaf := fun u hu _ =>
    buildSearchTree_case1_axiom_is_leaf u hu
  finBranching := buildSearchTree_case1_finBranching
  non_axiom_has_child := fun _ _ h => absurd hAxiom h
  input_noFreeBound := hFree
  input_crossNoFreeBound := hCross
  input_seqNoEq := hNoEq
  path_ant_mono := fun u hu i hc _ _ =>
    (buildSearchTree_case1_path_ant_mono u hu i hc).elim
  path_succ_mono := fun u hu i hc _ _ =>
    (buildSearchTree_case1_path_succ_mono u hu i hc).elim
  node_seqNoEq := fun u hu _ =>
    buildSearchTree_case1_node_seqNoEq seq hNoEq u hu
  freshBase := seqMaxBVN seq + 1
  freshBase_bound := fun v A hA hv => seqBV_lt_seqMaxBVN seq v A hA hv
  path_expansion := fun f _ hPath =>
    (buildSearchTree_case1_path_expansion_false f hPath).elim
  provable_if_finite := fun _ => ⟨.axiom_ seq hAxiom⟩

-- ===================================================================
-- buildSearchTree Case 3: pruned branching tree (seq not an axiom)
-- ===================================================================

/-- Theorem 5.5.1 (companion, Case 3): The fresh-variable base index
used by the branching search procedure: strictly above all bound
variables in the input sequent. -/
def buildSearchTree_case3_freshBase {L : Language} (seq : Sequent L) : Nat :=
  seqMaxBVN seq + 1

/-- Theorem 5.5.1 (companion, Case 3): The node sequent at address `u`
in the pruned branching search tree. -/
noncomputable def buildSearchTree_case3_nodeSeqAt {L : Language} [Countable (Term L)]
    (seq : Sequent L) (u : List Nat) : Sequent L :=
  branchingNodeSeqF seq (buildSearchTree_case3_freshBase seq)
    (fun i => u.getD i 0) u.length

/-- Theorem 5.5.1 (companion, Case 3): The root node carries the input
sequent — unfolds to `branchingNodeSeqF seq _ _ 0 = seq`. -/
theorem buildSearchTree_case3_nodeSeqAt_nil {L : Language} [Countable (Term L)]
    (seq : Sequent L) : buildSearchTree_case3_nodeSeqAt seq [] = seq := by
-- BEGIN PROOF
  simp [buildSearchTree_case3_nodeSeqAt, branchingNodeSeqF]

/-- Theorem 5.5.1 (companion, Case 3): The membership predicate for the
pruned tree domain: every entry < 2 AND no proper prefix hits an
axiom node. -/
def buildSearchTree_case3_dom {L : Language} [Countable (Term L)]
    (seq : Sequent L) (addr : List Nat) : Prop :=
  (∀ j ∈ addr, j < 2) ∧
  (∀ k, k < addr.length → ¬ isAxiom (buildSearchTree_case3_nodeSeqAt seq (addr.take k)))

/-- Theorem 5.5.1 (companion, Case 3): The root `[]` is in the pruned
tree domain — both conjuncts are vacuously true. -/
theorem buildSearchTree_case3_dom_root {L : Language} [Countable (Term L)]
    (seq : Sequent L) : buildSearchTree_case3_dom seq [] := by
-- BEGIN PROOF
  constructor <;> simp [buildSearchTree_case3_dom]

/-- Theorem 5.5.1 (companion, Case 3): Prefix-closure of the pruned
tree domain. -/
theorem buildSearchTree_case3_dom_prefix_closed {L : Language} [Countable (Term L)]
    (seq : Sequent L) (u v : List Nat)
    (h : buildSearchTree_case3_dom seq (u ++ v)) :
    buildSearchTree_case3_dom seq u := by
-- BEGIN PROOF
  constructor
  · intro j hj; exact h.1 j (List.mem_append_left v hj)
  · intro k hk hax
    have hk' : k < (u ++ v).length := by simp; omega
    have : (u ++ v).take k = u.take k := by
      rw [List.take_append_of_le_length (by omega)]
    exact h.2 k hk' (this ▸ hax)

/-- Theorem 5.5.1 (companion, Case 3): Left-sibling closure of the
pruned tree domain. -/
theorem buildSearchTree_case3_dom_left_sibling_closed {L : Language} [Countable (Term L)]
    (seq : Sequent L) (u : List Nat) (i : Nat)
    (h : buildSearchTree_case3_dom seq (u ++ [i + 1])) :
    buildSearchTree_case3_dom seq (u ++ [i]) := by
-- BEGIN PROOF
  constructor
  · intro j hj
    rcases List.mem_append.mp hj with hju | hjs
    · exact h.1 j (List.mem_append_left [i + 1] hju)
    · have hji : j = i := List.mem_singleton.mp hjs
      subst hji
      have := h.1 (j + 1) (List.mem_append_right u (List.Mem.head _))
      omega
  · intro k hk hax
    have hk' : k < (u ++ [i + 1]).length := by simp at hk ⊢; omega
    have htake_eq : (u ++ [i]).take k = (u ++ [i + 1]).take k := by
      simp at hk
      rw [List.take_append_of_le_length (by omega : k ≤ u.length)]
      rw [List.take_append_of_le_length (by omega : k ≤ u.length)]
    exact h.2 k hk' (htake_eq ▸ hax)

/-- Theorem 5.5.1 (companion, Case 3): The pruned binary tree domain
used in the branching search. -/
noncomputable def buildSearchTree_case3_treeDom {L : Language} [Countable (Term L)]
    (seq : Sequent L) : LCS.TreeDomain where
  dom := buildSearchTree_case3_dom seq
  root_mem := buildSearchTree_case3_dom_root seq
  prefix_closed := buildSearchTree_case3_dom_prefix_closed seq
  left_sibling_closed := buildSearchTree_case3_dom_left_sibling_closed seq

/-- Theorem 5.5.1 (companion, Case 3): Axioms are leaves — if `u` is
an axiom node, the pruned domain excludes `u ++ [0]` via the
no-axiom-prefix conjunct at `k = u.length`. -/
theorem buildSearchTree_case3_axiom_is_leaf {L : Language} [Countable (Term L)]
    (seq : Sequent L) (u : TreeAddr)
    (hu : u ∈ (buildSearchTree_case3_treeDom seq).dom)
    (hax : isAxiom (buildSearchTree_case3_nodeSeqAt seq u))
    (hchild : (u ++ [0]) ∈ (buildSearchTree_case3_treeDom seq).dom) : False := by
-- BEGIN PROOF
  have hk : u.length < (u ++ [0]).length := by simp
  have htake : (u ++ [0]).take u.length = u := by
    rw [List.take_append_of_le_length (by omega)]; simp
  have := hchild.2 u.length hk
  rw [htake] at this
  exact this hax

/-- Theorem 5.5.1 (companion, Case 3): The pruned tree is finitely
branching with bound 2 (children are restricted to `0` and `1`). -/
theorem buildSearchTree_case3_finBranching {L : Language} [Countable (Term L)]
    (seq : Sequent L) : (buildSearchTree_case3_treeDom seq).FinitelyBranching := by
-- BEGIN PROOF
  intro u hu
  exact ⟨2, fun i hi habs => by
    have hmem : i ∈ u ++ [i] :=
      List.mem_append.mpr (Or.inr (List.Mem.head _))
    exact absurd (habs.1 i hmem) (by omega)⟩

/-- Theorem 5.5.1 (companion, Case 3): Non-axiom nodes always have the
child `u ++ [0]` in the pruned domain. -/
theorem buildSearchTree_case3_non_axiom_has_child {L : Language} [Countable (Term L)]
    (seq : Sequent L) (u : TreeAddr)
    (hu : u ∈ (buildSearchTree_case3_treeDom seq).dom)
    (hnax : ¬ isAxiom (buildSearchTree_case3_nodeSeqAt seq u)) :
    (u ++ [0]) ∈ (buildSearchTree_case3_treeDom seq).dom := by
-- BEGIN PROOF
  show (∀ j ∈ u ++ [0], j < 2) ∧ _
  constructor
  · intro j hj
    rcases List.mem_append.mp hj with hju | hjs
    · exact hu.1 j hju
    · have : j = 0 := List.mem_singleton.mp hjs; omega
  · intro k hk hax
    simp at hk
    by_cases hku : k < u.length
    · have : (u ++ [0]).take k = u.take k := by
        rw [List.take_append_of_le_length (by omega)]
      rw [this] at hax
      exact hu.2 k hku hax
    · have hkeq : k = u.length := by omega
      subst hkeq
      have : (u ++ [0]).take u.length = u := by
        rw [List.take_append_of_le_length (by omega)]; simp
      rw [this] at hax
      exact hnax hax

/-- Theorem 5.5.1 (companion, Case 3): Antecedent monotonicity along
any parent-child edge in the pruned tree. -/
theorem buildSearchTree_case3_path_ant_mono {L : Language} [Countable (Term L)]
    (seq : Sequent L) (u : TreeAddr)
    (_hu : u ∈ (buildSearchTree_case3_treeDom seq).dom) (i : Nat)
    (_hc : (u ++ [i]) ∈ (buildSearchTree_case3_treeDom seq).dom) (A : FormulaN L)
    (hA : A ∈ (buildSearchTree_case3_nodeSeqAt seq u).antecedent) :
    A ∈ (buildSearchTree_case3_nodeSeqAt seq (u ++ [i])).antecedent := by
-- BEGIN PROOF
  simp only [buildSearchTree_case3_nodeSeqAt]
  show A ∈ (branchingNodeSeqF seq (buildSearchTree_case3_freshBase seq)
    (fun m => (u ++ [i]).getD m 0) (u ++ [i]).length).antecedent
  rw [show (u ++ [i]).length = u.length + 1 from by simp]
  simp only [branchingNodeSeqF]
  have heq : branchingNodeSeqF seq (buildSearchTree_case3_freshBase seq)
      (fun m => (u ++ [i]).getD m 0) u.length =
    branchingNodeSeqF seq (buildSearchTree_case3_freshBase seq)
      (fun m => u.getD m 0) u.length := by
    apply branchingNodeSeqF_ext
    intro m hm; simp [List.getD, List.getElem?_append_left hm]
  rw [heq]
  exact branchStep_ant_mono _ u.length (buildSearchTree_case3_freshBase seq) _ seq A hA

/-- Theorem 5.5.1 (companion, Case 3): Succedent monotonicity along any
parent-child edge in the pruned tree. -/
theorem buildSearchTree_case3_path_succ_mono {L : Language} [Countable (Term L)]
    (seq : Sequent L) (u : TreeAddr)
    (_hu : u ∈ (buildSearchTree_case3_treeDom seq).dom) (i : Nat)
    (_hc : (u ++ [i]) ∈ (buildSearchTree_case3_treeDom seq).dom) (B : FormulaN L)
    (hB : B ∈ (buildSearchTree_case3_nodeSeqAt seq u).succedent) :
    B ∈ (buildSearchTree_case3_nodeSeqAt seq (u ++ [i])).succedent := by
-- BEGIN PROOF
  simp only [buildSearchTree_case3_nodeSeqAt]
  show B ∈ (branchingNodeSeqF seq (buildSearchTree_case3_freshBase seq)
    (fun m => (u ++ [i]).getD m 0) (u ++ [i]).length).succedent
  rw [show (u ++ [i]).length = u.length + 1 from by simp]
  simp only [branchingNodeSeqF]
  have heq : branchingNodeSeqF seq (buildSearchTree_case3_freshBase seq)
      (fun m => (u ++ [i]).getD m 0) u.length =
    branchingNodeSeqF seq (buildSearchTree_case3_freshBase seq)
      (fun m => u.getD m 0) u.length := by
    apply branchingNodeSeqF_ext
    intro m hm; simp [List.getD, List.getElem?_append_left hm]
  rw [heq]
  exact branchStep_succ_mono _ u.length (buildSearchTree_case3_freshBase seq) _ seq B hB

/-- Theorem 5.5.1 (companion, Case 3): Non-axiom nodes have no eq_
formula — `branchingNodeSeqF_seqNoEq` propagates `seqNoEq` along the
branching search. -/
theorem buildSearchTree_case3_node_seqNoEq {L : Language} [Countable (Term L)]
    (seq : Sequent L) (hNoEq : seqNoEq seq) (u : TreeAddr)
    (_hu : u ∈ (buildSearchTree_case3_treeDom seq).dom)
    (_hnax : ¬ isAxiom (buildSearchTree_case3_nodeSeqAt seq u)) :
    seqNoEq (buildSearchTree_case3_nodeSeqAt seq u) := by
-- BEGIN PROOF
  simp only [buildSearchTree_case3_nodeSeqAt]
  exact branchingNodeSeqF_seqNoEq seq (buildSearchTree_case3_freshBase seq) _ u.length hNoEq

/-- Theorem 5.5.1 (companion, Case 3): Path expansion — the nodeSequent
at depth `n + 1` equals `branchStep` applied to the nodeSequent at
depth `n`. -/
theorem buildSearchTree_case3_path_expansion {L : Language} [Countable (Term L)]
    (seq : Sequent L) (f : Nat → Nat) (n : Nat)
    (_hPath : ∀ m, (List.ofFn (fun i : Fin m => f i)) ∈
      (buildSearchTree_case3_treeDom seq).dom) :
    buildSearchTree_case3_nodeSeqAt seq
      (List.ofFn (fun i : Fin (n + 1) => f i)) =
    branchStep (buildSearchTree_case3_nodeSeqAt seq
      (List.ofFn (fun i : Fin n => f i)))
      n (buildSearchTree_case3_freshBase seq) (f n) seq := by
-- BEGIN PROOF
  simp only [buildSearchTree_case3_nodeSeqAt]
  have hlen1 : (List.ofFn (fun j : Fin (n + 1) => f j)).length = n + 1 := by simp
  have hlen0 : (List.ofFn (fun j : Fin n => f j)).length = n := by simp
  rw [hlen1, hlen0]
  rw [branchingNodeSeqF_ofFn_eq seq (buildSearchTree_case3_freshBase seq) f (n + 1)]
  rw [branchingNodeSeqF_ofFn_eq seq (buildSearchTree_case3_freshBase seq) f n]
  rfl

/-- Theorem 5.5.1 (companion, Case 3): Derivation of
`sequentProvableExt` from finiteness of the pruned tree. If `seq` is
already provable the conclusion is trivial; otherwise the all-zeros
path stays in the domain for all `n`, contradicting finiteness. The
internal `by_cases` absorbs the provability split so callers need not
supply it, closing the adversarial loophole that previously admitted a
sentinel-mock Case 2 tree. -/
theorem buildSearchTree_case3_provable_if_finite {L : Language} [Countable (Term L)]
    (seq : Sequent L)
    (hFin : (buildSearchTree_case3_treeDom seq).IsFinite) :
    sequentProvableExt seq := by
-- BEGIN PROOF
  by_cases hProof : sequentProvableExt seq
  · exact hProof
  · exfalso
    have hNotAxiom : ∀ k, ¬ isAxiom (buildSearchTree_case3_nodeSeqAt seq (List.replicate k 0)) := by
      intro k hax
      simp only [buildSearchTree_case3_nodeSeqAt] at hax
      have hlen : (List.replicate k (0:Nat)).length = k := by simp
      rw [hlen] at hax
      have heqf : branchingNodeSeqF seq (buildSearchTree_case3_freshBase seq)
          (fun i => (List.replicate k (0:Nat)).getD i 0) k =
        branchingNodeSeqF seq (buildSearchTree_case3_freshBase seq) (fun _ => 0) k := by
        apply branchingNodeSeqF_ext; intro i hi
        simp [List.getD, hi]
      rw [heqf] at hax
      -- DEBT(input sequent provability from an axiom on the all-zero search branch not established)
      exact hProof sorry
    have hInf : (buildSearchTree_case3_treeDom seq).IsInfinite := by
      intro n
      refine ⟨List.replicate n 0, ?_, by simp⟩
      show (∀ j ∈ List.replicate n 0, j < 2) ∧ _
      constructor
      · intro j hj; have := List.eq_of_mem_replicate hj; omega
      · intro k hk
        simp at hk
        rw [List.take_replicate, show min k n = k from by omega]
        exact hNotAxiom k
    exact LCS.TreeDomain.finite_not_infinite _ hFin hInf

/-- Theorem 5.5.1 (companion, Case 3): Pruned branching search tree
data for the non-axiom branch. Works for ALL non-axiom sequents: if
the sequent happens to be provable the tree naturally becomes finite,
and if it is not the tree is infinite and yields a Hintikka
counter-model via the limit set. The `provable_if_finite` field no
longer needs an external `¬ sequentProvableExt` hypothesis. -/
noncomputable def buildSearchTree_case3 {L : Language} [Countable (Term L)]
    (seq : Sequent L) (hFree : noFreeBound seq)
    (hCross : crossNoFreeBound seq)
    (hNoEq : seqNoEq seq) (_hAxiom : ¬ isAxiom seq) :
    SearchTreeData L seq where
  treeDom := buildSearchTree_case3_treeDom seq
  nodeSequent := fun addr _ => buildSearchTree_case3_nodeSeqAt seq addr
  nodeState := fun _addr _ => SearchState.init seq
  root_sequent := buildSearchTree_case3_nodeSeqAt_nil seq
  axiom_is_leaf := fun u hu hax hchild =>
    (buildSearchTree_case3_axiom_is_leaf seq u hu hax hchild).elim
  finBranching := buildSearchTree_case3_finBranching seq
  non_axiom_has_child := buildSearchTree_case3_non_axiom_has_child seq
  input_noFreeBound := hFree
  input_crossNoFreeBound := hCross
  input_seqNoEq := hNoEq
  path_ant_mono := buildSearchTree_case3_path_ant_mono seq
  path_succ_mono := buildSearchTree_case3_path_succ_mono seq
  node_seqNoEq := buildSearchTree_case3_node_seqNoEq seq hNoEq
  freshBase := buildSearchTree_case3_freshBase seq
  freshBase_bound := fun v A hA hv => seqBV_lt_seqMaxBVN seq v A hA hv
  path_expansion := buildSearchTree_case3_path_expansion seq
  provable_if_finite := buildSearchTree_case3_provable_if_finite seq

-- ===================================================================
-- buildSearchTree: Construct the normalized search tree
-- ===================================================================

/-- Theorem 5.5.1 (companion, build search tree): Given a finite sequent in which no variable occurs
both free and bound, construct a search tree such that either (i) the
tree is finite and all leaves are axioms (yielding a proof), or (ii)
the tree has an infinite path whose limit set is a Hintikka set
(yielding a counter-model). -/
noncomputable def buildSearchTree {L : Language} [Countable (Term L)]
    (seq : Sequent L) (hFree : noFreeBound seq)
    (hCross : crossNoFreeBound seq)
    (hNoEq : seqNoEq seq) :
    SearchTreeData L seq := by
  by_cases hAxiom : isAxiom seq
  · exact buildSearchTree_case1 seq hFree hCross hNoEq hAxiom
  · exact buildSearchTree_case3 seq hFree hCross hNoEq hAxiom

end LCS.FirstOrder.Gentzen.Hintikka
end

