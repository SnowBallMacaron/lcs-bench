import LCS.Item
import LCS.Util
import LCS.Resolution.Method.FiniteGraph
import Attach
import LCS.Resolution.Method.Completeness.Conversion.ProofsStamp

/-! # Converting GCNF'-proofs into resolution refutations (Section 4.3.4)

The construction of Theorem 4.3.1 on finite resolution graphs (shared input
leaves, replay of derived units, complementary unit resolution), the node
bounds of Lemma 4.3.3, and the completeness of the resolution method
(Theorem 4.3.2).
-/
section
namespace LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method
namespace FiniteGraph

/-- Directed adjacency, independent of the two premise positions. -/
@[blueprint "chap4__definition_4_3_3"]
def hasEdge (g : FiniteGraph) (i j : Nat) : Prop :=
  g.next i 0 = some j ∨ g.next i 1 = some j

/-- Canonical input identity is the first table position of the same leaf. -/
@[blueprint "chap4__theorem_4_3_1"]
def canonicalInput (g : FiniteGraph) (i : Nat) : Nat :=
  match g.node i with
  | some ⟨C, none⟩ => g.table.findIdx (fun n => decide (n = ⟨C, none⟩))
  | _ => i

-- ATTACH-BLOCKER: private declaration
private theorem firstInput_spec (g : FiniteGraph) (i : Nat) (C : Clause)
    (hi : g.node i = some ⟨C, none⟩) :
    let j := g.table.findIdx (fun n => decide (n = ⟨C, none⟩))
    j ≤ i ∧ g.node j = some ⟨C, none⟩ := by
  obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp hi
  have hmem : (⟨C, none⟩ : FiniteGraph.Node) ∈ g.table :=
    he ▸ List.getElem_mem hlt
  have hfound := List.findIdx_lt_length_of_exists
    (p := fun n => decide (n = (⟨C, none⟩ : FiniteGraph.Node))) ⟨_, hmem, by simp⟩
  have hnode := List.findIdx_getElem (w := hfound)
  simp only [decide_eq_true_eq] at hnode
  constructor
  · apply Nat.le_of_not_gt
    intro hgt
    have hnot := List.not_of_lt_findIdx hgt
    simp only [decide_eq_false_iff_not] at hnot
    exact hnot he
  · exact List.getElem?_eq_some_iff.mpr ⟨hfound, hnode⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem canonicalInput_le (g : FiniteGraph) (i : Nat) : g.canonicalInput i ≤ i := by
  cases hn : g.node i with
  | none => simp [canonicalInput, hn]
  | some n =>
    rcases n with ⟨C, inf⟩
    cases inf with
    | none => simpa [canonicalInput, hn] using (firstInput_spec g i C hn).1
    | some r => simp [canonicalInput, hn]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem node_canonicalInput (g : FiniteGraph) (i : Nat) :
    g.node (g.canonicalInput i) = g.node i := by
  cases hn : g.node i with
  | none => simp [canonicalInput, hn]
  | some n =>
    rcases n with ⟨C, inf⟩
    cases inf with
    | none => simpa [canonicalInput, hn] using (firstInput_spec g i C hn).2
    | some r => simp [canonicalInput, hn]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem canonicalInput_internal (g : FiniteGraph) (i : Nat)
    (hi : g.isInternal i = true) : g.canonicalInput i = i := by
  cases hn : g.node i with
  | none => simp [FiniteGraph.isInternal, hn] at hi
  | some n =>
    rcases n with ⟨C, inf⟩
    cases inf with
    | none => simp [FiniteGraph.isInternal, hn] at hi
    | some r => simp [canonicalInput, hn]

-- ATTACH-BLOCKER: private declaration
private def redirectInputNode (g : FiniteGraph) (n : FiniteGraph.Node) : FiniteGraph.Node :=
  { n with inference := n.inference.map fun r =>
      { r with left := g.canonicalInput r.left, right := g.canonicalInput r.right } }

/-- Identify equal input leaves while retaining every internal vertex identity. -/
@[blueprint "chap4__theorem_4_3_1"]
def coalesceInputLeaves (g : FiniteGraph) : FiniteGraph :=
  ⟨g.table.map (fun n => { n with inference := n.inference.map fun r =>
      { r with left := g.canonicalInput r.left, right := g.canonicalInput r.right } }),
    g.canonicalInput g.root⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem coalesceInputLeaves_table_length (g : FiniteGraph) :
    g.coalesceInputLeaves.table.length = g.table.length := by
  simp [coalesceInputLeaves]

-- ATTACH-BLOCKER: private declaration
private theorem node_coalesceInputLeaves (g : FiniteGraph) (i : Nat) :
    g.coalesceInputLeaves.node i = (g.node i).map (redirectInputNode g) := by
  simp only [FiniteGraph.node, coalesceInputLeaves, List.getElem?_map]
  rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem label_coalesceInputLeaves (g : FiniteGraph) (i : Nat) :
    g.coalesceInputLeaves.label i = g.label i := by
  simp only [FiniteGraph.label, node_coalesceInputLeaves]
  cases g.node i <;> rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem isInternal_coalesceInputLeaves (g : FiniteGraph) (i : Nat) :
    g.coalesceInputLeaves.isInternal i = g.isInternal i := by
  simp only [FiniteGraph.isInternal, node_coalesceInputLeaves]
  cases g.node i with
  | none => rfl
  | some n => cases hn : n.inference <;> simp [redirectInputNode, hn]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem isInternal_canonicalInput (g : FiniteGraph) (i : Nat) :
    g.isInternal (g.canonicalInput i) = g.isInternal i := by
  simp only [FiniteGraph.isInternal, node_canonicalInput]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
@[simp] theorem coalesceInputLeaves_rootLabel (g : FiniteGraph) :
    g.coalesceInputLeaves.rootLabel = g.rootLabel := by
  change g.coalesceInputLeaves.label (g.canonicalInput g.root) = g.label g.root
  rw [label_coalesceInputLeaves]
  simp only [FiniteGraph.label, node_canonicalInput]

-- ATTACH-BLOCKER: private declaration
private theorem next_coalesceInputLeaves (g : FiniteGraph) (i p : Nat) :
    g.coalesceInputLeaves.next (g.canonicalInput i) p =
      (g.next i p).map g.canonicalInput := by
  simp only [FiniteGraph.next, node_coalesceInputLeaves, node_canonicalInput]
  cases g.node i with
  | none => rfl
  | some n =>
    cases hn : n.inference with
    | none => simp [redirectInputNode, hn]
    | some r =>
      by_cases hp : p = 0
      · simp [redirectInputNode, hn, hp]
      · by_cases hp1 : p = 1 <;> simp [redirectInputNode, hn, hp, hp1]

-- ATTACH-BLOCKER: private declaration
private theorem reachableFrom_coalesceInputLeaves (g : FiniteGraph) (depth i : Nat) :
    g.coalesceInputLeaves.reachableFrom depth (g.canonicalInput i) =
      (g.reachableFrom depth i).map g.canonicalInput := by
  induction depth generalizing i with
  | zero => rfl
  | succ depth ih =>
    simp only [FiniteGraph.reachableFrom, next_coalesceInputLeaves]
    cases h0 : g.next i 0 <;> cases h1 : g.next i 1 <;> simp [ih]

-- ATTACH-BLOCKER: private declaration
private theorem vertexIds_coalesceInputLeaves (g : FiniteGraph) (i : Nat) :
    i ∈ g.coalesceInputLeaves.vertexIds ↔
      ∃ j, j ∈ g.vertexIds ∧ g.canonicalInput j = i := by
  simp only [FiniteGraph.vertexIds, List.mem_eraseDups]
  change i ∈ g.coalesceInputLeaves.reachableFrom
    g.coalesceInputLeaves.table.length (g.canonicalInput g.root) ↔ _
  rw [coalesceInputLeaves_table_length, reachableFrom_coalesceInputLeaves]
  simp [List.mem_map]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Redirected references keep the original resolution equation and topological order. -/
theorem coalesceInputLeaves_allRowsWellFormed (g : FiniteGraph)
    (hg : g.AllRowsWellFormed) : g.coalesceInputLeaves.AllRowsWellFormed := by
  constructor
  · change g.canonicalInput g.root < g.coalesceInputLeaves.table.length
    rw [coalesceInputLeaves_table_length]
    exact Nat.lt_of_le_of_lt (canonicalInput_le _ _) hg.1
  · intro i n hn r hr
    rw [node_coalesceInputLeaves] at hn
    cases hold : g.node i with
    | none => simp [hold] at hn
    | some old =>
      simp only [hold, Option.map_some, Option.some.injEq] at hn
      subst n
      cases hinf : old.inference with
      | none => simp [redirectInputNode, hinf] at hr
      | some oldr =>
        simp only [redirectInputNode, hinf, Option.map_some, Option.some.injEq] at hr
        subst r
        obtain ⟨hlt, hrt, a, b, ha, hb, hpa, hpb, heq⟩ := hg.2 i old hold oldr hinf
        refine ⟨Nat.lt_of_le_of_lt (canonicalInput_le _ _) hlt,
          Nat.lt_of_le_of_lt (canonicalInput_le _ _) hrt,
          redirectInputNode g a, redirectInputNode g b, ?_, ?_, hpa, hpb, heq⟩
        · simp only [node_coalesceInputLeaves, node_canonicalInput, ha, Option.map_some]
        · simp only [node_coalesceInputLeaves, node_canonicalInput, hb, Option.map_some]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Every selected input keeps the label of a reachable original input. -/
theorem coalesceInputLeaves_leavesFrom (g : FiniteGraph) (S : ClauseSequent)
    (hg : g.LeavesFrom S) : g.coalesceInputLeaves.LeavesFrom S := by
  intro i hi
  obtain ⟨hreach, hint⟩ := List.mem_filter.mp hi
  obtain ⟨j, hj, rfl⟩ := (vertexIds_coalesceInputLeaves g i).mp hreach
  have hjleaf : j ∈ g.leafIds := by
    apply List.mem_filter.mpr
    exact ⟨hj, by simpa only [isInternal_coalesceInputLeaves, isInternal_canonicalInput] using hint⟩
  obtain ⟨C, hC, hS⟩ := hg j hjleaf
  refine ⟨C, ?_, hS⟩
  rw [label_coalesceInputLeaves]
  simpa only [FiniteGraph.label, node_canonicalInput] using hC

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Coalescing inputs keeps every reachable internal vertex ID. -/
theorem stepIds_coalesceInputLeaves_subset (g : FiniteGraph) :
    ∀ i, i ∈ g.coalesceInputLeaves.stepIds → i ∈ g.stepIds := by
  intro i hi
  obtain ⟨hreach, hint⟩ := List.mem_filter.mp hi
  obtain ⟨j, hj, rfl⟩ := (vertexIds_coalesceInputLeaves g i).mp hreach
  have hjInt : g.isInternal j = true := by
    simpa only [isInternal_coalesceInputLeaves, isInternal_canonicalInput] using hint
  rw [canonicalInput_internal g j hjInt]
  exact List.mem_filter.mpr ⟨hj, hjInt⟩

-- ATTACH-BLOCKER: private declaration
private theorem nodup_length_le_of_subset {α : Type} [DecidableEq α]
    {xs ys : List α} (hNodup : xs.Nodup)
    (hSubset : ∀ x, x ∈ xs → x ∈ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons head tail ih =>
    have hParts := List.nodup_cons.mp hNodup
    have hHead : head ∈ ys := hSubset head List.mem_cons_self
    have hTailSubset : ∀ x, x ∈ tail → x ∈ ys.erase head := by
      intro x hx
      apply (List.mem_erase_of_ne ?_).mpr
        (hSubset x (List.mem_cons.mpr (Or.inr hx)))
      intro hEq
      subst x
      exact hParts.1 hx
    have hTailLe := ih hParts.2 hTailSubset
    have hLength := (List.perm_cons_erase hHead).length_eq
    simp only [List.length_cons] at hLength ⊢
    omega

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Count distinct reachable resolution vertices after input identification. -/
theorem coalesceInputLeaves_stepCount_le (g : FiniteGraph) :
    g.coalesceInputLeaves.stepCount ≤ g.stepCount :=
  nodup_length_le_of_subset (LCS.Resolution.Method.FiniteGraph.stepIds_nodup g.coalesceInputLeaves)
    (stepIds_coalesceInputLeaves_subset g)

end FiniteGraph
end LCS.Resolution.Method
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method

/-- Search for a natural-number witness. The existence proof bounds the
termination argument; the executable program tests successive candidates. -/
@[blueprint "chap4__theorem_4_3_1"]
def leastWitness (p : Nat → Prop) [DecidablePred p]
    (h : ∃ n, p n) : {n // p n} :=
  go 0 (Nat.zero_le _)
where
  go (n : Nat) (hn : n ≤ Classical.choose h) : {n // p n} :=
    if hp : p n then ⟨n, hp⟩ else
      go (n + 1) (by
        have hx := Classical.choose_spec h
        have : n ≠ Classical.choose h := by intro he; exact hp (he ▸ hx)
        omega)
  termination_by Classical.choose h - n
  decreasing_by
    have hx := Classical.choose_spec h
    have : n ≠ Classical.choose h := by intro he; exact hp (he ▸ hx)
    omega

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem table_node (g : FiniteGraph) (i : Fin g.table.length) :
    g.node i = some g.table[i] := by
  exact List.getElem?_eq_getElem i.isLt

/-- Recompute a label from modified inputs and the original resolution steps.
Every recursive premise is strictly earlier in the topological node table. -/
@[blueprint "chap4__theorem_4_3_1"]
def replayLabel (g : FiniteGraph)
    (f : Clause → Clause) (i : Fin g.table.length) : Clause :=
  match g.table[i].inference with
  | none => f g.table[i].clause
  | some r =>
    if hrow : r.left < i.val ∧ r.right < i.val then
      GCNF.Clause.union
        (GCNF.Clause.remove (replayLabel g f ⟨r.left, Nat.lt_trans hrow.1 i.isLt⟩) r.pivot)
        (GCNF.Clause.remove (replayLabel g f ⟨r.right, Nat.lt_trans hrow.2 i.isLt⟩)
          r.pivot.conjugate)
    else f g.table[i].clause
termination_by i.val

/-- Replace input labels and replay every resolution step without unfolding
shared vertices. -/
@[blueprint "chap4__theorem_4_3_1"]
def replay (g : FiniteGraph)
    (f : Clause → Clause) : FiniteGraph :=
  ⟨List.ofFn (fun i : Fin g.table.length =>
    { g.table[i] with clause := replayLabel g f i }), g.root⟩

-- ATTACH-BLOCKER: private declaration
private theorem resolve_bounds (a b a' b' : Clause) (L B : Literal)
    (ha : LCS.Finset.Subset a a' ∧ ∀ x ∈ a', x ∈ a ∨ x = B)
    (hb : LCS.Finset.Subset b b' ∧ ∀ x ∈ b', x ∈ b ∨ x = B) :
    LCS.Finset.Subset
      (GCNF.Clause.union (GCNF.Clause.remove a L) (GCNF.Clause.remove b L.conjugate))
      (GCNF.Clause.union (GCNF.Clause.remove a' L) (GCNF.Clause.remove b' L.conjugate)) ∧
    ∀ x ∈ GCNF.Clause.union (GCNF.Clause.remove a' L) (GCNF.Clause.remove b' L.conjugate),
      x ∈ GCNF.Clause.union (GCNF.Clause.remove a L) (GCNF.Clause.remove b L.conjugate) ∨ x = B := by
  simp only [LCS.Finset.Subset, GCNF.Clause.union, GCNF.Clause.remove, LCS.Finset.mem_union,
    LCS.Finset.mem_erase]
  constructor
  · intro x hx
    rcases hx with ⟨hx, hne⟩ | ⟨hx, hne⟩
    · exact Or.inl ⟨ha.1 x hx, hne⟩
    · exact Or.inr ⟨hb.1 x hx, hne⟩
  · intro x hx
    rcases hx with ⟨hx, hne⟩ | ⟨hx, hne⟩
    · exact (ha.2 x hx).elim (fun h => Or.inl (Or.inl ⟨h, hne⟩)) Or.inr
    · exact (hb.2 x hx).elim (fun h => Or.inl (Or.inr ⟨h, hne⟩)) Or.inr

-- ATTACH-BLOCKER: termination suffix
/-- Replaying additions of B preserves all old literals and can add only B. -/
theorem replayLabel_bounds (g : FiniteGraph) (hg : g.AllRowsWellFormed)
    (f : Clause → Clause) (B : Literal)
    (hf : ∀ C, LCS.Finset.Subset C (f C) ∧ ∀ x ∈ f C, x ∈ C ∨ x = B)
    (i : Fin g.table.length) :
    LCS.Finset.Subset g.table[i].clause (replayLabel g f i) ∧
      ∀ x ∈ replayLabel g f i, x ∈ g.table[i].clause ∨ x = B := by
  rw [replayLabel]
  split
  · exact hf _
  · rename_i r hr
    have hrow := hg.2 i g.table[i] (table_node g i) r hr
    obtain ⟨a, b, ha, hb, hL, hLc, hres⟩ := hrow.2.2
    have haleft : a = g.table[r.left]'(Nat.lt_trans hrow.1 i.isLt) :=
      Option.some.inj (ha.symm.trans (table_node g ⟨r.left, Nat.lt_trans hrow.1 i.isLt⟩))
    have hbright : b = g.table[r.right]'(Nat.lt_trans hrow.2.1 i.isLt) :=
      Option.some.inj (hb.symm.trans (table_node g ⟨r.right, Nat.lt_trans hrow.2.1 i.isLt⟩))
    subst a; subst b
    rw [dite_eq_left ⟨hrow.1, hrow.2.1⟩]
    have hbound := resolve_bounds _ _ _ _ r.pivot B
      (replayLabel_bounds g hg f B hf ⟨r.left, Nat.lt_trans hrow.1 i.isLt⟩)
      (replayLabel_bounds g hg f B hf ⟨r.right, Nat.lt_trans hrow.2.1 i.isLt⟩)
    constructor
    · intro x hx
      exact hbound.1 x (hres ▸ hx)
    · intro x hx
      rcases hbound.2 x hx with h | h
      · exact Or.inl (hres ▸ h)
      · exact Or.inr h
termination_by i.val

/-- The source's axiom case: two complementary units and their empty resolvent. -/
@[blueprint "chap4__theorem_4_3_1"]
def complementaryGraph (L : Literal) : FiniteGraph :=
  ⟨[⟨Clause.single L, none⟩, ⟨Clause.single L.conjugate, none⟩,
    ⟨Clause.empty, some ⟨L, 0, 1⟩⟩], 2⟩

/-- Decide whether all currently used input vertices already belong to S. -/
@[blueprint "chap4__definition_4_3_3"]
def leavesIn (g : FiniteGraph) (S : ClauseSequent) : Bool :=
  g.leafIds.all fun i => match g.label i with
    | none => false
    | some C => decide (C ∈ S)

/-- Add B precisely to input clauses absent from the current conclusion. -/
@[blueprint "chap4__theorem_4_3_1"]
def missingLift (S : ClauseSequent) (B : Literal) (C : Clause) : Clause :=
  if C ∈ S then C else clauseWithLiteral C B

/-- Select exactly the recipient's input occurrences of the derived unit B. -/
@[blueprint "chap4__theorem_4_3_1"]
def unitInputs (g : FiniteGraph) (B : Literal) (i : Nat) : Bool :=
  match g.node i with
  | some ⟨C, none⟩ => decide (C = Clause.single B)
  | _ => false

/-- An admissible executable choice of the complementary literal in each axiom. -/
@[blueprint "chap4__theorem_4_3_1"]
def AxiomPolicy := ∀ (S : ClauseSequent),
  (∃ P, Clause.single (.pos P) ∈ S ∧ Clause.single (.neg P) ∈ S) →
    {L : Literal // Clause.single L ∈ S ∧ Clause.single L.conjugate ∈ S}

/-- Select the least available atom and put its positive literal first. -/
@[blueprint "chap4__theorem_4_3_1"]
def leastAtomPolicy : AxiomPolicy := fun S h =>
  let witness := leastWitness
    (fun P => Clause.single (.pos P) ∈ S ∧ Clause.single (.neg P) ∈ S) h
  ⟨.pos witness.val, witness.property⟩

/-- Theorem 4.3.1: an effective conversion retaining shared graph vertices. -/
@[blueprint "chap4__theorem_4_3_1"]
def gcnfProofToResolution {S : ClauseSequent} (T : GCNFProofTree S)
    (pick : AxiomPolicy := leastAtomPolicy) : FiniteGraph :=
  match T with
  | .axiom_ S _ hTriv => complementaryGraph (pick S hTriv).val
  | .rule Gamma As B _ _ _ _ _ left right _ _ _ _ =>
    let S := LCS.Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B))
    let d1 := gcnfProofToResolution left pick
    let d2 := gcnfProofToResolution right pick
    if leavesIn d1 S then d1 else if leavesIn d2 S then d2 else
      let lifted := replay d1 (missingLift S B)
      if lifted.rootLabel = some GCNF.Clause.empty then lifted
      else (FiniteGraph.graft lifted d2 (unitInputs d2 B)).coalesceInputLeaves

/-- Proof of Theorem 4.3.1: the output refutes the same clause set and uses no
more resolution vertices than the input has axiom occurrences. -/
@[blueprint "chap4__theorem_4_3_1" (main := true)]
theorem gcnfProofToResolution_spec {S : ClauseSequent} (T : GCNFProofTree S)
    (pick : AxiomPolicy := leastAtomPolicy) :
    (gcnfProofToResolution T pick).IsRefutationFor S ∧
      (gcnfProofToResolution T pick).stepCount ≤ T.leafCount 

/-- Proof of Lemma 4.3.3: count actual reachable vertices, including sharing. -/
@[blueprint "chap4__lemma_4_3_3" (main := true)]
theorem gcnfToResolution_nodeBound {S : ClauseSequent} (T : GCNFProofTree S)
    (pick : AxiomPolicy := leastAtomPolicy) :
    (gcnfProofToResolution T pick).stepCount + 1 ≤ (gcnfProofToResolution T pick).nodeCount ∧
      (gcnfProofToResolution T pick).nodeCount ≤ T.nodeCount + 2 

/-- Proof of Theorem 4.3.2: GCNF′ completeness followed by the actual converter;
the empty input clause separately gives the zero-step refutation. -/
@[blueprint "chap4__theorem_4_3_2" (main := true)]
theorem resolution_completeness (S : ClauseSequent) :
    ClauseSet.isUnsatisfiable S ↔ ∃ D : ResolutionDAG, D.isRefutationFor S 

end LCS.Resolution.Method.Completeness
end
