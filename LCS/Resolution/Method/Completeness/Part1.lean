import LCS.Item
import LCS.Util
import LCS.Resolution.Method.FiniteGraph
import Attach
import LCS.Resolution.Method.Completeness.Part1.ProofsStamp
attach_helper_namespace LCS.Resolution.Method.Completeness.Proofs

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
end

section
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

/-- Choose the same atom while reversing the two complementary input positions. -/
@[blueprint "chap4__example_4_3_6"]
def negativeFirstPolicy : AxiomPolicy := fun S h =>
  let witness := leastWitness
    (fun P => Clause.single (.pos P) ∈ S ∧ Clause.single (.neg P) ∈ S) h
  ⟨.neg witness.val, witness.property.2, witness.property.1⟩

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


/-- The finite table and textbook quotient DAG count the same shared vertices. -/
@[blueprint "chap4__lemma_4_3_3"]
theorem gcnfToResolution_quotientNodeBound {S : ClauseSequent} (T : GCNFProofTree S)
    (pick : AxiomPolicy := leastAtomPolicy) :
    let g := gcnfProofToResolution T pick
    let D := g.toResolutionDAG (gcnfProofToResolution_spec T pick).1.1
    D.stepCount + 1 ≤ D.nodeCount ∧ D.nodeCount ≤ T.nodeCount + 2 

/-- Proof of Theorem 4.3.2: GCNF′ completeness followed by the actual converter;
the empty input clause separately gives the zero-step refutation. -/
@[blueprint "chap4__theorem_4_3_2" (main := true)]
theorem resolution_completeness (S : ClauseSequent) :
    ClauseSet.isUnsatisfiable S ↔ ∃ D : ResolutionDAG, D.isRefutationFor S 

end LCS.Resolution.Method.Completeness
end

section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF

@[blueprint "chap4__example_4_3_5"]
def displayedAxiom (P : Nat) :
    GCNFProofTree (LCS.Finset.union
      (ClauseSequent.single (Clause.single (.pos P)))
      (ClauseSequent.single (Clause.single (.neg P)))) :=
  .axiom_ _ (ClauseSequent.ordinary_union
    (ClauseSequent.ordinary_single (Clause.single_ordinary _))
    (ClauseSequent.ordinary_single (Clause.single_ordinary _)))
    ⟨P, by simp [ClauseSequent.single], by simp [ClauseSequent.single]⟩

@[blueprint "chap4__example_4_3_6"]
def displayedNegativeFirstAxiom (P : Nat) :
    GCNFProofTree (LCS.Finset.union
      (ClauseSequent.single (Clause.single (.neg P)))
      (ClauseSequent.single (Clause.single (.pos P)))) :=
  .axiom_ _ (ClauseSequent.ordinary_union
    (ClauseSequent.ordinary_single (Clause.single_ordinary _))
    (ClauseSequent.ordinary_single (Clause.single_ordinary _)))
    ⟨P, by simp [ClauseSequent.single], by simp [ClauseSequent.single]⟩

@[blueprint "chap4__example_4_3_5"]
def ex435InnerSequent (P S : Nat) : ClauseSequent :=
  ClauseSequent.ofList [Clause.single (.pos P), Clause.single (.pos S),
    Clause.ofList [.neg P, .neg S]]

@[blueprint "chap4__example_4_3_5"]
def ex435Sequent (P Q S : Nat) : ClauseSequent :=
  ClauseSequent.ofList [Clause.ofList [.pos P, .neg Q],
    Clause.ofList [.pos S, .neg Q], Clause.single (.pos Q),
    Clause.ofList [.neg P, .neg S]]

@[blueprint "chap4__example_4_3_5"]
def ex435InnerProof (P S : Nat) : GCNFProofTree (ex435InnerSequent P S) :=
  ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
    apply LCS.Finset.ext
    intro C
    simp [ex435InnerSequent, ClauseSequent.ofList, ClauseSequent.single,
      ClauseSequent.mapSet, clauseWithLiteral_single, or_left_comm, or_comm, eq_comm])
    (.rule (ClauseSequent.ofList [Clause.single (.pos P), Clause.single (.pos S)])
      (ClauseSequent.single (Clause.single (.neg P))) (.neg S)
      (ClauseSequent.single (Clause.single (.neg P)))
      (ClauseSequent.single (Clause.single (.pos P)))
      (ClauseSequent.single (Clause.single (.pos S)))
      (by
        apply ClauseSequent.ordinary_ofList
        intro C hC
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
        rcases hC with rfl | rfl <;> exact Clause.single_ordinary _)
      (ClauseSequent.ordinary_single (Clause.single_ordinary _))
      (displayedAxiom P) (displayedAxiom S)
      ⟨Clause.single (.neg P), by simp [ClauseSequent.single]⟩
      (fun _ h => h)
      (by
        intro C hC
        apply LCS.Finset.mem_union.mpr
        left
        simpa [ClauseSequent.single, ClauseSequent.ofList] using Or.inl hC)
      (by
        intro C hC
        apply LCS.Finset.mem_union.mpr
        left
        simpa [ClauseSequent.single, ClauseSequent.ofList] using Or.inr hC)))

@[blueprint "chap4__example_4_3_5"]
def ex435Proof (P Q S : Nat) : GCNFProofTree (ex435Sequent P Q S) :=
  ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
    apply LCS.Finset.ext
    intro C
    simp [ex435Sequent, ClauseSequent.ofList,
      ClauseSequent.mapSet, clauseWithLiteral_single, or_assoc, or_left_comm, or_comm, eq_comm])
    (.rule
      (ClauseSequent.ofList [Clause.single (.pos Q), Clause.ofList [.neg P, .neg S]])
      (ClauseSequent.ofList [Clause.single (.pos P), Clause.single (.pos S)]) (.neg Q)
      (ClauseSequent.ofList [Clause.single (.pos P), Clause.single (.pos S)])
      (ClauseSequent.single (Clause.ofList [.neg P, .neg S]))
      (ClauseSequent.single (Clause.single (.pos Q)))
      (by
        apply ClauseSequent.ordinary_ofList
        intro C hC
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
        rcases hC with rfl | rfl
        · exact Clause.single_ordinary _
        · exact Clause.ofList_cons_ordinary _ _)
      (by
        apply ClauseSequent.ordinary_ofList
        intro C hC
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
        rcases hC with rfl | rfl <;> exact Clause.single_ordinary _)
      (((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
        apply LCS.Finset.ext
        intro C
        simp [ex435InnerSequent, ClauseSequent.ofList, ClauseSequent.single,
          or_left_comm, or_comm]) (ex435InnerProof P S)))
      (displayedAxiom Q)
      ⟨Clause.single (.pos P), by simp [ClauseSequent.ofList]⟩
      (fun _ h => h)
      (by
        intro C hC
        apply LCS.Finset.mem_union.mpr
        left
        simpa [ClauseSequent.single, ClauseSequent.ofList] using Or.inr hC)
      (by
        intro C hC
        apply LCS.Finset.mem_union.mpr
        left
        simpa [ClauseSequent.single, ClauseSequent.ofList] using Or.inl hC)))

@[blueprint "chap4__example_4_3_5"]
theorem ex435Proof_leafCount (P Q S : Nat) : (ex435Proof P Q S).leafCount = 3 

@[blueprint "chap4__example_4_3_5"]
theorem ex435Proof_nodeCount (P Q S : Nat) : (ex435Proof P Q S).nodeCount = 5 

/-- The innermost conclusion in the displayed proof of Example 4.3.6. -/
@[blueprint "chap4__example_4_3_6"]
def ex436InnerSequent (P Q : Nat) : ClauseSequent :=
  ClauseSequent.ofList [Clause.single (.neg Q), Clause.single (.neg P),
    Clause.ofList [.pos P, .pos Q]]

/-- The left premise of the root rule in Example 4.3.6. -/
@[blueprint "chap4__example_4_3_6"]
def ex436MiddleSequent (P Q R : Nat) : ClauseSequent :=
  ClauseSequent.ofList [Clause.single (.neg R), Clause.single (.neg Q),
    Clause.ofList [.pos R, .neg P], Clause.ofList [.pos P, .pos Q]]

@[blueprint "chap4__example_4_3_6"]
def ex436Sequent (P Q R : Nat) : ClauseSequent :=
  ClauseSequent.ofList [Clause.single (.neg R), Clause.single (.neg Q),
    Clause.ofList [.pos R, .neg P], Clause.ofList [.pos P, .pos Q, .pos R]]

/-- The two-axiom subtree with leaves ¬P,P and ¬Q,Q, in that order. -/
@[blueprint "chap4__example_4_3_6"]
def ex436InnerProof (P Q : Nat) : GCNFProofTree (ex436InnerSequent P Q) :=
  ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
    apply LCS.Finset.ext
    intro C
    simp [ex436InnerSequent, ClauseSequent.ofList, ClauseSequent.single,
      ClauseSequent.mapSet, clauseWithLiteral_single, or_assoc, or_left_comm, or_comm, eq_comm])
    (.rule (ClauseSequent.ofList [Clause.single (.neg Q), Clause.single (.neg P)])
      (ClauseSequent.single (Clause.single (.pos P))) (.pos Q)
      (ClauseSequent.single (Clause.single (.pos P)))
      (ClauseSequent.single (Clause.single (.neg P)))
      (ClauseSequent.single (Clause.single (.neg Q)))
      (by
        apply ClauseSequent.ordinary_ofList
        intro C hC
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
        rcases hC with rfl | rfl <;> exact Clause.single_ordinary _)
      (ClauseSequent.ordinary_single (Clause.single_ordinary _))
      (displayedNegativeFirstAxiom P) (displayedNegativeFirstAxiom Q)
      ⟨Clause.single (.pos P), by simp [ClauseSequent.single]⟩
      (fun _ h => h)
      (by
        intro C hC
        apply LCS.Finset.mem_union.mpr
        left
        simpa [ClauseSequent.single, ClauseSequent.ofList] using Or.inr hC)
      (by
        intro C hC
        apply LCS.Finset.mem_union.mpr
        left
        simpa [ClauseSequent.single, ClauseSequent.ofList] using Or.inl hC)))

/-- The first branch is the axiom ¬R,R; the second is the P,Q subtree. -/
@[blueprint "chap4__example_4_3_6"]
def ex436MiddleProof (P Q R : Nat) : GCNFProofTree (ex436MiddleSequent P Q R) :=
  ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
    apply LCS.Finset.ext
    intro C
    simp [ex436MiddleSequent, ClauseSequent.ofList, ClauseSequent.single,
      ClauseSequent.mapSet, clauseWithLiteral_single, or_assoc, or_left_comm, or_comm, eq_comm])
    (.rule
      (ClauseSequent.ofList [Clause.single (.neg R), Clause.single (.neg Q),
        Clause.ofList [.pos P, .pos Q]])
      (ClauseSequent.single (Clause.single (.pos R))) (.neg P)
      (ClauseSequent.single (Clause.single (.pos R)))
      (ClauseSequent.single (Clause.single (.neg R)))
      (ClauseSequent.ofList [Clause.single (.neg Q), Clause.ofList [.pos P, .pos Q]])
      (by
        apply ClauseSequent.ordinary_ofList
        intro C hC
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
        rcases hC with rfl | rfl | rfl
        · exact Clause.single_ordinary _
        · exact Clause.single_ordinary _
        · exact Clause.ofList_cons_ordinary _ _)
      (ClauseSequent.ordinary_single (Clause.single_ordinary _))
      (displayedNegativeFirstAxiom R)
      (((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
        apply LCS.Finset.ext
        intro C
        simp [ex436InnerSequent, ClauseSequent.ofList, ClauseSequent.single,
          or_left_comm, or_comm]) (ex436InnerProof P Q)))
      ⟨Clause.single (.pos R), by simp [ClauseSequent.single]⟩
      (fun _ h => h)
      (by
        intro C hC
        apply LCS.Finset.mem_union.mpr
        left
        simpa [ClauseSequent.single, ClauseSequent.ofList] using Or.inl hC)
      (by
        intro C hC
        apply LCS.Finset.mem_union.mpr
        left
        simpa [ClauseSequent.ofList] using Or.inr hC)))

/-- The middle rule in the order used by the Example 4.3.6 conversion narrative:
the P,Q subtree supplies ¬P and the other premise supplies R. -/
@[blueprint "chap4__example_4_3_6"]
def ex436NarratedMiddleProof (P Q R : Nat) : GCNFProofTree (ex436MiddleSequent P Q R) :=
  ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
    apply LCS.Finset.ext
    intro C
    simp [ex436MiddleSequent, ClauseSequent.ofList, ClauseSequent.single,
      ClauseSequent.mapSet, clauseWithLiteral_single,
      GCNF.clauseOfList_swap (.neg P) (.pos R), or_assoc, or_left_comm, or_comm, eq_comm])
    (.rule
      (ClauseSequent.ofList [Clause.single (.neg R), Clause.single (.neg Q),
        Clause.ofList [.pos P, .pos Q]])
      (ClauseSequent.single (Clause.single (.neg P))) (.pos R)
      (ClauseSequent.single (Clause.single (.neg P)))
      (ClauseSequent.ofList [Clause.single (.neg Q), Clause.ofList [.pos P, .pos Q]])
      (ClauseSequent.single (Clause.single (.neg R)))
      (by
        apply ClauseSequent.ordinary_ofList
        intro C hC
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
        rcases hC with rfl | rfl | rfl
        · exact Clause.single_ordinary _
        · exact Clause.single_ordinary _
        · exact Clause.ofList_cons_ordinary _ _)
      (ClauseSequent.ordinary_single (Clause.single_ordinary _))
      (((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
        apply LCS.Finset.ext
        intro C
        simp [ex436InnerSequent, ClauseSequent.ofList, ClauseSequent.single,
          or_left_comm, or_comm]) (ex436InnerProof P Q)))
      (displayedNegativeFirstAxiom R)
      ⟨Clause.single (.neg P), by simp [ClauseSequent.single]⟩
      (fun _ h => h)
      (by
        intro C hC
        apply LCS.Finset.mem_union.mpr
        left
        simpa [ClauseSequent.ofList] using Or.inr hC)
      (by
        intro C hC
        apply LCS.Finset.mem_union.mpr
        left
        simpa [ClauseSequent.single, ClauseSequent.ofList] using Or.inl hC)))

/-- Complete the common root rule from either middle premise ordering. -/
@[blueprint "chap4__example_4_3_6"]
def ex436WithMiddleProof (P Q R : Nat)
    (middle : GCNFProofTree (ex436MiddleSequent P Q R)) : GCNFProofTree (ex436Sequent P Q R) :=
  ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
    apply LCS.Finset.ext
    intro C
    simp [ex436Sequent, ClauseSequent.ofList, ClauseSequent.single,
      ClauseSequent.mapSet, GCNF.clauseWithLiteral_ofList, or_left_comm, or_comm, eq_comm])
    (.rule
      (ClauseSequent.ofList [Clause.single (.neg R), Clause.single (.neg Q),
        Clause.ofList [.pos R, .neg P]])
      (ClauseSequent.single (Clause.ofList [.pos P, .pos Q])) (.pos R)
      (ClauseSequent.single (Clause.ofList [.pos P, .pos Q]))
      (ClauseSequent.ofList [Clause.single (.neg R), Clause.single (.neg Q),
        Clause.ofList [.pos R, .neg P]])
      (ClauseSequent.single (Clause.single (.neg R)))
      (by
        apply ClauseSequent.ordinary_ofList
        intro C hC
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
        rcases hC with rfl | rfl | rfl
        · exact Clause.single_ordinary _
        · exact Clause.single_ordinary _
        · exact Clause.ofList_cons_ordinary _ _)
      (ClauseSequent.ordinary_single (Clause.ofList_cons_ordinary _ _))
      (((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
        apply LCS.Finset.ext
        intro C
        simp [ex436MiddleSequent, ClauseSequent.ofList, ClauseSequent.single,
          or_left_comm, or_comm]) middle))
      (displayedNegativeFirstAxiom R)
      ⟨Clause.ofList [.pos P, .pos Q], by simp [ClauseSequent.single]⟩
      (fun _ h => h)
      (fun _ h => LCS.Finset.mem_union.mpr (Or.inl h))
      (by
        intro C hC
        apply LCS.Finset.mem_union.mpr
        left
        simpa [ClauseSequent.single, ClauseSequent.ofList] using Or.inl hC)))

/-- The displayed four-axiom tree T, with both occurrences of ¬R,R retained. -/
@[blueprint "chap4__example_4_3_6"]
def ex436Proof (P Q R : Nat) : GCNFProofTree (ex436Sequent P Q R) :=
  ex436WithMiddleProof P Q R (ex436MiddleProof P Q R)

/-- The premise ordering used by the narrated D1–D8 construction. -/
@[blueprint "chap4__example_4_3_6"]
def ex436NarratedProof (P Q R : Nat) : GCNFProofTree (ex436Sequent P Q R) :=
  ex436WithMiddleProof P Q R (ex436NarratedMiddleProof P Q R)

@[blueprint "chap4__example_4_3_6"]
theorem ex436NarratedProof_leafCount (P Q R : Nat) :
    (ex436NarratedProof P Q R).leafCount = 4 

/-- The shorter proof uses one grouped rule for {¬P,R} and {P,Q,R}. -/
@[blueprint "chap4__example_4_3_6"]
def ex436ShorterProof (P Q R : Nat) : GCNFProofTree (ex436Sequent P Q R) :=
  ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
    apply LCS.Finset.ext
    intro C
    simp [ex436Sequent, ClauseSequent.ofList,
      ClauseSequent.mapSet, clauseWithLiteral_single, GCNF.clauseWithLiteral_ofList,
      GCNF.clauseOfList_swap (.neg P) (.pos R), or_assoc, or_left_comm, or_comm, eq_comm])
    (.rule
      (ClauseSequent.ofList [Clause.single (.neg R), Clause.single (.neg Q)])
      (ClauseSequent.ofList [Clause.single (.neg P), Clause.ofList [.pos P, .pos Q]]) (.pos R)
      (ClauseSequent.ofList [Clause.single (.neg P), Clause.ofList [.pos P, .pos Q]])
      (ClauseSequent.single (Clause.single (.neg Q)))
      (ClauseSequent.single (Clause.single (.neg R)))
      (by
        apply ClauseSequent.ordinary_ofList
        intro C hC
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
        rcases hC with rfl | rfl <;> exact Clause.single_ordinary _)
      (by
        apply ClauseSequent.ordinary_ofList
        intro C hC
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
        rcases hC with rfl | rfl
        · exact Clause.single_ordinary _
        · exact Clause.ofList_cons_ordinary _ _)
      (((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
        apply LCS.Finset.ext
        intro C
        simp [ex436InnerSequent, ClauseSequent.ofList, ClauseSequent.single,
          or_left_comm, or_comm]) (ex436InnerProof P Q)))
      (displayedNegativeFirstAxiom R)
      ⟨Clause.single (.neg P), by simp [ClauseSequent.ofList]⟩
      (fun _ h => h)
      (by
        intro C hC
        apply LCS.Finset.mem_union.mpr
        left
        simpa [ClauseSequent.single, ClauseSequent.ofList] using Or.inr hC)
      (by
        intro C hC
        apply LCS.Finset.mem_union.mpr
        left
        simpa [ClauseSequent.single, ClauseSequent.ofList] using Or.inl hC)))

@[blueprint "chap4__example_4_3_6"]
theorem ex436Proof_leafCount (P Q R : Nat) : (ex436Proof P Q R).leafCount = 4 

@[blueprint "chap4__example_4_3_6"]
theorem ex436Proof_nodeCount (P Q R : Nat) : (ex436Proof P Q R).nodeCount = 7 

@[blueprint "chap4__example_4_3_6"]
theorem ex436ShorterProof_leafCount (P Q R : Nat) : (ex436ShorterProof P Q R).leafCount = 3 

@[blueprint "chap4__example_4_3_6"]
theorem ex436ShorterProof_nodeCount (P Q R : Nat) : (ex436ShorterProof P Q R).nodeCount = 5 

end LCS.Resolution.Method.Completeness
end

section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

@[blueprint "chap4__example_4_3_5"]
def ex435D1 (P : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos P], none⟩,
    ⟨Clause.ofList [.neg P], none⟩,
    ⟨Clause.ofList [], some ⟨.pos P, 0, 1⟩⟩], 2⟩



@[blueprint "chap4__example_4_3_5"]
theorem ex435D1_wellFormed (P : Nat)  :
    (ex435D1 P).WellFormed 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D1_counts (P : Nat) :
    (ex435D1 P).stepCount = 1 ∧ (ex435D1 P).nodeCount = 3 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D1_rootLabel (P : Nat) :
    (ex435D1 P).rootLabel = some (Clause.ofList []) 

@[blueprint "chap4__example_4_3_5"]
def ex435D2 (S : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos S], none⟩,
    ⟨Clause.ofList [.neg S], none⟩,
    ⟨Clause.ofList [], some ⟨.pos S, 0, 1⟩⟩], 2⟩



@[blueprint "chap4__example_4_3_5"]
theorem ex435D2_wellFormed (S : Nat)  :
    (ex435D2 S).WellFormed 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D2_counts (S : Nat) :
    (ex435D2 S).stepCount = 1 ∧ (ex435D2 S).nodeCount = 3 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D2_rootLabel (S : Nat) :
    (ex435D2 S).rootLabel = some (Clause.ofList []) 

@[blueprint "chap4__example_4_3_5"]
def ex435D3 (P S : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos P], none⟩,
    ⟨Clause.ofList [.neg P, .neg S], none⟩,
    ⟨Clause.ofList [.neg S], some ⟨.pos P, 0, 1⟩⟩], 2⟩



@[blueprint "chap4__example_4_3_5"]
theorem ex435D3_wellFormed (P S : Nat) (hPS : P ≠ S) :
    (ex435D3 P S).WellFormed 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D3_counts (P S : Nat) :
    (ex435D3 P S).stepCount = 1 ∧ (ex435D3 P S).nodeCount = 3 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D3_rootLabel (P S : Nat) :
    (ex435D3 P S).rootLabel = some (Clause.ofList [.neg S]) 

@[blueprint "chap4__example_4_3_5"]
def ex435D4 (P S : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos P], none⟩,
    ⟨Clause.ofList [.neg P, .neg S], none⟩,
    ⟨Clause.ofList [.pos S], none⟩,
    ⟨Clause.ofList [.neg S], some ⟨.pos P, 0, 1⟩⟩,
    ⟨Clause.ofList [], some ⟨.neg S, 3, 2⟩⟩], 4⟩



@[blueprint "chap4__example_4_3_5"]
theorem ex435D4_wellFormed (P S : Nat) (hPS : P ≠ S) :
    (ex435D4 P S).WellFormed 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D4_counts (P S : Nat) :
    (ex435D4 P S).stepCount = 2 ∧ (ex435D4 P S).nodeCount = 5 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D4_rootLabel (P S : Nat) :
    (ex435D4 P S).rootLabel = some (Clause.ofList []) 

@[blueprint "chap4__example_4_3_5"]
def ex435D5 (Q : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos Q], none⟩,
    ⟨Clause.ofList [.neg Q], none⟩,
    ⟨Clause.ofList [], some ⟨.pos Q, 0, 1⟩⟩], 2⟩

end LCS.Resolution.Method.Completeness
end

