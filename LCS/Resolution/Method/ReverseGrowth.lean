import LCS.Resolution.Method.Reverse
import Attach
import LCS.Resolution.Method.ReverseGrowth.ProofsStamp

/-! # Growth of the actual resolution-to-GCNF conversion

A shared chain derives a fresh unit at each level. Each level has two branches
using the preceding unit derivation. The reverse converter unfolds this sharing.
The results below count its output, rather than only the input unfolding.
-/

namespace LCS.Resolution.Method.ReverseGrowth

open LCS.Resolution.GCNF
open ResolutionTree

@[blueprint "chap4__theorem_4_3_3"]
abbrev p (n : Nat) : Literal := .pos (2 * n)
@[blueprint "chap4__theorem_4_3_3"]
abbrev r (n : Nat) : Literal := .pos (2 * n + 1)

@[blueprint "chap4__theorem_4_3_3"]
def leftInput (n : Nat) : GCNF.Clause :=
  GCNF.Clause.ofList [.neg (2 * n), r n, p (n + 1)]
@[blueprint "chap4__theorem_4_3_3"]
def rightInput (n : Nat) : GCNF.Clause :=
  GCNF.Clause.ofList [.neg (2 * n), (r n).conjugate, p (n + 1)]
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
def leftResidual (n : Nat) : GCNF.Clause :=
  GCNF.Clause.ofList [.neg (2 * n), r n]
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
def rightResidual (n : Nat) : GCNF.Clause :=
  GCNF.Clause.ofList [.neg (2 * n), (r n).conjugate]

@[blueprint "chap4__theorem_4_3_3"]
def units : Nat → ResolutionTree
  | 0 => .axiom_ (GCNF.Clause.single (p 0))
  | n + 1 => .resolve
      (.resolve (units n) (.axiom_ (leftInput n)) (p n))
      (.resolve (units n) (.axiom_ (rightInput n)) (p n)) (r n)

@[blueprint "chap4__theorem_4_3_3"]
def refutation (n : Nat) : ResolutionTree :=
  .resolve (units n) (.axiom_ (GCNF.Clause.single (p n).conjugate)) (p n)





-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem left_label (n : Nat) (U : ResolutionTree)
    (hU : U.label = GCNF.Clause.single (p n)) :
    (resolve U (axiom_ (leftInput n)) (p n)).label =
      GCNF.Clause.ofList [r n, p (n + 1)] := by
  apply LCS.Finset.ext
  intro L
  cases L <;>
    simp [label, hU, leftInput, GCNF.Clause.ofList, GCNF.Clause.single,
      GCNF.Clause.union, GCNF.Clause.remove, Literal.conjugate,
      LCS.Finset.mem_erase, LCS.Finset.mem_singleton, p, r] <;> omega

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem right_label (n : Nat) (U : ResolutionTree)
    (hU : U.label = GCNF.Clause.single (p n)) :
    (resolve U (axiom_ (rightInput n)) (p n)).label =
      GCNF.Clause.ofList [(r n).conjugate, p (n + 1)] := by
  apply LCS.Finset.ext
  intro L
  cases L <;>
    simp [label, hU, rightInput, GCNF.Clause.ofList, GCNF.Clause.single,
      GCNF.Clause.union, GCNF.Clause.remove, Literal.conjugate,
      LCS.Finset.mem_erase, LCS.Finset.mem_singleton, p] <;> omega

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem units_label (n : Nat) : (units n).label = GCNF.Clause.single (p n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (resolve _ _ _).label = _
    rw [label, left_label n _ ih, right_label n _ ih]
    apply LCS.Finset.ext
    intro L
    cases L <;>
      simp [GCNF.Clause.ofList, GCNF.Clause.single, GCNF.Clause.union,
        GCNF.Clause.remove, Literal.conjugate, LCS.Finset.mem_erase,
        LCS.Finset.mem_singleton, p, r] <;> omega



-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem units_wellFormed (n : Nat) : (units n).IsWellFormed := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨⟨ih, True.intro, ?_, ?_⟩, ⟨ih, True.intro, ?_, ?_⟩, ?_, ?_⟩
    · simp [units_label, GCNF.Clause.single]
    · simp [label, leftInput, GCNF.Clause.ofList, p, Literal.conjugate]
    · simp [units_label, GCNF.Clause.single]
    · simp [label, rightInput, GCNF.Clause.ofList, p, Literal.conjugate]
    · rw [left_label n _ (units_label n)]
      simp [GCNF.Clause.ofList]
    · rw [right_label n _ (units_label n)]
      simp [GCNF.Clause.ofList]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem refutation_wellFormed (n : Nat) : (refutation n).IsWellFormed := by
  refine ⟨units_wellFormed n, True.intro, ?_, ?_⟩
  · simp [units_label, GCNF.Clause.single]
  · simp [label, GCNF.Clause.single]





@[blueprint "chap4__theorem_4_3_3"]
theorem refutation_inputs_ordinary (n : Nat) : (refutation n).inputs.isOrdinary 


-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem leftInput_not_single (n : Nat) (L : Literal) :
    leftInput n ≠ GCNF.Clause.single L := by
  intro h
  have ha : Literal.neg (2 * n) ∈ GCNF.Clause.single L := h ▸ (by simp [leftInput, GCNF.Clause.ofList])
  have hb : p (n + 1) ∈ GCNF.Clause.single L := h ▸ (by simp [leftInput, GCNF.Clause.ofList])
  cases L <;> simp [GCNF.Clause.single, p] at *

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem rightInput_not_single (n : Nat) (L : Literal) :
    rightInput n ≠ GCNF.Clause.single L := by
  intro h
  have ha : Literal.neg (2 * n) ∈ GCNF.Clause.single L := h ▸ (by simp [rightInput, GCNF.Clause.ofList])
  have hb : p (n + 1) ∈ GCNF.Clause.single L := h ▸ (by simp [rightInput, GCNF.Clause.ofList])
  cases L <;> simp [GCNF.Clause.single, p] at *

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem leftResidual_not_single (n : Nat) (L : Literal) :
    leftResidual n ≠ GCNF.Clause.single L := by
  intro h
  have ha : Literal.neg (2 * n) ∈ GCNF.Clause.single L := h ▸ (by simp [leftResidual, GCNF.Clause.ofList])
  have hb : r n ∈ GCNF.Clause.single L := h ▸ (by simp [leftResidual, GCNF.Clause.ofList])
  cases L <;> simp [GCNF.Clause.single, r] at *

-- ATTACH-BLOCKER: private declaration
private theorem rightResidual_not_single (n : Nat) (L : Literal) :
    rightResidual n ≠ GCNF.Clause.single L := by
  intro h
  have ha : Literal.neg (2 * n) ∈ GCNF.Clause.single L := h ▸ (by simp [rightResidual, GCNF.Clause.ofList])
  have hb : (r n).conjugate ∈ GCNF.Clause.single L := h ▸ (by simp [rightResidual, GCNF.Clause.ofList])
  cases L <;> simp [GCNF.Clause.single, Literal.conjugate] at * <;> omega































-- ATTACH-BLOCKER: private declaration
@[simp] private theorem single_ne_leftInput (n : Nat) (L : Literal) :
    GCNF.Clause.single L ≠ leftInput n := Ne.symm (leftInput_not_single n L)
-- ATTACH-BLOCKER: private declaration
@[simp] private theorem single_ne_rightInput (n : Nat) (L : Literal) :
    GCNF.Clause.single L ≠ rightInput n := Ne.symm (rightInput_not_single n L)
-- ATTACH-BLOCKER: private declaration
@[simp] private theorem single_ne_leftResidual (n : Nat) (L : Literal) :
    GCNF.Clause.single L ≠ leftResidual n := Ne.symm (leftResidual_not_single n L)
-- ATTACH-BLOCKER: private declaration
@[simp] private theorem single_ne_rightResidual (n : Nat) (L : Literal) :
    GCNF.Clause.single L ≠ rightResidual n := Ne.symm (rightResidual_not_single n L)











end LCS.Resolution.Method.ReverseGrowth


namespace LCS.Resolution.Method.FiniteGraph

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Appending or otherwise extending a topological table preserves the unfolded
    tree at each old vertex when all old rows keep their contents. -/
theorem unfoldAt_eq_of_node_prefix
    (g h : FiniteGraph) (htG : g.Topological) (htH : h.Topological)
    (hnodes : ∀ i, i < g.table.length → h.node i = g.node i) :
    ∀ (i : Nat) (hiG : i < g.table.length) (hiH : i < h.table.length),
      h.unfoldAt htH i hiH = g.unfoldAt htG i hiG := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hiG hiH
    let n := g.table[i]
    have hnG : g.node i = some n := by simp [node, n, hiG]
    have hnH : h.node i = some n := (hnodes i hiG).trans hnG
    cases hr : n.inference with
    | none =>
      rw [LCS.Resolution.Method.FiniteGraph.unfoldAt_leaf h htH i hiH n hnH hr,
        LCS.Resolution.Method.FiniteGraph.unfoldAt_leaf g htG i hiG n hnG hr]
    | some r =>
      have hltG := htG i n hnG r hr
      have hltH := htH i n hnH r hr
      rw [LCS.Resolution.Method.FiniteGraph.unfoldAt_step h htH i hiH n hnH r hr,
        LCS.Resolution.Method.FiniteGraph.unfoldAt_step g htG i hiG n hnG r hr]
      rw [ih r.left hltG.1 (Nat.lt_trans hltG.1 hiG) (Nat.lt_trans hltH.1 hiH),
        ih r.right hltG.2 (Nat.lt_trans hltG.2 hiG) (Nat.lt_trans hltH.2 hiH)]

end LCS.Resolution.Method.FiniteGraph


namespace LCS.Resolution.Method.ReverseGrowthGraph
open LCS.Resolution.GCNF
open FiniteGraph

@[blueprint "chap4__theorem_4_3_3"]
def pos (n : Nat) : Literal := .pos (2 * n)
@[blueprint "chap4__theorem_4_3_3"]
def aux (n : Nat) : Literal := .pos (2 * n + 1)
@[blueprint "chap4__theorem_4_3_3"]
def unit (n : Nat) : Clause := GCNF.Clause.single (pos n)
@[blueprint "chap4__theorem_4_3_3"]
def input (n : Nat) (r : Literal) : Clause :=
  GCNF.Clause.ofList [(pos n).conjugate, r, pos (n+1)]
@[blueprint "chap4__theorem_4_3_3"]
def middle (n : Nat) (r : Literal) : Clause := GCNF.Clause.ofList [r, pos (n+1)]
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem pos_mem_unit (n : Nat) : pos n ∈ unit n := by
  simp [unit, GCNF.Clause.single]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem conjugate_pos_mem_input (n : Nat) (r : Literal) :
    (pos n).conjugate ∈ input n r := by
  simp [input, GCNF.Clause.ofList]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem mem_middle (n : Nat) (r : Literal) : r ∈ middle n r := by
  simp [middle, GCNF.Clause.ofList]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem conjugate_pos_mem_negativeUnit (n : Nat) :
    (pos n).conjugate ∈ GCNF.Clause.single (pos n).conjugate := by
  simp [GCNF.Clause.single]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem middle_eq (n : Nat) (r : Literal) (hr : r ≠ (pos n).conjugate) :
    middle n r = GCNF.Clause.union
      (GCNF.Clause.remove (unit n) (pos n))
      (GCNF.Clause.remove (input n r) (pos n).conjugate) := by
  apply LCS.Finset.ext
  intro x
  cases x <;> cases r <;>
    simp [middle, input, unit, pos, GCNF.Clause.ofList,
      GCNF.Clause.union, GCNF.Clause.single, GCNF.Clause.remove,
      LCS.Finset.mem_union_exp, LCS.Finset.mem_erase, Literal.conjugate] at * <;> grind

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem aux_ne_conjugate_pos (n : Nat) : aux n ≠ (pos n).conjugate := by
  simp [aux, pos, Literal.conjugate]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem conjugate_aux_ne_conjugate_pos (n : Nat) :
    (aux n).conjugate ≠ (pos n).conjugate := by
  simp [aux, pos, Literal.conjugate]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem positiveMiddle_eq (n : Nat) :
    middle n (aux n) = GCNF.Clause.union
      (GCNF.Clause.remove (unit n) (pos n))
      (GCNF.Clause.remove (input n (aux n)) (pos n).conjugate) :=
  middle_eq n (aux n) (aux_ne_conjugate_pos n)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem negativeMiddle_eq (n : Nat) :
    middle n (aux n).conjugate = GCNF.Clause.union
      (GCNF.Clause.remove (unit n) (pos n))
      (GCNF.Clause.remove (input n (aux n).conjugate) (pos n).conjugate) :=
  middle_eq n (aux n).conjugate (conjugate_aux_ne_conjugate_pos n)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem nextUnit_eq (n : Nat) :
    unit (n + 1) = GCNF.Clause.union
      (GCNF.Clause.remove (middle n (aux n)) (aux n))
      (GCNF.Clause.remove (middle n (aux n).conjugate) (aux n).conjugate) := by
  apply LCS.Finset.ext
  intro x
  cases x <;>
    simp [middle, unit, pos, aux, GCNF.Clause.ofList,
      GCNF.Clause.union, GCNF.Clause.single, GCNF.Clause.remove,
      LCS.Finset.mem_union_exp, LCS.Finset.mem_erase, Literal.conjugate] <;> omega

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem empty_eq_resolveUnits (n : Nat) :
    GCNF.Clause.empty = GCNF.Clause.union
      (GCNF.Clause.remove (unit n) (pos n))
      (GCNF.Clause.remove (GCNF.Clause.single (pos n).conjugate)
        (pos n).conjugate) := by
  apply LCS.Finset.ext
  intro x
  simp [unit, GCNF.Clause.empty, GCNF.Clause.union, GCNF.Clause.single, GCNF.Clause.remove,
    LCS.Finset.mem_union_exp, LCS.Finset.mem_erase]
  exact LCS.Finset.not_mem_empty


@[blueprint "chap4__theorem_4_3_3"]
def block (n : Nat) : List Node :=
  [⟨(input n (aux n)), none⟩,
   ⟨(input n (aux n).conjugate), none⟩,
   ⟨(middle n (aux n)), some ⟨(pos n), (5*n), (5*n+1)⟩⟩,
   ⟨(middle n (aux n).conjugate), some ⟨(pos n), (5*n), (5*n+2)⟩⟩,
   ⟨(unit (n+1)), some ⟨(aux n), (5*n+3), (5*n+4)⟩⟩]
@[blueprint "chap4__theorem_4_3_3"]
def table : Nat → List Node
  | 0 => [⟨(unit 0), none⟩]
  | n+1 => table n ++ block n
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
def graph (n : Nat) : FiniteGraph := ⟨table n, 5*n⟩
@[blueprint "chap4__theorem_4_3_3"]
def refutation (n : Nat) : FiniteGraph :=
  ⟨table n ++ [⟨(GCNF.Clause.single (pos n).conjugate), none⟩,
    ⟨GCNF.Clause.empty, some ⟨(pos n), (5*n), (5*n+1)⟩⟩], 5*n+2⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem table_length (n : Nat) : (table n).length = 5*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [table, block, ih]; omega

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem graph_table_length (n : Nat) : (graph n).table.length = 5*n+1 :=
  table_length n

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem refutation_table_length (n : Nat) :
    (refutation n).table.length = 5*n+3 := by simp [refutation] <;> omega

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem graph_root (n : Nat) : (graph n).root = 5*n := rfl
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem refutation_root (n : Nat) : (refutation n).root = 5*n+2 := rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem graph_node_old (n i : Nat) (hi : i < 5*n+1) :
    (graph (n+1)).node i = (graph n).node i := by
  simp only [FiniteGraph.node, graph, table]
  rw [List.getElem?_append_left (by simpa using hi)]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem graph_node_new (n j : Nat) :
    (graph (n+1)).node (5*n+1+j) = (block n)[j]? := by
  simp only [FiniteGraph.node, graph, table]
  rw [List.getElem?_append_right (by simp <;> omega)]
  congr 1
  simp

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem graph_node_root (n : Nat) :
    (graph n).node (5*n) = some (if n = 0 then ⟨(unit 0), none⟩
      else ⟨(unit n), some ⟨(aux (n-1)), (5*(n-1)+3), (5*(n-1)+4)⟩⟩) := by
  cases n with
  | zero => rfl
  | succ n =>
    have he : 5*(n+1) = 5*n+1+4 := by omega
    rw [he, graph_node_new]
    simp [block]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem graph_rootLabel (n : Nat) : (graph n).rootLabel = some (unit n) := by
  simp [FiniteGraph.rootLabel, FiniteGraph.label, graph_node_root]
  split <;> rename_i h
  · subst n; rfl
  · rfl

end LCS.Resolution.Method.ReverseGrowthGraph

namespace LCS.Resolution.Method.ReverseGrowthGraph
open LCS.Resolution.GCNF
open FiniteGraph

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A table extension preserves reachability from every retained root. -/
theorem vertexIds_extension {g h : FiniteGraph}
    (hg : g.WellFormed) (hh : h.WellFormed)
    (hn : ∀ i, i < g.table.length → h.node i = g.node i)
    (hr : g.root ∈ h.vertexIds) {i : Nat} (hi : i ∈ g.vertexIds) :
    i ∈ h.vertexIds := by
  obtain ⟨a, ha, _⟩ := (mem_vertexIds_iff g i).mp hi
  have hp : g.root ∈ g.vertexIds ∧ g.root ∈ h.vertexIds :=
    ⟨LCS.Resolution.Method.FiniteGraph.root_mem_vertexIds g hg, hr⟩
  have hclosed : ∀ j p k, j ∈ g.vertexIds ∧ j ∈ h.vertexIds →
      g.next j p = some k → k ∈ g.vertexIds ∧ k ∈ h.vertexIds := by
    intro j p k hj hk
    refine ⟨LCS.Resolution.Method.FiniteGraph.next_mem_vertexIds hg hj.1 hk, LCS.Resolution.Method.FiniteGraph.next_mem_vertexIds (p := p) hh hj.2 ?_⟩
    simpa only [FiniteGraph.next, hn j (LCS.Resolution.Method.FiniteGraph.vertexIds_index_lt hg hj.1)] using hk
  exact (LCS.Resolution.Method.FiniteGraph.followFrom_closed hclosed hp ha).2

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Exact vertex count when every row belongs to the rooted graph. -/
theorem nodeCount_eq_length {g : FiniteGraph} (hg : g.WellFormed)
    (hreach : ∀ i, i < g.table.length → i ∈ g.vertexIds) :
    g.nodeCount = g.table.length := by
  have hp := LCS.list_perm_of_nodup_of_mem_iff
    (LCS.Resolution.Method.FiniteGraph.vertexIds_nodup g) (List.nodup_range (n := g.table.length))
    (fun i => show i ∈ g.vertexIds ↔ i ∈ List.range g.table.length from
      ⟨fun hi => List.mem_range.mpr (LCS.Resolution.Method.FiniteGraph.vertexIds_index_lt hg hi),
       fun hi => hreach i (List.mem_range.mp hi)⟩)
  simpa [FiniteGraph.nodeCount] using hp.length_eq

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem graph_node_leftInput (n : Nat) :
    (graph (n+1)).node (5*n+1) = some (⟨(input n (aux n)), none⟩) := by
  simpa [block] using graph_node_new n 0

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem graph_node_rightInput (n : Nat) :
    (graph (n+1)).node (5*n+2) = some (⟨(input n (aux n).conjugate), none⟩) := by
  simpa [block, Nat.add_assoc] using graph_node_new n 1

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem graph_node_leftMiddle (n : Nat) :
    (graph (n+1)).node (5*n+3) =
      some (⟨(middle n (aux n)), some ⟨(pos n), (5*n), (5*n+1)⟩⟩) := by
  simpa [block, Nat.add_assoc] using graph_node_new n 2

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem graph_node_rightMiddle (n : Nat) :
    (graph (n+1)).node (5*n+4) =
      some (⟨(middle n (aux n).conjugate), some ⟨(pos n), (5*n), (5*n+2)⟩⟩) := by
  simpa [block, Nat.add_assoc] using graph_node_new n 3

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem graph_node_newRoot (n : Nat) :
    (graph (n+1)).node (5*n+5) =
      some (⟨(unit (n+1)), some ⟨(aux n), (5*n+3), (5*n+4)⟩⟩) := by
  simpa [block, Nat.add_assoc] using graph_node_new n 4

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem graph_root_node_exists (n : Nat) :
    ∃ a, (graph n).node (5*n) = some a ∧ a.clause = unit n := by
  have h := graph_rootLabel n
  simp only [FiniteGraph.rootLabel, FiniteGraph.label, graph_root] at h
  cases hn : (graph n).node (5*n) with
  | none => simp [hn] at h
  | some a => exact ⟨a, rfl, Option.some.inj (by simpa [hn] using h)⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem graph_allRows_step (n : Nat) (hg : (graph n).AllRowsWellFormed)
    (hfirst : ∀ r ∈ [aux n, (aux n).conjugate],
      pos n ∈ unit n ∧ (pos n).conjugate ∈ input n r ∧
      middle n r = GCNF.Clause.union (GCNF.Clause.remove (unit n) (pos n))
        (GCNF.Clause.remove (input n r) (pos n).conjugate))
    (hlast : aux n ∈ middle n (aux n) ∧
      (aux n).conjugate ∈ middle n (aux n).conjugate ∧
      unit (n+1) = GCNF.Clause.union
        (GCNF.Clause.remove (middle n (aux n)) (aux n))
        (GCNF.Clause.remove (middle n (aux n).conjugate) (aux n).conjugate)) :
    (graph (n+1)).AllRowsWellFormed := by
  refine ⟨by simp <;> omega, ?_⟩
  intro i v hv r hr
  by_cases hi : i < 5*n+1
  · have hv' : (graph n).node i = some v := by
      rwa [graph_node_old n i hi] at hv
    obtain ⟨hl, hright, a, b, ha, hb, hp, hc, heq⟩ := hg.2 i v hv' r hr
    refine ⟨hl, hright, a, b, ?_, ?_, hp, hc, heq⟩
    · rw [graph_node_old n r.left (by omega)]; exact ha
    · rw [graph_node_old n r.right (by omega)]; exact hb
  · have hib := LCS.Resolution.Method.FiniteGraph.node_index_lt hv
    simp only [graph_table_length] at hib
    have hiCases : i = 5*n+1 ∨ i = 5*n+2 ∨ i = 5*n+3 ∨
        i = 5*n+4 ∨ i = 5*n+5 := by omega
    rcases hiCases with rfl | rfl | rfl | rfl | rfl
    · simp only [graph_node_leftInput, Option.some.injEq] at hv
      subst v
      simp at hr
    · simp only [graph_node_rightInput, Option.some.injEq] at hv
      subst v
      simp at hr
    · simp only [graph_node_leftMiddle, Option.some.injEq] at hv
      subst v
      cases hr
      obtain ⟨a, ha, hac⟩ := graph_root_node_exists n
      have hf := hfirst (aux n) (by simp)
      refine ⟨by simp <;> omega, by simp <;> omega, a, ⟨(input n (aux n)), none⟩, ?_,
        graph_node_leftInput n, ?_, hf.2.1, ?_⟩
      · rw [graph_node_old n (5*n) (by omega)]; exact ha
      · simp [hac]
      · simpa [hac] using hf.2.2
    · simp only [graph_node_rightMiddle, Option.some.injEq] at hv
      subst v
      cases hr
      obtain ⟨a, ha, hac⟩ := graph_root_node_exists n
      have hf := hfirst (aux n).conjugate (by simp)
      refine ⟨by simp <;> omega, by simp <;> omega, a, ⟨(input n (aux n).conjugate), none⟩, ?_,
        graph_node_rightInput n, ?_, hf.2.1, ?_⟩
      · rw [graph_node_old n (5*n) (by omega)]; exact ha
      · simp [hac]
      · simpa [hac] using hf.2.2
    · simp only [graph_node_newRoot, Option.some.injEq] at hv
      subst v
      cases hr
      exact ⟨by simp <;> omega, by simp <;> omega,
        ⟨(middle n (aux n)), some ⟨(pos n), (5*n), (5*n+1)⟩⟩,
        ⟨(middle n (aux n).conjugate), some ⟨(pos n), (5*n), (5*n+2)⟩⟩,
        graph_node_leftMiddle n, graph_node_rightMiddle n,
        hlast.1, hlast.2.1, hlast.2.2⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem graph_all_reachable
    (hwell : ∀ n, (graph n).WellFormed) (n : Nat) :
    ∀ i, i < 5*n+1 → i ∈ (graph n).vertexIds := by
  induction n with
  | zero =>
    intro i hi
    have he : i = 0 := by omega
    subst i
    exact LCS.Resolution.Method.FiniteGraph.root_mem_vertexIds (graph 0) (hwell 0)
  | succ n ih =>
    have hr : 5*n+5 ∈ (graph (n+1)).vertexIds := by
      have h := LCS.Resolution.Method.FiniteGraph.root_mem_vertexIds (graph (n+1)) (hwell (n+1))
      simpa [graph, Nat.mul_add] using h
    have hleft : 5*n+3 ∈ (graph (n+1)).vertexIds :=
      LCS.Resolution.Method.FiniteGraph.next_mem_vertexIds (p := 0) (hwell (n+1)) hr
        (by simp [FiniteGraph.next])
    have hright : 5*n+4 ∈ (graph (n+1)).vertexIds :=
      LCS.Resolution.Method.FiniteGraph.next_mem_vertexIds (p := 1) (hwell (n+1)) hr
        (by simp [FiniteGraph.next])
    have hold : 5*n ∈ (graph (n+1)).vertexIds :=
      LCS.Resolution.Method.FiniteGraph.next_mem_vertexIds (p := 0) (hwell (n+1)) hleft
        (by simp [FiniteGraph.next])
    have hinput1 : 5*n+1 ∈ (graph (n+1)).vertexIds :=
      LCS.Resolution.Method.FiniteGraph.next_mem_vertexIds (p := 1) (hwell (n+1)) hleft
        (by simp [FiniteGraph.next])
    have hinput2 : 5*n+2 ∈ (graph (n+1)).vertexIds :=
      LCS.Resolution.Method.FiniteGraph.next_mem_vertexIds (p := 1) (hwell (n+1)) hright
        (by simp [FiniteGraph.next])
    intro i hi
    by_cases hiold : i < 5*n+1
    · exact vertexIds_extension (hwell n) (hwell (n+1))
        (fun j hj => graph_node_old n j (by simpa using hj)) hold (ih i hiold)
    · have hcases : i = 5*n+1 ∨ i = 5*n+2 ∨ i = 5*n+3 ∨
          i = 5*n+4 ∨ i = 5*n+5 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl
      · exact hinput1
      · exact hinput2
      · exact hleft
      · exact hright
      · exact hr



-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem refutation_node_old (n i : Nat) (hi : i < 5*n+1) :
    (refutation n).node i = (graph n).node i := by
  simp only [FiniteGraph.node, refutation, graph]
  rw [List.getElem?_append_left (by simpa using hi)]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem refutation_node_input (n : Nat) :
    (refutation n).node (5*n+1) = some (⟨(GCNF.Clause.single (pos n).conjugate), none⟩) := by
  simp [FiniteGraph.node, refutation, table_length]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem refutation_node_root (n : Nat) :
    (refutation n).node (5*n+2) = some (⟨GCNF.Clause.empty, some ⟨(pos n), (5*n), (5*n+1)⟩⟩) := by
  simp [FiniteGraph.node, refutation, table_length]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem refutation_all_reachable
    (hwell : ∀ n, (graph n).WellFormed) (n : Nat)
    (href : (refutation n).WellFormed) :
    ∀ i, i < 5*n+3 → i ∈ (refutation n).vertexIds := by
  have hr : 5*n+2 ∈ (refutation n).vertexIds := LCS.Resolution.Method.FiniteGraph.root_mem_vertexIds _ href
  have hold : 5*n ∈ (refutation n).vertexIds :=
    LCS.Resolution.Method.FiniteGraph.next_mem_vertexIds (p := 0) href hr (by simp [FiniteGraph.next])
  have hinput : 5*n+1 ∈ (refutation n).vertexIds :=
    LCS.Resolution.Method.FiniteGraph.next_mem_vertexIds (p := 1) href hr (by simp [FiniteGraph.next])
  intro i hi
  by_cases hio : i < 5*n+1
  · exact vertexIds_extension (hwell n) href
      (fun j hj => refutation_node_old n j (by simpa using hj)) hold
      (graph_all_reachable hwell n i hio)
  · have hc : i = 5*n+1 ∨ i = 5*n+2 := by omega
    rcases hc with rfl | rfl
    · exact hinput
    · exact hr

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem refutation_nodeCount_of_wellFormed
    (hwell : ∀ n, (graph n).WellFormed) (n : Nat)
    (href : (refutation n).WellFormed) :
    (refutation n).nodeCount = 5*n+3 := by
  rw [nodeCount_eq_length href
    (fun i hi => refutation_all_reachable hwell n href i (by simpa using hi))]
  exact refutation_table_length n

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem graph_allRowsWellFormed (n : Nat) : (graph n).AllRowsWellFormed := by
  induction n with
  | zero =>
    refine ⟨by decide, ?_⟩
    intro i v hv r hr
    cases i with
    | zero => simp only [FiniteGraph.node, graph, table, List.getElem?_cons_zero,
        Option.some.injEq] at hv
              subst v
              simp at hr
    | succ i => simp [FiniteGraph.node, graph, table] at hv
  | succ n ih =>
    apply graph_allRows_step n ih
    · intro r hr
      refine ⟨pos_mem_unit n, conjugate_pos_mem_input n r, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact positiveMiddle_eq n
      · exact negativeMiddle_eq n
    · exact ⟨mem_middle n _, mem_middle n _, nextUnit_eq n⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem graph_wellFormed (n : Nat) : (graph n).WellFormed :=
  (graph_allRowsWellFormed n).wellFormed



-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem refutation_allRowsWellFormed (n : Nat) :
    (refutation n).AllRowsWellFormed := by
  refine ⟨by simp <;> omega, ?_⟩
  intro i v hv r hr
  by_cases hi : i < 5*n+1
  · have hv' : (graph n).node i = some v := by
      rwa [refutation_node_old n i hi] at hv
    obtain ⟨hl, hright, a, b, ha, hb, hp, hc, heq⟩ :=
      (graph_allRowsWellFormed n).2 i v hv' r hr
    refine ⟨hl, hright, a, b, ?_, ?_, hp, hc, heq⟩
    · rw [refutation_node_old n r.left (by omega)]; exact ha
    · rw [refutation_node_old n r.right (by omega)]; exact hb
  · have hib := LCS.Resolution.Method.FiniteGraph.node_index_lt hv
    simp only [refutation_table_length] at hib
    have hc : i = 5*n+1 ∨ i = 5*n+2 := by omega
    rcases hc with rfl | rfl
    · simp only [refutation_node_input, Option.some.injEq] at hv
      subst v
      simp at hr
    · simp only [refutation_node_root, Option.some.injEq] at hv
      subst v
      cases hr
      obtain ⟨a, ha, hac⟩ := graph_root_node_exists n
      refine ⟨by simp <;> omega, by simp <;> omega,
        a, ⟨(GCNF.Clause.single (pos n).conjugate), none⟩, ?_, refutation_node_input n,
        ?_, conjugate_pos_mem_negativeUnit n, ?_⟩
      · rw [refutation_node_old n (5*n) (by omega)]; exact ha
      · simp [hac]
      · simpa [hac] using empty_eq_resolveUnits n

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem refutation_wellFormed (n : Nat) : (refutation n).WellFormed :=
  (refutation_allRowsWellFormed n).wellFormed

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem refutation_nodeCount (n : Nat) : (refutation n).nodeCount = 5*n+3 :=
  refutation_nodeCount_of_wellFormed graph_wellFormed n (refutation_wellFormed n)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
@[simp] theorem refutation_rootLabel (n : Nat) :
    (refutation n).rootLabel = some GCNF.Clause.empty := by
  simp [FiniteGraph.rootLabel, FiniteGraph.label]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The graph unfolds to precisely the recursively duplicated unit derivation. -/
theorem graph_unfold_eq (t : Nat → ResolutionTree)
    (hzero : t 0 = .axiom_ (unit 0))
    (hsucc : ∀ n, t (n+1) = .resolve
      (.resolve (t n) (.axiom_ (input n (aux n))) (pos n))
      (.resolve (t n) (.axiom_ (input n (aux n).conjugate)) (pos n)) (aux n))
    (n : Nat) : (graph n).unfold (graph_wellFormed n) = t n := by
  induction n with
  | zero =>
    rw [hzero]
    exact LCS.Resolution.Method.FiniteGraph.unfoldAt_leaf (graph 0) (graph_wellFormed 0).2.1 0
      (graph_wellFormed 0).1 (⟨(unit 0), none⟩) rfl rfl
  | succ n ih =>
    rw [hsucc]
    have hOld : ∀ hi, (graph (n+1)).unfoldAt (graph_wellFormed (n+1)).2.1
        (5*n) hi = t n := by
      intro hi
      rw [unfoldAt_eq_of_node_prefix (graph n) (graph (n+1))
        (graph_wellFormed n).2.1 (graph_wellFormed (n+1)).2.1
        (fun i hi => graph_node_old n i (by simpa using hi))
        (5*n) (graph_wellFormed n).1 hi]
      exact ih
    change (graph (n+1)).unfoldAt (graph_wellFormed (n+1)).2.1 (5*n+5) _ = _
    refine (LCS.Resolution.Method.FiniteGraph.unfoldAt_step (graph (n+1)) (graph_wellFormed (n+1)).2.1
      (5*n+5) _ _ (graph_node_newRoot n) _ rfl).trans ?_
    rw [LCS.Resolution.Method.FiniteGraph.unfoldAt_step (graph (n+1)) (graph_wellFormed (n+1)).2.1
      (5*n+3) _ _ (graph_node_leftMiddle n) _ rfl]
    rw [LCS.Resolution.Method.FiniteGraph.unfoldAt_step (graph (n+1)) (graph_wellFormed (n+1)).2.1
      (5*n+4) _ _ (graph_node_rightMiddle n) _ rfl]
    rw [LCS.Resolution.Method.FiniteGraph.unfoldAt_leaf (graph (n+1)) (graph_wellFormed (n+1)).2.1
      (5*n+1) _ _ (graph_node_leftInput n) rfl]
    rw [LCS.Resolution.Method.FiniteGraph.unfoldAt_leaf (graph (n+1)) (graph_wellFormed (n+1)).2.1
      (5*n+2) _ _ (graph_node_rightInput n) rfl]
    rw [hOld]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The two appended rows refute exactly that unfolded unit derivation. -/
theorem refutation_unfold_eq (t : Nat → ResolutionTree)
    (hzero : t 0 = .axiom_ (unit 0))
    (hsucc : ∀ n, t (n+1) = .resolve
      (.resolve (t n) (.axiom_ (input n (aux n))) (pos n))
      (.resolve (t n) (.axiom_ (input n (aux n).conjugate)) (pos n)) (aux n))
    (n : Nat) : (refutation n).unfold (refutation_wellFormed n) =
      .resolve (t n) (.axiom_ (GCNF.Clause.single (pos n).conjugate)) (pos n) := by
  change (refutation n).unfoldAt (refutation_wellFormed n).2.1 (5*n+2) _ = _
  refine (LCS.Resolution.Method.FiniteGraph.unfoldAt_step (refutation n) (refutation_wellFormed n).2.1
    (5*n+2) _ _ (refutation_node_root n) _ rfl).trans ?_
  rw [LCS.Resolution.Method.FiniteGraph.unfoldAt_leaf (refutation n) (refutation_wellFormed n).2.1
    (5*n+1) _ _ (refutation_node_input n) rfl]
  rw [unfoldAt_eq_of_node_prefix (graph n) (refutation n)
    (graph_wellFormed n).2.1 (refutation_wellFormed n).2.1
    (fun i hi => refutation_node_old n i (by simpa using hi))
    (5*n) (graph_wellFormed n).1 _]
  rw [show (graph n).unfoldAt (graph_wellFormed n).2.1 (5*n) (graph_wellFormed n).1 = t n
    from graph_unfold_eq t hzero hsucc n]

end LCS.Resolution.Method.ReverseGrowthGraph


namespace LCS.Resolution.Method.ReverseGrowth

open LCS.Resolution.GCNF



/-- The family consists of refutations of ordinary input clauses. -/
@[blueprint "chap4__theorem_4_3_3"]
theorem graph_refutes (n : Nat) :
    (ReverseGrowthGraph.refutation n).IsRefutationFor (refutation n).inputs 

/-- Linear-size graphs produce proof trees with exponentially many axioms.
Both counts refer to the concrete graph and the actual converter output. -/
@[blueprint "chap4__theorem_4_3_3"]
theorem linear_graph_exponential_output (n : Nat) :
    (ReverseGrowthGraph.refutation n).nodeCount = 5 * n + 3 ∧
    ((ReverseGrowthGraph.refutation n).toGCNF (refutation n).inputs
      (graph_refutes n) (refutation_inputs_ordinary n)).leafCount + 2 = 3 * 2 ^ n 

/-- The same growth comparison counts all vertices of the returned GCNF tree. -/
@[blueprint "chap4__theorem_4_3_3"]
theorem actual_graph_output_nodeCount (n : Nat) :
    ((ReverseGrowthGraph.refutation n).toGCNF (refutation n).inputs
      (graph_refutes n) (refutation_inputs_ordinary n)).nodeCount + 5 = 6 * 2 ^ n 

end LCS.Resolution.Method.ReverseGrowth
