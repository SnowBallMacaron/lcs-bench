import LCS.Item
import LCS.Util
import LCS.Resolution.GCNF
import Attach
import LCS.Resolution.Method.ResolutionDAGs
import LCS.Resolution.Method.RefutationExample.ProofsStamp

/-! # Example 4.3.4: a resolution refutation with a shared leaf
-/
section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

-- ========= Example 4.3.4: Resolution Refutation =========

/-- Example 4.3.4 (companion): The 9-address domain of the refutation DAG. -/
@[blueprint "chap4__example_4_3_4"]
def exResolutionRefutation_dom : TreeAddr → Prop :=
  fun a =>
    a = [] ∨ a = [0] ∨ a = [0, 0] ∨ a = [0, 1] ∨
    a = [1] ∨ a = [1, 0] ∨ a = [1, 0, 0] ∨ a = [1, 0, 1] ∨ a = [1, 1]

/-- Example 4.3.4 (companion): Prefix closure for the refutation
    DAG domain. -/
@[blueprint "chap4__example_4_3_4"]
theorem exResolutionRefutation_prefix_closed :
    ∀ u v, (u ++ v) ∈ exResolutionRefutation_dom →
      u ∈ exResolutionRefutation_dom 

/-- Example 4.3.4 (companion): Left-sibling closure for the refutation
    DAG domain. -/
@[blueprint "chap4__example_4_3_4"]
theorem exResolutionRefutation_left_sibling_closed :
    ∀ u i, (u ++ [i + 1]) ∈ exResolutionRefutation_dom →
      (u ++ [i]) ∈ exResolutionRefutation_dom 

/-- Example 4.3.4 (companion): Tree domain for the refutation DAG. -/
@[blueprint "chap4__example_4_3_4"]
def exResolutionRefutation_domain : TreeDomain where
  dom := exResolutionRefutation_dom
  root_mem := Or.inl rfl
  prefix_closed := exResolutionRefutation_prefix_closed
  left_sibling_closed := exResolutionRefutation_left_sibling_closed

/-- Example 4.3.4 (companion): Labeling of the 9 addresses in the
    refutation DAG tree. -/
@[blueprint "chap4__example_4_3_4"]
def exResolutionRefutation_label (P Q : Nat)
    (a : TreeAddr) (_ha : a ∈ exResolutionRefutation_domain.dom) : Clause :=
  match a with
  | []         => GCNF.Clause.empty        -- □
  | [0]        => GCNF.Clause.ofList [Literal.pos P]   -- {P}
  | [0, 0]     => GCNF.Clause.ofList [Literal.pos P, Literal.pos Q]   -- {P,Q}
  | [0, 1]     => GCNF.Clause.ofList [Literal.pos P, Literal.neg Q]   -- {P,¬Q}
  | [1]        => GCNF.Clause.ofList [Literal.neg P]   -- {¬P}
  | [1, 0]     => GCNF.Clause.ofList [Literal.pos Q]   -- {Q}
  | [1, 0, 0]  => GCNF.Clause.ofList [Literal.pos P, Literal.pos Q]   -- {P,Q}
  | [1, 0, 1]  => GCNF.Clause.ofList [Literal.neg P, Literal.pos Q]   -- {¬P,Q}
  | [1, 1]     => GCNF.Clause.ofList [Literal.neg P, Literal.neg Q]   -- {¬P,¬Q}
  | _          => GCNF.Clause.empty  -- unreachable

/-- Example 4.3.4 (companion): Labeled tree underlying the refutation DAG. -/
@[blueprint "chap4__example_4_3_4"]
def exResolutionRefutation_tree (P Q : Nat) : LabeledTree Clause where
  domain := exResolutionRefutation_domain
  label := (exResolutionRefutation_label P Q)

/-- Example 4.3.4 (companion): Equivalence relation on tree addresses for
    the refutation DAG, identifying `[0,0]` with `[1,0,0]`. -/
@[blueprint "chap4__example_4_3_4"]
def exResolutionRefutation_rel : TreeAddr → TreeAddr → Prop :=
  fun u v =>
    u = v ∨ (u = [0, 0] ∧ v = [1, 0, 0]) ∨ (u = [1, 0, 0] ∧ v = [0, 0])

/-- Example 4.3.4 (companion): `exResolutionRefutation_rel` is an
    equivalence relation. -/
@[blueprint "chap4__example_4_3_4"]
theorem exResolutionRefutation_rel_equiv :
    Equivalence exResolutionRefutation_rel 

/-- Example 4.3.4 (companion): Address independence for the refutation
    DAG's relation. -/
@[blueprint "chap4__example_4_3_4"]
theorem exResolutionRefutation_addr_independence :
    ∀ u v, exResolutionRefutation_rel u v → u ≠ v →
      ¬ List.isPrefixOf u v = true ∧ ¬ List.isPrefixOf v u = true 

/-- Example 4.3.4 (companion): Child preservation for the refutation DAG's
    relation. The only non-trivial equivalence class is `{[0,0],[1,0,0]}`,
    both leaves. -/
@[blueprint "chap4__example_4_3_4"]
theorem exResolutionRefutation_child_preservation :
    ∀ u v, exResolutionRefutation_rel u v → ∀ i,
      (u ++ [i]) ∈ (exResolutionRefutation_tree P Q).domain.dom ↔
      (v ++ [i]) ∈ (exResolutionRefutation_tree P Q).domain.dom 

/-- Example 4.3.4 (companion): Child equivalence for the refutation
    DAG's relation. -/
@[blueprint "chap4__example_4_3_4"]
theorem exResolutionRefutation_child_equivalence :
    ∀ u v, exResolutionRefutation_rel u v → ∀ i,
      (u ++ [i]) ∈ (exResolutionRefutation_tree P Q).domain.dom →
      exResolutionRefutation_rel (u ++ [i]) (v ++ [i]) 

/-- Example 4.3.4 (companion): Label agreement for the refutation DAG's
    relation. -/
@[blueprint "chap4__example_4_3_4"]
theorem exResolutionRefutation_label_agreement (P Q : Nat) :
    ∀ u v, exResolutionRefutation_rel u v →
      labelAtOpt (exResolutionRefutation_tree P Q) u =
        labelAtOpt (exResolutionRefutation_tree P Q) v 

/-- Example 4.3.4 (companion): The underlying DAG of the refutation. -/
@[blueprint "chap4__example_4_3_4"]
def exResolutionRefutation_dag (P Q : Nat) : DAG Clause where
  tree := (exResolutionRefutation_tree P Q)
  rel := exResolutionRefutation_rel
  rel_equiv := exResolutionRefutation_rel_equiv
  addr_independence := exResolutionRefutation_addr_independence
  child_preservation := exResolutionRefutation_child_preservation
  child_equivalence := exResolutionRefutation_child_equivalence
  label_agreement := (exResolutionRefutation_label_agreement P Q)

/-- Example 4.3.4 (companion): Binary branching for the refutation DAG. -/
@[blueprint "chap4__example_4_3_4"]
theorem exResolutionRefutation_binary_branching (P Q : Nat) :
    ∀ (u : TreeAddr) (_hu : u ∈ (exResolutionRefutation_dag P Q).tree.domain.dom),
      (u ++ [0]) ∈ (exResolutionRefutation_dag P Q).tree.domain.dom →
      (u ++ [1]) ∈ (exResolutionRefutation_dag P Q).tree.domain.dom 

/-- Example 4.3.4 (companion): Resolvent-at-internal constraint for the
    refutation DAG. -/
@[blueprint "chap4__example_4_3_4"]
theorem exResolutionRefutation_resolvent_at_internal (P Q : Nat) (hPQ : P ≠ Q) :
    ∀ (u : TreeAddr) (hu : u ∈ (exResolutionRefutation_dag P Q).tree.domain.dom)
      (h0 : (u ++ [0]) ∈ (exResolutionRefutation_dag P Q).tree.domain.dom),
      let h1 := (exResolutionRefutation_binary_branching P Q) u hu h0
      ∃ L : Literal,
        L ∈ (exResolutionRefutation_dag P Q).tree.label (u ++ [0]) h0 ∧
        Literal.conjugate L ∈ (exResolutionRefutation_dag P Q).tree.label (u ++ [1]) h1 ∧
        (exResolutionRefutation_dag P Q).tree.label u hu =
          GCNF.Clause.union
            (GCNF.Clause.remove
              ((exResolutionRefutation_dag P Q).tree.label (u ++ [0]) h0) L)
            (GCNF.Clause.remove
              ((exResolutionRefutation_dag P Q).tree.label (u ++ [1]) h1)
              (Literal.conjugate L)) 

/-- Example 4.3.4: A concrete resolution refutation DAG (page 126) with
    shared leaf {P,Q}, refuting {P,Q}, {P,¬Q}, {¬P,Q}, {¬P,¬Q}. -/
@[blueprint "chap4__example_4_3_4" (main := true)]
noncomputable def exResolutionRefutation (P Q : Nat) (hPQ : P ≠ Q) : ResolutionDAG where
  dag := (exResolutionRefutation_dag P Q)
  binary_branching := exResolutionRefutation_binary_branching P Q
  children_binary := by
    intro u hu i hi
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hi with h | h | h | h | h | h | h | h | h <;> simp_all
  resolvent_at_internal := exResolutionRefutation_resolvent_at_internal P Q hPQ
  dom_finite := ⟨[[], [0], [0, 0], [0, 1], [1], [1, 0], [1, 0, 0], [1, 0, 1], [1, 1]],
    fun a => by
      constructor
      · intro ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      · intro ha; simp at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | exact Or.inl rfl
                | exact Or.inr (Or.inl rfl)
                | exact Or.inr (Or.inr (Or.inl rfl))
                | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
                | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
                | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
                | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
                | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))⟩
  decidable_dom := fun a =>
    if h : a = [] ∨ a = [0] ∨ a = [0, 0] ∨ a = [0, 1] ∨
            a = [1] ∨ a = [1, 0] ∨ a = [1, 0, 0] ∨ a = [1, 0, 1] ∨ a = [1, 1]
    then isTrue h
    else isFalse h

/-- The displayed four-clause input, with arbitrary atom identities. -/
@[blueprint "chap4__example_4_3_4"]
def exResolutionRefutationInput (P Q : Nat) : ClauseSequent :=
  GCNF.ClauseSequent.ofList [
    GCNF.Clause.ofList [.pos P, .pos Q],
    GCNF.Clause.ofList [.pos P, .neg Q],
    GCNF.Clause.ofList [.neg P, .pos Q],
    GCNF.Clause.ofList [.neg P, .neg Q]]

/-- Under the example's distinct-atom reading, the displayed DAG refutes
    exactly its displayed input. -/
@[blueprint "chap4__example_4_3_4"]
theorem exResolutionRefutation_correct (P Q : Nat) (hPQ : P ≠ Q) :
    (exResolutionRefutation P Q hPQ).isResolutionRefutation
      (exResolutionRefutationInput P Q) 

end LCS.Resolution.Method
end
