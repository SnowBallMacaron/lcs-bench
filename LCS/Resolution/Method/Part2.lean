import LCS.Item
import LCS.Util
import LCS.Resolution.GCNF
import Attach
import LCS.Resolution.Method.Part2.ProofsStamp
import LCS.Resolution.Method.Part1
attach_helper_namespace LCS.Resolution.Method.Proofs

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF

/-- Definition 4.3.3: a resolution DAG for S is a finite set of distinct
    constituent DAGs whose leaves belong to S. Constituents here use the finite
    derivation reading supported by the resolution method and soundness proof. -/
@[blueprint "chap4__definition_4_3_3" (main := true)]
structure ResolutionForest (S : ClauseSequent) where
  members : Set (Quotient ResolutionDAG.sourceSetoid)
  finite : Set.Finite members
  leavesFrom : ∀ D : ResolutionDAG, D.sourceClass ∈ members → D.leavesFrom S

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionForest

/-- A refutation consists of exactly one DAG, with empty root label. -/
@[blueprint "chap4__definition_4_3_3"]
def isRefutation {S : ClauseSequent} (F : ResolutionForest S) : Prop :=
  ∃ D : ResolutionDAG, F.members = (fun E => E = D.sourceClass) ∧ D.rootLabel = GCNF.Clause.empty

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
def singleton {S : ClauseSequent} (D : ResolutionDAG) (h : D.leavesFrom S) :
    ResolutionForest S where
  members := fun E => E = D.sourceClass
  finite := ⟨[D.sourceClass], fun E => by simp⟩
  leavesFrom := by
    intro E hE
    exact (ResolutionDAG.leavesFrom_sourceEquivalent (Quotient.exact hE) S).mpr h

@[blueprint "chap4__definition_4_3_3"]
theorem refutation_iff (S : ClauseSequent) :
    (∃ F : ResolutionForest S, F.isRefutation) ↔
      ∃ D : ResolutionDAG, D.isResolutionRefutation S 

/-- The empty clause already present in the input gives a zero-step refutation. -/
@[blueprint "chap4__definition_4_3_3"]
theorem emptyClauseRefutation (S : ClauseSequent) (h : GCNF.Clause.empty ∈ S) :
    (ResolutionDAG.mk_axiom GCNF.Clause.empty).isResolutionRefutation S 

@[blueprint "chap4__definition_4_3_3"]
theorem emptyClauseRefutation_zeroSteps :
    (ResolutionDAG.mk_axiom GCNF.Clause.empty).stepCount = 0 

end ResolutionForest
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF

/-- Theorem 4.3.1 (companion — tree type): Inductive resolution tree used
    as an algorithmic vehicle in the proof of Theorem 4.3.1. -/
@[blueprint "chap4__theorem_4_3_3"]
inductive ResolutionTree where
  | axiom_ : Clause → ResolutionTree
  | resolve : ResolutionTree → ResolutionTree → Literal → ResolutionTree

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ResolutionTree
open LCS.Resolution.GCNF

/-- Theorem 4.3.1 (companion — tree label): Root label of the resolution
    tree. -/
@[blueprint "chap4__theorem_4_3_3"]
def label : ResolutionTree → Clause
  | .axiom_ C => C
  | .resolve T1 T2 L =>
    GCNF.Clause.union
      (GCNF.Clause.remove T1.label L)
      (GCNF.Clause.remove T2.label (Literal.conjugate L))

/-- Theorem 4.3.1 (companion — tree leaf condition): All leaf labels
    of the resolution tree are members of S. -/
@[blueprint "chap4__theorem_4_3_3"]
def leavesFrom (T : ResolutionTree) (S : ClauseSequent) : Prop :=
  match T with
  | .axiom_ C => C ∈ S
  | .resolve T1 T2 _ => T1.leavesFrom S ∧ T2.leavesFrom S

/-- A structural certificate that every internal tree node performs a genuine
    resolution step: the pivot occurs in the left premise and its conjugate
    occurs in the right premise.  `ResolutionTree.label` already computes the
    corresponding resolvent, so these occurrence witnesses rule out malformed
    nodes whose labels merely erase absent literals. -/
@[blueprint "chap4__theorem_4_3_3"]
def IsWellFormed : ResolutionTree → Prop
  | .axiom_ _ => True
  | .resolve T1 T2 pivot =>
    T1.IsWellFormed ∧
    T2.IsWellFormed ∧
    pivot ∈ T1.label ∧
    Literal.conjugate pivot ∈ T2.label

/-- Number of resolve nodes (resolution steps). -/
@[blueprint "chap4__theorem_4_3_3"]
def treeStepCount : ResolutionTree → Nat
  | .axiom_ _ => 0
  | .resolve T1 T2 _ => 1 + T1.treeStepCount + T2.treeStepCount

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- A well-formed resolution tree yields a finite resolution DAG, together
    with its exact root label. -/
noncomputable def toResolutionDAGWithLabel : (T : ResolutionTree) →
    T.IsWellFormed → {D : ResolutionDAG // D.rootLabel = T.label}
  | .axiom_ C, _ => ⟨ResolutionDAG.mk_axiom C, rfl⟩
  | .resolve T1 T2 L, h =>
    let D1 := toResolutionDAGWithLabel T1 h.1
    let D2 := toResolutionDAGWithLabel T2 h.2.1
    ⟨ResolutionDAG.mk_resolve D1.val D2.val L
      (D1.property.symm ▸ h.2.2.1) (D2.property.symm ▸ h.2.2.2), by
      rw [ResolutionDAG.rootLabel_resolve, D1.property, D2.property]
      rfl⟩

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Tree-to-DAG conversion requires a genuine pivot at every internal node. -/
noncomputable def toResolutionDAG (T : ResolutionTree) (h : T.IsWellFormed) : ResolutionDAG :=
  (T.toResolutionDAGWithLabel h).val

end ResolutionTree
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace Clause

/-- Definition 4.3.3 (companion def): The empty clause, containing no literals.
    A set of clauses containing the empty clause is unsatisfiable. -/
@[blueprint "chap4__definition_4_3_3"]
def empty : Clause := GCNF.Clause.empty

end Clause
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace Clause

/-- Lemma 4.3.1 (companion def): A valuation satisfies a clause iff it
    satisfies at least one literal in the clause. -/
@[blueprint "chap4__lemma_4_3_1"]
def satisfies (v : Nat → Bool) (C : Clause) : Prop :=
  ∃ L ∈ C, Literal.satisfiedBy L v

end Clause
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ClauseSet

/-- Definition 4.3.2 (companion def): A valuation satisfies a set of clauses iff
    it satisfies every clause in the set. -/
@[blueprint "chap4__definition_4_3_2"]
def satisfies (v : Nat → Bool) (S : ClauseSequent) : Prop :=
  ∀ C ∈ S, Clause.satisfies v C

end ClauseSet
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
namespace ClauseSet

/-- Definition 4.3.2 (companion def): A set of clauses is unsatisfiable iff no
    valuation satisfies all clauses in the set. -/
@[blueprint "chap4__definition_4_3_2"]
def isUnsatisfiable (S : ClauseSequent) : Prop :=
  ¬ ∃ v : Nat → Bool, ClauseSet.satisfies v S

end ClauseSet
end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF

/-- Example 4.3.1 (companion def): Valid tree addresses for the example tree,
    a 9-address domain encoding an f-h-f-f-f-b-b-b-b tree. -/
@[blueprint "chap4__example_4_3_1"]
def exDAGTreeAddrs : Set TreeAddr :=
  fun a => a ∈ ([[], [0], [1], [1,0], [1,1], [1,0,0], [1,0,1], [1,1,0], [1,1,1]] : List TreeAddr)

/-- Example 4.3.1 (companion): The root address `[]` is in `exDAGTreeAddrs`. -/
@[blueprint "chap4__example_4_3_1"]
theorem exDAGTreeDomain_root_mem : [] ∈ exDAGTreeAddrs 

/-- Example 4.3.1 (companion): `exDAGTreeAddrs` is closed under prefixes. -/
@[blueprint "chap4__example_4_3_1"]
theorem exDAGTreeDomain_prefix_closed :
    ∀ u v, (u ++ v) ∈ exDAGTreeAddrs → u ∈ exDAGTreeAddrs 

/-- Example 4.3.1 (companion): `exDAGTreeAddrs` is closed under
    left-siblings. -/
@[blueprint "chap4__example_4_3_1"]
theorem exDAGTreeDomain_left_sibling_closed :
    ∀ u i, (u ++ [i + 1]) ∈ exDAGTreeAddrs → (u ++ [i]) ∈ exDAGTreeAddrs 

/-- Example 4.3.1 (companion def): Tree domain with closure properties. -/
@[blueprint "chap4__example_4_3_1"]
def exDAGTreeDomain : TreeDomain where
  dom := exDAGTreeAddrs
  root_mem := exDAGTreeDomain_root_mem
  prefix_closed := exDAGTreeDomain_prefix_closed
  left_sibling_closed := exDAGTreeDomain_left_sibling_closed

/-- Example 4.3.1 (companion def): Labeling function for the example tree. -/
@[blueprint "chap4__example_4_3_1"]
noncomputable def exDAGTreeLabel (a : TreeAddr) (_ : a ∈ exDAGTreeDomain.dom) : Char :=
  match a with
  | []        => 'f'
  | [0]       => 'h'
  | [1]       => 'f'
  | [1, 0]    => 'f'
  | [1, 1]    => 'f'
  | [1, 0, 0] => 'b'
  | [1, 0, 1] => 'b'
  | [1, 1, 0] => 'b'
  | [1, 1, 1] => 'b'
  | _         => 'x'  -- unreachable for valid addresses

/-- Example 4.3.1: A concrete labeled tree over Char illustrating shared
    subtrees: root 'f', left leaf 'h', right subtree f(f(b,b), f(b,b)). -/
@[blueprint "chap4__example_4_3_1" (main := true)]
noncomputable def exDAGTree : LabeledTree Char where
  domain := exDAGTreeDomain
  label := exDAGTreeLabel

/-- Example 4.3.2 (companion def): List of valid tree addresses. -/
@[blueprint "chap4__example_4_3_2"]
def exDAGAddrs : List TreeAddr :=
  [[], [0], [1], [1,0], [1,1], [1,0,0], [1,0,1], [1,1,0], [1,1,1]]

/-- Example 4.3.2 (companion theorem): Membership in the tree domain unfolds to
    list membership. -/
@[blueprint "chap4__example_4_3_2"]
theorem exDAG_mem_dom_iff (a : TreeAddr) :
    a ∈ exDAGTree.domain.dom ↔ a ∈ exDAGAddrs 

/-- Example 4.3.2 (companion theorem): [1,0] is in the tree domain. -/
@[blueprint "chap4__example_4_3_2"]
theorem exDAG_mem_10 : [1,0] ∈ exDAGTree.domain.dom 

/-- Example 4.3.2 (companion theorem): [1,1] is in the tree domain. -/
@[blueprint "chap4__example_4_3_2"]
theorem exDAG_mem_11 : [1,1] ∈ exDAGTree.domain.dom 
-- ========= Example 4.3.2: Collapsed DAG =========

/-- Example 4.3.2 (companion): Equivalence relation identifying the two
    shared subtrees of `exDAGTree`. -/
@[blueprint "chap4__example_4_3_2"]
def exCollapsedDAG_rel : TreeAddr → TreeAddr → Prop :=
  fun u v => u = v ∨
    ((u = [1,0] ∧ v = [1,1]) ∨ (u = [1,1] ∧ v = [1,0])) ∨
    (u ∈ [[1,0,0], [1,0,1], [1,1,0], [1,1,1]] ∧
     v ∈ [[1,0,0], [1,0,1], [1,1,0], [1,1,1]])

/-- Example 4.3.2 (companion): `exCollapsedDAG_rel` is an equivalence
    relation. -/
@[blueprint "chap4__example_4_3_2"]
theorem exCollapsedDAG_rel_equiv : Equivalence exCollapsedDAG_rel 

/-- Example 4.3.2 (companion): Address independence for
    `exCollapsedDAG_rel`. -/
@[blueprint "chap4__example_4_3_2"]
theorem exCollapsedDAG_addr_independence :
    ∀ u v, exCollapsedDAG_rel u v → u ≠ v →
      ¬ List.isPrefixOf u v = true ∧ ¬ List.isPrefixOf v u = true 

/-- Example 4.3.2 (companion): Child preservation for
    `exCollapsedDAG_rel`. -/
@[blueprint "chap4__example_4_3_2"]
theorem exCollapsedDAG_child_preservation :
    ∀ u v, exCollapsedDAG_rel u v → ∀ i,
      (u ++ [i]) ∈ exDAGTree.domain.dom ↔
      (v ++ [i]) ∈ exDAGTree.domain.dom 

/-- Example 4.3.2 (companion): Child equivalence for
    `exCollapsedDAG_rel`. -/
@[blueprint "chap4__example_4_3_2"]
theorem exCollapsedDAG_child_equivalence :
    ∀ u v, exCollapsedDAG_rel u v → ∀ i,
      (u ++ [i]) ∈ exDAGTree.domain.dom →
      exCollapsedDAG_rel (u ++ [i]) (v ++ [i]) 

/-- Example 4.3.2 (companion): Label agreement for `exCollapsedDAG_rel`. -/
@[blueprint "chap4__example_4_3_2"]
theorem exCollapsedDAG_label_agreement :
    ∀ u v, exCollapsedDAG_rel u v →
      labelAtOpt exDAGTree u = labelAtOpt exDAGTree v 

/-- Example 4.3.2: DAG obtained by collapsing shared subtrees in exDAGTree,
    identifying the two f(b,b) subtrees and all four b leaves. -/
@[blueprint "chap4__example_4_3_2" (main := true)]
noncomputable def exCollapsedDAG : DAG Char where
  tree := exDAGTree
  rel := exCollapsedDAG_rel
  rel_equiv := exCollapsedDAG_rel_equiv
  addr_independence := exCollapsedDAG_addr_independence
  child_preservation := exCollapsedDAG_child_preservation
  child_equivalence := exCollapsedDAG_child_equivalence
  label_agreement := exCollapsedDAG_label_agreement

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF

/-- Example 4.3.3: Under the contextually distinct-atom reading, the two
    displayed clauses have exactly the two displayed resolvents. A and B
    range over arbitrary atom identities, not a fixed chosen pair. -/
@[blueprint "chap4__example_4_3_3" (main := true)]
theorem exampleTwoResolvents (A B : Nat) (hAB : A ≠ B) (C : Clause) :
    Clause.isResolvent C
      (GCNF.Clause.ofList [.pos A, .pos B])
      (GCNF.Clause.ofList [.neg A, .neg B]) ↔
    C = GCNF.Clause.ofList [.pos A, .neg A] ∨
      C = GCNF.Clause.ofList [.pos B, .neg B] 

/-- The two resolvents in the distinct-atom example are themselves distinct. -/
@[blueprint "chap4__example_4_3_3"]
theorem exampleTwoResolventsDistinct (A B : Nat) (hAB : A ≠ B) :
    GCNF.Clause.ofList [.pos A, .neg A] ≠
      GCNF.Clause.ofList [.pos B, .neg B] 

/-- Coincident atom substitutions collapse the parents to complementary units,
    so the only resolvent is empty. This records why distinctness is a source
    interpretation choice rather than a consequence of clause syntax. -/
@[blueprint "chap4__example_4_3_3"]
theorem exampleCoincidentResolvent (A : Nat) (C : Clause) :
    Clause.isResolvent C
      (GCNF.Clause.ofList [.pos A, .pos A])
      (GCNF.Clause.ofList [.neg A, .neg A]) ↔ C = GCNF.Clause.empty 


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

/-- The two occurrences of {P,Q} are the same graph vertex. -/
@[blueprint "chap4__example_4_3_4"]
theorem exResolutionRefutation_sharedLeaf (P Q : Nat) :
    (exResolutionRefutation_dag P Q).eqClass [0, 0] =
      (exResolutionRefutation_dag P Q).eqClass [1, 0, 0] 

/-- Eight distinct quotient vertices; the repeated leaf is represented once. -/
@[blueprint "chap4__example_4_3_4"]
def exResolutionRefutationNodeClasses (P Q : Nat) : List (Set TreeAddr) :=
  [[], [0], [1], [1, 0], [0, 0], [0, 1], [1, 0, 1], [1, 1]].map
    (exResolutionRefutation_dag P Q).eqClass

@[blueprint "chap4__example_4_3_4"]
theorem exResolutionRefutation_eightVertices (P Q : Nat) :
    (exResolutionRefutationNodeClasses P Q).length = 8 ∧
    (exResolutionRefutationNodeClasses P Q).Nodup ∧
    ∀ V, V ∈ (exResolutionRefutation_dag P Q).nodes ↔
      V ∈ exResolutionRefutationNodeClasses P Q 

/-- Under coincident atom substitution, the printed graph's g-step fails:
    its premises resolve to empty, whereas its printed conclusion is {¬P}. -/
@[blueprint "chap4__example_4_3_4"]
theorem exResolutionRefutation_coincidentFailure (P : Nat) :
    ¬ Clause.isResolvent (GCNF.Clause.ofList [.neg P])
      (GCNF.Clause.ofList [.pos P]) (GCNF.Clause.ofList [.neg P, .neg P]) 

-- ========= Lemma 4.3.1: Resolution Tautology =========



/-- Lemma 4.3.1: (A∨P) ∧ (B∨¬P) ≡ (A∨P) ∧ (B∨¬P) ∧ (A∨B) (adding the
    resolvent preserves satisfaction). -/
@[blueprint "chap4__lemma_4_3_1"]
theorem resolution_tautology (A B : Clause) (P : Literal) :
    (∀ v : Nat → Bool,
      (Clause.satisfies v (GCNF.Clause.union A (GCNF.Clause.single P)) ∧
       Clause.satisfies v (GCNF.Clause.union B (GCNF.Clause.single (Literal.conjugate P)))) ↔
      (Clause.satisfies v (GCNF.Clause.union A (GCNF.Clause.single P)) ∧
       Clause.satisfies v (GCNF.Clause.union B (GCNF.Clause.single (Literal.conjugate P))) ∧
       Clause.satisfies v (GCNF.Clause.union A B))) 

end LCS.Resolution.Method
end

section
namespace LCS.Resolution.Method
open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Propositional.Syntax LCS.Propositional.Semantics

/-- Proof of Lemma 4.3.1: The displayed equivalence is a tautology for
    arbitrary formulas A and B and propositional symbol P. False represents
    an empty residual disjunction, so these instances are included. -/
@[blueprint "chap4__lemma_4_3_1" (main := true)]
theorem resolutionFormulaTautology (A B : PropFormula) (P : Nat) :
    ∀ v : Valuation,
      evalExt v (.equiv_
        (.conj (.disj A (.var P)) (.disj B (.neg (.var P))))
        (.conj (.conj (.disj A (.var P)) (.disj B (.neg (.var P))))
          (.disj A B))) = .T 

/-- Empty residual disjunctions have exactly the reductions used in
    Lemma 4.3.1, including the both-empty contradiction. -/
@[blueprint "chap4__lemma_4_3_1"]
theorem emptyDisjunctionReductions (A : PropFormula) (P : Nat) (v : Valuation) :
    evalExt v (.disj .fls A) = evalExt v A ∧
    evalExt v (.disj A .fls) = evalExt v A ∧
    evalExt v (.conj
      (.conj (.disj .fls (.var P)) (.disj .fls (.neg (.var P))))
      (.disj .fls .fls)) = evalExt v (.conj (.var P) (.neg (.var P))) 



/-- The introductory residual union is the exact resolvent when the displayed
    residuals are what remains after deleting the pivot and its conjugate. -/
@[blueprint "chap4__definition_4_3_2"]
theorem residualUnionIsResolvent (A B : Clause) (L : Literal)
    (hA : L ∉ A) (hB : Literal.conjugate L ∉ B) :
    Clause.isResolvent (GCNF.Clause.union A B)
      (GCNF.Clause.union A (GCNF.Clause.single L))
      (GCNF.Clause.union B (GCNF.Clause.single (Literal.conjugate L))) 

/-- Complementary unit clauses resolve to the empty clause. -/
@[blueprint "chap4__example_4_3_3"]
theorem complementaryUnitsResolve (L : Literal) :
    Clause.isResolvent GCNF.Clause.empty (GCNF.Clause.single L)
      (GCNF.Clause.single (Literal.conjugate L)) 

/-- Adding any resolvent of clauses already in S preserves every model. -/
@[blueprint "chap4__definition_4_3_2"]
theorem resolventInsertionPreservesModels (S : ClauseSequent) (C C₁ C₂ : Clause)
    (h₁ : C₁ ∈ S) (h₂ : C₂ ∈ S) (hC : Clause.isResolvent C C₁ C₂)
    (v : Nat → Bool) :
    ClauseSet.satisfies v (LCS.Finset.insert C S) ↔ ClauseSet.satisfies v S 

/-- Resolution augmentation preserves unsatisfiability in both directions. -/
@[blueprint "chap4__definition_4_3_2"]
theorem resolventInsertionPreservesUnsatisfiability (S : ClauseSequent)
    (C C₁ C₂ : Clause) (h₁ : C₁ ∈ S) (h₂ : C₂ ∈ S)
    (hC : Clause.isResolvent C C₁ C₂) :
    ClauseSet.isUnsatisfiable (LCS.Finset.insert C S) ↔
      ClauseSet.isUnsatisfiable S 

/-- The motivating clause-set equivalence holds for arbitrary residual blocks,
    even if a residual itself repeats a pivot literal. -/
@[blueprint "chap4__lemma_4_3_1"]
theorem residualInsertionPreservesModels (S : ClauseSequent) (A B : Clause)
    (L : Literal) (v : Nat → Bool) :
    let initial := LCS.Finset.insert (GCNF.Clause.union A (GCNF.Clause.single L))
      (LCS.Finset.insert (GCNF.Clause.union B
        (GCNF.Clause.single (Literal.conjugate L))) S)
    ClauseSet.satisfies v (LCS.Finset.insert (GCNF.Clause.union A B) initial) ↔
      ClauseSet.satisfies v initial 

/-- A resolution step selects two existing parent clauses and adds exactly
    one resolvent, retaining every original clause. -/
@[blueprint "chap4__definition_4_3_3"]
def resolutionStep (S T : ClauseSequent) : Prop :=
  ∃ C₁ ∈ S, ∃ C₂ ∈ S, ∃ C,
    Clause.isResolvent C C₁ C₂ ∧ T = LCS.Finset.insert C S

/-- Every single resolution step preserves the same satisfying valuations. -/
@[blueprint "chap4__definition_4_3_3"]
theorem resolutionStepPreservesModels {S T : ClauseSequent}
    (h : resolutionStep S T) (v : Nat → Bool) :
    ClauseSet.satisfies v T ↔ ClauseSet.satisfies v S 

/-- A finite sequence of successive resolution steps beginning with S.
    Zero steps are permitted, as needed when S already contains the empty clause. -/
@[blueprint "chap4__definition_4_3_3"]
structure ResolutionProcess (S : ClauseSequent) where
  length : Nat
  stage : Fin (length + 1) → ClauseSequent
  initial : stage ⟨0, Nat.zero_lt_succ length⟩ = S
  successive : ∀ i : Fin length,
    resolutionStep (stage ⟨i.val, by omega⟩) (stage ⟨i.val + 1, by omega⟩)

/-- The resolution method succeeds when the last set contains the empty clause. -/
@[blueprint "chap4__definition_4_3_3"]
def ResolutionProcess.successful {S : ClauseSequent} (R : ResolutionProcess S) : Prop :=
  GCNF.Clause.empty ∈ R.stage ⟨R.length, Nat.lt_succ_self R.length⟩

/-- Every stage of the finite process has precisely the original models. -/
@[blueprint "chap4__lemma_4_3_2"]
theorem ResolutionProcess.preservesModels {S : ClauseSequent}
    (R : ResolutionProcess S) (v : Nat → Bool) (i : Fin (R.length + 1)) :
    ClauseSet.satisfies v (R.stage i) ↔ ClauseSet.satisfies v S 

/-- A clause set containing the empty clause has no satisfying valuation. -/
@[blueprint "chap4__definition_4_3_3"]
theorem containsEmptyIsUnsatisfiable (S : ClauseSequent)
    (h : GCNF.Clause.empty ∈ S) : ClauseSet.isUnsatisfiable S 

/-- A successful finite sequence certifies unsatisfiability of its input. -/
@[blueprint "chap4__lemma_4_3_2"]
theorem ResolutionProcess.successfulSound {S : ClauseSequent}
    (R : ResolutionProcess S) (h : R.successful) : ClauseSet.isUnsatisfiable S 

/-- The motivating augmentation also preserves unsatisfiability for arbitrary
    residual blocks, with no pivot-absence restriction needed semantically. -/
@[blueprint "chap4__lemma_4_3_1"]
theorem residualInsertionPreservesUnsatisfiability (S : ClauseSequent) (A B : Clause)
    (L : Literal) :
    let initial := LCS.Finset.insert (GCNF.Clause.union A (GCNF.Clause.single L))
      (LCS.Finset.insert (GCNF.Clause.union B
        (GCNF.Clause.single (Literal.conjugate L))) S)
    ClauseSet.isUnsatisfiable (LCS.Finset.insert (GCNF.Clause.union A B) initial) ↔
      ClauseSet.isUnsatisfiable initial 

/-- The source's deletion example, parameterized by its two atom metavariables. -/
@[blueprint "chap4__definition_4_3_2"]
def parentDeletionInput (P Q : Nat) : ClauseSequent :=
  ClauseSequent.ofList [GCNF.Clause.ofList [.pos P, .pos Q],
    GCNF.Clause.single (.neg Q)]

/-- In the contextually distinct-atom reading, the displayed positive unit is
    the exact resolvent of the two parents. With P=Q this assertion is false. -/
@[blueprint "chap4__definition_4_3_2"]
theorem parentDeletionResolvent (P Q : Nat) (hPQ : P ≠ Q) :
    Clause.isResolvent (GCNF.Clause.single (.pos P))
      (GCNF.Clause.ofList [.pos P, .pos Q]) (GCNF.Clause.single (.neg Q)) 

/-- Adding the displayed resolvent and removing both parents leaves exactly
    the positive unit clause. The distinctness qualification is explicit. -/
@[blueprint "chap4__definition_4_3_2"]
theorem parentDeletionResult (P Q : Nat) (hPQ : P ≠ Q) :
    LCS.Finset.erase
      (LCS.Finset.erase
        (LCS.Finset.insert (GCNF.Clause.single (.pos P)) (parentDeletionInput P Q))
        (GCNF.Clause.ofList [.pos P, .pos Q]))
      (GCNF.Clause.single (.neg Q)) =
      ClauseSequent.single (GCNF.Clause.single (.pos P)) 

/-- Every valuation satisfying both P and Q satisfies the reduced
    singleton clause set and falsifies the original set. The model discrepancy
    holds even for coincident atoms; distinctness is needed only for the displayed
    resolvent/deletion construction. -/
@[blueprint "chap4__definition_4_3_2"]
theorem parentDeletionCountervaluation (P Q : Nat) (v : Nat → Bool)
    (hP : v P = true) (hQ : v Q = true) :
    ClauseSet.satisfies v
      (ClauseSequent.single (GCNF.Clause.single (.pos P))) ∧
    ¬ ClauseSet.satisfies v (parentDeletionInput P Q) 

/-- Thus deletion of the parents is not model-equivalent to the original set. -/
@[blueprint "chap4__definition_4_3_2"]
theorem parentDeletionNotEquivalent (P Q : Nat) :
    ¬ (∀ v : Nat → Bool,
      ClauseSet.satisfies v (parentDeletionInput P Q) ↔
      ClauseSet.satisfies v (ClauseSequent.single (GCNF.Clause.single (.pos P)))) 


-- ========= Lemma 4.3.2: Soundness of Resolution =========

/-- Lemma 4.3.2: If a set S of clauses has a resolution refutation, then S
    is unsatisfiable. -/
@[blueprint "chap4__lemma_4_3_2" (main := true)]
theorem resolution_soundness (S : ClauseSequent) (D : ResolutionDAG)
    (hRef : ResolutionDAG.isResolutionRefutation D S) :
    ClauseSet.isUnsatisfiable S 

end LCS.Resolution.Method
end

