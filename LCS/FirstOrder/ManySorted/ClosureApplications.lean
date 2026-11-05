import LCS.FirstOrder.ManySorted.CongruenceClosure
import LCS.FirstOrder.ManySorted.ClosureApplications.ProofsStamp

/-! # Forward unification closure and graph size

The unnumbered definitions and assertions following Lemma 10.6.5 in §10.6.6.
Variable labels are distinguished nullary symbols. Relations are sorted, and
successor propagation uses the common label's argument sorts.
-/

namespace LCS.FirstOrder.ManySorted.ClosureApplications

open CongruenceClosure

/-- The distinguished variable labels of a ranked alphabet. Every variable
label has empty arity; other nullary labels may be constants. -/
@[blueprint "chap10__lemma_10_6_5"]
structure MSVariableLabels (A : MSRankedAlphabet) where
  isVariable : A.symbols → Prop
  variable_nullary : ∀ f, isVariable f → (A.rank f).1 = []

/-- A sorted equivalence on the vertices: related nodes have the same sort,
and the restriction to every sort fiber is an equivalence relation. -/
@[blueprint "chap10__lemma_10_6_5"]
def msSortedEquivalence (G : MSLabeledGraph)
    (R : G.Node → G.Node → Prop) : Prop :=
  MSSortSupported G R ∧
  ∀ s, Equivalence
    (fun u v : {u : G.Node // G.nodeSort u = s} => R u.val v.val)

/-- Clause (1) of unification closure: equal labels, or a variable label
on the left, or a variable label on the right. -/
@[blueprint "chap10__lemma_10_6_5"]
def msUnificationLabelCompatible (G : MSLabeledGraph)
    (X : MSVariableLabels G.Sigma) (u v : G.Node) : Prop :=
  G.Lambda u = G.Lambda v ∨
    X.isVariable (G.Lambda u) ∨ X.isVariable (G.Lambda v)

/-- The equal-label successor clause for a fixed pair of nodes. Every
matching successor pair belongs to the relation at the common label's
corresponding argument sort. Label equality transports the successor index
to the second node; the related-parent premise is shared with clause (1)
in `msIsUnificationClosure`. -/
@[blueprint "chap10__lemma_10_6_5"]
def msUnificationSuccessors (G : MSLabeledGraph)
    (R : G.Node → G.Node → Prop) (u v : G.Node) : Prop :=
  ∀ h : G.Lambda u = G.Lambda v,
    ∀ i : Fin (G.Sigma.rank (G.Lambda u)).1.length,
      restrictToSort G R ((G.Sigma.rank (G.Lambda u)).1.get i)
        (G.delta u i) (G.delta v (h ▸ i))

/-- A unification closure on a finite sorted graph is a sorted equivalence
whose related nodes satisfy label compatibility and forward closure. Cycles
are permitted, including identifications of a variable with a node that
has that variable as a successor. -/
@[blueprint "chap10__lemma_10_6_5"]
def msIsUnificationClosure (G : MSLabeledGraph)
    (X : MSVariableLabels G.Sigma) (R : G.Node → G.Node → Prop) : Prop :=
  msSortedEquivalence G R ∧
  ∀ u v, R u v →
    msUnificationLabelCompatible G X u v ∧ msUnificationSuccessors G R u v

/-- The least unification closure containing a relation `R`: `U` is a
unification closure containing `R`, and is included in every such closure.
Existence is a separate question; any containing sorted closure forces
the seed relation itself to be sort-supported. -/
@[blueprint "chap10__lemma_10_6_5"]
def msIsLeastUnificationClosure (G : MSLabeledGraph)
    (X : MSVariableLabels G.Sigma) (R U : G.Node → G.Node → Prop) : Prop :=
  msIsUnificationClosure G X U ∧
  (∀ u v, R u v → U u v) ∧
  ∀ U', msIsUnificationClosure G X U' →
    (∀ u v, R u v → U' u v) → ∀ u v, U u v → U' u v

/-- A required pair with distinct nonvariable labels obstructs every
containing unification closure, even when the seed is sort-supported. -/
@[attach_debt, blueprint "chap10__lemma_10_6_5"]
theorem msUnificationClosure_labelClash (G : MSLabeledGraph)
    (X : MSVariableLabels G.Sigma) (R : G.Node → G.Node → Prop)
    (hR : MSSortSupported G R) (u v : G.Node) (huv : R u v)
    (hne : G.Lambda u ≠ G.Lambda v)
    (hu : ¬ X.isVariable (G.Lambda u))
    (hv : ¬ X.isVariable (G.Lambda v)) :
    ¬ ∃ U, msIsUnificationClosure G X U ∧ (∀ a b, R a b → U a b)

/-- A one-sort signature with two distinct nullary symbols. -/
@[blueprint "chap10__lemma_10_6_5"]
def msLabelClashAlphabet : MSRankedAlphabet where
  SortType := Unit
  symbols := Bool
  rank := fun _ => ([], ())

/-- Two leaves labeled by the two different symbols of the signature. -/
@[blueprint "chap10__lemma_10_6_5"]
def msLabelClashGraph : MSLabeledGraph where
  Sigma := msLabelClashAlphabet
  Node := Bool
  nodeSort := fun _ => ()
  nodeFinite := ⟨[false, true], by intro b; cases b <;> simp⟩
  Lambda := id
  delta := fun _ i => Fin.elim0 i
  lambda_rank_sort := fun _ => rfl
  delta_succ_sort := fun _ i => Fin.elim0 i

/-- Both nullary labels in the two-leaf example are constants. -/
@[blueprint "chap10__lemma_10_6_5"]
def msLabelClashVariables : MSVariableLabels msLabelClashGraph.Sigma where
  isVariable := fun _ => False
  variable_nullary := fun _ h => False.elim h

/-- The required pair in the two-leaf example. Both vertices have the
single sort of the example signature. -/
@[blueprint "chap10__lemma_10_6_5"]
def msLabelClashSeed (u v : msLabelClashGraph.Node) : Prop :=
  u = false ∧ v = true

/-- The concrete two-leaf seed has no containing unification closure and,
consequently, no least containing unification closure. -/
@[attach_debt, blueprint "chap10__lemma_10_6_5"]
theorem msLabelClashGraph_noUnificationClosure :
    (¬ ∃ U, msIsUnificationClosure msLabelClashGraph msLabelClashVariables U ∧
      (∀ u v, msLabelClashSeed u v → U u v)) ∧
    ¬ ∃ U, msIsLeastUnificationClosure
      msLabelClashGraph msLabelClashVariables msLabelClashSeed U

/-- Possible nonexistence ranges over graphs and their signatures:
there are same-sort leaves with distinct nonvariable labels whose required
pair belongs to no unification closure. The two-leaf graph above supplies
the concrete example. -/
@[attach_debt, blueprint "chap10__lemma_10_6_5"]
theorem msUnificationClosure_mayNotExist :
    ∃ (G : MSLabeledGraph) (X : MSVariableLabels G.Sigma)
      (R : G.Node → G.Node → Prop) (u v : G.Node),
      MSSortSupported G R ∧ R u v ∧
      G.nodeSort u = G.nodeSort v ∧
      G.isTerminal u ∧ G.isTerminal v ∧
      G.Lambda u ≠ G.Lambda v ∧
      ¬ X.isVariable (G.Lambda u) ∧ ¬ X.isVariable (G.Lambda v) ∧
      (¬ ∃ U, msIsUnificationClosure G X U ∧ (∀ a b, R a b → U a b)) ∧
      ¬ ∃ U, msIsLeastUnificationClosure G X R U

/-- The finite vertex set of a graph, obtained extensionally from its
total-finiteness witness. Duplicate entries in that witness are removed. -/
@[blueprint "chap10__lemma_10_6_5"]
noncomputable def msGraphNodes (G : MSLabeledGraph) : Finset G.Node := by
  classical
  exact Finset.ofList (Classical.choose G.nodeFinite)

/-- The finite set of indexed edges `(v, i)` in the domain of `δ`.
Distinct indices are distinct edges even when their endpoints coincide. -/
@[blueprint "chap10__lemma_10_6_5"]
noncomputable def msGraphEdges (G : MSLabeledGraph) : Finset G.Edge := by
  classical
  exact Finset.ofList ((Classical.choose G.nodeFinite).flatMap fun v =>
    (List.finRange (G.Sigma.rank (G.Lambda v)).1.length).map fun i =>
      (⟨v, i⟩ : G.Edge))

/-- The number `n` of vertices. -/
@[blueprint "chap10__lemma_10_6_5"]
noncomputable def msGraphNodeCount (G : MSLabeledGraph) : Nat :=
  (msGraphNodes G).card

/-- The number `m` of indexed edges `(v, i)`. Counting the domain of `δ`
is the adopted reading for the independent size assertion in §10.6.6. -/
@[blueprint "chap10__lemma_10_6_5"]
noncomputable def msGraphEdgeCount (G : MSLabeledGraph) : Nat :=
  (msGraphEdges G).card

/-- Every vertex has incoming or outgoing incidence with an indexed edge.
A loop supplies both kinds of incidence. -/
@[blueprint "chap10__lemma_10_6_5"]
def msGraphNoIsolatedNodes (G : MSLabeledGraph) : Prop :=
  ∀ v, (∃ e : G.Edge, G.delta e.1 e.2 = v) ∨
    (∃ e : G.Edge, e.1 = v)

/-- With `m` read as the number of indexed edges `(v, i)`, every finite
graph without isolated vertices has `n ≤ 2m`. This is the uniform,
independent size assertion underlying the source's `n = O(m)` remark. -/
@[attach_debt, blueprint "chap10__lemma_10_6_5"]
theorem msGraphNodeCount_le_twice_edgeCount (G : MSLabeledGraph)
    (hG : msGraphNoIsolatedNodes G) :
    msGraphNodeCount G ≤ 2 * msGraphEdgeCount G

end LCS.FirstOrder.ManySorted.ClosureApplications
