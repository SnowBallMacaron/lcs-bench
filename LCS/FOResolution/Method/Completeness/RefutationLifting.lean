import LCS.Item
import LCS.Util
import LCS.FOResolution.Method
import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.Method.HerbrandBridge
import LCS.Herbrand.SHGTheorem.Main
import LCS.FOResolution.GroundResolution
import LCS.CutElim.LK
import LCS.Resolution.Method.DAGs
import Attach
import LCS.FOResolution.Method.Completeness.RefutationLifting.ProofsStamp

section
namespace LCS.FOResolution.Method.Completeness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.GroundResolution
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.HerbrandBridge
open LCS.CutElim.LK
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open Classical

/-- Lemma 8.5.4 (companion): the clause labeling an actual quotient node
    of a DAG. A representative must belong to the underlying tree domain. -/
@[blueprint "chap8__lemma_8_5_4"]
def FOResolutionDAGLabel {L : Language} (hNoEq : L.withoutEquality)
    (H : LCS.Resolution.Method.DAG (FOClause L hNoEq))
    (u : Set (List Nat)) (C : FOClause L hNoEq) : Prop :=
  ∃ a, a ∈ H.tree.domain.dom ∧ u = H.eqClass a ∧
    LCS.Resolution.Method.labelAtOpt H.tree a = some C

/-- Lemma 8.5.4 (companion): a rooted, onto homomorphism between the
    actual finite quotient-node sets of two clause-labeled DAGs. The immediate
    descendants are preserved exactly, in their underlying tree order;
    edges and leaves are preserved. At each source node a possibly different finite
    ground substitution gives the target label, as a set of literals.
    Equal labels do not identify distinct vertices. -/
@[blueprint "chap8__lemma_8_5_4"]
structure FOResolutionTreeHom (L : Language) (hNoEq : L.withoutEquality)
    (H H_g : LCS.Resolution.Method.DAG (FOClause L hNoEq)) where
  /-- Both graphs have finitely many actual vertices. -/
  source_finite : Set.Finite H.nodes
  target_finite : Set.Finite H_g.nodes
  /-- Domain and codomain are the vertices of the supplied graphs. -/
  mapNode : {u // H.nodes u} → {v // H_g.nodes v}
  /-- Immediate descendant edges remain edges, including shared targets. -/
  edge_pres : ∀ u v, H.edges (u.val, v.val) →
    H_g.edges ((mapNode u).val, (mapNode v).val)
  /-- At each actual source occurrence, a representative of its image has
      exactly the same child indices. Each child class maps to the target
      child class at that index. Thus the two ordered premises map to the
      two ordered premises; coincident classes still allow shared vertices. -/
  descendant_pres : ∀ (a : List Nat) (ha : a ∈ H.tree.domain.dom),
    ∃ (b : List Nat) (_hb : b ∈ H_g.tree.domain.dom),
      (mapNode ⟨H.eqClass a, ⟨a, ha, rfl⟩⟩).val = H_g.eqClass b ∧
      ∀ i : Nat,
        (a ++ [i] ∈ H.tree.domain.dom ↔ b ++ [i] ∈ H_g.tree.domain.dom) ∧
        ∀ hi : a ++ [i] ∈ H.tree.domain.dom,
          (mapNode ⟨H.eqClass (a ++ [i]), ⟨a ++ [i], hi, rfl⟩⟩).val =
            H_g.eqClass (b ++ [i])
  /-- The selected source root maps to the selected target root. -/
  root_pres : ∀ u, u.val = H.root → (mapNode u).val = H_g.root
  /-- Every target vertex lies in the image. -/
  onto : ∀ v, ∃ u, mapNode u = v
  /-- A source leaf maps to a target leaf, including zero-step DAGs. -/
  leaf_pres : ∀ u, (∀ v : {v // H.nodes v}, ¬ H.edges (u.val, v.val)) →
    ∀ v : {v // H_g.nodes v}, ¬ H_g.edges ((mapNode u).val, v.val)
  /-- Grounding is local to each node, with finite moved support and
      identity elsewhere; labels agree extensionally after substitution. -/
  label_pres : ∀ u, ∃ (theta : Nat → Term L) (support : List Nat),
    (∀ x, x ∉ support → theta x = Term.var x) ∧
    (∀ x, theta x ≠ Term.var x → termFV (theta x) = Set.empty) ∧
    (∀ C C_g,
      FOResolutionDAGLabel hNoEq H u.val C →
      FOResolutionDAGLabel hNoEq H_g (mapNode u).val C_g →
      FOClause.isGround hNoEq C_g ∧
      ∀ lit, lit ∈ C_g ↔ lit ∈ substLits hNoEq theta C)

-- ===================================================================
-- Lemma 8.5.4 (helper): groundifyTree
-- ===================================================================

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness
/-- Substituting the identity substitution into a literal is the identity. -/
theorem substLit_id {L : Language} (hNoEq : L.withoutEquality) (lit : FOLiteral L hNoEq) :
    (substLit (hNoEq := by all_goals exact hNoEq)) (fun n => Term.var n) lit = lit := by
-- BEGIN PROOF
  cases lit with
  | pos B =>
    simp only [substLit]
    congr 1; exact substAtom_id B
  | neg B =>
    simp only [substLit]
    congr 1; exact substAtom_id B
where
  termSubstAll_id {L : Language} (t : Term L) :
      termSubstAll t (fun n => Term.var n) = t := by
    induction t with
    | var x => rfl
    | const c => rfl
    | func f args ih =>
      simp only [termSubstAll]; congr 1; funext i; exact ih i
  substAtom_id : (atom : FOAtom L hNoEq) →
      (atom.subst (hNoEq := by all_goals exact hNoEq)) (fun n => Term.var n) = atom
    | .predN P args => by
        simp only [FOAtomCore.subst, FOAtomCore.mapTerms]
        congr 1
        funext i
        exact termSubstAll_id (args i)
    | .eq_ hL lhs rhs => by
        simp only [FOAtomCore.subst, FOAtomCore.mapTerms]
        congr 1 <;> exact termSubstAll_id _
  substFormula_id {L : Language} : (A : FormulaN L) →
      substLit.substFormula (fun n => Term.var n) A = A
    | .predN P args => by
        simp only [substLit.substFormula]; congr 1; funext i; exact termSubstAll_id (args i)
    | .eq_ _ t1 t2 => by
        simp only [substLit.substFormula]; congr 1 <;> exact termSubstAll_id _
    | .neg A => congrArg _ (substFormula_id A)
    | .conj A B => by
        simp only [substLit.substFormula]; congr 1 <;> exact substFormula_id _
    | .disj A B => by
        simp only [substLit.substFormula]; congr 1 <;> exact substFormula_id _
    | .impl A B => by
        simp only [substLit.substFormula]; congr 1 <;> exact substFormula_id _
    | .all i A => congrArg _ (substFormula_id A)
    | .ex i A => congrArg _ (substFormula_id A)

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness
/-- Substituting the identity substitution into a literal list is the identity. -/
theorem substLits_id {L : Language} (hNoEq : L.withoutEquality) (lits : List (FOLiteral L hNoEq)) :
    (substLits (hNoEq := by all_goals exact hNoEq)) (fun n => Term.var n) lits = lits := by
-- BEGIN PROOF
  simp only [substLits]
  induction lits with
  | nil => rfl
  | cons hd tl ih => simp [(substLit_id (hNoEq := by all_goals exact hNoEq)), ih]

-- ===================================================================
-- Lemma 8.5.4 (helper): allLabelsGround
-- ===================================================================

/-- Lemma 8.5.4 (companion): Predicate that all labels in a resolution
    tree are ground. For leaves, the label is the stored clause.
    For resolve nodes, the label is the resolvent plus the recursive
    property on both subtrees. -/
@[blueprint "chap8__lemma_8_5_4"]
def FOResolutionTree.allLabelsGround {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)] : FOResolutionTree L hNoEq → Prop
  | .axiom_ C => (FOClause.isGround (by all_goals exact hNoEq)) C
  | .resolve T1 T2 rA rB rho rho' sigma =>
    allLabelsGround hNoEq T1 ∧ allLabelsGround hNoEq T2 ∧
    (FOClause.isGround (by all_goals exact hNoEq))
      ((FOResolutionTree.label (hNoEq := by all_goals exact hNoEq))
        (.resolve T1 T2 rA rB rho rho' sigma))

/-- allLabelsGround implies the root label is ground. -/
theorem FOResolutionTree.allLabelsGround_label
    {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FOLiteral L hNoEq)]
    (T : FOResolutionTree L hNoEq)
    (h : allLabelsGround hNoEq T) :
    (FOClause.isGround (by all_goals exact hNoEq)) (T.label (hNoEq := by all_goals exact hNoEq)) := by
-- BEGIN PROOF
  cases T with
  | axiom_ C => exact h
  | resolve T1 T2 rA rB rho rho' sigma => exact h.2.2

-- ===================================================================
-- Lemma 8.5.4: Lifting lemma for resolution refutations
-- ===================================================================

/-- Lemma 8.5.4 (companion): a finite quotient DAG is a resolution DAG
    for S when its leaves belong to S and each internal occurrence has
    exactly two ordered premises and a lawful resolvent. The two premises
    may represent the same quotient vertex. Clause-only labels use the
    simplified convention following Definition 8.5.3. -/
@[blueprint "chap8__lemma_8_5_4"]
def FOResolutionDAGFor {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    (H : LCS.Resolution.Method.DAG (FOClause L hNoEq))
    (S : FOClause L hNoEq → Prop) : Prop :=
  Set.Finite H.tree.domain.dom ∧
  (∀ a, a ∈ H.tree.domain.dom → ∀ i, a ++ [i] ∈ H.tree.domain.dom → i < 2) ∧
  (∀ a, a ∈ H.tree.domain.dom →
    a ++ [0] ∈ H.tree.domain.dom → a ++ [1] ∈ H.tree.domain.dom) ∧
  (∀ a (ha : a ∈ H.tree.domain.dom),
    (¬ a ++ [0] ∈ H.tree.domain.dom) → S (H.tree.label a ha)) ∧
  (∀ a (ha : a ∈ H.tree.domain.dom)
    (h0 : a ++ [0] ∈ H.tree.domain.dom)
    (h1 : a ++ [1] ∈ H.tree.domain.dom),
    IsResolvent hNoEq (H.tree.label a ha)
      (H.tree.label (a ++ [0]) h0) (H.tree.label (a ++ [1]) h1))

/-- Lemma 8.5.4 (companion): every actual node of the ground DAG carries
    a ground clause, including internal nodes and the root. -/
@[blueprint "chap8__lemma_8_5_4"]
def FOResolutionDAGGround {L : Language} (hNoEq : L.withoutEquality)
    (H : LCS.Resolution.Method.DAG (FOClause L hNoEq)) : Prop :=
  ∀ u C, FOResolutionDAGLabel hNoEq H u C → FOClause.isGround hNoEq C

/-- Lemma 8.5.4 (companion): an allowed ground instance of a clause of S.
    The caller may select the allowed substitutions. Their moved support is
    finite, moved images are closed, and the resulting clause is ground;
    clauses are compared by literal membership. -/
@[blueprint "chap8__lemma_8_5_4"]
def FOSelectedGroundInstance {L : Language} (hNoEq : L.withoutEquality)
    (S : FOClause L hNoEq → Prop)
    (select : FOClause L hNoEq → (Nat → Term L) → Prop)
    (C_g : FOClause L hNoEq) : Prop :=
  ∃ (C : FOClause L hNoEq) (sigma : Nat → Term L) (support : List Nat),
    S C ∧ select C sigma ∧
    (∀ x, x ∉ support → sigma x = Term.var x) ∧
    (∀ x, sigma x ≠ Term.var x → termFV (sigma x) = Set.empty) ∧
    FOClause.isGround hNoEq C_g ∧
    (∀ lit, lit ∈ C_g ↔ lit ∈ substLits hNoEq sigma C)

/-- Lemma 8.5.4: every finite family of finite ground resolution DAGs for
    selected ground instances of S lifts to a finite family of lawful
    resolution DAGs for S. Every target component is the rooted, onto image
    of a lifted component, with the node-local ground substitutions carried
    by FOResolutionTreeHom; every lifted component maps to a target component.
    S itself may be arbitrary: only the displayed derivations are finite. -/
@[attach_debt, blueprint "chap8__lemma_8_5_4" (main := true)]
theorem lifting_lemma_refutation {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    (S : FOClause L hNoEq → Prop)
    (groundInstances : FOClause L hNoEq → (Nat → Term L) → Prop)
    (G_g : Set (LCS.Resolution.Method.DAG (FOClause L hNoEq)))
    (hFinite : Set.Finite G_g)
    (hWF : ∀ H_g, G_g H_g →
      FOResolutionDAGFor hNoEq H_g (FOSelectedGroundInstance hNoEq S groundInstances))
    (hAllGround : ∀ H_g, G_g H_g → FOResolutionDAGGround hNoEq H_g) :
    ∃ G : Set (LCS.Resolution.Method.DAG (FOClause L hNoEq)),
      Set.Finite G ∧
      (∀ H, G H → FOResolutionDAGFor hNoEq H S) ∧
      (∀ H_g, G_g H_g → ∃ H, G H ∧ Nonempty (FOResolutionTreeHom L hNoEq H H_g)) ∧
      (∀ H, G H → ∃ H_g, G_g H_g ∧ Nonempty (FOResolutionTreeHom L hNoEq H H_g))

end LCS.FOResolution.Method.Completeness
end
