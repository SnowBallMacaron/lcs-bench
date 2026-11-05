import LCS.Item
import LCS.Util
import LCS.FOResolution.Method
import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.Method.HerbrandBridge
import LCS.Herbrand.SHGTheorem.Main
import LCS.FOResolution.GroundResolution
import LCS.CutElim.LK
import LCS.Resolution.Method.Part1
import Attach
import LCS.FOResolution.Method.Completeness.Substitutions.ProofsStamp

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
-- Example 8.5.3: Lifting example -- clauses C1, C2, C3
-- ===================================================================

/-- Example 8.5.3: C_1 = {neg P(z_1, a), neg P(z_1, x), neg P(x, z_1)}
    from Example 8.2.1. Variables: z_1 = var 1, x = var 4. -/
@[blueprint "chap8__example_8_5_3" (main := true)]
def exLiftClause_C1 : FOClause exClauseFormLang rfl :=
  exClause_C1

/-- Example 8.5.3: C_2 = {P(z_2, f(z_2)), P(z_2, a)}
    from Example 8.2.1. Variable: z_2 = var 2. -/
@[blueprint "chap8__example_8_5_3" (main := true)]
def exLiftClause_C2 : FOClause exClauseFormLang rfl :=
  exClause_C2

/-- Example 8.5.3: C_3 = {P(f(z_3), z_3), P(z_3, a)}
    from Example 8.2.1. Variable: z_3 = var 3. -/
@[blueprint "chap8__example_8_5_3" (main := true)]
def exLiftClause_C3 : FOClause exClauseFormLang rfl :=
  exClause_C3

-- ===================================================================
-- Example 8.5.3: Ground instances G1-G4
-- ===================================================================

/-- Example 8.5.3: G_1 = {neg P(a,a)}, the ground instance of C_1
    under substitution sigma_2 = (a/z_1, a/x). -/
@[blueprint "chap8__example_8_5_3" (main := true)]
def exLiftGroundG1 : FOClause exClauseFormLang rfl :=
  [ FOLiteralCore.neg (exPred_P exSkolemConst_a exSkolemConst_a) ]

/-- Example 8.5.3: G_2 = {P(a,f(a)), P(a,a)}, the ground instance
    of C_2 under substitution sigma_1 = (a/z_2). -/
@[blueprint "chap8__example_8_5_3" (main := true)]
def exLiftGroundG2 : FOClause exClauseFormLang rfl :=
  [ FOLiteralCore.pos (exPred_P exSkolemConst_a exGroundTerm_fa),
    FOLiteralCore.pos (exPred_P exSkolemConst_a exSkolemConst_a) ]

/-- Example 8.5.3: G_3 = {P(f(a),a), P(a,a)}, the ground instance
    of C_3 under substitution sigma_3 = (a/z_3). -/
@[blueprint "chap8__example_8_5_3" (main := true)]
def exLiftGroundG3 : FOClause exClauseFormLang rfl :=
  [ FOLiteralCore.pos (exPred_P exGroundTerm_fa exSkolemConst_a),
    FOLiteralCore.pos (exPred_P exSkolemConst_a exSkolemConst_a) ]

/-- Example 8.5.3: G_4 = {neg P(f(a),a), neg P(a,f(a))}, the ground
    instance of C_1 under substitution sigma_4 = (f(a)/z_1, a/x). -/
@[blueprint "chap8__example_8_5_3" (main := true)]
def exLiftGroundG4 : FOClause exClauseFormLang rfl :=
  [ FOLiteralCore.neg (exPred_P exGroundTerm_fa exSkolemConst_a),
    FOLiteralCore.neg (exPred_P exSkolemConst_a exGroundTerm_fa) ]

-- ===================================================================
-- Example 8.5.3: Ground substitutions sigma_1 through sigma_4
-- ===================================================================

/-- Example 8.5.3: sigma_1 = (a/z_2): maps z_2 (var 2) to constant a,
    identity elsewhere. Used to obtain G_2 from C_2. -/
@[blueprint "chap8__example_8_5_3" (main := true)]
def exLiftSigma1 : Nat → Term exClauseFormLang
  | 2 => exSkolemConst_a  -- z_2 -> a
  | n => Term.var n

/-- Example 8.5.3: sigma_2 = (a/z_1, a/x) maps z_1 (var 1) and
    x (var 4) to a, identity elsewhere; used to obtain G_1 from C_1. -/
@[blueprint "chap8__example_8_5_3" (main := true)]
def exLiftSigma2 : Nat → Term exClauseFormLang
  | 1 => exSkolemConst_a  -- z_1 -> a
  | 4 => exSkolemConst_a  -- x -> a
  | n => Term.var n

/-- Example 8.5.3: sigma_3 = (a/z_3): maps z_3 (var 3) to constant a,
    identity elsewhere. Used to obtain G_3 from C_3. -/
@[blueprint "chap8__example_8_5_3" (main := true)]
def exLiftSigma3 : Nat → Term exClauseFormLang
  | 3 => exSkolemConst_a  -- z_3 -> a
  | n => Term.var n

/-- Example 8.5.3: sigma_4 = (f(a)/z_1, a/x) maps z_1 (var 1) to
    f(a), x (var 4) to a, identity elsewhere; used to obtain G_4 from C_1. -/
@[blueprint "chap8__example_8_5_3" (main := true)]
def exLiftSigma4 : Nat → Term exClauseFormLang
  | 1 => exGroundTerm_fa   -- z_1 -> f(a)
  | 4 => exSkolemConst_a   -- x -> a
  | n => Term.var n

/-- Example 8.5.3 (companion): four leaves followed by four resolution
    steps. Vertices 0,1,2,3 are the displayed leaves 11,12,212,22;
    vertices 4,5,6,7 are the steps 1,21,2 and the root. -/
@[blueprint "chap8__example_8_5_3"]
abbrev ExLiftVertex := Fin 8

/-- Example 8.5.3 (companion): substitutions with an explicit finite
    support witness, using the existing finite-substitution carrier. -/
@[blueprint "chap8__example_8_5_3"]
abbrev ExLiftSubstitution := FiniteSubstitution exClauseFormLang

/-- Example 8.5.3 (companion): an inference stores two earlier vertices,
    its selected literal subsets, separating substitutions and unifier.
    Earlier-vertex bounds make cycles unrepresentable. -/
@[blueprint "chap8__example_8_5_3"]
structure ExLiftInference (index : Nat) where
  left : Fin index
  right : Fin index
  resolvedA : FOClause exClauseFormLang rfl
  resolvedB : FOClause exClauseFormLang rfl
  rho : ExLiftSubstitution
  rho' : ExLiftSubstitution
  sigma : ExLiftSubstitution

/-- Example 8.5.3 (companion): an eight-vertex labeled DAG with a selected
    root. Repeated premise IDs denote a shared vertex, independently of
    whether different vertices have equal clause labels. -/
@[blueprint "chap8__example_8_5_3"]
structure ExLiftDiagram where
  label : ExLiftVertex → FOClause exClauseFormLang rfl
  inference : (v : ExLiftVertex) → Option (ExLiftInference v.val)
  root : ExLiftVertex

/-- Example 8.5.3 (companion): the identity substitution at ground nodes
    and the separating substitutions of the displayed inferences. -/
@[blueprint "chap8__example_8_5_3"]
def exLiftIdentity : ExLiftSubstitution := FiniteSubstitution.identity

/-- Example 8.5.3: the actual node-local finite substitutions. The four
    internal labels are already ground and use the identity substitution. -/
@[blueprint "chap8__example_8_5_3" (main := true)]
def exLiftNodeSubsts : ExLiftVertex → ExLiftSubstitution
  | ⟨0, _⟩ => {
      support := [2]
      map := exLiftSigma1
      outsideSupport := by intro x hx; unfold exLiftSigma1; split <;> simp_all }
  | ⟨1, _⟩ => {
      support := [1, 4]
      map := exLiftSigma2
      outsideSupport := by intro x hx; unfold exLiftSigma2; split <;> simp_all }
  | ⟨2, _⟩ => {
      support := [3]
      map := exLiftSigma3
      outsideSupport := by intro x hx; unfold exLiftSigma3; split <;> simp_all }
  | ⟨3, _⟩ => {
      support := [1, 4]
      map := exLiftSigma4
      outsideSupport := by intro x hx; unfold exLiftSigma4; split <;> simp_all }
  | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ => exLiftIdentity
  | ⟨n + 8, h⟩ => False.elim (by omega)

/-- Example 8.5.3 (companion): the first inference's unifier sends
    z₁,z₂,x to a and fixes every other variable. -/
@[blueprint "chap8__example_8_5_3"]
def exLiftStep1Subst : ExLiftSubstitution where
  support := [1, 2, 4]
  map := fun x => if x ∈ [1, 2, 4] then exSkolemConst_a else Term.var x
  outsideSupport := by intro x hx; simp [hx]

/-- Example 8.5.3 (companion): the second inference's unifier sends
    z₁,z₃,x to a and fixes every other variable. -/
@[blueprint "chap8__example_8_5_3"]
def exLiftStep2Subst : ExLiftSubstitution where
  support := [1, 3, 4]
  map := fun x => if x ∈ [1, 3, 4] then exSkolemConst_a else Term.var x
  outsideSupport := by intro x hx; simp [hx]

/-- Example 8.5.3: the ground diagram has one G₁ vertex shared by its
    first two steps. The final root is the empty clause. -/
@[blueprint "chap8__example_8_5_3" (main := true)]
def exLiftGroundDAG : ExLiftDiagram where
  label
    | ⟨0, _⟩ => exLiftGroundG2
    | ⟨1, _⟩ => exLiftGroundG1
    | ⟨2, _⟩ => exLiftGroundG3
    | ⟨3, _⟩ => exLiftGroundG4
    | ⟨4, _⟩ => [.pos (exPred_P exSkolemConst_a exGroundTerm_fa)]
    | ⟨5, _⟩ => [.pos (exPred_P exGroundTerm_fa exSkolemConst_a)]
    | ⟨6, _⟩ => [.neg (exPred_P exSkolemConst_a exGroundTerm_fa)]
    | ⟨7, _⟩ => []
    | ⟨n + 8, h⟩ => False.elim (by omega)
  inference
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => none
    | ⟨4, _⟩ => some ⟨0, 1,
        [.pos (exPred_P exSkolemConst_a exSkolemConst_a)], exLiftGroundG1,
        exLiftIdentity, exLiftIdentity, exLiftIdentity⟩
    | ⟨5, _⟩ => some ⟨1, 2,
        exLiftGroundG1, [.pos (exPred_P exSkolemConst_a exSkolemConst_a)],
        exLiftIdentity, exLiftIdentity, exLiftIdentity⟩
    | ⟨6, _⟩ => some ⟨5, 3,
        [.pos (exPred_P exGroundTerm_fa exSkolemConst_a)],
        [.neg (exPred_P exGroundTerm_fa exSkolemConst_a)],
        exLiftIdentity, exLiftIdentity, exLiftIdentity⟩
    | ⟨7, _⟩ => some ⟨4, 6,
        [.pos (exPred_P exSkolemConst_a exGroundTerm_fa)],
        [.neg (exPred_P exSkolemConst_a exGroundTerm_fa)],
        exLiftIdentity, exLiftIdentity, exLiftIdentity⟩
    | ⟨n + 8, h⟩ => False.elim (by omega)
  root := 7

/-- Example 8.5.3: the lifted diagram shares vertex 1, labeled C₁,
    between steps 4 and 5. Vertex 3 is the distinct C₁ occurrence for G₄.
    Step 6 selects its actual ground parent P(f(a),a); step 7 yields □. -/
@[blueprint "chap8__example_8_5_3" (main := true)]
def exLiftedDAG : ExLiftDiagram where
  label
    | ⟨0, _⟩ => exLiftClause_C2
    | ⟨1, _⟩ => exLiftClause_C1
    | ⟨2, _⟩ => exLiftClause_C3
    | ⟨3, _⟩ => exLiftClause_C1
    | ⟨4, _⟩ => [.pos (exPred_P exSkolemConst_a exGroundTerm_fa)]
    | ⟨5, _⟩ => [.pos (exPred_P exGroundTerm_fa exSkolemConst_a)]
    | ⟨6, _⟩ => [.neg (exPred_P exSkolemConst_a exGroundTerm_fa)]
    | ⟨7, _⟩ => []
    | ⟨n + 8, h⟩ => False.elim (by omega)
  inference
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => none
    | ⟨4, _⟩ => some ⟨0, 1,
        [.pos (exPred_P (.var 2) exSkolemConst_a)], exLiftClause_C1,
        exLiftIdentity, exLiftIdentity, exLiftStep1Subst⟩
    | ⟨5, _⟩ => some ⟨1, 2,
        exLiftClause_C1, [.pos (exPred_P (.var 3) exSkolemConst_a)],
        exLiftIdentity, exLiftIdentity, exLiftStep2Subst⟩
    | ⟨6, _⟩ => some ⟨5, 3,
        [.pos (exPred_P exGroundTerm_fa exSkolemConst_a)],
        [.neg (exPred_P (.var 1) exSkolemConst_a),
         .neg (exPred_P (.var 1) (.var 4))],
        exLiftIdentity, exLiftIdentity, exLiftNodeSubsts 3⟩
    | ⟨7, _⟩ => some ⟨4, 6,
        [.pos (exPred_P exSkolemConst_a exGroundTerm_fa)],
        [.neg (exPred_P exSkolemConst_a exGroundTerm_fa)],
        exLiftIdentity, exLiftIdentity, exLiftIdentity⟩
    | ⟨n + 8, h⟩ => False.elim (by omega)
  root := 7

/-- Example 8.5.3: the displayed homomorphism is the identity on the
    common eight-vertex topology of H and H_g. -/
@[blueprint "chap8__example_8_5_3" (main := true)]
def exLiftHom : ExLiftVertex → ExLiftVertex := id

/-- Example 8.5.3: the two shared finite diagrams, with the lifted
    source first and its ground image second. -/
@[blueprint "chap8__example_8_5_3" (main := true)]
def exLiftingExample : ExLiftDiagram × ExLiftDiagram :=
  (exLiftedDAG, exLiftGroundDAG)

/-- Example 8.5.3 (companion): the simultaneous substitution carried by
    each displayed finite substitution. -/
@[blueprint "chap8__example_8_5_3"]
def ExLiftSubstitution.toSubst (sigma : ExLiftSubstitution) :
    Nat → Term exClauseFormLang := sigma.map

/-- Example 8.5.3 (companion): the two ordered premise vertices of an
    actual inference row; leaves have no premises. -/
@[blueprint "chap8__example_8_5_3"]
def ExLiftDiagram.premises (G : ExLiftDiagram) (v : ExLiftVertex) :
    Option (ExLiftVertex × ExLiftVertex) :=
  (G.inference v).map fun step =>
    (⟨step.left.val, Nat.lt_trans step.left.isLt v.isLt⟩,
     ⟨step.right.val, Nat.lt_trans step.right.isLt v.isLt⟩)

/-- Example 8.5.3 (companion): legality uses the actual parent labels,
    selected subsets, separating pair and MGU stored in this inference.
    The conclusion is the stored label, compared as a set of literals. -/
@[blueprint "chap8__example_8_5_3"]
def ExLiftDiagram.inferenceLegal (G : ExLiftDiagram) (v : ExLiftVertex)
    (step : ExLiftInference v.val) : Prop :=
  IsResolventVia (L := exClauseFormLang) rfl (G.label v)
    (G.label ⟨step.left.val, Nat.lt_trans step.left.isLt v.isLt⟩)
    (G.label ⟨step.right.val, Nat.lt_trans step.right.isLt v.isLt⟩)
    step.resolvedA step.resolvedB
    step.rho.toSubst step.rho'.toSubst step.sigma.toSubst

/-- Example 8.5.3 (companion): a finite refutation has source-clause
    leaves, lawful stored inferences and an empty root. Earlier premise
    indices in ExLiftInference already ensure acyclicity. -/
@[blueprint "chap8__example_8_5_3"]
def ExLiftDiagram.IsRefutation (G : ExLiftDiagram)
    (S : List (FOClause exClauseFormLang rfl)) : Prop :=
  (∀ v, G.inference v = none → G.label v ∈ S) ∧
  (∀ v step, G.inference v = some step → G.inferenceLegal v step) ∧
  G.label G.root = []

/-- Example 8.5.3 (companion): F sends the two actual ordered premises
    to the two actual ordered premises, and sends leaves to leaves. -/
@[blueprint "chap8__example_8_5_3"]
theorem exLiftHom_preserves_premises (v : ExLiftVertex) :
    exLiftGroundDAG.premises (exLiftHom v) =
      (exLiftedDAG.premises v).map (fun p => (exLiftHom p.1, exLiftHom p.2))

/-- Example 8.5.3 (companion): every ground vertex is the image of a
    displayed lifted vertex. -/
@[blueprint "chap8__example_8_5_3"]
theorem exLiftHom_onto : ∀ v : ExLiftVertex, ∃ u, exLiftHom u = v

/-- Example 8.5.3 (companion): F carries the lifted root to the ground
    root, both of which are labeled by the empty clause. -/
@[blueprint "chap8__example_8_5_3"]
theorem exLiftHom_roots :
    exLiftHom exLiftedDAG.root = exLiftGroundDAG.root ∧
    exLiftedDAG.label exLiftedDAG.root = [] ∧
    exLiftGroundDAG.label exLiftGroundDAG.root = []

/-- Example 8.5.3 (companion): all eight node-local substitutions have
    closed moved images and send the actual source label to its ground
    image label as a set of literals. This includes both distinct C₁
    occurrences and the four internal nodes with identity substitutions. -/
@[attach_debt, blueprint "chap8__example_8_5_3"]
theorem exLiftHom_node_labels (v : ExLiftVertex) :
    (∀ x, (exLiftNodeSubsts v).toSubst x ≠ Term.var x →
      termFV ((exLiftNodeSubsts v).toSubst x) = Set.empty) ∧
    FOClause.isGround (L := exClauseFormLang) rfl (exLiftGroundDAG.label (exLiftHom v)) ∧
    (∀ lit, lit ∈ substLits (L := exClauseFormLang) rfl (exLiftNodeSubsts v).toSubst (exLiftedDAG.label v) ↔
      lit ∈ exLiftGroundDAG.label (exLiftHom v))

/-- Example 8.5.3 (companion): every lifted inference is legal with
    precisely its stored selected literals, separating pair and MGU. -/
@[attach_debt, blueprint "chap8__example_8_5_3"]
theorem exLiftedDAG_inferences_legal (v : ExLiftVertex)
    (step : ExLiftInference v.val) (h : exLiftedDAG.inference v = some step) :
    exLiftedDAG.inferenceLegal v step

/-- Example 8.5.3 (companion): all four ground inferences are legal
    with their stored witnesses and the shared G₁ premise. -/
@[attach_debt, blueprint "chap8__example_8_5_3"]
theorem exLiftGroundDAG_inferences_legal (v : ExLiftVertex)
    (step : ExLiftInference v.val) (h : exLiftGroundDAG.inference v = some step) :
    exLiftGroundDAG.inferenceLegal v step

/-- Example 8.5.3 (companion): the actual example pair consists of a
    refutation of C₁,C₂,C₃ and a refutation of their displayed ground
    instances G₁,G₂,G₃,G₄. -/
@[blueprint "chap8__example_8_5_3"]
theorem exLiftingExample_refutations :
    exLiftingExample.1.IsRefutation [exLiftClause_C1, exLiftClause_C2, exLiftClause_C3] ∧
    exLiftingExample.2.IsRefutation
      [exLiftGroundG1, exLiftGroundG2, exLiftGroundG3, exLiftGroundG4]

-- ===================================================================
-- Lemma 8.5.3 (companion def): substInverse
-- ===================================================================

/-- Lemma 8.5.3 (companion): Given a substitution rho that is injective
    and variable-to-variable on a set S, computes the inverse: for each
    variable y in the range of rho restricted to S, returns the unique
    x in S such that rho(x) = var y. Identity elsewhere. -/
@[blueprint "chap8__lemma_8_5_3"]
noncomputable def substInverse {L : Language}
    (rho : Nat → Term L) (S : Set Nat) : Nat → Term L :=
  fun y =>
    if h : ∃ x, S x ∧ rho x = Term.var y
    then Term.var h.choose
    else Term.var y

-- ===================================================================
-- Lemma 8.5.3 (companion def): combinedSubst
-- ===================================================================

/-- Lemma 8.5.3 (companion): Given separating substitutions (rho, rho')
    and ground substitutions (sigma_1, sigma_2) for clauses A and B,
    forms the combined substitution sigma: for variables in the range
    of rho (i.e., rho(FV(A))), sigma = rho^{-1} composed with sigma_1;
    for variables in the range of rho' (i.e., rho'(FV(B))),
    sigma = rho'^{-1} composed with sigma_2; identity elsewhere.
    Well-defined because the ranges are disjoint. -/
@[blueprint "chap8__lemma_8_5_3"]
noncomputable def combinedSubst {L : Language} (hNoEq : L.withoutEquality)
    (rho rho' : Nat → Term L)
    (sigma_1 sigma_2 : Nat → Term L)
    (A B : FOClause L hNoEq) : Nat → Term L :=
  fun y =>
    if ∃ x, (clauseFV (hNoEq := by all_goals exact hNoEq)) A x ∧ rho x = Term.var y
    then SubstitutionCore.substCompose sigma_1 (substInverse rho ((clauseFV (hNoEq := by all_goals exact hNoEq)) A)) y
    else if ∃ x, (clauseFV (hNoEq := by all_goals exact hNoEq)) B x ∧ rho' x = Term.var y
    then SubstitutionCore.substCompose sigma_2 (substInverse rho' ((clauseFV (hNoEq := by all_goals exact hNoEq)) B)) y
    else Term.var y

-- ===================================================================
-- Lemma 8.5.3 (companion def): liftedLitSubsets
-- ===================================================================

/-- Lemma 8.5.3 (companion): Given a combined substitution sigma, a
    clause A, and a ground literal Q, returns the subset A' of A
    consisting of those literals whose sigma-image equals Q (for
    positive Q) or whose sigma-image of the conjugate equals Q (for
    negative Q). -/
@[blueprint "chap8__lemma_8_5_3"]
def liftedLitSubsets {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FOLiteral L hNoEq)]
    (sigma : Nat → Term L)
    (clause : FOClause L hNoEq)
    (Q : FOLiteral L hNoEq) : List (FOLiteral L hNoEq) :=
  clause.filter (fun lit => (substLit (hNoEq := by all_goals exact hNoEq)) sigma lit = Q)

-- ===================================================================
-- Lemma 8.5.3 (helper): Substitution composition lemmas
-- ===================================================================

-- retained: used by LCS.SLD.FirstOrder.Soundness
/-- Substitution composition for terms: applying theta then sigma
    equals applying (SubstitutionCore.substCompose sigma theta) in one step. -/
theorem termSubstAll_comp {L : Language} (t : Term L) (sigma theta : Nat → Term L) :
    termSubstAll (termSubstAll t theta) sigma = termSubstAll t (SubstitutionCore.substCompose sigma theta) := by
-- BEGIN PROOF
  induction t with
  | var x => simp [termSubstAll, SubstitutionCore.substCompose]
  | const c => simp [termSubstAll]
  | func f args ih => simp only [termSubstAll]; congr 1; funext i; exact ih i

-- retained: used by LCS.SLD.FirstOrder.Soundness
/-- Substitution composition for formulas: applying theta then sigma
    equals applying (SubstitutionCore.substCompose sigma theta) in one step. -/
theorem substFormula_comp {L : Language} (A : FormulaN L) (sigma theta : Nat → Term L) :
    substLit.substFormula sigma (substLit.substFormula theta A) =
    substLit.substFormula (SubstitutionCore.substCompose sigma theta) A := by
-- BEGIN PROOF
  induction A with
  | predN P args =>
    simp only [substLit.substFormula]; congr 1; funext i; exact termSubstAll_comp _ _ _
  | eq_ t1 t2 =>
    simp only [substLit.substFormula]; congr 1 <;> exact termSubstAll_comp _ _ _
  | neg A ih => exact congrArg _ ih
  | conj A B ihA ihB =>
    simp only [substLit.substFormula]; congr 1 <;> assumption
  | disj A B ihA ihB =>
    simp only [substLit.substFormula]; congr 1 <;> assumption
  | impl A B ihA ihB =>
    simp only [substLit.substFormula]; congr 1 <;> assumption
  | all i A ih => exact congrArg _ ih
  | ex i A ih => exact congrArg _ ih

-- retained: used by LCS.SLD.FirstOrder.Soundness, LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
/-- Structural substitution composition for atomic carriers. -/
theorem atomSubst_comp {L : Language} (hNoEq : L.withoutEquality) (atom : FOAtom L hNoEq)
    (sigma theta : Nat → Term L) :
    ((atom.subst (hNoEq := by all_goals exact hNoEq)) theta).subst (hNoEq := hNoEq) sigma =
      (atom.subst (hNoEq := by all_goals exact hNoEq)) (SubstitutionCore.substCompose sigma theta) := by
  cases atom with
  | predN P args =>
      simp only [FOAtomCore.subst, FOAtomCore.mapTerms]
      congr 1
      funext i
      exact termSubstAll_comp _ _ _
  | eq_ hL lhs rhs =>
      simp only [FOAtomCore.subst, FOAtomCore.mapTerms]
      congr 1 <;> exact termSubstAll_comp _ _ _

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting
/-- Substitution composition for literals: applying theta then sigma
    equals applying (SubstitutionCore.substCompose sigma theta) in one step. -/
theorem substLit_comp {L : Language} (hNoEq : L.withoutEquality) (lit : FOLiteral L hNoEq) (sigma theta : Nat → Term L) :
    (substLit (hNoEq := by all_goals exact hNoEq)) sigma ((substLit (hNoEq := by all_goals exact hNoEq)) theta lit) = (substLit (hNoEq := by all_goals exact hNoEq)) (SubstitutionCore.substCompose sigma theta) lit := by
-- BEGIN PROOF
  cases lit with
  | pos B => simp only [substLit]; congr 1; exact (atomSubst_comp (hNoEq := by all_goals exact hNoEq)) B sigma theta
  | neg B => simp only [substLit]; congr 1; exact (atomSubst_comp (hNoEq := by all_goals exact hNoEq)) B sigma theta

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting
/-- Substitution composition for literal lists: applying theta then sigma
    equals applying (SubstitutionCore.substCompose sigma theta) in one step. -/
theorem substLits_comp {L : Language} (hNoEq : L.withoutEquality) (lits : List (FOLiteral L hNoEq)) (sigma theta : Nat → Term L) :
    (substLits (hNoEq := by all_goals exact hNoEq)) sigma ((substLits (hNoEq := by all_goals exact hNoEq)) theta lits) = (substLits (hNoEq := by all_goals exact hNoEq)) (SubstitutionCore.substCompose sigma theta) lits := by
-- BEGIN PROOF
  simp only [substLits, List.map_map]
  congr 1; funext lit; exact (substLit_comp (hNoEq := by all_goals exact hNoEq)) lit sigma theta

-- ===================================================================
-- Lemma 8.5.3 (helper): MGU existence from unifiability
-- ===================================================================



-- ===================================================================
-- Lemma 8.5.3 (helpers): Substitution extensionality and groundness
-- ===================================================================

-- retained: used by LCS.SLD.FirstOrder.Soundness
/-- If two substitutions agree on all free variables of a term,
    then termSubstAll gives the same result for both. -/
theorem termSubstAll_ext {L : Language} (t : Term L) (sigma tau : Nat → Term L)
    (h : ∀ x, termFV t x → sigma x = tau x) :
    termSubstAll t sigma = termSubstAll t tau := by
-- BEGIN PROOF
  induction t with
  | var x => simp only [termSubstAll]; exact h x rfl
  | const c => rfl
  | func f args ih =>
    simp only [termSubstAll]; congr 1; funext i
    exact ih i (fun x hx => h x ⟨i, hx⟩)

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting, LCS.SLD.FirstOrder.HashLanguage, LCS.SLD.FirstOrder.HornEncoding, LCS.SLD.FirstOrder.Soundness
/-- termVars (from ClauseForm) and termFV (from Syntax.Variables)
    are equivalent for the same term. -/
theorem termVars_iff_termFV {L : Language} (t : Term L) (n : Nat) :
    termVars t n ↔ termFV t n := by
  constructor
  · intro h; induction t with
    | var x => exact h | const c => exact h.elim
    | func f args ih => obtain ⟨i, hi⟩ := h; exact ⟨i, ih i hi⟩
  · intro h; induction t with
    | var x => exact h | const c => exact h.elim
    | func f args ih => obtain ⟨i, hi⟩ := h; exact ⟨i, ih i hi⟩

-- retained: used by LCS.SLD.FirstOrder.Soundness
/-- If two substitutions agree on all formula variables, then
    substLit.substFormula gives the same result for both. -/
theorem substFormula_ext_vars {L : Language} (A : FormulaN L)
    (sigma tau : Nat → Term L)
    (h : ∀ x, formulaVars A x → sigma x = tau x) :
    substLit.substFormula sigma A = substLit.substFormula tau A := by
-- BEGIN PROOF
  induction A with
  | predN P args =>
    simp only [substLit.substFormula]; congr 1; funext i
    exact termSubstAll_ext _ _ _
      (fun x hx => h x ⟨i, (termVars_iff_termFV _ x).mpr hx⟩)
  | eq_ t1 t2 =>
    simp only [substLit.substFormula]; congr 1
    · exact termSubstAll_ext _ _ _
        (fun x hx => h x (Or.inl ((termVars_iff_termFV _ x).mpr hx)))
    · exact termSubstAll_ext _ _ _
        (fun x hx => h x (Or.inr ((termVars_iff_termFV _ x).mpr hx)))
  | neg A ih => simp only [substLit.substFormula]; congr 1; exact ih h
  | conj A B ihA ihB =>
    simp only [substLit.substFormula]; congr 1
    · exact ihA (fun x hx => h x (Or.inl hx))
    · exact ihB (fun x hx => h x (Or.inr hx))
  | disj A B ihA ihB =>
    simp only [substLit.substFormula]; congr 1
    · exact ihA (fun x hx => h x (Or.inl hx))
    · exact ihB (fun x hx => h x (Or.inr hx))
  | impl A B ihA ihB =>
    simp only [substLit.substFormula]; congr 1
    · exact ihA (fun x hx => h x (Or.inl hx))
    · exact ihB (fun x hx => h x (Or.inr hx))
  | all i A ih => simp only [substLit.substFormula]; congr 1; exact ih h
  | ex i A ih => simp only [substLit.substFormula]; congr 1; exact ih h

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting
/-- Atom substitution depends only on variables occurring in the atom. -/
theorem atomSubst_ext_vars {L : Language} (hNoEq : L.withoutEquality) (atom : FOAtom L hNoEq)
    (sigma tau : Nat → Term L)
    (h : ∀ x, atom.vars x → sigma x = tau x) :
    (atom.subst (hNoEq := by all_goals exact hNoEq)) sigma = (atom.subst (hNoEq := by all_goals exact hNoEq)) tau := by
  cases atom with
  | predN P args =>
      simp only [FOAtomCore.subst, FOAtomCore.mapTerms]
      congr 1
      funext i
      exact termSubstAll_ext _ _ _
        (fun x hx => h x ⟨i, (termVars_iff_termFV _ x).mpr hx⟩)
  | eq_ hL lhs rhs =>
      simp only [FOAtomCore.subst, FOAtomCore.mapTerms]
      congr 1
      · exact termSubstAll_ext _ _ _
          (fun x hx => h x (Or.inl ((termVars_iff_termFV _ x).mpr hx)))
      · exact termSubstAll_ext _ _ _
          (fun x hx => h x (Or.inr ((termVars_iff_termFV _ x).mpr hx)))

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting
/-- If two substitutions agree on all variables of a literal, then
    substLit gives the same result for both. -/
theorem substLit_ext_vars {L : Language} (hNoEq : L.withoutEquality) (lit : FOLiteral L hNoEq)
    (sigma tau : Nat → Term L)
    (h : ∀ x, (FOLiteral.vars hNoEq lit) x → sigma x = tau x) :
    (substLit (hNoEq := by all_goals exact hNoEq)) sigma lit = (substLit (hNoEq := by all_goals exact hNoEq)) tau lit := by
-- BEGIN PROOF
  cases lit with
  | pos B => simp only [substLit]; congr 1; exact (atomSubst_ext_vars (hNoEq := by all_goals exact hNoEq)) B sigma tau h
  | neg B => simp only [substLit]; congr 1; exact (atomSubst_ext_vars (hNoEq := by all_goals exact hNoEq)) B sigma tau h

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting
/-- If two substitutions agree on all variables of every literal in
    a clause, then substLits gives the same result for both. -/
theorem substLits_ext_vars {L : Language} (hNoEq : L.withoutEquality) (c : FOClause L hNoEq)
    (sigma tau : Nat → Term L)
    (h : ∀ lit ∈ c, ∀ x, (FOLiteral.vars hNoEq lit) x → sigma x = tau x) :
    (substLits (hNoEq := by all_goals exact hNoEq)) sigma c = (substLits (hNoEq := by all_goals exact hNoEq)) tau c := by
-- BEGIN PROOF
  simp only [substLits]
  induction c with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map]; congr 1
    · exact (substLit_ext_vars (hNoEq := by all_goals exact hNoEq)) hd sigma tau (h hd List.mem_cons_self)
    · exact ih (fun lit hlit => h lit (List.mem_cons_of_mem _ hlit))

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness, LCS.FOResolution.Method.Completeness.Lifting
/-- A literal in a ground clause has no variables. -/
theorem isGround_lit_no_vars {L : Language} (hNoEq : L.withoutEquality) (c : FOClause L hNoEq)
    (hGround : (FOClause.isGround (by all_goals exact hNoEq)) c)
    (lit : FOLiteral L hNoEq) (hlit : lit ∈ c) :
    (FOLiteral.vars hNoEq lit) = Set.empty := by
-- BEGIN PROOF
  ext m; constructor
  · intro h
    have hHas : (FOClause.vars hNoEq c) m := ⟨lit, hlit, h⟩
    dsimp only [FOClause.vars] at hHas; rw [hGround] at hHas; exact hHas
  · intro h; exact h.elim

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness, LCS.FOResolution.Method.Completeness.Lifting
/-- Substitution on a ground clause is the identity.
    Ground means no variables, so substitution changes nothing. -/
theorem substLits_ground_id {L : Language} (hNoEq : L.withoutEquality) (c : FOClause L hNoEq)
    (sigma : Nat → Term L)
    (hGround : (FOClause.isGround (by all_goals exact hNoEq)) c) :
    (substLits (hNoEq := by all_goals exact hNoEq)) sigma c = c := by
-- BEGIN PROOF
  simp only [substLits]
  induction c with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map]; congr 1
    · -- substLit sigma hd = hd
      have hhd : FOLiteral.vars hNoEq hd = Set.empty :=
        (isGround_lit_no_vars (hNoEq := by all_goals exact hNoEq)) (hd :: tl) hGround hd List.mem_cons_self
      exact substLit_ground_id hd sigma hhd
    · exact ih (by
        ext m; constructor
        · intro ⟨l, hm, hv⟩
          have : (FOClause.vars (by all_goals exact hNoEq)) (hd :: tl) m :=
            ⟨l, List.mem_cons_of_mem _ hm, hv⟩
          dsimp only [FOClause.vars] at this; rw [hGround] at this; exact this
        · intro h; exact h.elim)
where
  /-- Inline proof: substLit on a ground literal is identity. -/
  substLit_ground_id (lit : FOLiteral L hNoEq)
      (sigma : Nat → Term L) (hGround : (FOLiteral.vars hNoEq lit) = Set.empty) :
      (substLit (hNoEq := by all_goals exact hNoEq)) sigma lit = lit := by
    cases lit with
    | pos B =>
      simp only [substLit]; congr 1
      exact substAtom_ground_id B sigma hGround
    | neg B =>
      simp only [substLit]; congr 1
      exact substAtom_ground_id B sigma hGround
  /-- Inline proof: atom substitution on a ground atom is identity. -/
  substAtom_ground_id (atom : FOAtom L hNoEq)
      (sigma : Nat → Term L) (hGround : atom.vars = Set.empty) :
      (atom.subst (hNoEq := by all_goals exact hNoEq)) sigma = atom := by
    cases atom with
    | predN P args =>
      simp only [FOAtomCore.subst, FOAtomCore.mapTerms]; congr 1; funext i
      exact termSubstAll_ground_id (args i) sigma (by
        ext n; constructor
        · intro h
          have : FOAtomCore.vars (.predN P args) n :=
            ⟨i, (termVars_iff_termFV _ n).mpr h⟩
          rw [hGround] at this; exact this
        · intro h; exact h.elim)
    | eq_ hLeq t1 t2 =>
      simp only [FOAtomCore.subst, FOAtomCore.mapTerms]; congr 1
      all_goals (apply termSubstAll_ground_id; ext n; constructor)
      · intro h; have := (show FOAtomCore.vars (.eq_ hLeq t1 t2) n from
          Or.inl ((termVars_iff_termFV _ n).mpr h)); rw [hGround] at this; exact this
      · intro h; exact h.elim
      · intro h; have := (show FOAtomCore.vars (.eq_ hLeq t1 t2) n from
          Or.inr ((termVars_iff_termFV _ n).mpr h)); rw [hGround] at this; exact this
      · intro h; exact h.elim
  /-- Inline proof: termSubstAll on ground term is identity. -/
  termSubstAll_ground_id {L : Language} (t : Term L)
      (sigma : Nat → Term L) (hGround : termFV t = Set.empty) :
      termSubstAll t sigma = t := by
    induction t with
    | var x =>
      exfalso
      have : termFV (@Term.var L x) = Set.singleton x := by
        ext n; simp [termFV, Set.singleton]
      rw [this] at hGround
      have : (Set.singleton x : Set Nat) x := rfl
      rw [hGround] at this; exact this
    | const c => rfl
    | func f args ih =>
      simp only [termSubstAll]; congr 1; funext i; apply ih i
      ext n; constructor
      · intro h
        have : termFV (Term.func f args) n :=
          show (Set.iUnion fun j => termFV (args j)) n from ⟨i, h⟩
        rw [hGround] at this; exact this
      · intro h; exact h.elim

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness, LCS.FOResolution.Method.Completeness.Lifting
/-- A sublist of a ground clause is ground. -/
theorem isGround_of_sublist {L : Language} (hNoEq : L.withoutEquality) (c sub : FOClause L hNoEq)
    (hGround : (FOClause.isGround (by all_goals exact hNoEq)) c) (hSub : IsSublist sub c) :
    (FOClause.isGround (by all_goals exact hNoEq)) sub := by
-- BEGIN PROOF
  ext m; constructor
  · intro ⟨l, hm, hv⟩
    have : (FOClause.vars (by all_goals exact hNoEq)) c m := ⟨l, hSub l hm, hv⟩
    dsimp only [FOClause.vars] at this; rw [hGround] at this; exact this
  · intro h; exact h.elim

-- retained: used by LCS.FOResolution.GroundResolution.PropositionalTranslation, LCS.FOResolution.Method.Completeness.Completeness, LCS.FOResolution.Method.Completeness.Lifting
/-- The append of two ground clauses is ground. -/
theorem isGround_append {L : Language} (hNoEq : L.withoutEquality) (c1 c2 : FOClause L hNoEq)
    (h1 : (FOClause.isGround (by all_goals exact hNoEq)) c1) (h2 : (FOClause.isGround (by all_goals exact hNoEq)) c2) :
    (FOClause.isGround (by all_goals exact hNoEq)) (c1 ++ c2) := by
-- BEGIN PROOF
  ext m; constructor
  · intro ⟨l, hm, hv⟩; rw [List.mem_append] at hm
    rcases hm with h | h
    · have : (FOClause.vars (by all_goals exact hNoEq)) c1 m := ⟨l, h, hv⟩; dsimp only [FOClause.vars] at this; rw [h1] at this; exact this
    · have : (FOClause.vars (by all_goals exact hNoEq)) c2 m := ⟨l, h, hv⟩; dsimp only [FOClause.vars] at this; rw [h2] at this; exact this
  · intro h; exact h.elim

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting
/-- substLits distributes over list append. -/
theorem substLits_append {L : Language} (hNoEq : L.withoutEquality) (sigma : Nat → Term L)
    (l1 l2 : List (FOLiteral L hNoEq)) :
    (substLits (hNoEq := by all_goals exact hNoEq)) sigma (l1 ++ l2) = (substLits (hNoEq := by all_goals exact hNoEq)) sigma l1 ++ (substLits (hNoEq := by all_goals exact hNoEq)) sigma l2 := by
-- BEGIN PROOF
  simp [substLits, List.map_append]

-- ===================================================================
-- Lemma 8.5.3 (helpers): combinedSubst composition properties
-- ===================================================================

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting
/-- The combined substitution composed with rho gives sigma_1
    on variables in FV(A). This is the key property that connects
    the lifted substitution to the ground substitution on the A side. -/
theorem combinedSubst_compose_rho {L : Language} (hNoEq : L.withoutEquality)
    (A B : FOClause L hNoEq)
    (sigma_1 sigma_2 : Nat → Term L)
    (rho rho' : Nat → Term L)
    (hSep : (IsSeparatingPair (hNoEq := by all_goals exact hNoEq)) rho rho' A B)
    (x : Nat) (hx : (clauseFV (hNoEq := by all_goals exact hNoEq)) A x) :
    SubstitutionCore.substCompose ((combinedSubst (hNoEq := by all_goals exact hNoEq)) rho rho' sigma_1 sigma_2 A B) rho x =
      sigma_1 x := by
-- BEGIN PROOF
  obtain ⟨hRhoVar, _, hRhoInj, _, _, _, _⟩ := hSep
  obtain ⟨y, hy_eq⟩ := hRhoVar x hx
  show termSubstAll (rho x) ((combinedSubst (hNoEq := by all_goals exact hNoEq)) rho rho' sigma_1 sigma_2 A B) =
    sigma_1 x
  rw [hy_eq]; simp only [termSubstAll]
  show (combinedSubst (hNoEq := by all_goals exact hNoEq)) rho rho' sigma_1 sigma_2 A B y = sigma_1 x
  unfold combinedSubst
  have hCond : ∃ z, (clauseFV (hNoEq := by all_goals exact hNoEq)) A z ∧ rho z = Term.var y := ⟨x, hx, hy_eq⟩
  rw [if_pos hCond]
  show SubstitutionCore.substCompose sigma_1 (substInverse rho ((clauseFV (hNoEq := by all_goals exact hNoEq)) A)) y = sigma_1 x
  unfold SubstitutionCore.substCompose substInverse
  rw [dif_pos hCond]; simp only [termSubstAll]
  congr 1
  exact hRhoInj hCond.choose x hCond.choose_spec.1 hx
    (by rw [hCond.choose_spec.2, hy_eq])

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting
/-- The combined substitution composed with rho' gives sigma_2
    on variables in FV(B). Analogous to combinedSubst_compose_rho
    but uses the disjoint ranges property. -/
theorem combinedSubst_compose_rho' {L : Language} (hNoEq : L.withoutEquality)
    (A B : FOClause L hNoEq)
    (sigma_1 sigma_2 : Nat → Term L)
    (rho rho' : Nat → Term L)
    (hSep : (IsSeparatingPair (hNoEq := by all_goals exact hNoEq)) rho rho' A B)
    (x : Nat) (hx : (clauseFV (hNoEq := by all_goals exact hNoEq)) B x) :
    SubstitutionCore.substCompose ((combinedSubst (hNoEq := by all_goals exact hNoEq)) rho rho' sigma_1 sigma_2 A B) rho' x =
      sigma_2 x := by
-- BEGIN PROOF
  obtain ⟨_, hRho'Var, _, hRho'Inj, hDisjoint, _, _⟩ := hSep
  obtain ⟨y, hy_eq⟩ := hRho'Var x hx
  show termSubstAll (rho' x) ((combinedSubst (hNoEq := by all_goals exact hNoEq)) rho rho' sigma_1 sigma_2 A B) =
    sigma_2 x
  rw [hy_eq]; simp only [termSubstAll]
  show (combinedSubst (hNoEq := by all_goals exact hNoEq)) rho rho' sigma_1 sigma_2 A B y = sigma_2 x
  unfold combinedSubst
  have hNotA : ¬ ∃ z, (clauseFV (hNoEq := by all_goals exact hNoEq)) A z ∧ rho z = Term.var y := by
    intro ⟨z, hz, hrho_z⟩
    have hInRange_rho : substRangeOnSet rho ((clauseFV (hNoEq := by all_goals exact hNoEq)) A) y := ⟨z, hz, hrho_z⟩
    have hInRange_rho' : substRangeOnSet rho' ((clauseFV (hNoEq := by all_goals exact hNoEq)) B) y := ⟨x, hx, hy_eq⟩
    have hInInter : (substRangeOnSet rho ((clauseFV (hNoEq := by all_goals exact hNoEq)) A) ∩
      substRangeOnSet rho' ((clauseFV (hNoEq := by all_goals exact hNoEq)) B)) y :=
      ⟨hInRange_rho, hInRange_rho'⟩
    rw [hDisjoint] at hInInter; exact hInInter
  rw [if_neg hNotA]
  have hCondB : ∃ z, (clauseFV (hNoEq := by all_goals exact hNoEq)) B z ∧ rho' z = Term.var y := ⟨x, hx, hy_eq⟩
  rw [if_pos hCondB]
  show SubstitutionCore.substCompose sigma_2 (substInverse rho' ((clauseFV (hNoEq := by all_goals exact hNoEq)) B)) y = sigma_2 x
  unfold SubstitutionCore.substCompose substInverse
  rw [dif_pos hCondB]; simp only [termSubstAll]
  congr 1
  exact hRho'Inj hCondB.choose x hCondB.choose_spec.1 hx
    (by rw [hCondB.choose_spec.2, hy_eq])

-- ===================================================================
-- Lemma 8.5.3 (helpers): List filter/map commutativity
-- ===================================================================

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting
/-- Filter and map commute when the predicates correspond:
    (xs.map f).filter q = (xs.filter p).map f when p = q ∘ f on xs. -/
theorem list_filter_map_comm {α β : Type}
    (f : α → β) (p : α → Bool) (q : β → Bool) (xs : List α)
    (h : ∀ x ∈ xs, p x = q (f x)) :
    (xs.map f).filter q = (xs.filter p).map f := by
-- BEGIN PROOF
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map, List.filter]
    rw [h x List.mem_cons_self]
    split
    · next _ => simp only [List.map]; congr 1
                exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    · next _ => exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting
/-- For a ∈ xs, (xs.filter pred).contains a = pred a. -/
theorem filter_contains_eq_pred {α : Type} [DecidableEq α]
    (xs : List α) (pred : α → Bool) (a : α) (ha : a ∈ xs) :
    (xs.filter pred).contains a = pred a := by
-- BEGIN PROOF
  cases hpa : pred a
  · apply Bool.eq_false_iff.mpr
    intro hc; rw [List.contains_iff_exists_mem_beq] at hc
    obtain ⟨b, hb_mem, hb_eq⟩ := hc
    rw [eq_of_beq hb_eq] at hpa
    rw [List.mem_filter] at hb_mem
    rw [hb_mem.2] at hpa; exact Bool.noConfusion hpa
  · rw [List.contains_iff_exists_mem_beq]
    exact ⟨a, List.mem_filter.mpr ⟨ha, hpa⟩, beq_self_eq_true a⟩

-- ===================================================================
-- Lemma 8.5.3 (helpers): litSetUnifTerms invariance and substitution
-- ===================================================================













-- retained: used by LCS.FOResolution.Method.Completeness.Lifting
/-- Membership characterization for litSetUnifTerms (foldl version):
    t is in the foldl result iff it was in the accumulator or it is
    an argument of some predN literal in the list. Uses the inline
    step function matching litSetUnifTerms definition. -/
theorem litSetUnifTerms_mem_iff_foldl {L : Language} (hNoEq : L.withoutEquality)
    {lits : List (FOLiteral L hNoEq)} {acc : List (Term L)} {t : Term L} :
    t ∈ lits.foldl (fun acc lit =>
      match lit with
      | .pos (.predN _ args) => acc ++ List.ofFn args
      | .neg (.predN _ args) => acc ++ List.ofFn args
      | _ => acc) acc ↔
    t ∈ acc ∨ ∃ (P : L.predSymbols)
      (args : Fin (L.predArity P) → Term L)
      (i : Fin (L.predArity P)),
      (FOLiteralCore.pos (.predN P args) ∈ lits ∨
       FOLiteralCore.neg (.predN P args) ∈ lits) ∧
      t = args i := by
-- BEGIN PROOF
  induction lits generalizing acc with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl_cons]; rw [ih]
    constructor
    · intro h
      rcases h with h_acc | ⟨P, args, i, hmem, rfl⟩
      · cases hd with
        | pos f =>
          cases f with
          | predN P args =>
            rw [List.mem_append] at h_acc
            rcases h_acc with h | h
            · exact Or.inl h
            · rw [List.mem_ofFn] at h; obtain ⟨i, rfl⟩ := h
              exact Or.inr ⟨P, args, i, Or.inl (List.mem_cons_self ..), rfl⟩
          | _ => exact Or.inl h_acc
        | neg f =>
          cases f with
          | predN P args =>
            rw [List.mem_append] at h_acc
            rcases h_acc with h | h
            · exact Or.inl h
            · rw [List.mem_ofFn] at h; obtain ⟨i, rfl⟩ := h
              exact Or.inr ⟨P, args, i, Or.inr (List.mem_cons_self ..), rfl⟩
          | _ => exact Or.inl h_acc
      · exact Or.inr ⟨P, args, i,
          hmem.imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _), rfl⟩
    · intro h
      rcases h with h | ⟨P, args, i, hmem, rfl⟩
      · left
        cases hd with
        | pos f => cases f <;> first | exact List.mem_append_left _ h | exact h
        | neg f => cases f <;> first | exact List.mem_append_left _ h | exact h
      · rcases hmem with hmem | hmem
        · rcases List.mem_cons.mp hmem with rfl | htl
          · left
            exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
          · right; exact ⟨P, args, i, Or.inl htl, rfl⟩
        · rcases List.mem_cons.mp hmem with rfl | htl
          · left
            exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
          · right; exact ⟨P, args, i, Or.inr htl, rfl⟩

end LCS.FOResolution.Method.Completeness
end
