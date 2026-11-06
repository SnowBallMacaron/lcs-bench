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
import LCS.FOResolution.Method.Completeness.LiftingExample.ProofsStamp

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

end LCS.FOResolution.Method.Completeness
end
