import LCS.Item
import LCS.Util
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import LCS.FOResolution.Method.Resolvents
import LCS.FOResolution.Method.ResolutionDAGs
import LCS.FOResolution.Method.ResolventExample
import Attach
import LCS.FOResolution.Method.RefutationExample.ProofsStamp

section
namespace LCS.FOResolution.Method
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification

-- ===================================================================
-- Example 8.5.2: Resolution refutation example
-- ===================================================================

/-- Example 8.5.2: C_1 = {neg P(z_1, a), neg P(z_1, x), neg P(x, z_1)}
    with z_1 = var 1, x = var 4. -/
@[blueprint "chap8__example_8_5_2" (main := true)]
def exRefClause_C1 : FOClause exClauseFormLang rfl :=
  exClause_C1

/-- Example 8.5.2: C_2 = {P(z_2, f(z_2)), P(z_2, a)} with z_2 = var 2. -/
@[blueprint "chap8__example_8_5_2" (main := true)]
def exRefClause_C2 : FOClause exClauseFormLang rfl :=
  exClause_C2

/-- Example 8.5.2: C_3 = {P(f(z_3), z_3), P(z_3, a)} with z_3 = var 3. -/
@[blueprint "chap8__example_8_5_2" (main := true)]
def exRefClause_C3 : FOClause exClauseFormLang rfl :=
  exClause_C3

/-- Example 8.5.2: Step 1 -- C_2 resolves with C_1 using identity
    separating pair and mgu (a/z_1, a/z_2, a/x), yielding {P(a, f(a))}. -/
@[blueprint "chap8__example_8_5_2" (main := true)]
def exRefStep1 : FOResolutionTree exClauseFormLang rfl :=
  .resolve
    (.axiom_ exRefClause_C2)
    (.axiom_ exRefClause_C1)
    -- resolvedA: P(z_2, a) from C_2
    [ FOLiteralCore.pos (exPred_P (Term.var 2) exSkolemConst_a) ]
    -- resolvedB: all of C_1
    exRefClause_C1
    (fun n => Term.var n)  -- rho = identity
    (fun n => Term.var n)  -- rho' = identity
    (fun n => match n with -- sigma = (a/z_1, a/z_2, a/x)
      | 1 => exSkolemConst_a
      | 2 => exSkolemConst_a
      | 4 => exSkolemConst_a
      | n => Term.var n)

/-- Example 8.5.2: Step 2 -- C_1 resolves with C_3 using identity
    separating pair and mgu (a/z_1, a/x, a/z_3), yielding {P(f(a), a)}. -/
@[blueprint "chap8__example_8_5_2" (main := true)]
def exRefStep2 : FOResolutionTree exClauseFormLang rfl :=
  .resolve
    (.axiom_ exRefClause_C1)
    (.axiom_ exRefClause_C3)
    -- resolvedA: all of C_1 (negative literals)
    exRefClause_C1
    -- resolvedB: P(z_3, a) from C_3
    [ FOLiteralCore.pos (exPred_P (Term.var 3) exSkolemConst_a) ]
    (fun n => Term.var n)
    (fun n => Term.var n)
    (fun n => match n with
      | 1 => exSkolemConst_a
      | 3 => exSkolemConst_a
      | 4 => exSkolemConst_a
      | n => Term.var n)

/-- Example 8.5.2: Step 3 -- C_1 resolves with V = {P(f(a), a)}
    from step 2, using mgu (f(a)/z_1, a/x), yielding {neg P(a, f(a))}. -/
@[blueprint "chap8__example_8_5_2" (main := true)]
def exRefStep3 : FOResolutionTree exClauseFormLang rfl :=
  .resolve
    (.axiom_ exRefClause_C1)
    exRefStep2
    -- The first two negative literals of C_1.
    [ FOLiteralCore.neg (exPred_P (Term.var 1) exSkolemConst_a),
      FOLiteralCore.neg (exPred_P (Term.var 1) (Term.var 4)) ]
    -- All of V = {P(f(a), a)}.
    [ FOLiteralCore.pos (exPred_P
        (Term.func ExClauseFunc.f (fun _ => exSkolemConst_a)) exSkolemConst_a) ]
    (fun n => Term.var n)
    (fun n => Term.var n)
    (fun n => match n with
      | 1 => Term.func ExClauseFunc.f (fun _ => exSkolemConst_a)
      | 4 => exSkolemConst_a
      | n => Term.var n)

/-- Example 8.5.2: Step 4 -- U resolves with W, the result of the
    C_1,V inference, using the identity mgu and yielding the empty clause. -/
@[blueprint "chap8__example_8_5_2" (main := true)]
def exRefStep4 : FOResolutionTree exClauseFormLang rfl :=
  .resolve
    exRefStep1
    exRefStep3
    -- resolvedA: all of step 1 label = {P(a,f(a))}
    [ FOLiteralCore.pos (exPred_P exSkolemConst_a
        (Term.func ExClauseFunc.f (fun _ => exSkolemConst_a))) ]
    -- resolvedB: all of step 3 label = {neg P(a,f(a))}
    [ FOLiteralCore.neg (exPred_P exSkolemConst_a
        (Term.func ExClauseFunc.f (fun _ => exSkolemConst_a))) ]
    (fun n => Term.var n)
    (fun n => Term.var n)
    (fun n => Term.var n)  -- identity mgu

/-- Example 8.5.2: The positive unit label U = {P(a,f(a))}. -/
@[blueprint "chap8__example_8_5_2"]
def exRefLabel_U : FOClause exClauseFormLang rfl := exRes_C_second

/-- Example 8.5.2: The positive unit label V = {P(f(a),a)}. -/
@[blueprint "chap8__example_8_5_2"]
def exRefLabel_V : FOClause exClauseFormLang rfl :=
  [FOLiteralCore.pos (exPred_P
    (Term.func ExClauseFunc.f (fun _ => exSkolemConst_a)) exSkolemConst_a)]

/-- Example 8.5.2: The negative unit label W = {neg P(a,f(a))}. -/
@[blueprint "chap8__example_8_5_2"]
def exRefLabel_W : FOClause exClauseFormLang rfl :=
  [FOLiteralCore.neg (exPred_P exSkolemConst_a
    (Term.func ExClauseFunc.f (fun _ => exSkolemConst_a)))]

/-- Example 8.5.2: The identity substitutions displayed at the inference nodes. -/
@[blueprint "chap8__example_8_5_2"]
def exRefId : Nat → Term exClauseFormLang := Term.var

/-- Example 8.5.2: An internal vertex stores its two premise vertex IDs,
    pivot subsets, separating maps, and unifier. IDs range over the seven
    displayed vertices C1,C2,C3,U,V,W,E in that order. -/
@[blueprint "chap8__example_8_5_2"]
structure ExRefInference where
  left : Fin 7
  right : Fin 7
  resolvedA : FOClause exClauseFormLang rfl
  resolvedB : FOClause exClauseFormLang rfl
  rho : Nat → Term exClauseFormLang
  rho' : Nat → Term exClauseFormLang
  sigma : Nat → Term exClauseFormLang

/-- Example 8.5.2: A graph vertex has its displayed clause and, precisely
    at an internal vertex, its local inference data. -/
@[blueprint "chap8__example_8_5_2"]
structure ExRefNode where
  clause : FOClause exClauseFormLang rfl
  inference : Option ExRefInference

/-- Example 8.5.2: The finite graph table with vertices C1,C2,C3,U,V,W,E.
    Each premise occurrence names a vertex in this same table. In particular
    the three occurrences of C1 all reference vertex 0; E is vertex 6. -/
@[blueprint "chap8__example_8_5_2" (main := true)]
def exResolutionRefutation (i : Fin 7) : ExRefNode :=
  match i.val with
  | 0 => ⟨exRefClause_C1, none⟩
  | 1 => ⟨exRefClause_C2, none⟩
  | 2 => ⟨exRefClause_C3, none⟩
  | 3 => ⟨exRefLabel_U, some {
      left := 1, right := 0
      resolvedA := [FOLiteralCore.pos (exPred_P (Term.var 2) exSkolemConst_a)]
      resolvedB := exRefClause_C1
      rho := exRefId, rho' := exRefId
      sigma := fun n => match n with
        | 1 | 2 | 4 => exSkolemConst_a
        | n => Term.var n }⟩
  | 4 => ⟨exRefLabel_V, some {
      left := 0, right := 2
      resolvedA := exRefClause_C1
      resolvedB := [FOLiteralCore.pos (exPred_P (Term.var 3) exSkolemConst_a)]
      rho := exRefId, rho' := exRefId
      sigma := fun n => match n with
        | 1 | 3 | 4 => exSkolemConst_a
        | n => Term.var n }⟩
  | 5 => ⟨exRefLabel_W, some {
      left := 0, right := 4
      resolvedA := [FOLiteralCore.neg (exPred_P (Term.var 1) exSkolemConst_a),
        FOLiteralCore.neg (exPred_P (Term.var 1) (Term.var 4))]
      resolvedB := exRefLabel_V
      rho := exRefId, rho' := exRefId
      sigma := fun n => match n with
        | 1 => Term.func ExClauseFunc.f (fun _ => exSkolemConst_a)
        | 4 => exSkolemConst_a
        | n => Term.var n }⟩
  | _ => ⟨[], some {
      left := 3, right := 5
      resolvedA := exRefLabel_U, resolvedB := exRefLabel_W
      rho := exRefId, rho' := exRefId, sigma := exRefId }⟩

/-- Example 8.5.2: The root is the displayed empty-clause vertex E. -/
@[blueprint "chap8__example_8_5_2"]
def exResolutionRefutation_root : Fin 7 := 6

/-- Example 8.5.2: Follow ordered premise occurrences in the finite graph;
    false chooses the left premise and true the right premise. -/
@[blueprint "chap8__example_8_5_2"]
def exResolutionRefutation_follow (i : Fin 7) : List Bool → Option (Fin 7)
  | [] => some i
  | side :: rest => do
      let step ← (exResolutionRefutation i).inference
      exResolutionRefutation_follow (if side then step.right else step.left) rest

/-- Example 8.5.2: The four corrected computation trees have exactly the
    displayed labels U,V,W,empty. -/
@[attach_debt, blueprint "chap8__example_8_5_2"]
theorem exRefStep_labels :
    @FOResolutionTree.label exClauseFormLang rfl (Classical.typeDecidableEq _) exRefStep1 = exRefLabel_U ∧
    @FOResolutionTree.label exClauseFormLang rfl (Classical.typeDecidableEq _) exRefStep2 = exRefLabel_V ∧
    @FOResolutionTree.label exClauseFormLang rfl (Classical.typeDecidableEq _) exRefStep3 = exRefLabel_W ∧
    @FOResolutionTree.label exClauseFormLang rfl (Classical.typeDecidableEq _) exRefStep4 = []

/-- Example 8.5.2: Premises precede their conclusions, every one of the
    seven vertices is reachable from E, and exactly the three input vertices
    are leaves. Together with lawful inferences and the empty root this
    certifies the displayed finite shared refutation. -/
@[attach_debt, blueprint "chap8__example_8_5_2"]
theorem exResolutionRefutation_correct :
    (∀ (i : Fin 7) (step : ExRefInference),
      (exResolutionRefutation i).inference = some step →
      step.left.val < i.val ∧ step.right.val < i.val) ∧
    (∀ i : Fin 7, ∃ path : List Bool,
      exResolutionRefutation_follow exResolutionRefutation_root path = some i) ∧
    (∀ i : Fin 7, (exResolutionRefutation i).inference = none ↔ i.val < 3) ∧
    (exResolutionRefutation 0).clause = exRefClause_C1 ∧
    (exResolutionRefutation 1).clause = exRefClause_C2 ∧
    (exResolutionRefutation 2).clause = exRefClause_C3 ∧
    (∀ (i : Fin 7) (step : ExRefInference),
      (exResolutionRefutation i).inference = some step →
      @IsResolventVia exClauseFormLang rfl (Classical.typeDecidableEq _)
        (exResolutionRefutation i).clause
        (exResolutionRefutation step.left).clause
        (exResolutionRefutation step.right).clause
        step.resolvedA step.resolvedB step.rho step.rho' step.sigma) ∧
    (exResolutionRefutation exResolutionRefutation_root).clause = []

end LCS.FOResolution.Method
end
