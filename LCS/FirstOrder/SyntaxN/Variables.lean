import LCS.Item
import LCS.FirstOrder.SyntaxN
import Attach
import LCS.FirstOrder.SyntaxN.Variables.ProofsStamp

/-! # FirstOrder.SyntaxN.Variables
    Free and bound variables for FormulaN (§5.3.8+ normalized formulae).
    Self-contained on FormulaN. Uses termFV from Basic.lean.
-/

namespace LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN

-- ===================================================================
-- Free variables of FormulaN
-- ===================================================================

/-- Definition 5.2.4 (companion): The set FV(A) of free variables of a
normalized formula A — the FormulaN-side transcription of Def 5.2.4's
FV(A) clause. -/
@[blueprint "chap5__definition_5_2_4"]
def formulaFVN {L : Language} : FormulaN L → Set Nat
  | .predN P ts =>
    Set.iUnion (fun (j : Fin (L.predArity P)) => termFV (ts j))
  | .eq_ _ t1 t2 => termFV t1 ∪ termFV t2
  | .neg A => formulaFVN A
  | .conj A B => formulaFVN A ∪ formulaFVN B
  | .disj A B => formulaFVN A ∪ formulaFVN B
  | .impl A B => formulaFVN A ∪ formulaFVN B
  | .all i A => formulaFVN A \ Set.singleton i
  | .ex i A => formulaFVN A \ Set.singleton i

/-- Definition 5.2.4 (companion): Computable `List Nat` variant of
`formulaFVN`, collecting the free-variable indices of a FormulaN (with
duplicates, in traversal order). Companion of Def 5.2.4's
`termVarIndicesList` at the FormulaN layer. -/
@[blueprint "chap5__definition_5_2_4"]
def formulaFreeVarIndices {L : Language} : FormulaN L → List Nat
  | .predN P ts =>
    let indices := List.ofFn (fun (j : Fin (L.predArity P)) => j)
    indices.foldl (fun acc j => acc ++ termVarIndicesList (ts j)) []
  | .eq_ _ t1 t2 => termVarIndicesList t1 ++ termVarIndicesList t2
  | .neg A => formulaFreeVarIndices A
  | .conj A B => formulaFreeVarIndices A ++ formulaFreeVarIndices B
  | .disj A B => formulaFreeVarIndices A ++ formulaFreeVarIndices B
  | .impl A B => formulaFreeVarIndices A ++ formulaFreeVarIndices B
  | .all i A => (formulaFreeVarIndices A).filter (· != i)
  | .ex i A => (formulaFreeVarIndices A).filter (· != i)

/-- Definition 5.4.9 (companion): Computable `List (Term L)` variant
collecting the constant `Term.const` values occurring in a FormulaN.
Used by §5.4.7 TERM₀ initialization to gather the constants of the
input sequent. -/
@[blueprint "chap5__definition_5_4_9"]
def formulaConstsList {L : Language} : FormulaN L → List (Term L)
  | .predN P ts =>
    let indices := List.ofFn (fun (j : Fin (L.predArity P)) => j)
    indices.foldl (fun acc j => acc ++ termConstsList (ts j)) []
  | .eq_ _ t1 t2 => termConstsList t1 ++ termConstsList t2
  | .neg A => formulaConstsList A
  | .conj A B => formulaConstsList A ++ formulaConstsList B
  | .disj A B => formulaConstsList A ++ formulaConstsList B
  | .impl A B => formulaConstsList A ++ formulaConstsList B
  | .all _ A => formulaConstsList A
  | .ex _ A => formulaConstsList A

-- ===================================================================
-- Bound variables of FormulaN
-- ===================================================================

/-- Definition 5.2.5 (companion): The set BV(A) of bound variables of a
normalized formula A — the FormulaN-side transcription of Def 5.2.5
within the §5.3.8 grammar. -/
@[blueprint "chap5__definition_5_2_5"]
def formulaBVN {L : Language} : FormulaN L → Set Nat
  | .predN _ _ => ∅
  | .eq_ _ _ _ => ∅
  | .neg A => formulaBVN A
  | .conj A B => formulaBVN A ∪ formulaBVN B
  | .disj A B => formulaBVN A ∪ formulaBVN B
  | .impl A B => formulaBVN A ∪ formulaBVN B
  | .all i A => formulaBVN A ∪ Set.singleton i
  | .ex i A => formulaBVN A ∪ Set.singleton i

/-- Definition 5.2.5 (companion): Computable `List Nat` variant of
`formulaBVN`, collecting bound-variable indices of a FormulaN (with
duplicates). Companion to `formulaFreeVarIndices`. -/
@[blueprint "chap5__definition_5_2_5"]
def formulaBoundVarIndices {L : Language} : FormulaN L → List Nat
  | .predN _ _ => []
  | .eq_ _ _ _ => []
  | .neg A => formulaBoundVarIndices A
  | .conj A B => formulaBoundVarIndices A ++ formulaBoundVarIndices B
  | .disj A B => formulaBoundVarIndices A ++ formulaBoundVarIndices B
  | .impl A B => formulaBoundVarIndices A ++ formulaBoundVarIndices B
  | .all i A => i :: formulaBoundVarIndices A
  | .ex i A => i :: formulaBoundVarIndices A

-- ===================================================================
-- No free-bound overlap
-- ===================================================================



-- ===================================================================
-- Closed formulae and sentences
-- ===================================================================

namespace FormulaN

/-- Definition 5.2.4: A normalized formula is
closed if FV(A) = empty. -/
@[blueprint "chap5__definition_5_2_4"]
def isClosed {L : Language} (A : FormulaN L) : Prop :=
  formulaFVN A = ∅

/-- Definition 5.2.4 (companion — N variant): A sentence is a closed
formula. -/
@[blueprint "chap5__definition_5_2_4"]
abbrev isSentence {L : Language} (A : FormulaN L) : Prop :=
  isClosed A

end FormulaN

end LCS.FirstOrder.SyntaxN.Variables
