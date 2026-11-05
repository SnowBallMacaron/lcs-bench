import LCS.FirstOrder.Effective.Presentation
import Attach
import LCS.FirstOrder.Effective.Syntax.ProofsStamp

/-! # Executable finite syntax tests

Tests use structural recursion and the natural codes of presented symbols.
Argument order, binder indices, and every normalized connective are retained.
Reflection propositions are separate from the data-producing definitions.
-/

namespace LCS.FirstOrder.Effective

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.Gentzen
open LCS.FirstOrder.SyntaxN.Variables LCS.FirstOrder.SyntaxN.Substitution

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (effective companion): Decide equality of presented
symbols by equality of their natural codes. -/
def symbolDecEq {accept : Nat → Bool} (a b : {n : Nat // accept n = true}) :
    Decidable (a = b) :=
  if h : a.val = b.val then isTrue (Subtype.ext h)
  else isFalse (fun e => h (congrArg Subtype.val e))

/-- Definition 5.4.9 (effective companion): Structural equality of terms.
Equal function symbols have equal ranks; their argument tuples are compared
position by position. -/
@[blueprint "chap5__definition_5_4_9"]
def termEq {p : EffectivePresentation} : Term p.toLanguage → Term p.toLanguage → Bool
  | .var x, .var y => x == y
  | .const c, .const d => symbolEq c d
  | .func f ts, .func g us =>
    letI : DecidableEq p.toLanguage.funSymbols := symbolDecEq
    if h : f = g then
      (List.ofFn fun i => termEq (ts i) (us (Fin.cast (congrArg p.toLanguage.funArity h) i))).all id
    else false
  | _, _ => false

/-- Definition 5.4.9 (effective companion): Structural equality of normalized
formulae, including rank-zero predicates and ordered equality terms.
Quantifiers compare their binder indices as well as their bodies. -/
@[blueprint "chap5__definition_5_4_9"]
def formulaEq {p : EffectivePresentation} :
    FormulaN p.toLanguage → FormulaN p.toLanguage → Bool
  | .predN P ts, .predN Q us =>
    letI : DecidableEq p.toLanguage.predSymbols := symbolDecEq
    if h : P = Q then
      (List.ofFn fun i => termEq (ts i) (us (Fin.cast (congrArg p.toLanguage.predArity h) i))).all id
    else false
  | .eq_ _ t u, .eq_ _ v w => termEq t v && termEq u w
  | .neg A, .neg B => formulaEq A B
  | .conj A B, .conj C D
  | .disj A B, .disj C D
  | .impl A B, .impl C D => formulaEq A C && formulaEq B D
  | .all x A, .all y B
  | .ex x A, .ex y B => x == y && formulaEq A B
  | _, _ => false

/-- Definition 5.4.9 (effective companion): Test occurrence of a variable
in a term using the existing executable variable-index list. -/
@[blueprint "chap5__definition_5_2_4"]
def termVarOccurs {L : Language} (x : Nat) (t : Term L) : Bool :=
  (termVarIndicesList t).contains x

/-- Definition 5.4.9 (effective companion): Test free occurrence of a
variable in a formula; bound occurrences are removed by the index collector. -/
@[blueprint "chap5__definition_5_2_4"]
def formulaVarOccurs {L : Language} (x : Nat) (A : FormulaN L) : Bool :=
  (formulaFreeVarIndices A).contains x

/-- Definition 5.4.9 (effective companion): The finite free-for test follows
isFreeForN: at a binder y, either x=y or y is absent from t and the body
passes the recursive test. -/
@[blueprint "chap5__definition_5_2_7"]
def freeForDecide {L : Language} (t : Term L) (x : Nat) : FormulaN L → Bool
  | .predN _ _ | .eq_ _ _ _ => true
  | .neg A => freeForDecide t x A
  | .conj A B | .disj A B | .impl A B => freeForDecide t x A && freeForDecide t x B
  | .all y A | .ex y A => x == y || (!termVarOccurs y t && freeForDecide t x A)

/-- Definition 5.4.9 (effective companion): A finite sequent is an axiom
exactly when a formula on its left also occurs on its right. -/
@[blueprint "chap5__definition_5_4_1"]
def axiomDecide {p : EffectivePresentation} (s : Sequent p.toLanguage) : Bool :=
  s.antecedent.any fun A => s.succedent.any fun B => formulaEq A B

/-- The structural term test reflects term equality. -/
theorem termEq_correct {p : EffectivePresentation} (t u : Term p.toLanguage) :
    termEq t u = true ↔ t = u := by
  -- REPAIR(T149): proof pending
  sorry

/-- The structural formula test reflects normalized formula equality. -/
theorem formulaEq_correct {p : EffectivePresentation} (A B : FormulaN p.toLanguage) :
    formulaEq A B = true ↔ A = B := by
  -- REPAIR(T149): proof pending
  sorry









/-- Definition 5.4.9 (effective companion): A selected list occurrence,
with its absolute index and an order- and multiplicity-preserving decomposition. -/
@[blueprint "chap5__definition_5_4_9"]
structure OccurrenceSplit {α : Type} (xs : List α) where
  index : Nat
  «prefix» : List α
  focus : α
  suffix : List α
  prefix_length : «prefix».length = index
  recombine : xs = «prefix» ++ focus :: suffix


/-- Definition 5.4.9 (effective companion): Select the first matching
principal formula by scanning the sequent list from left to right. Interpretation
assumption D3: where the printed procedure leaves repeated occurrences
unspecified, use leftmost-outermost. Here the focus is an entire sequent formula;
its proper subformulae are not selection candidates. Duplicate formulae after
the selected occurrence remain in the suffix. -/
@[blueprint "chap5__definition_5_4_9"]
def splitOccurrence {p : EffectivePresentation} (A : FormulaN p.toLanguage) :
    (xs : List (FormulaN p.toLanguage)) → Option (OccurrenceSplit xs)
  | [] => none
  | B :: bs =>
    if formulaEq B A then
      some ⟨0, [], B, bs, rfl, rfl⟩
    else
      match splitOccurrence A bs with
      | none => none
      | some r => some ⟨r.index + 1, B :: r.prefix, r.focus, r.suffix,
          by simp [r.prefix_length], congrArg (List.cons B) r.recombine⟩

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The stored index points to the stored focused element. -/
theorem OccurrenceSplit.focus_at {α : Type} {xs : List α} (r : OccurrenceSplit xs) :
    xs[r.index]? = some r.focus := by
  rcases r with ⟨i, pre, a, post, hi, hs⟩
  simp only
  rw [← hi, hs]
  simp





/-- Definition 5.4.9 (effective companion): Read a fresh variable directly
from a supplied stream at the specified cursor. Exhaustion, a non-variable
entry, or a forbidden index returns none. The cursor is not skipped or advanced;
an admissible variable supply makes the successful case available. -/
@[blueprint "chap5__definition_5_4_9"]
def freshVariableAt {L : Language} (entries : Nat → Option (Term L))
    (cursor : Nat) (forbidden : List Nat) : Option Nat :=
  match entries cursor with
  | some (.var x) => if forbidden.contains x then none else some x
  | _ => none



end LCS.FirstOrder.Effective
