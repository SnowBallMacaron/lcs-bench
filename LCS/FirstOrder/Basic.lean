import LCS.Item
import LCS.Util
import Attach
import LCS.FirstOrder.Basic.ProofsStamp

/-! # FirstOrder.Basic
    Shared foundations for first-order logic: languages, terms, structures,
    assignments, and term-level operations. These definitions are used by
    BOTH the Formula world (§5.2–§5.3.7) and the FormulaN world (§5.3.8+).
-/

namespace LCS.FirstOrder.Basic

-- ===================================================================
-- Definition 5.2.1: First-order language
-- ===================================================================

/-- A signature (symbol sets, ranks, equality flag) without the countability and
positivity conditions; L(M) of Definition 5.3.8 is such a signature. -/
@[blueprint "chap5__definition_5_3_8"]
structure Language : Type 1 where
  funSymbols : Type
  funArity : funSymbols → Nat
  constSymbols : Type
  predSymbols : Type
  predArity : predSymbols → Nat
  hasEquality : Bool := true

/-- Definition 5.2.1: A first-order language has countable, possibly empty sets
of function, constant, and predicate symbols, with positive function arities. -/
@[blueprint "chap5__definition_5_2_1" (main := true)]
structure FirstOrderLanguage extends Language where
  funSymbols_countable : ∃ e : funSymbols → Nat, Function.Injective e
  constSymbols_countable : ∃ e : constSymbols → Nat, Function.Injective e
  predSymbols_countable : ∃ e : predSymbols → Nat, Function.Injective e
  funArity_pos : ∀ f, 0 < funArity f

namespace Language

/-- Definition 5.2.1 (companion): A first-order language without equality. -/
@[blueprint "chap5__definition_5_2_1"]
def withoutEquality (L : Language) : Prop :=
  L.hasEquality = false

end Language

-- ===================================================================
-- Definition 5.2.2: Terms
-- ===================================================================

/-- Definition 5.2.2: The set TERM_L of L-terms is the inductive closure of
the union of the variables V and constants CS under the function-symbol constructors C_f. A term is either a variable x_i, a constant c, or a function application f(t_1,...,t_n) of a function symbol f of rank n to terms t_1,...,t_n. -/
@[blueprint "chap5__definition_5_2_2" (main := true)]
inductive Term (L : Language) : Type where
  | var : Nat → Term L
  | const : L.constSymbols → Term L
  | func : (f : L.funSymbols) → (Fin (L.funArity f) → Term L) → Term L

/-- Definition 5.2.2 (required helper): classical `DecidableEq` for `Term L`,
used by `LCS.Finset.insert`/`erase` and other tactic-level reasoning on terms. -/
noncomputable instance instDecidableEqTerm : DecidableEq (Term L) :=
  fun a b => Classical.propDecidable (a = b)

-- ===================================================================
-- Helpers: vec1, vec2
-- ===================================================================

-- retained: used by LCS.CutElim.Beth.Part2, LCS.FirstOrder.Equality.MetaTheorems, LCS.FirstOrder.Semantics, LCS.FirstOrder.Syntax, LCS.SLD.LogicProgramming
/-- Example 5.2.1 (companion): helper for building a 1-argument `Fin`-indexed
vector from a single element, used to encode unary function applications
in textbook example terms. -/
def vec1 (a : α) : Fin 1 → α
  | ⟨0, _⟩ => a

/-- Example 5.2.1 (companion): helper for building a 2-argument `Fin`-indexed
vector, used to encode binary function/predicate applications. -/
@[blueprint "chap5__example_5_2_1"]
def vec2 (a b : α) : Fin 2 → α
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b

-- ===================================================================
-- Term free variables
-- ===================================================================

/-- Definition 5.2.4: Given a term t, the set FV(t) of free variables of t
is defined by recursion: FV(x_i) = {x_i}, FV(c) = empty, and FV(f(t_1,...,t_n)) = FV(t_1) union ... union FV(t_n). -/
@[blueprint "chap5__definition_5_2_4" (main := true)]
def termFV {L : Language} : Term L → Set Nat
  | .var i => Set.singleton i
  | .const _ => ∅
  | .func f ts => Set.iUnion (fun (j : Fin (L.funArity f)) => termFV (ts j))

/-- Definition 5.2.4 (companion): Computable `List Nat` variant of `termFV`,
collecting the variable indices occurring in a term (with duplicates).
Used wherever FV needs to be enumerated rather than reasoned about as a
set. -/
@[blueprint "chap5__definition_5_2_4"]
def termVarIndicesList {L : Language} : Term L → List Nat
  | .var i => [i]
  | .const _ => []
  | .func f ts =>
    let indices := List.ofFn (fun (j : Fin (L.funArity f)) => j)
    indices.foldl (fun acc j => acc ++ termVarIndicesList (ts j)) []

/-- Definition 5.4.9 (companion): Collect the constant `Term.const`
values occurring in a term, with duplicates. Used by §5.4.7 TERM₀
initialization to gather the constants of an input sequent. -/
@[blueprint "chap5__definition_5_4_9"]
def termConstsList {L : Language} : Term L → List (Term L)
  | .var _ => []
  | .const c => [.const c]
  | .func f ts =>
    let indices := List.ofFn (fun (j : Fin (L.funArity f)) => j)
    indices.foldl (fun acc j => acc ++ termConstsList (ts j)) []

namespace Term

/-- Definition 5.2.4 (companion): A term t is closed if FV(t) = empty. -/
@[blueprint "chap5__definition_5_2_4" (main := true)]
def isClosed {L : Language} (t : Term L) : Prop :=
  termFV t = ∅

end Term

-- ===================================================================
-- Term substitution
-- ===================================================================

/-- Definition 5.2.6: The result of substituting a term t for a variable x
in a term s, denoted s[t/x], defined by recursion: x_i[t/x] = t if i = x otherwise x_i, c[t/x] = c, and f(t_1,...,t_n)[t/x] = f(t_1[t/x],...,t_n[t/x]). -/
@[blueprint "chap5__definition_5_2_6" (main := true)]
def termSubst {L : Language} : Term L → Term L → Nat → Term L
  | .var i, t, x => if i = x then t else .var i
  | .const c, _, _ => .const c
  | .func f ts, t, x => .func f (fun i => termSubst (ts i) t x)

-- retained: used by LCS.FirstOrder.SyntaxN.Substitution
/-- Substituting var x for x in a term is the identity. -/
theorem termSubst_var_self {L : Language} (t : Term L) (x : Nat) :
    termSubst t (Term.var x) x = t := by
-- BEGIN PROOF
  induction t with
  | var n => simp [termSubst]; omega
  | const c => simp [termSubst]
  | func f ts ih => simp [termSubst]; ext i; exact ih i

-- ===================================================================
-- Structures, assignments, term evaluation
-- ===================================================================

/-- Definition 5.3.1: Given a first-order language L, an L-structure M is a
pair (M, I) where M is a nonempty set (the domain) and I is the interpretation function assigning: a function M^n -> M to every rank-n function symbol, an element of M to every constant, and a predicate M^n -> Prop to every rank-n predicate symbol. -/
@[blueprint "chap5__definition_5_3_1" (main := true)]
structure Structure (L : Language) : Type 1 where
  carrier : Type
  carrierNonempty : Nonempty carrier
  interpFunc : (f : L.funSymbols) → (Fin (L.funArity f) → carrier) → carrier
  interpConst : L.constSymbols → carrier
  interpPred : (P : L.predSymbols) → (Fin (L.predArity P) → carrier) → Prop

/-- Definition 5.3.2: An assignment is any function s : V -> M from the set
of variables V to the carrier M of a structure. The set of all such functions is denoted [V -> M]. -/
@[blueprint "chap5__definition_5_3_2" (main := true)]
abbrev Assignment {L : Language} (M : Structure L) : Type :=
  Nat → M.carrier

/-- Definition 5.3.3: Given an assignment s : V -> M, an
element a in M, and a variable index i, the updated assignment
s[x_i := a] agrees with s everywhere except at x_i, where it takes
the value a. -/
@[blueprint "chap5__definition_5_3_3" (main := true)]
def assignUpdate {L : Language} {M : Structure L}
    (s : Assignment M) (i : Nat) (a : M.carrier) : Assignment M :=
  fun j => if j = i then a else s j

/-- Definition 5.3.3 (companion): Universal quantification of a truth-value
function at variable x_i ranges over every value assigned to that variable. -/
@[blueprint "chap5__definition_5_3_3" (main := true)]
def forallM {L : Language} (M : Structure L) (i : Nat)
    (f : Assignment M → Prop) : Assignment M → Prop :=
  fun s => ∀ a : M.carrier, f (assignUpdate s i a)

/-- Definition 5.3.3 (companion): Existential quantification of a truth-value
function at variable x_i holds for some value assigned to that variable. -/
@[blueprint "chap5__definition_5_3_3" (main := true)]
def existsM {L : Language} (M : Structure L) (i : Nat)
    (f : Assignment M → Prop) : Assignment M → Prop :=
  fun s => ∃ a : M.carrier, f (assignUpdate s i a)

/-- Definition 5.3.4: The lifted Boolean connective ∧_M on truth-value
functions `[V → M] → Prop`. For `f, g : Assignment M → Prop`, the pointwise
conjunction `andM f g s` holds iff both `f s` and `g s` hold. -/
@[simp, blueprint "chap5__definition_5_3_4" (main := true)]
def andM {L : Language} {M : Structure L}
    (f g : Assignment M → Prop) : Assignment M → Prop :=
  fun s => f s ∧ g s

/-- Definition 5.3.4 (companion): The lifted Boolean connective ∨_M.
Pointwise `or` of two truth-value functions. -/
@[simp, blueprint "chap5__definition_5_3_4" (main := true)]
def orM {L : Language} {M : Structure L}
    (f g : Assignment M → Prop) : Assignment M → Prop :=
  fun s => f s ∨ g s

/-- Definition 5.3.4 (companion): The lifted Boolean connective ⊃_M.
Pointwise `implies` of two truth-value functions. -/
@[simp, blueprint "chap5__definition_5_3_4" (main := true)]
def implM {L : Language} {M : Structure L}
    (f g : Assignment M → Prop) : Assignment M → Prop :=
  fun s => f s → g s

/-- Definition 5.3.4 (companion): The lifted Boolean connective ≡_M.
Pointwise `iff` of two truth-value functions. -/
@[simp, blueprint "chap5__definition_5_3_4" (main := true)]
def equivM {L : Language} {M : Structure L}
    (f g : Assignment M → Prop) : Assignment M → Prop :=
  fun s => f s ↔ g s

/-- Definition 5.3.4 (companion): The lifted Boolean connective ¬_M.
Pointwise negation of a truth-value function. -/
@[simp, blueprint "chap5__definition_5_3_4" (main := true)]
def negM {L : Language} {M : Structure L}
    (f : Assignment M → Prop) : Assignment M → Prop :=
  fun s => ¬ f s

/-- Definition 5.3.5: The function
t_M : [V -> M] -> M defined by a term t. For an assignment s and term t,
evaluates recursively: variables by s, constants by the interpretation
function, and function symbols by applying the interpretation function
to the recursively evaluated arguments. -/
@[blueprint "chap5__definition_5_3_5" (main := true)]
def termEval {L : Language} (M : Structure L)
    (s : Assignment M) : Term L → M.carrier
  | .var i => s i
  | .const c => M.interpConst c
  | .func f ts => M.interpFunc f (fun i => termEval M s (ts i))

-- ===================================================================
-- Definition 5.3.8: Extended language L(M) with naming constants
-- ===================================================================

/-- Definition 5.3.8: Given a language L and a structure M, the extended
language L(M) is obtained by adjoining a naming constant for each element of M's domain. -/
@[blueprint "chap5__definition_5_3_8" (main := true)]
def extendedLanguage (L : Language) (M : Type) : Language where
  funSymbols := L.funSymbols
  funArity := L.funArity
  constSymbols := L.constSymbols ⊕ M
  predSymbols := L.predSymbols
  predArity := L.predArity
  hasEquality := L.hasEquality

/-- Definition 5.3.8 (companion): Naming constant for element m. -/
@[blueprint "chap5__definition_5_3_8"]
def namingConst {L : Language} {M : Type} (m : M) :
    Term (extendedLanguage L M) :=
  Term.const (Sum.inr m)

/-- Definition 5.3.8 (companion): Extended interpretation — original
constants interpreted as before, naming constants m interpreted as m. -/
@[blueprint "chap5__definition_5_3_8" (main := true)]
def extendedInterp {L : Language} (S : Structure L) :
    Structure (extendedLanguage L S.carrier) where
  carrier := S.carrier
  carrierNonempty := S.carrierNonempty
  interpFunc := S.interpFunc
  interpConst
    | Sum.inl c => S.interpConst c
    | Sum.inr m => m
  interpPred := S.interpPred

/-- Definition 5.3.8 (companion): For any assignment s, the evaluation
of naming constant m yields m itself: (m)_M[s] = m. -/
@[blueprint "chap5__definition_5_3_8"]
theorem namingConstEval {L : Language} (S : Structure L)
    (s : Assignment (extendedInterp S)) (m : S.carrier) :
    termEval (extendedInterp S) s (namingConst m) = m 

end LCS.FirstOrder.Basic
