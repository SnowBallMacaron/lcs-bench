import LCS.Item
import LCS.Util
import Attach
import LCS.FirstOrder.ManySorted.ProofsStamp

/-! # FirstOrder.ManySorted
    Formalization of Chapter 10, Section 10.2.

    Many-sorted first-order languages: alphabets (Def 10.2.1), terms and
    formulae (Def 10.2.2), the stack-language example (Example 10.2.1,
    10.2.2), free generation (Theorem 10.2.1), and free/bound variables
    with substitution (§10.2.3).

    Source: Logic for Computer Science, Gallier 2015.
-/

namespace LCS.FirstOrder.ManySorted

-- ===================================================================
-- Definition 10.2.1: Many-sorted first-order language
-- ===================================================================

-- ATTACH-BLOCKER: unsupported untagged structure
/-- A general many-sorted signature with nonempty data sorts and positive
function ranks. It permits arbitrary symbol carriers, including the names
for all elements of a structure in the semantic expansion L(M). -/
@[blueprint "chap10__definition_10_2_1"]
structure MSLanguage : Type 1 where
  SortType : Type
  /-- Def 10.2.1 constraint: `S` is nonempty. A witness sort. -/
  someSort : SortType
  funSymbols : Type
  funRank : funSymbols → (List SortType) × SortType
  /-- Def 10.2.1 (i) constraint: the arity string u of every function
      symbol is in S^+ (nonempty). 0-ary symbols belong to CS, not FS. -/
  funRank_nonempty : ∀ f, (funRank f).1 ≠ []
  constSymbols : SortType → Type
  predSymbols : Type
  predArity : predSymbols → List SortType
  hasEquality : Bool := true

/-- Definition 10.2.1: The alphabet of a many-sorted first-order language.

A countable set of non-bool sorts `SortType` (S in the textbook; bool is
modelled implicitly by `MSFormula`). Fixed logical symbols (∧, ∨, ⊃, ≡,
¬, ⊥, ∀_s, ∃_s, =̇_s) and auxiliary parentheses are part of every
language. The variable family V_s is also fixed: countably infinite
(represented by `Nat`) for each sort s.

The non-logical symbols are:
(i)   Function symbols `funSymbols` with rank function
      `funRank : funSymbols → (List SortType) × SortType`, where the first
      component is the arity u = u_1…u_n ∈ S^+ and the second is the
      output sort s ∈ S.
(ii)  Constants `constSymbols`, a family indexed by sort s giving the
      set CS_s of constants of rank (e, s).
(iii) Predicate symbols `predSymbols` with arity function
      `predArity : predSymbols → List SortType` (u ∈ S^*; output is always
      bool). An empty arity makes the predicate a propositional letter.

The flag `hasEquality` toggles whether the equality symbols =̇_s are
in the alphabet (Section 10.5 uses G_= with equality; Section 10.4
uses G without). The `MSFormula.eq_` constructor carries a proof
`hasEquality = true`, so when `hasEquality = false` the constructor
is uninhabited — faithfully realizing the textbook's "languages
obtained by omitting the equality symbol".

Countability is witnessed by injections into `Nat` for the data sorts,
function symbols, each constant fiber, and predicate symbols. The symbol
carriers may be empty. This uses the countable source-language reading of
Definition 10.2.1 and the rank domains of Definition 5.2.1.

Structural guarantees:
  * `S` nonempty: the field `someSort : SortType` supplies a witness.
  * `bool ∉ S`: the textbook's distinguished bool sort is realized by
    `MSFormula L` (a Lean type distinct from the carrier of any
    `s : SortType`, which is `MSTerm L s`). There is therefore no
    element of `SortType` that IS the bool sort; any user-named
    element of `SortType` is always a non-bool sort, regardless of
    what string it is named. -/
@[blueprint "chap10__definition_10_2_1" (main := true)]
structure MSFirstOrderLanguage extends MSLanguage where
  sortCode : SortType → Nat
  sortCode_injective : Function.Injective sortCode
  funCode : funSymbols → Nat
  funCode_injective : Function.Injective funCode
  constCode : (s : SortType) → constSymbols s → Nat
  constCode_injective : ∀ s, Function.Injective (constCode s)
  predCode : predSymbols → Nat
  predCode_injective : Function.Injective predCode

namespace MSLanguage

/-- Definition 10.2.1 (companion): A many-sorted first-order language
without equality — the equality symbols =̇_s are omitted. -/
@[blueprint "chap10__definition_10_2_1"]
def withoutEquality (L : MSLanguage) : Prop :=
  L.hasEquality = false

end MSLanguage

/-- Definition 10.2.1 (companion): A many-sorted variable is identified by
its sort s ∈ S and its index i ∈ ℕ, i.e. the textbook variable x_i of
sort s (written x_i^s or x_i : s). The family V = (V_s)_{s ∈ S} of
variables is thus `MSVar L = L.SortType × Nat`. -/
@[blueprint "chap10__definition_10_2_1"]
abbrev MSVar (L : MSLanguage) : Type := L.SortType × Nat

/-- Definition 10.2.1 (required helper): classical `DecidableEq` for
`MSVar L`, needed to phrase `FV(A) \ {(s, i)}` in the quantifier
clauses of `msFormulaFV` via `Set.singleton`. -/
@[blueprint "chap10__definition_10_2_1"]
noncomputable instance instDecidableEqMSVar (L : MSLanguage) :
    DecidableEq (MSVar L) :=
  fun a b => Classical.propDecidable (a = b)

-- ===================================================================
-- Definition 10.2.2: Many-sorted terms and formulae
-- ===================================================================

/-- Definition 10.2.2 (companion): The family TERM_L of L-terms is the carrier of
sort s ∈ S of the least subalgebra of the string algebra T(L, V)
containing the V-indexed family of variables. Informally (§10.2.2's
"less formal" restatement):

(i)  Every constant of sort s and every variable of sort s is a term
     of sort s.
(ii) If t_1,…,t_n are terms, each t_i of sort u_i, and f is a function
     symbol of rank (u_1…u_n, s), then f(t_1,…,t_n) is a term of sort s.

Terms are sort-indexed: `MSTerm L s` is the set TERM^s_L. -/
@[blueprint "chap10__definition_10_2_2"]
inductive MSTerm (L : MSLanguage) : L.SortType → Type where
  /-- A variable x_i of sort s is a term of sort s. -/
  | var : (s : L.SortType) → Nat → MSTerm L s
  /-- A constant of sort s is a term of sort s. -/
  | const : (s : L.SortType) → L.constSymbols s → MSTerm L s
  /-- For a function symbol f of rank (u_1…u_n, s) and terms t_i each
      of sort u_i, f(t_1,…,t_n) is a term of sort s. -/
  | func : (f : L.funSymbols) →
      ((i : Fin (L.funRank f).1.length) → MSTerm L ((L.funRank f).1.get i)) →
      MSTerm L (L.funRank f).2

/-- Definition 10.2.2 (companion): The set FORM_L of L-formulae is the carrier of
sort bool of the least subalgebra T(L, V). Informally:

(iii)  Every propositional letter (predicate symbol of empty arity) is
       an atomic formula, and so is ⊥.
(iv)   For a predicate symbol P of arity u_1…u_n and terms t_i of sort
       u_i, P(t_1,…,t_n) is an atomic formula. For terms t_1, t_2 of
       sort s, (t_1 =̇_s t_2) is an atomic formula.
(v)    Every atomic formula is a formula.
(vi)   For formulae A and B, (A ∧ B), (A ∨ B), (A ⊃ B), (A ≡ B) and ¬A
       are formulae.
(vii)  For any variable x_i of sort s and formula A, ∀_s x_i A and
       ∃_s x_i A are formulae. -/
@[blueprint "chap10__definition_10_2_2"]
inductive MSFormula (L : MSLanguage) : Type where
  /-- Falsum ⊥ of rank (e, bool). -/
  | falsum : MSFormula L
  /-- For a predicate symbol P of arity u_1…u_n and terms t_i each of
      sort u_i, P(t_1,…,t_n) is an atomic formula. When u is empty
      (n = 0), this encodes a propositional letter P (Def 10.2.1's
      "u = e" case). -/
  | pred : (P : L.predSymbols) →
      ((i : Fin (L.predArity P).length) → MSTerm L ((L.predArity P).get i)) →
      MSFormula L
  /-- For terms t_1, t_2 of sort s, (t_1 =̇_s t_2) is an atomic
      formula. Only available when `L.hasEquality = true`; the proof
      argument makes the constructor uninhabited for without-equality
      languages (Def 10.2.1: "omitting the equality symbol"). -/
  | eq_ : L.hasEquality = true →
      (s : L.SortType) → MSTerm L s → MSTerm L s → MSFormula L
  /-- Conjunction (A ∧ B). -/
  | conj : MSFormula L → MSFormula L → MSFormula L
  /-- Disjunction (A ∨ B). -/
  | disj : MSFormula L → MSFormula L → MSFormula L
  /-- Implication (A ⊃ B). -/
  | impl : MSFormula L → MSFormula L → MSFormula L
  /-- Equivalence (A ≡ B). -/
  | equiv_ : MSFormula L → MSFormula L → MSFormula L
  /-- Negation ¬A. -/
  | neg : MSFormula L → MSFormula L
  /-- Universal quantifier ∀_s x_i A. -/
  | all : (s : L.SortType) → Nat → MSFormula L → MSFormula L
  /-- Existential quantifier ∃_s x_i A. -/
  | ex : (s : L.SortType) → Nat → MSFormula L → MSFormula L

namespace MSFormula

/-- Definition 10.2.2 (companion): A many-sorted formula is atomic if it
is falsum, a predicate application (including propositional letters
when the predicate has empty arity), or an equality. -/
@[blueprint "chap10__definition_10_2_2"]
def isAtomic {L : MSLanguage} : MSFormula L → Prop
  | .falsum => True
  | .pred _ _ => True
  | .eq_ _ _ _ _ => True
  | _ => False

end MSFormula

-- ===================================================================
-- Example 10.2.1: Many-sorted language of stacks
-- ===================================================================

/-- Example 10.2.1 (companion): The sorts S = {stack, integer} for the
stack-language example. -/
@[blueprint "chap10__example_10_2_1"]
inductive StackSort : Type where
  | stack : StackSort
  | integer : StackSort

/-- Example 10.2.1 (companion): Function symbols FS for the stack
language — Succ : integer → integer, + and * : integer×integer →
integer, push : stack×integer → stack, pop : stack → stack, top :
stack → integer. -/
@[blueprint "chap10__example_10_2_1"]
inductive StackFunc : Type where
  | Succ : StackFunc
  | plus : StackFunc
  | times : StackFunc
  | push : StackFunc
  | pop : StackFunc
  | top : StackFunc

/-- Example 10.2.1 (companion): Constants of sort integer — just 0
(CS_integer = {0}). -/
@[blueprint "chap10__example_10_2_1"]
inductive IntegerConst : Type where
  | zero : IntegerConst

/-- Example 10.2.1 (companion): Constants of sort stack — just Λ (the
empty stack; CS_stack = {Λ}). -/
@[blueprint "chap10__example_10_2_1"]
inductive StackConst : Type where
  | empty : StackConst

/-- Example 10.2.1 (companion): Predicate symbols PS for the stack
language — just < (comparison on integers). -/
@[blueprint "chap10__example_10_2_1"]
inductive StackPred : Type where
  | lt : StackPred

/-- Example 10.2.1: The many-sorted language L for stacks, with
S = {stack, integer}, CS_integer = {0}, CS_stack = {Λ},
FS = {Succ, +, *, push, pop, top}, PS = {<}.

The rank functions are:
  r(Succ) = (integer, integer);
  r(+) = r(*) = (integer.integer, integer);
  r(push) = (stack.integer, stack);
  r(pop) = (stack, stack);
  r(top) = (stack, integer);
  r(<) = (integer.integer, bool). -/
@[blueprint "chap10__example_10_2_1" (main := true)]
def stackLanguage : MSLanguage where
  SortType := StackSort
  someSort := StackSort.integer
  funSymbols := StackFunc
  funRank
    | .Succ  => ([StackSort.integer], StackSort.integer)
    | .plus  => ([StackSort.integer, StackSort.integer], StackSort.integer)
    | .times => ([StackSort.integer, StackSort.integer], StackSort.integer)
    | .push  => ([StackSort.stack, StackSort.integer], StackSort.stack)
    | .pop   => ([StackSort.stack], StackSort.stack)
    | .top   => ([StackSort.stack], StackSort.integer)
  funRank_nonempty := fun f => by cases f <;> decide
  constSymbols
    | .integer => IntegerConst
    | .stack   => StackConst
  predSymbols := StackPred
  predArity
    | .lt => [StackSort.integer, StackSort.integer]

/-- Example 10.2.1 (companion): Helper for building the argument vector
of the unary stack-language function `Succ`: its arity is `[integer]`,
so there is exactly one argument (of sort integer). -/
@[blueprint "chap10__example_10_2_1"]
def stackSuccArg (t : MSTerm stackLanguage StackSort.integer) :
    (i : Fin (stackLanguage.funRank StackFunc.Succ).1.length) →
      MSTerm stackLanguage ((stackLanguage.funRank StackFunc.Succ).1.get i)
  | ⟨0, _⟩ => t

/-- Example 10.2.1 (companion): Helper for building the argument vector
of the unary stack-language function `top`: its arity is `[stack]`. -/
@[blueprint "chap10__example_10_2_1"]
def stackTopArg (t : MSTerm stackLanguage StackSort.stack) :
    (i : Fin (stackLanguage.funRank StackFunc.top).1.length) →
      MSTerm stackLanguage ((stackLanguage.funRank StackFunc.top).1.get i)
  | ⟨0, _⟩ => t

/-- Example 10.2.1 (companion): Helper for building the argument vector
of the unary stack-language function `pop`: its arity is `[stack]`. -/
@[blueprint "chap10__example_10_2_1"]
def stackPopArg (t : MSTerm stackLanguage StackSort.stack) :
    (i : Fin (stackLanguage.funRank StackFunc.pop).1.length) →
      MSTerm stackLanguage ((stackLanguage.funRank StackFunc.pop).1.get i)
  | ⟨0, _⟩ => t

/-- Example 10.2.1 (companion): Helper for building the argument vector
of the binary stack-language function `push`: its arity is
`[stack, integer]`, so there are two arguments. -/
@[blueprint "chap10__example_10_2_1"]
def stackPushArgs (s : MSTerm stackLanguage StackSort.stack)
    (i_ : MSTerm stackLanguage StackSort.integer) :
    (i : Fin (stackLanguage.funRank StackFunc.push).1.length) →
      MSTerm stackLanguage ((stackLanguage.funRank StackFunc.push).1.get i)
  | ⟨0, _⟩ => s
  | ⟨1, _⟩ => i_

/-- Example 10.2.1 (companion): Helper for building the argument vector
of the binary stack-language predicate `<`: its arity is
`[integer, integer]`. -/
@[blueprint "chap10__example_10_2_1"]
def stackLtArgs (a b : MSTerm stackLanguage StackSort.integer) :
    (i : Fin (stackLanguage.predArity StackPred.lt).length) →
      MSTerm stackLanguage ((stackLanguage.predArity StackPred.lt).get i)
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b

/-- Example 10.2.1: The term `Succ 0` of sort integer in the stack
language — unary function applied to the unique constant of sort
integer. -/
@[blueprint "chap10__example_10_2_1" (main := true)]
def stackTerm_Succ0 : MSTerm stackLanguage StackSort.integer :=
  MSTerm.func (L := stackLanguage) StackFunc.Succ
    (stackSuccArg (MSTerm.const (L := stackLanguage) StackSort.integer IntegerConst.zero))

/-- Example 10.2.1: The term `top(push(Λ, Succ 0))` — in the textbook's
prefix notation, `top push Λ Succ 0`. Applies the `top` function to
the result of pushing `Succ 0` onto the empty stack Λ, giving an
integer. -/
@[blueprint "chap10__example_10_2_1" (main := true)]
def stackTerm_top_push : MSTerm stackLanguage StackSort.integer :=
  MSTerm.func (L := stackLanguage) StackFunc.top
    (stackTopArg (MSTerm.func (L := stackLanguage) StackFunc.push
      (stackPushArgs
        (MSTerm.const (L := stackLanguage) StackSort.stack StackConst.empty)
        stackTerm_Succ0)))

-- ===================================================================
-- Example 10.2.2: Formulae in the stack language
-- ===================================================================

/-- Example 10.2.2: The atomic formula `< 0 Succ 0`, i.e. `0 < Succ 0`. -/
@[blueprint "chap10__example_10_2_2" (main := true)]
def stackFormula_lt_0_Succ0 : MSFormula stackLanguage :=
  MSFormula.pred (L := stackLanguage) StackPred.lt
    (stackLtArgs (MSTerm.const (L := stackLanguage) StackSort.integer IntegerConst.zero)
                 stackTerm_Succ0)

/-- Example 10.2.2: The stack axiom

  ∀_integer x ∀_stack y  (pop (push y x) =̇_stack y),

which in the textbook's prefix notation is
  `∀_integer x ∀_stack y =̇_stack pop push y x y`.
Here x is the integer variable of index 0 and y is the stack variable
of index 0 (distinct because they have different sorts). -/
@[blueprint "chap10__example_10_2_2" (main := true)]
def stackFormula_stack_axiom : MSFormula stackLanguage :=
  MSFormula.all (L := stackLanguage) StackSort.integer 0
    (MSFormula.all (L := stackLanguage) StackSort.stack 0
      (MSFormula.eq_ (L := stackLanguage) rfl StackSort.stack
        (MSTerm.func (L := stackLanguage) StackFunc.pop
          (stackPopArg (MSTerm.func (L := stackLanguage) StackFunc.push
            (stackPushArgs
              (MSTerm.var (L := stackLanguage) StackSort.stack 0)
              (MSTerm.var (L := stackLanguage) StackSort.integer 0)))))
        (MSTerm.var (L := stackLanguage) StackSort.stack 0)))

-- ===================================================================
-- Theorem 10.2.1: Free generation of terms and formulae
-- ===================================================================

-- retained: used by LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.Encoding
/-- Theorem 10.2.1 (required helper): Structural size of a many-sorted
term counting all subterms, so that `ts i` has strictly smaller size
than `MSTerm.func f ts`. Needed because Lean's auto-derived `SizeOf`
for `Fin n → MSTerm L ·` defaults to 1 and does not see into the
arguments. -/
def msTermSize {L : MSLanguage} : {s : L.SortType} → MSTerm L s → Nat
  | _, .var _ _     => 1
  | _, .const _ _   => 1
  | _, .func f ts   =>
    1 + (List.ofFn (fun i => msTermSize (ts i))).foldl (· + ·) 0

-- retained: used by LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.Encoding
/-- Theorem 10.2.1 (required helper): folding addition is monotone in the
initial value — an equivalent "shift" lemma used to bound individual
`ts i` below the sum. -/
theorem msTermSize_foldl_shift (l : List Nat) (init : Nat) :
    l.foldl (· + ·) init = init + l.foldl (· + ·) 0 := by
-- BEGIN PROOF
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp [List.foldl_cons]
    rw [ih (init + x), ih x]; omega

-- retained: used by LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.Encoding
/-- Theorem 10.2.1 (required helper): every summand in a size fold is
bounded by the fold. Specialized to `ofFn` of `msTermSize (ts i)` to
get `msTermSize (ts i) ≤ Σ_j msTermSize (ts j)`. -/
theorem msTermSize_foldl_ofFn_ge_elem {L : MSLanguage} {n : Nat}
    (sorts : Fin n → L.SortType)
    (ts : (i : Fin n) → MSTerm L (sorts i)) (i : Fin n) :
    msTermSize (ts i) ≤
      (List.ofFn (fun j => msTermSize (ts j))).foldl (· + ·) 0 := by
-- BEGIN PROOF
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [List.ofFn_succ, List.foldl_cons, msTermSize_foldl_shift]
    by_cases hi : i.val = 0
    · have heq : i = (0 : Fin (n + 1)) := Fin.ext hi
      rw [heq]; omega
    · have hpos : 0 < i.val := Nat.pos_of_ne_zero hi
      have hlt : i.val - 1 < n := by omega
      let j : Fin n := ⟨i.val - 1, hlt⟩
      have heq : i = Fin.succ j := Fin.ext (by simp [j]; omega)
      rw [heq]
      have h := ih (fun k => sorts k.succ) (fun k => ts k.succ) j
      omega

-- ===================================================================
-- Section 10.2.3: Free and Bound Variables, Substitutions
-- ===================================================================
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- §10.2.3: The set FV(t) of free variables of a many-sorted term t of
sort s. Extends Definition 5.2.4 to the many-sorted case — each free
variable carries its sort, so FV(t) ⊆ V = ⋃_s V_s is represented as a
set of (sort, index) pairs. §10.2.3 states these definitions extend
from Chapter 5; no new textbook item is introduced, so this decl
carries no `lcsitem` tag. -/
@[blueprint "chap10__definition_10_2_2"]
def msTermFV {L : MSLanguage} :
    {s : L.SortType} → MSTerm L s → Set (MSVar L)
  | s, .var _ i      => Set.singleton (s, i)
  | _, .const _ _    => ∅
  | _, .func _ ts    =>
    Set.iUnion (fun i => msTermFV (ts i))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- §10.2.3: The set FV(A) of free variables of a many-sorted formula A.
Extends Definition 5.2.4; quantifier cases remove the bound variable
(with its sort) from the subformula's free-variable set. -/
@[blueprint "chap10__definition_10_2_2"]
def msFormulaFV {L : MSLanguage} : MSFormula L → Set (MSVar L)
  | .falsum         => ∅
  | .pred P ts      =>
    Set.iUnion (fun (i : Fin (L.predArity P).length) => msTermFV (ts i))
  | .eq_ _ _ t1 t2  => msTermFV t1 ∪ msTermFV t2
  | .conj A B       => msFormulaFV A ∪ msFormulaFV B
  | .disj A B       => msFormulaFV A ∪ msFormulaFV B
  | .impl A B       => msFormulaFV A ∪ msFormulaFV B
  | .equiv_ A B     => msFormulaFV A ∪ msFormulaFV B
  | .neg A          => msFormulaFV A
  | .all s i A      => msFormulaFV A \ Set.singleton (s, i)
  | .ex s i A       => msFormulaFV A \ Set.singleton (s, i)

namespace MSFormula

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- §10.2.3: A many-sorted formula A is closed if FV(A) = ∅. -/
def isClosed {L : MSLanguage} (A : MSFormula L) : Prop :=
  msFormulaFV A = ∅

-- retained: used by LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.HerbrandSatisfaction, LCS.Propositional.Infinite.SignedFormulae.Proofs
/-- §10.2.3: A many-sorted formula is open if it contains no
quantifiers. -/
@[blueprint "chap10__definition_10_2_2"]
def isOpen {L : MSLanguage} : MSFormula L → Prop
  | .falsum         => True
  | .pred _ _       => True
  | .eq_ _ _ _ _    => True
  | .neg A          => isOpen A
  | .conj A B       => isOpen A ∧ isOpen B
  | .disj A B       => isOpen A ∧ isOpen B
  | .impl A B       => isOpen A ∧ isOpen B
  | .equiv_ A B     => isOpen A ∧ isOpen B
  | .all _ _ _      => False
  | .ex _ _ _       => False

end MSFormula

-- retained: used by LCS.FirstOrder.ManySorted.Semantics
/-- §10.2.3: The set BV(A) of bound variables of a many-sorted formula.
Extends Definition 5.2.5; only quantifiers contribute bound variables,
each tagged with its sort. -/
def msFormulaBV {L : MSLanguage} : MSFormula L → Set (MSVar L)
  | .falsum         => ∅
  | .pred _ _       => ∅
  | .eq_ _ _ _ _    => ∅
  | .neg A          => msFormulaBV A
  | .conj A B       => msFormulaBV A ∪ msFormulaBV B
  | .disj A B       => msFormulaBV A ∪ msFormulaBV B
  | .impl A B       => msFormulaBV A ∪ msFormulaBV B
  | .equiv_ A B     => msFormulaBV A ∪ msFormulaBV B
  | .all s i A      => msFormulaBV A ∪ Set.singleton (s, i)
  | .ex s i A       => msFormulaBV A ∪ Set.singleton (s, i)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- §10.2.3: Substitution of a term t of sort u for the variable x_i^u in
a term of sort s. Extends Definition 5.2.6; the textbook imposes that
the sort of t must match the sort of the replaced variable — this is
encoded statically by the `MSTerm L u` typing of the replacement term.
When recursing across sorts, a variable x_i^s with s ≠ u is left
untouched. -/
@[blueprint "chap10__definition_10_2_2"]
def msTermSubst {L : MSLanguage} [DecidableEq L.SortType]
    (u : L.SortType) (x : Nat) (t : MSTerm L u) :
    {s : L.SortType} → MSTerm L s → MSTerm L s
  | _, .var s i =>
      if h : s = u then
        if i = x then h.symm ▸ t else MSTerm.var s i
      else MSTerm.var s i
  | _, .const s c => MSTerm.const s c
  | _, .func f ts =>
      MSTerm.func f (fun i => msTermSubst u x t (ts i))

-- retained: used by LCS.FirstOrder.ManySorted.Gentzen.Calculus, LCS.FirstOrder.ManySorted.Semantics
/-- §10.2.3: A term t of sort u is free for variable x_i^u in a
many-sorted formula A if no free occurrence of x_i^u in A lies within
the scope of a quantifier ∀_s' y_j or ∃_s' y_j such that (s', j) is a
free variable of t. Extends Definition 5.2.7 to the many-sorted case:
the quantifier clause becomes `(u, x) = (s, i) ∨ ((s, i) ∉ FV(t) ∧ …)`,
exactly matching Ch5's `isFreeFor` but with (sort, index) pairs in
place of plain Nat indices. -/
@[blueprint "chap10__definition_10_2_2"]
def msIsFreeFor {L : MSLanguage} :
    MSFormula L → (u : L.SortType) → Nat → MSTerm L u → Prop
  | .falsum,       _, _, _ => True
  | .pred _ _,     _, _, _ => True
  | .eq_ _ _ _ _,  _, _, _ => True
  | .neg A,        u, x, t => msIsFreeFor A u x t
  | .conj A B,     u, x, t => msIsFreeFor A u x t ∧ msIsFreeFor B u x t
  | .disj A B,     u, x, t => msIsFreeFor A u x t ∧ msIsFreeFor B u x t
  | .impl A B,     u, x, t => msIsFreeFor A u x t ∧ msIsFreeFor B u x t
  | .equiv_ A B,   u, x, t => msIsFreeFor A u x t ∧ msIsFreeFor B u x t
  | .all s i A,    u, x, t =>
    (u = s ∧ x = i) ∨ ((s, i) ∉ msTermFV t ∧ msIsFreeFor A u x t)
  | .ex s i A,     u, x, t =>
    (u = s ∧ x = i) ∨ ((s, i) ∉ msTermFV t ∧ msIsFreeFor A u x t)

-- retained: used by LCS.FirstOrder.ManySorted.Equality.Reduction, LCS.FirstOrder.ManySorted.Gentzen.Calculus, LCS.FirstOrder.ManySorted.Gentzen.Completeness, LCS.FirstOrder.ManySorted.Semantics, LCS.FirstOrder.ManySorted.Semantics.Substitution
/-- §10.2.3: Substitution of a term t of sort u for the variable x_i^u in
a many-sorted formula A. Extends Definition 5.2.8; atomic cases
recurse into `msTermSubst`, binary connectives recurse pointwise, and
quantifier cases skip substitution when the bound variable equals
(u, x) (identical sort and index). -/
@[blueprint "chap10__definition_10_2_2"]
def msFormulaSubst {L : MSLanguage} [DecidableEq L.SortType] :
    MSFormula L → (u : L.SortType) → Nat → MSTerm L u → MSFormula L
  | .falsum,       _, _, _ => .falsum
  | .pred P ts,    u, x, t =>
    .pred P (fun i => msTermSubst u x t (ts i))
  | .eq_ hL s t1 t2, u, x, t =>
    .eq_ hL s (msTermSubst u x t t1) (msTermSubst u x t t2)
  | .conj A B,     u, x, t =>
    .conj (msFormulaSubst A u x t) (msFormulaSubst B u x t)
  | .disj A B,     u, x, t =>
    .disj (msFormulaSubst A u x t) (msFormulaSubst B u x t)
  | .impl A B,     u, x, t =>
    .impl (msFormulaSubst A u x t) (msFormulaSubst B u x t)
  | .equiv_ A B,   u, x, t =>
    .equiv_ (msFormulaSubst A u x t) (msFormulaSubst B u x t)
  | .neg A,        u, x, t => .neg (msFormulaSubst A u x t)
  | .all s i A,    u, x, t =>
    if s = u ∧ i = x then .all s i A
    else .all s i (msFormulaSubst A u x t)
  | .ex s i A,     u, x, t =>
    if s = u ∧ i = x then .ex s i A
    else .ex s i (msFormulaSubst A u x t)

end LCS.FirstOrder.ManySorted
