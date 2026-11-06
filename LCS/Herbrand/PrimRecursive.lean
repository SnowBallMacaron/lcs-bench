import LCS.Item
import LCS.Util
import Attach
import LCS.Herbrand.PrimRecursive.ProofsStamp

/-! # Primitive Recursive Functions (Section 7.7)
    Source: Logic for Computer Science, Gallier 2015

    Covers Definitions 7.7.1-7.7.6 (composition, primitive recursion,
    base functions, primitive recursive functions, minimization,
    partial recursive functions) and Examples 7.7.1-7.7.2
    (Ackermann's function, arithmetic operations).
-/

namespace LCS.Herbrand.PrimRecursive

-- ============================================================
-- Definition 7.7.1 — Composition (type layer: NaryFunc abbrev)
-- ============================================================

/-- Definition 7.7.1 (companion type): An n-ary total function over the naturals: takes n natural number arguments (as a Fin n -> Nat vector) and returns a natural number. -/
@[blueprint "chap7__definition_7_7_1"]
abbrev NaryFunc (n : Nat) : Type := (Fin n → Nat) → Nat

-- ============================================================
-- Definition 7.7.3 — Base Functions
-- ============================================================

/-- Definition 7.7.3: The base functions from which primitive recursive functions are built: (i) the successor function S(x) = x + 1, (ii) the zero function Z(x) = 0, and (iii) the projection functions P^n_i(x_1,...,x_n) = x_i. -/
@[blueprint "chap7__definition_7_7_3"]
inductive BaseFunc : Nat → Type where
  /-- The successor function S, such that S(x) = x + 1. Arity 1. -/
  | succ : BaseFunc 1
  /-- The zero function Z, such that Z(x) = 0. Arity 1. -/
  | zero : BaseFunc 1
  /-- The projection function P^n_i, for n > 0 and 1 <= i <= n,
      such that P^n_i(x_1,...,x_n) = x_i. -/
  | proj (n : Nat) (i : Fin n) : BaseFunc n

-- ============================================================
-- Definition 7.7.4 — Primitive Recursive Functions
-- ============================================================

/-- Definition 7.7.4: The class of primitive recursive functions: the least class of total functions over N containing the base functions and closed under composition (Definition 7.7.1) and primitive recursion (Definition 7.7.2). Represented as an arity-indexed inductive type whose terms witness that a function belongs to this class. -/
@[blueprint "chap7__definition_7_7_4" (main := true)]
inductive PrimRec : Nat → Type where
  /-- A base function (successor, zero, or projection) is primitive recursive. -/
  | base : BaseFunc n → PrimRec n
  /-- Composition: given a primitive recursive f of m arguments and m
      primitive recursive functions g_1,...,g_m each of n arguments,
      the composition f ∘ (g_1,...,g_m) is primitive recursive of n arguments. -/
  | comp : PrimRec m → (Fin m → PrimRec n) → PrimRec n
  /-- Primitive recursion: given a primitive recursive f of n arguments
      (base case) and a primitive recursive g of n+2 arguments (step case),
      the function h of n+1 arguments defined by primitive recursion
      from f and g is primitive recursive. -/
  | primRec : PrimRec n → PrimRec (n + 2) → PrimRec (n + 1)

-- ============================================================
-- Definition 7.7.5 — Minimization (type layer: PartialNaryFunc abbrev)
-- ============================================================

/-- Definition 7.7.5 (companion type): An n-ary partial function over the naturals: takes n natural number arguments and returns an optional natural number (None when undefined). -/
@[blueprint "chap7__definition_7_7_5"]
abbrev PartialNaryFunc (n : Nat) : Type := (Fin n → Nat) → Option Nat

-- ============================================================
-- Definition 7.7.6 — Partial Recursive Functions
-- ============================================================

/-- Definition 7.7.6: The class of partial recursive functions: the least class of partial functions over N containing the base functions and closed under composition, primitive recursion, and minimization. Extends PrimRec by adding a minimization constructor. -/
@[blueprint "chap7__definition_7_7_6" (main := true)]
inductive PartialRec : Nat → Type where
  /-- A base function (successor, zero, or projection) is partial recursive. -/
  | base : BaseFunc n → PartialRec n
  /-- Composition: given a partial recursive f of m arguments and m
      partial recursive functions g_1,...,g_m each of n arguments,
      the composition is partial recursive. -/
  | comp : PartialRec m → (Fin m → PartialRec n) → PartialRec n
  /-- Primitive recursion: given a partial recursive f of n arguments
      and a partial recursive g of n+2 arguments, the function defined
      by primitive recursion from f and g is partial recursive. -/
  | primRec : PartialRec n → PartialRec (n + 2) → PartialRec (n + 1)
  /-- Minimization: given a partial recursive g of n+1 arguments,
      the function f of n arguments defined by minimization (searching
      for the least y such that g(x_1,...,x_n,y) = 0) is partial recursive. -/
  | min : PartialRec (n + 1) → PartialRec n

-- ============================================================
-- Definition 7.7.1 — Composition (function layer)
-- ============================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 7.7.6 (companion def): Collect Option results from all Fin m positions into a single Option (Fin m -> Nat), returning none if any position is none. -/
def collectOptionResults {m : Nat} (results : Fin m → Option Nat)
    : Option (Fin m → Nat) :=
  let go (idx : Nat) (acc : Option (Fin m → Nat))
      : Option (Fin m → Nat) :=
    match acc with
    | none => none
    | some f =>
      if h : idx < m then
        match results ⟨idx, h⟩ with
        | none => none
        | some v => some (fun i => if i.val = idx then v else f i)
      else some f
  List.foldl (fun acc idx => go idx acc) (some (fun _ => 0))
    (List.range m)

/-- Definition 7.7.1: Strict composition of partial functions. Every inner
function must be defined on the same input vector, and the outer function must
be defined on their ordered results. For the textbook's positive arities this
is its composition operation; the same formula also handles nullary functions. -/
@[blueprint "chap7__definition_7_7_6"]
def compose (m n : Nat) (f : PartialNaryFunc m) (gs : Fin m → PartialNaryFunc n)
    : PartialNaryFunc n :=
  fun args => do
    let results ← collectOptionResults (fun i => gs i args)
    f results

/-- Definition 7.7.1 (companion def): Composition specialized to total operands,
so all inner results and the outer result are defined. -/
@[blueprint "chap7__definition_7_7_1" (main := true)]
def composeTotal (m n : Nat) (f : NaryFunc m) (gs : Fin m → NaryFunc n)
    : NaryFunc n :=
  fun args => f (fun i => gs i args)

-- ============================================================
-- Definition 7.7.2 — Primitive Recursion (function layer)
-- ============================================================

namespace primRecursion

/-- Definition 7.7.2 (companion def): Helper for primitive recursion that recurses on the explicit natural number y (the recursion variable). -/
@[blueprint "chap7__definition_7_7_2"]
def aux (n : Nat) (f : NaryFunc n) (g : NaryFunc (n + 2))
    (xs : Fin n → Nat) : Nat → Nat
  | 0 => f xs
  | Nat.succ y' =>
    let hVal := aux n f g xs y'
    let stepArgs : Fin (n + 2) → Nat := fun i =>
      if h0 : i.val = 0 then y'
      else if h1 : i.val = 1 then hVal
      else xs ⟨i.val - 2, by omega⟩
    g stepArgs

end primRecursion

/-- Definition 7.7.2: Primitive recursion: given a base function f of n arguments and a step function g of n+2 arguments, produces a function h of n+1 arguments where h(x_1,...,x_n,0) = f(x_1,...,x_n) and h(x_1,...,x_n,y+1) = g(y, h(x_1,...,x_n,y), x_1,...,x_n). The last argument is the recursion variable y. -/
@[blueprint "chap7__definition_7_7_2" (main := true)]
def primRecursion (n : Nat) (f : NaryFunc n) (g : NaryFunc (n + 2))
    : NaryFunc (n + 1) :=
  fun args =>
    let xs : Fin n → Nat := fun i => args i.castSucc
    let y := args (Fin.last n)
    primRecursion.aux n f g xs y

/-- Definition 7.7.2 (companion def): Primitive recursion, nullary special case (n=0): h(0) = m (a constant), h(y+1) = g(y, h(y)). Matches the textbook's explicit treatment of the case when the base function has 0 arguments. -/
@[blueprint "chap7__definition_7_7_2" (main := true)]
def primRecursionNullary (base : Nat) (g : NaryFunc 2)
    : NaryFunc 1 :=
  fun args =>
    let y := args ⟨0, by omega⟩
    primRecursionNullary.aux base g y
where
  /-- Helper for the nullary special case that recurses on y directly. -/
  aux (base : Nat) (g : NaryFunc 2) : Nat → Nat
    | 0 => base
    | Nat.succ y' =>
      let hVal := aux base g y'
      g (fun i => if i.val = 0 then y' else hVal)

-- ============================================================
-- Definition 7.7.3 — Base Functions (eval layer)
-- ============================================================

namespace BaseFunc

/-- Definition 7.7.3 (companion def): Evaluates a base function on an input vector: succ maps x to x+1, zero maps x to 0, proj n i maps (x_1,...,x_n) to x_i. -/
@[blueprint "chap7__definition_7_7_3" (main := true)]
def eval : BaseFunc n → NaryFunc n
  | .succ => fun args => args ⟨0, by omega⟩ + 1
  | .zero => fun args => 0
  | .proj _ i => fun args => args i

end BaseFunc

-- ============================================================
-- Definition 7.7.4 — Primitive Recursive Functions (eval layer)
-- ============================================================

namespace PrimRec

/-- Definition 7.7.4 (companion def): Evaluates a PrimRec term by structural recursion: base delegates to BaseFunc.eval, comp uses composeTotal, primRec uses primRecursion. -/
@[blueprint "chap7__definition_7_7_4"]
def eval : PrimRec n → NaryFunc n
  | .base bf => bf.eval
  | .comp f gs => composeTotal _ _ f.eval (fun i => (gs i).eval)
  | .primRec f g => primRecursion _ f.eval g.eval

end PrimRec

-- ============================================================
-- Definition 7.7.5 — Minimization (function layer)
-- ============================================================

namespace minimize

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 7.7.5 (companion def): Fuel-bounded search starting at the given
y. Returns the first zero encountered, requiring every value from that starting
index through the returned index to be defined. Returns none on timeout or an
undefined intermediate value. The minimization approximant starts at zero. -/
def search (n : Nat) (g : PartialNaryFunc (n + 1))
    (args : Fin n → Nat) : Nat → Nat → Option Nat
  | _, 0 => none
  | y, fuel + 1 =>
    let fullArgs : Fin (n + 1) → Nat := fun i =>
      if h : i.val < n then args ⟨i.val, h⟩ else y
    match g fullArgs with
    | none => none
    | some 0 => some y
    | some (_ + 1) => search n g args (y + 1) fuel

end minimize

/-- Definition 7.7.5: The unbounded graph of minimization. Its output is y
exactly when g(args,y) is zero and every earlier value is defined and nonzero.
This describes a partial function mathematically, with no evaluation cutoff. -/
@[blueprint "chap7__definition_7_7_5" (main := true)]
def minimize (n : Nat) (g : PartialNaryFunc (n + 1))
    (args : Fin n → Nat) (y : Nat) : Prop :=
  let value := fun z => g (fun i => if h : i.val < n then args ⟨i.val, h⟩ else z)
  value y = some 0 ∧ ∀ z, z < y → ∃ v, value z = some v ∧ v ≠ 0

namespace minimize





/-- Definition 7.7.5 (companion theorem): Minimization is defined exactly when
some zero has a fully defined prefix, including the value at that zero. -/
@[blueprint "chap7__definition_7_7_5"]
theorem domainIff (n : Nat) (g : PartialNaryFunc (n + 1))
    (args : Fin n → Nat) :
    (∃ y, minimize n g args y) ↔
      ∃ y, g (fun i => if h : i.val < n then args ⟨i.val, h⟩ else y) = some 0 ∧
        ∀ z, z ≤ y → ∃ v,
          g (fun i => if h : i.val < n then args ⟨i.val, h⟩ else z) = some v 

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 7.7.5 (companion def): Finite evaluator approximant, searching
from zero for at most fuel steps. A timeout is only an approximation to the
unbounded graph; an undefined intermediate value also returns none. -/
def approx (n : Nat) (g : PartialNaryFunc (n + 1)) (fuel : Nat)
    : PartialNaryFunc n :=
  fun args => search n g args 0 fuel

end minimize









-- ============================================================
-- Definition 7.7.6 — Partial Recursive Functions (eval + isTotal)
-- ============================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 7.7.6 (companion def): Helper for evaluating primitive recursion on partial functions, recursing on the Nat y value directly. Uses pre-evaluated f and g functions to avoid mutual recursion issues. -/
def primRecPartial {n : Nat} (evalF : PartialNaryFunc n)
    (evalG : PartialNaryFunc (n + 2))
    (xs : Fin n → Nat) : Nat → Option Nat
  | 0 => evalF xs
  | Nat.succ y' => do
    let hVal ← primRecPartial evalF evalG xs y'
    let stepArgs : Fin (n + 2) → Nat := fun i =>
      if h0 : i.val = 0 then y'
      else if h1 : i.val = 1 then hVal
      else xs ⟨i.val - 2, by omega⟩
    evalG stepArgs

namespace PartialRec

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 7.7.6 (companion def): Evaluates a PartialRec term with a fuel bound: base delegates to BaseFunc.eval (wrapped in some), comp uses strict compose, primRec uses primitive recursion lifted to Option, min uses minimize.approx with the given fuel. Uses structural recursion on the PartialRec term. -/
def eval (pr : PartialRec n) (fuel : Nat)
    : PartialNaryFunc n :=
  match pr with
  | .base bf => fun args => some (bf.eval args)
  | .comp f gs => compose _ _ (f.eval fuel) (fun i => (gs i).eval fuel)
  | .primRec f g =>
    fun args =>
      let xs : Fin _ → Nat := fun i => args (Fin.castSucc i)
      let y := args (Fin.last _)
      let evalF := f.eval fuel
      let evalG := g.eval fuel
      primRecPartial evalF evalG xs y
  | .min g =>
    fun args => minimize.approx _ (g.eval fuel) fuel args

/-- Definition 7.7.6 (companion): the unbounded convergence graph of a
partial-recursive program. A result is defined when some finite evaluator
approximant returns it; the fuel may depend on the input and result. -/
@[blueprint "chap7__definition_7_7_6"]
def converges (pr : PartialRec n) (args : Fin n → Nat) (v : Nat) : Prop :=
  ∃ fuel : Nat, pr.eval fuel args = some v

/-- Definition 7.7.6 (companion def): A partial recursive function is total (i.e., recursive) iff for all inputs there exists a fuel value such that eval returns some value. -/
@[blueprint "chap7__definition_7_7_6" (main := true)]
def isTotal (pr : PartialRec n) : Prop :=
  ∀ (args : Fin n → Nat), ∃ (fuel : Nat) (v : Nat),
    pr.eval fuel args = some v

end PartialRec

-- ============================================================
-- Section 7.7.3 — Decidable and partially decidable problems
-- ============================================================





-- ============================================================
-- Example 7.7.1 — Ackermann's Function
-- ============================================================

/-- Example 7.7.1: Ackermann's function: A(x, y) defined by well-founded recursion on the lexicographic order of (x, y). This is a total recursive function that is not primitive recursive. A(0, y) = y + 1; A(x+1, 0) = A(x, 1); A(x+1, y+1) = A(x, A(x+1, y)). -/
@[blueprint "chap7__example_7_7_1" (main := true)]
def ackermann : Nat → Nat → Nat
  | 0, y => y + 1
  | x + 1, 0 => ackermann x 1
  | x + 1, y + 1 => ackermann x (ackermann (x + 1) y)

/-- Example 7.7.1: the displayed Ackermann function has a total binary
partial-recursive representation. Positions 0 and 1 of the input vector are
its arguments x and y. One program represents the existing recurrence at
every input; successful values are specified by its exact convergence graph. -/
@[attach_debt, blueprint "chap7__example_7_7_1" (main := true)]
theorem ackermannIsRecursive :
    ∃ pr : PartialRec 2, pr.isTotal ∧
      ∀ (args : Fin 2 → Nat) (v : Nat),
        pr.converges args v ↔ v = ackermann (args 0) (args 1) 

/-- Example 7.7.1: no binary primitive-recursive program agrees with the
displayed Ackermann function on every input. The excluded representation
uses the same argument order and the same Ackermann definition as the
recursive-membership statement. -/
@[attach_debt, blueprint "chap7__example_7_7_1" (main := true)]
theorem ackermannNotPrimitiveRecursive :
    ¬ ∃ pr : PrimRec 2, ∀ args : Fin 2 → Nat,
      pr.eval args = ackermann (args 0) (args 1) 

-- ============================================================
-- Example 7.7.2 — Primitive Recursive Arithmetic Operations
-- ============================================================

/-- Example 7.7.2 (companion def): zero function of arbitrary arity n+1. For arity 1, uses the base zero function directly. For arity > 1, composes zero with a projection. -/
@[blueprint "chap7__example_7_7_2"]
def primRecZero (n : Nat) : PrimRec (n + 1) :=
  PrimRec.comp (PrimRec.base BaseFunc.zero)
    (fun _ => PrimRec.base (BaseFunc.proj (n + 1) ⟨0, by omega⟩))

/-- Example 7.7.2 (companion def): constant function returning k, of
    arity n+1. Built by iterating successor over the zero function. -/
@[blueprint "chap7__example_7_7_2"]
def primRecConst : Nat → (n : Nat) → PrimRec (n + 1)
  | 0, n => primRecZero n
  | k + 1, n => PrimRec.comp (PrimRec.base BaseFunc.succ)
      (fun _ => primRecConst k n)

/-- Example 7.7.2: Addition as a PrimRec term: base case: x + 0 = P^1_1(x) = x, step case: x + (y+1) = S(x + y). Uses primitive recursion with P^1_1 as base function and a composition of successor with projection as step function. -/
@[blueprint "chap7__example_7_7_2" (main := true)]
def primRecAdd : PrimRec 2 :=
  PrimRec.primRec
    -- base: f(x) = P^1_1(x) = x
    (PrimRec.base (BaseFunc.proj 1 ⟨0, by omega⟩))
    -- step: g(y, h_val, x) = S(h_val) = S(x + y)
    -- g is a 3-ary function; we compose S with projection of h_val (index 1)
    (PrimRec.comp
      (PrimRec.base BaseFunc.succ)
      (fun _ => PrimRec.base (BaseFunc.proj 3 ⟨1, by omega⟩)))

/-- Example 7.7.2: Multiplication as a PrimRec term: base case: x * 0 = Z(x) = 0, step case: x * (y+1) = (x*y) + x. Uses primitive recursion with Z as base function and addition composed with appropriate projections as step function. -/
@[blueprint "chap7__example_7_7_2" (main := true)]
def primRecMul : PrimRec 2 :=
  PrimRec.primRec
    -- base: f(x) = Z(x) = 0
    (PrimRec.base BaseFunc.zero)
    -- step: g(y, h_val, x) = h_val + x = (x*y) + x
    -- g is 3-ary; compose primRecAdd with projections for h_val and x
    (PrimRec.comp
      primRecAdd
      (fun i =>
        if i.val = 0 then PrimRec.base (BaseFunc.proj 3 ⟨1, by omega⟩)
        else PrimRec.base (BaseFunc.proj 3 ⟨2, by omega⟩)))

/-- Example 7.7.2: Exponentiation as a PrimRec term: base case: exp(x, 0) = 1, step case: exp(x, y+1) = exp(x, y) * x. The base returns constant 1, step multiplies accumulated power by x. -/
@[blueprint "chap7__example_7_7_2" (main := true)]
def primRecExp : PrimRec 2 :=
  PrimRec.primRec
    -- base: f(x) = 1 (constant function returning 1)
    -- Compose S with Z: S(Z(x)) = 0 + 1 = 1
    (primRecConst 1 0)
    -- step: g(y, h_val, x) = h_val * x = exp(x,y) * x
    (PrimRec.comp
      primRecMul
      (fun i =>
        if i.val = 0 then PrimRec.base (BaseFunc.proj 3 ⟨1, by omega⟩)
        else PrimRec.base (BaseFunc.proj 3 ⟨2, by omega⟩)))

/-- Example 7.7.2 (companion def): Factorial as a PrimRec term (nullary base case pattern): fact(0) = 1, fact(y+1) = fact(y) * S(y). Since PrimRec 0 cannot be directly built from base functions (all of which have arity >= 1), we encode factorial as a 2-ary function factAux(x, y) = fact(y) that ignores its first argument, then project to get the unary version. -/
@[blueprint "chap7__example_7_7_2"]
def primRecFactAux : PrimRec 2 :=
  PrimRec.primRec
    -- base: f(x) = 1 (constant 1, ignoring x)
    (primRecConst 1 0)
    -- step: g(y, h_val, x) = h_val * S(y)
    (PrimRec.comp primRecMul
      (fun i =>
        if i.val = 0
        then PrimRec.base (BaseFunc.proj 3 ⟨1, by omega⟩)  -- h_val
        else PrimRec.comp (PrimRec.base BaseFunc.succ)       -- S(y)
          (fun _ => PrimRec.base (BaseFunc.proj 3 ⟨0, by omega⟩))))

/-- Example 7.7.2: Factorial as a PrimRec 1 term: fact(y) = factAux(0, y).
    Projects the 2-ary factAux by fixing the unused first argument to 0. -/
@[blueprint "chap7__example_7_7_2" (main := true)]
def primRecFact : PrimRec 1 :=
  PrimRec.comp primRecFactAux
    (fun i =>
      if i.val = 0
      then PrimRec.base BaseFunc.zero                    -- first arg = 0
      else PrimRec.base (BaseFunc.proj 1 ⟨0, by omega⟩)) -- second arg = y

/-- Example 7.7.2 (companion def): Iterated exponentiation as a PrimRec term: ex(0) = 0, ex(y+1) = exp(2, ex(y)). Encoded as a 2-ary function exAux(x, y) = ex(y) that ignores its first argument, then projected to unary. -/
@[blueprint "chap7__example_7_7_2"]
def primRecIterExpAux : PrimRec 2 :=
  PrimRec.primRec
    -- base: f(x) = 0
    (PrimRec.base BaseFunc.zero)
    -- step: g(y, h_val, x) = exp(2, h_val)
    (PrimRec.comp primRecExp
      (fun i =>
        if i.val = 0
        -- const 2
        then primRecConst 2 2
        -- h_val = proj index 1 of (y, h_val, x)
        else PrimRec.base (BaseFunc.proj 3 ⟨1, by omega⟩)))

/-- Example 7.7.2: Iterated exponentiation as a PrimRec 1 term:
    ex(y) = exAux(0, y). -/
@[blueprint "chap7__example_7_7_2" (main := true)]
def primRecIterExp : PrimRec 1 :=
  PrimRec.comp primRecIterExpAux
    (fun i =>
      if i.val = 0
      then PrimRec.base BaseFunc.zero
      else PrimRec.base (BaseFunc.proj 1 ⟨0, by omega⟩))


/-- Example 7.7.2 (companion def): Composition with a unary function. -/
@[blueprint "chap7__example_7_7_2"]
def primRecComposeOne {n : Nat} (f : PrimRec 1) (g : PrimRec n) : PrimRec n :=
  .comp f (fun _ => g)

/-- Example 7.7.2 (companion def): Composition with a binary function. -/
@[blueprint "chap7__example_7_7_2"]
def primRecComposeTwo {n : Nat} (f : PrimRec 2) (g h : PrimRec n) : PrimRec n :=
  .comp f (fun i => if i.val = 0 then g else h)

/-- Example 7.7.2 (companion def): Projection onto coordinate i. -/
@[blueprint "chap7__example_7_7_2"]
def primRecProj {n : Nat} (i : Fin n) : PrimRec n :=
  .base (.proj n i)

/-- Example 7.7.2 (companion def): Sign, with sign(0) = 0 and sign(y+1) = 1.
The auxiliary recursion ignores its first argument. -/
@[blueprint "chap7__example_7_7_2"]
def primRecSign : PrimRec 1 :=
  primRecComposeTwo (.primRec (primRecConst 0 0) (primRecConst 1 2))
    (primRecConst 0 0) (primRecProj 0)

/-- Example 7.7.2 (companion def): Predecessor, with pred(0) = 0 and
pred(y+1) = y. The auxiliary recursion ignores its first argument. -/
@[blueprint "chap7__example_7_7_2"]
def primRecPred : PrimRec 1 :=
  primRecComposeTwo (.primRec (primRecConst 0 0) (primRecProj 0))
    (primRecConst 0 0) (primRecProj 0)

/-- Example 7.7.2 (companion def): Truncated subtraction x ∸ y, obtained by
iterating predecessor y times from x. -/
@[blueprint "chap7__example_7_7_2"]
def primRecSub : PrimRec 2 :=
  .primRec (primRecProj 0) (primRecComposeOne primRecPred (primRecProj 1))

/-- Example 7.7.2 (companion def): Characteristic function of zero:
zeroTest(x) = 1 ∸ sign(x). -/
@[blueprint "chap7__example_7_7_2"]
def primRecZeroTest : PrimRec 1 :=
  primRecComposeTwo primRecSub (primRecConst 1 0) primRecSign

/-- Example 7.7.2 (companion def): Characteristic function of x = y,
by testing (x ∸ y) + (y ∸ x) for zero. -/
@[blueprint "chap7__example_7_7_2"]
def primRecEqual : PrimRec 2 :=
  primRecComposeOne primRecZeroTest
    (primRecComposeTwo primRecAdd primRecSub
      (primRecComposeTwo primRecSub (primRecProj 1) (primRecProj 0)))

/-- Example 7.7.2 (companion def): Characteristic function of x < y. -/
@[blueprint "chap7__example_7_7_2"]
def primRecLess : PrimRec 2 :=
  primRecComposeOne primRecSign
    (primRecComposeTwo primRecSub (primRecProj 1) (primRecProj 0))

/-- Example 7.7.2 (companion def): Bounded sum of f(xs,k) for k < b.
There are n+1 fixed parameters xs; the last argument is the bound b.
The recursion step receives (k, accumulated sum, xs). -/
@[blueprint "chap7__example_7_7_2"]
def primRecBoundedSum {n : Nat} (f : PrimRec (n + 2)) : PrimRec (n + 2) :=
  .primRec (primRecConst 0 n)
    (primRecComposeTwo primRecAdd (primRecProj 1)
      (.comp f (fun i =>
        if h : i.val < n + 1 then primRecProj ⟨i.val + 2, by omega⟩
        else primRecProj 0)))

/-- Example 7.7.2 (companion def): Bounded product of f(xs,k) for k < b,
with empty product 1. The last argument is the bound b. -/
@[blueprint "chap7__example_7_7_2"]
def primRecBoundedProduct {n : Nat} (f : PrimRec (n + 2)) : PrimRec (n + 2) :=
  .primRec (primRecConst 1 n)
    (primRecComposeTwo primRecMul (primRecProj 1)
      (.comp f (fun i =>
        if h : i.val < n + 1 then primRecProj ⟨i.val + 2, by omega⟩
        else primRecProj 0)))

/-- Example 7.7.2 (companion def): Characteristic function of divisibility
on (d,m): sign of the sum of [d*k = m] for k < m+1. This also gives the
usual convention that 0 divides 0 and does not divide a positive number. -/
@[blueprint "chap7__example_7_7_2"]
def primRecDivides : PrimRec 2 :=
  let factor : PrimRec 3 := primRecComposeTwo primRecEqual
    (primRecComposeTwo primRecMul (primRecProj 0) (primRecProj 2))
    (primRecProj 1)
  primRecComposeOne primRecSign
    (.comp (primRecBoundedSum factor) (fun i =>
      if i.val = 0 then primRecProj 0
      else if i.val = 1 then primRecProj 1
      else primRecComposeOne (.base .succ) (primRecProj 1)))

/-- Example 7.7.2 (companion def): Characteristic function of primality.
For q ≥ 2, multiply 1 ∸ [d divides q] over 2 ≤ d < q; for q < 2,
the additional factor [1 < q] makes the result zero. -/
@[blueprint "chap7__example_7_7_2"]
def primRecPrime : PrimRec 1 :=
  let factor : PrimRec 2 := primRecComposeOne primRecZeroTest
    (primRecComposeTwo primRecDivides
      (primRecComposeTwo primRecAdd (primRecProj 1) (primRecConst 2 1))
      (primRecProj 0))
  primRecComposeTwo primRecMul
    (primRecComposeTwo primRecLess (primRecConst 1 0) (primRecProj 0))
    (primRecComposeTwo (primRecBoundedProduct factor) (primRecProj 0)
      (primRecComposeTwo primRecSub (primRecProj 0) (primRecConst 2 0)))

/-- Example 7.7.2 (companion def): Bounded minimization of a characteristic
function P(xs,q). Returns the least q ≤ b with P(xs,q) = 1, or b+1 if none
exists. It is the sum, for i < b+1, of the products of 1 ∸ P(xs,j) for
j < i+1. Each product is 1 exactly while no witness has been encountered. -/
@[blueprint "chap7__example_7_7_2"]
def primRecBoundedMin {n : Nat} (p : PrimRec (n + 2)) : PrimRec (n + 2) :=
  let prefixProduct := primRecBoundedProduct (primRecComposeOne primRecZeroTest p)
  let inclusivePrefix : PrimRec (n + 2) := .comp prefixProduct (fun i =>
    if h : i.val < n + 1 then primRecProj i
    else primRecComposeOne (.base .succ) (primRecProj i))
  .comp (primRecBoundedSum inclusivePrefix) (fun i =>
    if h : i.val < n + 1 then primRecProj i
    else primRecComposeOne (.base .succ) (primRecProj i))

/-- Example 7.7.2 (companion def): The next prime after p, for prime p.
Bounded minimization searches for a prime q with p < q ≤ p!+1.
A prime divisor of p!+1 is greater than p, so this interval contains a prime. -/
@[blueprint "chap7__example_7_7_2"]
def primRecNextPrime : PrimRec 1 :=
  let candidate : PrimRec 2 := primRecComposeTwo primRecMul primRecLess
    (primRecComposeOne primRecPrime (primRecProj 1))
  primRecComposeTwo (primRecBoundedMin candidate) (primRecProj 0)
    (primRecComposeOne (.base .succ) primRecFact)

/-- Example 7.7.2: The function taking n to the n-th prime number, as a
PrimRec term. The convention is zero-based: p(0) = 2, p(1) = 3, p(2) = 5.
Primitive recursion starts at 2 and takes the least prime q with
p(n) < q ≤ p(n)!+1 at each step. The auxiliary recursion uses one ignored
parameter so its base function has positive arity. -/
@[blueprint "chap7__example_7_7_2" (main := true)]
def primRecNthPrime : PrimRec 1 :=
  primRecComposeTwo
    (.primRec (primRecConst 2 0)
      (primRecComposeOne primRecNextPrime (primRecProj 1)))
    (primRecConst 0 0) (primRecProj 0)

end LCS.Herbrand.PrimRecursive
