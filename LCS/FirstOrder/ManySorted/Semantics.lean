import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.Propositional.Semantics
import Attach
import LCS.FirstOrder.ManySorted.Semantics.ProofsStamp

/-! # FirstOrder.ManySorted.Semantics
    Formalization of Chapter 10, Section 10.3 (Semantics of Many-Sorted
    First-Order Logic).

    Many-sorted L-structures (Def 10.3.1), assignments (Def 10.3.2), the
    derived many-sorted algebra 𝓜 with quantifier/connective operations
    (Def 10.3.3, 10.3.4), and the recursive meaning of terms (Def 10.3.5)
    and formulae (Def 10.3.6).

    Builds on §10.2 (LCS.FirstOrder.ManySorted): MSLanguage, MSTerm,
    MSFormula. The truth domain BOOL and the truth functions
    H_and/H_or/H_supset/H_equiv/H_neg are `BoolVal` and
    `hAnd/hOr/hImplies/hEquiv/hNeg` from Chapter 3
    (LCS.Propositional.Semantics).

    Source: Logic for Computer Science, Gallier 2015.
-/

namespace LCS.FirstOrder.ManySorted.Semantics

open LCS.FirstOrder.ManySorted
open LCS.Propositional.Semantics

-- ===================================================================
-- Definition 10.3.1: Many-sorted L-structure
-- ===================================================================

/-- Definition 10.3.1: Given a many-sorted first-order language `L`, a
many-sorted L-structure `M` is a many-sorted L-algebra such that the
carrier of sort bool is the set BOOL = {T, F}.

  * `carrier s` is the nonempty domain `M_s` of each (non-bool) sort
    `s ∈ S`. (`carrierNonempty` records the textbook's requirement that
    each `M_s` is nonempty.)
  * `interpFunc` interprets every function symbol `f` of rank
    `(u_1…u_n, s)` as a function `f_M : M^u → M_s`. The product domain
    `M^u = M^{u_1} × … × M^{u_n}` is the dependent function type
    `(i : Fin (L.funRank f).1.length) → carrier ((L.funRank f).1.get i)`
    (a `Fin`-indexed family whose i-th component lies in the carrier of
    the i-th arity sort); the codomain is the carrier of the output sort
    `(L.funRank f).2`.
  * `interpConst` interprets every constant `c` of sort `s` as an element
    `c_M ∈ M_s`.
  * `interpPred` interprets every predicate `P` of arity `u_1…u_n` as a
    function `P_M : M^u → BOOL`. The codomain is fixed to `BoolVal`
    (the textbook's BOOL), realizing "the carrier of sort bool is BOOL";
    there is no `SortType` entry for bool (bool ∉ S, Def 10.2.1).

Direct analogue of one-sorted `Structure` (chap5 Def 5.3.1), specialized
to sort-tagged carriers and a `BoolVal`-valued predicate interpretation.
`Type 1` because `carrier` is a `Type`-valued field. -/
@[blueprint "chap10__definition_10_3_1" (main := true)]
structure MSStructure (L : MSLanguage) : Type 1 where
  /-- The nonempty carrier `M_s` of each sort `s ∈ S`. -/
  carrier : L.SortType → Type
  /-- Def 10.3.1 constraint: each sort carrier `M_s` is nonempty. -/
  carrierNonempty : (s : L.SortType) → Nonempty (carrier s)
  /-- Interpretation `f_M : M^u → M_s` of each function symbol `f`. -/
  interpFunc : (f : L.funSymbols) →
    ((i : Fin (L.funRank f).1.length) → carrier ((L.funRank f).1.get i)) →
    carrier (L.funRank f).2
  /-- Interpretation `c_M ∈ M_s` of each constant `c` of sort `s`. -/
  interpConst : (s : L.SortType) → L.constSymbols s → carrier s
  /-- Interpretation `P_M : M^u → BOOL` of each predicate symbol `P`. -/
  interpPred : (P : L.predSymbols) →
    ((i : Fin (L.predArity P).length) → carrier ((L.predArity P).get i)) →
    BoolVal

-- ===================================================================
-- Definition 10.3.2: Assignments
-- ===================================================================

/-- Definition 10.3.2 (companion): The set `[V_s → M_s]` of all
assignments of sort `s` — a function `v_s : V_s → M_s` from the
sort-`s` variables (modelled by `Nat`, matching §10.2's
`MSVar L = L.SortType × Nat`) to the carrier `M_s`. As a Lean type its
inhabitants are exactly the sort-`s` assignments. -/
@[blueprint "chap10__definition_10_3_2"]
abbrev MSAssignmentOfSort {L : MSLanguage} (M : MSStructure L)
    (s : L.SortType) : Type :=
  Nat → M.carrier s

/-- Definition 10.3.2: An assignment `v` is any S-indexed family
`v = (v_s)_{s ∈ S}` of assignments of sort `s`, each `v_s : V_s → M_s`.
The set `[V → M]` of all assignments IS this type: its inhabitants are
exactly the S-indexed assignment families. Applying `v` at the sort-`s`
variable `x_i` is `v s i`.

Analogue of one-sorted `Assignment` (chap5 Def 5.3.2:
`abbrev Assignment M := Nat → M.carrier`), specialized so each variable's
value lies in the carrier of its own sort. -/
@[blueprint "chap10__definition_10_3_2" (main := true)]
abbrev MSAssignment {L : MSLanguage} (M : MSStructure L) : Type :=
  (s : L.SortType) → MSAssignmentOfSort M s

-- ===================================================================
-- Definition 10.3.4: Carriers of the derived algebra 𝓜 (script-M)
-- ===================================================================

/-- Definition 10.3.4 (companion): For each sort `s`, the carrier `𝓜_s`
of the derived many-sorted algebra `𝓜` is the function space
`[[V → M] → M_s]` of all functions from full assignments to `M_s`.
Term meanings are elements of this full carrier. -/
@[blueprint "chap10__definition_10_3_4"]
abbrev MSSemTerm {L : MSLanguage} (M : MSStructure L)
    (s : L.SortType) : Type :=
  MSAssignment M → M.carrier s

/-- Definition 10.3.4 (companion): The bool carrier `𝓜_bool` of `𝓜`,
the function space `[[V → M] → BOOL]`. This is simultaneously the
semantic function space of formula meanings and the codomain of the
quantifier/connective operations of `𝓜`. -/
@[blueprint "chap10__definition_10_3_4"]
abbrev MSSemBool {L : MSLanguage} (M : MSStructure L) : Type :=
  MSAssignment M → BoolVal

-- ===================================================================
-- Definition 10.3.5: Subformula relation
-- ===================================================================

/-- Definition 10.3.5: The subformula relation `MSIsSubformula X A`
("`X` is a subformula of `A`"), defined by recursion on `A` exactly as
the one-sorted `IsSubformula` (chap5 Def 5.3.9), generalized to
sort-tagged quantifiers `MSFormula.all s i` / `MSFormula.ex s i`.

  * `refl` makes every formula a subformula of itself; this
    simultaneously realizes the three atomic base cases (predicate
    application, equality, falsum are atomic and produce no proper
    subformulae, so the only `X` with `MSIsSubformula X A` for atomic
    `A` is `X = A`).
  * The binary-connective cases (`∧, ∨, ⊃, ≡`) recurse into either
    operand.
  * The negation case recurses into the operand.
  * The quantifier cases recurse into `B[t/x_i^s]` for a term `t` of
    sort `s` that is free for `x_i^s` in `B`, as in Definition 5.3.9.
    A sort-equality decision is used only to form the substitution
    instance; it is not a parameter of the subformula relation. -/
inductive MSIsSubformula {L : MSLanguage} :
    MSFormula L → MSFormula L → Prop where
  /-- Reflexivity: every formula is a subformula of itself; covers the
      atomic base cases (pred, eq_, falsum). -/
  | refl : (A : MSFormula L) → MSIsSubformula A A
  /-- Conjunction, left operand. -/
  | conjLeft : MSIsSubformula X B → MSIsSubformula X (MSFormula.conj B C)
  /-- Conjunction, right operand. -/
  | conjRight : MSIsSubformula X C → MSIsSubformula X (MSFormula.conj B C)
  /-- Disjunction, left operand. -/
  | disjLeft : MSIsSubformula X B → MSIsSubformula X (MSFormula.disj B C)
  /-- Disjunction, right operand. -/
  | disjRight : MSIsSubformula X C → MSIsSubformula X (MSFormula.disj B C)
  /-- Implication, left operand. -/
  | implLeft : MSIsSubformula X B → MSIsSubformula X (MSFormula.impl B C)
  /-- Implication, right operand. -/
  | implRight : MSIsSubformula X C → MSIsSubformula X (MSFormula.impl B C)
  /-- Equivalence, left operand. -/
  | equivLeft : MSIsSubformula X B →
      MSIsSubformula X (MSFormula.equiv_ B C)
  /-- Equivalence, right operand. -/
  | equivRight : MSIsSubformula X C →
      MSIsSubformula X (MSFormula.equiv_ B C)
  /-- Negation: `X` subformula of `B` ⇒ `X` subformula of `¬B`. -/
  | negSub : MSIsSubformula X B → MSIsSubformula X (MSFormula.neg B)
  /-- Universal quantifier: subformulae of a same-sort free-for instance
      `B[t/x_i^s]` are subformulae of `∀_s x_i B`. -/
  | allSub [DecidableEq L.SortType] : (t : MSTerm L s) →
      msIsFreeFor B s i t → MSIsSubformula X (msFormulaSubst B s i t) →
      MSIsSubformula X (MSFormula.all s i B)
  /-- Existential quantifier: subformulae of a same-sort free-for instance
      `B[t/x_i^s]` are subformulae of `∃_s x_i B`. -/
  | exSub [DecidableEq L.SortType] : (t : MSTerm L s) →
      msIsFreeFor B s i t → MSIsSubformula X (msFormulaSubst B s i t) →
      MSIsSubformula X (MSFormula.ex s i B)

-- ===================================================================
-- Definition 10.3.3: Assignment update v[x_i := a]
-- ===================================================================

/-- Definition 10.3.3 (companion): The updated assignment `v[x_i := a]`
that agrees with `v` everywhere except it maps the sort-`s` variable
`x_i` to `a ∈ M_s`. Because carriers are sort-indexed, the update must
match on whether the queried sort `s'` equals `s` and rewrite the
carrier type accordingly (`h ▸ a`). Uses the classical `DecidableEq
L.SortType`, so the definition is `noncomputable`. -/
@[blueprint "chap10__definition_10_3_3"]
noncomputable def msAssignUpdate {L : MSLanguage} (M : MSStructure L)
    (v : MSAssignment M) (s : L.SortType) (i : Nat) (a : M.carrier s) :
    MSAssignment M :=
  fun s' j =>
    letI := Classical.propDecidable (s' = s)
    if h : s' = s then
      (if j = i then h ▸ a else v s' j)
    else v s' j

-- ===================================================================
-- Definition 10.3.4: Lifted connective operations of 𝓜 (script-M)
-- ===================================================================

/-- Definition 10.3.4 (companion): The lifted conjunction `∧_𝓜` on
`𝓜_bool`: `∧_𝓜(f, g)(v) = H_and(f(v), g(v))`, the pointwise lifting of
the Chapter 3 truth function `hAnd`. -/
@[blueprint "chap10__definition_10_3_4"]
def andM {L : MSLanguage} (M : MSStructure L)
    (f g : MSSemBool M) : MSSemBool M :=
  fun v => hAnd (f v) (g v)

/-- Definition 10.3.4 (companion): The lifted disjunction `∨_𝓜`:
`∨_𝓜(f, g)(v) = H_or(f(v), g(v))`. -/
@[blueprint "chap10__definition_10_3_4"]
def orM {L : MSLanguage} (M : MSStructure L)
    (f g : MSSemBool M) : MSSemBool M :=
  fun v => hOr (f v) (g v)

/-- Definition 10.3.4 (companion): The lifted implication `⊃_𝓜`:
`⊃_𝓜(f, g)(v) = H_supset(f(v), g(v))`. -/
@[blueprint "chap10__definition_10_3_4"]
def implM {L : MSLanguage} (M : MSStructure L)
    (f g : MSSemBool M) : MSSemBool M :=
  fun v => hImplies (f v) (g v)

/-- Definition 10.3.4 (companion): The lifted equivalence `≡_𝓜`:
`≡_𝓜(f, g)(v) = H_equiv(f(v), g(v))`. -/
@[blueprint "chap10__definition_10_3_4"]
def equivM {L : MSLanguage} (M : MSStructure L)
    (f g : MSSemBool M) : MSSemBool M :=
  fun v => hEquiv (f v) (g v)

/-- Definition 10.3.4 (companion): The lifted negation `¬_𝓜`:
`¬_𝓜(f)(v) = H_neg(f(v))`. -/
@[blueprint "chap10__definition_10_3_4"]
def negM {L : MSLanguage} (M : MSStructure L)
    (f : MSSemBool M) : MSSemBool M :=
  fun v => hNeg (f v)

/-- Definition 10.3.4: The lifted same-sort equality operation on the
full semantic carriers: `eqM M f g v = T` iff `f v = g v`, and F otherwise.
Both inputs are arbitrary functions from full assignments to `M_s`.
This completes the semantic signature with the equality operation supplied by
Definition 10.3.6, using its pointwise carrier-equality test. -/
@[blueprint "chap10__definition_10_3_4" (main := true)]
noncomputable def eqM {L : MSLanguage} (M : MSStructure L)
    {s : L.SortType} (f g : MSSemTerm M s) : MSSemBool M :=
  fun v =>
    letI := Classical.propDecidable (f v = g v)
    if f v = g v then BoolVal.T else BoolVal.F

-- ===================================================================
-- Definition 10.3.4: Lifted nonlogical operations of 𝓜 (script-M)
-- ===================================================================

/-- Definition 10.3.4 (companion): The lifted function-symbol operation
`f_𝓜` of `𝓜`: `f_𝓜(g_1, …, g_n)(v) = f_M(g_1(v), …, g_n(v))`, applying
the structure's interpretation `interpFunc` pointwise to the argument
meanings. -/
@[blueprint "chap10__definition_10_3_4"]
def funM {L : MSLanguage} (M : MSStructure L) (f : L.funSymbols)
    (gs : (i : Fin (L.funRank f).1.length) →
      MSSemTerm M ((L.funRank f).1.get i)) :
    MSSemTerm M (L.funRank f).2 :=
  fun v => M.interpFunc f (fun i => gs i v)

/-- Definition 10.3.4 (companion): The lifted predicate-symbol operation
`P_𝓜` of `𝓜`: `P_𝓜(g_1, …, g_n)(v) = P_M(g_1(v), …, g_n(v))`. -/
@[blueprint "chap10__definition_10_3_4"]
def predM {L : MSLanguage} (M : MSStructure L) (P : L.predSymbols)
    (gs : (i : Fin (L.predArity P).length) →
      MSSemTerm M ((L.predArity P).get i)) :
    MSSemBool M :=
  fun v => M.interpPred P (fun i => gs i v)

/-- Definition 10.3.4 (companion): The lifted constant operation `c_𝓜`
of `𝓜`: the constant-valued function `c_𝓜(v) = c_M` on assignments. -/
@[blueprint "chap10__definition_10_3_4"]
def constM {L : MSLanguage} (M : MSStructure L) (s : L.SortType)
    (c : L.constSymbols s) : MSSemTerm M s :=
  fun _ => M.interpConst s c

/-- Definition 10.3.4 (companion): The variable meaning `x_𝓜 ∈ 𝓜_s`
of the sort-`s` variable `x_i`, the function such that
`x_𝓜(v) = v_s(x) = v s i`. -/
@[blueprint "chap10__definition_10_3_4"]
def varMeaning {L : MSLanguage} (M : MSStructure L) (s : L.SortType)
    (i : Nat) : MSSemTerm M s :=
  fun v => v s i

-- ===================================================================
-- Definition 10.3.3: Quantifier semantic functions (A_i^s)_M, (E_i^s)_M
-- ===================================================================

/-- Definition 10.3.3: The universal-quantifier semantic function
`(A_i^s)_𝓜` on `𝓜_bool`: `(A_i^s)_𝓜(f)(v) = T` iff
`f(v[x_i := a]) = T` for all `a ∈ M_s` (equivalently, `= F` iff
`f(v[x_i := a]) = F` for some `a`). The `∀` over `M.carrier s` is a
`Prop` decided classically, so this is `noncomputable`. -/
@[blueprint "chap10__definition_10_3_3" (main := true)]
noncomputable def forallM {L : MSLanguage} (M : MSStructure L)
    {s : L.SortType} (i : Nat) (f : MSSemBool M) : MSSemBool M :=
  fun v =>
    letI := Classical.propDecidable
      (∀ a : M.carrier s, f (msAssignUpdate M v s i a) = BoolVal.T)
    if (∀ a : M.carrier s, f (msAssignUpdate M v s i a) = BoolVal.T) then
      BoolVal.T
    else BoolVal.F

/-- Definition 10.3.3: The existential-quantifier semantic function
`(E_i^s)_𝓜` on `𝓜_bool`: `(E_i^s)_𝓜(f)(v) = T` iff
`f(v[x_i := a]) = T` for some `a ∈ M_s`. `noncomputable` for the same
reason as `forallM`. -/
@[blueprint "chap10__definition_10_3_3"]
noncomputable def existsM {L : MSLanguage} (M : MSStructure L)
    {s : L.SortType} (i : Nat) (f : MSSemBool M) : MSSemBool M :=
  fun v =>
    letI := Classical.propDecidable
      (∃ a : M.carrier s, f (msAssignUpdate M v s i a) = BoolVal.T)
    if (∃ a : M.carrier s, f (msAssignUpdate M v s i a) = BoolVal.T) then
      BoolVal.T
    else BoolVal.F

-- ===================================================================
-- Definition 10.3.5: Recursive term meaning t_M = φ-hat(t)
-- ===================================================================

/-- Definition 10.3.5: The recursive meaning `t_M` of a term `t` of sort
`s`, i.e. the value `φ-hat(t)`. For each assignment `v`, `t_M[v] ∈ M_s`
is defined by recursion on `MSTerm`:

  * (i)   `x_M[v] = v_s(x)`            — `varMeaning M s i v = v s i`;
  * (ii)  `c_M[v] = c_M`              — `M.interpConst s c`;
  * (iii) `(f t_1…t_n)_M[v] = f_M((t_1)_M[v], …, (t_n)_M[v])`.

Built from the lifted operations `varMeaning`/`constM`/`funM` so that it
is literally the value of the unique homomorphism `φ-hat` (extending
`φ = phiMap`) at the term — and `noncomputable` because `msFormulaEval`
(below) uses it alongside the classically-decided quantifier/equality
clauses. -/
@[blueprint "chap10__definition_10_3_5" (main := true)]
noncomputable def msTermEval {L : MSLanguage} (M : MSStructure L)
    (v : MSAssignment M) : {s : L.SortType} → MSTerm L s → M.carrier s
  | _, .var s i   => varMeaning M s i v
  | _, .const s c => constM M s c v
  | _, .func f ts => funM M f (fun i => fun w => msTermEval M w (ts i)) v

-- ===================================================================
-- Definition 10.3.6: Recursive formula meaning A_M = φ-hat(A)
-- ===================================================================

/-- Definition 10.3.6: The recursive meaning `A_M : [V → M] → BOOL` of a
formula `A`, i.e. `φ-hat(A)`; `A_M[v]` is the truth value of `A` under
the assignment `v`. Defined by recursion on `MSFormula`:

Atomic clauses:
  * `(⊥)_M[v] = F`;
  * `(P t_1…t_n)_M[v] = P_M((t_1)_M[v], …, (t_n)_M[v])`;
  * `(=_s t_1 t_2)_M[v] = T` iff `(t_1)_M[v] = (t_2)_M[v]` (the
    carrier-equality test is decided classically).

Nonatomic clauses (lifted operations of `𝓜`):
  * `(A * B)_M = *_𝓜(A_M, B_M)` for `* ∈ {∧, ∨, ⊃, ≡}`;
  * `(¬A)_M = ¬_𝓜(A_M)`;
  * `(∀_s x_i A)_M = (A_i^s)_𝓜(A_M)`;
  * `(∃_s x_i A)_M = (E_i^s)_𝓜(A_M)`.

Both `msTermEval` and `msFormulaEval` are the unique homomorphism
`φ-hat` (terms before formulae); `noncomputable` because of `forallM`/
`existsM` and the equality test. -/
@[blueprint "chap10__definition_10_3_6" (main := true)]
noncomputable def msFormulaEval {L : MSLanguage} (M : MSStructure L) :
    MSFormula L → MSSemBool M
  | .falsum         => fun _ => BoolVal.F
  | .pred P ts      =>
    predM M P (fun i => fun v => msTermEval M v (ts i))
  | .eq_ _ _ t1 t2  =>
    eqM M (fun v => msTermEval M v t1) (fun v => msTermEval M v t2)
  | .conj A B       => andM M (msFormulaEval M A) (msFormulaEval M B)
  | .disj A B       => orM M (msFormulaEval M A) (msFormulaEval M B)
  | .impl A B       => implM M (msFormulaEval M A) (msFormulaEval M B)
  | .equiv_ A B     => equivM M (msFormulaEval M A) (msFormulaEval M B)
  | .neg A          => negM M (msFormulaEval M A)
  | .all s i A      => forallM M (s := s) i (msFormulaEval M A)
  | .ex s i A       => existsM M (s := s) i (msFormulaEval M A)

-- ===================================================================
-- Definition 10.3.6: Rectified formulae
-- ===================================================================

/-- A structural formula address: 0 selects a unary body or a binary
left operand; 1 selects a binary right operand. The root address is `[]`. -/
abbrev MSFormulaPosition := List Nat

/-- Look up the actual syntax subtree at a formula address. -/
def msSubformulaAt {L : MSLanguage} :
    MSFormula L → MSFormulaPosition → Option (MSFormula L)
  | A, [] => some A
  | .conj B _, 0 :: pos | .disj B _, 0 :: pos
  | .impl B _, 0 :: pos | .equiv_ B _, 0 :: pos => msSubformulaAt B pos
  | .conj _ C, 1 :: pos | .disj _ C, 1 :: pos
  | .impl _ C, 1 :: pos | .equiv_ _ C, 1 :: pos => msSubformulaAt C pos
  | .neg B, 0 :: pos | .all _ _ B, 0 :: pos | .ex _ _ B, 0 :: pos =>
      msSubformulaAt B pos
  | _, _ => none

/-- A variable occurrence is either a quantifier's binder position or a
variable inside an atomic argument. Atomic and function arguments use
zero-based indices; equality has arguments 0 and 1. -/
inductive MSVariableOccurrence where
  | atom (formulaPos : MSFormulaPosition) (argument : Nat) (termPos : List Nat)
  | binder (formulaPos : MSFormulaPosition)

/-- The formula address containing a variable occurrence. -/
def MSVariableOccurrence.formulaPos : MSVariableOccurrence → MSFormulaPosition
  | .atom p _ _ => p
  | .binder p => p

/-- Look up a variable's sort and index at a term address. Constants and
invalid paths return `none`; function paths select an actual argument. -/
def msTermVariableAt {L : MSLanguage} :
    {s : L.SortType} → MSTerm L s → List Nat → Option (MSVar L)
  | _, .var s i, [] => some (s, i)
  | _, .func f ts, k :: pos =>
      if h : k < (L.funRank f).1.length then
        msTermVariableAt (ts ⟨k, h⟩) pos
      else none
  | _, _, _ => none

/-- Look up the sort/index pair of an atomic-term or binder occurrence.
Binder positions include vacuous quantifiers. Invalid addresses return `none`. -/
def msVariableAt {L : MSLanguage} (A : MSFormula L)
    (occ : MSVariableOccurrence) : Option (MSVar L) :=
  match occ with
  | .binder p =>
      match msSubformulaAt A p with
      | some (.all s i _) | some (.ex s i _) => some (s, i)
      | _ => none
  | .atom p argument termPos =>
      match msSubformulaAt A p with
      | some (.pred P ts) =>
          if h : argument < (L.predArity P).length then
            msTermVariableAt (ts ⟨argument, h⟩) termPos
          else none
      | some (.eq_ _ _ t u) =>
          match argument with
          | 0 => msTermVariableAt t termPos
          | 1 => msTermVariableAt u termPos
          | _ => none
      | _ => none

end LCS.FirstOrder.ManySorted.Semantics
