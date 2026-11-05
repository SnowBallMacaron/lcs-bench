import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import Attach
import LCS.FirstOrder.ManySorted.Semantics.Substitution.ProofsStamp

/-! # FirstOrder.ManySorted.Semantics.Substitution
    Formalization of Chapter 10, Subsections 10.3.3-10.3.5.

    The alternate substitution-based semantics for quantifiers
    (Lemma 10.3.1) and the dependence of a formula's meaning only on its
    free variables (Lemma 10.3.2). Subformulae and rectified formulae
    (§10.3.5) generalize §5.3.6 and are handled in the sibling core
    semantics module.

    Lemma 10.3.1 (§10.3.3) characterizes the sorted quantifiers by
    quantifying over the SEMANTIC DOMAIN elements `m ∈ M_s` (each named by
    a fresh naming constant), exactly as Gallier states it — NOT over the
    syntactic naming terms `t : MSTerm L s` (which would be strictly weaker
    when not every element of `M_s` is term-denotable). To express "`B` with
    the element `m` substituted for `x_i`" syntactically we adjoin, for each
    sort `s`, a fresh naming constant for every element of `M_s`, generalizing
    the one-sorted extended language `L(M)` (§5.3.8) to the many-sorted
    setting. The quantifier clauses and their substitution bridges range
    over arbitrary formulas and terms of this one fixed L(M), including
    expressions that already contain naming constants.

    Builds on §10.3 core semantics (LCS.FirstOrder.ManySorted.Semantics):
    MSStructure, MSAssignment, msFormulaEval, msTermEval, msAssignUpdate,
    forallM, existsM, MSSemBool, BoolVal, andM/orM/implM/equivM/negM. Uses
    §10.2 (LCS.FirstOrder.ManySorted): MSFormula, MSTerm, MSVar,
    msFormulaSubst, msTermSubst, msFormulaFV, msTermFV, MSFormula.isSentence.

    Source: Logic for Computer Science, Gallier 2015.
-/

namespace LCS.FirstOrder.ManySorted.Semantics.Substitution

open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.Propositional.Semantics

-- ===================================================================
-- Many-sorted extended language L(M) with naming constants
-- (many-sorted analogue of §5.3.8 extendedLanguage/namingConst/
--  extendedInterp; exists to STATE Lemma 10.3.1).
-- ===================================================================

/-- Lemma 10.3.1 (required helper, many-sorted analogue of one-sorted
`extendedLanguage`): given a many-sorted language `L` and an S-indexed
family `M : L.SortType → Type` of domains, the extended language `L(M)`
adjoins, for EACH sort `s`, a fresh naming constant for every element of
`M s`. Concretely the sort-`s` constants become `L.constSymbols s ⊕ M s`;
all other components (sorts, functions, predicates, equality flag) are
unchanged. This is the §10.3.3 device for naming the domain elements
`m ∈ M_s` over which Lemma 10.3.1 quantifies. -/
@[blueprint "chap10__lemma_10_3_1"]
def msExtendedLanguage (L : MSLanguage) (M : L.SortType → Type) :
    MSLanguage where
  SortType := L.SortType
  someSort := L.someSort
  funSymbols := L.funSymbols
  funRank := L.funRank
  funRank_nonempty := L.funRank_nonempty
  constSymbols := fun s => L.constSymbols s ⊕ M s
  predSymbols := L.predSymbols
  predArity := L.predArity
  hasEquality := L.hasEquality

/-- Lemma 10.3.1 (required helper): `DecidableEq` for the sorts of the
extended language `L(M)`. Its `SortType` is definitionally `L.SortType`, so
the instance transports directly from `DecidableEq L.SortType`. Needed
because `msTermSubst`/`msFormulaSubst` over `L(M)` require a sort-equality
decision. -/
@[blueprint "chap10__lemma_10_3_1"]
instance instDecidableEqMSExtendedSortType {L : MSLanguage}
    {M : L.SortType → Type} [DecidableEq L.SortType] :
    DecidableEq (msExtendedLanguage L M).SortType :=
  inferInstanceAs (DecidableEq L.SortType)

/-- Lemma 10.3.1 (required helper, many-sorted analogue of one-sorted
`namingConst`): the naming constant of the element `m : M s`, as a term of
sort `s` in the extended language `L(M)`. The sort of the naming constant
is exactly the sort `s` of the element it names, so substituting it for a
sort-`s` variable typechecks. -/
@[blueprint "chap10__lemma_10_3_1"]
def msNamingConst {L : MSLanguage} {M : L.SortType → Type} {s : L.SortType}
    (m : M s) : MSTerm (msExtendedLanguage L M) s :=
  MSTerm.const (L := msExtendedLanguage L M) s (Sum.inr m)

/-- Lemma 10.3.1 (required helper, many-sorted analogue of one-sorted
`extendedInterp`): the extended structure `M(·)` over the language
`L(M.carrier)`. Original constants are interpreted as before; the naming
constant of an element `m ∈ M_s` is interpreted as `m` itself. Carriers,
function and predicate interpretations are inherited unchanged from `M`. -/
@[blueprint "chap10__lemma_10_3_1"]
def msExtendedInterp {L : MSLanguage} (M : MSStructure L) :
    MSStructure (msExtendedLanguage L M.carrier) where
  carrier := M.carrier
  carrierNonempty := M.carrierNonempty
  interpFunc := M.interpFunc
  interpConst := fun s c =>
    match c with
    | Sum.inl c => M.interpConst s c
    | Sum.inr m => m
  interpPred := M.interpPred

/-- Lemma 10.3.1 (required helper, many-sorted analogue of one-sorted
`namingConstEval`): for any assignment `v`, the naming constant of
`m ∈ M_s` evaluates to `m` itself in the extended structure:
`(m)_{M(·)}[v] = m`. The semantic anchor that turns substitution of a
naming constant into the modified-assignment update `v[x_i := m]`. -/
@[blueprint "chap10__lemma_10_3_1"]
theorem msNamingConstEval {L : MSLanguage} (M : MSStructure L)
    (v : MSAssignment (msExtendedInterp M)) {s : L.SortType}
    (m : M.carrier s) :
    msTermEval (msExtendedInterp M) v (msNamingConst m) = m 

-- ===================================================================
-- Lifting terms/formulae from L to the extended language L(M)
-- ===================================================================

/-- Lemma 10.3.1 (required helper, many-sorted analogue of one-sorted
`liftTerm`): lift a term from `L` to the extended language `L(M)`, mapping
each original constant `c` to `Sum.inl c` and leaving variables and
function applications structurally unchanged (lifting arguments
recursively). The sort is preserved. -/
@[blueprint "chap10__lemma_10_3_1"]
def msLiftTermExt {L : MSLanguage} (M : L.SortType → Type) :
    {s : L.SortType} → MSTerm L s → MSTerm (msExtendedLanguage L M) s
  | _, .var s i   => MSTerm.var (L := msExtendedLanguage L M) s i
  | _, .const s c =>
      MSTerm.const (L := msExtendedLanguage L M) s (Sum.inl c)
  | _, .func f ts =>
      MSTerm.func (L := msExtendedLanguage L M) f (fun i => msLiftTermExt M (ts i))

/-- Lemma 10.3.1 (required helper, many-sorted analogue of one-sorted
`liftFormula`): lift a formula from `L` to the extended language `L(M)` by
lifting all embedded terms (via `msLiftTermExt`) and recursing through the
connectives and quantifiers. The equality flag is shared between `L` and
`L(M)`, so the `eq_` proof argument transfers unchanged. -/
@[blueprint "chap10__lemma_10_3_1"]
def msLiftFormulaExt {L : MSLanguage} (M : L.SortType → Type) :
    MSFormula L → MSFormula (msExtendedLanguage L M)
  | .falsum         => .falsum
  | .pred P ts      => .pred P (fun i => msLiftTermExt M (ts i))
  | .eq_ hL s t1 t2 => .eq_ hL s (msLiftTermExt M t1) (msLiftTermExt M t2)
  | .conj A B       => .conj (msLiftFormulaExt M A) (msLiftFormulaExt M B)
  | .disj A B       => .disj (msLiftFormulaExt M A) (msLiftFormulaExt M B)
  | .impl A B       => .impl (msLiftFormulaExt M A) (msLiftFormulaExt M B)
  | .equiv_ A B     => .equiv_ (msLiftFormulaExt M A) (msLiftFormulaExt M B)
  | .neg A          => .neg (msLiftFormulaExt M A)
  | .all s i A      => .all s i (msLiftFormulaExt M A)
  | .ex s i A       => .ex s i (msLiftFormulaExt M A)

-- ===================================================================
-- Lemma 10.3.1: Substitution-based semantics for sorted quantifiers
-- ===================================================================

/-- Lemma 10.3.1 (term-level bridge): for any term `r` over the fixed
extended language `L(M)`, evaluation under `v[x_i^s := m]` equals evaluation
of `r[name(m)/x_i^s]` under `v`, in the same naming structure `M(·)`.
The term may already contain arbitrary original or naming constants.
The domain element and replacement variable have the same sort. -/
@[blueprint "chap10__lemma_10_3_1"]
theorem msTermSubstEval {L : MSLanguage} [DecidableEq L.SortType]
    (M : MSStructure L) (v : MSAssignment (msExtendedInterp M))
    (s : L.SortType) (i : Nat) (m : M.carrier s) :
    {s' : (msExtendedLanguage L M.carrier).SortType} →
      (r : MSTerm (msExtendedLanguage L M.carrier) s') →
    msTermEval (msExtendedInterp M)
        (msAssignUpdate (msExtendedInterp M) v s i m)
        r =
      msTermEval (msExtendedInterp M) v
        (msTermSubst (L := msExtendedLanguage L M.carrier) s i
          (msNamingConst m) r) 

-- retained: used by LCS.FirstOrder.ManySorted.Gentzen.Calculus
/-- Lemma 10.3.1 (required helper): updating the variable `(s, i)` twice
collapses to the outer update — `v[x_i := m][x_i := a] = v[x_i := a]`. The
many-sorted analogue of the one-sorted `assignUpdate`-idempotence step used
in the matched-bound-variable subcase of the quantifier induction. -/
theorem msAssignUpdate_idem {L : MSLanguage} (M : MSStructure L)
    (v : MSAssignment M) (s : L.SortType) (i : Nat)
    (m a : M.carrier s) :
    msAssignUpdate M (msAssignUpdate M v s i m) s i a =
      msAssignUpdate M v s i a := by
-- BEGIN PROOF
  funext s'' j
  simp only [msAssignUpdate]
  by_cases h : s'' = s
  · subst h
    by_cases hj : j = i <;> simp [hj]
  · simp [h]

-- retained: used by LCS.FirstOrder.ManySorted.Gentzen.Calculus
/-- Lemma 10.3.1 (required helper): two updates at DISTINCT variables
commute — `v[x_i^s := m][x_j^{s'} := a] = v[x_j^{s'} := a][x_i^s := m]`
whenever `(s', j) ≠ (s, i)`. The many-sorted analogue of the one-sorted
`assignUpdate`-swap step used in the distinct-bound-variable subcase of the
quantifier induction. -/
theorem msAssignUpdate_swap {L : MSLanguage} (M : MSStructure L)
    (v : MSAssignment M) (s s' : L.SortType) (i j : Nat)
    (m : M.carrier s) (a : M.carrier s')
    (hne : ¬ (s' = s ∧ j = i)) :
    msAssignUpdate M (msAssignUpdate M v s i m) s' j a =
      msAssignUpdate M (msAssignUpdate M v s' j a) s i m := by
-- BEGIN PROOF
  funext s'' k
  simp only [msAssignUpdate]
  by_cases h1 : s'' = s' <;> by_cases h2 : s'' = s <;>
    by_cases hk1 : k = j <;> by_cases hk2 : k = i <;>
    simp_all <;> subst_vars <;> simp_all

/-- Lemma 10.3.1 (substitution-evaluation bridge): for every formula `B`
of the fixed extended language `L(M)` and every full assignment `v`,
evaluating `B` under `v[x_i^s := m]` equals evaluating `B[name(m)/x_i^s]`
under `v` in the same naming structure. Existing naming constants in `B`
keep their interpretations. The replacement is a closed same-sort constant,
so structural induction uses assignment-update commutation under quantifiers. -/
@[blueprint "chap10__lemma_10_3_1"]
theorem msFormulaSubstEval {L : MSLanguage} [DecidableEq L.SortType]
    (M : MSStructure L) (B : MSFormula (msExtendedLanguage L M.carrier))
    (v : MSAssignment (msExtendedInterp M))
    (s : L.SortType) (i : Nat) (m : M.carrier s) :
    msFormulaEval (msExtendedInterp M) B
        (msAssignUpdate (msExtendedInterp M) v s i m) =
      msFormulaEval (msExtendedInterp M)
        (msFormulaSubst B s i
          (msNamingConst m)) v 

/-- Lemma 10.3.1 part (1): for every formula `B` of the fixed language
`L(M)` and every full assignment `v`, `∀ x_i:s B` is true in `M(·)` iff
`B[name(m)/x_i^s]` is true there under `v` for every `m ∈ M_s`.
Both sides use the same naming language and structure, including when `B`
already contains names. This is the fixed-L(M) reading inherited from
Lemma 5.3.2. The substitution bridge realizes the assignment update. -/
@[blueprint "chap10__lemma_10_3_1" (main := true)]
theorem msForallSemantics {L : MSLanguage} [DecidableEq L.SortType]
    (M : MSStructure L) (B : MSFormula (msExtendedLanguage L M.carrier))
    (v : MSAssignment (msExtendedInterp M))
    (s : L.SortType) (i : Nat) :
    msFormulaEval (msExtendedInterp M)
        (MSFormula.all s i B) v = BoolVal.T ↔
      ∀ m : M.carrier s,
        msFormulaEval (msExtendedInterp M)
          (msFormulaSubst B s i
            (msNamingConst m)) v = BoolVal.T 

/-- Lemma 10.3.1 part (2): for every formula `B` of the fixed language
`L(M)` and every full assignment `v`, `∃ x_i:s B` is true in `M(·)` iff
`B[name(m)/x_i^s]` is true there under `v` for some `m ∈ M_s`.
Existing names in `B` and the substituted name are interpreted in the same
fixed structure; the witness ranges over the whole carrier of sort `s`. -/
@[blueprint "chap10__lemma_10_3_1"]
theorem msExistsSemantics {L : MSLanguage} [DecidableEq L.SortType]
    (M : MSStructure L) (B : MSFormula (msExtendedLanguage L M.carrier))
    (v : MSAssignment (msExtendedInterp M))
    (s : L.SortType) (i : Nat) :
    msFormulaEval (msExtendedInterp M)
        (MSFormula.ex s i B) v = BoolVal.T ↔
      ∃ m : M.carrier s,
        msFormulaEval (msExtendedInterp M)
          (msFormulaSubst B s i
            (msNamingConst m)) v = BoolVal.T 

-- ===================================================================
-- Lemma 10.3.2: Coincidence lemma for many-sorted formulae
-- ===================================================================

/-- Lemma 10.3.2 (term-level helper, many-sorted analogue of one-sorted
`termCoincidence`): a term's value depends only on the assignment's
values on the term's free variables. If `v1` and `v2` agree on every
free variable of the term `t` (each variable applied at its own sort
`y.1` and index `y.2`), then `t_M[v1] = t_M[v2]`.

Proved by induction on `t` (var: directly from the agreement
hypothesis; const: `rfl`; func: congruence + IH on each argument). Used
in the atomic (`pred`, `eq_`) cases of the formula induction. -/
@[blueprint "chap10__lemma_10_3_2"]
theorem msTermCoincidence {L : MSLanguage} (M : MSStructure L)
    {s : L.SortType} (t : MSTerm L s) (v1 v2 : MSAssignment M)
    (hAgree : ∀ y : MSVar L, y ∈ msTermFV t → v1 y.1 y.2 = v2 y.1 y.2) :
    msTermEval M v1 t = msTermEval M v2 t 



/-- Lemma 10.3.2: coincidence lemma for many-sorted formulae. Given a
formula `A` and two assignments `v1 v2 : MSAssignment M` that agree on
every FREE variable of `A` (`∀ y ∈ msFormulaFV A, v1 y.1 y.2 = v2 y.1
y.2`), the meaning of `A` is the same under both:

  `A_M[v1] = A_M[v2]`.

The truth value depends only on the values the assignment gives to the
free variables. Variables are `(sort, index)` pairs `MSVar L =
L.SortType × Nat`; the agreement applies the S-indexed assignment at the
variable's sort `y.1` and index `y.2`.

Many-sorted analogue of one-sorted `coincidenceLemma` (Lemma 5.3.3).
NON-TRIVIAL: the hypothesis and conclusion use DIFFERENT assignments
`v1 v2`, related only by `hAgree` restricted to the FREE variables, so
it is not `rfl`-provable. Proved by structural induction on `A`
generalizing `v1 v2` (atomic cases via `msTermCoincidence`; connectives
by congruence; quantifiers by the IH on the modified assignments, which
agree on the body's free variables). -/
@[blueprint "chap10__lemma_10_3_2" (main := true)]
theorem msCoincidenceLemma {L : MSLanguage} (M : MSStructure L)
    (A : MSFormula L) (v1 v2 : MSAssignment M)
    (hAgree : ∀ y : MSVar L, y ∈ msFormulaFV A → v1 y.1 y.2 = v2 y.1 y.2) :
    msFormulaEval M A v1 = msFormulaEval M A v2 

/-- Lemma 10.3.2 (consequence, many-sorted analogue of one-sorted
`sentenceTruthIndep`): a SENTENCE (closed formula, `FV(A) = ∅` via
`MSFormula.isSentence`) has assignment-independent meaning, since the
agreement hypothesis of `msCoincidenceLemma` is vacuously satisfied (no
free variables). Strengthens "equal meaning under agreeing assignments"
to unconditional equality for closed `A`. -/
@[blueprint "chap10__lemma_10_3_2"]
theorem msSentenceTruthIndep {L : MSLanguage} (M : MSStructure L)
    (A : MSFormula L) (hSent : MSFormula.isSentence A)
    (v1 v2 : MSAssignment M) :
    msFormulaEval M A v1 = msFormulaEval M A v2 

/-- §10.3.5, generalizing Lemma 5.3.4(i): universal bound-variable
renaming preserves meaning in every structure and assignment. The replacement
variable has the same sort, is free for the original variable in the arbitrary
formula `A`, and is absent from `FV(A) \ {x}`. This permits `y = x`. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msAlphaEquivUniv {L : MSLanguage} [DecidableEq L.SortType]
    (A : MSFormula L) (s : L.SortType) (x y : Nat)
    (hFree : msIsFreeFor A s x (MSTerm.var s y))
    (hFresh : (s, y) ∉ msFormulaFV A \ Set.singleton (s, x))
    (M : MSStructure L) (v : MSAssignment M) :
    msFormulaEval M (MSFormula.all s x A) v =
      msFormulaEval M (MSFormula.all s y (msFormulaSubst A s x (MSTerm.var s y))) v

/-- §10.3.5, generalizing Lemma 5.3.4(i): existential bound-variable
renaming preserves meaning in every structure and assignment. The replacement
variable has the same sort, is free for the original variable in the arbitrary
formula `A`, and is absent from `FV(A) \ {x}`. This permits `y = x`. -/
@[attach_debt, blueprint "chap10__lemma_10_3_2"]
theorem msAlphaEquivEx {L : MSLanguage} [DecidableEq L.SortType]
    (A : MSFormula L) (s : L.SortType) (x y : Nat)
    (hFree : msIsFreeFor A s x (MSTerm.var s y))
    (hFresh : (s, y) ∉ msFormulaFV A \ Set.singleton (s, x))
    (M : MSStructure L) (v : MSAssignment M) :
    msFormulaEval M (MSFormula.ex s x A) v =
      msFormulaEval M (MSFormula.ex s y (msFormulaSubst A s x (MSTerm.var s y))) v

end LCS.FirstOrder.ManySorted.Semantics.Substitution
