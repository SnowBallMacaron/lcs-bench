import LCS.Item
import LCS.Util
import LCS.SLD.FirstOrder
import Attach
import LCS.SLD.PrologSyntax.ProofsStamp

/-! # SLD.PrologSyntax — Prolog surface-syntax layer

    A thin surface-syntax layer over `FOHornClause` / `Term` that
    makes first-order Horn clauses and goals in Lean read like the
    Prolog programs users are familiar with.

    The atomic query interface follows §9.5.1; the remaining combinators
    provide surface notation for the clause and term constructors.

    ## What it provides

    **Term-level**
    - `pFin2 x y`, `pFin3 x y z` — Fin-indexed argument packagers
      (replacements for per-file `pair2` / `triple3`).
    - `prologList xs` and list-literal notation `⟦a, b, c⟧` and
      `⟦h ::: t⟧` (for `[h | t]` in Prolog) — but ONLY once the user
      has provided a `nil` and a `cons` operation via the helpers
      below.

    **Clause-level**
    - `fact` / `rule` / `goalClause` collect the displayed body atoms
      into extensional finite sets.

    **Query-level**
    - `?- atom` denotes an open positive atomic query.
    - `AtomicQuery.toGoal` translates its negation to a negative clause.

    ## Usage pattern

    In a client file, a user:
    1. Defines their language `L : Language`.
    2. Declares per-language smart constructors for predicate atoms,
       constants, and function symbols. Predicate builders return
       `FOAtom`; these constructors are domain-specific and can't be
       generic — `nil`, `cons`, `succ`, `zero`, etc. vary per file.
    3. Uses the generic combinators here to assemble clauses, goals,
       and queries in a more Prolog-ish form.

    See `LCS/Examples/PrologAppend.lean` for a worked example. -/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace LCS.SLD.PrologSyntax

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FOResolution.ClauseForm
open LCS.SLD.FirstOrder

-- ===================================================================
-- Fin-indexed argument packagers (arity 1, 2, 3 cover most Prolog
-- predicates and functions; add larger arities as needed).
-- ===================================================================

/-- Package one term into a `Fin 1 → Term L` argument tuple — e.g.
    for a unary function symbol like `succ/1`. -/
def pFin1 {L : Language} (x : Term L) : Fin 1 → Term L
  | ⟨0, _⟩ => x

/-- Package two terms into a `Fin 2 → Term L` argument tuple — e.g.
    for a binary function symbol like `cons/2`. -/
def pFin2 {L : Language} (x y : Term L) : Fin 2 → Term L
  | ⟨0, _⟩ => x
  | ⟨1, _⟩ => y

/-- Package three terms into a `Fin 3 → Term L` argument tuple — e.g.
    for a ternary predicate like `append/3` or `add/3`. -/
def pFin3 {L : Language} (x y z : Term L) : Fin 3 → Term L
  | ⟨0, _⟩ => x
  | ⟨1, _⟩ => y
  | ⟨2, _⟩ => z

/-- Package four terms into a `Fin 4 → Term L` argument tuple. -/
def pFin4 {L : Language} (x y z w : Term L) : Fin 4 → Term L
  | ⟨0, _⟩ => x
  | ⟨1, _⟩ => y
  | ⟨2, _⟩ => z
  | ⟨3, _⟩ => w

/-- Package five terms into a `Fin 5 → Term L` argument tuple. -/
def pFin5 {L : Language} (x y z w v : Term L) : Fin 5 → Term L
  | ⟨0, _⟩ => x
  | ⟨1, _⟩ => y
  | ⟨2, _⟩ => z
  | ⟨3, _⟩ => w
  | ⟨4, _⟩ => v

-- ===================================================================
-- Horn-clause aliases matching Prolog syntax
--   fact      ≡   head.
--   rule h b  ≡   head :- b₁, b₂, ..., bₙ.
--   goalClause b ≡ :- b₁, b₂, ..., bₙ.
-- ===================================================================

/-- Prolog fact clause: `head.` — no body. -/
abbrev fact {L : Language} (hNoEq : L.withoutEquality) (head : FOAtom L hNoEq) : FOHornClause L hNoEq :=
  (FOHornClause.fact (hNoEq := by all_goals exact hNoEq)) head

/-- Prolog rule clause: `head :- b₁, b₂, …, bₙ.`. -/
abbrev rule {L : Language} (hNoEq : L.withoutEquality) (head : FOAtom L hNoEq) (body : List (FOAtom L hNoEq)) :
    FOHornClause L hNoEq :=
  (FOHornClause.rule (hNoEq := by all_goals exact hNoEq)) head (LCS.Finset.ofList body)

/-- The negative program goal clause `:- b₁, b₂, …, bₙ.`. -/
abbrev goalClause {L : Language} (hNoEq : L.withoutEquality) (body : List (FOAtom L hNoEq)) : FOHornClause L hNoEq :=
  (FOHornClause.goal (hNoEq := by all_goals exact hNoEq)) (LCS.Finset.ofList body)

/-- The open positive atomic query of §9.5.1 (SQ31). The equality-free
    language boundary restricts its atom to a predicate application. -/
@[blueprint "chap9__definition_9_5_1"]
structure AtomicQuery (L : Language) (hNoEq : L.withoutEquality) where
  atom : FOAtom L hNoEq

/-- The positive matrix, before existential closure or answer substitution. -/
@[blueprint "chap9__definition_9_5_1"]
def AtomicQuery.matrix {L : Language} {hNoEq : L.withoutEquality}
    (q : AtomicQuery L hNoEq) : FormulaN L := q.atom.toFormula

/-- Output variables are exactly the free variables of the open matrix (SQ31). -/
@[blueprint "chap9__definition_9_5_1"]
def AtomicQuery.outputVars {L : Language} {hNoEq : L.withoutEquality}
    (q : AtomicQuery L hNoEq) : Set Nat :=
  LCS.FirstOrder.SyntaxN.Variables.formulaFVN q.matrix

/-- Negating the atomic query produces the negative Horn goal `:- G`;
    the goal's universal closure is interpreted by the Horn semantics (SQ25). -/
@[blueprint "chap9__definition_9_5_1"]
def AtomicQuery.toGoal {L : Language} {hNoEq : L.withoutEquality}
    (q : AtomicQuery L hNoEq) : FOHornClause L hNoEq :=
  FOHornClause.goal (hNoEq := hNoEq) (LCS.Finset.singleton q.atom)

/-- The source query marker keeps the positive atom open (§9.5.1). -/
@[blueprint "chap9__definition_9_5_1"]
def goal {L : Language} (hNoEq : L.withoutEquality) (atom : FOAtom L hNoEq) :
    AtomicQuery L hNoEq := ⟨atom⟩

-- ===================================================================
-- Rule and query notation — variadic, comma-separated bodies
-- ===================================================================

/-- Prolog rule clause: `head :- b₁, b₂, …, bₙ`. Expands to
    `rule _ head [b₁, b₂, …, bₙ]`. For a fact, use `fact hNoEq head`
    (Lean cannot reclaim `.` as a clause terminator — it's already
    used for field access and namespace). -/
syntax:10 term:11 " :- " sepBy1(term:11, ", ") : term

macro_rules
  | `($head:term :- $[$bodies:term],*) => `(rule _ $head [$[$bodies],*])

/-- Negative goal-clause notation. -/
syntax:10 ":- " sepBy1(term:11, ", ") : term

macro_rules
  | `(:- $[$bodies:term],*) => `(goalClause _ [$[$bodies],*])

/-- Open positive atomic query notation. -/
syntax:10 "?- " term:11 : term

macro_rules
  | `(?- $atom:term) => `(goal _ $atom)

-- ===================================================================
-- Separating renaming / MGU builders
-- ===================================================================

/-- The identity substitution — leaves every variable unchanged. -/
def idSubst {L : Language} : Nat → Term L := Term.var

/-- Override substitution: `subst[[n ↦ t]]` returns a new substitution
    equal to `subst` except at index `n`, where it returns `t`. -/
def overrideSubst {L : Language}
    (subst : Nat → Term L) (n : Nat) (t : Term L) : Nat → Term L :=
  fun m => if m = n then t else subst m

/-- Single-binding override:  `ovr subst n t` is `subst` with `n ↦ t`. -/
abbrev ovr {L : Language} (subst : Nat → Term L) (n : Nat) (t : Term L) :
    Nat → Term L :=
  overrideSubst subst n t

/-- Substitution-literal notation:
    `⟦ n₁ ↦ t₁ | n₂ ↦ t₂ | n₃ ↦ t₃ ⟧` builds the substitution that
    sends `n₁ → t₁`, `n₂ → t₂`, `n₃ → t₃`, and every other variable
    to itself (via `idSubst`). Right-associative nesting of `ovr`. -/
syntax "⟦ " sepBy1(term " ↦ " term, " | ") " ⟧" : term

macro_rules
  | `(⟦ $[ $ns:term ↦ $ts:term ]|* ⟧) => do
      let mut acc ← `(idSubst)
      for (n, t) in ns.zip ts do
        acc ← `(ovr $acc $n $t)
      return acc

/-- Variable-name convention:
    uppercase `V 0`, `V 1`, … are the Prolog-style variables,
    mirroring Prolog's convention that identifiers starting with a
    capital letter are logic variables. Clients can introduce their
    own readable aliases (e.g. `def X := V 0`, `def Xs := V 1`). -/
abbrev V {L : Language} (n : Nat) : Term L := Term.var n

-- ===================================================================
-- Sanity check: the substitution-literal notation parses.
-- ===================================================================

section SanityChecks

/-- Empty-language smoke test: `⟦ 0 ↦ V 7 ⟧` makes a single-binding subst. -/
example (L : Language) : Nat → Term L :=
  ⟦ 0 ↦ V 7 ⟧

/-- Multi-binding smoke test. -/
example (L : Language) : Nat → Term L :=
  ⟦ 0 ↦ V 7 | 1 ↦ V 8 | 2 ↦ V 9 ⟧

end SanityChecks

end LCS.SLD.PrologSyntax
end
