import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Equality.SystemGEq
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Gentzen
import LCS.FirstOrder.ManySorted.Equality
import Attach
import LCS.FirstOrder.ManySorted.Equality.Reduction.ProofsStamp

/-! # FirstOrder.ManySorted.Equality.Reduction
    Formalization of Chapter 10, Subsection 10.5.4 (Reduction of
    Many-Sorted Logic to One-Sorted Logic).

    The translation of a many-sorted language L into a one-sorted
    language L' via domain predicates D_s, the recursive relativization
    of quantified formulae, the set MS of domain-nonemptiness, function
    closure and constant-typing axioms, and the provability-preservation result
    (Lemma 10.5.2).

    Enderton's reduction: the one-sorted target is the EXISTING §5.x
    first-order formalization (LCS.FirstOrder.Basic.Language,
    LCS.FirstOrder.SyntaxN.FormulaN, LCS.FirstOrder.Gentzen.Sequent /
    sequentProvableExtNoEq, and LCS.FirstOrder.Equality.sequentProvableEq).
    The source is the six-connective presentation of §10.2 syntax with
    §10.4 G or §10.5 G= proofs. Consequence uses finite support from an
    arbitrary theory, with shared free-variable guards on the target side.

    `msReductionToOneSorted` (Lemma 10.5.2) can be used to transfer
    one-sorted metatheorems (compactness, model existence,
    Löwenheim-Skolem) to many-sorted first-order logic.

    Builds on §10.5 system G_= (LCS.FirstOrder.ManySorted.Equality).

    Source: Logic for Computer Science, Gallier 2015.
-/

namespace LCS.FirstOrder.ManySorted.Equality.Reduction

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Gentzen

-- ===================================================================
-- Lemma 10.5.2: building the translated one-sorted language L'
-- ===================================================================

/-- Lemma 10.5.2 (companion): the function symbols of the translated
one-sorted language L' are exactly the function symbols of L. Sorts are
erased; only the LENGTH of the arity string survives (the function symbol
keeps its identity, its sort discipline is re-imposed only via the MS
function-closure axiom). -/
@[blueprint "chap10__lemma_10_5_2"]
abbrev OneSortedFun (L : MSLanguage) : Type := L.funSymbols

/-- Lemma 10.5.2 (companion): the constants of L' are the disjoint union
over all sorts of the per-sort constant sets `CS_s` of L. Flattens the
sort-indexed family `constSymbols : SortType → Type` of `MSLanguage` into
a single unindexed one-sorted constant type, since one-sorted `Language`
has an unindexed `constSymbols : Type`. -/
@[blueprint "chap10__lemma_10_5_2"]
abbrev OneSortedConst (L : MSLanguage) : Type :=
  Σ s : L.SortType, L.constSymbols s

/-- Lemma 10.5.2 (companion): the predicate symbols of L' are the ORIGINAL
predicate symbols of L (constructor `orig`) PLUS one new unary domain
predicate `D_s` for each sort s (constructor `domain`). This is the
"add domain predicate symbols D_s, one for each sort" step of Enderton's
construction; the `domain` constructor realizes the domain predicate
symbol `D_s` keyword. -/
@[blueprint "chap10__lemma_10_5_2"]
inductive OneSortedPred (L : MSLanguage) : Type where
  /-- An original many-sorted predicate symbol `P`, re-used in L'. -/
  | orig : L.predSymbols → OneSortedPred L
  /-- The new unary domain predicate symbol `D_s` for sort `s`. -/
  | domain : L.SortType → OneSortedPred L

/-- Lemma 10.5.2 (companion): the translated one-sorted language L'. Builds
a one-sorted `Language` from the many-sorted L by adding the domain
predicate symbols `D_s` and erasing sort information from the arities:
`funArity f` is the number of arguments of `f` (the arity string LENGTH,
output sort dropped), `constSymbols` is the Σ-flattened constant family,
`predSymbols` is `orig P` ⊕ `domain s`, each domain predicate `D_s` is
unary (arity 1) while the original predicate `P` keeps its argument count,
and `hasEquality` is preserved. The lost sort information is recovered at
the formula level by the domain predicates. -/
@[blueprint "chap10__lemma_10_5_2"]
def msToOneSortedLang (L : MSLanguage) : Language where
  funSymbols := OneSortedFun L
  funArity f := (L.funRank f).1.length
  constSymbols := OneSortedConst L
  predSymbols := OneSortedPred L
  predArity := fun
    | .orig P => (L.predArity P).length
    | .domain _ => 1
  hasEquality := L.hasEquality

-- ===================================================================
-- Lemma 10.5.2: the recursive term translation
-- ===================================================================

/-- Lemma 10.5.2 (companion): the recursive translation of a many-sorted
term (of any sort s) into a one-sorted term of L', parameterized by an
INJECTIVE variable renaming `ν : L.SortType × Nat → Nat`. By recursion on
`MSTerm`: a variable `var s i` becomes `Term.var (ν (s, i))` (the sort tag
is FOLDED INTO the one-sorted index via `ν`, since one-sorted variables are
sort-free); a constant `const s c` becomes the flattened `Term.const ⟨s, c⟩`;
a function application `func f ts` becomes
`Term.func f (fun i => translate (ts i))`. The function symbol is preserved
and the dependent `Fin`-indexed argument family is mapped pointwise — the
index type `Fin ((msToOneSortedLang L).funArity f)` equals
`Fin (L.funRank f).1.length` definitionally, so no transport is needed.
This is a REAL recursive function: the term tree structure is preserved
while the per-node sort information is collapsed into the renamed index.

ν-RENAMING (issue c79e2e42, the unblock). The earlier translation dropped
the sort entirely (`var s i ↦ Term.var i`), so distinct sorted variables
`(s, i)` and `(s', i)` collapsed to the SAME one-sorted variable `i`. By
threading an INJECTIVE `ν`, distinct sorted variables map to distinct
one-sorted variables `ν (s, i) ≠ ν (s', i)`, which is exactly what the
substitution-commutation and eigenvariable-freshness lemmas need (see
`msTermTranslate_subst_comm`, `msFormulaFVN_translate_subset`). The
injectivity of `ν` is carried as a faithful precondition `hν` on the
lemmas that need it, NOT baked into the definition (so the definition stays
total and applicable to any `ν`). -/
@[blueprint "chap10__lemma_10_5_2"]
def msTermTranslate (L : MSLanguage) (ν : L.SortType × Nat → Nat) :
    {s : L.SortType} → MSTerm L s → Term (msToOneSortedLang L)
  | _, .var s i => Term.var (ν (s, i))
  | _, .const s c => Term.const ⟨s, c⟩
  | _, .func f ts => Term.func f (fun i => msTermTranslate L ν (ts i))

-- ===================================================================
-- Lemma 10.5.2: the domain atom D_s(t)
-- ===================================================================

/-- Lemma 10.5.2 (companion): the one-sorted atomic formula `D_s(t)` —
applies the domain predicate symbol of sort `s` to the single argument
term `t`. This named builder realizes the textbook notation `D_s(x)` used
both in the quantifier guards (`msFormulaTranslate`) and in the MS axioms
(`msDomainNonemptyAxiom`, `msFuncClosureAxiom`); it is the single shared
occurrence of "apply domain predicate `D_s`". The argument vector is the
constant-`t` family over `Fin ((msToOneSortedLang L).predArity (.domain s)) = Fin 1`. -/
@[blueprint "chap10__lemma_10_5_2"]
def msDomainAtom (L : MSLanguage) (s : L.SortType)
    (t : Term (msToOneSortedLang L)) : FormulaN (msToOneSortedLang L) :=
  FormulaN.predN (OneSortedPred.domain s) (fun _ => t)

-- ===================================================================
-- Lemma 10.5.2: the recursive formula translation A ↦ A'
-- ===================================================================

/-- Lemma 10.5.2: the recursive formula translation `A ↦ A'` — the heart of
the reduction. By recursion on `MSFormula L`, exhaustive over all 10
constructors:

* `falsum` becomes a canonical one-sorted contradiction
  `FormulaN.falsum (D_{someSort}(x_0))` = `(D ∧ ¬D)` (`FormulaN` has no
  falsum constructor; falsum is NOT silently dropped);
* `pred P ts` becomes `predN (orig P) (fun i => msTermTranslate (ts i))`
  (original predicate application with translated arguments; the index
  types match since `(msToOneSortedLang L).predArity (.orig P) = (L.predArity P).length`);
* `eq_ hL s t1 t2` becomes `eq_ hL (translate t1) (translate t2)`
  (equality preserved; `hasEquality` is preserved by `msToOneSortedLang`,
  so the proof `hL` transports directly);
* `conj`/`disj`/`impl`/`neg` recurse structurally;
* `equiv_ A B` becomes `conj (impl A' B') (impl B' A')` (`FormulaN` has no
  `equiv_` constructor, so the §5.3.8 abbreviation is inlined);
* the TWO quantifier cases are the essential rewrites:
  `all s x B ↦ ∀x (D_s(x) ⊃ B')` and `ex s x B ↦ ∃x (D_s(x) ∧ B')`.

This function is NOT the identity: on every quantifier it inserts a fresh
domain-predicate guard `D_s(x)`, so its output differs structurally from a
naive sort-erasure (Pattern-3 "algorithms must be real").

ν-RENAMING. Threaded through `msTermTranslate`; the two quantifier cases
bind and guard the RENAMED variable `ν (s, x)`:
`all s x B ↦ ∀_{ν(s,x)} (D_s(x_{ν(s,x)}) ⊃ B')` and
`ex s x B ↦ ∃_{ν(s,x)} (D_s(x_{ν(s,x)}) ∧ B')`. -/
@[blueprint "chap10__lemma_10_5_2"]
def msFormulaTranslate (L : MSLanguage) (ν : L.SortType × Nat → Nat) :
    MSFormula L → FormulaN (msToOneSortedLang L)
  | .falsum =>
      FormulaN.falsum (msDomainAtom L L.someSort (Term.var (ν (L.someSort, 0))))
  | .pred P ts =>
      FormulaN.predN (OneSortedPred.orig P) (fun i => msTermTranslate L ν (ts i))
  | .eq_ hL _ t1 t2 =>
      FormulaN.eq_ hL (msTermTranslate L ν t1) (msTermTranslate L ν t2)
  | .conj A B =>
      FormulaN.conj (msFormulaTranslate L ν A) (msFormulaTranslate L ν B)
  | .disj A B =>
      FormulaN.disj (msFormulaTranslate L ν A) (msFormulaTranslate L ν B)
  | .impl A B =>
      FormulaN.impl (msFormulaTranslate L ν A) (msFormulaTranslate L ν B)
  | .equiv_ A B =>
      FormulaN.conj
        (FormulaN.impl (msFormulaTranslate L ν A) (msFormulaTranslate L ν B))
        (FormulaN.impl (msFormulaTranslate L ν B) (msFormulaTranslate L ν A))
  | .neg A =>
      FormulaN.neg (msFormulaTranslate L ν A)
  | .all s x B =>
      FormulaN.all (ν (s, x))
        (FormulaN.impl (msDomainAtom L s (Term.var (ν (s, x))))
          (msFormulaTranslate L ν B))
  | .ex s x B =>
      FormulaN.ex (ν (s, x))
        (FormulaN.conj (msDomainAtom L s (Term.var (ν (s, x))))
          (msFormulaTranslate L ν B))

-- ===================================================================
-- Lemma 10.5.2: the many-sorted axiom set MS
-- ===================================================================

/-- Lemma 10.5.2 (companion): MS clause (1), the domain-nonemptiness axiom
`∃x D_s(x)` for a sort `s`. Asserts that sort `s` is nonempty in any model
of MS: there exists an element `x` (the renamed index `ν (s, 0)`)
satisfying the domain predicate `D_s`. One such axiom per sort `s ∈ S`.
ν-renamed: binds the renamed variable `ν (s, 0)` so the witness lives in
the same variable namespace as the translated quantifiers of sort `s`. -/
@[blueprint "chap10__lemma_10_5_2"]
def msDomainNonemptyAxiom (L : MSLanguage) (ν : L.SortType × Nat → Nat)
    (s : L.SortType) :
    FormulaN (msToOneSortedLang L) :=
  FormulaN.ex (ν (s, 0)) (msDomainAtom L s (Term.var (ν (s, 0))))

/-- Lemma 10.5.2 (companion): the exact right-nested conjunction
`D_{s₀}(x₀) ∧ … ∧ D_{sₙ}(xₙ)` for a nonempty argument-sort list.
Argument i uses the variable ν(sᵢ,i). A singleton contributes just its
atom; the nonempty rank ensures that the empty-list default is unused. -/
@[blueprint "chap10__lemma_10_5_2"]
def msDomainGuardConj (L : MSLanguage) (ν : L.SortType × Nat → Nat)
    (sorts : List L.SortType) (hne : sorts ≠ []) :
    FormulaN (msToOneSortedLang L) :=
  LCS.FirstOrder.Equality.conjoinFormulae
    (msDomainAtom L (sorts.head hne) (Term.var (ν (sorts.head hne, 0))))
    ((List.finRange sorts.length).map fun i =>
      msDomainAtom L (sorts.get i) (Term.var (ν (sorts.get i, i.val))))

/-- Lemma 10.5.2 (companion): MS clause (2), the function-closure axiom for a
function symbol `f` of rank `(s_1…s_n, s) = L.funRank f`. Builds
`∀x_1…∀x_n (D_{s_1}(x_1) ∧ … ∧ D_{s_n}(x_n) ⊃ D_s(f(x_1,…,x_n)))`: the
guard conjunction (over the argument sorts `sorts = (L.funRank f).1`)
implies that `f` applied to the argument variables `x_0,…,x_{n-1}` lands in
the output sort's domain `D_s` (`s = (L.funRank f).2`); then `n` universal
quantifiers `∀x_0…∀x_{n-1}` are prefixed. One such axiom per function
symbol `f`. Asserts that `f` maps domain elements of the argument sorts
into the result sort. ν-renamed: argument `i` (of sort `sorts.get i`) is
the renamed one-sorted variable `ν (sorts.get i, i)`, bound by the prefixed
universal quantifiers and used as the `i`-th argument of `f`. -/
@[blueprint "chap10__lemma_10_5_2"]
def msFuncClosureAxiom (L : MSLanguage) (ν : L.SortType × Nat → Nat)
    (f : L.funSymbols) :
    FormulaN (msToOneSortedLang L) :=
  let sorts := (L.funRank f).1
  let outSort := (L.funRank f).2
  let n := sorts.length
  let body : FormulaN (msToOneSortedLang L) :=
    FormulaN.impl
      (msDomainGuardConj L ν sorts (L.funRank_nonempty f))
      (msDomainAtom L outSort
        (Term.func f (fun i => Term.var (ν (sorts.get i, i.val)))))
  (List.finRange n).foldr
    (fun i acc => FormulaN.all (ν (sorts.get i, i.val)) acc) body

/-- Lemma 10.5.2 (companion): constant typing D_s(c) for each c : s.
This is the adopted nullary completion of the printed MS closure scheme. -/
@[blueprint "chap10__lemma_10_5_2"]
def msConstTypingAxiom (L : MSLanguage) (c : OneSortedConst L) :
    FormulaN (msToOneSortedLang L) :=
  msDomainAtom L c.1 (Term.const c)

/-- Lemma 10.5.2 (companion): the full axiom set MS contains data-sort
nonemptiness, positive-arity function closure, and constant typing.
The domain predicates range over data sorts, with no disjointness or
covering requirement. -/
@[blueprint "chap10__lemma_10_5_2"]
def msAxioms (L : MSLanguage) (ν : L.SortType × Nat → Nat) :
    Set (FormulaN (msToOneSortedLang L)) :=
  fun B =>
    (∃ s : L.SortType, B = msDomainNonemptyAxiom L ν s) ∨
    (∃ f : L.funSymbols, B = msFuncClosureAxiom L ν f) ∨
    (∃ c : OneSortedConst L, B = msConstTypingAxiom L c)

/-- Lemma 10.5.2 (companion): the set translation T' — the image of a set T
of many-sorted formulae under the formula translation. Translates every
many-sorted formula in T into its one-sorted translation A'. ν-renamed. -/
@[blueprint "chap10__lemma_10_5_2"]
def msTheoryTranslate (L : MSLanguage) (ν : L.SortType × Nat → Nat)
    (T : Set (MSFormula L)) :
    Set (FormulaN (msToOneSortedLang L)) :=
  fun B => ∃ A, T A ∧ B = msFormulaTranslate L ν A

/-- Lemma 10.5.2 (companion): one shared typing guard for each sorted
variable free in T or A. The same ν names variables throughout the theory
and goal, preserving their common-assignment interpretation. -/
@[blueprint "chap10__lemma_10_5_2"]
def msSharedGuards (L : MSLanguage) (ν : L.SortType × Nat → Nat)
    (T : Set (MSFormula L)) (A : MSFormula L) :
    Set (FormulaN (msToOneSortedLang L)) :=
  fun B => ∃ p : MSVar L,
    (p ∈ msFormulaFV A ∨ ∃ C, T C ∧ p ∈ msFormulaFV C) ∧
    B = msDomainAtom L p.1 (Term.var (ν p))

/-- Lemma 10.5.2 (companion): T′ together with full MS and the shared
free-variable guards of T and A, possibly an infinite set of premises. -/
@[blueprint "chap10__lemma_10_5_2"]
def msReductionPremises (L : MSLanguage) (ν : L.SortType × Nat → Nat)
    (T : Set (MSFormula L)) (A : MSFormula L) :
    Set (FormulaN (msToOneSortedLang L)) :=
  fun B => msTheoryTranslate L ν T B ∨ msAxioms L ν B ∨ msSharedGuards L ν T A B

/-- Lemma 10.5.2 (companion): consequence from an arbitrary premise set
in many-sorted G, witnessed by a finite list of premises and a G-proof. -/
@[blueprint "chap10__lemma_10_5_2"]
def msTheoryProvableG {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.withoutEquality) (T : Set (MSFormula L)) (A : MSFormula L) : Prop :=
  ∃ Γ : List (MSFormula L), (∀ B ∈ Γ, T B) ∧
    msSequentProvable hL (MSSequentCore.mk Γ [A])

/-- Lemma 10.5.2 (companion): finite-premise consequence in many-sorted
G=, using the equality proof tree on the selected finite sequent. -/
@[blueprint "chap10__lemma_10_5_2"]
def msTheoryProvableEq {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.hasEquality = true) (T : Set (MSFormula L)) (A : MSFormula L) : Prop :=
  ∃ Γ : List (MSFormula L), (∀ B ∈ Γ, T B) ∧
    Nonempty (MSGEqProofTree hL (MSSequentCore.mk Γ [A]))

/-- Lemma 10.5.2 (companion): arbitrary-set consequence in one-sorted G,
with finite proof support under the chapter 5 extended-rule convention. -/
@[blueprint "chap10__lemma_10_5_2"]
def oneSortedTheoryProvableG {L : Language} (hL : L.withoutEquality)
    (T : Set (FormulaN L)) (A : FormulaN L) : Prop :=
  ∃ Γ : List (FormulaN L), (∀ B ∈ Γ, T B) ∧
    sequentProvableExtNoEq hL (Sequent.mk Γ [A])

/-- Lemma 10.5.2 (companion): arbitrary-set consequence in one-sorted G=,
with finite proof support and the actual chapter 5 equality proof predicate. -/
@[blueprint "chap10__lemma_10_5_2"]
def oneSortedTheoryProvableEq {L : Language} (hL : L.hasEquality = true)
    (T : Set (FormulaN L)) (A : FormulaN L) : Prop :=
  ∃ Γ : List (FormulaN L), (∀ B ∈ Γ, T B) ∧
    LCS.FirstOrder.Equality.sequentProvableEq hL (Sequent.mk Γ [A])

-- ===================================================================
-- Lemma 10.5.2: the reduction biconditional
-- ===================================================================

/-- Lemma 10.5.2: reduction of arbitrary open theories in the
six-connective presentation of equality-free G. With injective sorted
variable renaming, T proves A iff T′, full MS and the shared guards for
FV(T) ∪ FV(A) prove A′ in one-sorted G. Each proof uses finitely many
premises; neither T nor the shared guard set is required to be finite.
Primitive ⊥ and ≡ retain their total translation above and enter the
source calculus through the existing abbreviation-expansion interface. -/
@[attach_debt, blueprint "chap10__lemma_10_5_2" (main := true)]
theorem msReductionToOneSorted {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.withoutEquality)
    (ν : L.SortType × Nat → Nat) (hν : Function.Injective ν)
    (T : Set (MSFormula L)) (A : MSFormula L)
    (hT : ∀ B, T B → msIsSixConnective B) (hA : msIsSixConnective A) :
    msTheoryProvableG hL T A ↔
      oneSortedTheoryProvableG (L := msToOneSortedLang L) hL
        (msReductionPremises L ν T A) (msFormulaTranslate L ν A)

/-- Lemma 10.5.2 (companion): the same shared-guard reduction for G=.
Equality in the source and target uses their respective equality rules;
MS includes the typing axiom of every sorted constant. -/
@[attach_debt, blueprint "chap10__lemma_10_5_2"]
theorem msReductionToOneSortedEq {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.hasEquality = true)
    (ν : L.SortType × Nat → Nat) (hν : Function.Injective ν)
    (T : Set (MSFormula L)) (A : MSFormula L)
    (hT : ∀ B, T B → msIsSixConnective B) (hA : msIsSixConnective A) :
    msTheoryProvableEq hL T A ↔
      oneSortedTheoryProvableEq (L := msToOneSortedLang L) hL
        (msReductionPremises L ν T A) (msFormulaTranslate L ν A)

end LCS.FirstOrder.ManySorted.Equality.Reduction
