import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Semantics.Substitution
import LCS.Propositional.Semantics
import LCS.FirstOrder.ManySorted.Gentzen.Soundness
import Attach
import LCS.FirstOrder.ManySorted.Gentzen.Completeness.ProofsStamp

section
namespace LCS.FirstOrder.ManySorted.Gentzen
open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.Propositional.Semantics

-- ===================================================================
-- Theorem 10.4.1 (companion type): MSSignedFormula
-- ===================================================================

/-- Theorem 10.4.1 (companion): A signed many-sorted formula `T A` /
`F A`, used by the many-sorted Hintikka-set definition in the
completeness proof. Direct many-sorted analogue of one-sorted
`SignedFormula` (chap5 Def 5.4.3). -/
@[blueprint "chap10__theorem_10_4_1"]
inductive MSSignedFormula (L : MSLanguage) : Type where
  /-- The signed formula `T A` ("A is true"). -/
  | trueF : MSFormula L → MSSignedFormula L
  /-- The signed formula `F A` ("A is false"). -/
  | falseF : MSFormula L → MSSignedFormula L

-- ===================================================================
-- Theorem 10.4.1 (companion def): many-sorted Hintikka set
-- ===================================================================

/-- Theorem 10.4.1 (companion): A many-sorted Hintikka set — the
modification of the Hintikka-set definition "so that it applies to a
many-sorted algebra" (the textbook explicitly calls for this in the
completeness proof). Here `H` is an `S`-indexed family of per-sort
term-carriers `H s : Set (MSTerm L s)`, and the closure conditions
H0–H6 are sort-aware: in particular the quantifier conditions (H3 for
`∀`-true / `∃`-false universal premises, H4 for `∀`-false / `∃`-true
witness premises) instantiate over terms `t : MSTerm L s` of the sort
`s` matching the quantifier's bound variable, drawn from `H s`.

  * H0: no atomic formula and its conjugate both lie in `S`.
  * H1 (type-A / conjunctive): both components of a conjunctive signed
    formula are in `S` (covering `T (A ∧ B)`, `F (A ∨ B)`,
    `F (A ⊃ B)`, `T ¬A`, `F ¬A`).
  * H2 (type-B / disjunctive): at least one component of a disjunctive
    signed formula is in `S` (covering `F (A ∧ B)`, `T (A ∨ B)`,
    `T (A ⊃ B)`).
  * H3 (type-C / universal): if a universally-acting quantified signed
    formula is in `S`, its sort-`s` instance is in `S` for every
    `t ∈ H s`.
  * H4 (type-D / existential): if an existentially-acting quantified
    signed formula is in `S`, its sort-`s` instance is in `S` for some
    `t ∈ H s`.
  * H5: every variable `(s, i)` free in some formula of `S` has its
    variable term in `H s`.
  * H6: instantiation terms drawn from `H s` are free for the bound
    variable in every quantified formula of `S`.

Direct many-sorted analogue of one-sorted `IsHintikkaSet`
(chap5 Def 5.4.7), sort-indexed. Referenced by the completeness (→)
direction of `msGoedelExtendedCompletenessG`. -/
@[blueprint "chap10__theorem_10_4_1"]
def MSIsHintikkaSet (L : MSLanguage) [DecidableEq L.SortType]
    (H : (s : L.SortType) → Set (MSTerm L s))
    (S : Set (MSSignedFormula L)) : Prop :=
  -- H0: no atomic formula and its conjugate are both in S.
  (∀ A : MSFormula L, A.isAtomic →
    ¬ (MSSignedFormula.trueF A ∈ S ∧ MSSignedFormula.falseF A ∈ S)) ∧
  -- H0 (falsum): `⊥` is never signed true in S (the §5.4 condition
  -- `h0_falsum`; in the one-sorted normalized `FormulaN` there is no
  -- `falsum` constructor, so this clause is automatic there, but
  -- `MSFormula` has `⊥`, so it must be stated). `F ⊥ ∈ S` is allowed
  -- (consistent with `⊥` evaluating to F).
  (MSSignedFormula.trueF MSFormula.falsum ∉ S) ∧
  -- H0 (no equality): no `eq_` formula appears signed in S. §10.4 is the
  -- system WITHOUT equality (the §5.4 standing assumption `hNoEq`); the
  -- one-sorted normalized `FormulaN` carries equality only via `eq_`,
  -- excluded from Hintikka sets by `hNoEq`.
  (∀ (hL : L.hasEquality = true) (s : L.SortType) (t1 t2 : MSTerm L s),
    MSSignedFormula.trueF (MSFormula.eq_ hL s t1 t2) ∉ S ∧
    MSSignedFormula.falseF (MSFormula.eq_ hL s t1 t2) ∉ S) ∧
  -- H0 (no equivalence): no `≡` formula appears signed in S. The §5.4
  -- normalized signed-formula decomposition (type-A/type-B) does not
  -- cover `≡` (Gallier eliminates `≡` before the search/Hintikka stage),
  -- so a faithful Hintikka set contains no `≡` formula. In the one-sorted
  -- `FormulaN` there is no `equiv_` constructor (`h0_no_equiv` automatic);
  -- `MSFormula` has `≡`, so it must be stated.
  (∀ A B : MSFormula L,
    MSSignedFormula.trueF (MSFormula.equiv_ A B) ∉ S ∧
    MSSignedFormula.falseF (MSFormula.equiv_ A B) ∉ S) ∧
  -- H1 (conjunctive / type-A): both components in S.
  (∀ A B : MSFormula L,
    (MSSignedFormula.trueF (MSFormula.conj A B) ∈ S →
      MSSignedFormula.trueF A ∈ S ∧ MSSignedFormula.trueF B ∈ S) ∧
    (MSSignedFormula.falseF (MSFormula.disj A B) ∈ S →
      MSSignedFormula.falseF A ∈ S ∧ MSSignedFormula.falseF B ∈ S) ∧
    (MSSignedFormula.falseF (MSFormula.impl A B) ∈ S →
      MSSignedFormula.trueF A ∈ S ∧ MSSignedFormula.falseF B ∈ S)) ∧
  (∀ A : MSFormula L,
    (MSSignedFormula.trueF (MSFormula.neg A) ∈ S →
      MSSignedFormula.falseF A ∈ S) ∧
    (MSSignedFormula.falseF (MSFormula.neg A) ∈ S →
      MSSignedFormula.trueF A ∈ S)) ∧
  -- H2 (disjunctive / type-B): at least one component in S.
  (∀ A B : MSFormula L,
    (MSSignedFormula.falseF (MSFormula.conj A B) ∈ S →
      MSSignedFormula.falseF A ∈ S ∨ MSSignedFormula.falseF B ∈ S) ∧
    (MSSignedFormula.trueF (MSFormula.disj A B) ∈ S →
      MSSignedFormula.trueF A ∈ S ∨ MSSignedFormula.trueF B ∈ S) ∧
    (MSSignedFormula.trueF (MSFormula.impl A B) ∈ S →
      MSSignedFormula.falseF A ∈ S ∨ MSSignedFormula.trueF B ∈ S)) ∧
  -- H3 (universal / type-C): sort-s instance for EVERY t ∈ H s.
  (∀ (s : L.SortType) (x : Nat) (A : MSFormula L),
    (MSSignedFormula.trueF (MSFormula.all s x A) ∈ S →
      ∀ t : MSTerm L s, t ∈ H s →
        MSSignedFormula.trueF (msFormulaSubst A s x t) ∈ S) ∧
    (MSSignedFormula.falseF (MSFormula.ex s x A) ∈ S →
      ∀ t : MSTerm L s, t ∈ H s →
        MSSignedFormula.falseF (msFormulaSubst A s x t) ∈ S)) ∧
  -- H4 (existential / type-D): sort-s instance for SOME t ∈ H s.
  (∀ (s : L.SortType) (x : Nat) (A : MSFormula L),
    (MSSignedFormula.falseF (MSFormula.all s x A) ∈ S →
      ∃ t : MSTerm L s, t ∈ H s ∧
        MSSignedFormula.falseF (msFormulaSubst A s x t) ∈ S) ∧
    (MSSignedFormula.trueF (MSFormula.ex s x A) ∈ S →
      ∃ t : MSTerm L s, t ∈ H s ∧
        MSSignedFormula.trueF (msFormulaSubst A s x t) ∈ S)) ∧
  -- H5: free variables of formulae in S are carried by H (per sort).
  (∀ (A : MSFormula L),
    (MSSignedFormula.trueF A ∈ S ∨ MSSignedFormula.falseF A ∈ S) →
      ∀ p : MSVar L, p ∈ msFormulaFV A → MSTerm.var p.1 p.2 ∈ H p.1) ∧
  -- H6: terms in H are free for the bound variable in quantified
  -- formulae of S (sort-matched).
  (∀ (s : L.SortType) (x : Nat) (A : MSFormula L) (t : MSTerm L s),
    t ∈ H s →
    (MSSignedFormula.trueF (MSFormula.all s x A) ∈ S ∨
     MSSignedFormula.falseF (MSFormula.all s x A) ∈ S ∨
     MSSignedFormula.trueF (MSFormula.ex s x A) ∈ S ∨
     MSSignedFormula.falseF (MSFormula.ex s x A) ∈ S) →
    msIsFreeFor A s x t)

/-- Definition 5.4.5 (many-sorted companion): an `S`-indexed family of
per-sort term-carriers `H` is a (generated) term algebra iff each sort
carrier `H s` is nonempty, is closed under the matching-sort function
applications and constants, and is closed under sub-terms. Direct
many-sorted analogue of one-sorted `IsGeneratedTermAlgebra`
(chap5 Def 5.4.5), with the function/constant closure now sort-indexed:
`f`'s value lands in `H (L.funRank f).2` when its arguments lie in the
per-arity-sort carriers, and a constant of sort `s` lies in `H s`.

This is the textbook standing hypothesis "`H` is a term algebra" of
Lemma 5.4.5 (the Hintikka-set satisfiability lemma): the carrier of the
Herbrand structure built below is the sort-indexed family `{t // t ∈ H s}`,
which is a many-sorted `MSStructure` exactly because of these closure
conditions (nonemptiness gives `carrierNonempty`, function/constant
closure give `interpFunc`/`interpConst`, sub-term closure gives the
`msTermEvalIdentity` evaluation identity). -/
@[blueprint "chap10__lemma_10_4_1"]
structure MSIsGeneratedTermAlgebra (L : MSLanguage)
    (H : (s : L.SortType) → Set (MSTerm L s)) : Prop where
  /-- Each sort carrier `H s` is nonempty. -/
  nonempty : ∀ s : L.SortType, ∃ t : MSTerm L s, t ∈ H s
  /-- Closure under function symbols (sort-matched): if every argument
      `ts i` lies in the carrier of its arity sort, then `f ts` lies in
      the carrier of the output sort. -/
  closedFunc : ∀ (f : L.funSymbols)
    (ts : (i : Fin (L.funRank f).1.length) → MSTerm L ((L.funRank f).1.get i)),
    (∀ i, ts i ∈ H ((L.funRank f).1.get i)) →
    MSTerm.func f ts ∈ H (L.funRank f).2
  /-- Every constant `c` of sort `s` lies in `H s`. -/
  closedConst : ∀ (s : L.SortType) (c : L.constSymbols s),
    MSTerm.const s c ∈ H s
  /-- Sub-term closure: if `f ts` lies in the output carrier, then each
      argument `ts i` lies in the carrier of its arity sort. -/
  closedSubterm : ∀ (f : L.funSymbols)
    (ts : (i : Fin (L.funRank f).1.length) → MSTerm L ((L.funRank f).1.get i)),
    MSTerm.func f ts ∈ H (L.funRank f).2 →
    ∀ i, ts i ∈ H ((L.funRank f).1.get i)

-- ATTACH-BLOCKER: size gate: retain original helper span in front
/-- Lemma 10.4.1 (companion): if every free variable `(s', i)` of a
sort-`s` term `t` has its variable term `var s' i ∈ H s'`, then `t ∈ H s`.
Many-sorted analogue of one-sorted `termInH`. Proved by induction on `t`:
variables are in `H` by assumption, constants by `closedConst`, function
applications by `closedFunc` with the induction hypothesis. -/
theorem msTermInH {L : MSLanguage}
    {H : (s : L.SortType) → Set (MSTerm L s)}
    (hTA : MSIsGeneratedTermAlgebra L H) :
    {s : L.SortType} → (t : MSTerm L s) →
    (∀ p : MSVar L, p ∈ msTermFV t → MSTerm.var p.1 p.2 ∈ H p.1) →
    t ∈ H s := by
  intro s t
  induction t with
  | var s' i =>
    intro hvars
    exact hvars (s', i) rfl
  | const s' c =>
    intro _
    exact hTA.closedConst s' c
  | func f ts ih =>
    intro hvars
    exact hTA.closedFunc f ts (fun i => ih i (fun p hp =>
      hvars p ⟨i, hp⟩))

-- ===================================================================
-- Lemma 10.4.1 (companion): Herbrand structure on a term algebra H
-- ===================================================================

/-- Lemma 10.4.1 (companion): the Herbrand structure `H_S` built from a
many-sorted Hintikka set `S` over a term algebra `H`. The carrier of
sort `s` is the subtype `{t : MSTerm L s // t ∈ H s}`; functions and
constants are interpreted syntactically (landing back in `H` by the
term-algebra closure conditions), and the predicate interpretation tests
membership of the signed atom `T (P t…)` in `S`. Many-sorted analogue of
one-sorted `hintikkaStructure`. -/
@[blueprint "chap10__lemma_10_4_1"]
noncomputable def msHintikkaStructure {L : MSLanguage}
    (H : (s : L.SortType) → Set (MSTerm L s))
    (S : Set (MSSignedFormula L))
    (hTA : MSIsGeneratedTermAlgebra L H) : MSStructure L where
  carrier := fun s => { t : MSTerm L s // t ∈ H s }
  carrierNonempty := fun s =>
    let ⟨t, ht⟩ := hTA.nonempty s
    ⟨⟨t, ht⟩⟩
  interpFunc := fun f ts =>
    ⟨MSTerm.func f (fun i => (ts i).val),
     hTA.closedFunc f _ (fun i => (ts i).property)⟩
  interpConst := fun s c => ⟨MSTerm.const s c, hTA.closedConst s c⟩
  interpPred := fun P ts =>
    open Classical in
    if MSSignedFormula.trueF (MSFormula.pred P (fun i => (ts i).val)) ∈ S
    then BoolVal.T else BoolVal.F

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 10.4.1 (companion): the identity assignment for the Herbrand
structure. The sort-`s` variable `x_i` is sent to itself `⟨var s i, _⟩`
when `var s i ∈ H s`, otherwise to the chosen nonempty witness. Many-sorted
analogue of one-sorted `identityAssignment`. -/
noncomputable def msIdentityAssignment {L : MSLanguage}
    (H : (s : L.SortType) → Set (MSTerm L s))
    (S : Set (MSSignedFormula L))
    (hTA : MSIsGeneratedTermAlgebra L H) :
    MSAssignment (msHintikkaStructure H S hTA) :=
  fun s i =>
    open Classical in
    if h : MSTerm.var s i ∈ H s then ⟨MSTerm.var s i, h⟩
    else ⟨(hTA.nonempty s).choose, (hTA.nonempty s).choose_spec⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 10.4.1 (companion): evaluating a sort-`s` term `t ∈ H s` in the
Herbrand structure under the identity assignment yields `⟨t, ht⟩` — i.e.
`t` itself. Many-sorted analogue of one-sorted `termEvalIdentity`. Proved
by structural induction on `t`; the function case uses sub-term closure
(`closedSubterm`) so the recursive calls apply. -/
theorem msTermEvalIdentity {L : MSLanguage}
    {H : (s : L.SortType) → Set (MSTerm L s)}
    {S : Set (MSSignedFormula L)} {hTA : MSIsGeneratedTermAlgebra L H} :
    {s : L.SortType} → (t : MSTerm L s) → (ht : t ∈ H s) →
    msTermEval (msHintikkaStructure H S hTA)
      (msIdentityAssignment H S hTA) t = ⟨t, ht⟩ := by
  intro s t
  induction t with
  | var s' i =>
    intro ht
    simp only [msTermEval, varMeaning, msIdentityAssignment]
    exact dif_pos ht
  | const s' c =>
    intro _
    simp only [msTermEval, constM, msHintikkaStructure]
  | func f ts ih =>
    intro ht
    simp only [msTermEval, funM, msHintikkaStructure]
    apply Subtype.ext
    simp only
    congr 1
    funext i
    have hti : ts i ∈ H ((L.funRank f).1.get i) := hTA.closedSubterm f ts ht i
    exact congrArg Subtype.val (ih i hti)

-- ===================================================================
-- Lemma 10.4.1 (companion): formula depth, for the satisfaction induction
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 10.4.1 (companion): the connective/quantifier depth of a
many-sorted formula; atomic formulae (falsum, pred, eq_) have depth 0.
Used for the well-founded induction in the Hintikka satisfiability
proof (the quantifier cases need the claim for the same-depth instance
`A[t/x]`). Many-sorted analogue of one-sorted `formulaDepth`. -/
def msFormulaDepth {L : MSLanguage} : MSFormula L → Nat
  | .falsum       => 0
  | .pred _ _     => 0
  | .eq_ _ _ _ _  => 0
  | .neg A        => 1 + msFormulaDepth A
  | .conj A B     => 1 + msFormulaDepth A + msFormulaDepth B
  | .disj A B     => 1 + msFormulaDepth A + msFormulaDepth B
  | .impl A B     => 1 + msFormulaDepth A + msFormulaDepth B
  | .equiv_ A B   => 1 + msFormulaDepth A + msFormulaDepth B
  | .all _ _ A    => 1 + msFormulaDepth A
  | .ex _ _ A     => 1 + msFormulaDepth A

-- ATTACH-BLOCKER: size gate: retain original helper span in front
/-- Lemma 10.4.1 (companion): substitution preserves formula depth.
Many-sorted analogue of one-sorted `formulaSubstN_depth`. -/
theorem msFormulaSubst_depth {L : MSLanguage} [DecidableEq L.SortType]
    (A : MSFormula L) (u : L.SortType) (x : Nat) (t : MSTerm L u) :
    msFormulaDepth (msFormulaSubst A u x t) = msFormulaDepth A := by
  induction A with
  | falsum => rfl
  | pred _ _ => rfl
  | eq_ _ _ _ _ => rfl
  | neg A ih => simp [msFormulaSubst, msFormulaDepth, ih]
  | conj A B ihA ihB => simp [msFormulaSubst, msFormulaDepth, ihA, ihB]
  | disj A B ihA ihB => simp [msFormulaSubst, msFormulaDepth, ihA, ihB]
  | impl A B ihA ihB => simp [msFormulaSubst, msFormulaDepth, ihA, ihB]
  | equiv_ A B ihA ihB => simp [msFormulaSubst, msFormulaDepth, ihA, ihB]
  | all s i A ih =>
    simp only [msFormulaSubst]; split
    · rfl
    · simp only [msFormulaDepth]; omega
  | ex s i A ih =>
    simp only [msFormulaSubst]; split
    · rfl
    · simp only [msFormulaDepth]; omega

/-- Theorem 10.4.1 (companion): the many-sorted Hintikka-set
satisfiability bridge used by the completeness (→) direction. If `S` is
a many-sorted Hintikka set with respect to the `S`-indexed term-carrier
family `H` — which is a term algebra (`MSIsGeneratedTermAlgebra`, the
textbook standing hypothesis of Lemma 5.4.5) — then `S` is satisfiable
in the Herbrand structure built on `H`: there is a structure `M` and
assignment `v` making every `T A ∈ S` evaluate to `T` and every
`F A ∈ S` evaluate to `F`. This is the heart of the many-sorted
completeness argument (the §5.5 Hintikka satisfiability lemma transported
to the many-sorted algebra). It references `MSIsHintikkaSet`, so the
predicate is genuinely used by the completeness infrastructure.

The proof builds the Herbrand structure `msHintikkaStructure H S hTA`
with the identity assignment `msIdentityAssignment H S hTA`, then proves
the key satisfaction claim by well-founded induction on `msFormulaDepth`
(8 cases, atomic + connective + quantifier), using the H0–H6 Hintikka
conditions and the proven substitution-evaluation lemma
`msFormulaSubstEvalDirect`. Direct many-sorted analogue of one-sorted
`hintikka_set_satisfiable`. -/
@[blueprint "chap10__theorem_10_4_1"]
theorem msHintikkaSetSatisfiable {L : MSLanguage} [DecidableEq L.SortType]
    (H : (s : L.SortType) → Set (MSTerm L s))
    (S : Set (MSSignedFormula L)) (hTA : MSIsGeneratedTermAlgebra L H)
    (hHS : MSIsHintikkaSet L H S) :
    ∃ (M : MSStructure L) (v : MSAssignment M),
      (∀ A : MSFormula L, MSSignedFormula.trueF A ∈ S →
        msFormulaEval M A v = BoolVal.T) ∧
      (∀ A : MSFormula L, MSSignedFormula.falseF A ∈ S →
        msFormulaEval M A v = BoolVal.F) 

/-- Theorem 10.4.1: no sorted variable free in any end-sequent formula
occurs bound in any end-sequent formula, on either side. -/
@[blueprint "chap10__theorem_10_4_1"]
def MSInfSequent.crossNoFreeBound {L : MSLanguage} {hL : L.withoutEquality}
    (seq : MSInfSequent L hL) : Prop :=
  ∀ x : MSVar L,
    ((∃ i, x ∈ msFormulaFV (seq.val.antecedent.formula i)) ∨
      (∃ j, x ∈ msFormulaFV (seq.val.succedent.formula j))) →
    (∀ i, x ∉ msFormulaBV (seq.val.antecedent.formula i)) ∧
      (∀ j, x ∉ msFormulaBV (seq.val.succedent.formula j))

/-- Theorem 10.4.1: Gödel's extended completeness theorem for many-sorted
G. A possibly infinite equality-free six-connective end sequent with no
sorted variable both free and bound is valid iff it has a finite
G-provable subsequent in the inherited order. -/
@[attach_debt, blueprint "chap10__theorem_10_4_1" (main := true)]
theorem msGoedelExtendedCompletenessG {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.withoutEquality) (seq : MSInfSequent L hL)
    (hCross : seq.crossNoFreeBound) :
    msInfSequentValid seq ↔ msInfSequentProvable hL seq

end LCS.FirstOrder.ManySorted.Gentzen
end
