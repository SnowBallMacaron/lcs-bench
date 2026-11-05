import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Gentzen
import LCS.Propositional.Semantics
import Attach
import LCS.FirstOrder.ManySorted.Equality.ProofsStamp

/-! # FirstOrder.ManySorted.Equality
    Formalization of Chapter 10, Section 10.5 (Gentzen System G_= for
    Languages With Equality).

    The equality rules added to G to obtain G_= (Def 10.5.1): reflexivity,
    function congruence, and predicate congruence; soundness of G_=
    (Lemma 10.5.1); and Gödel's extended completeness theorem for G_=
    (Theorem 10.5.1).

    Builds on §10.4 system G (LCS.FirstOrder.ManySorted.Gentzen). EXTENDS
    that system — it does NOT redefine MSSequent, MSGentzenStep1/2,
    MSGProofTree, msSequentProvable, msSequentValid, or msSoundnessG.
    `MSGEqProofTree` embeds an `MSGProofTreeCore` via its `base`
    constructor and re-exposes the G axiom/one-premise/two-premise rules
    so G-rules and the equality rules may freely interleave, matching the
    textbook 'G_= = G plus the equality rules'.

    Direct many-sorted analogue of the one-sorted §5.6 treatment
    (LCS/FirstOrder/Equality.lean). The truth domain is `BoolVal`
    (Ch3 Def 3.3.1), so validity is phrased over `msFormulaEval M A v`
    via `= BoolVal.T`, NOT over Prop.

    Source: Logic for Computer Science, Gallier 2015.
-/

namespace LCS.FirstOrder.ManySorted.Equality

open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.FirstOrder.ManySorted.Gentzen
open LCS.Propositional.Semantics

-- ===================================================================
-- Definition 10.5.1 (companion def): msConjoinFormulae
-- ===================================================================

/-- Definition 10.5.1 (companion): fold a list of many-sorted formulae
into a right-nested conjunction. Returns the single formula if the list
has one element; nests the remaining conjunction on the right for multiple
elements; for an empty list returns the provided `default`. Realizes the textbook
conjunction `(s_1 ≐_{u_1} t_1) ∧ … ∧ (s_n ≐_{u_n} t_n)`. Sort-aware
analogue of one-sorted `conjoinFormulae` (chap5 Def 5.6.1). -/
@[blueprint "chap10__definition_10_5_1"]
def msConjoinFormulae {L : MSLanguage} (default : MSFormula L) :
    List (MSFormula L) → MSFormula L
  | [] => default
  | [A] => A
  | A :: rest => MSFormula.conj A (msConjoinFormulae default rest)

-- ===================================================================
-- Definition 10.5.1 (companion def): msEqPairsList
-- ===================================================================

/-- Definition 10.5.1 (companion): the list of per-argument sort-indexed
equalities `(s_i ≐_{u_i} t_i)`, each formed at its own sort
`sorts i = u_i`. The `sorts`-indexed dependent typing statically enforces
the textbook side condition that `s_i` and `t_i` are both of sort `u_i`
(the i-th sort in the rank/arity). Requires `hL : L.hasEquality = true`
so `MSFormula.eq_` can be constructed. Sort-aware analogue of one-sorted
`eqPairsList` (chap5 Def 5.6.1). -/
@[blueprint "chap10__definition_10_5_1"]
def msEqPairsList {L : MSLanguage} (hL : L.hasEquality = true) {n : Nat}
    (sorts : Fin n → L.SortType)
    (ss ts : (i : Fin n) → MSTerm L (sorts i)) : List (MSFormula L) :=
  (List.finRange n).map (fun i => MSFormula.eq_ hL (sorts i) (ss i) (ts i))

-- ===================================================================
-- Definition 10.5.1 (companion def): msEqCongruenceImplFunc
-- ===================================================================

/-- Definition 10.5.1 (companion): the function-congruence implication
formula `(s_1 ≐_{u_1} t_1) ∧ … ∧ (s_n ≐_{u_n} t_n) ⊃ (f s_1…s_n ≐_s f t_1…t_n)`.
The argument families `ss ts` are typed so each `ss i`, `ts i` is of sort
`u_i = (L.funRank f).1.get i`, and the consequent equality is at the
output sort `s = (L.funRank f).2`. For the empty-pairs corner the
`msConjoinFormulae` default (the consequent) keeps the antecedent
well-formed; Def 10.2.1's `funRank_nonempty` guarantees the arity is
nonempty. Sort-aware analogue of one-sorted `eqCongruenceImplFunc`
(chap5 Def 5.6.1). -/
@[blueprint "chap10__definition_10_5_1"]
def msEqCongruenceImplFunc (L : MSLanguage) (hL : L.hasEquality = true)
    (f : L.funSymbols)
    (ss ts : (i : Fin (L.funRank f).1.length) →
      MSTerm L ((L.funRank f).1.get i)) : MSFormula L :=
  let pairs := msEqPairsList hL (L.funRank f).1.get ss ts
  let consequent :=
    MSFormula.eq_ hL (L.funRank f).2 (MSTerm.func f ss) (MSTerm.func f ts)
  MSFormula.impl (msConjoinFormulae consequent pairs) consequent

-- ===================================================================
-- Definition 10.5.1 (companion def): msEqCongruenceImplPred
-- ===================================================================

/-- Definition 10.5.1 (companion): the predicate-congruence implication
formula `((s_1 ≐_{u_1} t_1) ∧ … ∧ (s_n ≐_{u_n} t_n) ∧ P s_1…s_n) ⊃ P t_1…t_n`.
The argument families `ss ts` are typed so each `ss i`, `ts i` is of sort
`u_i = (L.predArity P).get i`. The `msConjoinFormulae` antecedent appends
the premise predicate `P s_1…s_n` to the equality pairs. Because the
equality symbol `≐_s` is realized by the `MSFormula.eq_` constructor
rather than a member of `L.predSymbols`, the textbook's 'P (including
≐_s)' instance is provided separately via `msEqCongruenceImplEq`.
Sort-aware analogue of one-sorted `eqCongruenceImplPred` (chap5 Def
5.6.1). -/
@[blueprint "chap10__definition_10_5_1"]
def msEqCongruenceImplPred (L : MSLanguage) (hL : L.hasEquality = true)
    (P : L.predSymbols)
    (ss ts : (i : Fin (L.predArity P).length) →
      MSTerm L ((L.predArity P).get i)) : MSFormula L :=
  let pairs := msEqPairsList hL (L.predArity P).get ss ts
  let premisePred := MSFormula.pred P ss
  let consequent := MSFormula.pred P ts
  let antecedent := msConjoinFormulae premisePred (pairs ++ [premisePred])
  MSFormula.impl antecedent consequent

-- ===================================================================
-- Definition 10.5.1 (companion def): msEqCongruenceImplEq
-- ===================================================================

/-- Definition 10.5.1 (companion): the predicate-congruence implication
for the binary equality symbol `≐_s` (the textbook's H6(iii) instance
'P including ≐_s'): `((s_1 ≐_s t_1) ∧ (s_2 ≐_s t_2) ∧ (s_1 ≐_s s_2)) ⊃ (t_1 ≐_s t_2)`,
all equalities taken at the common sort `s`. Since `≐_s` is realized by
`MSFormula.eq_` (not a member of `L.predSymbols`), this congruence-of-
equality instance is stated explicitly, mirroring one-sorted
`eqCongruenceImplEq` (chap5 Def 5.6.2). -/
@[blueprint "chap10__definition_10_5_1"]
def msEqCongruenceImplEq {L : MSLanguage} (hL : L.hasEquality = true)
    (s : L.SortType) (s1 s2 t1 t2 : MSTerm L s) : MSFormula L :=
  MSFormula.impl
    (MSFormula.conj (MSFormula.eq_ hL s s1 t1)
      (MSFormula.conj (MSFormula.eq_ hL s s2 t2) (MSFormula.eq_ hL s s1 s2)))
    (MSFormula.eq_ hL s t1 t2)

-- ===================================================================
-- Definition 10.5.1: MSGEqProofTree
-- ===================================================================

/-- Definition 10.5.1: ordered proof trees for the six-connective system
`G_=` over a language with equality. Ordinary steps use the general G carriers.
Each equality step removes exactly one rightmost antecedent formula:
`Γ ++ [A] ⇒ Δ` gives `Γ ⇒ Δ`. Predicate congruence covers every arity;
`eqEqCong` supplies its binary logical-equality instance. Argument families
are indexed by the input sorts of the corresponding rank. -/
@[blueprint "chap10__definition_10_5_1" (main := true)]
inductive MSGEqProofTree {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.hasEquality = true) : MSSequentCore L → Type where
  /-- Embed a standard indexed G proof tree into G_=. -/
  | base {s : MSSequentCore L} (g : MSGProofTreeCore s) : MSGEqProofTree hL s
  /-- G-axiom leaf inside G_=: an axiom sequent of G serves as a leaf of
      the G_= proof tree directly (without the `base` wrapper). -/
  | axiom_ (s : MSSequentCore L) (hDomain : s.IsSixConnective) (hAx : MSSequentCore.isAxiom s) :
      MSGEqProofTree hL s
  /-- G one-premise rule lifted into G_=, so G-rules and eq-rules may
      interleave. -/
  | onePremise {prem conc : MSSequentCore L}
      (rule : MSGentzenStep1Core prem conc) (sub : MSGEqProofTree hL prem) :
      MSGEqProofTree hL conc
  /-- G two-premise rule lifted into G_=, so G-rules and eq-rules may
      interleave. -/
  | twoPremise {prem1 prem2 conc : MSSequentCore L}
      (rule : MSGentzenStep2Core prem1 prem2 conc)
      (sub1 : MSGEqProofTree hL prem1) (sub2 : MSGEqProofTree hL prem2) :
      MSGEqProofTree hL conc
  /-- Sort-indexed equality reflexivity rule: infer `Γ → Δ` from a tree
      whose conclusion is `Γ, t ≐_s t → Δ`. -/
  | eqRefl (s : L.SortType) (t : MSTerm L s)
      (Γ Δ : List (MSFormula L))
      (sub : MSGEqProofTree hL
        (MSSequentCore.mk (Γ ++ [MSFormula.eq_ hL s t t]) Δ)) :
      MSGEqProofTree hL (MSSequentCore.mk Γ Δ)
  /-- Many-sorted function-congruence rule. -/
  | eqFuncCong (f : L.funSymbols)
      (ss ts : (i : Fin (L.funRank f).1.length) →
        MSTerm L ((L.funRank f).1.get i))
      (Γ Δ : List (MSFormula L))
      (sub : MSGEqProofTree hL
        (MSSequentCore.mk (Γ ++ [msEqCongruenceImplFunc L hL f ss ts]) Δ)) :
      MSGEqProofTree hL (MSSequentCore.mk Γ Δ)
  /-- Predicate congruence for every arity. -/
  | eqPredCong (P : L.predSymbols)
      (ss ts : (i : Fin (L.predArity P).length) →
        MSTerm L ((L.predArity P).get i))
      (Γ Δ : List (MSFormula L))
      (sub : MSGEqProofTree hL
        (MSSequentCore.mk (Γ ++ [msEqCongruenceImplPred L hL P ss ts]) Δ)) :
      MSGEqProofTree hL (MSSequentCore.mk Γ Δ)
  /-- Predicate congruence for the binary logical equality symbol. -/
  | eqEqCong (s : L.SortType) (s1 s2 t1 t2 : MSTerm L s)
      (Γ Δ : List (MSFormula L))
      (sub : MSGEqProofTree hL
        (MSSequentCore.mk (Γ ++ [msEqCongruenceImplEq hL s s1 s2 t1 t2]) Δ)) :
      MSGEqProofTree hL (MSSequentCore.mk Γ Δ)

-- ===================================================================
-- Definition 10.5.1 (companion def): msSequentProvableEq
-- ===================================================================

/-- Definition 10.5.1 (companion): possibly infinite ordered sequents in
 the six-connective language with equality. -/
@[blueprint "chap10__definition_10_5_1"]
def MSInfSequentEq (L : MSLanguage) (_hL : L.hasEquality = true) :=
  {seq : MSInfSequentCore L // seq.IsSixConnective}

/-- Definition 10.5.1 (companion): a possibly infinite sequent is G=-provable
when a finite subsequent in the inherited order has a G= proof tree. -/
@[blueprint "chap10__definition_10_5_1"]
def msSequentProvableEq {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.hasEquality = true) (seq : MSInfSequentEq L hL) : Prop :=
  ∃ finite : MSSequentCore L,
    seq.val.IsFiniteSubsequent finite ∧ Nonempty (MSGEqProofTree hL finite)

/-- Lemma 10.5.1 (companion): shared-assignment validity of a possibly
infinite equality sequent. -/
@[blueprint "chap10__lemma_10_5_1"]
def msInfSequentValidEq {L : MSLanguage} {hL : L.hasEquality = true}
    (seq : MSInfSequentEq L hL) : Prop := msInfSequentValidCore seq.val

/-- Theorem 10.5.1 (companion): every sorted variable free in any end-sequent
formula is absent from the bound variables of every formula on either side. -/
@[blueprint "chap10__theorem_10_5_1"]
def MSInfSequentEq.crossNoFreeBound {L : MSLanguage} {hL : L.hasEquality = true}
    (seq : MSInfSequentEq L hL) : Prop :=
  ∀ x : MSVar L,
    ((∃ i, x ∈ msFormulaFV (seq.val.antecedent.formula i)) ∨
      (∃ j, x ∈ msFormulaFV (seq.val.succedent.formula j))) →
    (∀ i, x ∉ msFormulaBV (seq.val.antecedent.formula i)) ∧
      (∀ j, x ∉ msFormulaBV (seq.val.succedent.formula j))

-- ===================================================================
-- Lemma 10.5.1 (companion theorem): per-rule validity helpers
-- ===================================================================

/-- Lemma 10.5.1 (companion): the equality reflexivity formula `t ≐_s t`
is universally valid — under every many-sorted L-structure and
assignment it evaluates to `T`, because `t_M[v] = t_M[v]`. -/
@[blueprint "chap10__lemma_10_5_1"]
theorem msEqReflValid {L : MSLanguage} (hL : L.hasEquality = true)
    (s : L.SortType) (t : MSTerm L s) (M : MSStructure L)
    (v : MSAssignment M) :
    msFormulaEval M (MSFormula.eq_ hL s t t) v = BoolVal.T

-- ===================================================================
-- Lemma 10.5.1 (companion helpers): BoolVal connective lemmas
-- ===================================================================



-- retained: used by LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.HerbrandSatisfaction.Proofs, LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.QuotientModel.Proofs, LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.SemanticEquality.Proofs
/-- Helper: `hAnd x y = T` iff `x = T` and `y = T`. -/
theorem hAnd_eq_T_iff (x y : BoolVal) :
    hAnd x y = BoolVal.T ↔ (x = BoolVal.T ∧ y = BoolVal.T) := by
  cases x <;> cases y <;> simp [hAnd]

-- retained: used by LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.HerbrandSatisfaction.Proofs
/-- Helper: evaluation of an implication unfolds to `hImplies` of the
component evaluations. -/
theorem msFormulaEval_impl {L : MSLanguage} (M : MSStructure L)
    (A B : MSFormula L) (v : MSAssignment M) :
    msFormulaEval M (MSFormula.impl A B) v
      = hImplies (msFormulaEval M A v) (msFormulaEval M B v) := rfl

-- retained: used by LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.HerbrandSatisfaction.Proofs, LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.QuotientModel.Proofs, LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.SemanticEquality.Proofs, LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.Decision.Proofs, LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.Encoding.Proofs
/-- Helper: evaluation of a conjunction unfolds to `hAnd` of the
component evaluations. -/
theorem msFormulaEval_conj {L : MSLanguage} (M : MSStructure L)
    (A B : MSFormula L) (v : MSAssignment M) :
    msFormulaEval M (MSFormula.conj A B) v
      = hAnd (msFormulaEval M A v) (msFormulaEval M B v) := rfl

-- retained: used by LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.QuotientModel.Proofs, LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.SemanticEquality.Proofs, LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.CongruenceModel.Proofs, LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.Decision.Proofs, LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.Encoding.Proofs
/-- Helper: evaluation of an equality formula is `T` iff the two term
meanings coincide. -/
theorem msFormulaEval_eq_T_iff {L : MSLanguage} (M : MSStructure L)
    (hL : L.hasEquality = true) (s : L.SortType) (t1 t2 : MSTerm L s)
    (v : MSAssignment M) :
    msFormulaEval M (MSFormula.eq_ hL s t1 t2) v = BoolVal.T
      ↔ msTermEval M v t1 = msTermEval M v t2 := by
  dsimp only [msFormulaEval, eqM]
  by_cases h : msTermEval M v t1 = msTermEval M v t2
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]



/-- Lemma 10.5.1 (companion): the function-congruence implication
`msEqCongruenceImplFunc` is universally valid: if each `s_i ≐_{u_i} t_i`
holds then `f s_1…s_n ≐_s f t_1…t_n` holds, because equal argument
meanings give equal `interpFunc` results. -/
@[blueprint "chap10__lemma_10_5_1"]
theorem msEqFuncCongValid {L : MSLanguage} (hL : L.hasEquality = true)
    (f : L.funSymbols)
    (ss ts : (i : Fin (L.funRank f).1.length) →
      MSTerm L ((L.funRank f).1.get i))
    (M : MSStructure L) (v : MSAssignment M) :
    msFormulaEval M (msEqCongruenceImplFunc L hL f ss ts) v = BoolVal.T

/-- Lemma 10.5.1 (companion): the predicate-congruence implication
`msEqCongruenceImplPred` is universally valid: if each `s_i ≐_{u_i} t_i`
holds and `P s_1…s_n` holds then `P t_1…t_n` holds, because equal
argument meanings give equal `interpPred` results. -/
@[blueprint "chap10__lemma_10_5_1"]
theorem msEqPredCongValid {L : MSLanguage} (hL : L.hasEquality = true)
    (P : L.predSymbols)
    (ss ts : (i : Fin (L.predArity P).length) →
      MSTerm L ((L.predArity P).get i))
    (M : MSStructure L) (v : MSAssignment M) :
    msFormulaEval M (msEqCongruenceImplPred L hL P ss ts) v = BoolVal.T

/-- Lemma 10.5.1 (companion): the logical equality-predicate congruence
implication is valid under every structure and assignment. -/
@[attach_debt, blueprint "chap10__lemma_10_5_1"]
theorem msEqEqCongValid {L : MSLanguage} (hL : L.hasEquality = true)
    (s : L.SortType) (s1 s2 t1 t2 : MSTerm L s)
    (M : MSStructure L) (v : MSAssignment M) :
    msFormulaEval M (msEqCongruenceImplEq hL s s1 s2 t1 t2) v = BoolVal.T

/-- Lemma 10.5.1 (companion): adding a universally-valid formula `A` to
the antecedent of a sequent does not change its validity. The forward
direction holds because the extra antecedent formula is true anyway; the
backward direction holds because removing a true antecedent only weakens
the hypothesis. This is the `BoolVal`-valued many-sorted analogue of
one-sorted `addValidToAntecedent_iff`. -/
@[blueprint "chap10__lemma_10_5_1"]
theorem msAddValidToAntecedent_iff {L : MSLanguage}
    (Γ Δ Λ : List (MSFormula L)) (A : MSFormula L)
    (hvalid : ∀ (M : MSStructure L) (v : MSAssignment M),
      msFormulaEval M A v = BoolVal.T) :
    msSequentValid (MSSequentCore.mk (Γ ++ Δ) Λ) ↔
    msSequentValid (MSSequentCore.mk (Γ ++ [A] ++ Δ) Λ)

-- ===================================================================
-- Lemma 10.5.1 (companion theorem): tree-validity recursion
-- ===================================================================

/-- Lemma 10.5.1 (companion): every finite G= proof tree has a valid
conclusion, using general-core soundness for ordinary rules and validity
of the four equality-rule instances. -/
@[blueprint "chap10__lemma_10_5_1"]
theorem msEqTreeValid {L : MSLanguage} [DecidableEq L.SortType]
    {hL : L.hasEquality = true} {seq : MSSequentCore L}
    (t : MSGEqProofTree hL seq) : msSequentValid seq

-- ===================================================================
-- Lemma 10.5.1: msSoundnessGEq
-- ===================================================================

/-- Lemma 10.5.1: every possibly infinite G=-provable sequent is valid.
A finite proof witnesses provability; its true succedent formula remains
in the original ordered sequent. -/
@[blueprint "chap10__lemma_10_5_1" (main := true)]
theorem msSoundnessGEq {L : MSLanguage} [DecidableEq L.SortType]
    (hL : L.hasEquality = true) (seq : MSInfSequentEq L hL)
    (h : msSequentProvableEq hL seq) : msInfSequentValidEq seq

-- ===================================================================
-- Theorem 10.5.1 (companion type): MSIsHintikkaSetEq
-- ===================================================================

/-- Theorem 10.5.1 (companion): atomic consistency and the signed logical
closure conditions for a many-sorted equality-Hintikka set. Equality atoms
participate in atomic consistency, and terms used for quantifier instances
must be free for their sorted variables. -/
@[blueprint "chap10__theorem_10_5_1"]
def MSIsHintikkaSetEqBase (L : MSLanguage) [DecidableEq L.SortType]
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

/-- Theorem 10.5.1 (companion): the equality-Hintikka-set predicate for a
many-sorted algebra — the §5.6 `IsHintikkaSetEq` modified 'so that it
applies to a many-sorted algebra'. `H` is an `S`-indexed family of
per-sort term-carriers `H s : Set (MSTerm L s)`, the base closure
conditions are sort-aware, and the equality conditions H6(i)–H6(iii)
require the reflexivity / function-congruence / predicate-congruence
equality formulae (over argument terms of the matching sorts) to be in
`S` (in signed form `T(…)`). Referenced by the completeness (→) direction
of `msGoedelExtendedCompletenessGEq`. Many-sorted analogue of one-sorted
`IsHintikkaSetEq` (chap5 Def 5.6.1). -/
@[blueprint "chap10__theorem_10_5_1"]
structure MSIsHintikkaSetEq (L : MSLanguage) [DecidableEq L.SortType]
    (hL : L.hasEquality = true)
    (H : (s : L.SortType) → Set (MSTerm L s))
    (S : Set (MSSignedFormula L)) : Prop where
  /-- Atomic consistency, logical closure, and free-for conditions with
      respect to the per-sort term-carrier family `H`. -/
  base : MSIsHintikkaSetEqBase L H S
  /-- H6(i): for every sort `s` and term `t ∈ H s`, the signed
      reflexivity formula `T(t ≐_s t)` is in `S`. -/
  h6i : ∀ (s : L.SortType) (t : MSTerm L s), t ∈ H s →
    MSSignedFormula.trueF (MSFormula.eq_ hL s t t) ∈ S
  /-- H6(ii): for every function symbol `f` and argument families `ss`,
      `ts` (each of the matching sort) drawn from `H`, the signed
      function-congruence implication is in `S`. -/
  h6ii : ∀ (f : L.funSymbols)
    (ss ts : (i : Fin (L.funRank f).1.length) →
      MSTerm L ((L.funRank f).1.get i)),
    (∀ i, ss i ∈ H ((L.funRank f).1.get i)) →
    (∀ i, ts i ∈ H ((L.funRank f).1.get i)) →
    MSSignedFormula.trueF (msEqCongruenceImplFunc L hL f ss ts) ∈ S
  /-- H6(iii): for every predicate `P` and argument families `ss`,
      `ts` (each of the matching sort) drawn from `H`, the signed
      predicate-congruence implication is in `S`. -/
  h6iii : ∀ (P : L.predSymbols)
    (ss ts : (i : Fin (L.predArity P).length) →
      MSTerm L ((L.predArity P).get i)),
    (∀ i, ss i ∈ H ((L.predArity P).get i)) →
    (∀ i, ts i ∈ H ((L.predArity P).get i)) →
    MSSignedFormula.trueF (msEqCongruenceImplPred L hL P ss ts) ∈ S
  /-- H6(iii-eq): congruence of equality with respect to equality —
      H6(iii) applied to the equality symbol `≐_s` (which is realized by
      `MSFormula.eq_`, not a member of `L.predSymbols`). For every sort
      `s` and terms `s1 s2 t1 t2 ∈ H s`, the signed
      `msEqCongruenceImplEq` formula is in `S`. -/
  h6iii_eq : ∀ (s : L.SortType) (s1 s2 t1 t2 : MSTerm L s),
    s1 ∈ H s → s2 ∈ H s → t1 ∈ H s → t2 ∈ H s →
    MSSignedFormula.trueF (msEqCongruenceImplEq hL s s1 s2 t1 t2) ∈ S

-- ===================================================================
-- Theorem 10.5.1: msGoedelExtendedCompletenessGEq
-- ===================================================================

/-- Theorem 10.5.1: Gödel's extended completeness theorem for G=.
A possibly infinite six-connective sequent in a language with equality,
with no sorted variable both free and bound anywhere in the end sequent,
is valid iff some finite ordered subsequent has a G= proof. -/
@[attach_debt, blueprint "chap10__theorem_10_5_1" (main := true)]
theorem msGoedelExtendedCompletenessGEq {L : MSLanguage}
    [DecidableEq L.SortType] (hL : L.hasEquality = true)
    (seq : MSInfSequentEq L hL) (hCross : seq.crossNoFreeBound) :
    msInfSequentValidEq seq ↔ msSequentProvableEq hL seq

end LCS.FirstOrder.ManySorted.Equality
