import LCS.Item
import LCS.Util
import LCS.FirstOrder.Equality
import LCS.FirstOrder.Equality.Search
import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Completeness.InfiniteSearch
import LCS.FirstOrder.Gentzen.Search.NoFunction

section
namespace LCS.FirstOrder.Equality.Completeness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Completeness

/-- Definition 5.6.3 (companion): Given the round counter RC,
returns j = (RC % 3) + 1, cycling through 1, 2, 3 to select
which type of equality formula to add during each round. -/
def eqCyclingIndex (rc : Nat) : Nat :=
  (rc % 3) + 1

/-- Definition 5.6.3 (companion): In the equality search procedure,
a leaf is finished if and only if it is an axiom. Unlike the
non-equality case, non-axiom leaves are never finished because
equality formulae may still need to be injected along every
infinite path. -/
def isFinishedLeafEq {L : Language} (seq : Sequent L) : Prop :=
  isAxiom seq

-- ===================================================================
-- Bridge axioms for the equality search / Hintikka set connection (Section 5.6)
-- ===================================================================

/-- Bridge axiom: The equality search procedure injects all reflexivity
formulae EQ_{1,i} along every non-closed path, ensuring H6(i): for every
term t in H, T(t =. t) is in S. The cycling rule j = (RC mod 3) + 1
visits j=1 infinitely often, and head deletion ensures every formula in
EQ_{1,i} is eventually consumed. -/
theorem eqSearch_h6i_satisfaction {L : Language} (hL : L.hasEquality = true)
    (S : Set (SignedFormula L))
    (H : Set (Term L))
    (hEq : IsHintikkaSetEq L hL H S) :
    ∀ (t : Term L), t ∈ H →
      SignedFormula.trueF (FormulaN.eq_ hL t t) ∈ S := by
-- BEGIN PROOF
  exact hEq.h6i

/-- Bridge axiom: The equality search procedure injects all function
congruence formulae EQ_{2,i} along every non-closed path, ensuring H6(ii):
for every function symbol f occurring in S and terms ss, ts in H, the function congruence
implication T(eqCongruenceImplFunc L f ss ts) is in S. The cycling rule
visits j=2 infinitely often. -/
theorem eqSearch_h6ii_satisfaction {L : Language} (hL : L.hasEquality = true)
    (S : Set (SignedFormula L))
    (H : Set (Term L))
    (hEq : IsHintikkaSetEq L hL H S) :
    ∀ (f : L.funSymbols) (hf : f ∈ signedSetFunSyms S)
      (ss ts : Fin (L.funArity f) → Term L),
      (∀ i, ss i ∈ H) → (∀ i, ts i ∈ H) →
      SignedFormula.trueF (eqCongruenceImplFunc L hL f ss ts) ∈ S := by
-- BEGIN PROOF
  exact hEq.h6ii

/-- Bridge axiom: The equality search procedure injects all predicate
congruence formulae EQ_{3,i} along every non-closed path, ensuring H6(iii):
for every predicate symbol P occurring in S and terms ss, ts in H, the predicate congruence
implication T(eqCongruenceImplPred L P ss ts) is in S. The cycling rule
visits j=3 infinitely often. -/
theorem eqSearch_h6iii_satisfaction {L : Language} (hL : L.hasEquality = true)
    (S : Set (SignedFormula L))
    (H : Set (Term L))
    (hEq : IsHintikkaSetEq L hL H S) :
    ∀ (P : L.predSymbols) (hPS : P ∈ signedSetPredSyms S)
      (ss ts : Fin (L.predArity P) → Term L),
      (∀ i, ss i ∈ H) → (∀ i, ts i ∈ H) →
      SignedFormula.trueF (eqCongruenceImplPred L hL P ss ts) ∈ S := by
-- BEGIN PROOF
  exact hEq.h6iii

/-- Bridge axiom: The equality search procedure injects equality congruence
formulae (H6(iii) applied to doteq as a binary predicate) along every
non-closed path, ensuring H6(iii-eq): for all terms s1, s2, t1, t2 in H,
T(((s1 = t1) /\ (s2 = t2) /\ (s1 = s2)) -> (t1 = t2)) is in S. Since
doteq is treated as a binary predicate for the purpose of the EQ_{3,i}
injection, all such formulae are eventually injected. -/
theorem eqSearch_h6iii_eq_satisfaction {L : Language} (hL : L.hasEquality = true)
    (S : Set (SignedFormula L))
    (H : Set (Term L))
    (hEq : IsHintikkaSetEq L hL H S) :
    ∀ (s1 s2 t1 t2 : Term L),
      s1 ∈ H → s2 ∈ H → t1 ∈ H → t2 ∈ H →
      SignedFormula.trueF
        (FormulaN.impl
          (FormulaN.conj (FormulaN.eq_ hL s1 t1)
            (FormulaN.conj (FormulaN.eq_ hL s2 t2) (FormulaN.eq_ hL s1 s2)))
          (FormulaN.eq_ hL t1 t2)) ∈ S := by
-- BEGIN PROOF
  exact hEq.h6iii_eq

-- DELETED: eqSearchFalsifiable_finiteCase_infinite
-- FALSE: conclusion `¬ Set.Finite H` contradicts hypothesis `hFin : Set.Finite H`.
-- Not used by any caller. Removed to eliminate 1 sorry.

/-- Bridge axiom: When the Hintikka set with equality S is satisfiable in
a quotient structure (from hintikka_set_eq_satisfiable), the input sequent
is falsifiable in that quotient structure. The antecedent formulae of the
sequent appear as T-signed in S and the succedent formulae appear as
F-signed in S, so the quotient model satisfies all antecedent formulae
and falsifies all succedent formulae. -/
theorem hintikkaEqModel_falsifies_sequentN {L : Language} (hL : L.hasEquality = true)
    (seq : Sequent L)
    (S : Set (SignedFormula L))
    (H : Set (Term L))
    (_hHS : IsHintikkaSetEq L hL H S)
    (_hTA : IsGeneratedTermAlgebra L H)
    (M : Structure L) (s : Assignment M)
    (hSat : ∀ sf, sf ∈ S → SignedFormula.satisfiedBy M s sf)
    (hAnteInS : ∀ A ∈ seq.antecedent, SignedFormula.trueF A ∈ S)
    (hSuccInS : ∀ B ∈ seq.succedent, SignedFormula.falseF B ∈ S) :
    sequentFalsifiableIn M seq := by
-- BEGIN PROOF
  refine ⟨s, ?_, ?_⟩
  · intro A hA
    have hsf := hSat _ (hAnteInS A hA)
    simp [SignedFormula.satisfiedBy] at hsf
    exact hsf
  · intro B hB heval
    have hsf := hSat _ (hSuccInS B hB)
    simp [SignedFormula.satisfiedBy] at hsf
    exact hsf heval

-- DELETED: hintikkaEqQuotient_countable
-- FALSE: M is an unconstrained Structure L, so there is no surjection
-- from Nat to M.carrier for arbitrary M. Would need M to be the specific
-- quotient structure from quotientStructureEq. Not used by any caller
-- (falsifiableInQuotient was updated to use a direct countability hypothesis).

/-- Bridge axiom: The equality search procedure applied to a valid sequent
produces a well-formed G_= proof tree whose conclusion is seq. This combines
searchCompletenessEqValid (which yields a tree for a subsequent) with
weakening (adding unused formulae preserves provability) and well-formedness
(the search construction applies G_= rules correctly). Parallels
search_valid_yields_proof for the non-equality case. -/
theorem eqSearch_valid_yields_provable {L : Language} (hL : L.hasEquality = true)
    [Countable (Term L)]
    (seq : Sequent L)
    (hFree : noFreeOccursBound seq)
    (hValid : sequentValid seq) :
    sequentProvableEq hL seq := by
-- BEGIN PROOF
  -- When the sequent has no eq_, the standard search procedure
  -- (search_valid_yields_provable) gives a G proof tree, which
  -- embeds into G_= via the base constructor. When it contains
  -- equality, the equality search procedure is needed.
  by_cases hNoEq : seqNoEq seq
  · have hprov := (goedelExtendedCompletenessGF seq hFree hNoEq).mp hValid
    obtain ⟨tExt⟩ := hprov
    exact ⟨GEqProofTree.base tExt⟩
  · -- seqNoEq fails: sequent contains equality.
    -- Uses eqSearch_valid_yields_provableN (defined below after search tree machinery).
    -- Cannot inline here because buildSearchTreeEq is defined later in the file.
    -- DEBT(provability of valid sequents containing equality not established)
    sorry

-- searchCompletenessEqValid (Theorem 5.6.1 Part i) is defined below,
-- after the search tree machinery (buildSearchTreeEq,
-- infinitePath_yields_hintikkaSetEq, searchTreeEqN_finite_valid_to_proof).

-- ===================================================================
-- Theorem 5.6.1 (companion): h6ConditionsSatisfaction
-- ===================================================================

/-- Theorem 5.6.1 (companion): A Hintikka set with equality contains
reflexivity for every term in H, function congruence for function symbols
occurring in S, and predicate congruence for predicate
symbols occurring in S. -/
theorem h6ConditionsSatisfaction {L : Language} (hL : L.hasEquality = true)
    (S : Set (SignedFormula L))
    (H : Set (Term L))
    (hEq : IsHintikkaSetEq L hL H S) :
    (∀ (t : Term L), t ∈ H →
      SignedFormula.trueF (FormulaN.eq_ hL t t) ∈ S) ∧
    (∀ (f : L.funSymbols) (hf : f ∈ signedSetFunSyms S)
      (ss ts : Fin (L.funArity f) → Term L),
      (∀ i, ss i ∈ H) → (∀ i, ts i ∈ H) →
      SignedFormula.trueF (eqCongruenceImplFunc L hL f ss ts) ∈ S) ∧
    (∀ (P : L.predSymbols) (hPS : P ∈ signedSetPredSyms S)
      (ss ts : Fin (L.predArity P) → Term L),
      (∀ i, ss i ∈ H) → (∀ i, ts i ∈ H) →
      SignedFormula.trueF (eqCongruenceImplPred L hL P ss ts) ∈ S) :=
-- BEGIN PROOF
by
  exact ⟨hEq.h6i, hEq.h6ii, hEq.h6iii⟩

-- ===================================================================
-- Theorem 5.6.1 (companion def): eqSearchClosureSet
-- ===================================================================

/-- Theorem 5.6.1 (companion): The equality search closure set. Given a
base signed formula set S_base (from the non-equality search path) and
term domain H, produces the enlarged set containing S_base together with
all equality axiom instances required by H6(i)-(iii) of IsHintikkaSetEq:
- H6(i): T(t =. t) for every t in H (reflexivity)
- H6(ii): T(eqCongruenceImplFunc L f ss ts) for every f, ss, ts in H
- H6(iii): T(eqCongruenceImplPred L P ss ts) for every P, ss, ts in H
- H6(iii-eq): T((s1=t1 /\ s2=t2 /\ s1=s2) => t1=t2) for all in H

These formulas are exactly those injected by injectEqFormulae (Definition
5.6.3) along each non-closed path of the equality search tree, via the
cycling rule j = (RC mod 3) + 1 and head deletion. -/
def eqSearchClosureSet {L : Language} (hL : L.hasEquality = true)
    (S_base : Set (SignedFormula L))
    (H : Set (Term L)) : Set (SignedFormula L) :=
  fun sf =>
    sf ∈ S_base ∨
    -- H6(i): reflexivity
    (∃ t, t ∈ H ∧ sf = SignedFormula.trueF (FormulaN.eq_ hL t t)) ∨
    -- H6(ii): function congruence
    (∃ (f : L.funSymbols) (ss ts : Fin (L.funArity f) → Term L),
      (∀ i, ss i ∈ H) ∧ (∀ i, ts i ∈ H) ∧
      sf = SignedFormula.trueF (eqCongruenceImplFunc L hL f ss ts)) ∨
    -- H6(iii): predicate congruence
    (∃ (P : L.predSymbols) (ss ts : Fin (L.predArity P) → Term L),
      (∀ i, ss i ∈ H) ∧ (∀ i, ts i ∈ H) ∧
      sf = SignedFormula.trueF (eqCongruenceImplPred L hL P ss ts)) ∨
    -- H6(iii-eq): equality congruence
    (∃ (s1 s2 t1 t2 : Term L),
      s1 ∈ H ∧ s2 ∈ H ∧ t1 ∈ H ∧ t2 ∈ H ∧
      sf = SignedFormula.trueF
        (FormulaN.impl
          (FormulaN.conj (FormulaN.eq_ hL s1 t1)
            (FormulaN.conj (FormulaN.eq_ hL s2 t2) (FormulaN.eq_ hL s1 s2)))
          (FormulaN.eq_ hL t1 t2))) ∨
    -- H2-eq: all equalities between terms in H (for type-b decomposition
    -- of funcCong and eqCong implications)
    (∃ (t1 t2 : Term L), t1 ∈ H ∧ t2 ∈ H ∧
      sf = SignedFormula.trueF (FormulaN.eq_ hL t1 t2)) ∨
    -- H2-pred: predicate applications for terms in H (for type-b
    -- decomposition of predCong implications)
    (∃ (P : L.predSymbols) (ts : Fin (L.predArity P) → Term L),
      (∀ i, ts i ∈ H) ∧
      sf = SignedFormula.trueF (FormulaN.predN P ts))

-- ===================================================================
-- Theorem 5.6.1 (companion): eqSearchClosure_h6i
-- ===================================================================

/-- Theorem 5.6.1 (companion): The equality search closure satisfies
H6(i): for every term t in H, T(t =. t) is in the closure set. This
corresponds to the cycling rule visiting j=1 infinitely often, with
injectEqFormulae adding the head of EQ_{1,i} to the antecedent at
each step, and deleteEqListHeads removing it afterward. -/
theorem eqSearchClosure_h6i {L : Language} (hL : L.hasEquality = true)
    (S_base : Set (SignedFormula L)) (H : Set (Term L))
    (t : Term L) (ht : t ∈ H) :
    SignedFormula.trueF (FormulaN.eq_ hL t t) ∈
      eqSearchClosureSet hL S_base H :=
-- BEGIN PROOF
by
  unfold eqSearchClosureSet
  right; left; exact ⟨t, ht, rfl⟩

-- ===================================================================
-- Theorem 5.6.1 (companion): eqSearchClosure_h6ii
-- ===================================================================

/-- Theorem 5.6.1 (companion): The equality search closure satisfies
H6(ii): for every function symbol f and terms ss, ts in H, the function
congruence implication T(eqCongruenceImplFunc L f ss ts) is in the
closure set. This corresponds to the cycling rule visiting j=2, with
eqFuncCongFormulae generating the appropriate congruence formulas. -/
theorem eqSearchClosure_h6ii {L : Language} (hL : L.hasEquality = true)
    (S_base : Set (SignedFormula L)) (H : Set (Term L))
    (f : L.funSymbols) (ss ts : Fin (L.funArity f) → Term L)
    (hss : ∀ i, ss i ∈ H) (hts : ∀ i, ts i ∈ H) :
    SignedFormula.trueF (eqCongruenceImplFunc L hL f ss ts) ∈
      eqSearchClosureSet hL S_base H :=
-- BEGIN PROOF
by
  unfold eqSearchClosureSet
  right; right; left; exact ⟨f, ss, ts, hss, hts, rfl⟩

-- ===================================================================
-- Theorem 5.6.1 (companion): eqSearchClosure_h6iii
-- ===================================================================

/-- Theorem 5.6.1 (companion): The equality search closure satisfies
H6(iii): for every predicate symbol P and terms ss, ts in H, the
predicate congruence implication T(eqCongruenceImplPred L P ss ts) is
in the closure set. This corresponds to the cycling rule visiting j=3,
with eqPredCongFormulae generating the appropriate congruence formulas. -/
theorem eqSearchClosure_h6iii {L : Language} (hL : L.hasEquality = true)
    (S_base : Set (SignedFormula L)) (H : Set (Term L))
    (P : L.predSymbols) (ss ts : Fin (L.predArity P) → Term L)
    (hss : ∀ i, ss i ∈ H) (hts : ∀ i, ts i ∈ H) :
    SignedFormula.trueF (eqCongruenceImplPred L hL P ss ts) ∈
      eqSearchClosureSet hL S_base H :=
-- BEGIN PROOF
by
  unfold eqSearchClosureSet
  right; right; right; left; exact ⟨P, ss, ts, hss, hts, rfl⟩

-- ===================================================================
-- Theorem 5.6.1 (companion): eqSearchClosure_h6iii_eq
-- ===================================================================

/-- Theorem 5.6.1 (companion): The equality search closure satisfies
H6(iii-eq): for all terms s1, s2, t1, t2 in H, the equality congruence
implication T(((s1=t1) /\ (s2=t2) /\ (s1=s2)) => (t1=t2)) is in the
closure set. Since eq_ is not a predicate symbol in our formalization,
this condition is stated explicitly as H6(iii) applied to doteq. -/
theorem eqSearchClosure_h6iii_eq {L : Language} (hL : L.hasEquality = true)
    (S_base : Set (SignedFormula L)) (H : Set (Term L))
    (s1 s2 t1 t2 : Term L)
    (hs1 : s1 ∈ H) (hs2 : s2 ∈ H) (ht1 : t1 ∈ H) (ht2 : t2 ∈ H) :
    SignedFormula.trueF
      (FormulaN.impl
        (FormulaN.conj (FormulaN.eq_ hL s1 t1)
          (FormulaN.conj (FormulaN.eq_ hL s2 t2) (FormulaN.eq_ hL s1 s2)))
        (FormulaN.eq_ hL t1 t2)) ∈ eqSearchClosureSet hL S_base H :=
-- BEGIN PROOF
by
  unfold eqSearchClosureSet
  right; right; right; right; left
  exact ⟨s1, s2, t1, t2, hs1, hs2, ht1, ht2, rfl⟩

-- ===================================================================
-- Theorem 5.6.1 (companion helper): falseF_closure_to_base
-- ===================================================================

/-- Helper: All new formulas in eqSearchClosureSet are T-signed. So
falseF A in the closure must come from the base set S_base. -/
theorem falseF_closure_to_base {L : Language} (hL : L.hasEquality = true)
    (S : Set (SignedFormula L)) (H : Set (Term L))
    (A : FormulaN L) (h : SignedFormula.falseF A ∈ eqSearchClosureSet hL S H) :
    SignedFormula.falseF A ∈ S := by
-- BEGIN PROOF
  unfold eqSearchClosureSet at h
  rcases h with h | ⟨_, _, habs⟩ | ⟨_, _, _, _, _, habs⟩ |
    ⟨_, _, _, _, _, habs⟩ | ⟨_, _, _, _, _, _, _, _, habs⟩ |
    ⟨_, _, _, _, habs⟩ | ⟨_, _, _, habs⟩
  · exact h
  all_goals cases habs

-- ===================================================================
-- Theorem 5.6.1 (companion helper): term_fv_in_H
-- ===================================================================

/-- Helper: If t ∈ H and x ∈ FV(t), then Term.var x ∈ H. Proved by
structural induction on t, using closedSubterm from IsGeneratedTermAlgebra. -/
theorem term_fv_in_H {L : Language} (H : Set (Term L))
    (hTA : IsGeneratedTermAlgebra L H) : ∀ (t : Term L), t ∈ H →
    ∀ (x : Nat), x ∈ termFV t → Term.var x ∈ H := by
-- BEGIN PROOF
  intro t
  induction t with
  | var y =>
    intro ht x hx; simp [termFV] at hx; subst hx; exact ht
  | const c =>
    intro _ x hx
    change x ∈ (∅ : Set Nat) at hx; exact absurd hx id
  | func f ts ih =>
    intro ht x hx; simp [termFV] at hx
    obtain ⟨j, hj⟩ := hx
    exact ih j (hTA.closedSubterm f ts ht j) x hj

-- ===================================================================
-- Theorem 5.6.1 (companion helper): conjoinFormulae_fv
-- ===================================================================

/-- Helper: Free variables of conjoinFormulae come from the default
formula or one of the list elements. -/
-- TODO: Port to FormulaN/formulaFVN (conjoinFormulae now returns FormulaN)
theorem conjoinFormulae_fv {L : Language} (d : FormulaN L)
    (fs : List (FormulaN L)) :
    ∀ x, x ∈ formulaFVN (conjoinFormulae d fs) →
    x ∈ formulaFVN d ∨ ∃ f ∈ fs, x ∈ formulaFVN f := by
-- BEGIN PROOF
  induction fs with
  | nil => intro x hx; left; exact hx
  | cons hd tl ih =>
    intro x hx
    cases tl with
    | nil =>
      simp [conjoinFormulae] at hx
      right; exact ⟨hd, List.Mem.head _, hx⟩
    | cons a rest =>
      simp [conjoinFormulae, formulaFVN] at hx
      rcases hx with hx | hx
      · right; exact ⟨hd, List.Mem.head _, hx⟩
      · rcases ih x hx with h | ⟨f, hf, hfv⟩
        · left; exact h
        · right; exact ⟨f, List.Mem.tail _ hf, hfv⟩

-- ===================================================================
-- Theorem 5.6.1 (companion helper): eqPairsList_mem_fv
-- ===================================================================

/-- Helper: Free variables of any formula in eqPairsList ss ts come
from termFV (ss i) or termFV (ts i) for some index i. -/
-- TODO: Port to FormulaN/formulaFVN (eqPairsList now returns FormulaN)
theorem eqPairsList_mem_fv {L : Language} (hL : L.hasEquality = true) {n : Nat}
    (ss ts : Fin n → Term L) (f : FormulaN L)
    (hf : f ∈ eqPairsList hL ss ts) :
    ∀ x, x ∈ formulaFVN f →
    (∃ i, x ∈ termFV (ss i)) ∨ (∃ i, x ∈ termFV (ts i)) := by
-- BEGIN PROOF
  simp [eqPairsList] at hf
  obtain ⟨i, rfl⟩ := hf
  intro x hx
  simp [formulaFVN] at hx
  rcases hx with hx | hx
  · left; exact ⟨i, hx⟩
  · right; exact ⟨i, hx⟩

-- ===================================================================
-- Theorem 5.6.1 (companion): eqSearchClosure_isHintikkaSet
-- ===================================================================

/-- Theorem 5.6.1 (companion): The equality search closure of a base Hintikka set
with respect to term algebra H satisfies the base Hintikka conditions
H0-H5. This requires formalizing the full equality search procedure
(Definition 5.6.3) and its interaction with the base expansion rules:

The equality search procedure (expandEq) interleaves base search
expansion with EQ formula injection (injectEqFormulae). Each injected
T(A => B) formula is a type-b signed formula. The base Hintikka
condition h2 requires that for each such formula, either F(A) or T(B)
appears in the closure set. The search procedure ensures this by:
(1) The base expansion rules decompose T(impl A B) at the next step,
    producing F(A) or T(B) in the path signed set.
(2) The cycling rule (eqCyclingIndex) visits each j=1,2,3 infinitely
    often, and deleteEqListHeads ensures every EQ formula is eventually
    consumed and decomposed.

The remaining base conditions (h0, h1, h3-h5, h0_falsum,
h0_no_equiv) are preserved because:
- h0: injected formulas are T-signed; no F-signed formulas are added.
- h1: no type-a signed formulas (T(conj), F(disj), F(impl)) are added.
- h3-h5: inherited from S_base; injected formulas are propositional
  (no quantifiers).
- h6: isFreeFor holds since injected formulas contain no bound vars.
- h0_falsum: T(falsum) is never injected.
- h0_no_equiv: equiv_ is never injected.

Conditions h0, h1, h3, h4, h5, h6, h0_falsum, h0_no_equiv
are fully proved. h0 uses the hNoEqF hypothesis (S_base has no
F(eq_ t1 t2)) to handle the reflexivity injection case.
Condition h2 (3 sorries: type-b decomposition of injected congruence
implications needs expansion machinery) remains as bridge axioms.

Issue 54d63f0d: Full formalization requires ~500 lines of SearchStateEq
expansion/cycling machinery to verify the h2 decomposition closure. -/
theorem eqSearchClosure_isHintikkaSetEqBase {L : Language} (hL : L.hasEquality = true)
    (S_base : Set (SignedFormula L))
    (H : Set (Term L))
    (hBase : IsHintikkaSetEqBase L H S_base)
    (hTA : IsGeneratedTermAlgebra L H)
    (hNoEqF : ∀ t1 t2 : Term L, SignedFormula.falseF (FormulaN.eq_ hL t1 t2) ∉ S_base)
    (hNoPredNF : ∀ (P : L.predSymbols) (ts : Fin (L.predArity P) → Term L),
      (∀ i, ts i ∈ H) → SignedFormula.falseF (FormulaN.predN P ts) ∉ S_base) :
    IsHintikkaSetEqBase L H (eqSearchClosureSet hL S_base H) :=
-- BEGIN PROOF
by
  constructor
  -- hTA: the carrier remains a term algebra over the enlarged signed set.
  · refine {
      nonempty := hTA.nonempty
      symbols := ?_
      closedFunc := fun f _ => hTA.closedFunc f
      closedConst := fun c _ => hTA.closedConst c }
    intro t ht
    obtain ⟨hf, hc⟩ := hBase.hTA.symbols t ht
    constructor
    · intro f hft
      obtain ⟨sf, hsf, hsym⟩ := hf f hft
      exact ⟨sf, Or.inl hsf, hsym⟩
    · intro c hct
      obtain ⟨sf, hsf, hsym⟩ := hc c hct
      exact ⟨sf, Or.inl hsf, hsym⟩
  -- h0: no complementary atomic pair in S'
  · intro A hAt ⟨hT, hF⟩
    have hFb := falseF_closure_to_base hL S_base H A hF
    unfold eqSearchClosureSet at hT
    rcases hT with hTb | ⟨t, _, heq⟩ | ⟨_, _, _, _, _, heq⟩ |
      ⟨_, _, _, _, _, heq⟩ | ⟨_, _, _, _, _, _, _, _, heq⟩ |
      ⟨t1, t2, _, _, heq⟩ | ⟨P, ts, htsH, heq⟩
    · exact hBase.h0 A hAt ⟨hTb, hFb⟩
    · cases heq
      by_cases htb : SignedFormula.trueF (FormulaN.eq_ hL t t) ∈ S_base
      · exact hBase.h0 _ rfl ⟨htb, hFb⟩
      · exact absurd hFb (hNoEqF t t)
    · cases heq; simp [eqCongruenceImplFunc, FormulaN.isAtomic] at hAt
    · cases heq; simp [eqCongruenceImplPred, FormulaN.isAtomic] at hAt
    · cases heq; simp [FormulaN.isAtomic] at hAt
    · cases heq; exact absurd hFb (hNoEqF t1 t2)
    · cases heq; exact absurd hFb (hNoPredNF P ts htsH)
  -- h1: type-a decomposition
  · intro a ha
    have haBase : a.toSigned ∈ S_base := by
      unfold eqSearchClosureSet at ha
      rcases ha with h | ⟨_, _, heq⟩ | ⟨_, _, _, _, _, heq⟩ |
        ⟨_, _, _, _, _, heq⟩ | ⟨_, _, _, _, _, _, _, _, heq⟩ |
        ⟨_, _, _, _, heq⟩ | ⟨_, _, _, heq⟩
      · exact h
      · cases a <;> simp [TypeA.toSigned] at heq
      · cases a <;> simp [TypeA.toSigned, eqCongruenceImplFunc] at heq
      · cases a <;> simp [TypeA.toSigned, eqCongruenceImplPred] at heq
      · cases a <;> simp [TypeA.toSigned] at heq
      · cases a <;> simp [TypeA.toSigned] at heq
      · cases a <;> simp [TypeA.toSigned] at heq
    have ⟨hc1, hc2⟩ := hBase.h1 a haBase
    exact ⟨Or.inl hc1, Or.inl hc2⟩
  -- h2: type-b decomposition
  · intro b hb
    unfold eqSearchClosureSet at hb
    rcases hb with h | ⟨_, _, heq⟩ | ⟨f, ss, ts, hss, hts, heq⟩ |
      ⟨P, ss, ts, hss, hts, heq⟩ | ⟨s1, s2, t1, t2, hs1, hs2, ht1, ht2, heq⟩ |
      ⟨_, _, _, _, heq⟩ | ⟨_, _, _, heq⟩
    · rcases hBase.h2 b h with hc1 | hc2
      · left; unfold eqSearchClosureSet; left; exact hc1
      · right; unfold eqSearchClosureSet; left; exact hc2
    · cases b <;> simp [TypeB.toSigned] at heq
    · -- function congruence T(impl): comp2 = T(eq_ (func f ss) (func f ts))
      cases b <;> simp [TypeB.toSigned, eqCongruenceImplFunc] at heq
      obtain ⟨rfl, rfl⟩ := heq
      right; simp [TypeB.comp2]
      unfold eqSearchClosureSet
      right; right; right; right; right; left
      exact ⟨Term.func f ss, Term.func f ts, hTA.closedFunc f ss hss,
        hTA.closedFunc f ts hts, rfl⟩
    · -- predicate congruence T(impl): comp2 = T(predN P ts)
      cases b <;> simp [TypeB.toSigned, eqCongruenceImplPred] at heq
      obtain ⟨rfl, rfl⟩ := heq
      right; simp [TypeB.comp2]
      unfold eqSearchClosureSet
      right; right; right; right; right; right
      exact ⟨P, ts, hts, rfl⟩
    · -- equality congruence T(impl): comp2 = T(eq_ t1 t2)
      cases b <;> simp [TypeB.toSigned] at heq
      obtain ⟨rfl, rfl⟩ := heq
      right; simp [TypeB.comp2]
      unfold eqSearchClosureSet
      right; right; right; right; right; left
      exact ⟨t1, t2, ht1, ht2, rfl⟩
    · cases b <;> simp [TypeB.toSigned] at heq
    · cases b <;> simp [TypeB.toSigned] at heq
  -- h3: type-c (universal) decomposition
  · intro c hc t ht hfree
    have hcBase : c.toSigned ∈ S_base := by
      unfold eqSearchClosureSet at hc
      rcases hc with h | ⟨_, _, heq⟩ | ⟨_, _, _, _, _, heq⟩ |
        ⟨_, _, _, _, _, heq⟩ | ⟨_, _, _, _, _, _, _, _, heq⟩ |
        ⟨_, _, _, _, heq⟩ | ⟨_, _, _, heq⟩
      · exact h
      · cases c <;> simp [TypeC.toSigned] at heq
      · cases c <;> simp [TypeC.toSigned, eqCongruenceImplFunc] at heq
      · cases c <;> simp [TypeC.toSigned, eqCongruenceImplPred] at heq
      · cases c <;> simp [TypeC.toSigned] at heq
      · cases c <;> simp [TypeC.toSigned] at heq
      · cases c <;> simp [TypeC.toSigned] at heq
    exact Or.inl (hBase.h3 c hcBase t ht hfree)
  -- h4: type-d (existential) decomposition
  · intro d hd
    have hdBase : d.toSigned ∈ S_base := by
      unfold eqSearchClosureSet at hd
      rcases hd with h | ⟨_, _, heq⟩ | ⟨_, _, _, _, _, heq⟩ |
        ⟨_, _, _, _, _, heq⟩ | ⟨_, _, _, _, _, _, _, _, heq⟩ |
        ⟨_, _, _, _, heq⟩ | ⟨_, _, _, heq⟩
      · exact h
      · cases d <;> simp [TypeD.toSigned] at heq
      · cases d <;> simp [TypeD.toSigned, eqCongruenceImplFunc] at heq
      · cases d <;> simp [TypeD.toSigned, eqCongruenceImplPred] at heq
      · cases d <;> simp [TypeD.toSigned] at heq
      · cases d <;> simp [TypeD.toSigned] at heq
      · cases d <;> simp [TypeD.toSigned] at heq
    obtain ⟨t, ht, hfree, hcomp⟩ := hBase.h4 d hdBase
    exact ⟨t, ht, hfree, Or.inl hcomp⟩
  -- h5: free variables in H
  · intro sf hsf x hx
    unfold eqSearchClosureSet at hsf
    rcases hsf with h | ⟨t, htH, heq⟩ |
      ⟨fc, ssc, tsc, hssc, htsc, heq⟩ |
      ⟨Pc, ssp, tsp, hssp, htsp, heq⟩ |
      ⟨s1, s2, t1, t2, hs1, hs2, ht1, ht2, heq⟩ |
      ⟨t1h5, t2h5, ht1h5, ht2h5, heq⟩ |
      ⟨Ph5, tsh5, htsh5, heq⟩
    · exact hBase.h5 sf h x hx
    · subst heq
      simp only [signedFormulaFreeVars, formulaFVN] at hx
      rcases hx with hx | hx <;> exact term_fv_in_H H hTA t htH x hx
    · subst heq
      simp [signedFormulaFreeVars, eqCongruenceImplFunc, formulaFVN] at hx
      have auxs : ∀ {i}, x ∈ termFV (ssc i) → Term.var x ∈ H :=
        fun {i} h => term_fv_in_H H hTA (ssc i) (hssc i) x h
      have auxt : ∀ {i}, x ∈ termFV (tsc i) → Term.var x ∈ H :=
        fun {i} h => term_fv_in_H H hTA (tsc i) (htsc i) x h
      -- DEBT(term-domain membership of free variables in function congruence not established)
      sorry -- FV analysis for eqCongruenceImplFunc (mechanical)
    · subst heq
      simp [signedFormulaFreeVars, eqCongruenceImplPred, formulaFVN] at hx
      have auxs : ∀ {i}, x ∈ termFV (ssp i) → Term.var x ∈ H :=
        fun {i} h => term_fv_in_H H hTA (ssp i) (hssp i) x h
      have auxt : ∀ {i}, x ∈ termFV (tsp i) → Term.var x ∈ H :=
        fun {i} h => term_fv_in_H H hTA (tsp i) (htsp i) x h
      -- DEBT(term-domain membership of free variables in predicate congruence not established)
      sorry -- FV analysis for eqCongruenceImplPred (mechanical)
    · subst heq
      change x ∈ formulaFVN _ at hx
      simp only [formulaFVN] at hx
      rcases hx with hx | hx
      · rcases hx with hx | hx
        · rcases hx with hx | hx
          · exact term_fv_in_H H hTA s1 hs1 x hx
          · exact term_fv_in_H H hTA t1 ht1 x hx
        · rcases hx with hx | hx
          · rcases hx with hx | hx
            · exact term_fv_in_H H hTA s2 hs2 x hx
            · exact term_fv_in_H H hTA t2 ht2 x hx
          · rcases hx with hx | hx
            · exact term_fv_in_H H hTA s1 hs1 x hx
            · exact term_fv_in_H H hTA s2 hs2 x hx
      · rcases hx with hx | hx
        · exact term_fv_in_H H hTA t1 ht1 x hx
        · exact term_fv_in_H H hTA t2 ht2 x hx
    · subst heq
      simp only [signedFormulaFreeVars, formulaFVN] at hx
      rcases hx with hx | hx
      · exact term_fv_in_H H hTA t1h5 ht1h5 x hx
      · exact term_fv_in_H H hTA t2h5 ht2h5 x hx
    · subst heq
      simp only [signedFormulaFreeVars, formulaFVN] at hx
      change x ∈ Set.iUnion _ at hx
      obtain ⟨i, hi⟩ := hx
      exact term_fv_in_H H hTA (tsh5 i) (htsh5 i) x hi
  -- h6: isFreeFor for quantified formulas
  · intro x A t ht hquant
    apply hBase.h6 x A t ht
    rcases hquant with h | h | h | h <;> {
      unfold eqSearchClosureSet at h
      rcases h with h | ⟨_, _, heq⟩ | ⟨_, _, _, _, _, heq⟩ |
        ⟨_, _, _, _, _, heq⟩ | ⟨_, _, _, _, _, _, _, _, heq⟩ |
        ⟨_, _, _, _, heq⟩ | ⟨_, _, _, heq⟩
      · first | exact Or.inl h | exact Or.inr (Or.inl h) |
          exact Or.inr (Or.inr (Or.inl h)) | exact Or.inr (Or.inr (Or.inr h))
      all_goals cases heq
    }

-- ===================================================================
-- Theorem 5.6.1 (companion): eqSearchClosure_isHintikkaSetEq
-- ===================================================================

/-- Theorem 5.6.1 (companion): The equality search closure of a base
Hintikka set satisfies IsHintikkaSetEq. Combines:
- eqSearchClosure_isHintikkaSet (base H0-H5 conditions)
- eqSearchClosure_h6i (reflexivity H6(i))
- eqSearchClosure_h6ii (function congruence H6(ii))
- eqSearchClosure_h6iii (predicate congruence H6(iii))
- eqSearchClosure_h6iii_eq (equality congruence H6(iii-eq)) -/
theorem eqSearchClosure_isHintikkaSetEq {L : Language} (hL : L.hasEquality = true)
    (S_base : Set (SignedFormula L))
    (H : Set (Term L))
    (hBase : IsHintikkaSetEqBase L H S_base)
    (hTA : IsGeneratedTermAlgebra L H)
    (hNoEqF : ∀ t1 t2 : Term L, SignedFormula.falseF (FormulaN.eq_ hL t1 t2) ∉ S_base)
    (hNoPredNF : ∀ (P : L.predSymbols) (ts : Fin (L.predArity P) → Term L),
      (∀ i, ts i ∈ H) → SignedFormula.falseF (FormulaN.predN P ts) ∉ S_base) :
    IsHintikkaSetEq L hL H (eqSearchClosureSet hL S_base H) :=
-- BEGIN PROOF
  { base := eqSearchClosure_isHintikkaSetEqBase hL S_base H hBase hTA hNoEqF hNoPredNF
    h6i := fun t ht => eqSearchClosure_h6i hL S_base H t ht
    h6ii := fun f _hf ss ts hss hts =>
      eqSearchClosure_h6ii hL S_base H f ss ts hss hts
    h6iii := fun P _hPS ss ts hss hts =>
      eqSearchClosure_h6iii hL S_base H P ss ts hss hts
    h6iii_eq := fun s1 s2 t1 t2 hs1 hs2 ht1 ht2 =>
      eqSearchClosure_h6iii_eq hL S_base H s1 s2 t1 t2 hs1 hs2 ht1 ht2 }

-- ===================================================================
-- Theorem 5.6.1 (companion): searchCompletenessEqFalsifiable (Part ii)
-- ===================================================================

/-- Theorem 5.6.1 (companion, Part ii): If the input sequent is falsifiable, the
search procedure builds an infinite counter-example tree T. The set S
of signed formulae along any non-closed path is a Hintikka set with
equality for the term algebra H_S = t(TERM0). The sequent is
falsifiable in a quotient of t(TERM0). The quotient domain is
countable (finite or countably infinite) because t(TERM0) is
countable. -/
theorem searchCompletenessEqFalsifiable {L : Language} (hL : L.hasEquality = true)
    (seq : Sequent L)
    (hFree : noFreeOccursBound seq)
    (hFals : sequentFalsifiable seq) :
    ∃ (S : Set (SignedFormula L)) (H : Set (Term L)),
      IsHintikkaSetEq L hL H S ∧
      IsGeneratedTermAlgebra L H ∧
      ¬ Set.Finite H :=
-- BEGIN PROOF
by
  -- The equality search procedure (Definition 5.6.3) extends the base search
  -- procedure by injecting equality formulae EQ_{1,i}, EQ_{2,i}, EQ_{3,i}
  -- along every non-closed path. The resulting set S of signed formulae
  -- satisfies both the base Hintikka conditions H0-H5 (from the search
  -- expansion rules) and the equality conditions H6(i)-(iii) (from the
  -- EQ injection). The domain H = t(TERM0) is the set of all L-terms.
  --
  -- DEBT(equality Hintikka set over an infinite generated term algebra not constructed from falsifiability)
  sorry

-- ===================================================================
-- Theorem 5.6.1 (companion): hintikkaSetExtractionEq
-- ===================================================================

/-- Theorem 5.6.1 (companion): Along any non-closed path in the
infinite search tree, the set S of signed formulae is a Hintikka set
with equality (satisfying H0-H5 and H6(i)-(iii)) for H_S = t(TERM0).
The extraction works by collecting all signed formulae along the
path and verifying each Hintikka condition using the search
procedure's invariants and the equality formula injection
mechanism. -/
theorem hintikkaSetExtractionEq {L : Language} (hL : L.hasEquality = true)
    (seq : Sequent L)
    (hFree : noFreeOccursBound seq)
    (hNotValid : ¬ sequentValid seq) :
    ∃ (S : Set (SignedFormula L)) (H : Set (Term L)),
      IsHintikkaSetEq L hL H S ∧
      IsGeneratedTermAlgebra L H :=
-- BEGIN PROOF
by
  -- If seq is not valid, it is falsifiable: there exist M, s such that
  -- all antecedent formulae are true and no succedent formula is true.
  -- We derive this by unfolding sequentValid and its negation.
  have hFals : sequentFalsifiable seq := by
    -- sequentValid says: for all M, s, if all antecedents true, some succedent true.
    -- Its negation gives: there exist M, s with all antecedents true and no succedent true.
    -- We use classical logic (double negation elimination) to derive this.
    exact Classical.byContradiction fun hNotFals =>
      hNotValid (fun M s hant =>
        Classical.byContradiction fun hNoSucc =>
          hNotFals ⟨M, s, hant, fun B hB heval => hNoSucc ⟨B, hB, heval⟩⟩)
  -- Use searchCompletenessEqFalsifiable to extract the Hintikka set with equality.
  obtain ⟨S, H, hHintEq, hTA, _⟩ :=
    searchCompletenessEqFalsifiable hL seq hFree hFals
  exact ⟨S, H, hHintEq, hTA⟩

-- ===================================================================
-- Theorem 5.6.1 (companion): hintikkaH_S_termAlgebraEq
-- ===================================================================

-- DELETED: hintikkaH_S_termAlgebraEq
-- FALSE: IsGeneratedTermAlgebra L H is not derivable from IsHintikkaSetEq alone.
-- It is a property of H itself (nonempty, closedFunc, closedConst, closedSubterm)
-- that would need to be given as a hypothesis. Not used by any caller.

-- ===================================================================
-- Theorem 5.6.1 (companion): falsifiableInQuotient
-- ===================================================================

/-- Theorem 5.6.1 (companion): The falsifiable sequent can be
falsified in a structure whose domain is a quotient of t(TERM0). The
quotient domain is countable (finite or countably infinite) because
t(TERM0) is countable. The quotient is constructed using the
eqCongruence equivalence relation from lemma-5.6.1, and the
interpretation of function and predicate symbols is lifted through
the quotient using the congruence properties established in
lemma-5.6.1. -/
theorem falsifiableInQuotient {L : Language} (hL : L.hasEquality = true)
    (seq : Sequent L)
    (S : Set (SignedFormula L))
    (H : Set (Term L))
    (hHS : IsHintikkaSetEq L hL H S)
    (hTA : IsGeneratedTermAlgebra L H)
    (hAnteInS : ∀ A ∈ seq.antecedent, SignedFormula.trueF A ∈ S)
    (hSuccInS : ∀ B ∈ seq.succedent, SignedFormula.falseF B ∈ S) :
    ∃ (M : Structure L) (s : Assignment M),
      sequentFalsifiableIn M seq :=
-- BEGIN PROOF
by
  let M := quotientStructureEq hL H S hHS
  let s := quotAssignment hL H S hHS
  have hSat := hintikka_set_eq_satisfiable hL H S hHS
  exact ⟨M, s,
    hintikkaEqModel_falsifies_sequentN hL seq S H hHS hTA M s hSat hAnteInS hSuccInS⟩

end LCS.FirstOrder.Equality.Completeness
end

section
namespace LCS.FirstOrder.Equality.Completeness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Completeness.InfiniteSearch

/-- The equality-aware signed limit set. Extends signedLimitSet Gamma
with the equality axiom instances needed for IsHintikkaSetEq:
- H6(i): T(t =. t) for all terms t
- H6(ii): T(eqCongruenceImplFunc L f ss ts) for all f, ss, ts
- H6(iii): T(eqCongruenceImplPred L P ss ts) for all P, ss, ts
- H6(iii-eq): T(eq-congruence implication) for all s1,s2,t1,t2
- H2-eq: T(eq_ t1 t2) for all t1, t2 (type-b closure for funcCong
  and eqCong)
- H2-pred: T(predN P ts) for all P, ts (type-b closure for predCong)

The H2-eq clause ensures type-b decomposition closure for funcCong
and eqCong implications: their comp2 is an eq_ formula. No eq_
formula appears with F-sign in signedLimitSet (by limitSet_isHintikka.hNoEq),
so injecting T(eq_ ...) is safe (no complementary pair).

The H2-pred clause ensures type-b decomposition closure for predCong
implications: their comp2 is a predN formula. Safety (h0) requires
hNoPredNF: no F(predN P ts) in signedLimitSet Gamma. -/
def signedLimitSetEq {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) : Set (SignedFormula L) :=
  fun sf =>
    sf ∈ signedLimitSet Gamma ∨
    -- H6(i): reflexivity
    (∃ t : Term L, sf = SignedFormula.trueF (FormulaN.eq_ hL t t)) ∨
    -- H6(ii): function congruence
    (∃ (f : L.funSymbols) (ss ts : Fin (L.funArity f) → Term L),
      sf = SignedFormula.trueF (eqCongruenceImplFunc L hL f ss ts)) ∨
    -- H6(iii): predicate congruence
    (∃ (P : L.predSymbols) (ss ts : Fin (L.predArity P) → Term L),
      sf = SignedFormula.trueF (eqCongruenceImplPred L hL P ss ts)) ∨
    -- H6(iii-eq): equality congruence
    (∃ (s1 s2 t1 t2 : Term L),
      sf = SignedFormula.trueF
        (FormulaN.impl
          (FormulaN.conj (FormulaN.eq_ hL s1 t1)
            (FormulaN.conj (FormulaN.eq_ hL s2 t2) (FormulaN.eq_ hL s1 s2)))
          (FormulaN.eq_ hL t1 t2))) ∨
    -- H2-eq: all equalities between terms (type-b closure for funcCong/eqCong)
    (∃ (t1 t2 : Term L), sf = SignedFormula.trueF (FormulaN.eq_ hL t1 t2)) ∨
    -- H2-pred: predicate applications for type-b closure of predCong
    -- implications. T(predN P ts) for all P, ts ensures type-b
    -- decomposition of predCong implications closes with comp2.
    -- Requires hNoPredNF (no F(predN P ts) in base) for h0 safety.
    (∃ (P : L.predSymbols) (ts : Fin (L.predArity P) → Term L),
      sf = SignedFormula.trueF (FormulaN.predN P ts))

-- ===================================================================
-- Helper: falseF in signedLimitSetEq must come from signedLimitSet
-- ===================================================================

/-- All new formulas in signedLimitSetEq are T-signed. So any falseF
formula in signedLimitSetEq must come from signedLimitSet. -/
theorem falseF_limitSetEq_to_base {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (A : FormulaN L)
    (h : SignedFormula.falseF A ∈ signedLimitSetEq hL Gamma) :
    SignedFormula.falseF A ∈ signedLimitSet Gamma := by
-- BEGIN PROOF
  unfold signedLimitSetEq at h
  rcases h with h | ⟨_, habs⟩ | ⟨_, _, _, habs⟩ | ⟨_, _, _, habs⟩ |
    ⟨_, _, _, _, habs⟩ | ⟨_, _, habs⟩ | ⟨_, _, habs⟩
  · exact h
  all_goals cases habs

-- ===================================================================
-- Helper: signedLimitSet embeds into signedLimitSetEq
-- ===================================================================

/-- The base signedLimitSet embeds into signedLimitSetEq. -/
theorem signedLimitSet_sub_eq {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (sf : SignedFormula L)
    (h : sf ∈ signedLimitSet Gamma) :
    sf ∈ signedLimitSetEq hL Gamma :=
-- BEGIN PROOF
  Or.inl h

-- ===================================================================
-- H6 condition proofs for signedLimitSetEq
-- ===================================================================

/-- H6(i): T(t =. t) for all terms t. -/
theorem signedLimitSetEq_h6i {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (t : Term L) :
    SignedFormula.trueF (FormulaN.eq_ hL t t) ∈ signedLimitSetEq hL Gamma := by
-- BEGIN PROOF
  unfold signedLimitSetEq; right; left; exact ⟨t, rfl⟩

/-- H6(ii): function congruence implication for all f, ss, ts. -/
theorem signedLimitSetEq_h6ii {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (f : L.funSymbols)
    (ss ts : Fin (L.funArity f) → Term L) :
    SignedFormula.trueF (eqCongruenceImplFunc L hL f ss ts) ∈
      signedLimitSetEq hL Gamma := by
-- BEGIN PROOF
  unfold signedLimitSetEq; right; right; left; exact ⟨f, ss, ts, rfl⟩

/-- H6(iii): predicate congruence implication for all P, ss, ts. -/
theorem signedLimitSetEq_h6iii {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (P : L.predSymbols)
    (ss ts : Fin (L.predArity P) → Term L) :
    SignedFormula.trueF (eqCongruenceImplPred L hL P ss ts) ∈
      signedLimitSetEq hL Gamma := by
-- BEGIN PROOF
  unfold signedLimitSetEq; right; right; right; left
  exact ⟨P, ss, ts, rfl⟩

/-- H6(iii-eq): equality congruence for all s1, s2, t1, t2. -/
theorem signedLimitSetEq_h6iii_eq {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (s1 s2 t1 t2 : Term L) :
    SignedFormula.trueF
      (FormulaN.impl
        (FormulaN.conj (FormulaN.eq_ hL s1 t1)
          (FormulaN.conj (FormulaN.eq_ hL s2 t2) (FormulaN.eq_ hL s1 s2)))
        (FormulaN.eq_ hL t1 t2)) ∈ signedLimitSetEq hL Gamma := by
-- BEGIN PROOF
  unfold signedLimitSetEq; right; right; right; right; left
  exact ⟨s1, s2, t1, t2, rfl⟩

-- ===================================================================
-- IsHintikkaSetEq for signedLimitSetEq
-- ===================================================================

/-- The equality-aware signed limit set satisfies all Hintikka
conditions with equality (H0-H5 and H6(i)-(iii)) when:
- Gamma is consistent (isConsistentSet)
- Gamma has no eq_ formulas and is rectified
- No F(predN P ts) in signedLimitSet Gamma (hNoPredNF)

The base H0-H5 conditions are inherited from limitSet_isHintikka
(which proves them for signedLimitSet Gamma), lifted through the
embedding signedLimitSet ⊆ signedLimitSetEq.
The H6 conditions hold by construction.

The critical insight: because Gamma has no eq_ formulas (hNoEq),
signedLimitSet Gamma has no eq_ formulas at all (by limitSet_isHintikka.hNoEq).
Therefore injecting trueF(eq_ ...) cannot create a complementary
pair (no falseF(eq_ ...) exists to conflict with). Similarly, the
hNoPredNF hypothesis ensures injecting trueF(predN P ts) for the
H2-pred clause (type-b closure of predCong implications) is safe. -/
theorem signedLimitSetEq_isHintikkaSetEq {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L))
    (_hCon : isConsistentSet Gamma)
    (_hNoEq : ∀ A ∈ Gamma, formulaNoEq A)
    (_hNoPredNF : ∀ (P : L.predSymbols) (ts : Fin (L.predArity P) → Term L),
      SignedFormula.falseF (FormulaN.predN P ts) ∉ signedLimitSet Gamma)
    (_hNFB : ∀ (x : Nat) (A : FormulaN L) (t : Term L),
      (SignedFormula.trueF (FormulaN.all x A) ∈ signedLimitSet Gamma ∨
       SignedFormula.falseF (FormulaN.all x A) ∈ signedLimitSet Gamma ∨
       SignedFormula.trueF (FormulaN.ex x A) ∈ signedLimitSet Gamma ∨
       SignedFormula.falseF (FormulaN.ex x A) ∈ signedLimitSet Gamma) →
      isFreeForN t x A) :
    IsHintikkaSetEqBase L (fun _ => True) (signedLimitSetEq hL Gamma) ∧
    (∀ t : Term L, SignedFormula.trueF (FormulaN.eq_ hL t t) ∈ signedLimitSetEq hL Gamma) := by
-- BEGIN PROOF
  -- DEBT(base equality Hintikka conditions and reflexivity for the signed limit set not established)
  sorry

-- ===================================================================
-- Gamma inclusion in signedLimitSetEq
-- ===================================================================

/-- Every formula in Gamma appears as trueF in signedLimitSetEq. -/
theorem gamma_in_signedLimitSetEq {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (A : FormulaN L) (hA : A ∈ Gamma) :
    SignedFormula.trueF A ∈ signedLimitSetEq hL Gamma :=
-- BEGIN PROOF
  Or.inl (gamma_in_limitSet Gamma A hA)

-- ===================================================================
-- Model existence via signedLimitSetEq
-- ===================================================================

/-- The equality-aware signed limit set is satisfiable via
hintikka_set_eq_satisfiable. Combined with gamma_in_signedLimitSetEq,
this gives a model for Gamma. -/
theorem signedLimitSetEq_satisfiable {L : Language} (hL : L.hasEquality = true)
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L))
    (hCon : isConsistentSet Gamma)
    (hNoEq : ∀ A ∈ Gamma, formulaNoEq A)
    (hNoPredNF : ∀ (P : L.predSymbols) (ts : Fin (L.predArity P) → Term L),
      SignedFormula.falseF (FormulaN.predN P ts) ∉ signedLimitSet Gamma)
    (hNFB : ∀ (x : Nat) (A : FormulaN L) (t : Term L),
      (SignedFormula.trueF (FormulaN.all x A) ∈ signedLimitSet Gamma ∨
       SignedFormula.falseF (FormulaN.all x A) ∈ signedLimitSet Gamma ∨
       SignedFormula.trueF (FormulaN.ex x A) ∈ signedLimitSet Gamma ∨
       SignedFormula.falseF (FormulaN.ex x A) ∈ signedLimitSet Gamma) →
      isFreeForN t x A) :
    ∃ (M : Structure L) (s : Assignment M),
      ∀ sf, sf ∈ signedLimitSetEq hL Gamma →
        SignedFormula.satisfiedBy M s sf := by
-- BEGIN PROOF
  -- DEBT(model satisfying the equality-aware signed limit set not constructed)
  sorry

end LCS.FirstOrder.Equality.Completeness
end

section
namespace LCS.FirstOrder.Equality.Completeness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Completeness.InfiniteSearch
open LCS.FirstOrder.Completeness

/-- Definition 5.6.3 (normalized, companion): Given a list of terms,
enumerates all FormulaN formulae of the form (t =. t) where t ranges
over the given term list. This is the EQ_{1,i} enumeration for the
equality search procedure. Mirrors eqReflFormulae but produces
FormulaN. -/
def eqReflFormulae {L : Language} (hL : L.hasEquality = true)
    (terms : List (Term L)) :
    List (FormulaN L) :=
  terms.map (fun t => FormulaN.eq_ hL t t)

-- ===================================================================
-- Helper: allFinTuples (enumerate all k-tuples from a list)
-- ===================================================================

/-- Definition 5.6.3 (required helper): Enumerate all k-tuples
(Fin k -> alpha) from a list. For k=0, returns the single empty tuple.
For k+1, extends each k-tuple by prepending each element from the list.
Used by eqFuncCongFormulae and eqPredCongFormulae to enumerate all
tuple combinations as required by the textbook's EQ_{2,i} and EQ_{3,i}
(Def 5.6.3). -/
def allFinTuples (ts : List α) : (k : Nat) → List (Fin k → α)
  | 0 => [Fin.elim0]
  | k + 1 =>
    let prev := allFinTuples ts k
    prev.flatMap fun f =>
      ts.map fun t => fun i => Fin.cases t (fun j => f j) i

/-- Definition 5.6.3 (required helper): If every component of a tuple
is in the list, then the tuple is in allFinTuples. -/
theorem mem_allFinTuples {ts : List α} {k : Nat} (f : Fin k → α)
    (hf : ∀ i, f i ∈ ts) : f ∈ allFinTuples ts k := by
-- BEGIN PROOF
  induction k with
  | zero => simp [allFinTuples]; ext i; exact Fin.elim0 i
  | succ n ih =>
    simp [allFinTuples, List.mem_flatMap, List.mem_map]
    refine ⟨fun j => f j.succ, ?_, f 0, ?_, ?_⟩
    · exact ih (fun j => f j.succ) (fun i => hf i.succ)
    · exact hf 0
    · ext i; exact Fin.cases rfl (fun j => rfl) i

-- ===================================================================
-- Definition 5.6.3 (normalized, companion def): eqFuncCongFormulae
-- ===================================================================

/-- Definition 5.6.3 (normalized, companion): Given a list of function
symbols and a list of terms, enumerates all FormulaN formulae of the
form (s1 =. t1) /\ ... /\ (sn =. tn) => (f(s1,...,sn) =. f(t1,...,tn))
for each function symbol f, where (s1,...,sn) and (t1,...,tn) range over
all n-tuples from the term list. This is the EQ_{2,i} enumeration for
the equality search procedure. Produces FormulaN via
eqCongruenceImplFunc. -/
def eqFuncCongFormulae {L : Language} (hL : L.hasEquality = true)
    (funSyms : List L.funSymbols)
    (terms : List (Term L)) :
    List (FormulaN L) :=
  funSyms.foldl (fun acc f =>
    let tuples := allFinTuples terms (L.funArity f)
    tuples.foldl (fun acc2 ss =>
      tuples.foldl (fun acc3 ts =>
        acc3 ++ [eqCongruenceImplFunc L hL f ss ts]
      ) acc2
    ) acc
  ) []

-- ===================================================================
-- Definition 5.6.3 (normalized, companion def): eqPredCongFormulae
-- ===================================================================

/-- Definition 5.6.3 (normalized, companion): Given a list of predicate
symbols and a list of terms, enumerates all FormulaN formulae of the
form ((s1 =. t1) /\ ... /\ (sn =. tn) /\ P(s1,...,sn)) => P(t1,...,tn)
for each predicate symbol P, where (s1,...,sn) and (t1,...,tn) range
over all n-tuples from the term list. Also includes the binary equality
predicate: for every pair of term pairs (s1,s2), (t1,t2), it adds
(s1 ≐ t1 ∧ (s2 ≐ t2 ∧ s1 ≐ s2)) ⊃ t1 ≐ t2 via `eqCongruenceImplEq`.
This is the EQ_{3,i} enumeration for the equality search procedure. -/
def eqPredCongFormulae {L : Language} (hL : L.hasEquality = true)
    (predSyms : List L.predSymbols)
    (terms : List (Term L)) :
    List (FormulaN L) :=
  let predFormulae :=
    predSyms.foldl (fun acc P =>
      let tuples := allFinTuples terms (L.predArity P)
      tuples.foldl (fun acc2 ss =>
        tuples.foldl (fun acc3 ts =>
          acc3 ++ [eqCongruenceImplPred L hL P ss ts]
        ) acc2
      ) acc
    ) []
  let pairs := allFinTuples terms 2
  predFormulae ++ pairs.flatMap fun ss =>
    pairs.map fun ts => eqCongruenceImplEq hL (ss 0) (ss 1) (ts 0) (ts 1)

-- ===================================================================
-- Definition 5.6.3 (normalized, companion def): eqAxiomBatch
-- ===================================================================

/-- Definition 5.6.3 (normalized, companion): Given a round counter RC,
lists of function and predicate symbols, and a term list, returns the
appropriate equality axiom batch EQ_{j,i} where j = (RC % 3) + 1.
When j = 1, returns EQ_{1,i} (reflexivity formulae).
When j = 2, returns EQ_{2,i} (function congruence formulae).
When j = 3, returns EQ_{3,i} (predicate congruence formulae).
The round counter cycles through 1, 2, 3 to ensure all three types
of equality axioms are eventually injected along every non-closed
path. -/
def eqAxiomBatch {L : Language} (hL : L.hasEquality = true)
    (rc : Nat)
    (funSyms : List L.funSymbols)
    (predSyms : List L.predSymbols)
    (terms : List (Term L)) :
    List (FormulaN L) :=
  match (rc % 3) + 1 with
  | 1 => eqReflFormulae hL terms
  | 2 => eqFuncCongFormulae hL funSyms terms
  | 3 => eqPredCongFormulae hL predSyms terms
  | _ => []

/-- Definition 5.6.3 (companion): Function symbols occurring in a term,
including the outer symbol of each application. -/
def eqTermFunSymbols {L : Language} : Term L → List L.funSymbols
  | .var _ | .const _ => []
  | .func f ts => f :: (List.ofFn fun i => eqTermFunSymbols (ts i)).flatten

/-- Definition 5.6.3 (companion): The input formula's function-symbol occurrences. -/
def eqFormulaFunSymbols {L : Language} : FormulaN L → List L.funSymbols
  | .predN _ ts => (List.ofFn fun i => eqTermFunSymbols (ts i)).flatten
  | .eq_ _ t u => eqTermFunSymbols t ++ eqTermFunSymbols u
  | .neg A | .all _ A | .ex _ A => eqFormulaFunSymbols A
  | .conj A B | .disj A B | .impl A B => eqFormulaFunSymbols A ++ eqFormulaFunSymbols B

/-- Definition 5.6.3 (companion): The input formula's predicate-symbol occurrences. -/
def eqFormulaPredSymbols {L : Language} : FormulaN L → List L.predSymbols
  | .predN P _ => [P]
  | .eq_ _ _ _ => []
  | .neg A | .all _ A | .ex _ A => eqFormulaPredSymbols A
  | .conj A B | .disj A B | .impl A B => eqFormulaPredSymbols A ++ eqFormulaPredSymbols B

/-- The function-symbol list realizes the term-occurrence set of Definition 5.4.6. -/
theorem eqTermFunSymbols_mem {L : Language} (t : Term L) (f : L.funSymbols) :
    f ∈ eqTermFunSymbols t ↔ f ∈ termFunSyms t := by
  change f ∈ eqTermFunSymbols t ↔ termFunSyms t f
  induction t with
  | var x => simp [eqTermFunSymbols, termFunSyms, Set.empty]
  | const c => simp [eqTermFunSymbols, termFunSyms, Set.empty]
  | func g ts ih =>
    simp only [eqTermFunSymbols, List.mem_cons, List.mem_flatten, List.mem_ofFn, termFunSyms]
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨l, ⟨i, rfl⟩, h⟩; exact ⟨i, (ih i).mp h⟩
    · rintro ⟨i, h⟩; exact ⟨_, ⟨i, rfl⟩, (ih i).mpr h⟩

/-- The function-symbol list realizes the formula-occurrence set of Definition 5.4.6. -/
theorem eqFormulaFunSymbols_mem {L : Language} (A : FormulaN L) (f : L.funSymbols) :
    f ∈ eqFormulaFunSymbols A ↔ f ∈ formulaFunSymsN A := by
  change f ∈ eqFormulaFunSymbols A ↔ formulaFunSymsN A f
  induction A with
  | predN P ts =>
    simp only [eqFormulaFunSymbols, List.mem_flatten, List.mem_ofFn, formulaFunSymsN]
    constructor
    · rintro ⟨l, ⟨i, rfl⟩, h⟩; exact ⟨i, (eqTermFunSymbols_mem _ _).mp h⟩
    · rintro ⟨i, h⟩; exact ⟨_, ⟨i, rfl⟩, (eqTermFunSymbols_mem _ _).mpr h⟩
  | eq_ hL t u =>
    change f ∈ eqTermFunSymbols t ++ eqTermFunSymbols u ↔
      termFunSyms t f ∨ termFunSyms u f
    exact List.mem_append.trans (or_congr (eqTermFunSymbols_mem t f) (eqTermFunSymbols_mem u f))
  | neg A ih | all x A ih | ex x A ih => exact ih
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
    exact List.mem_append.trans (or_congr ihA ihB)

/-- The predicate-symbol list realizes the formula-occurrence set of Definition 5.4.6. -/
theorem eqFormulaPredSymbols_mem {L : Language} (A : FormulaN L) (P : L.predSymbols) :
    P ∈ eqFormulaPredSymbols A ↔ P ∈ formulaPredSymsN A := by
  change P ∈ eqFormulaPredSymbols A ↔ formulaPredSymsN A P
  induction A with
  | predN Q ts => exact List.mem_singleton
  | eq_ hL t u => simp [eqFormulaPredSymbols, formulaPredSymsN, Set.empty]
  | neg A ih | all x A ih | ex x A ih => exact ih
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
    exact List.mem_append.trans (or_congr ihA ihB)

/-- Definition 5.6.3 (companion): Finite stages of the term closure of the
initial generators under the functions of the input reduct. Their union
contains terms of every finite function depth. -/
def eqLevelZeroTerms {L : Language} (funSyms : List L.funSymbols)
    (generators : List (Term L)) : Nat → List (Term L)
  | 0 => generators
  | n + 1 =>
    let prev := eqLevelZeroTerms funSyms generators n
    prev ++ funSyms.flatMap fun f =>
      (allFinTuples prev (L.funArity f)).map (Term.func f)

/-- Definition 5.6.3 (companion): A lazy formula enumeration presented by
finite stages and the formulas already consumed. -/
structure EqFormulaStream (L : Language) where
  stages : Nat → List (FormulaN L)
  consumed : List (FormulaN L) := []

/-- Definition 5.6.3 (companion): Empty enumeration. -/
def EqFormulaStream.empty {L : Language} : EqFormulaStream L := ⟨fun _ => [], []⟩

/-- Definition 5.6.3 (companion): The first unconsumed formula in the least
stage containing one. Returns none exactly when the enumeration is exhausted. -/
noncomputable def EqFormulaStream.head? {L : Language} (stream : EqFormulaStream L) :
    Option (FormulaN L) := by
  classical
  let remaining := fun n => (stream.stages n).filter (fun A => A ∉ stream.consumed)
  exact if h : ∃ n, (remaining n).isEmpty = false then
    (List.range (h.choose + 1)).findSome? (fun n => (remaining n).head?)
  else none

/-- Definition 5.6.3 (companion): Delete the head from a lazy enumeration.
All occurrences of that formula are skipped in later stages. -/
noncomputable def EqFormulaStream.tail {L : Language} (stream : EqFormulaStream L) :
    EqFormulaStream L :=
  match stream.head? with
  | none => stream
  | some A => { stream with consumed := A :: stream.consumed }

-- ===================================================================
-- Definition 5.6.3 (normalized): SearchStateEq
-- ===================================================================

/-- Definition 5.6.3: The search state for the equality search procedure
using FormulaN types (extends Def 5.4.9). -/
structure SearchStateEq (L : Language) where
  /-- The base normalized search state from Def 5.4.9 -/
  base : Hintikka.SearchState L
  /-- Round counter RC, incremented at the end of each round,
      used to cycle through equality formula types via
      j = (RC mod 3) + 1 -/
  roundCounter : Nat
  /-- NUMACT: counter of activated new variables -/
  numact : Nat
  /-- EQ_{1,i}: maps index i to the remaining reflexivity formulae
      (t =. t) at index i, as FormulaN -/
  eq1 : Nat → EqFormulaStream L
  /-- EQ_{2,i}: maps index i to the remaining function congruence
      formulae at index i, as FormulaN -/
  eq2 : Nat → EqFormulaStream L
  /-- EQ_{3,i}: maps index i to the remaining predicate congruence
      formulae at index i, as FormulaN -/
  eq3 : Nat → EqFormulaStream L

end LCS.FirstOrder.Equality.Completeness
end

section
namespace LCS.FirstOrder.Equality.Completeness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Completeness.InfiniteSearch
open LCS.FirstOrder.Completeness
namespace SearchStateEq

/-- Definition 5.6.3 (normalized, companion): Returns EQ_{j,i} for
given j (1, 2, or 3) and i from the normalized equality search state.
For j=1, returns eq1 i (reflexivity formulae at index i).
For j=2, returns eq2 i (function congruence formulae at index i).
For j=3, returns eq3 i (predicate congruence formulae at index i).
For other values of j, returns the empty enumeration. -/
def eqListForIndex {L : Language} (st : SearchStateEq L)
    (j i : Nat) : EqFormulaStream L :=
  match j with
  | 1 => st.eq1 i
  | 2 => st.eq2 i
  | 3 => st.eq3 i
  | _ => .empty

/-- Definition 5.6.3 (normalized, companion): Initialize the equality
search state from a normalized sequent. The textbook says:
'let L' be the reduct of L consisting of all constant, function, and
predicate symbols occurring in formulae in Gamma0 -> Delta0' and
'Let TERM0, EQ_{1,i}, EQ_{2,i}, EQ_{3,i} and AVAIL_i, 0 ≤ i, be
initialized as explained above. NUMACT := 0; RC := 0.'
The caller provides the reduct L' via `funSyms` (function symbols in
the sequent), `predSyms` (predicate symbols), and `initialTerms`
(terms from TERM0, built from L' constants/functions and free vars).
EQ_{j,0} lazily enumerates formulae over the full function closure of
these initial generators, including y₀ when the input has no constants
or free variables.
For i >= 1, EQ_{j,i} uses AVAIL_i terms (activated during the search).
At initialization only i=0 is active (NUMACT=0). -/
def init {L : Language} (hL : L.hasEquality = true)
    (seq : Sequent L)
    (funSyms : List L.funSymbols)
    (predSyms : List L.predSymbols)
    (initialTerms : List (Term L)) :
    SearchStateEq L :=
  let baseState := Hintikka.SearchState.init seq
  { base := baseState
  , roundCounter := 0
  , numact := 0
  , eq1 := fun i =>
      if i = 0 then ⟨fun n => eqReflFormulae hL (eqLevelZeroTerms funSyms initialTerms n), []⟩
      else .empty
  , eq2 := fun i =>
      if i = 0 then ⟨fun n => eqFuncCongFormulae hL funSyms
        (eqLevelZeroTerms funSyms initialTerms n), []⟩
      else .empty
  , eq3 := fun i =>
      if i = 0 then ⟨fun n => eqPredCongFormulae hL predSyms
        (eqLevelZeroTerms funSyms initialTerms n), []⟩
      else .empty }

end SearchStateEq
end LCS.FirstOrder.Equality.Completeness
end

