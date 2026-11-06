import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.Completeness
import Attach
import LCS.FirstOrder.Equality.HintikkaSets.ProofsStamp

section
namespace LCS.FirstOrder.Equality
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution (formulaSubstEvalDirectN)
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Completeness

/-- Definition 5.6.1 (companion): fold a list of formulae into a
conjunction. Returns the single formula if the list has one element;
conjoins left-to-right for multiple elements. For an empty list,
returns the provided default (trivial equality reflexivity formula). -/
@[blueprint "chap5__definition_5_6_1"]
def conjoinFormulae {L : Language} (default : FormulaN L) :
    List (FormulaN L) → FormulaN L
  | [] => default
  | [A] => A
  | A :: rest => FormulaN.conj A (conjoinFormulae default rest)

-- ===================================================================
-- Definition 5.6.1 (companion def): eqPairsList
-- ===================================================================

/-- Definition 5.6.1 (companion): build a list of equality pairs
(si doteq ti) from two Fin-indexed families of terms, collecting
indices 0..n-1. Requires `hL : L.hasEquality = true` so `.eq_`
can be constructed. -/
@[blueprint "chap5__definition_5_6_1"]
def eqPairsList {L : Language} (hL : L.hasEquality = true) {n : Nat}
    (ss ts : Fin n → Term L) : List (FormulaN L) :=
  (List.finRange n).map (fun i => FormulaN.eq_ hL (ss i) (ts i))

-- ===================================================================
-- Definition 5.6.1 (companion def): eqCongruenceImplFunc
-- ===================================================================

/-- Definition 5.6.1 (companion): The formula
(s1 doteq t1) and ... and (sn doteq tn) implies (f(s1,...,sn) doteq f(t1,...,tn)).
Builds the conjunction of equalities for each argument position, then forms
the implication to the equality of function applications. For n = 0, the
antecedent defaults to a reflexivity tautology. Requires
`hL : L.hasEquality = true`. -/
@[blueprint "chap5__definition_5_6_1"]
def eqCongruenceImplFunc (L : Language) (hL : L.hasEquality = true)
    (f : L.funSymbols)
    (ss ts : Fin (L.funArity f) → Term L) : FormulaN L :=
  let pairs := eqPairsList hL ss ts
  let consequent := FormulaN.eq_ hL (Term.func f ss) (Term.func f ts)
  let default := consequent  -- trivial case: 0-ary function
  FormulaN.impl (conjoinFormulae default pairs) consequent

-- ===================================================================
-- Definition 5.6.1 (companion def): eqCongruenceImplPred
-- ===================================================================

/-- Definition 5.6.1 (companion): The formula
((s1 doteq t1) and ... and (sn doteq tn) and P(s1,...,sn)) implies P(t1,...,tn).
Builds the conjunction of equalities and the premise predicate application,
then forms the implication to the conclusion predicate application.
For n = 0, the antecedent is just P(s1,...,sn). Requires
`hL : L.hasEquality = true`. -/
@[blueprint "chap5__definition_5_6_1"]
def eqCongruenceImplPred (L : Language) (hL : L.hasEquality = true)
    (P : L.predSymbols)
    (ss ts : Fin (L.predArity P) → Term L) : FormulaN L :=
  let pairs := eqPairsList hL ss ts
  let premisePred := FormulaN.predN P ss
  let consequent := FormulaN.predN P ts
  let antecedent := conjoinFormulae premisePred (pairs ++ [premisePred])
  FormulaN.impl antecedent consequent

-- ===================================================================
-- Definition 5.6.1: IsHintikkaSetEq
-- ===================================================================

/-- Definition 5.6.1 (companion — base): The base Hintikka conditions
H0-H6 on a signed set S, with H a term algebra over its occurrence
language L_S. Equality atoms are permitted, and quantified components
must satisfy the free-for condition. -/
@[blueprint "chap5__definition_5_6_1"]
structure IsHintikkaSetEqBase (L : Language) (H : Set (Term L))
    (S : Set (SignedFormula L)) : Prop where
  /-- H is a term algebra over the symbols occurring in S. -/
  hTA : IsTermAlgebraOver L S H
  /-- H0: No atomic formula and its conjugate are both in S -/
  h0 : ∀ (A : FormulaN L), A.isAtomic = true →
    ¬(SignedFormula.trueF A ∈ S ∧ SignedFormula.falseF A ∈ S)
  /-- H1: If a type-A formula is in S, then both components are in S -/
  h1 : ∀ (a : TypeA L), a.toSigned ∈ S → a.comp1 ∈ S ∧ a.comp2 ∈ S
  /-- H2: If a type-B formula is in S, then at least one component is in S -/
  h2 : ∀ (b : TypeB L), b.toSigned ∈ S → b.comp1 ∈ S ∨ b.comp2 ∈ S
  /-- H3: Every free-for component C(t), for t in H, belongs to S.
  H6 supplies the required free-for evidence. -/
  h3 : ∀ (c : TypeC L), c.toSigned ∈ S →
    ∀ (t : Term L), t ∈ H → ∀ h : isFreeForN t c.var c.body, c.comp t h ∈ S
  /-- H4: A type-D formula in S has a free-for witness t in H with D(t) in S. -/
  h4 : ∀ (d : TypeD L), d.toSigned ∈ S →
    ∃ (t : Term L), t ∈ H ∧ ∃ h : isFreeForN t d.var d.body, d.comp t h ∈ S
  /-- H5: Every variable occurring free in some formula of S is in H -/
  h5 : ∀ (sf : SignedFormula L), sf ∈ S →
    ∀ (x : Nat), x ∈ signedFormulaFreeVars sf → Term.var x ∈ H
  /-- H6: isFreeFor holds for quantified formulae in S -/
  h6 : ∀ (x : Nat) (A : FormulaN L) (t : Term L), t ∈ H →
    (SignedFormula.trueF (.all x A) ∈ S ∨
     SignedFormula.falseF (.all x A) ∈ S ∨
     SignedFormula.trueF (.ex x A) ∈ S ∨
     SignedFormula.falseF (.ex x A) ∈ S) →
    isFreeForN t x A

/-- Definition 5.6.1: A Hintikka set S with equality over a term algebra H
of the occurrence language L_S. Its base conditions include free-for
substitution. H6(i) requires reflexivity for every term in H. H6(ii)
requires function congruence for the function symbols occurring in S;
H6(iii) requires predicate congruence for the predicate
symbols occurring in S. Equality itself is covered by the explicit binary
predicate-congruence condition H6(iii-eq). -/
@[blueprint "chap5__definition_5_6_1" (main := true)]
structure IsHintikkaSetEq (L : Language) (hL : L.hasEquality = true)
    (H : Set (Term L))
    (S : Set (SignedFormula L)) : Prop where
  /-- The base conditions, including the term algebra over L_S and free-for substitution. -/
  base : IsHintikkaSetEqBase L H S
  /-- H6(i): For every term t in H, T(t doteq t) in S -/
  h6i : ∀ (t : Term L), t ∈ H →
    SignedFormula.trueF (FormulaN.eq_ hL t t) ∈ S
  /-- H6(ii): For every function symbol f occurring in S and terms
      s1,...,sn, t1,...,tn in H, the function congruence implication
      is in S -/
  h6ii : ∀ (f : L.funSymbols) (hf : f ∈ signedSetFunSyms S)
    (ss ts : Fin (L.funArity f) → Term L),
    (∀ i, ss i ∈ H) → (∀ i, ts i ∈ H) →
    SignedFormula.trueF (eqCongruenceImplFunc L hL f ss ts) ∈ S
  /-- H6(iii): For every predicate symbol P occurring in S and terms
      s1,...,sn, t1,...,tn in H, the predicate congruence implication
      is in S -/
  h6iii : ∀ (P : L.predSymbols) (hPS : P ∈ signedSetPredSyms S)
    (ss ts : Fin (L.predArity P) → Term L),
    (∀ i, ss i ∈ H) → (∀ i, ts i ∈ H) →
    SignedFormula.trueF (eqCongruenceImplPred L hL P ss ts) ∈ S
  /-- H6(iii-eq): Equality congruence — H6(iii) applied to doteq.
      Since eq_ is not a predicate symbol in our formalization, this
      condition is stated explicitly: for all s1, s2, t1, t2 in H,
      T(((s1 = t1) /\ (s2 = t2) /\ (s1 = s2)) -> (t1 = t2)) in S.
      This is the textbook's H6(iii) with P = doteq, n = 2. -/
  h6iii_eq : ∀ (s1 s2 t1 t2 : Term L),
    s1 ∈ H → s2 ∈ H → t1 ∈ H → t2 ∈ H →
    SignedFormula.trueF
      (FormulaN.impl
        (FormulaN.conj (FormulaN.eq_ hL s1 t1)
          (FormulaN.conj (FormulaN.eq_ hL s2 t2) (FormulaN.eq_ hL s1 s2)))
        (FormulaN.eq_ hL t1 t2)) ∈ S

-- ===================================================================
-- Definition 5.6.2 (companion def): eqCongruenceImplEq
-- ===================================================================

/-- Definition 5.6.2 (companion): The predicate congruence formula
for the binary equality predicate doteq (which the textbook
explicitly lists as included in H6(iii)):
((s1 doteq t1) and (s2 doteq t2) and (s1 doteq s2)) implies
(t1 doteq t2). This is the instance of predicate congruence when
the predicate is doteq with arity 2. Since doteq is not a member of
`L.predSymbols` in our formalization, this case must be stated
explicitly (mirroring `h6iii_eq` in `IsHintikkaSetEq`). -/
@[blueprint "chap5__definition_5_6_1"]
def eqCongruenceImplEq {L : Language} (hL : L.hasEquality = true)
    (s1 s2 t1 t2 : Term L) :
    FormulaN L :=
  FormulaN.impl
    (FormulaN.conj (FormulaN.eq_ hL s1 t1)
      (FormulaN.conj (FormulaN.eq_ hL s2 t2) (FormulaN.eq_ hL s1 s2)))
    (FormulaN.eq_ hL t1 t2)

-- ===================================================================
-- Lemma 5.6.1 (companion def): eqCongruence
-- ===================================================================

/-- Lemma 5.6.1 (companion): The congruence relation on terms
defined by the equality symbol in S. Two terms s and t are
congruent (s ~ t) iff T(s doteq t) is in S. Uses SignedFormula. -/
@[blueprint "chap5__lemma_5_6_1"]
def eqCongruence {L : Language} (hL : L.hasEquality = true)
    (S : Set (SignedFormula L))
    (s t : Term L) : Prop :=
  SignedFormula.trueF (FormulaN.eq_ hL s t) ∈ S

-- ===================================================================
-- Lemma 5.6.1 (companion theorem): eqCongruence_symm
-- ===================================================================

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- Lemma 5.6.1 (companion): Symmetry of the congruence relation:
if T(s doteq t) in S then T(t doteq s) in S, using H6(iii)
with doteq as predicate and H2. -/
theorem eqCongruence_symm {L : Language}
    {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    (hHS : IsHintikkaSetEq L hL H S)
    (s t : Term L) (hs : s ∈ H) (ht : t ∈ H)
    (h : eqCongruence hL S s t) : eqCongruence hL S t s :=
-- BEGIN PROOF
by
  -- Following the textbook proof of Lemma 5.6.1, step (2):
  -- From T(s = t) in S, use H6(iii-eq) with s1=s, s2=s, t1=t, t2=s
  -- to get T(((s = t) /\ (s = s) /\ (s = s)) -> (t = s)) in S.
  unfold eqCongruence
  have h6eq := hHS.h6iii_eq s s t s hs hs ht hs
  -- h6eq : T(((s = t) /\ (s = s) /\ (s = s)) -> (t = s)) ∈ S
  -- By H2 (type-b for implication): F(antecedent) ∈ S ∨ T(t = s) ∈ S
  have hb := hHS.base.h2 (TypeB.tImpl
    (FormulaN.conj (FormulaN.eq_ hL s t) (FormulaN.conj (FormulaN.eq_ hL s s) (FormulaN.eq_ hL s s)))
    (FormulaN.eq_ hL t s))
  simp only [TypeB.toSigned, TypeB.comp1, TypeB.comp2] at hb
  cases hb h6eq with
  | inr hgoal => exact hgoal
  | inl hF =>
    -- F(antecedent) ∈ S, i.e., F((s = t) /\ ((s = s) /\ (s = s))) ∈ S
    -- By H2 (type-b for conjunction): F(s = t) ∈ S ∨ F((s = s) /\ (s = s)) ∈ S
    have hb2 := hHS.base.h2 (TypeB.fConj (FormulaN.eq_ hL s t) (FormulaN.conj (FormulaN.eq_ hL s s) (FormulaN.eq_ hL s s)))
    simp only [TypeB.toSigned, TypeB.comp1, TypeB.comp2] at hb2
    cases hb2 hF with
    | inl hFst =>
      -- F(s = t) ∈ S contradicts H0 + T(s = t) ∈ S (which is h)
      exfalso
      exact hHS.base.h0 (FormulaN.eq_ hL s t) rfl ⟨h, hFst⟩
    | inr hFss =>
      -- F((s = s) /\ (s = s)) ∈ S
      -- By H2: F(s = s) ∈ S ∨ F(s = s) ∈ S
      have hb3 := hHS.base.h2 (TypeB.fConj (FormulaN.eq_ hL s s) (FormulaN.eq_ hL s s))
      simp only [TypeB.toSigned, TypeB.comp1, TypeB.comp2] at hb3
      cases hb3 hFss with
      | inl hFss' =>
        -- F(s = s) contradicts H0 + H6(i) (T(s = s) ∈ S)
        exfalso
        exact hHS.base.h0 (FormulaN.eq_ hL s s) rfl ⟨hHS.h6i s hs, hFss'⟩
      | inr hFss' =>
        exfalso
        exact hHS.base.h0 (FormulaN.eq_ hL s s) rfl ⟨hHS.h6i s hs, hFss'⟩

-- ===================================================================
-- Lemma 5.6.1 (companion theorem): eqCongruence_trans
-- ===================================================================

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- Lemma 5.6.1 (companion): Transitivity of the congruence relation:
if T(r doteq s) and T(s doteq t) in S then T(r doteq t) in S,
using symmetry, H6(iii), and H2. -/
theorem eqCongruence_trans {L : Language}
    {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    (hHS : IsHintikkaSetEq L hL H S)
    (r s t : Term L) (hr : r ∈ H) (hs : s ∈ H) (ht : t ∈ H)
    (hrs : eqCongruence hL S r s) (hst : eqCongruence hL S s t) :
    eqCongruence hL S r t :=
-- BEGIN PROOF
by
  unfold eqCongruence
  have hsr : eqCongruence hL S s r := eqCongruence_symm hHS r s hr hs hrs
  have h6eq := hHS.h6iii_eq s s r t hs hs hr ht
  have hb := hHS.base.h2 (TypeB.tImpl
    (FormulaN.conj (FormulaN.eq_ hL s r) (FormulaN.conj (FormulaN.eq_ hL s t) (FormulaN.eq_ hL s s)))
    (FormulaN.eq_ hL r t))
  simp only [TypeB.toSigned, TypeB.comp1, TypeB.comp2] at hb
  cases hb h6eq with
  | inr hgoal => exact hgoal
  | inl hF =>
    have hb2 := hHS.base.h2 (TypeB.fConj (FormulaN.eq_ hL s r) (FormulaN.conj (FormulaN.eq_ hL s t) (FormulaN.eq_ hL s s)))
    simp only [TypeB.toSigned, TypeB.comp1, TypeB.comp2] at hb2
    cases hb2 hF with
    | inl hFsr =>
      exfalso
      exact hHS.base.h0 (FormulaN.eq_ hL s r) rfl ⟨hsr, hFsr⟩
    | inr hFst_ss =>
      have hb3 := hHS.base.h2 (TypeB.fConj (FormulaN.eq_ hL s t) (FormulaN.eq_ hL s s))
      simp only [TypeB.toSigned, TypeB.comp1, TypeB.comp2] at hb3
      cases hb3 hFst_ss with
      | inl hFst' =>
        exfalso
        exact hHS.base.h0 (FormulaN.eq_ hL s t) rfl ⟨hst, hFst'⟩
      | inr hFss =>
        exfalso
        exact hHS.base.h0 (FormulaN.eq_ hL s s) rfl ⟨hHS.h6i s hs, hFss⟩

-- ===================================================================
-- Lemma 5.6.1 (companion theorem): eqCongruence_equiv
-- ===================================================================

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- Lemma 5.6.1 (companion): The congruence relation restricted to H
is an equivalence relation: reflexivity from H6(i), symmetry from
H6(iii-eq)+H2, transitivity from symmetry+H6(iii-eq)+H2. The relation
is stated on the subtype { t : Term L // t ∈ H } so that reflexivity
is well-typed (every element of the subtype is in H by definition). -/
theorem eqCongruence_equiv {L : Language}
    {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    (hHS : IsHintikkaSetEq L hL H S) :
    Equivalence (fun (s t : { t : Term L // t ∈ H }) =>
      eqCongruence hL S s.val t.val) :=
-- BEGIN PROOF
by
  constructor
  · -- Reflexivity: by H6(i), T(t = t) ∈ S for every t ∈ H
    intro ⟨x, hx⟩
    exact hHS.h6i x hx
  · -- Symmetry: by eqCongruence_symm
    intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    exact eqCongruence_symm hHS x y hx hy hxy
  · -- Transitivity: by eqCongruence_trans
    intro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ hxy hyz
    exact eqCongruence_trans hHS x y z hx hy hz hxy hyz

-- ===================================================================
-- Helper: false conjunction of nonempty list with all true atomic
-- components is absurd in a Hintikka set.
-- ===================================================================

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- Helper: If F(conjoinFormulae default fs) ∈ S where fs is nonempty,
T(fi) ∈ S for every fi in fs, and all fi are atomic, then False.
Uses H0 and H2 (TypeB.fConj). -/
theorem falseConjoinContra {L : Language}
    {S : Set (SignedFormula L)}
    (h0 : ∀ (A : FormulaN L), A.isAtomic = true →
      ¬(SignedFormula.trueF A ∈ S ∧ SignedFormula.falseF A ∈ S))
    (h2 : ∀ (b : TypeB L), b.toSigned ∈ S → b.comp1 ∈ S ∨ b.comp2 ∈ S)
    (default : FormulaN L) (fs : List (FormulaN L))
    (hne : fs ≠ [])
    (hF : SignedFormula.falseF (conjoinFormulae default fs) ∈ S)
    (hTs : ∀ F, F ∈ fs → SignedFormula.trueF F ∈ S)
    (hAt : ∀ F, F ∈ fs → F.isAtomic = true) :
    False := by
-- BEGIN PROOF
  induction fs with
  | nil => exact absurd rfl hne
  | cons A rest ih =>
    have hmem_head : A ∈ A :: rest := List.Mem.head _
    match rest with
    | [] =>
      simp only [conjoinFormulae] at hF
      exact h0 A (hAt A hmem_head) ⟨hTs A hmem_head, hF⟩
    | B :: tail =>
      simp only [conjoinFormulae] at hF
      have hb2 := h2 (TypeB.fConj A (conjoinFormulae default (B :: tail)))
      simp only [TypeB.toSigned, TypeB.comp1, TypeB.comp2] at hb2
      cases hb2 hF with
      | inl hFA =>
        exact h0 A (hAt A hmem_head) ⟨hTs A hmem_head, hFA⟩
      | inr hFrest =>
        exact ih (List.cons_ne_nil B tail) hFrest
          (fun F hF' => hTs F (List.Mem.tail _ hF'))
          (fun F hF' => hAt F (List.Mem.tail _ hF'))

/-- Lemma 5.6.1 (companion): If s_i ~ t_i for all i, then
f(s1,...,sn) ~ f(t1,...,tn), using H6(ii) and H2. Ensures
well-definedness of the function interpretation on equivalence
classes. -/
theorem eqCongruence_func {L : Language}
    {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    (hHS : IsHintikkaSetEq L hL H S)
    (f : L.funSymbols) (hf : f ∈ signedSetFunSyms S)
    (ss ts : Fin (L.funArity f) → Term L)
    (hss : ∀ i, ss i ∈ H) (hts : ∀ i, ts i ∈ H)
    (hcong : ∀ i, eqCongruence hL S (ss i) (ts i)) :
    eqCongruence hL S (Term.func f ss) (Term.func f ts) :=
-- BEGIN PROOF
by
  have h6ii := hHS.h6ii f hf ss ts hss hts
  have hb := hHS.base.h2 (TypeB.tImpl
    (conjoinFormulae (FormulaN.eq_ hL (Term.func f ss) (Term.func f ts))
      (eqPairsList hL ss ts))
    (FormulaN.eq_ hL (Term.func f ss) (Term.func f ts)))
  simp only [TypeB.toSigned, TypeB.comp1, TypeB.comp2] at hb
  unfold eqCongruence
  cases hb h6ii with
  | inr h => exact h
  | inl hF =>
    exfalso
    by_cases hn : L.funArity f = 0
    · have hpairs_nil : eqPairsList hL ss ts = [] := by
        simp [eqPairsList, List.finRange, hn]
      rw [hpairs_nil] at hF
      simp only [conjoinFormulae] at hF
      have hss_eq : ss = ts := funext (fun i => absurd (Fin.pos i) (by omega))
      rw [hss_eq] at hF
      have hT := hHS.h6i (Term.func f ts) (hHS.base.hTA.closedFunc f hf ts hts)
      exact hHS.base.h0 (FormulaN.eq_ hL (Term.func f ts) (Term.func f ts)) rfl ⟨hT, hF⟩
    · have hpos : 0 < L.funArity f := Nat.pos_of_ne_zero hn
      have hne : eqPairsList hL ss ts ≠ [] := by
        intro h
        have : (eqPairsList hL ss ts).length = 0 := by rw [h]; rfl
        simp [eqPairsList, List.length_map, List.length_finRange] at this
        omega
      exact falseConjoinContra hHS.base.h0 hHS.base.h2
        (FormulaN.eq_ hL (Term.func f ss) (Term.func f ts))
        (eqPairsList hL ss ts) hne hF
        (fun F hF' => by
          simp [eqPairsList, List.mem_map] at hF'
          obtain ⟨i, _, rfl⟩ := hF'
          exact hcong i)
        (fun F hF' => by
          simp [eqPairsList, List.mem_map] at hF'
          obtain ⟨i, _, rfl⟩ := hF'
          exact rfl) /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

-- ===================================================================
-- Lemma 5.6.1 (companion theorem): eqCongruence_pred
-- ===================================================================

/-- Lemma 5.6.1 (companion): Negative predicate membership is invariant
under pointwise equality congruence of argument tuples in H. This includes
nullary predicates, whose argument tuples are empty, and makes the printed
predicate interpretation independent of the chosen representatives. -/
theorem eqCongruence_falsePred {L : Language}
    {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    (hHS : IsHintikkaSetEq L hL H S)
    (P : L.predSymbols)
    (ss ts : Fin (L.predArity P) → Term L)
    (hss : ∀ i, ss i ∈ H) (hts : ∀ i, ts i ∈ H)
    (hcong : ∀ i, eqCongruence hL S (ss i) (ts i)) :
    (SignedFormula.falseF (FormulaN.predN P ss) ∈ S ↔
     SignedFormula.falseF (FormulaN.predN P ts) ∈ S) := by
  have tailFalse (A : FormulaN L) (fs : List (FormulaN L))
      (hTs : ∀ F ∈ fs, SignedFormula.trueF F ∈ S)
      (hAt : ∀ F ∈ fs, F.isAtomic = true)
      (hF : SignedFormula.falseF (conjoinFormulae A (fs ++ [A])) ∈ S) :
      SignedFormula.falseF A ∈ S := by
    induction fs with
    | nil => exact hF
    | cons B rest ih =>
      have hConj : conjoinFormulae A ((B :: rest) ++ [A]) =
          FormulaN.conj B (conjoinFormulae A (rest ++ [A])) := by
        cases rest <;> rfl
      rw [hConj] at hF
      have hb := hHS.base.h2 (TypeB.fConj B (conjoinFormulae A (rest ++ [A]))) hF
      rcases hb with hB | hRest
      · exact False.elim (hHS.base.h0 B (hAt B List.mem_cons_self)
          ⟨hTs B List.mem_cons_self, hB⟩)
      · exact ih (fun F h => hTs F (List.Mem.tail _ h))
          (fun F h => hAt F (List.Mem.tail _ h)) hRest
  have forward : ∀ (uu vv : Fin (L.predArity P) → Term L),
      (∀ i, eqCongruence hL S (uu i) (vv i)) →
      (∀ i, uu i ∈ H) → (∀ i, vv i ∈ H) →
      SignedFormula.falseF (FormulaN.predN P uu) ∈ S →
      SignedFormula.falseF (FormulaN.predN P vv) ∈ S := by
    intro uu vv hc huu hvv hFuu
    have hPS : P ∈ signedSetPredSyms S :=
      ⟨SignedFormula.falseF (FormulaN.predN P uu), hFuu, rfl⟩
    have hImpl := hHS.h6iii P hPS vv uu hvv huu
    have hb := hHS.base.h2 (TypeB.tImpl
      (conjoinFormulae (FormulaN.predN P vv)
        (eqPairsList hL vv uu ++ [FormulaN.predN P vv]))
      (FormulaN.predN P uu)) hImpl
    rcases hb with hF | hTuu
    · apply tailFalse (FormulaN.predN P vv) (eqPairsList hL vv uu) _ _ hF
      · intro F hF'
        simp only [eqPairsList, List.mem_map] at hF'
        obtain ⟨i, _, rfl⟩ := hF'
        exact eqCongruence_symm hHS (uu i) (vv i) (huu i) (hvv i) (hc i)
      · intro F hF'
        simp only [eqPairsList, List.mem_map] at hF'
        obtain ⟨i, _, rfl⟩ := hF'
        rfl
    · exact False.elim (hHS.base.h0 (.predN P uu) rfl ⟨hTuu, hFuu⟩)
  exact ⟨forward ss ts hcong hss hts,
    forward ts ss (fun i => eqCongruence_symm hHS (ss i) (ts i)
      (hss i) (hts i) (hcong i)) hts hss⟩ /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

-- ===================================================================
-- Lemma 5.6.1 (companion theorem): quotientTermEvalIdentity
-- ===================================================================

-- ===================================================================
-- Lemma 5.6.1: hintikka_set_eq_satisfiable
-- ===================================================================

/-- Lemma 5.6.1 (companion): Equality in S induces a setoid on H. -/
@[blueprint "chap5__lemma_5_6_1"]
noncomputable def eqSetoid {L : Language}
    (hL : L.hasEquality = true)
    (H : Set (Term L)) (S : Set (SignedFormula L))
    (hHS : IsHintikkaSetEq L hL H S) :
    Setoid { t : Term L // t ∈ H } :=
  ⟨fun s t => eqCongruence hL S s.val t.val,
   eqCongruence_equiv hHS⟩

-- Abbreviation for the quotient type.
@[blueprint "chap5__lemma_5_6_1"]
abbrev QType {L : Language}
    (hL : L.hasEquality = true)
    (H : Set (Term L)) (S : Set (SignedFormula L))
    (hHS : IsHintikkaSetEq L hL H S) :=
  @Quotient { t : Term L // t ∈ H } (eqSetoid hL H S hHS)

@[blueprint "chap5__lemma_5_6_1"]
noncomputable abbrev qmk {L : Language}
    {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    {hHS : IsHintikkaSetEq L hL H S}
    (a : { t : Term L // t ∈ H }) : QType hL H S hHS :=
  @Quotient.mk _ (eqSetoid hL H S hHS) a

-- For n-ary operations on the quotient, we choose representatives
-- using Quotient.inductionOn and prove independence.
-- interpFunc: given quotient args, pick reps, apply func, quotient
-- the result. Well-definedness follows from eqCongruence_func.

-- Helper: given a function on reps that respects the setoid
-- on each argument, lift to a function on quotients.
-- Uses Classical.choose for representative selection.
noncomputable def chooseRep {L : Language}
    {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    {hHS : IsHintikkaSetEq L hL H S}
    (q : QType hL H S hHS) : { t : Term L // t ∈ H } :=
  Classical.choose (@Quotient.inductionOn
    { t : Term L // t ∈ H } (eqSetoid hL H S hHS)
    (fun q' => ∃ (a : { t : Term L // t ∈ H }),
      q' = @Quotient.mk _ (eqSetoid hL H S hHS) a)
    q (fun a => ⟨a, rfl⟩)) /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

noncomputable def finQuotLift {L : Language}
    {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    {hHS : IsHintikkaSetEq L hL H S}
    {β : Sort _} {n : Nat}
    (g : (Fin n → { t : Term L // t ∈ H }) → β)
    (_hg : ∀ xs ys : Fin n → { t : Term L // t ∈ H },
      (∀ i, @Setoid.r _ (eqSetoid hL H S hHS) (xs i) (ys i)) → g xs = g ys)
    (args : Fin n → QType hL H S hHS) : β :=
  g (fun i => chooseRep (args i)) /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

-- The key property of finQuotLift: when all args are qmk of known values,
-- the result agrees with applying g directly.

/-- Lemma 5.6.1 (companion): The model with carrier H modulo equality in S.
Function and constant symbols of L_S act on representatives by term construction;
those outside L_S receive a fixed default interpretation. A predicate atom is
false exactly when its negative signed atom belongs to S; positive and unmentioned
atoms are true, including predicates of rank zero. -/
@[blueprint "chap5__lemma_5_6_1"]
noncomputable def quotientStructureEq {L : Language}
    (hL : L.hasEquality = true)
    (H : Set (Term L)) (S : Set (SignedFormula L))
    (hHS : IsHintikkaSetEq L hL H S) : Structure L := by
  classical
  let default : QType hL H S hHS := qmk
    ⟨hHS.base.hTA.nonempty.choose, hHS.base.hTA.nonempty.choose_spec⟩
  exact {
    carrier := QType hL H S hHS
    carrierNonempty := ⟨default⟩
    interpFunc := fun f args => if hf : f ∈ signedSetFunSyms S then
      finQuotLift
        (fun reps => qmk ⟨Term.func f (fun i => (reps i).val),
          hHS.base.hTA.closedFunc f hf _ (fun i => (reps i).property)⟩)
        (fun xs ys h => by
          apply Quotient.sound
          exact eqCongruence_func hHS f hf
            (fun i => (xs i).val) (fun i => (ys i).val)
            (fun i => (xs i).property) (fun i => (ys i).property) h)
        args
      else default
    interpConst := fun c => if hc : c ∈ signedSetConstSyms S then
      qmk ⟨Term.const c, hHS.base.hTA.closedConst c hc⟩ else default
    interpPred := fun P args =>
      finQuotLift
        (fun reps => SignedFormula.falseF (FormulaN.predN P (fun i => (reps i).val)) ∉ S)
        (fun xs ys h => propext (not_congr (eqCongruence_falsePred hHS P
          (fun i => (xs i).val) (fun i => (ys i).val)
          (fun i => (xs i).property) (fun i => (ys i).property) h))) args }

-- Helper: terms with all free vars in H are in H.

-- Identity assignment for the quotient structure.
@[blueprint "chap5__lemma_5_6_1"]
noncomputable def quotAssignment {L : Language}
    (hL : L.hasEquality = true)
    (H : Set (Term L)) (S : Set (SignedFormula L))
    (hHS : IsHintikkaSetEq L hL H S) :
    Assignment (quotientStructureEq hL H S hHS) :=
  open Classical in
  fun x =>
    if h : Term.var x ∈ H then
      qmk ⟨Term.var x, h⟩
    else
      qmk ⟨hHS.base.hTA.nonempty.choose, hHS.base.hTA.nonempty.choose_spec⟩

/-- Lemma 5.6.1: Every equality Hintikka set over the occurrence-language
term algebra H is satisfied by the identity assignment in quotientStructureEq,
whose carrier is H modulo the equality relation induced by S. -/
@[blueprint "chap5__lemma_5_6_1" (main := true)]
theorem hintikka_set_eq_satisfiable {L : Language}
    (hL : L.hasEquality = true)
    (H : Set (Term L)) (S : Set (SignedFormula L))
    (hHS : IsHintikkaSetEq L hL H S) :
    ∀ sf, sf ∈ S → SignedFormula.satisfiedBy
      (quotientStructureEq hL H S hHS) (quotAssignment hL H S hHS) sf 

end LCS.FirstOrder.Equality
end
