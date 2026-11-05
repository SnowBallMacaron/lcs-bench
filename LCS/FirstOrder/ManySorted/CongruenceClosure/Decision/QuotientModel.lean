import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Equality
import LCS.FirstOrder.ManySorted.CongruenceClosure
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.HerbrandSatisfaction
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.SemanticEquality
import Attach
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.QuotientModel.ProofsStamp

section
namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.FirstOrder.ManySorted.Equality
open LCS.FirstOrder.ManySorted.CongruenceClosure
open LCS.Propositional.Semantics

/-- Lemma 10.6.2 (companion): Each constant or variable `t` of sort `s`
is interpreted in the term algebra `C` as the term `t` itself (the leaf
case of the algebra's interpretation; the `interpConst` field and the
variable handling of `termAlgebra`). -/
@[blueprint "chap10__lemma_10_6_2"]
def constVarInterp {L : MSLanguage} (C : MSFormula L) (s : L.SortType)
    (t : TermCarrier C s) : TermCarrier C s :=
  t

/-- Lemma 10.6.2 (companion): The node of `G(C)` named by a `TERM(C)_s`
element `t` — the sorted term `⟨s, t.1⟩` together with its membership
proof. -/
@[blueprint "chap10__lemma_10_6_2"]
def carrierNode {L : MSLanguage} (C : MSFormula L) (s : L.SortType)
    (t : TermCarrier C s) : (graphOfConjunction C).Node :=
  ⟨⟨s, t.1⟩, t.2⟩

/-- Lemma 10.6.2 (companion): The congruence-closure relation `R*` lifted
to `TERM(C)_s` carrier elements: `t` and `u` are `R*`-related when their
nodes `⟨s, t.1⟩`, `⟨s, u.1⟩` are related by
`msCongruenceClosure (graphOfConjunction C) (positiveEquationRelation C) (positiveEquationRelation_sortSupported C)`. -/
@[blueprint "chap10__lemma_10_6_2"]
def closureRel {L : MSLanguage} (C : MSFormula L) (s : L.SortType)
    (t u : TermCarrier C s) : Prop :=
  msCongruenceClosure (graphOfConjunction C) (positiveEquationRelation C) (positiveEquationRelation_sortSupported C)
    (carrierNode C s t) (carrierNode C s u)

/-- Lemma 10.6.2 (companion): If `f z_1…z_k ∈ TERM(C)_s` and each `z_i` is
`R*`-related to `w_i` (both in `TERM(C)`), then the term `f z_1…z_k`
itself, packaged as a `TERM(C)_s` carrier element, is `R*`-related to
`f w_1…w_k` whenever the latter is also in `TERM(C)_s`. The function
congruence (2b) of `R*` lifted to carrier elements. -/
@[attach_debt, blueprint "chap10__lemma_10_6_2"]
theorem funcNode_closureRel {L : MSLanguage} (C : MSFormula L)
    (f : L.funSymbols)
    (ws ws' : (i : Fin (L.funRank f).1.length) →
      TermCarrier C ((L.funRank f).1.get i))
    (hw : termSetOfSort C (L.funRank f).2 (MSTerm.func f (fun i => (ws i).1)))
    (hw' : termSetOfSort C (L.funRank f).2 (MSTerm.func f (fun i => (ws' i).1)))
    (hcong : ∀ i, closureRel C ((L.funRank f).1.get i) (ws i) (ws' i)) :
    closureRel C (L.funRank f).2
      ⟨MSTerm.func f (fun i => (ws i).1), hw⟩
      ⟨MSTerm.func f (fun i => (ws' i).1), hw'⟩ 

/-- Lemma 10.6.2 (companion): The operation `f_C(y_1,…,y_k)` of the term
algebra, defined by cases on membership of `f y_1…y_k` in `TERM(C)_s`
(see `funOpC_case1/2/3`): direct membership (case 1), a `R*`-congruent
representative `f z_1…z_k ∈ TERM(C)_s` (case 2), or — when no representative
exists at all — the junk value `none` (case 3).
`noncomputable` because the cases are decided classically.

The carrier is PADDED with `Option` so that the operation is total even on
sorts `s ∉ S(C)` whose `TERM(C)_s` carrier is genuinely empty: there the
result is `none`. On sorts in `S(C)` the genuine term value is returned;
the padding only supplies a junk element for irrelevant sorts, so the
satisfaction of `C` is unaffected (FIX for issue f53e69a2). -/
@[blueprint "chap10__lemma_10_6_2"]
noncomputable def funOpC {L : MSLanguage} (C : MSFormula L) (f : L.funSymbols)
    (ys : (i : Fin (L.funRank f).1.length) →
      Option (TermCarrier C ((L.funRank f).1.get i))) :
    Option (TermCarrier C (L.funRank f).2) :=
  -- If any argument is the junk element `none`, the result is junk.
  letI := Classical.propDecidable (∀ i, (ys i).isSome)
  if hall : ∀ i, (ys i).isSome then
    let ws : (i : Fin (L.funRank f).1.length) →
        TermCarrier C ((L.funRank f).1.get i) := fun i => (ys i).get (hall i)
    let applied : MSTerm L (L.funRank f).2 :=
      MSTerm.func f (fun i => (ws i).1)
    letI := Classical.propDecidable (termSetOfSort C (L.funRank f).2 applied)
    -- Case 1: f y_1…y_k ∈ TERM(C)_s
    if h1 : termSetOfSort C (L.funRank f).2 applied then
      some ⟨applied, h1⟩
    -- Case 2: an `R*`-congruent representative f z_1…z_k ∈ TERM(C)_s
    else
      letI := Classical.propDecidable
        (∃ (zs : (i : Fin (L.funRank f).1.length) →
            TermCarrier C ((L.funRank f).1.get i)),
          (∀ i, closureRel C ((L.funRank f).1.get i) (ws i) (zs i)) ∧
            termSetOfSort C (L.funRank f).2 (MSTerm.func f (fun i => (zs i).1)))
      if h2 : ∃ (zs : (i : Fin (L.funRank f).1.length) →
            TermCarrier C ((L.funRank f).1.get i)),
          (∀ i, closureRel C ((L.funRank f).1.get i) (ws i) (zs i)) ∧
            termSetOfSort C (L.funRank f).2 (MSTerm.func f (fun i => (zs i).1)) then
        some ⟨MSTerm.func f (fun i => (h2.choose i).1), h2.choose_spec.2⟩
      -- Case 3: no representative — the junk element `none`.
      else
        none
  else
    none

/-- Lemma 10.6.2 (companion): The many-sorted `Σ`-algebra `C` built on the
`S(C)`-indexed family `TERM(C)`: carrier `s := Option (TERM(C)_s)`
(`Option`-padded so EVERY sort carrier is nonempty, FIX for issue
f53e69a2); `interpConst s c :=` the constant term itself when it lies in
`TERM(C)_s`, else the junk `none`; `interpFunc f ys := funOpC C f ys` (the
three-case operation). The term algebra over `TERM(C)`. -/
@[blueprint "chap10__lemma_10_6_2"]
noncomputable def termAlgebra {L : MSLanguage} (C : MSFormula L) :
    MSStructure L where
  carrier := fun s => Option (TermCarrier C s)
  carrierNonempty := fun _ => ⟨none⟩
  interpFunc := fun f ys => funOpC C f ys
  interpConst := fun s c =>
    letI := Classical.propDecidable (termSetOfSort C s (MSTerm.const s c))
    if h : termSetOfSort C s (MSTerm.const s c) then
      some ⟨MSTerm.const s c, h⟩
    else none
  interpPred := fun _ _ => BoolVal.F

/-- Lemma 10.6.2 (companion): Case 1 (direct membership):
`f_C(some y_1,…,some y_k) = some (f y_1…y_k)` when `f y_1…y_k ∈ TERM(C)_s`. -/
@[blueprint "chap10__lemma_10_6_2"]
theorem funOpC_case1 {L : MSLanguage} (C : MSFormula L) (f : L.funSymbols)
    (ys : (i : Fin (L.funRank f).1.length) →
      TermCarrier C ((L.funRank f).1.get i))
    (hmem : termSetOfSort C (L.funRank f).2 (MSTerm.func f (fun i => (ys i).1))) :
    funOpC C f (fun i => some (ys i)) = some ⟨MSTerm.func f (fun i => (ys i).1), hmem⟩ 

/-- Lemma 10.6.2 (companion): Case 2 (congruent representative): when
`f y_1…y_k ∉ TERM(C)_s` but there is a family `z_i` with `y_i R* z_i` and
`f z_1…z_k ∈ TERM(C)_s`, then `f_C(some y_1,…,some y_k) = some (f z'_1…z'_k)`
for some representative `z'` that is `R*`-congruent to `y` with
`f z'_1…z'_k ∈ TERM(C)_s`; in particular the result is `R*`-EQUIVALENT to
`f z_1…z_k` (FIX for issue da1bcbf1: only equality-mod-`R*` holds, since
`funOpC` uses `Classical.choose`). -/
@[blueprint "chap10__lemma_10_6_2"]
theorem funOpC_case2 {L : MSLanguage} (C : MSFormula L) (f : L.funSymbols)
    (ys zs : (i : Fin (L.funRank f).1.length) →
      TermCarrier C ((L.funRank f).1.get i))
    (hnot : ¬ termSetOfSort C (L.funRank f).2 (MSTerm.func f (fun i => (ys i).1)))
    (hcong : ∀ i, closureRel C ((L.funRank f).1.get i) (ys i) (zs i))
    (hmem : termSetOfSort C (L.funRank f).2 (MSTerm.func f (fun i => (zs i).1))) :
    ∃ (w : TermCarrier C (L.funRank f).2),
      funOpC C f (fun i => some (ys i)) = some w ∧
      closureRel C (L.funRank f).2 w
        ⟨MSTerm.func f (fun i => (zs i).1), hmem⟩ 

/-- Lemma 10.6.2 (companion): Case 3 (junk value): when no `R*`-congruent
representative `f z_1…z_k ∈ TERM(C)_s` of `f y_1…y_k` exists (in
particular `f y_1…y_k ∉ TERM(C)_s` either, as `y` is congruent to itself),
`f_C(some y_1,…,some y_k) = none` — the padding junk element (FIX for issue
f53e69a2: on sorts with empty/insufficient `TERM(C)_s` the operation
cannot land in `TERM(C)_s`, so the `Option` carrier supplies `none`). -/
@[blueprint "chap10__lemma_10_6_2"]
theorem funOpC_case3 {L : MSLanguage} (C : MSFormula L) (f : L.funSymbols)
    (ys : (i : Fin (L.funRank f).1.length) →
      TermCarrier C ((L.funRank f).1.get i))
    (_hnot1 : ¬ termSetOfSort C (L.funRank f).2 (MSTerm.func f (fun i => (ys i).1)))
    (hnot2 : ¬ ∃ (zs : (i : Fin (L.funRank f).1.length) →
        TermCarrier C ((L.funRank f).1.get i)),
      (∀ i, closureRel C ((L.funRank f).1.get i) (ys i) (zs i)) ∧
        termSetOfSort C (L.funRank f).2 (MSTerm.func f (fun i => (zs i).1))) :
    funOpC C f (fun i => some (ys i)) = none 

-- ===================================================================
-- Lemma 10.6.2: the quotient model M and the meaning t_M[v] = [t]
-- ===================================================================

/-- Lemma 10.6.2 (companion): `R*`-equivalence of two `Option`-padded
carrier values at sort `s`: either both are the junk `none`, or both are
`some` of `R*`-related carrier elements. The relation transported to the
`Option`-padded carrier used by `termAlgebra`/`quotientModel`. -/
@[blueprint "chap10__lemma_10_6_2"]
def closureRelOpt {L : MSLanguage} (C : MSFormula L) (s : L.SortType)
    (a b : Option (TermCarrier C s)) : Prop :=
  (a = none ∧ b = none) ∨
    (∃ t u, a = some t ∧ b = some u ∧ closureRel C s t u)

/-- Lemma 10.6.2 (companion): `R*` is an ALGEBRA-congruence on the term
algebra `C`: componentwise-`R*`-congruent arguments produce
`R*`-equivalent `f_C` values. Because `TERM(C)` is not closed under
function application, the value may be the junk `none`; the congruence is
therefore phrased on the `Option`-padded carrier via `closureRelOpt`. The
three operation cases all reduce to function congruence (2b) of `R*`
(`funcNode_closureRel`): if a `R*`-congruent representative exists for `ys`
it exists for `zs` (and conversely), and any two such representatives are
`R*`-related; if none exists for either, both values are `none`. -/
@[blueprint "chap10__lemma_10_6_2"]
theorem closure_isAlgebraCongruence {L : MSLanguage} (C : MSFormula L)
    (f : L.funSymbols)
    (ys zs : (i : Fin (L.funRank f).1.length) →
      TermCarrier C ((L.funRank f).1.get i))
    (hcong : ∀ i, closureRel C ((L.funRank f).1.get i) (ys i) (zs i)) :
    closureRelOpt C (L.funRank f).2
      (funOpC C f (fun i => some (ys i)))
      (funOpC C f (fun i => some (zs i))) 

/-- Lemma 10.6.2 (companion): The setoid on the sort-`s` carrier
`TERM(C)_s` induced by the congruence closure `R*`: two terms are
equivalent when their nodes are `R*`-related. The quotient by this setoid
is the carrier of the quotient model. -/
@[blueprint "chap10__lemma_10_6_2"]
noncomputable def closureSetoid {L : MSLanguage} (C : MSFormula L)
    (s : L.SortType) : Setoid (TermCarrier C s) where
  r := fun t u =>
    ∃ (p q : (graphOfConjunction C).Node),
      p.1 = ⟨s, t.1⟩ ∧ q.1 = ⟨s, u.1⟩ ∧
        msCongruenceClosure (graphOfConjunction C)
          (positiveEquationRelation C) (positiveEquationRelation_sortSupported C) p q
  iseqv := by
    -- `R*` is an equivalence relation (from `msCongruenceClosure_isCongruence`).
    obtain ⟨hrefl, hsymm, htrans⟩ := positiveClosure_equivalence C
    refine ⟨?_, ?_, ?_⟩
    · -- Reflexivity: the node `⟨⟨s, t.1⟩, t.2⟩` exists in `TERM(C)`.
      intro t
      exact ⟨⟨⟨s, t.1⟩, t.2⟩, ⟨⟨s, t.1⟩, t.2⟩, rfl, rfl, hrefl _⟩
    · -- Symmetry.
      intro t u ⟨p, q, hp, hq, hpq⟩
      exact ⟨q, p, hq, hp, hsymm hpq⟩
    · -- Transitivity: the middle nodes coincide (same `.1`).
      intro t u w ⟨p, q, hp, hq, hpq⟩ ⟨p', q', hp', hq', hp'q'⟩
      have hmid : q = p' := Subtype.ext (hq.trans hp'.symm)
      subst hmid
      exact ⟨p, q', hp, hq', htrans hpq hp'q'⟩

/-- Lemma 10.6.2 (companion): The setoid relation of `closureSetoid`
coincides with `closureRel` on carrier elements — the `∃ p q` packaging
reduces to the closure between the canonical nodes `carrierNode C s t`,
`carrierNode C s u`. -/
@[blueprint "chap10__lemma_10_6_2"]
theorem closureSetoid_r_iff {L : MSLanguage} (C : MSFormula L) (s : L.SortType)
    (t u : TermCarrier C s) :
    (closureSetoid C s).r t u ↔ closureRel C s t u 

/-- Lemma 10.6.2 (companion): A representative chooser for the
`closureSetoid` quotient: every class has an underlying carrier element. -/
@[blueprint "chap10__lemma_10_6_2"]
noncomputable def chooseRep {L : MSLanguage} (C : MSFormula L) (s : L.SortType)
    (q : Quotient (closureSetoid C s)) : TermCarrier C s :=
  Classical.choose (Quotient.exists_rep q)

/-- Lemma 10.6.2 (companion): `chooseRep` returns a representative of its
class: `[chooseRep q] = q`. -/
@[blueprint "chap10__lemma_10_6_2"]
theorem chooseRep_spec {L : MSLanguage} (C : MSFormula L) (s : L.SortType)
    (q : Quotient (closureSetoid C s)) :
    Quotient.mk (closureSetoid C s) (chooseRep C s q) = q 

/-- Lemma 10.6.2 (companion): The `Option`-padded quotient interpretation
of `f`: from `Option (Quotient …)` arguments, choose representatives, apply
`funOpC`, and `Option`-map back into classes. Well-defined on classes by
`closure_isAlgebraCongruence`. -/
@[blueprint "chap10__lemma_10_6_2"]
noncomputable def quotientFunOp {L : MSLanguage} (C : MSFormula L)
    (f : L.funSymbols)
    (qs : (i : Fin (L.funRank f).1.length) →
      Option (Quotient (closureSetoid C ((L.funRank f).1.get i)))) :
    Option (Quotient (closureSetoid C (L.funRank f).2)) :=
  letI := Classical.propDecidable (∀ i, (qs i).isSome)
  if hall : ∀ i, (qs i).isSome then
    (funOpC C f (fun i => some (chooseRep C ((L.funRank f).1.get i)
      ((qs i).get (hall i))))).map (Quotient.mk (closureSetoid C (L.funRank f).2))
  else none

/-- Lemma 10.6.2 (companion): The `L`-structure `M` obtained as the
quotient of the term algebra `C` (`termAlgebra C`) by the congruence
`R* = msCongruenceClosure (graphOfConjunction C) (positiveEquationRelation
C)`: carrier `s :=` the `Option`-padded quotient of `termSetOfSort C s` by
the `R*`-induced setoid (`Option`-padded so EVERY sort carrier is nonempty,
FIX for issue f53e69a2); `interpFunc f := quotientFunOp` and `interpConst`
the induced operations on classes (junk `none` off `S(C)`). The candidate
model of `C` (quotient as in Subsection 2.5.8). -/
@[blueprint "chap10__lemma_10_6_2"]
noncomputable def quotientModel {L : MSLanguage} (C : MSFormula L) :
    MSStructure L where
  carrier := fun s => Option (Quotient (closureSetoid C s))
  carrierNonempty := fun _ => ⟨none⟩
  interpFunc := fun f qs => quotientFunOp C f qs
  interpConst := fun s c =>
    letI := Classical.propDecidable (termSetOfSort C s (MSTerm.const s c))
    if h : termSetOfSort C s (MSTerm.const s c) then
      some (Quotient.mk (closureSetoid C s) ⟨MSTerm.const s c, h⟩)
    else none
  interpPred := fun _ _ => BoolVal.F

/-- Lemma 10.6.2 (companion): The assignment `v` with `v(x) = [x]`, the
`R*`-congruence class of the variable `x` when `x ∈ TERM(C)`, and the junk
`none` otherwise — used to interpret variables in the quotient model `M`. -/
@[blueprint "chap10__lemma_10_6_2"]
noncomputable def quotientAssignment {L : MSLanguage} (C : MSFormula L) :
    MSAssignment (quotientModel C) :=
  fun s i =>
    letI := Classical.propDecidable (termSetOfSort C s (MSTerm.var s i))
    if h : termSetOfSort C s (MSTerm.var s i) then
      some (Quotient.mk (closureSetoid C s) ⟨MSTerm.var s i, h⟩)
    else none

/-- Lemma 10.6.2 (companion): The inductive claim that for every term
`t ∈ TERM(C)`, its meaning `t_M[v]` in the quotient model equals its
`R*`-congruence class `[t]` (textbook: "easily shown by induction and
left as an exercise"). Proof body `sorry`. -/
@[blueprint "chap10__lemma_10_6_2"]
theorem termMeaning_eq_class {L : MSLanguage} (C : MSFormula L)
    (s : L.SortType) (t : TermCarrier C s) :
    msTermEval (quotientModel C) (quotientAssignment C) (t.1 : MSTerm L s) =
      some (Quotient.mk (closureSetoid C s) t) 

/-- Lemma 10.6.2 (companion): If every literal conjunct of a
conjunction-of-literals `D` evaluates to `T` under `M, v`, then `D` itself
evaluates to `T`. The converse direction of `msConjunctContains_eval`,
proved by induction on the conjunction tree of `D`. -/
@[blueprint "chap10__lemma_10_6_2"]
theorem conjunctionOfLiterals_eval_T {L : MSLanguage} (M : MSStructure L)
    (v : MSAssignment M) :
    ∀ D : MSFormula L, msIsConjunctionOfLiterals D →
      (∀ X, msConjunctContains D X → MSFormula.isLiteral X →
        msFormulaEval M X v = BoolVal.T) →
      msFormulaEval M D v = BoolVal.T 

/-- Lemma 10.6.2 (companion): The two terms of a positive equation conjunct
of `C` lie in `TERM(C)`. -/
@[blueprint "chap10__lemma_10_6_2"]
theorem posEq_mem {L : MSLanguage} (C : MSFormula L)
    (hL : L.hasEquality = true) (s : L.SortType) (t u : MSTerm L s)
    (hcon : msConjunctContains C (MSFormula.eq_ hL s t u)) :
    termSetOfConjunction C ⟨s, t⟩ ∧ termSetOfConjunction C ⟨s, u⟩ 

/-- Lemma 10.6.2 (companion): The two terms of a negated equation conjunct
of `C` lie in `TERM(C)`. -/
@[blueprint "chap10__lemma_10_6_2"]
theorem negEq_mem {L : MSLanguage} (C : MSFormula L)
    (hL : L.hasEquality = true) (s : L.SortType) (r vt : MSTerm L s)
    (hcon : msConjunctContains C (MSFormula.neg (MSFormula.eq_ hL s r vt))) :
    termSetOfConjunction C ⟨s, r⟩ ∧ termSetOfConjunction C ⟨s, vt⟩ 

/-- Lemma 10.6.2 (companion, backward direction): When NO collision
occurs, the quotient model `M = quotientModel C` with assignment
`v = quotientAssignment C` satisfies `C` — every positive equation
`t_i =̇ u_i` holds because `[t_i] = [u_i]` (they are `R*`-congruent via
`E`), and every negated equation `¬ r_j =̇ v_j` holds because
`[r_j] ≠ [v_j]` (no collision); uses `termMeaning_eq_class`. Hence `C` is
satisfiable. -/
@[blueprint "chap10__lemma_10_6_2"]
theorem noCollision_sat_direction {L : MSLanguage} (C : MSFormula L)
    (hC : msIsConjunctionOfEquations C)
    (hno : ¬ ∃ (hL : L.hasEquality = true) (s : L.SortType) (r v : MSTerm L s)
      (p q : (graphOfConjunction C).Node),
      msConjunctContains C (MSFormula.neg (MSFormula.eq_ hL s r v)) ∧
        p.1 = ⟨s, r⟩ ∧ q.1 = ⟨s, v⟩ ∧
        msCongruenceClosure (graphOfConjunction C)
          (positiveEquationRelation C) (positiveEquationRelation_sortSupported C) p q) :
    msSatisfiable C 

-- ===================================================================
-- Lemma 10.6.2: msUnsatisfiable_iff_collision
-- ===================================================================

/-- Lemma 10.6.2 (Unsatisfiability criterion): Given a conjunction
`C = t_1 =̇_{s_1} u_1 ∧ … ∧ ¬ r_n =̇_{s'_n} v_n` of equations and negated
equations, with `G(C) = graphOfConjunction C`, `E = positiveEquationRelation
C`, and `R* = msCongruenceClosure G(C) E` the congruence closure of `E`
on `G(C)`, then `C` is unsatisfiable IFF for SOME negated equation
`¬ r_j =̇_{s'_j} v_j` of `C` the terms `r_j` and `v_j` fall in the SAME
congruence class of `R*` (`r_j R* v_j`).

A genuine biconditional: the forward direction is the soundness argument
(`collision_unsat_direction`: a collision yields a contradiction in any
model) and the backward direction is the completeness/model-construction
argument (`noCollision_sat_direction`: no collision ⇒ the quotient term
model satisfies `C`). The model construction is captured by the required
companions above. Requires `C` to be a conjunction of equations
(`msIsConjunctionOfEquations`, the §10.6.1 with-equality normal form).
Proof body `sorry` at this stage. -/
@[blueprint "chap10__lemma_10_6_2" (main := true)]
theorem msUnsatisfiable_iff_collision {L : MSLanguage} (C : MSFormula L)
    (hC : msIsConjunctionOfEquations C) :
    msUnsatisfiable C ↔
      ∃ (hL : L.hasEquality = true) (s : L.SortType) (r v : MSTerm L s)
        (p q : (graphOfConjunction C).Node),
        msConjunctContains C (MSFormula.neg (MSFormula.eq_ hL s r v)) ∧
          p.1 = ⟨s, r⟩ ∧ q.1 = ⟨s, v⟩ ∧
          msCongruenceClosure (graphOfConjunction C)
            (positiveEquationRelation C) (positiveEquationRelation_sortSupported C) p q

-- ===================================================================
-- Example 10.6.2: deciding C = (f(a,b) =̇ c) ∧ ¬(g(f(a,b),a) =̇ g(c,a))
-- ===================================================================

/-- Example 10.6.2 (companion): `TERM(C)_i` for the example conjunction
`C = (f(a,b) =̇_s c) ∧ ¬(g(f(a,b),a) =̇_s g(c,a))` — the sort-`i`
subterm set, which equals `{a}` (only the integer-sort term `a`
occurs). Reuses `exampleConjunction` from the sibling core module. -/
@[blueprint "chap10__example_10_6_2"]
def exampleTermSetI : Set (MSTerm exampleLanguage ExampleSort.i) :=
  termSetOfSort exampleConjunction ExampleSort.i

/-- Example 10.6.2 (companion): `TERM(C)_s` for the example conjunction —
the sort-`s` subterm set `{b, c, f(a,b), g(c,a), g(f(a,b),a)}`. -/
@[blueprint "chap10__example_10_6_2"]
def exampleTermSetS : Set (MSTerm exampleLanguage ExampleSort.s) :=
  termSetOfSort exampleConjunction ExampleSort.s

/-- Example 10.6.2 (companion): The seed relation `E = {(f(a,b), c)}`
(the single positive equation), fed to `msCongruenceClosure` on `G(C)` —
the example instance of `positiveEquationRelation`. -/
@[blueprint "chap10__example_10_6_2"]
def exampleE :
    (graphOfConjunction exampleConjunction).Node →
      (graphOfConjunction exampleConjunction).Node → Prop :=
  positiveEquationRelation exampleConjunction

/-- Lemma 10.6.2 (companion): Two graph nodes with equal underlying sorted
terms are equal (the membership proof is a `Prop`, so irrelevant). -/
@[blueprint "chap10__lemma_10_6_2"]
theorem node_eq_of_val_eq {L : MSLanguage} {C : MSFormula L}
    {p q : (graphOfConjunction C).Node} (h : p.1 = q.1) : p = q 

/-- The six shared nodes of the graph in Example 10.6.1. -/
@[blueprint "chap10__example_10_6_1"]
inductive ExampleNode where
  | a | b | c | fab | gca | gfaba
  deriving DecidableEq

/-- The sorted term named by each node. -/
@[blueprint "chap10__example_10_6_1"]
def exampleNodeTerm : ExampleNode → MSTermSig exampleLanguage
  | .a => ⟨ExampleSort.i, exampleTerm_a⟩
  | .b => ⟨ExampleSort.s, exampleTerm_b⟩
  | .c => ⟨ExampleSort.s, exampleTerm_c⟩
  | .fab => ⟨ExampleSort.s, exampleTerm_fab⟩
  | .gca => ⟨ExampleSort.s, exampleTerm_gca⟩
  | .gfaba => ⟨ExampleSort.s, exampleTerm_gfaba⟩

/-- The labels of the six nodes use exactly the five printed symbols. -/
@[blueprint "chap10__example_10_6_1"]
def exampleNodeLabel : ExampleNode → ExampleSym
  | .a => .a
  | .b => .b
  | .c => .c
  | .fab => .f
  | .gca | .gfaba => .g

/-- Ordered ports, with repeated occurrences sharing the same node. -/
@[blueprint "chap10__example_10_6_1"]
def exampleNodePorts : ExampleNode → List ExampleNode
  | .a | .b | .c => []
  | .fab => [.a, .b]
  | .gca => [.c, .a]
  | .gfaba => [.fab, .a]

/-- Every displayed node belongs to TERM(C). -/
@[attach_debt, blueprint "chap10__example_10_6_1"]
theorem exampleNode_mem (n : ExampleNode) :
    termSetOfConjunction exampleConjunction (exampleNodeTerm n)

/-- The displayed node as an actual vertex of G(C). -/
@[blueprint "chap10__example_10_6_1"]
def exampleGraphNode (n : ExampleNode) : (graphOfConjunction exampleConjunction).Node :=
  ⟨exampleNodeTerm n, exampleNode_mem n⟩

/-- Exactly six distinct vertices: each vertex has one displayed name. -/
@[attach_debt, blueprint "chap10__example_10_6_1"]
theorem exampleGraphNodes_exact (p : (graphOfConjunction exampleConjunction).Node) :
    ∃ n, exampleGraphNode n = p ∧ ∀ m, exampleGraphNode m = p → m = n

/-- The two fibers are exactly the printed singleton and five-element set. -/
@[attach_debt, blueprint "chap10__example_10_6_1"]
theorem exampleTermFibers_exact :
    (∀ t, exampleTermSetI t ↔ t = exampleTerm_a) ∧
    (∀ t, exampleTermSetS t ↔ t = exampleTerm_b ∨ t = exampleTerm_c ∨
      t = exampleTerm_fab ∨ t = exampleTerm_gca ∨ t = exampleTerm_gfaba)

/-- The five symbols, regarded as occurring symbols of G(C). -/
@[blueprint "chap10__example_10_6_1"]
def exampleGraphSymbol : ExampleSym → (graphOfConjunction exampleConjunction).Sigma.symbols
  | .a => .const ExampleSort.i .a (exampleNode_mem .a)
  | .b => .const ExampleSort.s .b (exampleNode_mem .b)
  | .c => .const ExampleSort.s .c (exampleNode_mem .c)
  | .f => .func .f ⟨exampleFArgs exampleTerm_a exampleTerm_b, exampleNode_mem .fab⟩
  | .g => .func .g ⟨exampleGArgs exampleTerm_c exampleTerm_a, exampleNode_mem .gca⟩

/-- Exactly the five occurring symbols; in particular no variable symbols occur. -/
@[attach_debt, blueprint "chap10__example_10_6_1"]
theorem exampleGraphSymbols_exact
    (σ : (graphOfConjunction exampleConjunction).Sigma.symbols) :
    ∃ e, exampleGraphSymbol e = σ ∧ ∀ d, exampleGraphSymbol d = σ → d = e

/-- The occurring ranks recover the printed two-sort alphabet. -/
@[blueprint "chap10__example_10_6_1"]
theorem exampleGraphRanks (e : ExampleSym) :
    let r := (graphOfConjunction exampleConjunction).Sigma.rank (exampleGraphSymbol e)
    (r.1.map Subtype.val, r.2.val) = exampleAlphabet.rank e

/-- The actual graph labels agree with the six-node diagram. -/
@[blueprint "chap10__example_10_6_1"]
theorem exampleGraphLabels (n : ExampleNode) :
    (graphOfConjunction exampleConjunction).Lambda (exampleGraphNode n) =
      exampleGraphSymbol (exampleNodeLabel n)

/-- The entire ordered successor list agrees with the diagram at every node. -/
@[blueprint "chap10__example_10_6_1"]
theorem exampleGraphPorts (n : ExampleNode) :
    List.ofFn ((graphOfConjunction exampleConjunction).delta (exampleGraphNode n)) =
      (exampleNodePorts n).map exampleGraphNode

/-- The only seed pair is the oriented positive equation (f(a,b),c). -/
@[attach_debt, blueprint "chap10__example_10_6_1"]
theorem exampleE_exact (p q : (graphOfConjunction exampleConjunction).Node) :
    exampleE p q ↔ p = exampleGraphNode .fab ∧ q = exampleGraphNode .c

/-- The four blocks, including both singleton classes. -/
@[blueprint "chap10__example_10_6_2"]
def exampleClass : ExampleNode → Fin 4
  | .a => 0
  | .b => 1
  | .fab | .c => 2
  | .gfaba | .gca => 3

/-- The exhaustive partition as finite data. -/
@[blueprint "chap10__example_10_6_2"]
def examplePartition : List (List ExampleNode) :=
  [[.a], [.b], [.fab, .c], [.gfaba, .gca]]

/-- Each node appears in exactly its displayed block, and block numbers separate classes. -/
@[blueprint "chap10__example_10_6_2"]
theorem examplePartition_exact (n : ExampleNode) (k : Fin 4) :
    n ∈ examplePartition[k.val]'(by exact k.isLt) ↔ exampleClass n = k

/-- The closure on all vertices is exactly the four displayed blocks. -/
@[attach_debt, blueprint "chap10__example_10_6_2"]
theorem exampleClosureClasses (p q : (graphOfConjunction exampleConjunction).Node) :
    msCongruenceClosure (graphOfConjunction exampleConjunction) exampleE
      (positiveEquationRelation_sortSupported exampleConjunction) p q ↔
    ∃ m n : ExampleNode, p = exampleGraphNode m ∧ q = exampleGraphNode n ∧
      exampleClass m = exampleClass n

/-- The two nontrivial identifications in the displayed partition. -/
@[blueprint "chap10__example_10_6_2"]
theorem exampleClosurePairs
    (pfab pc pgfaba pgca : (graphOfConjunction exampleConjunction).Node)
    (hpfab : pfab.1 = ⟨ExampleSort.s, exampleTerm_fab⟩)
    (hpc : pc.1 = ⟨ExampleSort.s, exampleTerm_c⟩)
    (hpgfaba : pgfaba.1 = ⟨ExampleSort.s, exampleTerm_gfaba⟩)
    (hpgca : pgca.1 = ⟨ExampleSort.s, exampleTerm_gca⟩) :
    msCongruenceClosure (graphOfConjunction exampleConjunction) exampleE (positiveEquationRelation_sortSupported exampleConjunction)
        pfab pc ∧
      msCongruenceClosure (graphOfConjunction exampleConjunction) exampleE (positiveEquationRelation_sortSupported exampleConjunction)
        pgfaba pgca 

/-- The five sort-s elements of the printed candidate algebra, before quotienting. -/
@[blueprint "chap10__example_10_6_2"]
inductive ExampleValueS where
  | b | c | fab | gca | gfaba
  deriving DecidableEq

/-- The candidate has one element of sort i and five of sort s. -/
@[blueprint "chap10__example_10_6_2"]
def exampleCarrier : ExampleSort → Type
  | .i => ExampleConstI
  | .s => ExampleValueS

/-- Carrier elements name the same six graph nodes. -/
@[blueprint "chap10__example_10_6_2"]
def exampleCarrierNode : (s : ExampleSort) → exampleCarrier s → ExampleNode
  | .i, .a => .a
  | .s, .b => .b
  | .s, .c => .c
  | .s, .fab => .fab
  | .s, .gca => .gca
  | .s, .gfaba => .gfaba

/-- The printed f-table: f(a,b) is its node; the other four results are b. -/
@[blueprint "chap10__example_10_6_2"]
def exampleCandidateF (_ : ExampleConstI) : ExampleValueS → ExampleValueS
  | .b => .fab
  | .c | .fab | .gca | .gfaba => .b

/-- The printed g-table: two occurring applications and three default values b. -/
@[blueprint "chap10__example_10_6_2"]
def exampleCandidateG : ExampleValueS → ExampleConstI → ExampleValueS
  | .c, .a => .gca
  | .fab, .a => .gfaba
  | .b, .a | .gca, .a | .gfaba, .a => .b

/-- The six-node pre-quotient candidate algebra of Example 10.6.2. -/
@[blueprint "chap10__example_10_6_2"]
def exampleCandidateAlgebra : MSStructure exampleLanguage where
  carrier := exampleCarrier
  carrierNonempty := fun s => by cases s; exact ⟨.a⟩; exact ⟨.b⟩
  interpConst := fun s => match s with
    | .i => fun _ => .a
    | .s => fun c => match c with | .b => .b | .c => .c
  interpFunc := fun f => match f with
    | .f => fun xs => exampleCandidateF (xs ⟨0, by decide⟩) (xs ⟨1, by decide⟩)
    | .g => fun xs => exampleCandidateG (xs ⟨0, by decide⟩) (xs ⟨1, by decide⟩)
  interpPred := fun p => nomatch p

/-- Well-sorted arguments for f in the candidate algebra. -/
@[blueprint "chap10__example_10_6_2"]
def exampleCandidateFArgs (x : ExampleConstI) (y : ExampleValueS) :
    (j : Fin (exampleLanguage.funRank ExampleFunc.f).1.length) →
      exampleCandidateAlgebra.carrier ((exampleLanguage.funRank ExampleFunc.f).1.get j)
  | ⟨0, _⟩ => x
  | ⟨1, _⟩ => y

/-- Well-sorted arguments for g in the candidate algebra. -/
@[blueprint "chap10__example_10_6_2"]
def exampleCandidateGArgs (x : ExampleValueS) (y : ExampleConstI) :
    (j : Fin (exampleLanguage.funRank ExampleFunc.g).1.length) →
      exampleCandidateAlgebra.carrier ((exampleLanguage.funRank ExampleFunc.g).1.get j)
  | ⟨0, _⟩ => x
  | ⟨1, _⟩ => y

/-- All ten entries of the printed table, checked against the structure operations. -/
@[blueprint "chap10__example_10_6_2"]
theorem exampleCandidateTable :
    exampleCandidateAlgebra.interpFunc .f (exampleCandidateFArgs .a .b) = .fab ∧
    exampleCandidateAlgebra.interpFunc .g (exampleCandidateGArgs .b .a) = .b ∧
    exampleCandidateAlgebra.interpFunc .g (exampleCandidateGArgs .c .a) = .gca ∧
    exampleCandidateAlgebra.interpFunc .f (exampleCandidateFArgs .a .c) = .b ∧
    exampleCandidateAlgebra.interpFunc .g (exampleCandidateGArgs .fab .a) = .gfaba ∧
    exampleCandidateAlgebra.interpFunc .f (exampleCandidateFArgs .a .fab) = .b ∧
    exampleCandidateAlgebra.interpFunc .f (exampleCandidateFArgs .a .gca) = .b ∧
    exampleCandidateAlgebra.interpFunc .g (exampleCandidateGArgs .gca .a) = .b ∧
    exampleCandidateAlgebra.interpFunc .f (exampleCandidateFArgs .a .gfaba) = .b ∧
    exampleCandidateAlgebra.interpFunc .g (exampleCandidateGArgs .gfaba .a) = .b

/-- Example 10.6.2 (companion): The negated equation `¬(g(f(a,b),a) =̇_s
g(c,a))` is the right conjunct of the example conjunction. -/
@[blueprint "chap10__example_10_6_2"]
theorem exampleConjunction_contains_neg :
    msConjunctContains exampleConjunction
      (MSFormula.neg (MSFormula.eq_ (L := exampleLanguage) rfl ExampleSort.s
        exampleTerm_gfaba exampleTerm_gca)) 

/-- Example 10.6.2 (companion): `g(f(a,b),a)` and `g(c,a)` both lie in
`TERM(C)`, being the two terms of the negated equation of `C`. -/
@[blueprint "chap10__example_10_6_2"]
theorem exampleTerm_gfaba_mem :
    termSetOfConjunction exampleConjunction ⟨ExampleSort.s, exampleTerm_gfaba⟩ 

@[blueprint "chap10__example_10_6_2"]
theorem exampleTerm_gca_mem :
    termSetOfConjunction exampleConjunction ⟨ExampleSort.s, exampleTerm_gca⟩ 

/-- Example 10.6.2 (companion): `f(a,b)` and `c` both lie in `TERM(C)`,
being subterms of terms occurring in the conjunction. -/
@[blueprint "chap10__example_10_6_2"]
theorem exampleTerm_fab_mem :
    termSetOfConjunction exampleConjunction ⟨ExampleSort.s, exampleTerm_fab⟩ 

@[blueprint "chap10__example_10_6_2"]
theorem exampleTerm_c_mem :
    termSetOfConjunction exampleConjunction ⟨ExampleSort.s, exampleTerm_c⟩ 

/-- Example 10.6.2: The witness that `g(f(a,b),a)` and `g(c,a)` are
`R*`-congruent (the same class) — the collision of Lemma 10.6.2 for the
example. Packaged as the existence of the two `TERM(C)` nodes for
`g(f(a,b),a)` and `g(c,a)` together with the closure proof. -/
@[blueprint "chap10__example_10_6_2"]
theorem exampleCollision :
    ∃ (hL : exampleLanguage.hasEquality = true) (r v : MSTerm exampleLanguage ExampleSort.s)
      (p q : (graphOfConjunction exampleConjunction).Node),
      msConjunctContains exampleConjunction
        (MSFormula.neg (MSFormula.eq_ hL ExampleSort.s r v)) ∧
        p.1 = ⟨ExampleSort.s, r⟩ ∧ q.1 = ⟨ExampleSort.s, v⟩ ∧
        msCongruenceClosure (graphOfConjunction exampleConjunction)
          (positiveEquationRelation exampleConjunction) (positiveEquationRelation_sortSupported exampleConjunction) p q

/-- Example 10.6.2: The conclusion that the example conjunction `C` is
unsatisfiable, obtained from `msUnsatisfiable_iff_collision` (Lemma
10.6.2) applied to `exampleCollision`. A genuine proposition
(`msUnsatisfiable exampleConjunction`), NOT `True := trivial`. Proof body
`sorry` (it depends on the `msIsConjunctionOfEquations` hypothesis of
Lemma 10.6.2 for the example conjunction). -/
@[blueprint "chap10__example_10_6_2" (main := true)]
theorem exampleDecision : msUnsatisfiable exampleConjunction 

end LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
end

