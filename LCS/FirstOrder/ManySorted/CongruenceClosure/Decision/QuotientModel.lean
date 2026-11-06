import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Equality
import LCS.FirstOrder.ManySorted.CongruenceClosure
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

end LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
end
