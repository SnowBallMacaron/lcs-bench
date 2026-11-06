import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Equality
import LCS.FirstOrder.ManySorted.CongruenceClosure
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
import LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.Encoding
import LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.CongruenceModel
import Attach
import LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.Decision.ProofsStamp

section
namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates
open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.FirstOrder.ManySorted.Equality
open LCS.FirstOrder.ManySorted.CongruenceClosure
open LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
open LCS.Propositional.Semantics

/-- Lemma 10.6.4 (helper): recast a `decodeModel`-argument of `f` to the
bool-extended `Sum.inl f` argument family — the inverse of `inlArgRecast`.
The `i`-th argument of `Sum.inl f` lies in `M'.carrier (((L.funRank
f).1.map some).get i)`, which after `List.getElem_map` is `M'.carrier
(some ((L.funRank f).1.get j))` = the decode carrier at `(L.funRank
f).1.get j`. -/
@[blueprint "chap10__lemma_10_6_4"]
noncomputable def decodeInlArgRecast (L : MSLanguage)
    (M' : MSStructure (boolExtendedLanguage L)) (f : L.funSymbols)
    (args : (j : Fin (L.funRank f).1.length) → M'.carrier (some ((L.funRank f).1.get j)))
    (i : Fin (((boolExtendedLanguage L).funRank (Sum.inl f)).1).length) :
    M'.carrier (((boolExtendedLanguage L).funRank (Sum.inl f)).1.get i) :=
  have hj : i.val < (L.funRank f).1.length := by
    have := i.isLt
    simpa [boolExtendedLanguage, boolExtendedFunRank, List.length_map] using this
  have hsort :
      (((boolExtendedLanguage L).funRank (Sum.inl f)).1.get i) =
        some ((L.funRank f).1.get ⟨i.val, hj⟩) := by
    simp [boolExtendedLanguage, boolExtendedFunRank, List.get_eq_getElem, List.getElem_map]
    all_goals exact List.getElem_map some
  hsort ▸ args ⟨i.val, hj⟩

/-- Lemma 10.6.4 (helper): recast a `decodeModel`-argument of the predicate
`P` to the bool-extended `Sum.inr P` argument family (the predicate
analogue of `decodeInlArgRecast`). -/
@[blueprint "chap10__lemma_10_6_4"]
noncomputable def decodeInrArgRecast (L : MSLanguage)
    (M' : MSStructure (boolExtendedLanguage L)) (P : L.predSymbols)
    (args : (j : Fin (L.predArity P).length) → M'.carrier (some ((L.predArity P).get j)))
    (i : Fin (((L.predArity P).map some)).length) :
    M'.carrier (((L.predArity P).map some).get i) :=
  have hj : i.val < (L.predArity P).length := by
    have := i.isLt
    simpa [boolExtendedLanguage, boolExtendedFunRank, List.length_map] using this
  have hsort :
      (((L.predArity P).map some).get i) =
        some ((L.predArity P).get ⟨i.val, hj⟩) := by
    simp [boolExtendedLanguage, boolExtendedFunRank, List.get_eq_getElem, List.getElem_map]
    all_goals exact List.getElem_map some
  hsort ▸ args ⟨i.val, hj⟩

/-- Lemma 10.6.4 (helper): the DECODED `L`-structure built from a model
`M'` of the bool-extended language `L'`. The sort-`s` carrier is
`M'.carrier (some s)`; a function symbol `f` is interpreted via
`M'`'s `Sum.inl f` (arguments recast by `decodeInlArgRecast`); a constant
`c : L.constSymbols s = (boolExtendedLanguage L).constSymbols (some s)` by
`M'.interpConst (some s) c`; and a predicate `P` is interpreted as `T` iff
the encoded value of `P` equals the value of `⊤`. For nullary `P` this
is a Boolean constant; for positive `P` it is a function application.
The decoded predicate value is always in the fixed two-element `BoolVal`. This is the converse of `encodeModel`. -/
@[blueprint "chap10__lemma_10_6_4"]
noncomputable def decodeModel (L : MSLanguage)
    (M' : MSStructure (boolExtendedLanguage L)) : MSStructure L where
  carrier := fun s => M'.carrier (some s)
  carrierNonempty := fun s => M'.carrierNonempty (some s)
  interpFunc := fun f args =>
    -- `M'.interpFunc (Sum.inl f)` returns `M'.carrier (boolExtendedFunRank
    -- (inl f)).2 = M'.carrier (some (L.funRank f).2)`, which IS the decode
    -- carrier at `(L.funRank f).2`; no cast needed.
    (show M'.carrier (((boolExtendedLanguage L).funRank (Sum.inl f)).2)
        = M'.carrier (some (L.funRank f).2) from rfl) ▸
      (M'.interpFunc (Sum.inl f) (decodeInlArgRecast L M' f args))
  interpConst := fun s c =>
    M'.interpConst (some s)
      (show (boolExtendedLanguage L).constSymbols (some s) from c)
  interpPred := fun P args =>
    let value : M'.carrier (MSBoolSort L) :=
      if h : (L.predArity P).length = 0 then
        M'.interpConst (MSBoolSort L) (Sum.inr ⟨P, List.length_eq_zero_iff.mp h⟩)
      else
        M'.interpFunc (Sum.inr ⟨P, fun hn => h (by rw [hn]; rfl)⟩)
          (decodeInrArgRecast L M' P args)
    letI := Classical.propDecidable (value = M'.interpConst (MSBoolSort L) (Sum.inl ()))
    if value = M'.interpConst (MSBoolSort L) (Sum.inl ()) then BoolVal.T else BoolVal.F

/-- Lemma 10.6.4 (helper): the decoded assignment over `L` induced by an
assignment `v'` of `M'`: a sort-`s` variable `x_i` maps to `v' (some s) i`
(the carriers `(decodeModel L M').carrier s = M'.carrier (some s)`
coincide). -/
@[blueprint "chap10__lemma_10_6_4"]
def decodeAssignment (L : MSLanguage)
    {M' : MSStructure (boolExtendedLanguage L)} (v' : MSAssignment M') :
    MSAssignment (decodeModel L M') :=
  fun s i => (v' (some s) i : (decodeModel L M').carrier s)

/-- Lemma 10.6.4 (DECODE formula transfer, core): `C` evaluated in the
decoded model `decodeModel L M'` under `decodeAssignment L v'` gives the
SAME `BoolVal` as the encoded `C' = msEncodeConjunction L C` evaluated in
`M'` under `v'`. By induction on `C`, mirroring
`msFormulaEval_encodeModel_encode`: equalities use the term transfer
`msTermEval_decodeModel_liftTerm`; predicate atoms use
`decodeModel.interpPred` + `msPredAsFuncTerm_eval_decode` + `msTopConst_eval'`;
connectives recurse; quantifiers transfer via `decodeAssignment_update`. -/
@[attach_debt, blueprint "chap10__lemma_10_6_4"]
theorem msFormulaEval_decodeModel_encode (L : MSLanguage)
    (M' : MSStructure (boolExtendedLanguage L)) :
    ∀ (C : MSFormula L) (v' : MSAssignment M'),
      msFormulaEval (decodeModel L M') C (decodeAssignment L v')
        = msFormulaEval M' (msEncodeConjunction L C) v' 

/-- Lemma 10.6.4: the encoding REFLECTS satisfiability — if the encoded
conjunction `C'` is satisfiable over `L'`, then `C` is satisfiable over `L`
(the converse of `encodePreservesSat`). From a model `(M', v')` of `C'`,
the decoded model `(decodeModel L M', decodeAssignment L v')` satisfies `C`
by the formula transfer `msFormulaEval_decodeModel_encode`. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem encodeReflectsSat (L : MSLanguage) (C : MSFormula L)
    (h : Decision.msSatisfiable (msEncodeConjunction L C)) :
    Decision.msSatisfiable C 

/-- Lemma 10.6.4 (required, backward direction): when NO collision occurs,
the encoded conjunction `C' = msEncodeConjunction L C` is satisfiable over
`L'` (the model construction `noCollision_sat_direction_guarded`, since the
literal conjuncts of `C'` are all (negated) equations) and DECODING that
model back to `L` yields a model of the ORIGINAL `C` (the inverse of
`encodePreservesSat`, via `encodeReflectsSat` / `decodeModel` /
`decodeAssignment` / `msFormulaEval_decodeModel_encode`). The predicate
cases use `decodeModel.interpPred P args = T iff P-as-function value = ⊤`,
matching the encoded equation's truth value.

FIX (faithfulness): the original statement carried NO hypothesis that `C`
is a conjunction of literals and is therefore FALSE as stated.
Counterexample: `C = MSFormula.falsum`. Then `msEncodeConjunction L
falsum = falsum`, whose graph has no negated equations, so `hno` holds
vacuously, yet `msSatisfiable falsum` is FALSE. The textbook (Lemma 10.6.4,
§10.6.5, lines 30-34) EXPLICITLY requires "`C'` is of the form
`t₁≐u₁ ∧ … ∧ ¬rₙ≐vₙ`", i.e. `C` is a conjunction of (negated)
equation/predicate LITERALS. Two faithfulness hypotheses are therefore
ADDED:
* `hC : Decision.msIsConjunctionOfLiterals C` — the textbook
  conjunction-of-literals precondition;
* `hNoBot` — every literal conjunct of `C` is a (negated) equation or
  (negated) predicate ATOM, i.e. NOT bare `falsum`/`neg falsum`. This is
  required because `falsum` is also `MSFormula.isAtomic` (hence a literal in
  the codebase's `isLiteral`), but a `falsum` conjunct makes `C`
  unsatisfiable while `hno` stays vacuous — so excluding it is what makes
  the model construction (and the theorem) TRUE. The textbook's literals
  ("`P t₁…t_k`, `¬P t₁…t_k`, or equations") never include bare `⊥`, so this
  matches the textbook EXACTLY and is NOT a weakening. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem noCollision_sat_direction_pred (L : MSLanguage) (C : MSFormula L)
    (hC : Decision.msIsConjunctionOfLiterals C)
    (hNoBot : ∀ X, Decision.msConjunctContains C X → MSFormula.isLiteral X →
      (X ≠ MSFormula.falsum ∧ X ≠ MSFormula.neg MSFormula.falsum))
    (hno : ¬ ∃ (s : (boolExtendedLanguage L).SortType)
      (r v : MSTerm (boolExtendedLanguage L) s)
      (p q : (graphOfConjunction (L := boolExtendedLanguage L)
        (msEncodeConjunction L C)).Node),
      Decision.msConjunctContains (msEncodeConjunction L C)
        (MSFormula.neg (MSFormula.eq_ (L := boolExtendedLanguage L) rfl s r v)) ∧
        p.1 = ⟨s, r⟩ ∧ q.1 = ⟨s, v⟩ ∧
        msCongruenceClosure
          (graphOfConjunction (L := boolExtendedLanguage L)
            (msEncodeConjunction L C))
          (positiveEquationRelation (L := boolExtendedLanguage L)
            (msEncodeConjunction L C)) (positiveEquationRelation_sortSupported (msEncodeConjunction L C)) p q) :
    Decision.msSatisfiable C 

-- ===================================================================
-- Lemma 10.6.4: msUnsatisfiable_iff_collision_withPredicates
-- ===================================================================

/-- Lemma 10.6.4 (Generalized unsatisfiability criterion WITH predicate
symbols): Given a conjunction of literals `C` over `L` (literals being
(negated) equations and (negated) atomic predicate formulae), let
`C' = msEncodeConjunction L C` be its bool-equation encoding over the
bool-extended language `L' = boolExtendedLanguage L` (every predicate `P`
reinterpreted as a function symbol of rank `(u₁…u_k, bool)`, `⊤` a
constant of sort bool, each atom `P t₁…t_k` replaced by
`(P t₁…t_k ≐_bool ⊤)`, each `¬P t₁…t_k` by `¬(P t₁…t_k ≐_bool ⊤)`). With
`G(C') = graphOfConjunction L' C'`, `E = positiveEquationRelation L' C'`,
and `R* = msCongruenceClosure G(C') E`, then `C` is unsatisfiable IFF for
SOME negated equation `¬ r_j ≐_{s'_j} v_j` of `C'` the terms `r_j` and
`v_j` fall in the SAME `R*`-congruence class (`r_j ↔*_E v_j`).

A GENUINE biconditional (NOT vacuous, NOT a one-way ∨). The forward
direction folds the two textbook proof cases — case (i) non-bool sort
(`collisionCaseNonBool`, identical to Lemma 10.6.2) and case (ii) `r_j`
atomic with `v_j = ⊤` (`collisionCaseAtomTop`, giving `E ⊨ r_j` and a
contradiction with `¬r_j`). The backward direction is the model
construction (`noCollision_sat_direction_pred`: the quotient term model
with the three-case predicate interpretation `P_C`). The goal
`Decision.msUnsatisfiable C` is the ORIGINAL (UN-encoded) `C`'s
unsatisfiability over `L`; the encoding preserves satisfiability because
`P ≡ (P ≡ ⊤)` is valid (`msEncodeAtom_eval`). Proof body `sorry` at
this stage — the type carries the full content.

FIX (faithfulness, hypotheses `hC` and `hNoBot` ADDED): the textbook
(lines 30-34) states this lemma for `C'` "of the form
`t₁≐u₁ ∧ … ∧ ¬rₙ≐vₙ`", i.e. for `C` a conjunction of (negated)
equation/predicate literals. Without that hypothesis the forward direction
(no collision ⇒ satisfiable) is FALSE — e.g. `C = falsum` has no collision
yet is unsatisfiable. Two hypotheses restore the textbook precondition:
* `(hC : Decision.msIsConjunctionOfLiterals C)` — the conjunction-of-
  literals shape;
* `(hNoBot …)` — every literal conjunct is a (negated) equation or
  (negated) predicate ATOM, i.e. NOT bare `falsum`/`neg falsum` (which the
  codebase's `isAtomic`/`isLiteral` would otherwise admit, but a `falsum`
  conjunct makes `C` unsatisfiable while the no-collision premise stays
  vacuous). The textbook's literals never include bare `⊥`, so this is
  faithful and NOT a weakening.
Both are threaded to `noCollision_sat_direction_pred` in the forward
direction; the backward direction (collision ⇒ unsat) needs NEITHER. -/
@[blueprint "chap10__lemma_10_6_4" (main := true)]
theorem msUnsatisfiable_iff_collision_withPredicates (L : MSLanguage)
    (C : MSFormula L)
    (hC : Decision.msIsConjunctionOfLiterals C)
    (hNoBot : ∀ X, Decision.msConjunctContains C X → MSFormula.isLiteral X →
      (X ≠ MSFormula.falsum ∧ X ≠ MSFormula.neg MSFormula.falsum)) :
    Decision.msUnsatisfiable C ↔
      ∃ (s : (boolExtendedLanguage L).SortType)
        (r v : MSTerm (boolExtendedLanguage L) s)
        (p q : (graphOfConjunction (L := boolExtendedLanguage L)
          (msEncodeConjunction L C)).Node),
        Decision.msConjunctContains (msEncodeConjunction L C)
          (MSFormula.neg (MSFormula.eq_ (L := boolExtendedLanguage L) rfl s r v)) ∧
          p.1 = ⟨s, r⟩ ∧ q.1 = ⟨s, v⟩ ∧
          msCongruenceClosure
            (graphOfConjunction (L := boolExtendedLanguage L)
              (msEncodeConjunction L C))
            (positiveEquationRelation (L := boolExtendedLanguage L)
              (msEncodeConjunction L C)) (positiveEquationRelation_sortSupported (msEncodeConjunction L C)) p q

end LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates
end

