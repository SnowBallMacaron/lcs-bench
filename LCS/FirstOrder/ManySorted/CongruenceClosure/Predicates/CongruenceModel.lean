import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Equality
import LCS.FirstOrder.ManySorted.CongruenceClosure
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
import LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.Encoding
import Attach
import LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.CongruenceModel.ProofsStamp

section
namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates
open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.FirstOrder.ManySorted.Equality
open LCS.FirstOrder.ManySorted.CongruenceClosure
open LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
open LCS.Propositional.Semantics

/-- Lemma 10.6.4 (soundness core): a collision on a negated equation of
`C' = msEncodeConjunction L C` (terms `r ↔*_E v` for some negated equation
`¬(r ≐_s v)` of `C'`) makes the ORIGINAL `C` unsatisfiable. The collision
makes `C'` unsatisfiable (Decision's `collision_unsat_direction` applied to
`C'`: any model of `C'` would satisfy both `r ≐ v` and `¬(r ≐ v)`); since the
encoding preserves satisfiability (`encodePreservesSat`), `C` is unsatisfiable
too. This single core folds BOTH textbook cases (non-bool sort and atom = ⊤):
the soundness argument is identical regardless of the colliding sort. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem collisionUnsatPredCore (L : MSLanguage) (C : MSFormula L)
    (s : (boolExtendedLanguage L).SortType)
    (r v : MSTerm (boolExtendedLanguage L) s)
    (p q : (graphOfConjunction (L := boolExtendedLanguage L)
      (msEncodeConjunction L C)).Node)
    (hcontains : Decision.msConjunctContains (msEncodeConjunction L C)
      (MSFormula.neg (MSFormula.eq_ (L := boolExtendedLanguage L) rfl s r v)))
    (hp : p.1 = ⟨s, r⟩) (hq : q.1 = ⟨s, v⟩)
    (hcol : msCongruenceClosure
      (graphOfConjunction (L := boolExtendedLanguage L) (msEncodeConjunction L C))
      (positiveEquationRelation (L := boolExtendedLanguage L)
        (msEncodeConjunction L C)) (positiveEquationRelation_sortSupported (msEncodeConjunction L C)) p q) :
    Decision.msUnsatisfiable C 

-- ===================================================================
-- Lemma 10.6.4 (helpers): semanticEqualityRelationPred is an equivalence
-- and a function congruence (mirrors Decision's semanticEqualityRelation)
-- ===================================================================

/-- Lemma 10.6.4 (helper): every formula is a conjunct of itself
(`msConjunctContains Y Y`) — for a `conj` via the self-disjunct `Or.inl
rfl`, otherwise by `rfl` of the catch-all clause. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem msConjunctContains_self {L' : MSLanguage} (Y : MSFormula L') :
    Decision.msConjunctContains Y Y 

/-- Lemma 10.6.4 (helper): for a non-`conj` formula `Y`, `msConjunctContains
Y X` is just `Y = X` (the catch-all clause of `msConjunctContains`). -/
@[blueprint "chap10__lemma_10_6_4"]
theorem msConjunctContains_nonConj {L' : MSLanguage} {Y X : MSFormula L'}
    (hY : ∀ A B, Y ≠ MSFormula.conj A B)
    (h : Decision.msConjunctContains Y X) : Y = X 

/-- Lemma 10.6.4 (helper): a positive equation is a literal. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem posEq_isLiteral {L' : MSLanguage} {X : MSFormula L'}
    (h : Decision.msIsPositiveEquation X) : MSFormula.isLiteral X 

/-- Lemma 10.6.4 (helper): a negated equation is a literal. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem negEq_isLiteral {L' : MSLanguage} {X : MSFormula L'}
    (h : Decision.msIsNegatedEquation X) : MSFormula.isLiteral X 

/-- Lemma 10.6.4 (helper): a positive or negated equation is a literal. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem eqOrNegEq_isLiteral {L' : MSLanguage} {X : MSFormula L'}
    (h : Decision.msIsPositiveEquation X ∨ Decision.msIsNegatedEquation X) :
    MSFormula.isLiteral X 

/-- Lemma 10.6.4 (helper): a single literal is a conjunction of literals —
a literal is atomic (`falsum`/`pred`/`eq_`) or `neg (atomic)`, none of
which is a `conj`, so `msIsConjunctionOfLiterals` falls to the catch-all
`isLiteral` clause. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem isLiteral_imp_conjOfLiterals {L' : MSLanguage} {X : MSFormula L'}
    (h : MSFormula.isLiteral X) : Decision.msIsConjunctionOfLiterals X 

/-- Lemma 10.6.4 (helper): the encoded formula is a conjunct of itself. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem encode_self_contains (L : MSLanguage) (A : MSFormula L) :
    Decision.msConjunctContains (msEncodeConjunction L A) (msEncodeConjunction L A) 

/-- Lemma 10.6.4 (helper): a literal `A` of `L` that is NOT `falsum` and
NOT `neg falsum` encodes to a single (positive or negated) equation over
`L'` — `eq_`/`pred` give a positive equation `eq_ … ⊤`, `neg (eq_)` /
`neg (pred)` give a negated equation. Since none of these encode to a
`conj`, `msConjunctContains (encode A) X` forces `X = encode A`, an
equation. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem encode_literal_isEq (L : MSLanguage)
    (A : MSFormula L) (hlit : MSFormula.isLiteral A)
    (hbot : A ≠ MSFormula.falsum) (hnbot : A ≠ MSFormula.neg MSFormula.falsum) :
    ∀ X, Decision.msConjunctContains (msEncodeConjunction L A) X →
      Decision.msIsPositiveEquation X ∨ Decision.msIsNegatedEquation X 

/-- Lemma 10.6.4 (helper): `msEncodeConjunction` preserves the conjunction
tree, so a conjunct of `encode (conj A B)` is one of `encode A` /
`encode B` (or the whole conjunction). -/
@[blueprint "chap10__lemma_10_6_4"]
theorem encode_conj_eq (L : MSLanguage) (A B : MSFormula L) :
    msEncodeConjunction L (MSFormula.conj A B)
      = MSFormula.conj (msEncodeConjunction L A) (msEncodeConjunction L B) 

/-- Lemma 10.6.4 (helper): `msEncodeConjunction` preserves the
conjunction-of-literals shape — the encoded conjunction is again a
conjunction of literals over `L'`. Each leaf literal (`eq_`/`pred`/
`neg eq_`/`neg pred`) encodes to a (negated) equation, which IS a literal;
`falsum`/`neg falsum` are excluded by `hbot`. The conjunction structure is
preserved by `encode_conj_eq`. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem encode_isConjOfLiterals (L : MSLanguage) :
    ∀ (C : MSFormula L), Decision.msIsConjunctionOfLiterals C →
      (∀ X, Decision.msConjunctContains C X → MSFormula.isLiteral X →
        (X ≠ MSFormula.falsum ∧ X ≠ MSFormula.neg MSFormula.falsum)) →
      Decision.msIsConjunctionOfLiterals (msEncodeConjunction L C) 

/-- Lemma 10.6.4 (helper, GUARDED `encode_isConjOfEquations`): every
LITERAL conjunct `X` of the encoded conjunction `C' = msEncodeConjunction
L C` is a positive or negated equation over `L'`. The `isLiteral X` guard
excludes the non-literal self-conjunct of an inner `conj` (a conjunction is
never an equation, so the unguarded `msIsConjunctionOfEquations` is in fact
NEVER provable for an actual conjunction — its `∀ X` ranges over the whole
`conj` self-conjunct). This guarded form is exactly what
`Decision.conjunctionOfLiterals_eval_T` consumes (it supplies the
`isLiteral X` guard), so it is the right bridge to the model construction.
Requires the textbook falsum-exclusion `hbot`. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem encode_conjuncts_isEq (L : MSLanguage) :
    ∀ (C : MSFormula L), Decision.msIsConjunctionOfLiterals C →
      (∀ X, Decision.msConjunctContains C X → MSFormula.isLiteral X →
        (X ≠ MSFormula.falsum ∧ X ≠ MSFormula.neg MSFormula.falsum)) →
      (∀ X, Decision.msConjunctContains (msEncodeConjunction L C) X →
        MSFormula.isLiteral X →
        Decision.msIsPositiveEquation X ∨ Decision.msIsNegatedEquation X) 

/-- Lemma 10.6.4 (helper, GUARDED model construction): the literal-guarded
analogue of `Decision.noCollision_sat_direction`. Given a conjunction of
literals `C'` over ANY language `L'` whose LITERAL conjuncts are all
(positive or negated) equations (`hCeq`, with the `isLiteral X` guard), and
no collision (`hno`), the quotient term model `quotientModel C'` with the
identity-class assignment satisfies `C'`. Mirrors Decision's proof body
exactly, but takes the guarded per-conjunct condition — this avoids the
UNPROVABLE `msIsConjunctionOfEquations C'` (whose `∀ X` would force the
non-literal `conj` self-conjunct to be an equation). The `isLiteral X`
guard is exactly the one `Decision.conjunctionOfLiterals_eval_T` supplies,
so the construction goes through unchanged. -/
@[attach_debt, blueprint "chap10__lemma_10_6_4"]
theorem noCollision_sat_direction_guarded {L' : MSLanguage} (C' : MSFormula L')
    (hClit : Decision.msIsConjunctionOfLiterals C')
    (hCeq : ∀ X, Decision.msConjunctContains C' X → MSFormula.isLiteral X →
      (Decision.msIsPositiveEquation X ∨ Decision.msIsNegatedEquation X))
    (hno : ¬ ∃ (hL : L'.hasEquality = true) (s : L'.SortType) (r v : MSTerm L' s)
      (p q : (graphOfConjunction C').Node),
      Decision.msConjunctContains C' (MSFormula.neg (MSFormula.eq_ hL s r v)) ∧
        p.1 = ⟨s, r⟩ ∧ q.1 = ⟨s, v⟩ ∧
        msCongruenceClosure (graphOfConjunction C')
          (positiveEquationRelation C') (positiveEquationRelation_sortSupported C') p q) :
    Decision.msSatisfiable C' 

end LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates
end

