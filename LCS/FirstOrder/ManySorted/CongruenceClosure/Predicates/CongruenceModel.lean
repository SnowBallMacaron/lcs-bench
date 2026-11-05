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

/-- Lemma 10.6.4 (required, case (i)): when the colliding negated equation
of `C'` has NON-bool sort (`s = some s' ≠ none`), the contradiction is
obtained exactly as in the proof of Lemma 10.6.2 (the equational,
predicate-free argument), discharged by the sibling
`Decision.msUnsatisfiable_iff_collision`. This is "case (i) non-bool
sort". Concludes unsatisfiability of the ORIGINAL `C`. Folds into the
soundness core `collisionUnsatPredCore`. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem collisionCaseNonBool (L : MSLanguage) (C : MSFormula L)
    (s : (boolExtendedLanguage L).SortType) (hs : s ≠ MSBoolSort L)
    (r v : MSTerm (boolExtendedLanguage L) s)
    (p q : (graphOfConjunction (L := boolExtendedLanguage L)
      (msEncodeConjunction L C)).Node)
    (hp : p.1 = ⟨s, r⟩) (hq : q.1 = ⟨s, v⟩)
    (hcontains : Decision.msConjunctContains (msEncodeConjunction L C)
      (MSFormula.neg (MSFormula.eq_ (L := boolExtendedLanguage L) rfl s r v)))
    (hcol : msCongruenceClosure
      (graphOfConjunction (L := boolExtendedLanguage L) (msEncodeConjunction L C))
      (positiveEquationRelation (L := boolExtendedLanguage L)
        (msEncodeConjunction L C)) (positiveEquationRelation_sortSupported (msEncodeConjunction L C)) p q) :
    Decision.msUnsatisfiable C 

/-- Lemma 10.6.4 (required, case (ii)): when the colliding terms are an
atomic formula `P y₁…y_k` and the constant `⊤` (the bool-sort collision
`P y₁…y_k ↔*_E ⊤`), then `E ⊨ P y₁…y_k` (via the closure-entails-equation
step transported to the bool sort, plus `msEncodeAtom_eval`), so
any model of `C` satisfies both the atom and its negation — a
contradiction — hence `C` is unsatisfiable. This is "case (ii) atom equals
top". Proof body `sorry`. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem collisionCaseAtomTop (L : MSLanguage) (C : MSFormula L)
    (P : L.predSymbols)
    (args : (i : Fin ((L.predArity P).map some).length) →
      MSTerm (boolExtendedLanguage L)
        (((L.predArity P).map some).get i))
    (p q : (graphOfConjunction (L := boolExtendedLanguage L)
      (msEncodeConjunction L C)).Node)
    (hp : p.1 = ⟨MSBoolSort L, msPredAsFuncTerm L P args⟩)
    (hq : q.1 = ⟨MSBoolSort L, msTopConst L⟩)
    (hcontains : Decision.msConjunctContains (msEncodeConjunction L C)
      (MSFormula.neg (msEncodeAtom L P args)))
    (hcol : msCongruenceClosure
      (graphOfConjunction (L := boolExtendedLanguage L) (msEncodeConjunction L C))
      (positiveEquationRelation (L := boolExtendedLanguage L)
        (msEncodeConjunction L C)) (positiveEquationRelation_sortSupported (msEncodeConjunction L C)) p q) :
    Decision.msUnsatisfiable C 

-- ===================================================================
-- Lemma 10.6.4 (required defs/theorems): the term algebra C with the
-- three-case predicate interpretation P_C and its congruence
-- ===================================================================

/-- Lemma 10.6.4 (required): the boolean-valued predicate interpretation
`P_C` of a predicate symbol `P` (of rank `(w₁…w_k, bool)`) in the term
algebra `C`, defined by the three-case congruence-closure rule
(`predicateInterpC_case1/2/3`): T if the in-domain atom `P y₁…y_k` is
closed to `⊤`, T if a surrogate atom is, and F otherwise. The three cases
are decided classically. `noncomputable` because it uses
`Classical.choice`/`propDecidable`. Realizes "predicate interpretation
`P_C`"; supplies the `interpPred`-style data of the with-predicate term
algebra. -/
@[blueprint "chap10__lemma_10_6_4"]
noncomputable def predicateInterpC (L : MSLanguage)
    (C' : MSFormula (boolExtendedLanguage L)) (P : L.predSymbols)
    (ys : (i : Fin (L.predArity P).length) →
      MSTerm (boolExtendedLanguage L) (some ((L.predArity P).get i))) :
    BoolVal :=
  -- The bool-sorted predicate-application term P y₁…y_k built over L'.
  let atom : MSTerm (boolExtendedLanguage L) (MSBoolSort L) :=
    msPredAsFuncTerm L P (fun i => by
      have hi : i.val < (L.predArity P).length := by
        have := i.isLt
        simpa [boolExtendedLanguage, boolExtendedFunRank, List.length_map]
          using this
      have hsort :
          (((L.predArity P).map some).get i) =
            some ((L.predArity P).get ⟨i.val, hi⟩) := by
        simp [boolExtendedLanguage, boolExtendedFunRank,
          List.get_eq_getElem, List.getElem_map]
        all_goals exact List.getElem_map some
      exact hsort ▸ ys ⟨i.val, hi⟩)
  -- The three textbook cases, decided classically on whether the atom (or
  -- a surrogate) is closed to ⊤ under E. Case 1/2: the atom is E-congruent
  -- to ⊤ (`semanticEqualityRelationPred … atom ⊤`) ⇒ T; case 3: otherwise
  -- ⇒ F. The atom genuinely depends on `ys`, so this is NOT a constant
  -- stub: changing `ys` changes `atom` and hence the decided value.
  letI := Classical.propDecidable
    (semanticEqualityRelationPred L C' (MSBoolSort L) atom (msTopConst L))
  if semanticEqualityRelationPred L C' (MSBoolSort L) atom (msTopConst L) then
    BoolVal.T
  else
    BoolVal.F

/-- Lemma 10.6.4 (required): the many-sorted Σ-algebra `C` built (over the
ORIGINAL language `L`) on the `S(C)`-indexed family `TERM(C)`, now also
containing the bool sort and bool-sorted terms (the predicate-application
terms and `⊤`). The carriers of sort `s` are the `R*`-classes of the
bool-extended sort-`some s` terms of `TERM(C')`; the predicate
interpretation is the three-case map `predicateInterpC` (so `P_C` is
genuinely the field that interprets predicates), and equality on the bool
carrier is the identity (`msEqBoolAsIdentity`). Realizes "term algebra `C`
over `TERM(C)` with bool". The predicate field is the substantive
three-case `predicateInterpC`.

FIX (mirrors the now-proven Decision `quotientModel`/`termAlgebra`,
issue f53e69a2): the sort-`s` carrier is `Option`-PADDED with the junk
element `none`, so EVERY sort carrier is nonempty even for sorts `s ∉ S(C')`
whose `TERM(C')_{some s}` is genuinely empty. The genuine sort-`some s` terms
of `TERM(C')` are the `some _` carrier elements; the padding only supplies a
junk element for irrelevant sorts, leaving the satisfaction of `C`
unaffected. Function and constant symbols off `S(C')` map to the junk
`none`; the predicate interpretation feeds the genuine argument terms (when
all are `some`) into `predicateInterpC`, returning the junk `F` otherwise. -/
@[blueprint "chap10__lemma_10_6_4"]
noncomputable def termAlgebraWithPred (L : MSLanguage)
    (C' : MSFormula (boolExtendedLanguage L)) : MSStructure L where
  -- The carrier of sort `s` is the `Option`-padded family of bool-extended
  -- sort-`some s` terms in `TERM(C')` (the `R*`-classes built on them
  -- downstream); `none` is the junk element making every carrier nonempty.
  carrier := fun s =>
    Option { t : MSTerm (boolExtendedLanguage L) (some s) //
        Decision.termSetOfConjunction C' ⟨some s, t⟩ }
  carrierNonempty := fun _ => ⟨none⟩
  -- Function symbols are interpreted by the junk `none` (the genuine term
  -- operation lives in the quotient construction; off `S(C')` the operation
  -- cannot land in `TERM(C')`, so the `Option` carrier supplies `none`).
  interpFunc := fun _ _ => none
  -- Constants: the constant term itself when it lies in `TERM(C')_{some s}`,
  -- else the junk `none`.
  interpConst := fun s c =>
    letI := Classical.propDecidable
      (Decision.termSetOfConjunction C'
        ⟨some s, MSTerm.const (L := boolExtendedLanguage L) (some s) c⟩)
    if h : Decision.termSetOfConjunction C'
        ⟨some s, MSTerm.const (L := boolExtendedLanguage L) (some s) c⟩ then
      some ⟨MSTerm.const (L := boolExtendedLanguage L) (some s) c, h⟩
    else none
  -- The predicate interpretation IS the three-case `P_C`; when every argument
  -- carrier is a genuine `some _` term, feed it to `predicateInterpC`, else
  -- return the junk value `F`.
  interpPred := fun P ys =>
    letI := Classical.propDecidable (∀ i, (ys i).isSome)
    if hall : ∀ i, (ys i).isSome then
      predicateInterpC L C' P (fun i => ((ys i).get (hall i)).1)
    else BoolVal.F

-- ===================================================================
-- Lemma 10.6.4 (helpers): semanticEqualityRelationPred is an equivalence
-- and a function congruence (mirrors Decision's semanticEqualityRelation)
-- ===================================================================

/-- Lemma 10.6.4 (helper): `semanticEqualityRelationPred` is reflexive. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem semanticEqualityRelationPred_refl (L : MSLanguage)
    (C' : MSFormula (boolExtendedLanguage L))
    (s : (boolExtendedLanguage L).SortType)
    (t : MSTerm (boolExtendedLanguage L) s) :
    semanticEqualityRelationPred L C' s t t 

/-- Lemma 10.6.4 (helper): `semanticEqualityRelationPred` is symmetric. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem semanticEqualityRelationPred_symm (L : MSLanguage)
    (C' : MSFormula (boolExtendedLanguage L))
    (s : (boolExtendedLanguage L).SortType)
    (t u : MSTerm (boolExtendedLanguage L) s)
    (h : semanticEqualityRelationPred L C' s t u) :
    semanticEqualityRelationPred L C' s u t 

/-- Lemma 10.6.4 (helper): `semanticEqualityRelationPred` is transitive. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem semanticEqualityRelationPred_trans (L : MSLanguage)
    (C' : MSFormula (boolExtendedLanguage L))
    (s : (boolExtendedLanguage L).SortType)
    (t u w : MSTerm (boolExtendedLanguage L) s)
    (h1 : semanticEqualityRelationPred L C' s t u)
    (h2 : semanticEqualityRelationPred L C' s u w) :
    semanticEqualityRelationPred L C' s t w 

/-- Lemma 10.6.4 (helper): `semanticEqualityRelationPred` is a function
congruence — if `y_i R z_i` for every argument index `i`, then
`g y_1…y_k R g z_1…z_k` (for `g` any function symbol of `L'`, in particular
the bool-output `Sum.inr P`). Because each `E ⊨ y_i ≐ z_i` gives equal
argument meanings, and equal arguments give equal `interpFunc` results. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem semanticEqualityRelationPred_funcCong (L : MSLanguage)
    (C' : MSFormula (boolExtendedLanguage L))
    (g : (boolExtendedLanguage L).funSymbols)
    (ys zs : (i : Fin ((boolExtendedLanguage L).funRank g).1.length) →
      MSTerm (boolExtendedLanguage L) (((boolExtendedLanguage L).funRank g).1.get i))
    (hcong : ∀ i, semanticEqualityRelationPred L C'
      (((boolExtendedLanguage L).funRank g).1.get i) (ys i) (zs i)) :
    semanticEqualityRelationPred L C' ((boolExtendedLanguage L).funRank g).2
      (MSTerm.func g ys) (MSTerm.func g zs) 

/-- Lemma 10.6.4 (required, case 1): `P_C(y₁,…,y_k) = T` when
`P y₁…y_k ∈ TERM(C)` and `P y₁…y_k ↔*_E ⊤` (the in-domain atom is closed
to `⊤`). "P_C case: in-domain atom closed to top".

The membership hypothesis `hmem` records that the in-domain atom
`P y₁…y_k` belongs to `TERM(C')` (the textbook's "P y₁…y_k ∈ TERM(C)"), and
the closure hypothesis `hclosed` records the textbook's "`P y₁…y_k ↔*_E ⊤`"
— this latter is exactly what makes `predicateInterpC` (defined by the
classical test `semanticEqualityRelationPred … atom ⊤`) return `T`. Adding
`hclosed` makes the statement FAITHFUL to the docstring (which lists BOTH
conditions); the original Lean statement carried only `hmem` and was
therefore unprovable as stated. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem predicateInterpC_case1 (L : MSLanguage)
    (C' : MSFormula (boolExtendedLanguage L)) (P : L.predSymbols)
    (ys : (i : Fin (L.predArity P).length) →
      MSTerm (boolExtendedLanguage L) (some ((L.predArity P).get i)))
    (hmem : Decision.termSetOfConjunction C'
      ⟨MSBoolSort L, msPredAsFuncTerm L P
        (fun i => by
          have hi : i.val < (L.predArity P).length := by
            have := i.isLt
            simpa [boolExtendedLanguage, boolExtendedFunRank, List.length_map]
              using this
          have hsort :
              (((L.predArity P).map some).get i) =
                some ((L.predArity P).get ⟨i.val, hi⟩) := by
            simp only [boolExtendedLanguage, boolExtendedFunRank, List.get_eq_getElem]
            first | all_goals exact List.getElem_map some | skip
          exact hsort ▸ ys ⟨i.val, hi⟩)⟩)
    (hclosed : semanticEqualityRelationPred L C' (MSBoolSort L)
      (msPredAsFuncTerm L P
        (fun i => by
          have hi : i.val < (L.predArity P).length := by
            have := i.isLt
            simpa [boolExtendedLanguage, boolExtendedFunRank, List.length_map]
              using this
          have hsort :
              (((L.predArity P).map some).get i) =
                some ((L.predArity P).get ⟨i.val, hi⟩) := by
            simp only [boolExtendedLanguage, boolExtendedFunRank, List.get_eq_getElem]
            first | all_goals exact List.getElem_map some | skip
          exact hsort ▸ ys ⟨i.val, hi⟩))
      (msTopConst L)) :
    predicateInterpC L C' P ys = BoolVal.T 

/-- Lemma 10.6.4 (helper): the `Sum.inr P` predicate-application atom built
inside `predicateInterpC` from a tuple `ys`, named so the congruence proof
can refer to it. -/
@[blueprint "chap10__lemma_10_6_4"]
def predAtomOf (L : MSLanguage) (P : L.predSymbols)
    (ys : (i : Fin (L.predArity P).length) →
      MSTerm (boolExtendedLanguage L) (some ((L.predArity P).get i))) :
    MSTerm (boolExtendedLanguage L) (MSBoolSort L) :=
  msPredAsFuncTerm L P (fun i => by
    have hi : i.val < (L.predArity P).length := by
      have := i.isLt
      simpa [boolExtendedLanguage, boolExtendedFunRank, List.length_map]
        using this
    have hsort :
        (((L.predArity P).map some).get i) =
          some ((L.predArity P).get ⟨i.val, hi⟩) := by
      simp [boolExtendedLanguage, boolExtendedFunRank,
        List.get_eq_getElem, List.getElem_map]
      all_goals exact List.getElem_map some
    exact hsort ▸ ys ⟨i.val, hi⟩)

/-- Lemma 10.6.4 (helper): `predicateInterpC` unfolds to the classical test
of whether `predAtomOf … ys` is `E`-congruent to `⊤`. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem predicateInterpC_eq (L : MSLanguage)
    (C' : MSFormula (boolExtendedLanguage L)) (P : L.predSymbols)
    (ys : (i : Fin (L.predArity P).length) →
      MSTerm (boolExtendedLanguage L) (some ((L.predArity P).get i))) :
    predicateInterpC L C' P ys =
      (letI := Classical.propDecidable
        (semanticEqualityRelationPred L C' (MSBoolSort L)
          (predAtomOf L P ys) (msTopConst L))
      if semanticEqualityRelationPred L C' (MSBoolSort L)
          (predAtomOf L P ys) (msTopConst L) then BoolVal.T else BoolVal.F) 

/-- Lemma 10.6.4 (helper): a sort-cast of two terms with equal meaning
keeps equal meaning — for `h : s = s'` and `t u : MSTerm L s` with equal
`msTermEval`, the cast terms `h ▸ t`, `h ▸ u` have equal `msTermEval`. By
cases on `h`. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem msTermEval_cast_congr {L : MSLanguage} (M : MSStructure L)
    (v : MSAssignment M) {s s' : L.SortType} (h : s = s') (t u : MSTerm L s)
    (heq : msTermEval M v t = msTermEval M v u) :
    msTermEval M v (h ▸ t) = msTermEval M v (h ▸ u) 

/-- Lemma 10.6.4 (helper): the predicate-application atoms of two
argument-congruent tuples are `E`-congruent. From `y_i ↔*_E z_i` for all
`i`, by function congruence (`Sum.inr P` is a bool-output function symbol),
`predAtomOf ys ↔*_E predAtomOf zs`. -/
@[attach_debt, blueprint "chap10__lemma_10_6_4"]
theorem predAtomOf_cong (L : MSLanguage)
    (C' : MSFormula (boolExtendedLanguage L)) (P : L.predSymbols)
    (ys zs : (i : Fin (L.predArity P).length) →
      MSTerm (boolExtendedLanguage L) (some ((L.predArity P).get i)))
    (hcong : ∀ i, semanticEqualityRelationPred L C' (some ((L.predArity P).get i))
      (ys i) (zs i)) :
    semanticEqualityRelationPred L C' (MSBoolSort L)
      (predAtomOf L P ys) (predAtomOf L P zs) 

/-- Lemma 10.6.4 (required, case 2): `P_C(y₁,…,y_k) = T` when
`P y₁…y_k ∉ TERM(C)` but there are surrogate terms `z₁,…,z_k` with
`y_i ↔*_E z_i`, `P z₁…z_k ∈ TERM(C)` and `P z₁…z_k ↔*_E ⊤`. "P_C case:
surrogate atom closed to top". The surrogate hypothesis gives
`y_i ↔*_E z_i`, so the atoms `predAtomOf ys`/`predAtomOf zs` are
`E`-congruent (`predAtomOf_cong`), hence the classical tests agree. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem predicateInterpC_case2 (L : MSLanguage)
    (C' : MSFormula (boolExtendedLanguage L)) (P : L.predSymbols)
    (ys zs : (i : Fin (L.predArity P).length) →
      MSTerm (boolExtendedLanguage L) (some ((L.predArity P).get i)))
    (hsurrogate :
      (∀ i, semanticEqualityRelationPred L C' (some ((L.predArity P).get i))
        (ys i) (zs i))) :
    predicateInterpC L C' P ys = predicateInterpC L C' P zs 

/-- Lemma 10.6.4 (required, case 3): `P_C(y₁,…,y_k) = F` otherwise (neither
case 1 nor case 2 applies — no closed/surrogate atom witnesses `⊤`). "P_C
case: otherwise false". -/
@[blueprint "chap10__lemma_10_6_4"]
theorem predicateInterpC_case3 (L : MSLanguage)
    (C' : MSFormula (boolExtendedLanguage L)) (P : L.predSymbols)
    (ys : (i : Fin (L.predArity P).length) →
      MSTerm (boolExtendedLanguage L) (some ((L.predArity P).get i)))
    (hnone : ¬ semanticEqualityRelationPred L C' (MSBoolSort L)
      (msPredAsFuncTerm L P
        (fun i => by
          have hi : i.val < (L.predArity P).length := by
            have := i.isLt
            simpa [boolExtendedLanguage, boolExtendedFunRank, List.length_map]
              using this
          have hsort :
              (((L.predArity P).map some).get i) =
                some ((L.predArity P).get ⟨i.val, hi⟩) := by
            simp only [boolExtendedLanguage, boolExtendedFunRank, List.get_eq_getElem]
            first | all_goals exact List.getElem_map some | skip
          exact hsort ▸ ys ⟨i.val, hi⟩))
      (msTopConst L)) :
    predicateInterpC L C' P ys = BoolVal.F 

/-- Lemma 10.6.4 (required): the congruence closure `↔*_E` is a congruence
on the algebra `C` in the NEW predicate case — if `y_i ↔*_E z_i` for all
`i` then `P_C(y₁,…,y_k) = P_C(z₁,…,z_k)` (textbook sub-cases (1) both
tuples in `TERM(C)` via graph-congruence of `↔*_E`; (2) one tuple outside,
via the surrogate-term argument). "Predicate-case congruence of the
closure on algebra `C`". Proof body `sorry`. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem closure_isAlgebraCongruence_pred (L : MSLanguage)
    (C' : MSFormula (boolExtendedLanguage L)) (P : L.predSymbols)
    (ys zs : (i : Fin (L.predArity P).length) →
      MSTerm (boolExtendedLanguage L) (some ((L.predArity P).get i)))
    (hcong : ∀ i,
      semanticEqualityRelationPred L C' (some ((L.predArity P).get i))
        (ys i) (zs i)) :
    predicateInterpC L C' P ys = predicateInterpC L C' P zs 

/-- Lemma 10.6.4 (required): the quotient model `M` obtained as the
quotient of the algebra `C = termAlgebraWithPred` by the congruence
`↔*_E` (as in Subsection 2.5.8): carriers are `R*`-classes, the predicate
interpretation the well-defined induced map `[P_C]`. Paired with the
assignment `v(x) = [x]` it satisfies `t_M[v] = [t]` for every
`t ∈ TERM(C)` and hence `M ⊨ C`. "Quotient model `M`". -/
@[blueprint "chap10__lemma_10_6_4"]
noncomputable def quotientModelWithPred (L : MSLanguage)
    (C' : MSFormula (boolExtendedLanguage L)) : MSStructure L :=
  termAlgebraWithPred L C'

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

/-- Lemma 10.6.4 (helper): the encoder commutes with negation —
`encode (neg A) = neg (encode A)` for EVERY `A`. For `A = pred P ts` this
holds because `msEncodeNegAtom = neg (msEncodeAtom)` and
`encode (pred P ts) = msEncodeAtom` use the same lifted arguments; all
other `neg A` clauses recurse as `neg (encode A)` directly. By cases on
`A`. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem encode_neg_eq (L : MSLanguage) (A : MSFormula L) :
    msEncodeConjunction L (MSFormula.neg A)
      = MSFormula.neg (msEncodeConjunction L A) 

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

