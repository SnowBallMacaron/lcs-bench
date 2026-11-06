import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.CutElim.CompletenessBridge
import LCS.CutElim.LKe
import LCS.CutElim.Interpolation
import LCS.FirstOrder.Syntax
import LCS.FirstOrder.Semantics
import LCS.CutElim.Beth.Definability
import Attach
import LCS.CutElim.Beth.WithoutEquality.ProofsStamp

section
namespace LCS.CutElim.Beth
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Completeness
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.SyntaxN.Variables
open Classical

-- ===================================================================
-- Theorem 6.6.1 (companion, part a): SomePredOccurs
-- ===================================================================
/-- Theorem 6.6.1 (companion, part a): At least one predicate symbol
P_i from the finite list actually occurs in the axiom formula. -/
@[blueprint "chap6__theorem_6_6_1"]
def SomePredOccurs {L : Language}
    (A : FormulaN L) (preds : PredList L) : Prop :=
  ∃ p ∈ preds.syms, formulaPredSymbolsEqN A p

-- ===================================================================
-- Theorem 6.6.1 (companion, part b): NoPredOccurs
-- ===================================================================
/-- Theorem 6.6.1 (companion, part b): None of the predicate symbols
P_1,...,P_k occur in the axiom formula. -/
@[blueprint "chap6__theorem_6_6_1"]
def NoPredOccurs {L : Language}
    (A : FormulaN L) (preds : PredList L) : Prop :=
  ∀ p ∈ preds.syms, ¬ formulaPredSymbolsEqN A p

-- ===================================================================
-- Theorem 6.6.1 (companion, part b): UnivTrueOrFalse
-- ===================================================================
/-- Theorem 6.6.1 (companion, part b): Q is either universally true
or universally false under the axioms, in the original language L. -/
@[blueprint "chap6__theorem_6_6_1"]
def UnivTrueOrFalse {L : Language}
    (implDef : ImplicitDefinability L) : Prop :=
  universallyValidN
    (FormulaN.impl implDef.axiomFormula
      (bethUniversalPrefix (L.predArity implDef.predQ)
        (bethPredApplied implDef.predQ))) ∨
  universallyValidN
    (FormulaN.impl implDef.axiomFormula
      (bethUniversalPrefix (L.predArity implDef.predQ)
        (FormulaN.neg (bethPredApplied implDef.predQ))))

-- ===================================================================
-- Theorem 6.6.1/6.6.2: ExplicitDefinabilityWitness
-- ===================================================================
/-- Theorem 6.6.1 (required helper): Predicate capturing that a
formula D explicitly defines Q from P_1,...,P_k for the given implDef:
namely, A(P_1,...,P_k,Q) ⊃ ∀x_1...∀x_n (Q(x_1,...,x_n) ≡ D(P_1,...,P_k))
is universally valid, with D's predicates among P_1,...,P_k, free vars
in {x_0,...,x_{n-1}}, and at least one P_i occurring. Used in the
statement of Theorem 6.6.1(a), for languages without equality. -/
@[blueprint "chap6__theorem_6_6_1"]
def ExplicitDefinabilityWitness {L : Language}
    (implDef : ImplicitDefinability L) (D : FormulaN L) : Prop :=
  (∀ v, v ∈ formulaFVN D → v < L.predArity implDef.predQ) ∧
  (∀ p, formulaPredSymbolsEqN D p → p ∈ implDef.preds.syms) ∧
  (∃ p ∈ implDef.preds.syms, formulaPredSymbolsEqN D p) ∧
  universallyValidN
    (FormulaN.impl implDef.axiomFormula
      (bethUniversalPrefix (L.predArity implDef.predQ)
        (FormulaN.equiv (bethPredApplied implDef.predQ) D)))

/- Semantic and finite-support helpers used in the common-predicate
branch of Beth's theorem. -/

-- ATTACH-BLOCKER: private declaration
/-- The left side of the Craig implication in L⁺: A(P,Q) ∧ Q(x̄). -/
private def bethCraigAntecedent {L : Language}
    (implDef : ImplicitDefinability L) :
    FormulaN (L.addPred (L.predArity implDef.predQ)) :=
  .conj (implDef.axiomFormula.liftAddPred (L.predArity implDef.predQ))
    (bethPredApplied (some implDef.predQ))

-- ATTACH-BLOCKER: private declaration
/-- The right side in L⁺: A(P,Q′) ⊃ Q′(x̄), where Q′ is the fresh predicate none. -/
private noncomputable def bethCraigConsequent {L : Language}
    (implDef : ImplicitDefinability L) :
    FormulaN (L.addPred (L.predArity implDef.predQ)) :=
  .impl
    (formulaPredSubstN (some implDef.predQ) none rfl
      (implDef.axiomFormula.liftAddPred (L.predArity implDef.predQ)))
    (bethPredApplied none)

/-- The implicit-definability condition yields the Craig implication
as an LK-provable sequent in the fresh-predicate expansion. -/
private theorem bethCraigImplication_provable {L : Language}
    (hNoEq : L.withoutEquality) (implDef : ImplicitDefinability L) :
    folkProvable
      ⟨[bethCraigAntecedent implDef], [bethCraigConsequent implDef]⟩ := by
  -- Specialize the universal prefix of validityCondition and curry the
  -- resulting implication; obtain an LK proof using validity with cuts.
  -- REPAIR(T6-57b): proof pending
  sorry

/-- If no listed predicate occurs in A, the two sides of the L⁺ Craig
implication have no common predicate: only some Q can occur on the left,
and only the fresh none can occur on the right. -/
private theorem bethCraig_no_common_pred {L : Language}
    (implDef : ImplicitDefinability L)
    (hNone : NoPredOccurs implDef.axiomFormula implDef.preds) :
    ∀ P : (L.addPred (L.predArity implDef.predQ)).predSymbols,
      ¬ (LCS.CutElim.Interpolation.formulaPredSymbolsN (bethCraigAntecedent implDef) P ∧
        LCS.CutElim.Interpolation.formulaPredSymbolsN (bethCraigConsequent implDef) P) := by
  -- REPAIR(T6-57b): proof pending
  sorry

/-- Interpret the fresh predicate as Q to lower Craig's disjunction
from L⁺ to the original language, then universally quantify Q's arguments. -/
private theorem bethCraig_dichotomy_lower {L : Language}
    (implDef : ImplicitDefinability L)
    (hCraig :
      folkProvable ⟨[bethCraigAntecedent implDef], []⟩ ∨
      folkProvable ⟨[], [bethCraigConsequent implDef]⟩) :
    UnivTrueOrFalse implDef := by
  -- The left branch says A ∧ Q is impossible; the right branch says
  -- A(P,Q′) implies Q′. Lower by interpreting the fresh copy as Q.
  -- REPAIR(T6-57b): proof pending
  sorry

private theorem beth_explicit_definer_exists
    (L : Language)
    (hNoEq : L.withoutEquality)
    (implDef : ImplicitDefinability L)
    (hOccurs : SomePredOccurs implDef.axiomFormula implDef.preds) :
    ∃ D : FormulaN L, ExplicitDefinabilityWitness implDef D := by
  -- Apply Craig interpolation in the fresh-predicate expansion, then
  -- lower the interpolant to L and adjoin a closed tautology over an
  -- occurring listed predicate to satisfy the nonempty-occurrence clause.
  -- REPAIR(T6-57a): proof pending
  sorry

-- ===================================================================
-- Theorem 6.6.1 (part a, required helper): beth_explicit_definer
-- ===================================================================
-- ATTACH-BLOCKER: private name in relocated declaration
/-- Theorem 6.6.1 (part a, required helper): Given an implicit
definability witness for Q together with a proof that at least one
P_i occurs in the axiom formula, constructs an explicit definability
witness — the L-formula D(P_1,...,P_k) obtained from Craig's
interpolation (Theorem 6.5.1) that explicitly defines Q from
P_1,...,P_k.

STANDING ASSUMPTION #11 (§5.4): Theorem 6.6.1 is for first-order
languages WITHOUT equality; encoded by `L.withoutEquality`. -/
noncomputable def beth_explicit_definer
    (L : Language)
    (hNoEq : L.withoutEquality)
    (implDef : ImplicitDefinability L)
    (hOccurs : SomePredOccurs implDef.axiomFormula implDef.preds) :
    FormulaN L :=
-- BEGIN PROOF
  Classical.choose
    (beth_explicit_definer_exists L hNoEq implDef hOccurs)

-- ATTACH-BLOCKER: private name in relocated declaration
/-- The formula produced by `beth_explicit_definer` satisfies the
four conditions bundled in `ExplicitDefinabilityWitness`: its free
variables are among {x_0,...,x_{n-1}}, its predicate symbols are
among P_1,...,P_k, at least one P_i occurs, and the biconditional
under the axiom is universally valid. -/
theorem beth_explicit_definer_spec
    (L : Language)
    (hNoEq : L.withoutEquality)
    (implDef : ImplicitDefinability L)
    (hOccurs : SomePredOccurs implDef.axiomFormula implDef.preds) :
    ExplicitDefinabilityWitness implDef
      (beth_explicit_definer L hNoEq implDef hOccurs) :=
-- BEGIN PROOF
by
  exact Classical.choose_spec
    (beth_explicit_definer_exists L hNoEq implDef hOccurs)

-- ===================================================================
-- Theorem 6.6.1 (companion, part a): beth_without_equality_part_a
-- ===================================================================
-- ===================================================================
-- Theorem 6.6.1 (companion, part b): beth_without_equality_part_b
-- ===================================================================
-- ATTACH-BLOCKER: private name in relocated declaration
/-- Theorem 6.6.1 (companion, part b): If no predicate symbol
occurs in the axiom formula, Q is universally true or false.

STANDING ASSUMPTION #11 (§5.4): Theorem 6.6.1 is for first-order
languages WITHOUT equality; encoded by `L.withoutEquality`. -/
theorem beth_without_equality_part_b
    (L : Language)
    (hNoEq : L.withoutEquality)
    (implDef : ImplicitDefinability L)
    (hNone : NoPredOccurs implDef.axiomFormula implDef.preds) :
    UnivTrueOrFalse implDef :=
-- BEGIN PROOF
by
  apply bethCraig_dichotomy_lower implDef
  exact LCS.CutElim.Interpolation.craig_interpolation_no_common_pred
    (bethCraigAntecedent implDef) (bethCraigConsequent implDef)
    (show (L.addPred (L.predArity implDef.predQ)).withoutEquality from hNoEq)
    (bethCraigImplication_provable hNoEq implDef)
    (bethCraig_no_common_pred implDef hNone)

-- ===================================================================
-- Theorem 6.6.1: beth_definability_without_equality
-- ===================================================================
/-- Theorem 6.6.1: (Beth's definability theorem, without equality)
(a) If some predicate symbol occurs in the axiom, implicit
definability implies explicit definability. (b) If no predicate
symbol occurs, Q is universally true or universally false.

STANDING ASSUMPTION #11 (§5.4): Theorem 6.6.1 is for first-order
languages WITHOUT equality; encoded by `L.withoutEquality`. -/
@[blueprint "chap6__theorem_6_6_1" (main := true)]
theorem beth_definability_without_equality
    (L : Language)
    (hNoEq : L.withoutEquality)
    (implDef : ImplicitDefinability L) :
    (SomePredOccurs implDef.axiomFormula implDef.preds →
      ∃ D : FormulaN L, ExplicitDefinabilityWitness implDef D) ∧
    (NoPredOccurs implDef.axiomFormula implDef.preds →
      UnivTrueOrFalse implDef) 

end LCS.CutElim.Beth
end
