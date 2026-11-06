import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Equality
import LCS.FirstOrder.ManySorted.CongruenceClosure
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.DisjunctiveNormalForm
import Attach
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.ValidityReduction.ProofsStamp

section
namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.FirstOrder.ManySorted.Equality
open LCS.FirstOrder.ManySorted.CongruenceClosure
open LCS.Propositional.Semantics

-- ===================================================================
-- Lemma 10.6.1 (companion): the Herbrand satisfaction lemma for the
-- no-equality trivial case (part (4) forward)
-- ===================================================================

/-- Lemma 10.6.1 (companion): the all-terms family `fun _ _ => True` is a
generated term algebra over `L` — every sort carrier is nonempty (the
variable `x_0^s`), and it is trivially closed under functions, constants and
subterms (every term is a member). Supplies the term-algebra hypothesis of
the Herbrand structure `Gentzen.msHintikkaStructure` used to satisfy a
collision-free conjunction of literals in part (4) of
`msValid_reduces_to_conjunction_unsat`. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem msIsGeneratedTermAlgebra_univ (L : MSLanguage) :
    Gentzen.MSIsGeneratedTermAlgebra L (fun _ => (fun _ => True : Set (MSTerm L _)))

/-- Lemma 10.6.1 (companion): the signed-formula set selecting the POSITIVE
atomic conjuncts of `C` — `T A ∈ trueConjunctsSet C` iff `A` is a conjunct
of `C`. Feeds the predicate valuation of the Herbrand structure: an atom
`P t₁…t_k` is interpreted as `T` exactly when it is a (positive) conjunct of
`C`. -/
@[blueprint "chap10__lemma_10_6_1"]
def trueConjunctsSet {L : MSLanguage} (C : MSFormula L) :
    Set (Gentzen.MSSignedFormula L) :=
  fun sf => ∃ A, sf = Gentzen.MSSignedFormula.trueF A ∧ msConjunctContains C A

/-- Lemma 10.6.1 (companion): the FORWARD direction of part (4) of Lemma
10.6.1, separated out. For a language WITHOUT equality, a
conjunction-of-literals `C` none of whose literal conjuncts is bare
`⊥`/`¬⊥` (`hNoBot`) and which contains NO complementary atomic pair (`hno`)
is SATISFIABLE. The model is the Herbrand structure on the all-terms term
algebra (`msHintikkaStructure (fun _ => Set.univ) (trueConjunctsSet C)`):
its predicate valuation makes an atom true exactly when it is a positive
conjunct of `C`. Every positive conjunct `P t₁…t_k` is then true; every
negated conjunct `¬P t₁…t_k` is true because otherwise `P t₁…t_k` would be a
positive conjunct, forming a complementary pair (contradicting `hno`). Since
no conjunct can be a bare `⊥`/`¬⊥` (`hNoBot`) or an equation (`hEq`, no
equality), these are the only literal shapes. Hence `C` is satisfied. -/
@[blueprint "chap10__lemma_10_6_1"]
theorem sat_of_no_complementary_pair {L : MSLanguage} (hEq : L.withoutEquality)
    (C : MSFormula L) (hClit : msIsConjunctionOfLiterals C)
    (hNoBot : ∀ X, msConjunctContains C X → MSFormula.isLiteral X →
      (X ≠ MSFormula.falsum ∧ X ≠ MSFormula.neg MSFormula.falsum))
    (hno : ¬ ∃ P, msConjunctContains C P ∧
      msConjunctContains C (MSFormula.neg P) ∧ P.isAtomic) :
    msSatisfiable C 

/-- Lemma 10.6.1: The reduction of deciding validity of a
quantifier-free formula to deciding unsatisfiability of conjunctions of
literals. Stated as the CONJUNCTION (∧) of four genuine, separately
meaningful parts:

(1) DNF existence (Lemma 10.6.1 proper): for every quantifier-free `A`
    there EXISTS a DNF formula `B` with `A ≡ B` valid;
(2) validity-via-unsat-of-negation: a quantifier-free `A` is valid iff
    the DNF `B` of `¬A` is unsatisfiable;
(3) DNF unsatisfiability criterion: a DNF `B = C_1 ∨ … ∨ C_n` is
    unsatisfiable iff every disjunct `C_i` is unsatisfiable;
(4) no-equality trivial case: if `L` has no equality symbols then a
    conjunction of literals `C` is unsatisfiable iff it contains some
    atomic formula together with its negation.

Each part adds information and uses a distinct hypothesis (Pattern 2/3:
the chain of equivalences the textbook actually argues).

The disjuncts in (3) are top-level conjunction leaves. -/
@[attach_debt, blueprint "chap10__lemma_10_6_1" (main := true)]
theorem msValid_reduces_to_conjunction_unsat (L : MSLanguage) :
    -- (1) DNF existence
    (∀ A : MSFormula L, msIsQuantifierFree A →
      ∃ B, msIsDNF B ∧ msValid (MSFormula.equiv_ A B)) ∧
    -- (2) validity via unsatisfiability of the negation's DNF
    (∀ A B : MSFormula L, msIsQuantifierFree A → msIsDNF B →
      msValid (MSFormula.equiv_ (MSFormula.neg A) B) →
        (msValid A ↔ msUnsatisfiable B)) ∧
    -- (3) DNF unsatisfiability criterion
    (∀ B : MSFormula L, msIsDNF B →
      (msUnsatisfiable B ↔ ∀ Ci, msIsDisjunctOf Ci B → msUnsatisfiable Ci)) ∧
    -- (4) no-equality trivial case
    --
    -- FIX (faithfulness, hypothesis `hNoBot` ADDED — issue c3de0858,
    -- mirroring the accepted Predicates Lemma 10.6.4 fix, review e021844c):
    -- the biconditional as ORIGINALLY stated is FALSE because `C = ⊥` is a
    -- conjunction-of-literals (`isAtomic ⊥ = True`) that is unsatisfiable yet
    -- contains NO complementary atomic pair. Gallier §10.6.1 phrases this
    -- trivial case for conjunctions of (negated) equation/predicate-atom
    -- literals, implicitly excluding the degenerate `⊥` literal. The
    -- `hNoBot` precondition restores exactly that textbook restriction —
    -- every literal conjunct of `C` is NOT bare `⊥`/`¬⊥` — making the
    -- forward direction (unsatisfiable ⇒ complementary pair) a theorem. It is
    -- NOT a weakening (the textbook literals never include bare `⊥`).
    (∀ C : MSFormula L, L.withoutEquality → msIsConjunctionOfLiterals C →
      (∀ X, msConjunctContains C X → MSFormula.isLiteral X →
        (X ≠ MSFormula.falsum ∧ X ≠ MSFormula.neg MSFormula.falsum)) →
      (msUnsatisfiable C ↔
        ∃ P, msConjunctContains C P ∧
          msConjunctContains C (MSFormula.neg P) ∧ P.isAtomic)) 

end LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
end
