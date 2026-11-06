import LCS.SLD.LogicProgramming.Queries
import LCS.Item
import LCS.Util
import LCS.SLD.LogicProgramming
import LCS.SLD.LogicProgramming.Correctness.SubstitutedClauseSet
import Attach
import LCS.SLD.LogicProgramming.Correctness.CorrectnessTheorem.ProofsStamp

/-! # Correctness of SLD-resolution (Lemma 9.5.3, Theorem 9.5.1)

Section 9.5.3: the substituted clause set of an SLD-refutation is unsatisfiable, and SLD-resolution is a correct procedure for computing answer substitutions; logical computation in PROLOG. -/

section
namespace LCS.SLD.LogicProgramming.Correctness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.SLD.FirstOrder
open LCS.SLD.LogicProgramming

-- ===================================================================
-- Theorem 9.5.1 (required defs): Negative clause subsequence,
-- computed answer tuple, ground substitution for output variables
-- ===================================================================

/-- Original input occurrences in their derivation order: N₀ has index 0,
    and the input Cᵢ has its actual step index i (SQ38). -/
@[blueprint "chap9__theorem_9_5_1"]
def inputClauseOccurrences {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)} :
    {cg : LCS.Finset (FOAtom L hNoEq)} → FOSLDDerivation hNoEq (fun c => c ∈ D) goals cg →
      List (Nat × FOHornClause L hNoEq)
  | _, .init goal _ => [(0, goal)]
  | _, .step prev clause _ _ _ _ _ _ _ _ _ _ =>
      inputClauseOccurrences hNoEq prev ++ [(FOSLDDerivation.length hNoEq prev + 1, clause)]

/-- Query occurrences are selected by membership of the original clause in
    the Horn translation of ¬G, before substitution. Definite query clauses
    are included. Repetitions and actual indices are retained; the family may
    be empty. The stored clause is the negated component, so its falsity is
    the truth of the answer component. N₀ uses θ₁ (SQ25, SQ38). -/
@[blueprint "chap9__theorem_9_5_1"]
noncomputable def negativeClauseSubsequence {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)}
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (d : FOSLDDerivation hNoEq (fun c => c ∈ D) goals cg) (queryClauses : List (FOHornClause L hNoEq)) :
    List (Nat × FOClause L hNoEq) := by
  classical
  exact ((inputClauseOccurrences hNoEq d).filter fun pair => pair.2 ∈ queryClauses).map
    fun (i, c) => (i, substLits hNoEq (intermediateResultSubst hNoEq d (max 1 i))
      (c.toFOClause hNoEq))

-- The clause formula of the current goal (all literals negated) is a conjunction
-- of negated body atoms. If it holds at assignment s, each body atom is false at s.
-- sld_goal_invariant (already proved) gives us: if M satisfies all clauses in
-- D ++ goals, then clauseToFormula(currentGoal.map neg) holds at all s.

-- Helper: extract the initial goal from a derivation.
-- Under the indexed API, goals is a type parameter, but the specific
-- goal clause used at init is recoverable from the init constructor.
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[blueprint "chap9__theorem_9_5_1"]
def getInitGoal {L : Language} (hNoEq : L.withoutEquality) {D goals : List (FOHornClause L hNoEq)} :
    {cg : LCS.Finset (FOAtom L hNoEq)} →
    (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg → FOHornClause L hNoEq
  | _, .init goal _ => goal
  | _, .step prev _ _ _ _ _ _ _ _ _ _ _ => (getInitGoal (hNoEq := hNoEq)) prev

-- Helper: initial goal is in goals. Under the indexed API this is
-- automatic from the `hGoal` field carried by the .init constructor.
-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem getInitGoal_mem_goals {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq))
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (d : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg) :
    (getInitGoal (hNoEq := hNoEq)) d ∈ goals := by
-- BEGIN PROOF
  induction d with
  | init goal hGoal => exact hGoal
  | step _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

/-- Lemma 9.5.3: If an SLD-refutation R exists for the clause set
    D ∪ goals, then the substituted clause set
    {θ_1(N_0), θ_1(C_1), ..., θ_p(C_p)} is unsatisfiable. This
    captures the textbook claim that the sequence of substituted
    clauses gathered along the refutation is jointly unsatisfiable
    at the identity substitution τ = Term.var. -/
@[blueprint "chap9__lemma_9_5_3" (main := true)]
theorem sldRefutation_unsatisfiable {L : Language} (hNoEq : L.withoutEquality) (A : FormulaN L)
    (D : List (FOHornClause L hNoEq))
    (goals : List (FOHornClause L hNoEq))
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (R : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg)
    (hGoalType : ∀ g ∈ goals, ∃ body, g = (FOHornClause.goal (hNoEq := hNoEq)) body)
    (hRef : (R.isRefutation (hNoEq := hNoEq))) :
    (FOClauseSet.isUnsatisfiable (hNoEq := hNoEq))
      (fun c => c ∈ (substitutedClauseSet (hNoEq := hNoEq)) R) 

-- ===================================================================
-- Theorem 9.5.1: Correctness of SLD-resolution
-- ===================================================================

-- Converse of unsat_from_pw_false: unsatisfiability implies pointwise
-- failure. If S is unsatisfiable, no structure can satisfy all clause
-- formulas at all assignments simultaneously.









/-- Theorem 9.5.1: every positive-length refutation from the Horn
    translation of the same P ∧ ¬G yields the disjunction of complemented
    query occurrences over the original universally satisfied P. Arbitrary
    P is represented by a set; D and goals are finite input witnesses in
    its full translation (SQ30). Empty extraction denotes false (SQ38). -/
@[attach_debt, blueprint "chap9__theorem_9_5_1" (main := true)]
theorem sldResolution_correct {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) (lp : LogicProgram L hNoEq)
    (D goals : List (FOHornClause L hNoEq))
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (R : FOSLDDerivation hNoEq (fun c => c ∈ D) goals cg)
    (hInput : ∀ c ∈ D ++ goals, c ∈ queryHornTranslation lp)
    (hGoalType : ∀ g ∈ goals, ∃ body, g = FOHornClause.goal (hNoEq := hNoEq) body)
    (hPositive : 0 < FOSLDDerivation.length hNoEq R) (hRef : R.isRefutation hNoEq) :
    ∀ M : Structure L, hornProgramModels lp.prog M → ∀ s : Assignment M,
      ∃ pair ∈ negativeClauseSubsequence hNoEq R (lp.qry.map AntiHornClause.negatedClause),
        ¬ formulaEvalN M (clauseToFormula hNoEq Afalsum pair.2) s

-- ===================================================================
-- Theorem 9.5.1 (corollary): Single-atom query answer entailment
-- ===================================================================

/-- Theorem 9.5.1 (companion): `resultSubstitution` coincides with
    `intermediateResultSubst hNoEq R 1`. Both definitions accumulate the
    per-step MGU compositions `(ρ_i ∘ σ_i)` from innermost to outermost,
    so at index 1 (the innermost step) they produce the same substitution.
    For `init`, both are `Term.var`. -/
@[blueprint "chap9__theorem_9_5_1"]
theorem resultSubstitution_eq_intermediate_one {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)}
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (R : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg) :
    (R.resultSubstitution (hNoEq := hNoEq)) = (intermediateResultSubst (hNoEq := hNoEq)) R 1 

/-- Theorem 9.5.1 (companion): both `getInitGoal` variants (top-level
    and the one inside `substitutedClauseSet`'s where-block) agree on
    every derivation. -/
@[blueprint "chap9__theorem_9_5_1"]
theorem substitutedClauseSet_getInitGoal_eq_top {L : Language} (hNoEq : L.withoutEquality)
    {D goals : List (FOHornClause L hNoEq)}
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (R : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg) :
    (substitutedClauseSet.getInitGoal (hNoEq := hNoEq)) R = (getInitGoal (hNoEq := hNoEq)) R 

/-- Theorem 9.5.1 (corollary, single-atom query case): If `R` is an
    SLD-refutation of `P ∪ {?- A}` whose `init` constructor used the
    identity substitution `sigmaInit = Term.var` (the textbook's
    convention B for single-atom queries), then for every structure
    `M` validating every clause of the program `P` pointwise, the
    query atom `A` substituted by the refutation's result substitution
    `σ = R.resultSubstitution` is satisfied at every assignment.

    This is the textbook's boxed paragraph after Thm 9.5.1 (the
    "Corollary" specialising the general subsequence form to
    single-atom queries): `⊨ P ⊃ A[σ]`. The proof is by
    contradiction using Lem 9.5.3 (`sldRefutation_unsatisfiable`)
    and the pointwise invariant (`sldDerivation_substituted_invariant_pw`):
    assuming `¬ A[σ]` at some `(M, s)`, every clause of the
    substituted clause set is satisfied at `(M, s)` — the initial
    goal entry via the contradiction hypothesis (after
    `resultSubstitution_eq_intermediate_one` + the `sigmaInit = Term.var`
    hypothesis collapse the substitution chain), step entries via
    `substLits_preserves_validity` on `P`-clauses — contradicting
    the empty-goal conclusion of the invariant. -/
@[blueprint "chap9__theorem_9_5_1" (main := true)]
theorem sldAnswer_entails {L : Language} (hNoEq : L.withoutEquality) (Afalsum : FormulaN L)
    (P : List (FOHornClause L hNoEq)) (queryAtom : FOAtom L hNoEq)
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (R : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ P) [(FOHornClause.goal (hNoEq := hNoEq)) (LCS.Finset.singleton queryAtom)] cg)
    (hRef : (R.isRefutation (hNoEq := hNoEq)))
    (hInitVar : substitutedClauseSet.getInitSigma hNoEq R = Term.var) :
    ∀ (M : Structure L),
      (∀ c ∈ P, ∀ s : Assignment M,
        formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) Afalsum (FOHornClause.toFOClause hNoEq c)) s) →
      ∀ (s : Assignment M),
        formulaEvalN M
          (formulaSubstAll queryAtom.toFormula (R.resultSubstitution (hNoEq := hNoEq))) s 

/-- Logical computation in PROLOG is a successful finite run of its main
    procedure, SLD-resolution. The derivation field checks every actual SLD
    transition and ends at the empty goal; finite input witnesses belong to
    the full Horn translation of the same program and query (SQ01, SQ30).
    This logical view supplies the refutation component of the correctness
    argument; the source's qualitative proof-effort comparison is OD-9-10. -/
@[blueprint "chap9__theorem_9_5_1"]
structure LogicalComputation {L : Language} (hNoEq : L.withoutEquality)
    (lp : LogicProgram L hNoEq) where
  prolog : LogicProgram.isPROLOG hNoEq lp
  inputs : List (FOHornClause L hNoEq)
  goals : List (FOHornClause L hNoEq)
  sameInput : ∀ c ∈ inputs ++ goals, c ∈ queryHornTranslation lp
  negativeGoals : ∀ g ∈ goals, ∃ body, g = FOHornClause.goal (hNoEq := hNoEq) body
  derivation : FOSLDDerivation hNoEq (fun c => c ∈ inputs) goals ∅
  positiveSteps : 0 < FOSLDDerivation.length hNoEq derivation

end LCS.SLD.LogicProgramming.Correctness
end
