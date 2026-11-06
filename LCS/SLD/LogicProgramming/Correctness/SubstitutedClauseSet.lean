import LCS.SLD.LogicProgramming.Queries
import LCS.Item
import LCS.Util
import LCS.SLD.LogicProgramming
import Attach
import LCS.SLD.LogicProgramming.Correctness.SubstitutedClauseSet.ProofsStamp

/-! # Substituted clause sets of an SLD-refutation

Section 9.5.3: the result substitutions θ_i of an SLD-refutation and the set of substituted input clauses used in Lemma 9.5.3, with the substitution and free-variable facts and the one-step semantic invariant along the refutation. -/

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
-- Lemma 9.5.3 (required defs): Intermediate result substitutions
-- ===================================================================

/-- Lemma 9.5.3 (required): Computes the intermediate result
    substitution theta_i for step i of the SLD-refutation.
    theta_p = rho_p circ sigma_p (base case at the last step).
    theta_i = (rho_i circ sigma_i) circ theta_{i+1} for i < p
    (recursive case). The index i counts from 1 (innermost step = 1).
    Uses an accumulator that processes steps from outside-in: at each
    step node j, thetaHere = (rho_j circ sigma_j) circ acc represents
    theta_j. Under Gallier convention B, (rho_j ∘ sigma_j) ∘ acc applied
    at x is acc(sigma_j(rho_j(x))) — order: rho_j, sigma_j, acc. In Lean
    standard-math SubstitutionCore.substCompose, that is `SubstitutionCore.substCompose acc (SubstitutionCore.substCompose sigma rho)`. -/
@[blueprint "chap9__lemma_9_5_3"]
def intermediateResultSubst {L : Language} (hNoEq : L.withoutEquality) {D goals : List (FOHornClause L hNoEq)}
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (d : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg) (i : Nat) : (Nat → Term L) :=
  go d i Term.var
where
  go :
      {cg : LCS.Finset (FOAtom L hNoEq)} →
      (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg → Nat → (Nat → Term L) → (Nat → Term L)
    | _, .init _ _, _, _ => Term.var
    | _, .step prev _ _ _ _ _ _ _ rho sigma _ _, i, acc =>
      let stepIdx := (FOSLDDerivation.length hNoEq prev) + 1
      let thetaHere := SubstitutionCore.substCompose acc (SubstitutionCore.substCompose sigma rho)
      if i = stepIdx then thetaHere
      else go prev i thetaHere

/-- Lemma 9.5.3 (required): Constructs the set
    {theta_1(N_0), theta_1(C_1), ..., theta_p(C_p)} of quantifier-free
    clauses obtained by applying intermediate result substitutions to
    the initial goal and each input clause used in the refutation.
    Returns a list of FOClauses. Each input clause C_i at step i gets
    theta_i applied; the initial goal N_0 gets theta_1. -/
@[blueprint "chap9__lemma_9_5_3"]
noncomputable def substitutedClauseSet {L : Language} (hNoEq : L.withoutEquality) {D goals : List (FOHornClause L hNoEq)} :
    {cg : LCS.Finset (FOAtom L hNoEq)} →
    (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg → List (FOClause L hNoEq)
  | _, .init goal _ =>
    let sigmaInit : Nat → Term L := Term.var
    -- The init constructor starts at the original goal, with identity
    -- substitution; retain the clause-substitution recurrence.
    [(substLits (hNoEq := hNoEq)) sigmaInit (FOHornClause.toFOClause hNoEq goal)]
  | _, d@(.step ..) =>
    let theta := (intermediateResultSubst (hNoEq := hNoEq)) d
    -- Apply theta_1 to the initial goal's clause.
    let initGoal := getInitGoal d
    let initSigma := getInitSigma d
    let goalClause :=
      (substLits (hNoEq := hNoEq)) (theta 1) ((substLits (hNoEq := hNoEq)) initSigma (FOHornClause.toFOClause hNoEq initGoal))
    -- theta_i(C_i) for each input clause C_i at step i
    goalClause :: collectInputClauses d theta
where
  getInitGoal :
      {cg : LCS.Finset (FOAtom L hNoEq)} →
      (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg → FOHornClause L hNoEq
    | _, .init goal _ => goal
    | _, .step prev _ _ _ _ _ _ _ _ _ _ _ => getInitGoal prev
  getInitSigma :
      {cg : LCS.Finset (FOAtom L hNoEq)} →
      (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg → (Nat → Term L)
    | _, .init _ _ => Term.var
    | _, .step prev _ _ _ _ _ _ _ _ _ _ _ => getInitSigma prev
  collectInputClauses :
      {cg : LCS.Finset (FOAtom L hNoEq)} →
      (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg → (Nat → Nat → Term L) → List (FOClause L hNoEq)
    | _, .init _ _, _ => []
    | _, .step prev clause _ _ _ _ _ _ _ _ _ _, theta =>
      let stepIdx := (FOSLDDerivation.length hNoEq prev) + 1
      -- Recurse to collect C_1,...,C_{i-1}, then append theta_i(C_i)
      collectInputClauses prev theta ++
        [(substLits (hNoEq := hNoEq)) (theta stepIdx) (FOHornClause.toFOClause hNoEq clause)]

-- ===================================================================
-- Lemma 9.5.3: Unsatisfiability of substituted clause set
-- ===================================================================

-- Helper: the empty clause is in any set that contains it, so the set
-- is unsatisfiable by universalClosure_nil_validIn_false.


-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem substLits_preserves_validity {L : Language} (hNoEq : L.withoutEquality) (A : FormulaN L)
    (M : Structure L) (C : FOClause L hNoEq) (sigma : Nat → Term L)
    (hQF : (ClauseQF (hNoEq := hNoEq)) C)
    (h : ∀ s : Assignment M, formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A C) s) :
    ∀ s : Assignment M, formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A ((substLits (hNoEq := hNoEq)) sigma C)) s := by
  intro s
  exact ((substLits_clauseToFormula_eval (A := A) (hNoEq := hNoEq)) M s sigma C hQF).mpr (h _)

-- Bridge: if for all M, pointwise satisfaction of all clause formulas in
-- S implies False, then S is FOClauseSet.isUnsatisfiable.
-- Uses resolvent_subtree_pw to strip universal closures to pointwise satisfaction.
-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem unsat_from_pw_false {L : Language} (hNoEq : L.withoutEquality) (A : FormulaN L)
    (S : FOClause L hNoEq → Prop)
    (h : ∀ (M : Structure L),
      (∀ C, S C → ∀ (s : Assignment M), formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A C) s) →
      False) :
    (FOClauseSet.isUnsatisfiable (hNoEq := hNoEq)) S := by
-- BEGIN PROOF
  intro ⟨M, hSat⟩
  exact h M (fun C hC => (resolvent_subtree_pw (hNoEq := hNoEq)) M A C
    (fun fvs _ => FOClause.universalClosure_of_validIn hNoEq M C (hSat C hC) A fvs))

-- Helper: collect all input clauses from the derivation (unsubstituted)


-- Helper: all collected clauses are in D. Under the indexed API this
-- is automatic from the `hClause` field carried by the .step
-- constructor.


-- Substitution composition helpers for the Lemma 9.5.3 proof
-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem termSubstAll_id_subst {L : Language} (t : Term L) :
    termSubstAll t Term.var = t := by
-- BEGIN PROOF
  induction t with
  | var n => exact termSubstAll_var n Term.var
  | const c => simp [termSubstAll]
  | func f args ih => simp [termSubstAll]; funext i; exact ih i

-- retained: used by LCS.FOResolution.Unification.Part1, LCS.FOResolution.Unification.Part2, LCS.SLD.LogicProgramming.Correctness.Correctness
theorem substCompose_assoc {L : Language} (a b c : Nat → Term L) :
    SubstitutionCore.substCompose (SubstitutionCore.substCompose a b) c = SubstitutionCore.substCompose a (SubstitutionCore.substCompose b c) := by
-- BEGIN PROOF
  funext x; simp [SubstitutionCore.substCompose, SubstitutionCore.termSubstAll_compose]

-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem substCompose_id_left_subst {L : Language} (sigma : Nat → Term L) :
    SubstitutionCore.substCompose Term.var sigma = sigma := by
-- BEGIN PROOF
  funext x; simp [SubstitutionCore.substCompose]; exact termSubstAll_id_subst (sigma x)

-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem substCompose_id_right_subst {L : Language} (sigma : Nat → Term L) :
    SubstitutionCore.substCompose sigma Term.var = sigma := by
-- BEGIN PROOF
  funext x; simp [SubstitutionCore.substCompose, termSubstAll]

-- intermediateResultSubst.go factorization (accumulator-outer form).
-- Under the convention-B composition order, the acc threads in as the
-- OUTER substitution. If we start the fold at (SubstitutionCore.substCompose outer acc)
-- rather than acc, the result factors as (SubstitutionCore.substCompose outer (go d i acc)).
-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem go_factor {L : Language} (hNoEq : L.withoutEquality) {D goals : List (FOHornClause L hNoEq)}
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (d : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg) (i : Nat)
    (hi : 1 ≤ i ∧ i ≤ (FOSLDDerivation.length hNoEq d)) :
    ∀ (outer acc : Nat → Term L),
    intermediateResultSubst.go hNoEq d i (SubstitutionCore.substCompose outer acc) =
    SubstitutionCore.substCompose outer (intermediateResultSubst.go hNoEq d i acc) := by
-- BEGIN PROOF
  induction d with
  | init _ _ => simp [FOSLDDerivation.length] at hi; omega
  | @step prevGoal prev _ _ _ _ _ _ _ rho sigma _ _ ih =>
    simp only [FOSLDDerivation.length] at hi; intro outer acc
    simp only [intermediateResultSubst.go]
    by_cases heq : i = (FOSLDDerivation.length hNoEq prev) + 1
    · simp [heq]; rw [substCompose_assoc]
    · simp [heq]
      have hi_prev : 1 ≤ i ∧ i ≤ (FOSLDDerivation.length hNoEq prev) := by omega
      rw [substCompose_assoc outer acc (SubstitutionCore.substCompose sigma rho)]
      exact ih hi_prev outer (SubstitutionCore.substCompose acc (SubstitutionCore.substCompose sigma rho))

-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem go_factor_from_id {L : Language} (hNoEq : L.withoutEquality) {D goals : List (FOHornClause L hNoEq)}
    {cg : LCS.Finset (FOAtom L hNoEq)}
    (d : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg) (i : Nat)
    (hi : 1 ≤ i ∧ i ≤ (FOSLDDerivation.length hNoEq d)) (outer : Nat → Term L) :
    intermediateResultSubst.go hNoEq d i outer =
    SubstitutionCore.substCompose outer (intermediateResultSubst.go hNoEq d i Term.var) := by
-- BEGIN PROOF
  have h := (go_factor (hNoEq := hNoEq)) d i hi outer Term.var
  rw [substCompose_id_right_subst] at h; exact h

-- Every structural Horn clause translates to a quantifier-free FO clause.
-- retained: used by LCS.SLD.LogicProgramming.Correctness.Correctness
theorem toFOClause_QF {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) : (ClauseQF (hNoEq := hNoEq)) (FOHornClause.toFOClause hNoEq c) := by
-- BEGIN PROOF
  intro lit _
  cases lit with
  | pos atom | neg atom =>
      simpa only [FOLiteral.formula, FOLiteralCore.formula] using (FOHornClause.atomToFormulaQF (hNoEq := hNoEq)) atom

/-- Pointwise-at-fixed-s variant of `sldDerivation_substituted_invariant`.
    Takes a single-assignment satisfaction premise and yields a
    single-assignment satisfaction conclusion. Proof mirrors the original
    with `s` threaded as a parameter rather than universally quantified.
    The pointwise form is what Thm 9.5.1 needs: at each s, we assume
    (for contradiction) all negSubseq pairs hold at s, and derive
    false-at-s via the invariant's conclusion on the empty current goal. -/
theorem sldDerivation_substituted_invariant_pw {L : Language} (hNoEq : L.withoutEquality) (A : FormulaN L)
    (D goals : List (FOHornClause L hNoEq))
    (hGoalType : ∀ g ∈ goals, ∃ body, g = (FOHornClause.goal (hNoEq := hNoEq)) body)
    (M : Structure L) :
    ∀ {cg : LCS.Finset (FOAtom L hNoEq)} (R : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg),
      ∀ (τ : Nat → Term L) (s : Assignment M),
      (∀ C ∈ (substitutedClauseSet (hNoEq := hNoEq)) R,
        formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A ((substLits (hNoEq := hNoEq)) τ C)) s) →
      formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A
            ((substLits (hNoEq := hNoEq)) τ (cg.toList.map FOLiteralCore.neg))) s := by
  -- REPAIR(T9-77a): proof pending — migration to extensional bodies/renamed-head steps
  sorry

/-- Lemma 9.5.3: Given a Horn set P and SLD-refutation R, the
    quantifier-free substituted set
    {theta_1(N_0), theta_1(C_1),...,theta_p(C_p)} is unsatisfiable.
    Under the indexed FOSLDDerivation API, well-formedness is
    automatic from the constructor fields. -/
theorem sldDerivation_substituted_invariant {L : Language} (hNoEq : L.withoutEquality) (A : FormulaN L)
    (D goals : List (FOHornClause L hNoEq))
    (hGoalType : ∀ g ∈ goals, ∃ body, g = (FOHornClause.goal (hNoEq := hNoEq)) body)
    (M : Structure L) :
    ∀ {cg : LCS.Finset (FOAtom L hNoEq)} (R : (FOSLDDerivation (hNoEq := hNoEq)) (fun c => c ∈ D) goals cg),
      ∀ (τ : Nat → Term L),
      (∀ C ∈ (substitutedClauseSet (hNoEq := hNoEq)) R, ∀ s,
        formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A ((substLits (hNoEq := hNoEq)) τ C)) s) →
      ∀ s, formulaEvalN M ((clauseToFormula (hNoEq := hNoEq)) A
            ((substLits (hNoEq := hNoEq)) τ (cg.toList.map FOLiteralCore.neg))) s := by
-- BEGIN PROOF
  intro cg R τ hSat s
  exact (sldDerivation_substituted_invariant_pw (hNoEq := hNoEq)) A D goals hGoalType M R
    τ s (fun C hC => hSat C hC s)

end LCS.SLD.LogicProgramming.Correctness
end
