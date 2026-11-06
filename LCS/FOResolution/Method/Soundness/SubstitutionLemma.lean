import LCS.Item
import LCS.Util
import LCS.FOResolution.Method
import LCS.FirstOrder.SemanticsN.Substitution
import LCS.FOResolution.Method.Soundness.ClauseSemantics
import Attach
import LCS.FOResolution.Method.Soundness.SubstitutionLemma.ProofsStamp

section
namespace LCS.FOResolution.Method.Soundness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method

-- ===================================================================
-- Helper: substitution-evaluation lemma for termSubstAll
-- ===================================================================

-- retained: used by LCS.FOResolution.Method.Soundness.ResolventValidity, LCS.SLD.LogicProgramming.Correctness.Correctness
/-- Evaluating a term after applying substitution sigma is the same as
    evaluating the term under a modified assignment that first evaluates
    sigma's images. This is the key semantic lemma connecting syntactic
    substitution to semantic evaluation. -/
theorem termSubstAll_eval {L : Language}
    (M : Structure L) (s : Assignment M) (sigma : Nat → Term L) :
    ∀ (t : Term L),
      termEval M s (termSubstAll t sigma) =
      termEval M (fun x => termEval M s (sigma x)) t := by
-- BEGIN PROOF
  intro t
  induction t with
  | var x => simp [termSubstAll, termEval]
  | const c => simp [termSubstAll, termEval]
  | func f ts ih =>
    simp [termSubstAll, termEval]
    congr 1; funext i; exact ih i

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.SLD.FirstOrder.Soundness
/-- For a predicate formula, evaluating after substitution equals
    evaluating under the substituted assignment. -/
theorem substFormula_predN_eval {L : Language}
    (M : Structure L) (s : Assignment M) (sigma : Nat → Term L)
    (P : L.predSymbols) (args : Fin (L.predArity P) → Term L) :
    formulaEvalN M (substLit.substFormula sigma (.predN P args)) s ↔
    formulaEvalN M (.predN P args) (fun x => termEval M s (sigma x)) := by
-- BEGIN PROOF
  simp only [substLit.substFormula, formulaEvalN]
  have heq : (fun i => termEval M s (termSubstAll (args i) sigma)) =
             (fun i => termEval M (fun x => termEval M s (sigma x)) (args i)) :=
    funext fun i => termSubstAll_eval M s sigma (args i)
  rw [heq]

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.SLD.FirstOrder.Soundness
/-- For an equality formula, evaluating after substitution equals
    evaluating under the substituted assignment. -/
theorem substFormula_eq_eval {L : Language}
    (M : Structure L) (s : Assignment M) (hL : L.hasEquality = true)
    (sigma : Nat → Term L) (t1 t2 : Term L) :
    formulaEvalN M (substLit.substFormula sigma (.eq_ hL t1 t2)) s ↔
    formulaEvalN M (.eq_ hL t1 t2) (fun x => termEval M s (sigma x)) := by
-- BEGIN PROOF
  simp only [substLit.substFormula, formulaEvalN]
  rw [termSubstAll_eval, termSubstAll_eval]

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.SLD.FirstOrder.Soundness
/-- A substitution sigma is fresh for a formula A when for every variable
    i that is bound in A, sigma maps i to var i and no sigma(y) mentions i.
    This ensures substFormula sigma A does not capture bound variables.
    For quantifier-free formulae (including all clause-form formulae used
    in resolution), this predicate is trivially True. -/
def SubstFreshFor {L : Language} (sigma : Nat → Term L) : FormulaN L → Prop
  | .predN _ _ => True
  | .eq_ _ _ _ => True
  | .neg A => SubstFreshFor sigma A
  | .conj A B => SubstFreshFor sigma A ∧ SubstFreshFor sigma B
  | .disj A B => SubstFreshFor sigma A ∧ SubstFreshFor sigma B
  | .impl A B => SubstFreshFor sigma A ∧ SubstFreshFor sigma B
  | .all i A => sigma i = .var i ∧ (∀ y, ¬ termFV (sigma y) i) ∧ SubstFreshFor sigma A
  | .ex i A => sigma i = .var i ∧ (∀ y, ¬ termFV (sigma y) i) ∧ SubstFreshFor sigma A

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.SLD.FirstOrder.Soundness
/-- A quantifier-free formula satisfies SubstFreshFor for any
    substitution, since there are no bound variables to capture. -/
theorem isQF_implies_substFreshFor {L : Language} (sigma : Nat → Term L)
    (A : FormulaN L) (h : isQuantifierFree A) :
    SubstFreshFor sigma A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => trivial
  | eq_ _ _ _ => trivial
  | neg A ih => exact ih h
  | conj A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | disj A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | impl A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | all _ _ => exact absurd h id
  | ex _ _ => exact absurd h id

/-- Lemma 8.5.1 (companion): A clause is quantifier-free when every
    literal's formula is. -/
@[blueprint "chap8__lemma_8_5_1"]
def ClauseQF {L : Language} (hNoEq : L.withoutEquality) (C : FOClause L hNoEq) : Prop :=
  ∀ lit, lit ∈ C → isQuantifierFree lit.formula

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.FOResolution.Method.Soundness.ResolventValidity
/-- Every first-order clause is quantifier-free by construction. -/
theorem clauseQF {L : Language} (hNoEq : L.withoutEquality) (C : FOClause L hNoEq) : (ClauseQF (hNoEq := by all_goals exact hNoEq)) C := by
  intro lit hlit
  cases lit <;> rename_i atom <;> cases atom <;>
    simp [FOLiteral.formula, FOLiteralCore.formula, FOAtomCore.toFormula, isQuantifierFree]

-- retained: used by LCS.FOResolution.Method.Soundness.ResolventValidity
/-- substLit preserves the quantifier-free property of a literal's formula. -/
theorem isQF_substLit_formula {L : Language} (hNoEq : L.withoutEquality) (sigma : Nat → Term L)
    (lit : FOLiteral L hNoEq) (h : isQuantifierFree lit.formula) :
    isQuantifierFree ((substLit (hNoEq := by all_goals exact hNoEq)) sigma lit).formula := by
-- BEGIN PROOF
  exact (clauseQF (hNoEq := by all_goals exact hNoEq)) [(substLit (hNoEq := by all_goals exact hNoEq)) sigma lit] _ (by simp)

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.SLD.FirstOrder.Soundness
/-- If variable i is not free in term t, then termEval is unchanged
    when assignment s is updated at i. -/
theorem termEval_assignUpdate_irrelevant {L : Language}
    (M : Structure L) (s : Assignment M) (i : Nat) (a : M.carrier)
    (t : Term L) (h : ¬ termFV t i) :
    termEval M (assignUpdate s i a) t = termEval M s t := by
-- BEGIN PROOF
  induction t with
  | var x =>
    simp [termFV, Set.singleton] at h
    simp [termEval, assignUpdate]
    intro heq; exact absurd heq.symm h
  | const c => simp [termEval]
  | func f ts ih =>
    simp [termEval]; congr 1; funext j
    apply ih j; intro hc; exact h ⟨j, hc⟩

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.SLD.FirstOrder.Soundness
/-- When sigma is fresh for bound variable i (sigma i = var i and no
    sigma(y) mentions i), the substitution-induced assignment commutes
    with assignUpdate at i. -/
theorem substFresh_assignment_eq {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M) (sigma : Nat → Term L)
    (i : Nat) (a : M.carrier)
    (hSigmaI : sigma i = .var i) (hFresh : ∀ y, ¬ termFV (sigma y) i) :
    (fun x => termEval M (assignUpdate s i a) (sigma x)) =
    assignUpdate (fun x => termEval M s (sigma x)) i a := by
-- BEGIN PROOF
  funext x; simp [assignUpdate]
  by_cases hxi : x = i
  · subst hxi; simp [hSigmaI, termEval, assignUpdate]
  · rw [termEval_assignUpdate_irrelevant M s i a (sigma x) (hFresh x)]; simp [hxi]

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.SLD.FirstOrder.Soundness
/-- General substitution-evaluation lemma for all formulae: evaluating
    substFormula sigma A under assignment s is equivalent to evaluating
    A under the substitution-induced assignment. The hypothesis
    SubstFreshFor sigma A ensures that sigma does not capture any
    bound variable of A. For quantifier-free formulae (including all
    clause-form formulae used in resolution), this hypothesis is
    trivially True. -/
theorem substFormula_eval {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M) (sigma : Nat → Term L)
    (A : FormulaN L) (hFresh : SubstFreshFor sigma A) :
      formulaEvalN M (substLit.substFormula sigma A) s ↔
      formulaEvalN M A (fun x => termEval M s (sigma x)) := by
-- BEGIN PROOF
  induction A generalizing s with
  | predN P args => exact substFormula_predN_eval M s sigma P args
  | eq_ hL t1 t2 => exact substFormula_eq_eval M s hL sigma t1 t2
  | neg A ih =>
    simp only [substLit.substFormula, formulaEvalN]
    exact not_congr (ih s hFresh)
  | conj A B ihA ihB =>
    simp only [substLit.substFormula, formulaEvalN]
    exact and_congr (ihA s hFresh.1) (ihB s hFresh.2)
  | disj A B ihA ihB =>
    simp only [substLit.substFormula, formulaEvalN]
    exact or_congr (ihA s hFresh.1) (ihB s hFresh.2)
  | impl A B ihA ihB =>
    simp only [substLit.substFormula, formulaEvalN]
    exact imp_congr (ihA s hFresh.1) (ihB s hFresh.2)
  | all i A ih =>
    obtain ⟨hSigmaI, hNoCapture, hFreshA⟩ := hFresh
    simp only [substLit.substFormula, formulaEvalN]
    constructor
    · intro h a
      rw [← (substFresh_assignment_eq (hNoEq := by all_goals exact hNoEq)) M s sigma i a hSigmaI hNoCapture]
      exact (ih (assignUpdate s i a) hFreshA).mp (h a)
    · intro h a
      apply (ih (assignUpdate s i a) hFreshA).mpr
      rw [(substFresh_assignment_eq (hNoEq := by all_goals exact hNoEq)) M s sigma i a hSigmaI hNoCapture]
      exact h a
  | ex i A ih =>
    obtain ⟨hSigmaI, hNoCapture, hFreshA⟩ := hFresh
    simp only [substLit.substFormula, formulaEvalN]
    constructor
    · intro ⟨a, ha⟩
      exact ⟨a, by
        rw [← (substFresh_assignment_eq (hNoEq := by all_goals exact hNoEq)) M s sigma i a hSigmaI hNoCapture]
        exact (ih (assignUpdate s i a) hFreshA).mp ha⟩
    · intro ⟨a, ha⟩
      exact ⟨a, by
        apply (ih (assignUpdate s i a) hFreshA).mpr
        rw [(substFresh_assignment_eq (hNoEq := by all_goals exact hNoEq)) M s sigma i a hSigmaI hNoCapture]
        exact ha⟩

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.FOResolution.Method.Soundness.ResolventValidity
/-- For a literal (positive or negative), evaluating the substituted
    literal under assignment s is equivalent to evaluating the original
    literal under the substitution-induced assignment. Requires that
    the literal's formula is quantifier-free (which ensures that
    substFormula does not capture bound variables). -/
theorem substLit_eval {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M) (sigma : Nat → Term L)
    (lit : FOLiteral L hNoEq)
    (hQF : isQuantifierFree lit.formula) :
    formulaEvalN M ((clauseToFormula.litToFormula (hNoEq := hNoEq)) ((substLit (hNoEq := by all_goals exact hNoEq)) sigma lit)) s ↔
    formulaEvalN M ((clauseToFormula.litToFormula (hNoEq := hNoEq)) lit)
      (fun x => termEval M s (sigma x)) := by
-- BEGIN PROOF
  cases lit with
  | pos B =>
    simp only [substLit, clauseToFormula.litToFormula]
    rw [(atomSubst_toFormula (hNoEq := by all_goals exact hNoEq))]
    exact (substFormula_eval (hNoEq := by all_goals exact hNoEq)) M s sigma B.toFormula
      (isQF_implies_substFreshFor sigma B.toFormula hQF)
  | neg B =>
    simp only [substLit, clauseToFormula.litToFormula, formulaEvalN]
    rw [(atomSubst_toFormula (hNoEq := by all_goals exact hNoEq))]
    exact not_congr ((substFormula_eval (hNoEq := by all_goals exact hNoEq)) M s sigma B.toFormula
      (isQF_implies_substFreshFor sigma B.toFormula hQF))

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions, LCS.SLD.LogicProgramming.Correctness.Correctness
theorem substLits_clauseToFormula_eval {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M) (A : FormulaN L)
    (sigma : Nat → Term L)
    (C : FOClause L hNoEq)
    (hQF : (ClauseQF (hNoEq := by all_goals exact hNoEq)) C) :
    formulaEvalN M ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A ((substLits (hNoEq := by all_goals exact hNoEq)) sigma C)) s ↔
    formulaEvalN M ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C) (fun x => termEval M s (sigma x)) := by
-- BEGIN PROOF
  constructor
  · intro h
    obtain ⟨lit', hmem', heval'⟩ := (clauseToFormula_exists_of_true (hNoEq := by all_goals exact hNoEq)) M s A _ h
    simp only [substLits, List.mem_map] at hmem'
    obtain ⟨lit, hmem, rfl⟩ := hmem'
    apply (clauseToFormula_true_of_mem (hNoEq := by all_goals exact hNoEq)) M _ A C lit hmem
    exact ((substLit_eval (hNoEq := by all_goals exact hNoEq)) M s sigma lit (hQF lit hmem)).mp heval'
  · intro h
    obtain ⟨lit, hmem, heval⟩ := (clauseToFormula_exists_of_true (hNoEq := by all_goals exact hNoEq)) M _ A _ h
    have hmem' : (substLit (hNoEq := by all_goals exact hNoEq)) sigma lit ∈ (substLits (hNoEq := by all_goals exact hNoEq)) sigma C := by
      simp only [substLits]; exact List.mem_map_of_mem hmem
    apply (clauseToFormula_true_of_mem (hNoEq := by all_goals exact hNoEq)) M s A _ ((substLit (hNoEq := by all_goals exact hNoEq)) sigma lit) hmem'
    exact ((substLit_eval (hNoEq := by all_goals exact hNoEq)) M s sigma lit (hQF lit hmem)).mpr heval

end LCS.FOResolution.Method.Soundness
end
