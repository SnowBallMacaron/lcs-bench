import LCS.Item
import LCS.Util
import LCS.SLD.Propositional
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import LCS.FOResolution.Method
import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.Method.Completeness
import LCS.Herbrand.SHGTheorem.Main
import LCS.SLD.FirstOrder.HornClauses
import LCS.SLD.FirstOrder.SLDRefutations
import Attach
import LCS.SLD.FirstOrder.Soundness.ProofsStamp

/-! # Soundness of SLD-resolution (Lemma 9.4.1)

Section 9.4.1: a set of Horn clauses with an SLD-refutation is unsatisfiable. -/

noncomputable section
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.Completeness

-- ===================================================================
-- Lemma 9.4.1 (key invariant): SLD goal clause preservation
-- ===================================================================

-- ATTACH-KEEP: existing oversized helper stays with its front size allowance
-- ATTACH-BLOCKER: existing oversized helper stays with its front size allowance
/-- Key invariant for SLD-resolution soundness: if the SLD-derivation
    is indexed by `currentGoalVal` against D and goals, and a structure
    M satisfies the universal closures of all clause translations in
    D ∪ goals, then for every assignment s, the clause formula of the
    current goal (translated as negative literals) holds in M at s.
    This means: for any assignment s, at least one current goal atom
    evaluates to False. When the derivation is a refutation (current
    goal is empty), the clause formula is falsum, giving a
    contradiction. Requires all Horn clauses to have quantifier-free
    atoms (always true for SLD clause-form). Well-formedness is now
    automatic from the indexed inductive's constructor fields, and
    quantifier-freeness is automatic from the structural atom carrier. -/
theorem sld_goal_invariant
    {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (D : Set (FOHornClause L hNoEq))
    (goals : List (FOHornClause L hNoEq))
    {currentGoalVal : LCS.Finset (FOAtom L hNoEq)}
    (d : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) D goals currentGoalVal)
    (hGoalType : ∀ g ∈ goals, ∃ body, g = FOHornClause.goal body hNoEq)
    (M : Structure L)
    (hSat : ∀ C, (∃ h, (h ∈ D ∨ h ∈ goals) ∧ (h.toFOClause (hNoEq := by all_goals exact hNoEq)) = C) →
      ∀ fvs, (∀ n, (FOClause.freeVars (hNoEq := by all_goals exact hNoEq)) C n → n ∈ fvs) →
        (∀ s : Assignment M, formulaEvalN M ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) Afalsum C fvs) s)) :
    ∀ s : Assignment M,
      formulaEvalN M
        ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) Afalsum (currentGoalVal.toList.map FOLiteralCore.neg)) s := by
  -- REPAIR(T9-77a): proof pending — migration to extensional bodies / renamed-head steps
  sorry

-- ===================================================================
-- Lemma 9.4.1: Soundness of first-order SLD-resolution
-- ===================================================================

/-- Lemma 9.4.1: if an arbitrary program and finite negative-goal family
    have an SLD-refutation, their same original union is unsatisfiable
    (SQ17). The derivation retains its local renaming and MGU certificates. -/
@[blueprint "chap9__lemma_9_4_1" (main := true)]
theorem foSLDResolution_sound
    {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (D : Set (FOHornClause L hNoEq))
    (goals : List (FOHornClause L hNoEq))
    {currentGoalVal : LCS.Finset (FOAtom L hNoEq)}
    (d : (FOSLDDerivation (hNoEq := by all_goals exact hNoEq)) D goals currentGoalVal)
    (hGoalType : ∀ g ∈ goals, ∃ body, g = FOHornClause.goal body hNoEq)
    (hRef : (d.isRefutation (hNoEq := by all_goals exact hNoEq))) :
    FOClauseSet.isUnsatisfiable hNoEq
      (fun C => ∃ h, (h ∈ D ∨ h ∈ goals) ∧ h.toFOClause = C)

end LCS.SLD.FirstOrder
end
