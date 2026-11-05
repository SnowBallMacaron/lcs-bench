import LCS.SLD.FirstOrder.HornClauses

section

namespace LCS.SLD.FirstOrder

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SemanticsN

open LCS.FOResolution.ClauseForm

open LCS.FOResolution.Unification

open LCS.FOResolution.Method

open LCS.FOResolution.Method.Soundness

open LCS.FOResolution.Method.Completeness





helper /-- Mapping `formulaSubstAll · Term.var` over a list of formulas is
    the identity. This is the list-level version of `formulaSubstAll_id`
    and matches the shape of the body-equality witness carried by
    `FOSLDDerivation.init` when `sigmaInit = Term.var`. -/
theorem map_formulaSubstAll_id {L : Language}
    (xs : List (FormulaN L)) :
    xs.map (fun a => formulaSubstAll a Term.var) = xs := by
-- BEGIN PROOF
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map]
    rw [formulaSubstAll_id x, ih]

helper /-- Identity map equality: `xs = xs.map (fun a => formulaSubstAll a Term.var)`.
    Used to discharge the `hBody` obligation in `FOSLDDerivation.init`
    call sites that want to recover the literal-body case
    (`sigmaInit = Term.var`). -/
theorem eq_map_formulaSubstAll_id {L : Language}
    (xs : List (FormulaN L)) :
    xs = xs.map (fun a => formulaSubstAll a Term.var) :=
  (map_formulaSubstAll_id xs).symm







end LCS.SLD.FirstOrder

end

section

namespace LCS.SLD.FirstOrder

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SemanticsN

open LCS.FOResolution.ClauseForm

open LCS.FOResolution.Unification

open LCS.FOResolution.Method

open LCS.FOResolution.Method.Soundness

open LCS.FOResolution.Method.Completeness

namespace FOHornClause

proof_of ruleTranslation := by
  -- BEGIN PROOF
    rfl


proof_of factTranslation := by
  -- BEGIN PROOF
    rfl


proof_of goalTranslation := by
  -- BEGIN PROOF
    rfl






helper theorem FOHornClause.bodyAtomsQF {L : Language} (hNoEq : L.withoutEquality)  (c : FOHornClause L hNoEq) :
    ∀ a ∈ (c.bodyAtoms (hNoEq := by all_goals exact hNoEq)), isQuantifierFree a := by
-- BEGIN PROOF
  cases c with
  | rule _ body | goal body =>
      intro a ha
      simp only [bodyAtoms, bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty, List.mem_map] at ha
      obtain ⟨atom, _, rfl⟩ := ha
      exact (atomToFormulaQF (hNoEq := by all_goals exact hNoEq)) atom
  | fact _ =>
      intro a ha
      simp [FOHornClause.bodyAtoms, bodyFOAtoms, FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body, finset_toList_empty] at ha

helper theorem FOHornClause.headAtomQF {L : Language} (hNoEq : L.withoutEquality)  (c : FOHornClause L hNoEq)
    (headA : FormulaN L) (hHead : (c.headAtom (hNoEq := by all_goals exact hNoEq)) = some headA) :
    isQuantifierFree headA := by
-- BEGIN PROOF
  cases c with
  | rule head _ | fact head =>
      simp [FOHornClause.headAtom, headFOAtom, FOHornClauseCore.headFOAtom] at hHead
      subst headA
      exact (atomToFormulaQF (hNoEq := by all_goals exact hNoEq)) head
  | goal _ =>
      simp [FOHornClause.headAtom, headFOAtom, FOHornClauseCore.headFOAtom] at hHead



end FOHornClause

end LCS.SLD.FirstOrder

end

section

namespace LCS.SLD.FirstOrder

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SemanticsN

open LCS.FOResolution.ClauseForm

open LCS.FOResolution.Unification

open LCS.FOResolution.Method

open LCS.FOResolution.Method.Soundness

open LCS.FOResolution.Method.Completeness





end LCS.SLD.FirstOrder

end

section

namespace LCS.SLD.FirstOrder

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SemanticsN

open LCS.FOResolution.ClauseForm

open LCS.FOResolution.Unification

open LCS.FOResolution.Method

open LCS.FOResolution.Method.Soundness

open LCS.FOResolution.Method.Completeness

helper /-- Example 9.4.1 (companion helper): zero is ground. -/
theorem termVars_zeroTm (n : Nat) : ¬ termVars zeroTm n := id



proof_of exAddSigma1_isAtomMGU := by
  refine ⟨exAddPairs1, ?_, exAddSigma1_isPairwiseMGU⟩
  classical
  have hRenamed :
      (mkAdd (Term.var 0) (mkSucc (Term.var 1))
        (mkSucc (Term.var 2))).subst (hNoEq := by all_goals rfl) exAddRho1 =
      mkAdd (Term.var 4) (mkSucc (Term.var 5))
        (mkSucc (Term.var 6)) := by
    simp [formulaSubstAll_mkAdd, termSubstAll, exAddRho1,
      termSubstAll_mkSucc]
  rw [hRenamed]
  exact (atomUnifPairs?_predN_same (hNoEq := by all_goals rfl)) _ _ _

proof_of exAddSigma2_isAtomMGU := by
  refine ⟨exAddPairs2, ?_, exAddSigma2_isPairwiseMGU⟩
  classical
  have hRenamed :
      (mkAdd (Term.var 0) zeroTm (Term.var 0)).subst (hNoEq := by all_goals rfl) exAddRho2 =
      mkAdd (Term.var 7) zeroTm (Term.var 7) := by
    simp [formulaSubstAll_mkAdd, termSubstAll,
      termSubstAll_zeroTm, exAddRho2]
  rw [hRenamed]
  exact (atomUnifPairs?_predN_same (hNoEq := by all_goals rfl)) _ _ _

proof_of exAddRefutation_isRefutation := by
  -- BEGIN PROOF
    show (∅ : LCS.Finset (FOAtom exAddLang rfl)) =
         (∅ : LCS.Finset (FOAtom exAddLang rfl))
    rfl


end LCS.SLD.FirstOrder

end
