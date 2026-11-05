import LCS.Herbrand.SHGTheorem.Part1

section

namespace LCS.Herbrand.SHGTheorem

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.Herbrand.NNFHauptsatz

open LCS.Herbrand.HerbrandTheorem

proof_of shgMotivPreparation := by
  refine ⟨rfl, by trivial, ?_, ?_⟩
  · simp [shgMotivNNFNeg, shgMotivLang,
      LCS.FirstOrder.Semantics.Subformulae.isRectified,
      LCS.FirstOrder.Semantics.Subformulae.boundVarsFresh,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
      formulaFVN, formulaBVN, termFV, Membership.mem,
      Set.iUnion, Set.union, Set.diff, Set.singleton, Set.empty,
      shgMotivVec1, shgMotivVec2, Fin.exists_fin_succ,
      Fin.forall_fin_succ] <;> (intros; omega)
  · change formulaFVN shgMotivNNFNeg = ∅
    funext x
    apply propext
    simp [shgMotivNNFNeg, shgMotivLang, formulaFVN, termFV,
      Membership.mem, Set.iUnion, Set.union, Set.diff, Set.singleton, Set.empty,
      shgMotivVec1, shgMotivVec2, Fin.exists_fin_succ,
      Fin.forall_fin_succ] <;> omega


helper /-- The generic preview applies to a supplied prepared sentence, not to
an unidentified raw formula. A semantic preparation of not A as the rectified
NNF sentence B transfers validity of the original A to unsatisfiability of B.
The sentence and normalization requirements are explicitly on B. -/
theorem shgPreview_preparation {L : Language} (A B : FormulaN L)
    (hNNF : B.isNNF)
    (hRect : LCS.FirstOrder.Semantics.Subformulae.isRectified B)
    (hSentence : FormulaN.isClosed B)
    (hPrepare : ∀ (M : Structure L) (s : Assignment M),
      LCS.FirstOrder.SemanticsN.formulaEvalN M B s ↔
        ¬ LCS.FirstOrder.SemanticsN.formulaEvalN M A s) :
    B.isNNF ∧ LCS.FirstOrder.Semantics.Subformulae.isRectified B ∧
      FormulaN.isClosed B ∧
      (LCS.FirstOrder.SemanticsN.universallyValidN A ↔
        ¬ LCS.FirstOrder.SemanticsN.satisfiableN B) := by
  refine ⟨hNNF, hRect, hSentence, ?_⟩
  have hs : LCS.FirstOrder.SemanticsN.satisfiableN B ↔
      LCS.FirstOrder.SemanticsN.satisfiableN (.neg A) := by
    constructor
    · rintro ⟨M, s, h⟩
      exact ⟨M, s, (hPrepare M s).mp h⟩
    · rintro ⟨M, s, h⟩
      exact ⟨M, s, (hPrepare M s).mpr h⟩
  exact (skolem_validity_duality A (.neg A) rfl).1.trans (not_congr hs).symm

end LCS.Herbrand.SHGTheorem

end

section

namespace LCS.Herbrand.SHGTheorem

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.Herbrand.NNFHauptsatz

open LCS.Herbrand.HerbrandTheorem

proof_of shgMotivMidsequent_substitution := set_option backward.isDefEq.respectTransparency false in
  by
    simp [shgMotivMidsequent, shgMotivTransformedMidsequent,
      ShgMotivProof.p, ShgMotivProof.r, ShgMotivProof.a,
      ShgMotivTransformedProof.fa, ShgMotivTransformedProof.a, shgMotivLang,
      formulaSubstN, ShgMotivProof.substVec1, ShgMotivProof.substVec2, termSubst]


helper /-- The displayed new midsequent is quantifier-free and ground. -/
theorem shgMotivTransformedMidsequent_ground :
    LCS.FirstOrder.SemanticsN.isQuantifierFree shgMotivTransformedMidsequent ∧
      FormulaN.isClosed shgMotivTransformedMidsequent := by
  constructor
  · trivial
  · change formulaFVN shgMotivTransformedMidsequent = ∅
    funext x
    apply propext
    simp [shgMotivTransformedMidsequent, ShgMotivProof.p, ShgMotivProof.r,
      ShgMotivProof.a, shgMotivLang, formulaFVN, termFV, Membership.mem,
      Set.iUnion, Set.union, Set.diff, Set.singleton, Set.empty,
      shgMotivVec1, shgMotivVec2, Fin.exists_fin_succ, Fin.forall_fin_succ]











end LCS.Herbrand.SHGTheorem

end
