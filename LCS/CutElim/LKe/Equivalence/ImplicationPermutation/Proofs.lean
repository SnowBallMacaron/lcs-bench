import LCS.CutElim.LKe.Equivalence.ImplicationPermutation

section

namespace LCS.CutElim.LKe.Equivalence

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.Hintikka

open LCS.FirstOrder.Equality

open LCS.FirstOrder.Completeness

open LCS.FirstOrder.Equality.Completeness

open LCS.CutElim.LK

open LCS.CutElim.LKe

open LCS.CutElim.CompletenessBridge

helper /-- Public depth-only projection of the leaf-preserving direct
implication-left commuting construction. -/
theorem geqPermute_implLeft {L : Language}
    {hL : L.hasEquality = true}
    (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L))
    (T : GEqProofTree hL
      (Sequent.mk (Γ ++ [FormulaN.impl A B] ++ Δ) Λ))
    (hleaf : ∀ s' ∈ geqLeafSequents T,
      seqAllAtomicOrQuantified s') :
    ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A])))
      (p2 : GEqProofTree hL (Sequent.mk ([B] ++ Γ ++ Δ) Λ)),
      1 + max (geqDepth p1) (geqDepth p2) = geqDepth T := by
  obtain ⟨p1, p2, hdepth, _, _⟩ :=
    geqPermute_implLeft_withLeaves A B Γ Δ Λ T hleaf
  exact ⟨p1, p2, hdepth⟩

proof_of conjRight_implLeft_permutation := by
  -- BEGIN PROOF
    -- Both branches are assembled from the direct G= permutation helpers.
    constructor
    · intro A B Γ Δ Λ h
      subst s
      obtain ⟨p1, p2, hdepth⟩ :=
        geqPermute_conjRight A B Γ Δ Λ T hleaf
      refine ⟨.twoPremise
          (GentzenStep2Ext.conjRight Γ Δ Λ A B) p1 p2, ?_, ?_⟩
      · simpa only [geqDepth] using hdepth
      · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · intro A B Γ Δ Λ h
      subst s
      obtain ⟨p1, p2, hdepth, hp1leaf, _⟩ :=
        geqPermute_implLeft_withLeaves A B Γ Δ Λ T hleaf
      obtain ⟨p1', hp1depth, _⟩ :=
        geqPermuteContexts p1 (Γ ++ Δ) ([A] ++ Λ)
          (List.Perm.refl _) (by exact List.perm_append_comm) hp1leaf
      refine ⟨.twoPremise
          (GentzenStep2Ext.implLeft Γ Δ Λ A B) p1' p2, ?_, ?_⟩
      · simp only [geqDepth]
        omega
      · exact ⟨rfl, rfl, rfl, rfl, rfl⟩


end LCS.CutElim.LKe.Equivalence

end
