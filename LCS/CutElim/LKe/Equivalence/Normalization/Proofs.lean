import LCS.CutElim.LKe.Equivalence.Normalization

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

helper theorem geqNormalize_atomic
    (L : Language) (hL : L.hasEquality = true)
    : ∀ (n : Nat) {s : Sequent L} (T : GEqProofTree hL s), geqDepth T = n → (∀ (s' : Sequent L), s' ∈
      geqLeafSequents T → seqAllAtomicOrQuantified s') → ∃ (T' : GEqProofTree hL s), geqIsConjImplNormalized
      T' ∧ geqDepth T' = geqDepth T := by
  classical
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro s T hdepth hleaf
    have normOne : ∀ {prem conc : Sequent L} (rule : GentzenStep1Ext prem conc) (sub : GEqProofTree hL prem),
          geqDepth sub < n →
          (∀ s' ∈ geqLeafSequents sub, seqAllAtomicOrQuantified s') →
          ¬ sequentHasConjImplTarget conc →
          ∃ p : GEqProofTree hL conc, geqIsConjImplNormalized p ∧ geqDepth p = 1 + geqDepth sub := by
      intro prem conc rule sub hsubdepth hsubleaf hconc
      obtain ⟨q, hqnorm, hqdepth⟩ := ih (geqDepth sub) hsubdepth sub rfl hsubleaf
      refine ⟨.onePremise rule q, ?_, ?_⟩
      · exact ⟨hconc, hqnorm⟩
      · simp only [geqDepth]
        omega
    have normTwo : ∀ {prem1 prem2 conc : Sequent L} (rule : GentzenStep2Ext prem1 prem2 conc)
          (sub1 : GEqProofTree hL prem1)
          (sub2 : GEqProofTree hL prem2),
          geqDepth sub1 < n →
          geqDepth sub2 < n →
          (∀ s' ∈ geqLeafSequents sub1, seqAllAtomicOrQuantified s') →
          (∀ s' ∈ geqLeafSequents sub2, seqAllAtomicOrQuantified s') →
          ¬ sequentHasConjImplTarget conc →
          ∃ p : GEqProofTree hL conc, geqIsConjImplNormalized p ∧ geqDepth p =
              1 + max (geqDepth sub1) (geqDepth sub2) := by
      intro prem1 prem2 conc rule sub1 sub2 hsub1depth hsub2depth hsub1leaf hsub2leaf hconc
      obtain ⟨q1, hq1norm, hq1depth⟩ := ih (geqDepth sub1) hsub1depth sub1 rfl hsub1leaf
      obtain ⟨q2, hq2norm, hq2depth⟩ := ih (geqDepth sub2) hsub2depth sub2 rfl hsub2leaf
      refine ⟨.twoPremise rule q1 q2, ?_, ?_⟩
      · cases rule <;>
          simp_all [geqIsConjImplNormalized, sequentHasConjImplTarget]
      · simp only [geqDepth]
        omega
    by_cases htarget : sequentHasConjImplTarget s
    · exact geqNormalize_target L hL n ih s T hleaf htarget hdepth
    · exact geqNormalize_other L hL n ih s T hdepth hleaf normOne normTwo htarget

proof_of geqNormalize_conjImpl := by
  -- BEGIN PROOF
    classical
    have normalizeAtomic :
        ∀ n : Nat, ∀ {s : Sequent L} (T : GEqProofTree hL s),
          geqDepth T = n →
          (∀ s' ∈ geqLeafSequents T,
            seqAllAtomicOrQuantified s') →
          ∃ T' : GEqProofTree hL s,
            geqIsConjImplNormalized T' ∧
            geqDepth T' = geqDepth T := by
      exact geqNormalize_atomic L hL
    by_cases hleaf :
        ∀ s' ∈ geqLeafSequents T,
          seqAllAtomicOrQuantified s'
    · obtain ⟨T', hnorm, hdepth⟩ :=
        normalizeAtomic (geqDepth T) T rfl hleaf
      exact ⟨T', hnorm, fun _ => hdepth⟩
    · obtain ⟨U, hUleaf⟩ := permutation_lemma_geq T
      obtain ⟨T', hnorm, _⟩ :=
        normalizeAtomic (geqDepth U) U rfl hUleaf
      refine ⟨T', hnorm, ?_⟩
      intro h
      exact (hleaf h).elim

end LCS.CutElim.LKe.Equivalence
end
