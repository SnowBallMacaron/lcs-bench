import LCS.Propositional.Infinite.Semantics

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

proof_of infSeqProvable_implies_valid := by
  -- BEGIN PROOF
    -- Extract the finite witnessing sequent and its provability
    obtain ⟨Gamma_fin, Delta_fin, hGamma, hDelta, hProv⟩ := h
    -- By soundness of G' (Lemma 3.4.3), the finite sequent is valid
    have hValid := soundness_G (Sequent.mk Gamma_fin Delta_fin) hProv
    -- Lift finite validity to the infinite sequent
    intro v hAnt
    -- v satisfies all antecedent formulae of the infinite sequent
    -- In particular, v satisfies the finite subset Gamma_fin
    have hFinAnt : ∀ A ∈ Gamma_fin, evalExtN v A = BoolVal.T := by
      intro A hA
      obtain ⟨n, hn⟩ := hGamma A hA
      exact hAnt n A hn
    -- By validity of the finite sequent, some B in Delta_fin is true
    obtain ⟨B, hBmem, hBtrue⟩ := hValid v hFinAnt
    -- This B is also in the infinite succedent
    obtain ⟨m, hm⟩ := hDelta B hBmem
    exact ⟨m, B, hm, hBtrue⟩

end LCS.Propositional.Infinite
end
