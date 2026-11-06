import LCS.CutElim.Interpolation.Equality.Craig

section
namespace LCS.CutElim.Interpolation.Equality
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.CutElim.Interpolation
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Equality.Completeness
open LCS.FirstOrder.Gentzen.Hintikka

proof_of craig_interpolation_equality := by
  -- BEGIN PROOF
    -- Adjoin a fresh nullary predicate so that A and B are ⊥-free,
    -- lift the derivation, and apply interpolation_key_lemma_equality.
    -- Replace ⊥ in the interpolant by ¬∀z(z ≐ z) and lower the two
    -- LKₑ derivations back to LKₑ over the original language.
    -- REPAIR(T6-50): proof pending
    sorry

end LCS.CutElim.Interpolation.Equality
end
