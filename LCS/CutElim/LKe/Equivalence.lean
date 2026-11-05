import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.CutElim.CompletenessBridge
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.LKe.Equivalence.AtomicLeaves
import LCS.CutElim.LKe.Equivalence.ContextPermutation
import LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
import LCS.CutElim.LKe.Equivalence.ImplicationPermutation
import LCS.CutElim.LKe.Equivalence.Normalization
import LCS.CutElim.LKe.Equivalence.AtomicTranslation
import LCS.CutElim.LKe.Equivalence.EqualityTranslation
import LCS.CutElim.LKe.Equivalence.Validity

/-! # CutElim.LKe.Equivalence
    Formalization of Chapter 6, Sections 3.2-3.3.
    Permutation lemma for G= and logical equivalence of G=, LKe, and LKe
    without essential cuts.

    Adapted for indexed proof tree types:
    - GProofTreeExt, GEqProofTree, FOLKProofTree, LKeProofTree are all
      indexed by their conclusion sequent.
    - WellFormed predicates are eliminated; structural validity is
      enforced by the types.
    - `conclusion` returns the type index (definitionally rfl).
-/

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

-- ===================================================================
-- Lemma 6.3.1 (required def): isQuantified
-- ===================================================================


-- ===================================================================
-- Lemma 6.3.1 (helper): GProofTreeExt atomic leaves
-- ===================================================================

section

variable
    (L : Language) (n : Nat) (ihS : ∀ (s' : Sequent L), sequentWeight s' < n → isAxiom s' → ∃ (g :
      GProofTreeExt s'), ∀ (l : Sequent L), l ∈ gProofTreeLeafSequents g → seqAllAtomicOrQuantified l)

include ihS


end


section

variable
    (L : Language) (hL : L.hasEquality = true) (n : Nat) (ih : ∀ (m : Nat), m < n → ∀ {s : Sequent L} (T :
      GEqProofTree hL s), geqDepth T = m → ∀ (Γ' Δ' : List (FormulaN L)), s.antecedent.Perm Γ' →
      s.succedent.Perm Δ' → (∀ (s' : Sequent L), s' ∈ geqLeafSequents T → seqAllAtomicOrQuantified s') → ∃ (T'
      : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth T' = geqDepth T ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents T' → seqAllAtomicOrQuantified s')

include ih


end


section

variable
    (L : Language) (hL : L.hasEquality = true) (n : Nat) (ih : ∀ (m : Nat), m < n → ∀ {s : Sequent L} (T :
      GEqProofTree hL s), geqDepth T = m → ∀ (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)), s = (Sequent.mk
      (Γ) (Δ ++ [A.conj B] ++ Λ)) → (∀ (s' : Sequent L), s' ∈ geqLeafSequents T → seqAllAtomicOrQuantified s')
      → ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ
      ++ [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth T ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s')

include ih



end


section

variable
    (L : Language) (hL : L.hasEquality = true) (n : Nat) (ih : ∀ (m : Nat), m < n → ∀ {s : Sequent L} (T :
      GEqProofTree hL s), geqDepth T = m → ∀ (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)), s = (Sequent.mk
      (Γ ++ [A.impl B] ++ Δ) (Λ)) → (∀ (s' : Sequent L), s' ∈ geqLeafSequents T → seqAllAtomicOrQuantified s')
      → ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ ++ Δ) (Λ ++ [A]))), ∃ (p2 : GEqProofTree hL (Sequent.mk ([B] ++
      Γ ++ Δ) (Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth T ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s')

include ih



end


-- ===================================================================
-- Lemma 6.3.3 (helper): direct G= full normalization
-- ===================================================================

section

variable
    (L : Language) (hL : L.hasEquality = true) (n : Nat) (ih : ∀ (m : Nat), m < n → ∀ {s : Sequent L} (T :
      GEqProofTree hL s), geqDepth T = m → (∀ (s' : Sequent L), s' ∈ geqLeafSequents T →
      seqAllAtomicOrQuantified s') → ∃ (T' : GEqProofTree hL s), geqIsConjImplNormalized T' ∧ geqDepth T' =
      geqDepth T)

include ih


end


namespace LKeAtomicProofTree


end LKeAtomicProofTree

-- ===================================================================
-- Theorem 6.3.1 (required def): lkeProvableWithoutEssentialCuts
-- ===================================================================


namespace ConjProjection

end ConjProjection

open LCS.FirstOrder.Equality


namespace ImplLeftProjection

end ImplLeftProjection



namespace ImplAntecedentProjection


end ImplAntecedentProjection





end LCS.CutElim.LKe.Equivalence
