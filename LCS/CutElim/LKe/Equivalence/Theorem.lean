import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.CutElim.CompletenessBridge
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.LKe.Equivalence.AtomicCuts
import LCS.CutElim.LKe.Equivalence.EqualityRules
import LCS.CutElim.LKe.Equivalence.Soundness
import LCS.CutElim.LKe.Equivalence.SemanticBridge.SupportLanguage
import LCS.CutElim.LKe.Equivalence.SemanticBridge.Lifting
import LCS.CutElim.LKe.Equivalence.SemanticBridge
import Attach
import LCS.CutElim.LKe.Equivalence.Theorem.ProofsStamp

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
open LCS.FirstOrder.Equality

-- Helper: removing a valid formula from the antecedent preserves lkeProvable.
-- retained: used by LCS.CutElim.Interpolation.Equality.Replay
theorem lkeProvable_remove_valid_antecedent {L : Language}
    (A : FormulaN L) (Γ Δ : List (FormulaN L)) (Λ : List (FormulaN L))
    (hvalid_A : ∀ (M : Structure L) (s : Assignment M), formulaEvalN M A s)
    (h : lkeProvable (Sequent.mk (Γ ++ [A] ++ Δ) Λ)) :
    lkeProvable (Sequent.mk (Γ ++ Δ) Λ) := by
-- BEGIN PROOF
  apply lkeProvable_of_valid
  have hvalid := lkeProvable_valid _ h
  intro M s hAnte
  apply hvalid M s
  intro F hF
  simp only [List.append_assoc, List.singleton_append] at hF
  rcases List.mem_append.mp hF with hFΓ | hFA
  · exact hAnte F (List.mem_append_left _ hFΓ)
  · rcases List.mem_cons.mp hFA with rfl | hFΔ
    · exact hvalid_A M s
    · exact hAnte F (List.mem_append_right _ hFΔ)

-- Helper: removing a list of valid formulas from the antecedent prefix
-- retained: used by LCS.CutElim.Interpolation.Equality.Replay
theorem lkeProvable_remove_valid_prefix {L : Language}
    (axioms : List (FormulaN L)) (rest : List (FormulaN L))
    (Λ : List (FormulaN L))
    (hvalid : ∀ A ∈ axioms,
      ∀ (M : Structure L) (s : Assignment M), formulaEvalN M A s)
    (h : lkeProvable (Sequent.mk (axioms ++ rest) Λ)) :
    lkeProvable (Sequent.mk rest Λ) := by
-- BEGIN PROOF
  induction axioms with
  | nil => exact h
  | cons a axioms' ih =>
    have hvalid_a : ∀ (M : Structure L) (s : Assignment M),
        formulaEvalN M a s :=
      hvalid a (List.Mem.head _)
    have hvalid' : ∀ A ∈ axioms',
        ∀ (M : Structure L) (s : Assignment M), formulaEvalN M A s :=
      fun A hA => hvalid A (List.mem_cons_of_mem _ hA)
    have h' : lkeProvable
        (Sequent.mk ([] ++ [a] ++ (axioms' ++ rest)) Λ) := by
      simp at h ⊢; exact h
    have h'' := lkeProvable_remove_valid_antecedent a []
      (axioms' ++ rest) Λ hvalid_a h'
    simp at h''
    exact ih hvalid' h''

end LCS.CutElim.LKe.Equivalence
end
