import LCS.CutElim.LK.Soundness

section
namespace LCS.CutElim.LK
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.CutElim.CompletenessBridge

helper /-- Lemma 6.2.1: Every axiom of LK is valid. For every rule of LK,
if the premises of the rule are valid, then the conclusion of the
rule is valid. Every LK-provable sequent is valid. -/
theorem lemma_6_2_1 {L : Language} :
    (∀ s : Sequent L, isFOLKAxiom s → sequentValid s) ∧
    (∀ {prem conc : Sequent L}, (rule : FOLKStep1 prem conc) →
      sequentValid prem → sequentValid conc) ∧
    (∀ {prem1 prem2 conc : Sequent L}, (rule : FOLKStep2 prem1 prem2 conc) →
      sequentValid prem1 → sequentValid prem2 → sequentValid conc) ∧
    (∀ seq : Sequent L, folkProvable seq → sequentValid seq) :=
-- BEGIN PROOF
  ⟨lemma_6_2_1_axioms_valid,
   fun rule hp => lemma_6_2_1_rules1_preserve_validity rule hp,
   fun rule hp1 hp2 => lemma_6_2_1_rules2_preserve_validity rule hp1 hp2,
   soundness_FOLK⟩

proof_of lemma_6_2_1NoEq := lemma_6_2_1

end LCS.CutElim.LK
end
