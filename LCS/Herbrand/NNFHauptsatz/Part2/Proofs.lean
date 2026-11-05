import LCS.Herbrand.NNFHauptsatz.Part2

section

namespace LCS.Herbrand.NNFHauptsatz

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Equality

namespace MaxQuantifierOccurrence

helper /-- Set-valued maximal-subformula membership is exactly existence of an
occurrence whose lookup has that syntax. -/
theorem MaxQuantifierOccurrence.mem_iff_exists {L : Language} {A Q : FormulaN L} :
    Membership.mem (maxQuantSubformulaeCore A) Q ↔
      ∃ occurrence : MaxQuantifierOccurrence A, occurrence.selected = Q := by
  constructor
  · exact exists_of_mem
  · rintro ⟨occurrence, rfl⟩
    exact occurrence.selected_mem

helper /-- Every maximal quantified subformula after selected replacement comes from
the unchanged ambient formula or from the replacement. -/
theorem MaxQuantifierOccurrence.replace_maxQuantSubformulae_subset {L : Language}
    {A : FormulaN L} (occurrence : MaxQuantifierOccurrence A)
    (replacement : FormulaN L) :
    maxQuantSubformulaeCore (occurrence.replace replacement) ⊆
      maxQuantSubformulaeCore A ∪ maxQuantSubformulaeCore replacement := by
  induction occurrence with
  | all _ _ =>
      intro Q hQ
      exact Or.inr hQ
  | ex _ _ =>
      intro Q hQ
      exact Or.inr hQ
  | conjLeft _ _ ih =>
      intro Q hQ
      rcases hQ with hQ | hQ
      · rcases ih Q hQ with hQ | hQ
        · exact Or.inl (Or.inl hQ)
        · exact Or.inr hQ
      · exact Or.inl (Or.inr hQ)
  | conjRight _ _ ih =>
      intro Q hQ
      rcases hQ with hQ | hQ
      · exact Or.inl (Or.inl hQ)
      · rcases ih Q hQ with hQ | hQ
        · exact Or.inl (Or.inr hQ)
        · exact Or.inr hQ
  | disjLeft _ _ ih =>
      intro Q hQ
      rcases hQ with hQ | hQ
      · rcases ih Q hQ with hQ | hQ
        · exact Or.inl (Or.inl hQ)
        · exact Or.inr hQ
      · exact Or.inl (Or.inr hQ)
  | disjRight _ _ ih =>
      intro Q hQ
      rcases hQ with hQ | hQ
      · exact Or.inl (Or.inl hQ)
      · rcases ih Q hQ with hQ | hQ
        · exact Or.inl (Or.inr hQ)
        · exact Or.inr hQ

end MaxQuantifierOccurrence

end LCS.Herbrand.NNFHauptsatz

end

section

namespace LCS.Herbrand.NNFHauptsatz

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Equality

helper /-- Definition 7.4.2 (companion): Recognizes a conjunction, disjunction or
quantified formula at a node reached through conjunction/disjunction edges.
Atoms, negations and implications return False, including self-comparison;
quantifier bodies are not traversed. Replacement uses its own equality checks. -/
def isSubformulaOf {L : Language} :
    FormulaN L → FormulaN L → Prop
  | _, .predN _ _  => False
  | _, .eq_ _ _ _  => False
  | _, .neg _      => False
  | B, .disj A1 A2 =>
    B = FormulaN.disj A1 A2 ∨ isSubformulaOf B A1 ∨ isSubformulaOf B A2
  | B, .conj A1 A2 =>
    B = FormulaN.conj A1 A2 ∨ isSubformulaOf B A1 ∨ isSubformulaOf B A2
  | B, .all x C    => B = FormulaN.all x C
  | B, .ex x C     => B = FormulaN.ex x C
  | _, .impl _ _   => False

end LCS.Herbrand.NNFHauptsatz

end

section

namespace LCS.Herbrand.NNFHauptsatz

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Equality

namespace G2nnfRule

namespace SideConditions



end SideConditions

end G2nnfRule

end LCS.Herbrand.NNFHauptsatz

end

section

namespace LCS.Herbrand.NNFHauptsatz

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Equality

namespace G2nnfProofTree





end G2nnfProofTree

end LCS.Herbrand.NNFHauptsatz

end

section

namespace LCS.Herbrand.NNFHauptsatz

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Equality

namespace G2nnfDeductionTree





end G2nnfDeductionTree

end LCS.Herbrand.NNFHauptsatz

end

section

namespace LCS.Herbrand.NNFHauptsatz

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Equality

proof_of qfExResult := by
  -- BEGIN PROOF
    unfold maxQuantSubformulae maxQuantSubformulaeCore qfExFormula
    rfl


proof_of qfExNonMaximal := by
  -- BEGIN PROOF
    unfold maxQuantSubformulae maxQuantSubformulaeCore qfExFormula LCS.Herbrand.NNFHauptsatz.sng
    intro h
    rcases h with (h | h) | h
    · exact nomatch h
    · rcases h with h | h
      · exact h
      · exact nomatch h
    · exact nomatch h


proof_of replaceExResult := by
  -- BEGIN PROOF
    unfold replaceMaxQuantSub replaceExFormula replaceExTarget replaceExReplacement
    simp only [replaceMaxQuantSubCore]
    have hne_disj : ∀ x B,
        FormulaN.disj
          (FormulaN.all 0 (FormulaN.predN NnfExPred.P (replExVec1 (Term.var 0))))
          ((FormulaN.predN NnfExPred.Q
              (replExVec1 (Term.const ReplExConst.b))).conj
            (FormulaN.all 1
              ((FormulaN.predN NnfExPred.P (replExVec1 (Term.var 1))).neg.disj
                (FormulaN.all 2
                  (FormulaN.predN NnfExPred.R
                    (replExVec2 (Term.var 1) (Term.var 2))))))) ≠
        @FormulaN.all replExLang x B := by
      intro x B h; cases h
    simp only [show ∀ x B, _ from hne_disj, if_false]
    split
    · rename_i h; cases h
    · split
      · rename_i h h'; cases h'
      · simp only [ite_true]


end LCS.Herbrand.NNFHauptsatz

end

section

namespace LCS.Herbrand.NNFHauptsatz

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Equality

namespace G2nnfEqRule

helper /-- A base rule preserves exactly its Core side conditions. -/
theorem G2nnfEqRule.sideConditions_base_iff {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)] (r : G2nnfRuleCore L) :
    SideConditions (hL := hL) (.base r) ↔ r.SideConditions := Iff.rfl

helper /-- Equality admission retains recursive WellFormed and checks NNF and
rectification on both full sides of the canonical axiom sequent. -/
theorem G2nnfEqRule.sideConditions_eqAxiom_iff {L : Language}
    {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    (ax : G1nnfEqAxiom L hL) :
    SideConditions (.eqAxiom ax) ↔
      ax.WellFormed ∧ AllNNF ax.toSequent ∧ AllRectified ax.toSequent := Iff.rfl

helper theorem G2nnfEqRule.sideConditions_allRectified {L : Language}
    {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    {rule : G2nnfEqRule L hL} (hSC : rule.SideConditions) :
    AllRectified rule.conclusion := by
  cases rule with
  | base _ => exact hSC.conclusionRectified
  | eqAxiom _ => exact hSC.2.2

helper theorem G2nnfEqRule.sideConditions_allNNF {L : Language}
    {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    {rule : G2nnfEqRule L hL} (hSC : rule.SideConditions) :
    AllNNF rule.conclusion := by
  cases rule with
  | base _ => exact hSC.conclusionNNF
  | eqAxiom _ => exact hSC.2.1

end G2nnfEqRule

end LCS.Herbrand.NNFHauptsatz

end

section

namespace LCS.Herbrand.NNFHauptsatz

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Equality

namespace G2nnfEqDeductionTree





end G2nnfEqDeductionTree

end LCS.Herbrand.NNFHauptsatz

end

section

namespace LCS.Herbrand.NNFHauptsatz

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Equality

helper /-- Guarded equality-leaf bridge: every admissible G1nnf= equality axiom is
accepted as a G2nnf= equality-axiom leaf, with its `WellFormed` evidence
forwarded together with NNF and rectification evidence for its whole sequent. -/
noncomputable def g2nnfEqProofTree_accepts_eqAxiom {L : Language}
    {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    (ax : G1nnfEqAxiom L hL)
    (hWF : ax.WellFormed)
    (hNNF : AllNNF ax.toSequent)
    (hRect : AllRectified ax.toSequent) :
    G2nnfEqProofTree hL ax.toSequent.1 ax.toSequent.2 :=
  .extraAxiom ax.toSequent.1 ax.toSequent.2 ⟨ax, hWF, rfl⟩ hNNF hRect

helper /-- Positive regression: a concrete admissible recursive negation closure is
accepted through the guarded G1nnf=-to-G2nnf= equality-leaf bridge. -/
noncomputable def g2nnfEqProofTree_accepts_legalNegLeft {L : Language}
    (hL : L.hasEquality = true) [DecidableEq (FormulaN L)] (t : Term L) :
    G2nnfEqProofTree hL
      (G1nnfEqAxiom.legalNegLeftExample hL t).toSequent.1
      (G1nnfEqAxiom.legalNegLeftExample hL t).toSequent.2 :=
  g2nnfEqProofTree_accepts_eqAxiom
    (G1nnfEqAxiom.legalNegLeftExample hL t)
    (G1nnfEqAxiom.legalNegLeftExample_wellFormed hL t)
    (by
      rw [G1nnfEqAxiom.legalNegLeftExample_toSequent]
      constructor
      · intro A hA
        rw [LCS.Finset.mem_singleton] at hA
        subst A
        trivial
      · intro A hA
        exact (LCS.Finset.not_mem_empty hA).elim)
    (by
      rw [G1nnfEqAxiom.legalNegLeftExample_toSequent]
      refine ⟨?_, ?_⟩
      · intro A hA
        rw [LCS.Finset.mem_singleton] at hA
        subst A
        exact AllRectified.isRectified_of_isQuantifierFree _ trivial
      · intro A hA
        exact (LCS.Finset.not_mem_empty hA).elim)

helper /-- Adversarial regression: the raw equality-rule wrapper rejects the known
malformed closure `negLeft (refl t ∅ ∅) (A ∧ B)` before it can become a
G2nnf= proof-tree leaf. -/
theorem g2nnfEqProofTree_rejects_malformedNonAtomicClosure {L : Language}
    (hL : L.hasEquality = true) (t : Term L) (A B : FormulaN L) :
    ¬ G2nnfEqRule.SideConditions
      (.eqAxiom
        (.negLeft
          (.refl (hL := hL) t LCS.Finset.empty LCS.Finset.empty)
          (.conj A B))) :=
  fun hSC =>
    G1nnfEqAxiom.wellFormed_negLeft_rejects_nonAtomic
      (.refl (hL := hL) t LCS.Finset.empty LCS.Finset.empty) A B hSC.1

helper /-- Delegation regression: wrapping an ordinary base G2nnf rule does not erase
its eigenvariable freshness condition. -/
theorem g2nnfEqProofTree_rejects_nonfreshAllSubRight {L : Language}
    (hL : L.hasEquality = true) (A B F : FormulaN L)
    (occurrence : MaxQuantifierOccurrence A)
    (x y : Nat) (Delta : LCS.Finset (FormulaN L))
    (hSelected : occurrence.selected = FormulaN.all x B)
    (hyF : Membership.mem (formulaFVN F) y) :
    ¬ G2nnfEqRule.SideConditions (hL := hL)
      (.base (.allSubRight A occurrence x B y hSelected
        (LCS.Finset.singleton F) Delta)) := by
  intro hSC
  exact hSC.logical.2.2.1 F ((LCS.Finset.mem_singleton F F).mpr rfl) hyF

end LCS.Herbrand.NNFHauptsatz

end

section

namespace LCS.Herbrand.NNFHauptsatz

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Equality

namespace G2nnfEqProofTree





end G2nnfEqProofTree

end LCS.Herbrand.NNFHauptsatz

end
