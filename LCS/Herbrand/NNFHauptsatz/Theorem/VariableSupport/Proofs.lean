import LCS.Herbrand.NNFHauptsatz.Theorem.VariableSupport

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.Herbrand.NNFHauptsatz

open LCS.Herbrand.NNFHauptsatz.Soundness

open LCS.Herbrand.SharpenedHauptsatz

open LCS.Herbrand.SharpenedHauptsatz.Permutability

open LCS.Herbrand.SharpenedHauptsatz.Theorem

open LCS.Herbrand.PrenexForm

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

open LCS.CutElim.LK

namespace LCS.Herbrand.NNFHauptsatz.G2nnfRuleCore

helper /-- Rule renaming preserves the quantifier-rule classifier. -/
theorem G2nnfRuleCore.isQuantifierRule_varMap_iff {L : Language}
    (ρ : Nat → Nat) (rule : _root_.LCS.Herbrand.NNFHauptsatz.G2nnfRuleCore L) :
    (rule.varMap ρ).isQuantifierRule ↔ rule.isQuantifierRule := by
  cases rule <;> rfl

helper /-- Rule renaming preserves the propositional-rule classifier. -/
theorem G2nnfRuleCore.isPropositionalRule_varMap_iff {L : Language}
    (ρ : Nat → Nat) (rule : _root_.LCS.Herbrand.NNFHauptsatz.G2nnfRuleCore L) :
    (rule.varMap ρ).isPropositionalRule ↔
      rule.isPropositionalRule := by
  cases rule <;> rfl

helper /-- Rule renaming preserves weakening classification. -/
theorem G2nnfRuleCore.isWeakening_varMap_iff {L : Language}
    (ρ : Nat → Nat) (rule : _root_.LCS.Herbrand.NNFHauptsatz.G2nnfRuleCore L) :
    (rule.varMap ρ).isWeakening ↔ rule.isWeakening := by
  cases rule <;> rfl



helper /-- Cut annotations are renamed exactly; non-cut rules remain non-cut. -/
theorem G2nnfRuleCore.cutFormula_varMap {L : Language}
    (ρ : Nat → Nat) (rule : _root_.LCS.Herbrand.NNFHauptsatz.G2nnfRuleCore L) :
    (rule.varMap ρ).cutFormula =
      rule.cutFormula.map (_root_.LCS.Herbrand.NNFHauptsatz.formulaVarMapN ρ) := by
  cases rule <;> rfl

end LCS.Herbrand.NNFHauptsatz.G2nnfRuleCore

end

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.Herbrand.NNFHauptsatz

open LCS.Herbrand.NNFHauptsatz.Soundness

open LCS.Herbrand.SharpenedHauptsatz

open LCS.Herbrand.SharpenedHauptsatz.Permutability

open LCS.Herbrand.SharpenedHauptsatz.Theorem

open LCS.Herbrand.PrenexForm

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

open LCS.CutElim.LK

namespace LCS.Herbrand.NNFHauptsatz

namespace G2nnfRuleCore



helper /-- An axiom's stored antecedent context is retained in the contextual carrier. -/
theorem G2nnfRuleCore.variableSupport_axiom_stored_left {L : Language}
    (A : FormulaN L) (hAtom : A.isAtomic)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (v : Nat) (hv : v ∈ formulaFinsetVariableSupport Gamma) :
    v ∈ (G2nnfRuleCore.axiomPosId A hAtom Gamma Delta).variableSupport :=
  LCS.Finset.mem_union.mpr
    (Or.inr (LCS.Finset.mem_union.mpr (Or.inl hv)))

helper /-- An axiom's stored succedent context is retained. -/
theorem G2nnfRuleCore.variableSupport_axiom_stored_right {L : Language}
    (A : FormulaN L) (hAtom : A.isAtomic)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (v : Nat) (hv : v ∈ formulaFinsetVariableSupport Delta) :
    v ∈ (G2nnfRuleCore.axiomPosId A hAtom Gamma Delta).variableSupport :=
  LCS.Finset.mem_union.mpr
    (Or.inr (LCS.Finset.mem_union.mpr (Or.inr hv)))

helper /-- An eigenvariable label is included even when it occurs only in a hidden
quantifier-rule annotation. -/
theorem G2nnfRuleCore.variableSupport_allSubRight_eigenvariable {L : Language}
    (A B : FormulaN L) (occurrence : _root_.LCS.Herbrand.NNFHauptsatz.MaxQuantifierOccurrence A)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (x y : Nat)
    (hSelected : occurrence.selected = FormulaN.all x B) :
    y ∈
      (G2nnfRuleCore.allSubRight A occurrence x B y hSelected Gamma Delta).variableSupport :=
  LCS.Finset.mem_union.mpr (Or.inl (
  LCS.Finset.mem_insert.mpr
    (Or.inr (LCS.Finset.mem_insert.mpr (Or.inl rfl)))))

helper /-- Symmetric existential-left eigenvariable coverage. -/
theorem G2nnfRuleCore.variableSupport_exSubLeft_eigenvariable {L : Language}
    (A B : FormulaN L) (occurrence : _root_.LCS.Herbrand.NNFHauptsatz.MaxQuantifierOccurrence A)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (x y : Nat)
    (hSelected : occurrence.selected = FormulaN.ex x B) :
    y ∈
      (G2nnfRuleCore.exSubLeft A occurrence x B y hSelected Gamma Delta).variableSupport :=
  LCS.Finset.mem_union.mpr (Or.inl (
  LCS.Finset.mem_insert.mpr
    (Or.inr (LCS.Finset.mem_insert.mpr (Or.inl rfl)))))

helper /-- Exact occurrence-principal annotations are retained independently of
whether their variables are visible in the raw contexts. -/
theorem G2nnfRuleCore.variableSupport_allSubRight_occurrence {L : Language}
    (A B : FormulaN L) (occurrence : _root_.LCS.Herbrand.NNFHauptsatz.MaxQuantifierOccurrence A)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (x y : Nat)
    (hSelected : occurrence.selected = FormulaN.all x B)
    (v : Nat) (hv : v ∈ occurrence.variableSupport) :
    v ∈
      (G2nnfRuleCore.allSubRight A occurrence x B y hSelected Gamma Delta).variableSupport :=
  LCS.Finset.mem_union.mpr (Or.inl (
  LCS.Finset.mem_insert.mpr
    (Or.inr (LCS.Finset.mem_insert.mpr
      (Or.inr (LCS.Finset.mem_union.mpr
        (Or.inr (LCS.Finset.mem_union.mpr (Or.inl hv)))))))))

helper /-- Instantiation-term variables are included even if absent from the rule's
conclusion sequent. -/
theorem G2nnfRuleCore.variableSupport_allSubLeft_term {L : Language}
    (A B : FormulaN L) (occurrence : _root_.LCS.Herbrand.NNFHauptsatz.MaxQuantifierOccurrence A)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (x : Nat) (t : Term L)
    (hSelected : occurrence.selected = FormulaN.all x B)
    (v : Nat) (hv : v ∈ termVariableSupport t) :
    v ∈
      (G2nnfRuleCore.allSubLeft A occurrence x B t hSelected Gamma Delta).variableSupport :=
  LCS.Finset.mem_union.mpr (Or.inl (
  LCS.Finset.mem_insert.mpr
    (Or.inr (LCS.Finset.mem_union.mpr
      (Or.inr (LCS.Finset.mem_union.mpr
        (Or.inr (LCS.Finset.mem_union.mpr (Or.inr hv)))))))))

end G2nnfRuleCore

end LCS.Herbrand.NNFHauptsatz

end

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.Herbrand.NNFHauptsatz

open LCS.Herbrand.NNFHauptsatz.Soundness

open LCS.Herbrand.SharpenedHauptsatz

open LCS.Herbrand.SharpenedHauptsatz.Permutability

open LCS.Herbrand.SharpenedHauptsatz.Theorem

open LCS.Herbrand.PrenexForm

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

open LCS.CutElim.LK

namespace LCS.Herbrand.NNFHauptsatz.G2nnfProofTree







end LCS.Herbrand.NNFHauptsatz.G2nnfProofTree

end
