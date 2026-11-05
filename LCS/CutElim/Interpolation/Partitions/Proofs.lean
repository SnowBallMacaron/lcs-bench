import LCS.CutElim.Interpolation.Partitions

section

namespace LCS.CutElim.Interpolation

open Classical

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

open LCS.FirstOrder.Gentzen.Hintikka

proof_of interpolant_language_dependence := by
  -- REPAIR(T6-37): proof pending
  sorry


proof_of interpolant_equality_witness := by
  simp [IsValidInterpolantEq, universallyValidN, validInN, formulaEvalN,
    implM, formulaFVN, termFV, formulaPredSymbolsN, formulaConstSymbolsN,
    termConstSymbols, Set.subset, Set.inter, Set.union, Set.diff, Set.singleton, Set.empty]


proof_of interpolant_true_witness := by
  simp [IsValidInterpolantBot, universallyValidBotN, validInN, formulaEvalN,
    implM, negM, botFormula, formulaFVN, formulaPredSymbolsWithEqN,
    formulaConstSymbolsN]
  refine ⟨?_, ?_, ?_⟩
  · intro v ⟨i, _⟩
    exact Fin.elim0 (hBot ▸ i)
  · intro R hR hn
    exact (hn hR).elim
  · intro c ⟨i, _⟩
    exact Fin.elim0 (hBot ▸ i)


end LCS.CutElim.Interpolation

end

section

namespace LCS.CutElim.Interpolation

open Classical

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

open LCS.FirstOrder.Gentzen.Hintikka

proof_of lkBot_cut_elimination := by
  -- REPAIR(T6-40): proof pending
  sorry




helper theorem folkToBot_conclusion {L : Language} (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) {s : Sequent L}
    (T : LCS.CutElim.LK.FOLKProofTree s) :
    (folkToBot botP hBotArity T).conclusion = s := rfl







helper /-- Example 6.5.1: Demonstrates Craig's interpolation theorem with
the implication (P(a) /\ forall x Q(x)) => (forall y S(y) \/ Q(b)).
The formula forall x Q(x) is an interpolant: Q is the common
predicate symbol, and the interpolant has no constants or free
variables. The example bundles the antecedent, consequent, and
interpolant together. -/
def interpolation_example :
    { triple : FormulaN interpExLanguage × FormulaN interpExLanguage
               × FormulaN interpExLanguage //
      triple.1 = interpExAntecedent ∧
      triple.2.1 = interpExInterpolant ∧
      triple.2.2 = interpExConsequent } :=
  ⟨(interpExAntecedent, interpExInterpolant, interpExConsequent), ⟨rfl, rfl, rfl⟩⟩

proof_of interpolation_example_spec := by
  constructor
  · exact ⟨.onePremise
      (.andLeftR _ interpExInterpolant [] [interpExInterpolant])
      (.axiom_ _ ⟨interpExInterpolant, rfl, rfl⟩)⟩
  · let q : FormulaN interpExLanguage :=
      .predN InterpExPred.Q (fun _ => .const InterpExConst.b)
    refine ⟨.onePremise (.orRightR _ q [interpExInterpolant] []) ?_⟩
    exact .onePremise
      (.allLeft (.const InterpExConst.b) 0
        (.predN InterpExPred.Q (fun _ => .var 0)) [] [q] trivial)
      (.axiom_ _ ⟨q, rfl, rfl⟩)
  · intro pred hPred
    change pred = InterpExPred.Q at hPred
    subst pred
    exact ⟨Or.inr rfl, Or.inr rfl⟩
  · intro c hc
    obtain ⟨i, hi⟩ := hc
    exact False.elim hi
  · intro x hx
    change (∃ _ : Fin 1, x = 0) ∧ ¬ x = 0 at hx
    obtain ⟨⟨i, hi⟩, hne⟩ := hx
    exact False.elim (hne hi)




end LCS.CutElim.Interpolation

end
