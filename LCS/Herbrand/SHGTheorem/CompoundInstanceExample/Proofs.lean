import LCS.Herbrand.SHGTheorem.CompoundInstanceExample

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Substitution

helper /-- Example 7.6.4: the witness retains exactly the displayed source B. -/
theorem cInstExDerivation_source :
    cInstExDerivation.source = cInstExSkolemForm := rfl

proof_of cInstExCInstance_isCInstanceOf := ⟨cInstExDerivation, cInstExDerivation_source,
    cInstExDerivation_toFormula, cInstExDerivation_wellFormed⟩

end LCS.Herbrand.SHGTheorem
end
