import LCS.FirstOrder.SyntaxN.Variables

namespace LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

helper /-- A FormulaN has no free-bound variable
overlap — FV(A) and BV(A) are disjoint. -/
def formulaNoFreeBoundN {L : Language} (A : FormulaN L) : Prop :=
  ∀ x : Nat, ¬(x ∈ formulaFVN A ∧ x ∈ formulaBVN A)

namespace FormulaN



end FormulaN

end LCS.FirstOrder.SyntaxN.Variables
