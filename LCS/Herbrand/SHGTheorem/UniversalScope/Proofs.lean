import LCS.Herbrand.SHGTheorem.UniversalScope

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Substitution

proof_of usExScopeOfExistsY := by
  -- BEGIN PROOF
    simp only [universalScope, usExFormula, universalScopeAux,
               usExExistsYSubformula,
               List.mem_append, List.mem_cons, List.mem_nil_iff,
               Prod.mk.injEq, List.nil_append, or_false,
               List.append_assoc]
    right; right; right; right; left; trivial

proof_of usExScopeOfExistsU := by
  -- BEGIN PROOF
    simp only [universalScope, usExFormula, universalScopeAux,
               usExExistsUSubformula,
               List.mem_append, List.mem_cons, List.mem_nil_iff,
               Prod.mk.injEq, List.nil_append, or_false,
               List.append_assoc]
    right; right; right; right; right; right; right; right; right; right; left; trivial

proof_of usExScopeOfExistsW := by
  -- BEGIN PROOF
    simp only [universalScope, usExFormula, universalScopeAux,
               usExExistsWSubformula,
               List.mem_append, List.mem_cons, List.mem_nil_iff,
               Prod.mk.injEq, List.nil_append, or_false,
               List.append_assoc]
    right; right; right; right; right; right; right; right; right; right; right; right; left; trivial

end LCS.Herbrand.SHGTheorem
end
