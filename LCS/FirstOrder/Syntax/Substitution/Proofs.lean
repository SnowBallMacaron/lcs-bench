import LCS.FirstOrder.Syntax.Substitution

open LCS.FirstOrder.Basic

open LCS.FirstOrder.Syntax

namespace LCS.FirstOrder.Syntax.Substitution

helper /-- Example 5.2.4: f(x)[g(y)/x] = f(g(y)), demonstrating term substitution.
Here f(x) is the term f applied to variable x = 0, and we substitute g(y) for x. -/
def substExample_5_2_4_term_subst : Term exSubstLanguage :=
  termSubst
    (Term.func ExSubstFunc.f (fun _ => Term.var 0))
    substExample_5_2_4_term_gy
    0

helper /-- Example 5.2.4: A[g(y)/y] = forall x(P(x) imp Q(x, f(g(y)))),
demonstrating formula substitution for the free variable y = 1. -/
def substExample_5_2_4_free_var_subst : Formula exSubstLanguage :=
  formulaSubst substExample_5_2_4_formula substExample_5_2_4_term_gy 1

helper /-- Example 5.2.4: A[g(y)/x] = A, demonstrating that substitution for the
bound variable x = 0 leaves the formula unchanged because x is bound by forall x. -/
def substExample_5_2_4_bound_var_subst : Formula exSubstLanguage :=
  formulaSubst substExample_5_2_4_formula substExample_5_2_4_term_gy 0

proof_of substExample_5_2_4_term_subst_eq := rfl


proof_of substExample_5_2_4_free_var_subst_eq := by
  simp [substExample_5_2_4_formula, formulaSubst, termSubst]
  congr 3
  funext j
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl


proof_of substExample_5_2_4_bound_var_subst_eq := rfl


proof_of captureExample_5_2_5_after_eq := by
  simp [captureExample_5_2_5_before, formulaSubst]
  congr 2
  funext j
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl


proof_of captureExample_5_2_5_isSentence := by
  change Variables.formulaFV
    (formulaSubst captureExample_5_2_5_before (Term.var 0) 1) = ∅
  rw [captureExample_5_2_5_after_eq]
  funext n
  apply propext
  dsimp [Variables.formulaFV, termFV, Set.iUnion, Set.diff, Set.singleton,
    Set.empty, arithLanguage]
  simp


proof_of freeForExample_5_2_6_positive := by
  dsimp [isFreeFor, substExample_5_2_4_formula, freeForExample_5_2_6_formulaB,
    termFV, Set.iUnion, Set.singleton, Membership.mem, exSubstLanguage]
  simp only [Fin.exists_fin_one]
  decide


proof_of freeForExample_5_2_6_capture := by
  dsimp [isFreeFor, substExample_5_2_4_formula, freeForExample_5_2_6_formulaB,
    termFV, Set.iUnion, Set.singleton, Membership.mem, exSubstLanguage]
  simp only [Fin.exists_fin_one]
  decide


proof_of freeForExample_5_2_6_nested := by
  dsimp [isFreeFor, substExample_5_2_4_formula, freeForExample_5_2_6_formulaB,
    termFV, Set.iUnion, Set.singleton, Membership.mem, exSubstLanguage]
  simp only [Fin.exists_fin_one]
  decide


proof_of freeForExample_5_2_6_trivial := by
  dsimp [isFreeFor, substExample_5_2_4_formula, freeForExample_5_2_6_formulaB,
    termFV, Set.iUnion, Set.singleton, Membership.mem, exSubstLanguage]
  simp only [Fin.exists_fin_one]
  decide


end LCS.FirstOrder.Syntax.Substitution
