import LCS.Herbrand.PrenexForm.Equivalences

namespace LCS.Herbrand.PrenexForm
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Equivalence
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN.Substitution

helper /-- Lemma 7.2.1 (d) (companion): forall x(A and B) equiv forall x A and forall x B. The universal quantifier distributes over conjunction. No side conditions. -/
theorem prenex_equiv_e_univ_conj_distrib {L : Language}
    (x : Nat) (A B : FormulaN L) :
    foLogEquivN
      (FormulaN.all x (FormulaN.conj A B))
      (FormulaN.conj (FormulaN.all x A) (FormulaN.all x B)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  exact ⟨fun h => ⟨fun a => (h a).1, fun a => (h a).2⟩,
         fun ⟨h1, h2⟩ a => ⟨h1 a, h2 a⟩⟩

helper /-- Lemma 7.2.1 (d) (companion): exists x(A or B) equiv exists x A or exists x B. The existential quantifier distributes over disjunction. No side conditions. -/
theorem prenex_equiv_e_ex_disj_distrib {L : Language}
    (x : Nat) (A B : FormulaN L) :
    foLogEquivN
      (FormulaN.ex x (FormulaN.disj A B))
      (FormulaN.disj (FormulaN.ex x A) (FormulaN.ex x B)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  exact ⟨fun ⟨a, h⟩ => h.elim (fun ha => Or.inl ⟨a, ha⟩) (fun hb => Or.inr ⟨a, hb⟩),
         fun h => h.elim (fun ⟨a, ha⟩ => ⟨a, Or.inl ha⟩) (fun ⟨a, hb⟩ => ⟨a, Or.inr hb⟩)⟩

proof_of lemma_7_2_1 := ⟨fun x A B hfree => prenex_equiv_a_univ_impl_left x A B hfree,
  -- BEGIN PROOF
     fun x A B hfree => prenex_equiv_a_ex_impl_left x A B hfree,
     fun x A B hfree => prenex_equiv_b_univ_impl_right x A B hfree,
     fun x A B hfree => prenex_equiv_b_ex_impl_right x A B hfree,
     fun x A => prenex_equiv_c_neg_all x A,
     fun x A => prenex_equiv_c_neg_ex x A,
     fun x A B hfree => prenex_equiv_d_univ_disj x A B hfree,
     fun x A B hfree => prenex_equiv_d_univ_conj x A B hfree,
     fun x A B hfree => prenex_equiv_d_ex_disj x A B hfree,
     fun x A B hfree => prenex_equiv_d_ex_conj x A B hfree,
     fun x A B => prenex_equiv_e_univ_conj_distrib x A B,
     fun x A B => prenex_equiv_e_ex_disj_distrib x A B,
     fun x y A hFor hNF => prenex_equiv_f_univ_rename x y A hFor hNF,
     fun x y A hFor hNF => prenex_equiv_f_ex_rename x y A hFor hNF⟩

end LCS.Herbrand.PrenexForm
