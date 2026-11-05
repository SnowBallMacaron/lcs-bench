import LCS.CutElim.Interpolation.Equality.Axioms

section

namespace LCS.CutElim.Interpolation.Equality

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

open LCS.CutElim.Interpolation

open LCS.FirstOrder.Completeness

open LCS.FirstOrder.Equality

open LCS.FirstOrder.Equality.Completeness

open LCS.FirstOrder.Gentzen.Hintikka



helper theorem f_in_funcCongToSequent {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (f : L.funSymbols) (ss ts : Fin (L.funArity f) → Term L) :
    f ∈ sequentFunSymbolsList
      ((LKeEqualityAxiom.funcCong f ss ts).toSequent hL) := by
-- BEGIN PROOF
  unfold sequentFunSymbolsList LKeEqualityAxiom.toSequent
  rw [List.mem_eraseDups, List.mem_flatMap]
  refine ⟨FormulaN.eq_ hL (Term.func f ss) (Term.func f ts), ?_, ?_⟩
  · rw [List.mem_append]; right; exact List.mem_cons_self ..
  · unfold sequentFunSymbolsList.formulaFunSyms; rw [List.mem_append]; left
    unfold sequentFunSymbolsList.termFunSymbols
    exact List.mem_append_left _ (List.mem_cons_self ..)

helper theorem P_in_predCongToSequent {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (P : L.predSymbols) (ss ts : Fin (L.predArity P) → Term L) :
    P ∈ sequentPredSymbolsList
      ((LKeEqualityAxiom.predCong P ss ts).toSequent hL) := by
-- BEGIN PROOF
  unfold sequentPredSymbolsList LKeEqualityAxiom.toSequent
  rw [List.mem_eraseDups, List.mem_flatMap]
  refine ⟨FormulaN.predN P ts, ?_, ?_⟩
  · rw [List.mem_append]; right; exact List.mem_cons_self ..
  · unfold sequentPredSymbolsList.formulaPredSyms
    exact List.mem_cons_self ..









helper /-- LKe weakening: prepend a list of formulas to the antecedent.
If Γ → Δ is LKe-provable, then pfx ++ Γ → Δ is also LKe-provable
(stronger antecedent preserves provability via semantic validity). -/
theorem lkeProvable_weakenLeftList {L : Language}
    (pfx : List (FormulaN L)) (Γ Δ : List (FormulaN L))
    (h : lkeProvable (Sequent.mk Γ Δ)) :
    lkeProvable (Sequent.mk (pfx ++ Γ) Δ) := by
-- BEGIN PROOF
  have hvalid := lkeProvable_valid _ h
  apply lkeProvable_of_sequentValid
  intro M s hAnte
  exact hvalid M s (fun A hA => hAnte A (List.mem_append_right _ hA))

helper /-- Instantiate closedFunCongAxiom f with specific terms ss, ts,
producing the concrete function congruence sequent as LKe-provable.
The original folkProvable signature was unprovable because FOLK's
allLeft rule requires isFreeFor, which fails when the closed axiom's
bound variables 0..2n-1 clash with variables in the substitution terms.
The LKe version uses semantic validity: the instantiated sequent is
valid (from closedFunCongAxiom_eval), so it's LKe-provable via the
semantic cut. -/
theorem closedFunCongAxiom_instantiation {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols]
    (f : L.funSymbols) (ss ts : Fin (L.funArity f) → Term L) :
    lkeProvable (Sequent.mk
      ([closedFunCongAxiom hL f] ++
        (List.finRange (L.funArity f)).map (fun i => FormulaN.eq_ hL (ss i) (ts i)))
      [FormulaN.eq_ hL (Term.func f ss) (Term.func f ts)]) := by
-- BEGIN PROOF
  apply lkeProvable_of_sequentValid
  intro M s hAnte
  refine ⟨FormulaN.eq_ hL (Term.func f ss) (Term.func f ts), List.Mem.head _, ?_⟩
  simp only [formulaEvalN, termEval]
  congr 1; funext i
  have hEq := hAnte (FormulaN.eq_ hL (ss i) (ts i))
    (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
  simp only [formulaEvalN] at hEq
  exact hEq

helper /-- Instantiate closedPredCongAxiom P with specific terms ss, ts,
producing the concrete predicate congruence sequent as LKe-provable.
Same approach as closedFunCongAxiom_instantiation: uses semantic
validity to bypass the isFreeFor constraint. -/
theorem closedPredCongAxiom_instantiation {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.predSymbols]
    (P : L.predSymbols) (ss ts : Fin (L.predArity P) → Term L) :
    lkeProvable (Sequent.mk
      ([closedPredCongAxiom hL P] ++
        (List.finRange (L.predArity P)).map (fun i => FormulaN.eq_ hL (ss i) (ts i)) ++
        [FormulaN.predN P ss])
      [FormulaN.predN P ts]) := by
-- BEGIN PROOF
  apply lkeProvable_of_sequentValid
  intro M s hAnte
  refine ⟨FormulaN.predN P ts, List.Mem.head _, ?_⟩
  simp only [formulaEvalN]
  have hPred := hAnte (FormulaN.predN P ss)
    (List.mem_append_right _ (List.Mem.head _))
  simp only [formulaEvalN] at hPred
  have hEqs : ∀ i : Fin (L.predArity P), termEval M s (ss i) = termEval M s (ts i) := by
    intro i
    have := hAnte (FormulaN.eq_ hL (ss i) (ts i))
      (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)))
    simp only [formulaEvalN] at this
    exact this
  have : (fun i : Fin (L.predArity P) => termEval M s (ts i)) =
      (fun i => termEval M s (ss i)) := funext (fun i => (hEqs i).symm)
  rw [this]; exact hPred

helper /-- Instantiate the closed congruence axiom for built-in equality,
producing its concrete LKe equality-congruence sequent. As for the
function and named-predicate schemas, semantic validity avoids any
capture restriction on the four instantiating terms. -/
theorem closedEqCongAxiom_instantiation {L : Language}
    (hL : L.hasEquality = true) (s1 s2 t1 t2 : Term L) :
    lkeProvable (Sequent.mk
      ([closedEqCongAxiom hL] ++
        [FormulaN.eq_ hL s1 t1, FormulaN.eq_ hL s2 t2,
          FormulaN.eq_ hL s1 s2])
      [FormulaN.eq_ hL t1 t2]) := by
-- BEGIN PROOF
  apply lkeProvable_of_sequentValid
  intro M s hAnte
  refine ⟨FormulaN.eq_ hL t1 t2, List.Mem.head _, ?_⟩
  have h1 := hAnte (FormulaN.eq_ hL s1 t1) (by simp)
  have h2 := hAnte (FormulaN.eq_ hL s2 t2) (by simp)
  have h3 := hAnte (FormulaN.eq_ hL s1 s2) (by simp)
  simp only [formulaEvalN] at h1 h2 h3 ⊢
  rw [← h1, h3, h2]

end LCS.CutElim.Interpolation.Equality

end
