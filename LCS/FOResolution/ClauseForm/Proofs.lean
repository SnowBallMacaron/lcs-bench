import LCS.FOResolution.ClauseForm

namespace LCS.FOResolution.ClauseForm

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SyntaxN.Variables

namespace FOAtomCore





helper /-- Parsing an embedded atom succeeds and returns that atom. -/
theorem FOAtomCore.ofFormula?_toFormula {L : Language} (A : FOAtomCore L) :
    ofFormula? A.toFormula = some A := by
  cases A <;> rfl

helper /-- A successful atomic parse embeds back to the original formula. -/
theorem FOAtomCore.toFormula_ofFormula? {L : Language} {A : FormulaN L}
    {atom : FOAtomCore L} (h : ofFormula? A = some atom) :
    atom.toFormula = A := by
  cases A with
  | predN P args =>
      simp only [ofFormula?, Option.some.injEq] at h
      subst atom
      rfl
  | eq_ hL lhs rhs =>
      simp only [ofFormula?, Option.some.injEq] at h
      subst atom
      rfl
  | neg _ | conj _ _ | disj _ _ | impl _ _ | all _ _ | ex _ _ =>
      simp [ofFormula?] at h



helper /-- Proof-indexed parsing is a left inverse of the embedding. -/
theorem FOAtomCore.toFormula_ofFormula {L : Language} (A : FormulaN L)
    (hAtomic : FormulaN.isAtomic A = true) :
    (ofFormula A hAtomic).toFormula = A := by
  cases A with
  | predN _ _ | eq_ _ _ _ => rfl
  | neg _ | conj _ _ | disj _ _ | impl _ _ | all _ _ | ex _ _ =>
      simp [FormulaN.isAtomic] at hAtomic

end FOAtomCore

namespace FOClauseCore

helper /-- Atomicity of every clause literal follows from the carrier. -/
theorem FOClauseCore.allAtomic_derived {L : Language} (c : FOClauseCore L) :
    c.allAtomic := by
  intro lit _
  cases lit <;> apply FOAtomCore.toFormula_isAtomic

end FOClauseCore

open LCS.FirstOrder.Semantics

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.Semantics.Subformulae

proof_of clauseFormConstruction := by
  -- REPAIR(T8-29): proof pending
  sorry


proof_of exClauseOriginal_toEliminated := by
  have hA := (FormulaN.neg exClauseOriginal).toNNF_equiv M s
  have hE := exClauseEliminated.toNNF_equiv M s
  exact ⟨fun h => hE.2 (hA.1 h), fun h => hA.2 (hE.1 h)⟩


proof_of exClauseEliminated_toNNF := by
  exact ⟨(exClauseEliminated.toNNF_equiv M s).1,
    (exClauseEliminated.toNNF_equiv M s).2⟩


proof_of exClauseNNF_toSkolem := by
  -- REPAIR(T8-31): proof pending
  sorry


proof_of exClauseSkolem_toPrenex := by
  -- REPAIR(T8-31): proof pending
  sorry


proof_of exClausePrenex_toCNF := by
  simp only [exClausePrenex, exClauseCNF, formulaEvalN, LCS.FirstOrder.Basic.andM, LCS.FirstOrder.Basic.orM]
  constructor
  · intro h z x
    obtain ⟨h1, h23⟩ := h z x
    rcases h23 with ⟨h2, h3⟩ | h4
    · exact ⟨h1, Or.inl h2, Or.inl h3⟩
    · exact ⟨h1, Or.inr h4, Or.inr h4⟩
  · intro h z x
    obtain ⟨h1, h2, h3⟩ := h z x
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h4
    · rcases h3 with h3 | h4
      · exact Or.inl ⟨h2, h3⟩
      · exact Or.inr h4
    · exact Or.inr h4


proof_of exClauseCNF_toClauses := by
  -- REPAIR(T8-31): proof pending
  sorry


proof_of exClauseFormConversion_negOriginal := by
  have lift {L : Language} (A B : FormulaN L)
      (h : ∀ (M : Structure L) (s : Assignment M),
        formulaEvalN M A s ↔ formulaEvalN M B s) :
      satisfiableN A ↔ satisfiableN B := by
    constructor
    · rintro ⟨M, s, hs⟩
      exact ⟨M, s, (h M s).mp hs⟩
    · rintro ⟨M, s, hs⟩
      exact ⟨M, s, (h M s).mpr hs⟩
  have hLast : satisfiableN exClauseCNF ↔
      ∃ M : Structure exClauseFormLang, exClauseFormSatisfied M := by
    constructor
    · rintro ⟨M, s, hs⟩
      exact ⟨M, (exClauseCNF_toClauses M s).mp hs⟩
    · rintro ⟨M, hM⟩
      obtain ⟨a⟩ := M.carrierNonempty
      exact ⟨M, (fun _ => a), (exClauseCNF_toClauses M (fun _ => a)).mpr hM⟩
  exact (lift _ _ exClauseOriginal_toEliminated).trans
    ((lift _ _ exClauseEliminated_toNNF).trans
      (exClauseNNF_toSkolem.trans
        ((lift _ _ exClauseSkolem_toPrenex).trans
          ((lift _ _ exClausePrenex_toCNF).trans hLast))))


proof_of exClauseFormConversion_valid_iff_unsatisfiable := by
  classical
  constructor
  · intro hValid hModel
    obtain ⟨M, s, hNeg⟩ := exClauseFormConversion_negOriginal.mpr hModel
    exact hNeg (hValid M s)
  · intro hUnsat M s
    apply Classical.byContradiction
    intro hNeg
    exact hUnsat (exClauseFormConversion_negOriginal.mp ⟨M, s, hNeg⟩)


end LCS.FOResolution.ClauseForm
