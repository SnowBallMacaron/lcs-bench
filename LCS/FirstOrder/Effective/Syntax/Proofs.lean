import LCS.FirstOrder.Effective.Syntax

namespace LCS.FirstOrder.Effective

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.Gentzen

open LCS.FirstOrder.SyntaxN.Variables LCS.FirstOrder.SyntaxN.Substitution

helper /-- The term occurrence test reflects membership in the term's free variables. -/
theorem termVarOccurs_correct {L : Language} (x : Nat) (t : Term L) :
    termVarOccurs x t = true ↔ x ∈ termFV t := by
  simp only [termVarOccurs, List.contains_iff_mem]
  induction t with
  | var y =>
    change x ∈ [y] ↔ x = y
    simp
  | const c =>
    change x ∈ ([] : List Nat) ↔ False
    simp
  | func f ts ih =>
    change x ∈ (List.ofFn fun j : Fin (L.funArity f) => j).foldl
      (fun acc j => acc ++ termVarIndicesList (ts j)) [] ↔ ∃ j, x ∈ termFV (ts j)
    rw [LCS.FirstOrder.Gentzen.Search.NoFunction.SearchState.mem_foldl_append_termVar]
    simp [ih]

helper /-- The formula occurrence test reflects membership in its free variables. -/
theorem formulaVarOccurs_correct {L : Language} (x : Nat) (A : FormulaN L) :
    formulaVarOccurs x A = true ↔ x ∈ formulaFVN A := by
  simpa [formulaVarOccurs] using
    LCS.FirstOrder.Gentzen.Search.NoFunction.SearchState.formulaFreeVarIndices_iff_formulaFVN A x

helper /-- The free-for test reflects the current normalized free-for predicate. -/
theorem freeForDecide_correct {L : Language} (t : Term L) (x : Nat) (A : FormulaN L) :
    freeForDecide t x A = true ↔ isFreeForN t x A := by
  induction A <;> simp_all [freeForDecide, isFreeForN, Bool.eq_false_iff, termVarOccurs_correct]

helper /-- The axiom test reflects the common-formula sequent axiom predicate. -/
theorem axiomDecide_correct {p : EffectivePresentation} (s : Sequent p.toLanguage) :
    axiomDecide s = true ↔ isAxiom s := by
  simp [axiomDecide, List.any_eq_true, formulaEq_correct, isAxiom]

helper /-- Definition 5.4.9 (effective companion): A successful split selects the
requested formula at its first occurrence, and reconstructs the original list
with every other occurrence in its original order. -/
theorem splitOccurrence_spec {p : EffectivePresentation} (A : FormulaN p.toLanguage)
    (xs : List (FormulaN p.toLanguage)) (r : OccurrenceSplit xs)
    (h : splitOccurrence A xs = some r) :
    r.focus = A ∧ A ∉ r.prefix ∧
      xs = r.prefix ++ [A] ++ r.suffix ∧ xs[r.index]? = some A := by
  have first : ∀ (ys : List (FormulaN p.toLanguage)) (s : OccurrenceSplit ys),
      splitOccurrence A ys = some s → s.focus = A ∧ A ∉ s.prefix := by
    intro ys
    induction ys with
    | nil => intro s hs; simp [splitOccurrence] at hs
    | cons B bs ih =>
      intro s hs
      by_cases hBA : formulaEq B A = true
      · simp [splitOccurrence, hBA] at hs
        subst s
        exact ⟨(formulaEq_correct B A).mp hBA, by simp⟩
      · cases he : splitOccurrence A bs with
        | none => simp [splitOccurrence, hBA, he] at hs
        | some t =>
          simp [splitOccurrence, hBA, he] at hs
          subst s
          have ht := ih t he
          have hne : B ≠ A := fun e => hBA ((formulaEq_correct B A).mpr e)
          exact ⟨ht.1, by simp [ht.2, Ne.symm hne]⟩
  obtain ⟨hf, hp⟩ := first xs r h
  refine ⟨hf, hp, ?_, ?_⟩
  · simpa [hf] using r.recombine
  · simpa [hf] using r.focus_at

helper /-- The scan fails exactly when the requested formula has no list occurrence. -/
theorem splitOccurrence_none_iff {p : EffectivePresentation} (A : FormulaN p.toLanguage)
    (xs : List (FormulaN p.toLanguage)) : splitOccurrence A xs = none ↔ A ∉ xs := by
  induction xs with
  | nil => simp [splitOccurrence]
  | cons B bs ih =>
    by_cases hBA : formulaEq B A = true
    · have hEq := (formulaEq_correct B A).mp hBA
      simp [splitOccurrence, hEq, formulaEq_correct]
    · have hne : B ≠ A := fun e => hBA ((formulaEq_correct B A).mpr e)
      simp only [splitOccurrence, hBA, Bool.false_eq_true, ↓reduceIte]
      cases he : splitOccurrence A bs <;> simp_all [Ne.symm hne]

helper /-- Successful extraction returns exactly the variable at the supplied cursor,
and its index is absent from the finite forbidden-variable list. -/
theorem freshVariableAt_spec {L : Language} (entries : Nat → Option (Term L))
    (cursor : Nat) (forbidden : List Nat) (x : Nat) :
    freshVariableAt entries cursor forbidden = some x ↔
      entries cursor = some (.var x) ∧ x ∉ forbidden := by
  cases he : entries cursor with
  | none => simp [freshVariableAt, he]
  | some t =>
    cases t with
    | var y =>
      by_cases hy : y ∈ forbidden
      · simp [freshVariableAt, he, hy]
        intro hxy
        subst x
        exact hy
      · simp [freshVariableAt, he, hy, eq_comm]
        intro hxy
        subst x
        exact hy
    | const c => simp [freshVariableAt, he]
    | func f ts => simp [freshVariableAt, he]

end LCS.FirstOrder.Effective
