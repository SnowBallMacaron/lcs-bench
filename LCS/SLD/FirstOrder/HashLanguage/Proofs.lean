import LCS.SLD.FirstOrder.HashLanguage

section

namespace LCS.SLD.FirstOrder

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SemanticsN

open LCS.FOResolution.ClauseForm

open LCS.FOResolution.Unification

open LCS.FOResolution.Method

open LCS.FOResolution.Method.Soundness

open LCS.FOResolution.Method.Completeness



helper /-- Since `hornClauses_to_formulaN`'s per-clause closures are sentences,
    their evaluation does not depend on the assignment. -/
theorem hornClauses_univClosure_eval_indep {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (A : FormulaN L) (h : FOHornClause L hNoEq)
    (s s' : Assignment M) :
    formulaEvalN M ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) A (h.toFOClause (hNoEq := by all_goals exact hNoEq)) ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) A h)) s ↔
    formulaEvalN M ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) A (h.toFOClause (hNoEq := by all_goals exact hNoEq)) ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) A h)) s' := by
-- BEGIN PROOF
  apply coincidenceLemmaN
  intro y hy
  exact absurd hy ((hornClauses_univClosure_sentence (hNoEq := by all_goals exact hNoEq)) A h y)

helper /-- Evaluation of the encoded formula decomposes over the conjunction:
    when the list of Horn clauses is non-empty, the encoded formula
    holds at `s` iff every clause's universal closure holds at `s`. -/
theorem hornClauses_to_formulaN_eval_iff {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (Afalsum : FormulaN L)
    (S : List (FOHornClause L hNoEq)) (hNe : S ≠ []) (s : Assignment M) :
    formulaEvalN M ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum S) s ↔
    ∀ h ∈ S, formulaEvalN M
      ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) Afalsum (h.toFOClause (hNoEq := by all_goals exact hNoEq)) ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum h)) s := by
-- BEGIN PROOF
  induction S with
  | nil => exact (hNe rfl).elim
  | cons hd tl ih =>
    cases tl with
    | nil =>
      simp only [hornClauses_to_formulaN]
      constructor
      · intro hH h hmem
        rw [List.mem_cons] at hmem
        cases hmem with
        | inl heq => subst heq; exact hH
        | inr hr => exact (List.not_mem_nil hr).elim
      · intro hAll
        exact hAll hd (List.mem_cons_self)
    | cons hd2 tl2 =>
      simp only [hornClauses_to_formulaN, formulaEvalN]
      have ihNe : (hd2 :: tl2 : List (FOHornClause L hNoEq)) ≠ [] := List.cons_ne_nil _ _
      have ihRes := ih ihNe
      constructor
      · intro hConj h hmem
        rw [List.mem_cons] at hmem
        cases hmem with
        | inl heq => subst heq; exact hConj.1
        | inr htl => exact ihRes.mp hConj.2 h htl
      · intro hAll
        refine ⟨hAll hd (List.mem_cons_self), ihRes.mpr ?_⟩
        intro h htl
        exact hAll h (List.mem_cons_of_mem hd htl)

proof_of satisfiableN_hornClauseSet_iff := by
  -- BEGIN PROOF
    constructor
    · intro hNotSat
      unfold FOHornClauseSet.isUnsatisfiable FOClauseSet.isUnsatisfiable
      intro ⟨M, hM⟩
      apply hNotSat
      refine ⟨M, fun _ => Classical.choice M.carrierNonempty, ?_⟩
      rw [(hornClauses_to_formulaN_eval_iff (hNoEq := by all_goals exact hNoEq)) _ _ _ hNe]
      intro h hmem
      exact FOClause.universalClosure_of_validIn hNoEq M _
        (hM _ ⟨h, hmem, rfl⟩) Afalsum (hornClauseVarsList hNoEq Afalsum h) _
    · intro hUnsat ⟨M, s, hsat⟩
      apply hUnsat
      refine ⟨M, ?_⟩
      intro C hC
      obtain ⟨h, hmem, heq⟩ := hC
      rw [(hornClauses_to_formulaN_eval_iff (hNoEq := by all_goals exact hNoEq)) _ _ _ hNe] at hsat
      have hh := hsat h hmem
      subst heq
      have hh_all : ∀ s'', formulaEvalN M
          ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) Afalsum (h.toFOClause (hNoEq := by all_goals exact hNoEq)) ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum h)) s'' := by
        intro s''
        exact ((hornClauses_univClosure_eval_indep (hNoEq := by all_goals exact hNoEq)) M Afalsum h s s'').mp hh
      exact FOClause.validIn_of_universalClosure hNoEq M Afalsum _
        (hornClauseVarsList hNoEq Afalsum h)
        (hornClauseVarsList_covers_clause hNoEq Afalsum h) hh_all














helper /-- Lifting a term preserves its free-variable set exactly. -/
theorem hashLiftTerm_termFV {L : Language} (t : Term L) :
    termFV (hashLiftTerm t) = termFV t :=
  LCS.Herbrand.SHGTheorem.Herbrand.liftTermSkolem_termFV t





helper /-- Lifting preserves the number of existential quantifiers exactly. -/
theorem hashLiftFormula_countExN {L : Language} (A : FormulaN L) :
    LCS.Herbrand.SHGTheorem.Herbrand.countExN (hashLiftFormula A) =
      LCS.Herbrand.SHGTheorem.Herbrand.countExN A :=
  LCS.Herbrand.SHGTheorem.Herbrand.liftFormulaSkolem_countExN A









helper /-- Equality of lifted terms is equivalent to equality of their sources. -/
theorem hashLiftTerm_eq_iff {L : Language} (t u : Term L) :
    hashLiftTerm t = hashLiftTerm u ↔ t = u :=
  ⟨fun h => hashLiftTerm_injective h, congrArg hashLiftTerm⟩



helper /-- Equality of lifted formulae is equivalent to equality of their sources. -/
theorem hashLiftFormula_eq_iff {L : Language} (A B : FormulaN L) :
    hashLiftFormula A = hashLiftFormula B ↔ A = B :=
  ⟨fun h => hashLiftFormula_injective h, congrArg hashLiftFormula⟩











helper /-- The literal lift is injective. -/
theorem hashLiftLiteral_injective {L : Language} (hNoEq : L.withoutEquality)  :
    Function.Injective (@hashLiftLiteral L (by all_goals exact hNoEq)) := by
  intro l₁ l₂ h
  cases l₁ <;> cases l₂
  · exact congrArg FOLiteralCore.pos
      ((hashLiftAtom_injective (hNoEq := by all_goals exact hNoEq)) (FOLiteralCore.pos.inj h))
  · cases h
  · cases h
  · exact congrArg FOLiteralCore.neg
      ((hashLiftAtom_injective (hNoEq := by all_goals exact hNoEq)) (FOLiteralCore.neg.inj h))



helper /-- Pointwise lifting is injective on lists of formulae. -/
theorem hashLiftFormulaList_injective {L : Language} :
    Function.Injective (List.map (@hashLiftFormula L)) := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons => cases h
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil => cases h
      | cons y ys =>
        have h' := List.cons.inj h
        rw [hashLiftFormula_injective h'.1, ih h'.2]



helper /-- Equality of lifted Horn clauses is equivalent to source equality. -/
theorem hashLiftHornClause_eq_iff {L : Language} (hNoEq : L.withoutEquality)
    (c d : FOHornClause L hNoEq) :
    (hashLiftHornClause (hNoEq := by all_goals exact hNoEq)) c = (hashLiftHornClause (hNoEq := by all_goals exact hNoEq)) d ↔ c = d :=
  ⟨fun h => (hashLiftHornClause_injective (hNoEq := by all_goals exact hNoEq)) h, congrArg (hashLiftHornClause (hNoEq := by all_goals exact hNoEq))⟩

helper /-- Head extraction commutes exactly with the Horn-clause lift. -/
theorem hashLiftHornClause_headAtom {L : Language} (hNoEq : L.withoutEquality)  (c : FOHornClause L hNoEq) :
    (((hashLiftHornClause (hNoEq := by all_goals exact hNoEq)) c).headAtom (hNoEq := by all_goals exact hNoEq)) =
      c.headAtom.map hashLiftFormula := by
  cases c <;>
    simp [hashLiftHornClause, FOHornClause.headAtom,
      FOHornClause.headFOAtom, FOHornClauseCore.headFOAtom, (hashLiftAtom_toFormula (hNoEq := by all_goals exact hNoEq))]

helper /-- Body extraction commutes with lifting up to permutation (SQ16). -/
theorem hashLiftHornClause_bodyAtoms {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) :
    ((hashLiftHornClause hNoEq c).bodyAtoms (L := HashLanguage L) hNoEq).Perm
      ((c.bodyAtoms hNoEq).map hashLiftFormula) := by
  have hp := finset_toList_image_perm (hashLiftAtom hNoEq)
    (hashLiftAtom_injective hNoEq)
  cases c <;>
    simp only [hashLiftHornClause, FOHornClause.bodyAtoms, FOHornClause.bodyFOAtoms,
      FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body]
  · rename_i head body
    simpa [List.map_map, Function.comp_def, hashLiftAtom_toFormula] using (hp body).map FOAtomCore.toFormula
  · simp [finset_toList_empty]
  · rename_i body
    simpa [List.map_map, Function.comp_def, hashLiftAtom_toFormula] using (hp body).map FOAtomCore.toFormula

helper /-- Structural head extraction commutes with the Horn-clause lift. -/
theorem hashLiftHornClause_headFOAtom {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) :
    (((hashLiftHornClause (hNoEq := by all_goals exact hNoEq)) c).headFOAtom (hNoEq := by all_goals exact hNoEq)) =
      c.headFOAtom.map (hashLiftAtom (hNoEq := by all_goals exact hNoEq)) := by
  cases c <;> rfl

helper /-- Structural body extraction commutes up to permutation (SQ16). -/
theorem hashLiftHornClause_bodyFOAtoms {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) :
    ((hashLiftHornClause hNoEq c).bodyFOAtoms (L := HashLanguage L) hNoEq).Perm
      ((c.bodyFOAtoms hNoEq).map (hashLiftAtom hNoEq)) := by
  cases c <;>
    simp only [hashLiftHornClause, FOHornClause.bodyFOAtoms,
      FOHornClauseCore.bodyFOAtoms, FOHornClauseCore.body]
  · exact finset_toList_image_perm _ (hashLiftAtom_injective hNoEq) _
  · simp [finset_toList_empty]
  · exact finset_toList_image_perm _ (hashLiftAtom_injective hNoEq) _

helper /-- The "all Horn atoms are atomic" side condition is reflected and
    preserved exactly by lifting. -/
theorem hashLiftHornClause_allAtomsAtomic_iff {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) :
    (((hashLiftHornClause (hNoEq := by all_goals exact hNoEq)) c).allAtomsAtomic (hNoEq := by all_goals exact hNoEq)) ↔ (c.allAtomsAtomic (hNoEq := by all_goals exact hNoEq)) := by
  exact ⟨fun _ => (c.allAtomsAtomic_derived (hNoEq := by all_goals exact hNoEq)),
    fun _ => (((hashLiftHornClause (hNoEq := by all_goals exact hNoEq)) c).allAtomsAtomic_derived (hNoEq := by all_goals exact hNoEq))⟩



helper /-- Literal membership in a lifted standard clause reflects source
    membership exactly. -/
theorem hashLiftLiteral_mem_hashLiftFOClause_iff {L : Language} (hNoEq : L.withoutEquality)
    (lit : FOLiteral L hNoEq) (C : FOClause L hNoEq) :
    (hashLiftLiteral (hNoEq := by all_goals exact hNoEq)) lit ∈ (hashLiftFOClause (hNoEq := by all_goals exact hNoEq)) C ↔ lit ∈ C := by
  unfold hashLiftFOClause
  constructor
  · intro h
    rw [List.mem_map] at h
    obtain ⟨lit', hlit', heq⟩ := h
    have : lit' = lit := (hashLiftLiteral_injective (hNoEq := by all_goals exact hNoEq)) heq
    simpa [this] using hlit'
  · intro h
    exact List.mem_map.mpr ⟨lit, h, rfl⟩

helper /-- Literal membership in a Horn clause's standard translation is
    preserved and reflected by lifting. -/
theorem hashLiftLiteral_mem_hashLiftHornClause_iff {L : Language} (hNoEq : L.withoutEquality)
    (lit : FOLiteral L hNoEq) (c : FOHornClause L hNoEq) :
    (hashLiftLiteral (hNoEq := by all_goals exact hNoEq)) lit ∈ (((hashLiftHornClause (hNoEq := by all_goals exact hNoEq)) c).toFOClause (hNoEq := by all_goals exact hNoEq)) ↔
      lit ∈ (c.toFOClause (hNoEq := by all_goals exact hNoEq)) := by
  rw [(hashLiftHornClause_toFOClause hNoEq c).mem_iff,
    (hashLiftLiteral_mem_hashLiftFOClause_iff (hNoEq := by all_goals exact hNoEq))]

helper /-- Body-atom membership is preserved and reflected by lifting. -/
theorem hashLiftFormula_mem_hashLiftBodyAtoms_iff {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (c : FOHornClause L hNoEq) :
    hashLiftFormula A ∈ (((hashLiftHornClause (hNoEq := by all_goals exact hNoEq)) c).bodyAtoms (hNoEq := by all_goals exact hNoEq)) ↔
      A ∈ (c.bodyAtoms (hNoEq := by all_goals exact hNoEq)) := by
  rw [(hashLiftHornClause_bodyAtoms hNoEq c).mem_iff]
  constructor
  · intro h
    rw [List.mem_map] at h
    obtain ⟨B, hB, heq⟩ := h
    have : B = A := hashLiftFormula_injective heq
    simpa [this] using hB
  · intro h
    exact List.mem_map.mpr ⟨A, h, rfl⟩













helper /-- Literal-variable sets are unchanged by lifting. -/
theorem hashLiftLiteral_vars {L : Language} (hNoEq : L.withoutEquality)  (lit : FOLiteral L hNoEq) :
    ((hashLiftLiteral (hNoEq := by all_goals exact hNoEq)) lit).vars = lit.vars := by
  cases lit <;> apply (hashLiftAtom_vars (hNoEq := by all_goals exact hNoEq))

helper /-- Clause free-variable sets are unchanged by lifting. -/
theorem hashLiftFOClause_clauseFV {L : Language} (hNoEq : L.withoutEquality)  (C : FOClause L hNoEq) :
    (clauseFV (hNoEq := by all_goals exact hNoEq)) ((hashLiftFOClause (hNoEq := by all_goals exact hNoEq)) C) = (clauseFV (hNoEq := by all_goals exact hNoEq)) C := by
  funext x
  apply propext
  constructor
  · rintro ⟨lit', hlit', hx⟩
    unfold hashLiftFOClause at hlit'
    rw [List.mem_map] at hlit'
    obtain ⟨lit, hlit, rfl⟩ := hlit'
    exact ⟨lit, hlit, ((hashLiftLiteral_vars (hNoEq := by all_goals exact hNoEq)) lit) ▸ hx⟩
  · rintro ⟨lit, hlit, hx⟩
    refine ⟨(hashLiftLiteral (hNoEq := by all_goals exact hNoEq)) lit, List.mem_map.mpr ⟨lit, hlit, rfl⟩, ?_⟩
    exact ((hashLiftLiteral_vars (hNoEq := by all_goals exact hNoEq)) lit).symm ▸ hx

helper /-- The literal-based free-variable set from soundness is also unchanged. -/
theorem hashLiftFOClause_freeVars {L : Language} (hNoEq : L.withoutEquality)  (C : FOClause L hNoEq) :
    (FOClause.freeVars (hNoEq := by all_goals exact hNoEq)) ((hashLiftFOClause (hNoEq := by all_goals exact hNoEq)) C) = (FOClause.freeVars (hNoEq := by all_goals exact hNoEq)) C := by
  funext x
  apply propext
  constructor
  · rintro ⟨lit', hlit', hx⟩
    unfold hashLiftFOClause at hlit'
    rw [List.mem_map] at hlit'
    obtain ⟨lit, hlit, rfl⟩ := hlit'
    refine ⟨lit, hlit, ?_⟩
    dsimp only [FOLiteral.formula] at *
    rw [(hashLiftLiteral_formula (hNoEq := by all_goals exact hNoEq)), hashLiftFormula_formulaFVN] at hx
    exact hx
  · rintro ⟨lit, hlit, hx⟩
    refine ⟨(hashLiftLiteral (hNoEq := by all_goals exact hNoEq)) lit,
      List.mem_map.mpr ⟨lit, hlit, rfl⟩, ?_⟩
    dsimp only [FOLiteral.formula] at *
    rw [(hashLiftLiteral_formula (hNoEq := by all_goals exact hNoEq)), hashLiftFormula_formulaFVN]
    exact hx

helper /-- The translated Horn clause therefore has exactly the same FV set
    before and after lifting. -/
theorem hashLiftHornClause_clauseFV {L : Language} (hNoEq : L.withoutEquality)  (c : FOHornClause L hNoEq) :
    (clauseFV (hNoEq := by all_goals exact hNoEq)) (((hashLiftHornClause (hNoEq := by all_goals exact hNoEq)) c).toFOClause (hNoEq := by all_goals exact hNoEq)) =
      (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) := by
  rw [← hashLiftFOClause_clauseFV hNoEq (c.toFOClause hNoEq)]
  funext x
  apply propext
  constructor <;> rintro ⟨lit, hm, hx⟩
  · exact ⟨lit, (hashLiftHornClause_toFOClause hNoEq c).mem_iff.mp hm, hx⟩
  · exact ⟨lit, (hashLiftHornClause_toFOClause hNoEq c).mem_iff.mpr hm, hx⟩

















helper /-- The lifted specification source is in NNF. -/
theorem hashLiftSkolemSpec_source_isNNF {L : Language}
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L) :
    (hashLiftSkolemSpec spec).source.isNNF :=
  (hashLiftSkolemSpec spec).hNNF

helper /-- The lifted specification source is rectified. -/
theorem hashLiftSkolemSpec_source_isRectified {L : Language}
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L) :
    LCS.FirstOrder.Semantics.Subformulae.isRectified
      (hashLiftSkolemSpec spec).source :=
  (hashLiftSkolemSpec spec).hRect

helper /-- The lifted specification source is closed. -/
theorem hashLiftSkolemSpec_source_isClosed {L : Language}
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L) :
    LCS.FirstOrder.SyntaxN.Variables.FormulaN.isClosed
      (hashLiftSkolemSpec spec).source :=
  (hashLiftSkolemSpec spec).hSentence

helper /-- Free variables of the lifted specification source agree exactly
    with those of the source specification. -/
theorem hashLiftSkolemSpec_source_formulaFVN {L : Language}
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L) :
    LCS.FirstOrder.SyntaxN.Variables.formulaFVN
        (hashLiftSkolemSpec spec).source =
      LCS.FirstOrder.SyntaxN.Variables.formulaFVN spec.source :=
  hashLiftFormula_formulaFVN spec.source

helper /-- Existential-quantifier count is unchanged in the lifted specification. -/
theorem hashLiftSkolemSpec_source_countExN {L : Language}
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L) :
    LCS.Herbrand.SHGTheorem.Herbrand.countExN
        (hashLiftSkolemSpec spec).source =
      LCS.Herbrand.SHGTheorem.Herbrand.countExN spec.source :=
  hashLiftFormula_countExN spec.source



helper /-- In particular, the no-allocation (`n = 0`) invariant is reflected
    and preserved exactly by specification lifting. -/
theorem hashLiftSkolemSpec_n_eq_zero_iff {L : Language}
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L) :
    (hashLiftSkolemSpec spec).n = 0 ↔ spec.n = 0 := by
  rw [hashLiftSkolemSpec_n]











































helper /-- The official term-FV set of a lowered ground term is contained in
    the singleton `{k}`. -/
theorem hashLowerTerm_termFV_subset_singleton {L : Language} (k : Nat)
    (t : Term (HashLanguage L))
    (hGround : ∀ x, ¬ termVars t x) :
    ∀ x, termFV (hashLowerTerm k t) x → x = k := by
  intro x hx
  exact hashLowerTerm_termVars_subset_singleton k t hGround x
    ((termVars_iff_termFV _ _).mpr hx)



helper /-- Free formula variables are always syntactic term-variable
    occurrences; binders can only remove occurrences from `formulaFVN`. -/
theorem formulaFVN_subset_formulaVars {L : Language} (A : FormulaN L) :
    ∀ x, LCS.FirstOrder.SyntaxN.Variables.formulaFVN A x →
      formulaVars A x := by
  induction A with
  | predN P args =>
    intro x hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, (termVars_iff_termFV _ _).mpr hi⟩
  | eq_ hL t₁ t₂ =>
    intro x hx
    exact hx.elim
      (fun h => Or.inl ((termVars_iff_termFV _ _).mpr h))
      (fun h => Or.inr ((termVars_iff_termFV _ _).mpr h))
  | neg A ih => exact ih
  | conj A B ihA ihB =>
    intro x hx
    exact hx.elim (fun h => Or.inl (ihA x h))
      (fun h => Or.inr (ihB x h))
  | disj A B ihA ihB =>
    intro x hx
    exact hx.elim (fun h => Or.inl (ihA x h))
      (fun h => Or.inr (ihB x h))
  | impl A B ihA ihB =>
    intro x hx
    exact hx.elim (fun h => Or.inl (ihA x h))
      (fun h => Or.inr (ihB x h))
  | all y A ih =>
    intro x hx
    exact ih x hx.1
  | ex y A ih =>
    intro x hx
    exact ih x hx.1

helper /-- Consequently the semantic free-variable set of a lowered ground
    formula is also contained in `{k}`. -/
theorem hashLowerFormula_formulaFVN_subset_singleton {L : Language}
    (k : Nat) (A : FormulaN (HashLanguage L))
    (hGround : ∀ x, ¬ formulaVars A x) :
    ∀ x, LCS.FirstOrder.SyntaxN.Variables.formulaFVN
        (hashLowerFormula k A) x → x = k := by
  intro x hx
  exact hashLowerFormula_formulaVars_subset_singleton k A hGround x
    (formulaFVN_subset_formulaVars _ x hx)

end LCS.SLD.FirstOrder

end
