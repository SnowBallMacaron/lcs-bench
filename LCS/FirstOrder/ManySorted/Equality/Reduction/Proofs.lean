import LCS.FirstOrder.ManySorted.Equality.Reduction

namespace LCS.FirstOrder.ManySorted.Equality.Reduction

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.ManySorted

open LCS.FirstOrder.ManySorted.Gentzen

proof_of msTheoryTranslate_mem := by
  -- BEGIN PROOF
    unfold msTheoryTranslate
    rw [List.mem_map]
    constructor
    · rintro ⟨A, hA, hB⟩
      exact ⟨A, hA, hB.symm⟩
    · rintro ⟨A, hA, hB⟩
      exact ⟨A, hA, hB.symm⟩


proof_of msTermTranslate_subst_comm := by
  -- BEGIN PROOF
    intro s r
    induction r with
    | var s' i =>
      by_cases hsu : s' = u
      · subst hsu
        by_cases hix : i = x
        · subst hix
          -- `(s', i) = (u, x)`: both sides reduce to `translate t`.
          show msTermTranslate L ν (if h : s' = s' then (if i = i then h.symm ▸ t
              else MSTerm.var s' i) else MSTerm.var s' i) = _
          rw [dif_pos rfl, if_pos rfl]
          show msTermTranslate L ν t = termSubst (Term.var (ν (s', i))) _ (ν (s', i))
          rw [termSubst]; rw [if_pos rfl]
        · -- same sort, different index: ν (s', i) ≠ ν (u, x) since i ≠ x.
          have hni : ν (s', i) ≠ ν (s', x) := fun h => hix (congrArg Prod.snd (hν h))
          show msTermTranslate L ν (if h : s' = s' then (if i = x then h.symm ▸ t
              else MSTerm.var s' i) else MSTerm.var s' i) = _
          rw [dif_pos rfl, if_neg hix]
          show Term.var (ν (s', i)) = termSubst (Term.var (ν (s', i))) _ (ν (s', x))
          rw [termSubst]; rw [if_neg hni]
      · -- different sort: ν (s', i) ≠ ν (u, x) since s' ≠ u.
        have hni : ν (s', i) ≠ ν (u, x) := fun h => hsu (congrArg Prod.fst (hν h))
        show msTermTranslate L ν (if h : s' = u then (if i = x then h.symm ▸ t
            else MSTerm.var s' i) else MSTerm.var s' i) = _
        rw [dif_neg hsu]
        show Term.var (ν (s', i)) = termSubst (Term.var (ν (s', i))) _ (ν (u, x))
        rw [termSubst]; rw [if_neg hni]
    | const s' c =>
      simp only [msTermSubst, msTermTranslate, termSubst]
    | func f ts ih =>
      simp only [msTermSubst, msTermTranslate, termSubst]
      congr 1
      funext i
      exact ih i


proof_of termFV_msTermTranslate := by
  -- BEGIN PROOF
    intro s r
    induction r with
    | var s' i =>
      intro n
      -- termFV (var (ν (s',i))) n  ↔  n = ν (s', i);
      -- msTermFV (var s' i) = Set.singleton (s', i).
      show (n = ν (s', i)) ↔ ∃ p : MSVar L, p ∈ msTermFV (MSTerm.var s' i) ∧ ν p = n
      constructor
      · intro h; exact ⟨(s', i), rfl, h.symm⟩
      · rintro ⟨p, hp, hpn⟩
        have : p = (s', i) := hp
        subst this; exact hpn.symm
    | const s' c =>
      intro n
      constructor
      · intro h; exact absurd h id
      · rintro ⟨p, hp, _⟩; exact absurd hp id
    | func f ts ih =>
      intro n
      -- termFV (func f …) n = ∃ j, termFV (translate (ts j)) n;
      -- msTermFV (func f ts) = iUnion (msTermFV ∘ ts).
      show (∃ j, n ∈ termFV (msTermTranslate L ν (ts j))) ↔
          ∃ p : MSVar L, (∃ j, p ∈ msTermFV (ts j)) ∧ ν p = n
      constructor
      · rintro ⟨i, hi⟩
        obtain ⟨p, hp, hpn⟩ := (ih i n).mp hi
        exact ⟨p, ⟨i, hp⟩, hpn⟩
      · rintro ⟨p, ⟨i, hp⟩, hpn⟩
        exact ⟨i, (ih i n).mpr ⟨p, hp, hpn⟩⟩


proof_of formulaFVN_msFormulaTranslate_subset := by
  -- BEGIN PROOF
    induction A with
    | falsum =>
      intro h
      -- translate ⊥ = D ∧ ¬D with D = predN (domain someSort) (fun _ => var (ν someSort 0)).
      -- formulaFVN = (∃ j, termFV (var (ν someSort 0)) n) on both conjuncts.
      rcases h with hD | hD <;>
      · obtain ⟨_, heq⟩ := hD
        exact Or.inr heq
    | pred P ts =>
      intro h
      obtain ⟨i, hi⟩ := h
      obtain ⟨p, hp, hpn⟩ := (termFV_msTermTranslate ν (ts i) n).mp hi
      exact Or.inl ⟨p, ⟨i, hp⟩, hpn⟩
    | eq_ hL s' t1 t2 =>
      intro h
      rcases h with h | h
      · obtain ⟨p, hp, hpn⟩ := (termFV_msTermTranslate ν t1 n).mp h
        exact Or.inl ⟨p, Or.inl hp, hpn⟩
      · obtain ⟨p, hp, hpn⟩ := (termFV_msTermTranslate ν t2 n).mp h
        exact Or.inl ⟨p, Or.inr hp, hpn⟩
    | conj A B ihA ihB =>
      intro h
      rcases h with h | h
      · rcases ihA h with ⟨p, hp, hpn⟩ | hsent
        · exact Or.inl ⟨p, Or.inl hp, hpn⟩
        · exact Or.inr hsent
      · rcases ihB h with ⟨p, hp, hpn⟩ | hsent
        · exact Or.inl ⟨p, Or.inr hp, hpn⟩
        · exact Or.inr hsent
    | disj A B ihA ihB =>
      intro h
      rcases h with h | h
      · rcases ihA h with ⟨p, hp, hpn⟩ | hsent
        · exact Or.inl ⟨p, Or.inl hp, hpn⟩
        · exact Or.inr hsent
      · rcases ihB h with ⟨p, hp, hpn⟩ | hsent
        · exact Or.inl ⟨p, Or.inr hp, hpn⟩
        · exact Or.inr hsent
    | impl A B ihA ihB =>
      intro h
      rcases h with h | h
      · rcases ihA h with ⟨p, hp, hpn⟩ | hsent
        · exact Or.inl ⟨p, Or.inl hp, hpn⟩
        · exact Or.inr hsent
      · rcases ihB h with ⟨p, hp, hpn⟩ | hsent
        · exact Or.inl ⟨p, Or.inr hp, hpn⟩
        · exact Or.inr hsent
    | equiv_ A B ihA ihB =>
      intro h
      -- equiv_ ↦ conj (impl A' B') (impl B' A'); FV is (FV A' ∪ FV B') ∪ (FV B' ∪ FV A').
      rcases h with (h | h) | (h | h)
      · rcases ihA h with ⟨p, hp, hpn⟩ | hsent
        · exact Or.inl ⟨p, Or.inl hp, hpn⟩
        · exact Or.inr hsent
      · rcases ihB h with ⟨p, hp, hpn⟩ | hsent
        · exact Or.inl ⟨p, Or.inr hp, hpn⟩
        · exact Or.inr hsent
      · rcases ihB h with ⟨p, hp, hpn⟩ | hsent
        · exact Or.inl ⟨p, Or.inr hp, hpn⟩
        · exact Or.inr hsent
      · rcases ihA h with ⟨p, hp, hpn⟩ | hsent
        · exact Or.inl ⟨p, Or.inl hp, hpn⟩
        · exact Or.inr hsent
    | neg A ih =>
      intro h
      exact ih h
    | all s x B ih =>
      intro h
      -- translate (all s x B) = ∀_{ν(s,x)} (D_s(x_{ν(s,x)}) ⊃ B').
      -- formulaFVN n = (FV(D_s) n ∨ FV B' n) ∧ ¬ (n = ν (s, x)).
      obtain ⟨hmem, hne⟩ := h
      have hne' : n ≠ ν (s, x) := fun hc => hne hc
      rcases hmem with hD | hB'
      · -- n ∈ FV of D_s(x_{ν(s,x)}) = {ν (s, x)} : contradicts hne'.
        obtain ⟨_, hDeq⟩ := hD
        exact absurd hDeq hne'
      · rcases ih hB' with ⟨p, hp, hpn⟩ | hsent
        · -- p ∈ FV B, and ν p = n ≠ ν (s, x), so p ≠ (s, x) by injectivity.
          refine Or.inl ⟨p, ⟨hp, ?_⟩, hpn⟩
          intro hsing
          have hpx : p = (s, x) := hsing
          rw [hpx] at hpn; exact hne' hpn.symm
        · exact Or.inr hsent
    | ex s x B ih =>
      intro h
      obtain ⟨hmem, hne⟩ := h
      have hne' : n ≠ ν (s, x) := fun hc => hne hc
      rcases hmem with hD | hB'
      · obtain ⟨_, hDeq⟩ := hD
        exact absurd hDeq hne'
      · rcases ih hB' with ⟨p, hp, hpn⟩ | hsent
        · refine Or.inl ⟨p, ⟨hp, ?_⟩, hpn⟩
          intro hsing
          have hpx : p = (s, x) := hsing
          rw [hpx] at hpn; exact hne' hpn.symm
        · exact Or.inr hsent


proof_of msTranslate_eigenvar_fresh := by
  -- BEGIN PROOF
    intro hmem
    rcases formulaFVN_msFormulaTranslate_subset ν A (ν (s, y)) hmem with ⟨p, hp, hpn⟩ | hsentEq
    · exact hfresh (hν hpn ▸ hp)
    · exact hsent (hν hsentEq)


proof_of msFormulaTranslate_subst_comm := by
  -- BEGIN PROOF
    induction A with
    | falsum =>
      -- falsum guard mentions only var (ν someSort 0); since (u, x) ≠
      -- (someSort, 0), injectivity gives ν (u, x) ≠ ν (someSort, 0), so the
      -- one-sorted substitution leaves the guard term untouched.
      have hguard : ν (L.someSort, 0) ≠ ν (u, x) := fun hc => hsent (hν hc.symm)
      simp only [msFormulaSubst, msFormulaTranslate, FormulaN.falsum, msDomainAtom,
        formulaSubstN, FormulaN.predN.injEq, heq_eq_eq, true_and,
        FormulaN.conj.injEq, FormulaN.neg.injEq]
      refine ⟨?_, ?_⟩ <;>
      · apply congrArg (FormulaN.predN (L := msToOneSortedLang L) (.domain L.someSort))
        funext k
        simp only [termSubst]
        rw [if_neg hguard]
    | pred P ts =>
      simp only [msFormulaSubst, msFormulaTranslate, formulaSubstN,
        FormulaN.predN.injEq, heq_eq_eq, true_and]
      apply congrArg (FormulaN.predN (L := msToOneSortedLang L) (.orig P))
      funext i
      exact msTermTranslate_subst_comm ν hν u x t (ts i)
    | eq_ hL s' t1 t2 =>
      simp only [msFormulaSubst, msFormulaTranslate, formulaSubstN]
      rw [msTermTranslate_subst_comm ν hν u x t t1,
          msTermTranslate_subst_comm ν hν u x t t2]
    | conj A B ihA ihB =>
      simp only [msFormulaSubst, msFormulaTranslate, formulaSubstN, ihA, ihB]
    | disj A B ihA ihB =>
      simp only [msFormulaSubst, msFormulaTranslate, formulaSubstN, ihA, ihB]
    | impl A B ihA ihB =>
      simp only [msFormulaSubst, msFormulaTranslate, formulaSubstN, ihA, ihB]
    | equiv_ A B ihA ihB =>
      simp only [msFormulaSubst, msFormulaTranslate, formulaSubstN, ihA, ihB]
    | neg A ih =>
      simp only [msFormulaSubst, msFormulaTranslate, formulaSubstN, ih]
    | all s' i A ih =>
      simp only [msFormulaSubst, msFormulaTranslate]
      by_cases hb : s' = u ∧ i = x
      · -- bound (s', i) = (u, x): substitution skipped on BOTH sides.
        obtain ⟨hs, hi⟩ := hb
        subst hs; subst hi
        rw [if_pos ⟨rfl, rfl⟩]
        simp only [msFormulaTranslate, formulaSubstN]
        rw [if_neg (by simp)]
      · -- bound (s', i) ≠ (u, x): recurse; one-sorted binder ν (s', i) ≠ ν (u, x).
        rw [if_neg hb]
        simp only [msFormulaTranslate, formulaSubstN]
        have hbinder : ν (s', i) ≠ ν (u, x) := by
          intro hc
          have := hν hc
          exact hb ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
        rw [if_pos (by simp [bne]; exact fun hc => hbinder hc.symm)]
        simp only [FormulaN.all.injEq, true_and, FormulaN.impl.injEq]
        refine ⟨?_, ih⟩
        -- the guard D_{s'}(x_{ν(s',i)}) is unchanged by substituting index
        -- ν(u,x) ≠ ν(s',i): its only variable is ν(s',i).
        simp only [msDomainAtom, formulaSubstN, FormulaN.predN.injEq, heq_eq_eq,
          true_and]
        apply congrArg (FormulaN.predN (L := msToOneSortedLang L) (.domain s'))
        funext k
        simp only [termSubst]
        rw [if_neg hbinder]
    | ex s' i A ih =>
      simp only [msFormulaSubst, msFormulaTranslate]
      by_cases hb : s' = u ∧ i = x
      · obtain ⟨hs, hi⟩ := hb
        subst hs; subst hi
        rw [if_pos ⟨rfl, rfl⟩]
        simp only [msFormulaTranslate, formulaSubstN]
        rw [if_neg (by simp)]
      · rw [if_neg hb]
        simp only [msFormulaTranslate, formulaSubstN]
        have hbinder : ν (s', i) ≠ ν (u, x) := by
          intro hc
          have := hν hc
          exact hb ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
        rw [if_pos (by simp [bne]; exact fun hc => hbinder hc.symm)]
        simp only [FormulaN.ex.injEq, true_and, FormulaN.conj.injEq]
        refine ⟨?_, ih⟩
        simp only [msDomainAtom, formulaSubstN, FormulaN.predN.injEq, heq_eq_eq,
          true_and]
        apply congrArg (FormulaN.predN (L := msToOneSortedLang L) (.domain s'))
        funext k
        simp only [termSubst]
        rw [if_neg hbinder]


proof_of msReductionToOneSorted := by
  -- DEBT(pre-existing: Lemma 10.5.2 both directions, proof pending)
  sorry

proof_of msReductionToOneSortedEq := by
  -- REPAIR(T10-10): proof pending — shared-guard reduction in both G= directions
  sorry


end LCS.FirstOrder.ManySorted.Equality.Reduction
