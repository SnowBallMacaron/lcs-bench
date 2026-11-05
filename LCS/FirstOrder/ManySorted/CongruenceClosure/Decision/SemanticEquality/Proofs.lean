import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.SemanticEquality

section

namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Decision

open LCS.FirstOrder.ManySorted

open LCS.FirstOrder.ManySorted.Semantics

open LCS.FirstOrder.ManySorted.Equality

open LCS.FirstOrder.ManySorted.CongruenceClosure

open LCS.Propositional.Semantics

proof_of positiveClosure_equivalence := by
  -- REPAIR(T10-22): proof pending — combine the sort-supported closure's fiber equivalences.
  sorry

proof_of positiveEquationRelation_sortSupported := by
  -- REPAIR(T10-22): proof pending — positive equation endpoints have identical occurring sorts.
  sorry

proof_of termSetOfConjunction_arg := by
  -- REPAIR(T10-35): proof pending — lift subterm closure through the equation occurrence witness.
  sorry

proof_of successorOfNode_mem := by
  -- REPAIR(T10-36): proof pending — an indexed successor is an occurring argument subterm.
  sorry

proof_of msValid_reduces_to_conjunction_unsat := by
  -- BEGIN PROOF
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- (1) DNF existence: `B := toDNF A` is a DNF (`msIsDNF_toDNF`) and
      -- `A ≡ B` is valid because `toDNF A` evaluates exactly like `A` on
      -- every structure/assignment (`eval_toDNF`).
      intro A hA
      refine ⟨toDNF A, msIsDNF_toDNF A hA, ?_⟩
      intro M v
      rw [msFormulaEval_equiv, eval_toDNF M v A hA]
      -- `hEquiv x x = T`.
      cases msFormulaEval M A v <;> rfl
    · -- (2) validity via unsatisfiability of the negation's DNF.
      -- From `(¬A) ≡ B` valid: `eval B v = hNeg (eval A v)` for all `M, v`.
      intro A B _ _ hequiv
      have hBval : ∀ (M : MSStructure L) (v : MSAssignment M),
          msFormulaEval M B v = hNeg (msFormulaEval M A v) := by
        intro M v
        have h := hequiv M v
        rw [msFormulaEval_equiv, msFormulaEval_neg] at h
        -- `hEquiv (hNeg (eval A)) (eval B) = T` forces equality.
        revert h
        cases msFormulaEval M A v <;> cases msFormulaEval M B v <;>
          simp [hEquiv, hNeg]
      constructor
      · -- `msValid A → msUnsatisfiable B`.
        intro hvalid
        rintro ⟨M, v, hBv⟩
        rw [hBval M v, hvalid M v] at hBv
        exact absurd hBv (by decide)
      · -- `msUnsatisfiable B → msValid A`.
        intro hunsat M v
        -- if `eval A v = F`, then `eval B v = hNeg F = T`, a model of `B` —
        -- contradicting unsatisfiability; so `eval A v = T`.
        cases hA' : msFormulaEval M A v with
        | T => rfl
        | F =>
          have hBT : msFormulaEval M B v = BoolVal.T := by
            rw [hBval M v, hA']; rfl
          exact (hunsat ⟨M, v, hBT⟩).elim
    · -- (3) DNF unsatisfiability criterion.
      intro B _
      constructor
      · -- unsat ⇒ every disjunct unsat (a satisfiable disjunct would make
        -- `B` satisfiable via `disjunctOf_eval`).
        intro hunsat Ci hdis
        rintro ⟨M, v, hCi⟩
        exact hunsat ⟨M, v, disjunctOf_eval M v B Ci hdis hCi⟩
      · -- REPAIR(T10-30): proof pending — a satisfied DNF has a satisfied conjunction leaf.
        sorry
    · -- (4) no-equality trivial case.
      -- The BACKWARD direction (a complementary pair forces unsatisfiability)
      -- is sound: a model satisfying the conjunction would have to satisfy both
      -- `P` and `¬P`, impossible. The FORWARD direction (unsatisfiable ⇒
      -- complementary pair) uses the contrapositive: with the `hNoBot`
      -- precondition (no bare `⊥`/`¬⊥` literal — issue c3de0858), a
      -- conjunction of literals with NO complementary pair is satisfied by the
      -- Herbrand model (`sat_of_no_complementary_pair`), contradicting
      -- unsatisfiability.
      intro C hEq hClit hNoBot
      constructor
      · -- forward: unsatisfiable ⇒ complementary pair, by contraposition via
        -- the Herbrand satisfaction lemma.
        intro hunsat
        refine Classical.byContradiction fun hno => ?_
        exact hunsat (sat_of_no_complementary_pair hEq C hClit hNoBot hno)
      · -- backward: a complementary atomic pair `P, ¬P` in `C` makes `C`
        -- unsatisfiable, since any model would satisfy both `P` and `¬P`.
        rintro ⟨P, hPin, hnPin, _⟩
        rintro ⟨M, v, hCeval⟩
        have hPeval : msFormulaEval M P v = BoolVal.T :=
          conjunctContains_eval M v C P hPin hCeval
        have hnPeval : msFormulaEval M (MSFormula.neg P) v = BoolVal.T :=
          conjunctContains_eval M v C (MSFormula.neg P) hnPin hCeval
        rw [msFormulaEval_neg, hPeval] at hnPeval
        exact absurd hnPeval (by decide)


proof_of msTermSubterms_iff_mem := by
  -- BEGIN PROOF
    intro s t
    induction t with
    | var s' i =>
      intro p
      simp only [msTermSubterms, msTermSubtermsList, List.mem_singleton]
    | const s' c =>
      intro p
      simp only [msTermSubterms, msTermSubtermsList, List.mem_singleton]
    | func f ts ih =>
      intro p
      simp only [msTermSubterms, msTermSubtermsList, Set.union, Set.iUnion,
        List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and]
      constructor
      · rintro (h | ⟨i, hi⟩)
        · exact Or.inl h
        · exact Or.inr ⟨i, (ih i p).mp hi⟩
      · rintro (h | ⟨i, hi⟩)
        · exact Or.inl h
        · exact Or.inr ⟨i, (ih i p).mpr hi⟩


proof_of conjTermsList_of_contains := by
  -- BEGIN PROOF
    intro C
    induction C with
    | conj A B ihA ihB =>
      intro X hcon p hp
      rcases hcon with hself | hsub
      · rw [← hself] at hp; exact hp
      · rcases hsub with hA | hB
        · exact List.mem_append_left _ (ihA X hA p hp)
        · exact List.mem_append_right _ (ihB X hB p hp)
    | falsum => intro X hcon p hp; rw [show X = MSFormula.falsum from hcon.symm] at hp; exact hp
    | pred P ts => intro X hcon p hp; rw [← hcon] at hp; exact hp
    | eq_ hL s t u => intro X hcon p hp; rw [← hcon] at hp; exact hp
    | disj A B _ _ => intro X hcon p hp; rw [← hcon] at hp; exact hp
    | impl A B _ _ => intro X hcon p hp; rw [← hcon] at hp; exact hp
    | equiv_ A B _ _ => intro X hcon p hp; rw [← hcon] at hp; exact hp
    | neg A _ => intro X hcon p hp; rw [← hcon] at hp; exact hp
    | all s i A _ => intro X hcon p hp; rw [← hcon] at hp; exact hp
    | ex s i A _ => intro X hcon p hp; rw [← hcon] at hp; exact hp


proof_of termSetOfConjunction_mem_list := by
  -- BEGIN PROOF
    obtain ⟨hL, s, t, u, hcontain, hsub⟩ := hp
    -- The containing literal `X` (positive or negated equation) has
    -- `conjTermsList X = subterms t ++ subterms u`, and `p` is a subterm
    -- of `t` or `u`.
    rcases hcontain with hpos | hneg
    · -- positive equation: conjTermsList (eq_ hL s t u) = subterms t ++ subterms u
      refine conjTermsList_of_contains C (MSFormula.eq_ hL s t u) hpos p ?_
      show p ∈ msTermSubtermsList t ++ msTermSubtermsList u
      rcases hsub with ht | hu
      · exact List.mem_append_left _ ((msTermSubterms_iff_mem t p).mp ht)
      · exact List.mem_append_right _ ((msTermSubterms_iff_mem u p).mp hu)
    · -- negated equation: conjTermsList (neg (eq_ ...)) = subterms t ++ subterms u
      refine conjTermsList_of_contains C (MSFormula.neg (MSFormula.eq_ hL s t u))
        hneg p ?_
      show p ∈ msTermSubtermsList t ++ msTermSubtermsList u
      rcases hsub with ht | hu
      · exact List.mem_append_left _ ((msTermSubterms_iff_mem t p).mp ht)
      · exact List.mem_append_right _ ((msTermSubterms_iff_mem u p).mp hu)


proof_of termSetOfSort_nonempty := hs
  -- BEGIN PROOF


proof_of labelOfNode_leaf_arity := by
  -- BEGIN PROOF
    rcases hleaf with ⟨i, rfl⟩ | ⟨c, rfl⟩ <;> rfl


proof_of labelOfNode_func_arity := by
  simp [labelOfNode, conjSymbolRank, List.map_ofFn, Function.comp_def, List.ofFn_getElem]


proof_of labelOfNode_rank_sort := by
  -- BEGIN PROOF
    obtain ⟨s, t⟩ := p
    cases t <;> rfl


proof_of successorOfNode_sort := by
  -- REPAIR(T10-22): proof pending — identify the transported argument sort at each indexed port.
  sorry


proof_of msTermSubterms_self := by
  -- BEGIN PROOF
    cases t with
    | var _ _   => rfl
    | const _ _ => rfl
    | func f ts => exact Or.inl rfl


proof_of msTermSubterms_subterm_closed := by
  -- BEGIN PROOF
    intro s t
    induction t with
    | var s' j =>
      intro f ts i hmem
      -- subterms of a variable is just {⟨s', var s' j⟩}, which can't be
      -- a function node.
      simp only [msTermSubterms] at hmem
      exact absurd hmem (by intro h; cases h)
    | const s' c =>
      intro f ts i hmem
      simp only [msTermSubterms] at hmem
      exact absurd hmem (by intro h; cases h)
    | func g us ih =>
      intro f ts i hmem
      -- Membership in `msTermSubterms (func g us)` unfolds to: the node IS
      -- this term, or it lies in some argument's subterms.
      simp only [msTermSubterms, Set.union, Set.iUnion] at hmem
      rcases hmem with hself | ⟨j, hj⟩
      · -- the function node IS this term: `⟨_, func g us⟩ = ⟨_, func f ts⟩`.
        -- Goal: `ts i` is an immediate subterm of `func g us`. Rewrite the
        -- goal's node `⟨(L.funRank f).1.get i, ts i⟩` using subterm-closure
        -- of `func f ts` itself, then transport along `hself`.
        -- It suffices to show `ts i ∈ msTermSubterms (func f ts)` and that
        -- `msTermSubterms (func g us) = msTermSubterms (func f ts)` (from
        -- `hself`), giving membership for `func g us`.
        have hsub_ft : msTermSubterms (MSTerm.func f ts)
            ⟨(L.funRank f).1.get i, ts i⟩ := by
          simp only [msTermSubterms, Set.union, Set.iUnion]
          exact Or.inr ⟨i, msTermSubterms_self (ts i)⟩
        -- `hself : ⟨_, func g us⟩ = ⟨_, func f ts⟩` lets us transport the
        -- subterm fact back to `func g us` by congruence of `msTermSubterms`
        -- as a dependent function of the sorted term.
        have hcong : msTermSubterms (MSTerm.func g us)
            = msTermSubterms (MSTerm.func f ts) :=
          congrArg (fun (p : MSTermSig L) => msTermSubterms p.2) hself.symm
        rw [hcong]
        exact hsub_ft
      · -- the node lies in some argument's subterms; apply the IH.
        simp only [msTermSubterms, Set.union, Set.iUnion]
        exact Or.inr ⟨j, ih j f ts i hj⟩


proof_of termSetOfConjunction_node_finite := by
  -- BEGIN PROOF
    classical
    -- Keep only the over-collected terms that genuinely lie in `TERM(C)`,
    -- then attach the membership proofs to obtain a list of nodes.
    let keep : List (MSTermSig L) :=
      (conjTermsList C).filter (fun p => decide (termSetOfConjunction C p))
    have hkeep_mem : ∀ p ∈ keep, termSetOfConjunction C p := by
      intro p hp
      have := (List.mem_filter.mp hp).2
      simpa using this
    -- The list of all nodes.
    let nodes : List { p : MSTermSig L // termSetOfConjunction C p } :=
      keep.pmap (fun p hp => ⟨p, hp⟩) hkeep_mem
    refine ⟨nodes, fun a => ⟨fun _ => ?_, fun _ => trivial⟩⟩
    -- `a.1 ∈ conjTermsList C` (superset) and satisfies `TERM(C)`, so it
    -- survives the filter; hence `a ∈ nodes`.
    obtain ⟨pa, hpa⟩ := a
    have hin_list : pa ∈ conjTermsList C := termSetOfConjunction_mem_list C pa hpa
    have hin_keep : pa ∈ keep :=
      List.mem_filter.mpr ⟨hin_list, by simpa using hpa⟩
    -- membership in the pmapped list.
    exact List.mem_pmap.mpr ⟨pa, hin_keep, rfl⟩


proof_of semanticEqualityRelation_refl := by
  -- BEGIN PROOF
    refine ⟨hL, ?_⟩
    intro M v _
    exact msEqReflValid hL s t M v


proof_of semanticEqualityRelation_symm := by
  -- BEGIN PROOF
    obtain ⟨hL, hent⟩ := h
    refine ⟨hL, ?_⟩
    intro M v hsat
    rw [msFormulaEval_eq_T_iff]
    exact ((msFormulaEval_eq_T_iff M hL s t u v).mp (hent M v hsat)).symm


proof_of semanticEqualityRelation_trans := by
  -- BEGIN PROOF
    obtain ⟨hL, hent1⟩ := h1
    obtain ⟨_, hent2⟩ := h2
    refine ⟨hL, ?_⟩
    intro M v hsat
    rw [msFormulaEval_eq_T_iff]
    have e1 := (msFormulaEval_eq_T_iff M hL s t u v).mp (hent1 M v hsat)
    have e2 := (msFormulaEval_eq_T_iff M hL s u w v).mp (hent2 M v hsat)
    exact e1.trans e2


proof_of semanticEqualityRelation_funcCong := by
  -- BEGIN PROOF
    refine ⟨hL, ?_⟩
    intro M v hsat
    rw [msFormulaEval_eq_T_iff]
    -- Each argument's meanings agree under v.
    have hargs : ∀ i, msTermEval M v (ys i) = msTermEval M v (zs i) := by
      intro i
      obtain ⟨_, henti⟩ := hcong i
      exact (msFormulaEval_eq_T_iff M hL _ _ _ v).mp (henti M v hsat)
    -- Hence the two function applications evaluate identically.
    simp only [msTermEval, funM]
    congr 1
    funext i
    exact hargs i


proof_of semanticEqualityRelationNode_mk := by
  -- BEGIN PROOF
    obtain ⟨uv, hum⟩ := u
    obtain ⟨vv, hvm⟩ := v
    simp only at hu hv ⊢
    subst hu; subst hv
    exact ⟨s, rfl, rfl, hrel⟩


proof_of semanticEqualityRelationNode_elim := by
  -- BEGIN PROOF
    obtain ⟨uv, hum⟩ := u
    obtain ⟨vv, hvm⟩ := v
    simp only at hu hv
    subst hu; subst hv
    obtain ⟨s', h1, h2, hr⟩ := hrel
    -- `s' = ⟨s,tu⟩.1 = s`; both transports collapse to identity.
    cases h1; cases h2
    exact hr


proof_of semanticEqualityRelationNode_of_eq := by
  -- BEGIN PROOF
    -- Reduce to the underlying sorted-term equality and discharge by
    -- reflexivity of the sort-level relation. Generalize `q.1` so the
    -- equality `heq` can be substituted cleanly.
    unfold semanticEqualityRelationNode
    obtain ⟨pv, hp⟩ := p
    obtain ⟨qv, hq⟩ := q
    simp only at heq ⊢
    subst heq
    exact ⟨pv.1, rfl, rfl, semanticEqualityRelation_refl C hL pv.1 pv.2⟩


proof_of decodeLeaf_labelOfNode := by
  -- BEGIN PROOF
    rcases hleaf with ⟨i, rfl⟩ | ⟨c, rfl⟩ <;> rfl


proof_of leaf_of_rank_empty := by
  -- BEGIN PROOF
    obtain ⟨s, t⟩ := p
    cases t with
    | var _ i   => exact Or.inl ⟨i, rfl⟩
    | const _ c => exact Or.inr ⟨c, rfl⟩
    | func f ts =>
      exact absurd hrank (by
        intro h
        have hempty := congrArg (List.map Subtype.val) h
        simp [labelOfNode, conjSymbolRank, List.map_ofFn, Function.comp_def, List.ofFn_getElem] at hempty
        exact L.funRank_nonempty f hempty)


proof_of func_of_rank_nonempty := by
  -- BEGIN PROOF
    obtain ⟨s, t⟩ := p
    cases t with
    | var _ i   => exact absurd rfl hrank
    | const _ c => exact absurd rfl hrank
    | func f fts => exact ⟨f, fts, rfl⟩


proof_of labelOfNode_leaf_inj := by
  -- BEGIN PROOF
    have e1 : decodeLeaf (labelOfNode C p hp) = p := by
      obtain ⟨sp, tp⟩ := p; exact decodeLeaf_labelOfNode tp hp hpleaf
    have e2 : decodeLeaf (labelOfNode C q hq) = q := by
      obtain ⟨sq, tq⟩ := q; exact decodeLeaf_labelOfNode tq hq hqleaf
    rw [← e1, ← e2, hlab]


proof_of semanticEqualityRelation_isCongruence := by
  -- REPAIR(T10-22): proof pending — establish sort support, fiber equivalence and backward closure over occurring labels.
  sorry


proof_of positiveEquationRelation_subset_semantic := by
  -- BEGIN PROOF
    obtain ⟨hL, s, t, u, hcontain, hp, hq⟩ := h
    refine semanticEqualityRelationNode_mk C p q s t u hp hq ⟨hL, ?_⟩
    -- `eq_ hL s t u` is a member of `E_set`, so any satisfying model makes
    -- it true.
    intro M v hsat
    exact hsat (MSFormula.eq_ hL s t u) ⟨⟨hL, s, t, u, rfl⟩, hcontain⟩


proof_of collision_entails_equation := by
  -- BEGIN PROOF
    -- `R*` is the least congruence containing `E`, and the semantic-equality
    -- node relation is a congruence containing `E`, so `R* ⊆ R`.
    have hsub := msCongruenceClosure_smallest (graphOfConjunction C)
      (positiveEquationRelation C) (positiveEquationRelation_sortSupported C) (semanticEqualityRelationNode C)
      (semanticEqualityRelation_isCongruence C)
      (positiveEquationRelation_subset_semantic C)
      p q hcol
    -- Extract the sort-level relation between `r`, `v`.
    have hrel := semanticEqualityRelationNode_elim C p q s r v hp hq hsub
    -- `hrel : ∃ hL', msEntails E_set (eq_ hL' s r v)`; the proof flag is
    -- irrelevant (proof of `L.hasEquality = true`).
    obtain ⟨hL', hent⟩ := hrel
    -- align the equality flag.
    have : hL' = hL := rfl
    rw [this] at hent
    exact hent


proof_of msConjunctContains_eval := by
  -- BEGIN PROOF
    intro C
    induction C with
    | conj A B ihA ihB =>
      intro X hcon hCeval
      rw [msFormulaEval_conj, hAnd_eq_T_iff] at hCeval
      rcases hcon with hself | hsub
      · rw [← hself]; rw [msFormulaEval_conj, hAnd_eq_T_iff]; exact hCeval
      · rcases hsub with hA | hB
        · exact ihA X hA hCeval.1
        · exact ihB X hB hCeval.2
    | falsum => intro X hcon hCeval; rw [show X = MSFormula.falsum from hcon.symm]; exact hCeval
    | pred P ts => intro X hcon hCeval; rw [← hcon]; exact hCeval
    | eq_ hL s t u => intro X hcon hCeval; rw [← hcon]; exact hCeval
    | disj A B _ _ => intro X hcon hCeval; rw [← hcon]; exact hCeval
    | impl A B _ _ => intro X hcon hCeval; rw [← hcon]; exact hCeval
    | equiv_ A B _ _ => intro X hcon hCeval; rw [← hcon]; exact hCeval
    | neg A _ => intro X hcon hCeval; rw [← hcon]; exact hCeval
    | all s i A _ => intro X hcon hCeval; rw [← hcon]; exact hCeval
    | ex s i A _ => intro X hcon hCeval; rw [← hcon]; exact hCeval


proof_of collision_unsat_direction := by
  -- BEGIN PROOF
    obtain ⟨hL, s, r, vt, p, q, hneg, hp, hq, hcol⟩ := h
    -- Suppose `C` is satisfiable; derive a contradiction.
    rintro ⟨M, v, hCeval⟩
    -- The collision entails `r =̇ vt` under any model of E_set.
    have hent := collision_entails_equation C hL s r vt p q hp hq hcol
    -- `M, v` satisfies E_set (the positive equations contained in C).
    have hEset : ∀ B, equationSetOfConjunction C B →
        msFormulaEval M B v = BoolVal.T := by
      intro B ⟨_, hBcontain⟩
      exact msConjunctContains_eval M v C B hBcontain hCeval
    -- So `r =̇ vt` is true under `M, v`.
    have hpos : msFormulaEval M (MSFormula.eq_ hL s r vt) v = BoolVal.T :=
      hent M v hEset
    -- But the negated equation is also true (it is a conjunct of C).
    have hnegeval : msFormulaEval M (MSFormula.neg (MSFormula.eq_ hL s r vt)) v
        = BoolVal.T :=
      msConjunctContains_eval M v C _ hneg hCeval
    -- Contradiction: `r =̇ vt` is true, so `r_M[v] = vt_M[v]`, making the
    -- negated equation evaluate to `F`, not `T`.
    have heq : msTermEval M v r = msTermEval M v vt :=
      (msFormulaEval_eq_T_iff M hL s r vt v).mp hpos
    dsimp only [msFormulaEval, negM, eqM] at hnegeval
    rw [if_pos heq] at hnegeval
    exact absurd hnegeval (by decide)


end LCS.FirstOrder.ManySorted.CongruenceClosure.Decision

end
