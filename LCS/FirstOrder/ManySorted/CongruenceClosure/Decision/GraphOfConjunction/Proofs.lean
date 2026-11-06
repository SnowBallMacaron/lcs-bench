import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.GraphOfConjunction

section

namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Decision

open LCS.FirstOrder.ManySorted

open LCS.FirstOrder.ManySorted.Semantics

open LCS.FirstOrder.ManySorted.Equality

open LCS.FirstOrder.ManySorted.CongruenceClosure

open LCS.Propositional.Semantics

proof_of positiveEquationRelation_sortSupported := by
  -- REPAIR(T10-22): proof pending — positive equation endpoints have identical occurring sorts.
  sorry

proof_of termSetOfConjunction_arg := by
  -- REPAIR(T10-35): proof pending — lift subterm closure through the equation occurrence witness.
  sorry

proof_of successorOfNode_mem := by
  -- REPAIR(T10-36): proof pending — an indexed successor is an occurring argument subterm.
  sorry

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

  -- BEGIN PROOF

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

end LCS.FirstOrder.ManySorted.CongruenceClosure.Decision

end
