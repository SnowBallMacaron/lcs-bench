import LCS.FOResolution.Unification.TwoTreeReduction

section
namespace LCS.FOResolution.Unification
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.SyntaxN.Variables

proof_of unifier_iff_auxiliary_unifier := by
  -- BEGIN PROOF
    -- Case split on ts to resolve the match expression
    cases ts with
    | nil =>
      -- ts = []: arity of sharp is 0, so both sharp-terms are identical
      -- (Term.func sharp with no arguments). IsUnifierCore sigma [] is trivially true,
      -- and IsUnifierCore sigma' [t, t] is trivially true (both terms equal).
      simp only [List.length_nil] at h_arity_sharp
      constructor
      · intro _
        intro t1 t2 ht1 ht2
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht1 ht2
        rcases ht1 with rfl | rfl <;> rcases ht2 with rfl | rfl <;> try rfl
        all_goals (simp only [termSubstAll]; congr 1; funext i; exact (h_arity_sharp ▸ i).elim0)
      · intro _
        intro t1 t2 ht1 ht2; simp at ht1
    | cons hd tl =>
      -- ts = hd :: tl
      constructor
      · -- Forward: sigma unifies ts => lifted sigma unifies sharp-terms
        intro hUnif t1 t2 ht1 ht2
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht1 ht2
        -- Suffices to show the two sharp-terms unify under lifted sigma
        suffices key : termSubstAll
            (Term.func sharp (fun i => liftTerm ((hd :: tl).get (i.cast h_arity_sharp))))
            (fun x => liftTerm (sigma x)) =
          termSubstAll
            (Term.func sharp (fun _ => liftTerm hd))
            (fun x => liftTerm (sigma x)) by
          rcases ht1 with rfl | rfl <;> rcases ht2 with rfl | rfl
          · rfl
          · exact key
          · exact key.symm
          · rfl
        -- Both sides reduce via termSubstAll for func
        simp only [termSubstAll]
        congr 1; funext i
        -- LHS: termSubstAll (liftTerm ((hd :: tl)[i])) (liftTerm ∘ sigma)
        -- = liftTerm (termSubstAll ((hd :: tl)[i]) sigma)  by h_lift_subst
        rw [← h_lift_subst ((hd :: tl).get (i.cast h_arity_sharp))]
        -- RHS: termSubstAll (liftTerm hd) (liftTerm ∘ sigma)
        -- = liftTerm (termSubstAll hd sigma)  by h_lift_subst
        rw [← h_lift_subst hd]
        -- Now: liftTerm (termSubstAll ((hd::tl)[i]) sigma) = liftTerm (termSubstAll hd sigma)
        congr 1
        -- By IsUnifierCore: all terms in ts map to the same value
        apply hUnif
        · exact List.get_mem (hd :: tl) (i.cast h_arity_sharp)
        · exact .head _
      · -- Backward: lifted sigma unifies sharp-terms => sigma unifies ts
        -- Uses injectivity of liftTerm and injectivity of Term.func on arguments.
        intro hUnif t1 t2 ht1 ht2
        -- From hUnif, the two sharp-terms are equal under the lifted substitution.
        have key := hUnif
          (Term.func sharp (fun i => liftTerm ((hd :: tl).get (i.cast h_arity_sharp))))
          (Term.func sharp (fun _ => liftTerm hd))
          (.head _) (List.mem_cons.mpr (Or.inr (.head _)))
        -- Both sides reduce via termSubstAll for func
        simp only [termSubstAll] at key
        -- key : Term.func sharp (...) = Term.func sharp (...)
        -- By Term.func injectivity on arguments, all components agree.
        -- For any t ∈ (hd :: tl), show termSubstAll t sigma = termSubstAll hd sigma.
        have h_all_eq_hd : ∀ (j : Fin (hd :: tl).length),
            termSubstAll ((hd :: tl).get j) sigma = termSubstAll hd sigma := by
          intro j
          have hj_lt : j.val < L'.funArity sharp := by
            rw [h_arity_sharp]; exact j.isLt
          let idx : Fin (L'.funArity sharp) := ⟨j.val, hj_lt⟩
          -- Use injection on key to extract argument equality
          injection key with _hf_eq h_args_eq
          -- h_args_eq : (fun i => ...) = (fun _ => ...)
          have h_at_idx := congrFun h_args_eq idx
          rw [← h_lift_subst ((hd :: tl).get (idx.cast h_arity_sharp)),
              ← h_lift_subst hd] at h_at_idx
          have h_get_eq : (hd :: tl).get (idx.cast h_arity_sharp) = (hd :: tl).get j := by
            congr 1
          rw [h_get_eq] at h_at_idx
          exact h_lift_injective _ _ h_at_idx
        -- t1, t2 ∈ (hd :: tl), so their images under sigma are both equal to
        -- termSubstAll hd sigma.
        obtain ⟨i1, hi1⟩ := List.get_of_mem ht1
        obtain ⟨i2, hi2⟩ := List.get_of_mem ht2
        rw [← hi1, ← hi2, h_all_eq_hd i1, h_all_eq_hd i2]

end LCS.FOResolution.Unification
end
