import LCS.FirstOrder.ManySorted.CongruenceClosure

namespace LCS.FirstOrder.ManySorted.CongruenceClosure

proof_of msCongruenceClosure_contains := fun _ _ h => ⟨0, Or.inl h⟩


proof_of msCongruenceIterate_succ_mono := Or.inl h


proof_of msCongruenceIterate_mono := by
  induction j with
  | zero =>
    have : i = 0 := Nat.le_zero.mp hij
    subst this; exact h
  | succ k ih =>
    rcases Nat.lt_or_ge i (k + 1) with hlt | hge
    · -- i ≤ k, so use IH then one-step monotonicity
      have hik : i ≤ k := Nat.lt_succ_iff.mp hlt
      exact msCongruenceIterate_succ_mono G R hR k u v (ih hik)
    · -- k + 1 ≤ i and i ≤ k + 1, so i = k + 1
      have : i = k + 1 := Nat.le_antisymm hij hge
      subst this; exact h


proof_of finBound_le := @fun
  | 0, _, j => absurd j.isLt (Nat.not_lt_zero _)
  | n + 1, g, j => by
    rcases Nat.lt_or_ge j.val n with hlt | hge
    · -- j < n: it is a castSucc, use the recursive bound
      have hrec := finBound_le n (fun k => g k.castSucc) ⟨j.val, hlt⟩
      have hcast : (⟨j.val, hlt⟩ : Fin n).castSucc = j := by
        apply Fin.ext; simp [Fin.castSucc]
      rw [hcast] at hrec
      exact Nat.le_trans hrec (Nat.le_max_right _ _)
    · -- j = n: it is the top element
      have hjn : j.val = n := Nat.le_antisymm (Nat.lt_succ_iff.mp j.isLt) hge
      have hjtop : j = ⟨n, Nat.lt_succ_self n⟩ := by apply Fin.ext; exact hjn
      rw [hjtop]
      exact Nat.le_max_left _ _


proof_of msCongruenceClosure_isCongruence := by
  -- BEGIN PROOF
    have hs : ∀ i, MSSortSupported G (msCongruenceIterate G R hR i) := by
      intro i
      induction i with
      | zero =>
        intro u v huv
        rcases huv with hseed | hleaf | hdiag
        · exact hR u v hseed
        · exact (G.lambda_rank_sort u).symm.trans
            ((congrArg (fun f => (G.Sigma.rank f).2) hleaf.1).trans (G.lambda_rank_sort v))
        · exact congrArg G.nodeSort hdiag
      | succ i ih =>
        intro u v huv
        rcases huv with hold | hsym | ⟨w, huw, hwv, _, _⟩ | ⟨hlab, _⟩
        · exact ih u v hold
        · exact (ih v u hsym).symm
        · exact huw.trans hwv
        · exact (G.lambda_rank_sort u).symm.trans
            ((congrArg (fun f => (G.Sigma.rank f).2) hlab).trans (G.lambda_rank_sort v))
    refine ⟨(fun u v ⟨i, hi⟩ => hs i u v hi), ?_, ?_, ?_⟩
    · intro s
      refine ⟨?_, ?_, ?_⟩
      · -- Reflexivity: u = u is in the reflexive seed at stage 0.
        intro u
        exact ⟨0, Or.inr (Or.inr rfl)⟩
      · -- Symmetry: from R^i u v, the symmetric step at stage i+1 gives v u.
        intro u v ⟨i, hi⟩
        exact ⟨i + 1, Or.inr (Or.inl hi)⟩
      · -- Transitivity: lift both to a common stage, then transitive step.
        intro u v w ⟨i, hi⟩ ⟨j, hj⟩
        refine ⟨max i j + 1, Or.inr (Or.inr (Or.inl
          ⟨v.val, u.property.trans v.property.symm,
            v.property.trans w.property.symm, ?_, ?_⟩))⟩
        · exact msCongruenceIterate_mono G R hR (Nat.le_max_left i j) hi
        · exact msCongruenceIterate_mono G R hR (Nat.le_max_right i j) hj
    · -- Backward closure (2a): leaf base case, in the leaf-pair seed at 0.
      intro u v hlab hrank
      exact ⟨0, Or.inr (Or.inl ⟨hlab, hrank⟩)⟩
    · -- Backward closure (2b): successor step. Each successor pair is
      -- related at some stage; take the common bound, then apply the
      -- successor-congruence step at that stage + 1.
      intro u v hlab hsucc
      -- Choose, for each index j, a stage at which the j-th successors are
      -- related, then dominate all of them by `finBound`.
      classical
      -- For each j, extract a stage witness.
      let g : Fin (G.Sigma.rank (G.Lambda u)).1.length → Nat :=
        fun j => Classical.choose (hsucc j)
      have hg : ∀ j, msCongruenceIterate G R hR (g j) (G.delta u j) (G.delta v (hlab ▸ j)) :=
        fun j => Classical.choose_spec (hsucc j)
      refine ⟨finBound _ g + 1, Or.inr (Or.inr (Or.inr ⟨hlab, fun j => ?_⟩))⟩
      -- Lift the j-th witness to the common stage finBound n g.
      exact msCongruenceIterate_mono G R hR (finBound_le _ g j) (hg j)


proof_of msCongruenceIterate_subset_of_congruence := by
  -- BEGIN PROOF
    obtain ⟨hsupport, hequiv, hbc2a, hbc2b⟩ := hR'
    have hrefl (u : G.Node) : R' u u := (hequiv (G.nodeSort u)).refl ⟨u, rfl⟩
    have hsymm (u v : G.Node) (h : R' u v) : R' v u :=
      (hequiv (G.nodeSort u)).symm (x := ⟨u, rfl⟩)
        (y := ⟨v, (hsupport u v h).symm⟩) h
    have htrans (u v w : G.Node) (huv : R' u v) (hvw : R' v w) : R' u w :=
      (hequiv (G.nodeSort u)).trans (x := ⟨u, rfl⟩)
        (y := ⟨v, (hsupport u v huv).symm⟩)
        (z := ⟨w, ((hsupport u v huv).trans (hsupport v w hvw)).symm⟩) huv hvw
    intro i
    induction i with
    | zero =>
      -- R^0 = R ∪ leaf-pairs ∪ diagonal.
      intro u v h
      rcases h with hR | hleaf | hdiag
      · exact hContains u v hR
      · -- leaf-pair seed: equal empty-arity labels ⇒ R' by (2a).
        exact hbc2a u v hleaf.1 hleaf.2
      · -- reflexive seed: u = v ⇒ R' by reflexivity.
        subst hdiag; exact hrefl u
    | succ k ih =>
      -- R^{k+1} = R^k ∪ symmetric ∪ transitive ∪ successor-congruence.
      intro u v h
      rcases h with hk | hsym | htr | hsc
      · exact ih u v hk
      · -- symmetric step: R^k v u ⇒ R' v u ⇒ R' u v.
        exact hsymm v u (ih v u hsym)
      · -- transitive step: ∃ x, R^k u x ∧ R^k x w.
        obtain ⟨x, _, _, hux, hxv⟩ := htr
        exact htrans u x v (ih u x hux) (ih x v hxv)
      · -- successor-congruence step: equal labels with componentwise-R^k
        -- successors ⇒ R' by (2b).
        obtain ⟨hlab, hsucc⟩ := hsc
        exact hbc2b u v hlab (fun j => ih _ _ (hsucc j))


proof_of msCongruenceClosure_smallest := fun R' hR' hContains u v ⟨i, hi⟩ =>
  -- BEGIN PROOF
      msCongruenceIterate_subset_of_congruence G R R' hR hR' hContains i u v hi

proof_of msCongruenceClosure_least := ⟨msCongruenceClosure_isCongruence G R hR,
  -- BEGIN PROOF
      msCongruenceClosure_contains G R hR,
      msCongruenceClosure_smallest G R hR⟩


end LCS.FirstOrder.ManySorted.CongruenceClosure
