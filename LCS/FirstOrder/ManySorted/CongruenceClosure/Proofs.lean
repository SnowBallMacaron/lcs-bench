import LCS.FirstOrder.ManySorted.CongruenceClosure

namespace LCS.FirstOrder.ManySorted.CongruenceClosure

proof_of msCongruenceClosure_eq_iUnion := Iff.rfl


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


proof_of msCongruenceClosure_exists_least := ⟨msCongruenceClosure G R hR,
  -- BEGIN PROOF
      msCongruenceClosure_isCongruence G R hR,
      msCongruenceClosure_contains G R hR,
      msCongruenceClosure_smallest G R hR⟩


proof_of msCongruenceIterateStep_congr := by
  unfold msCongruenceIterateStep msSymmetricStep msTransitiveStep
    msSuccessorCongruenceStep
  constructor
  · rintro (h1 | h1 | ⟨x, hux, hxv, hx1, hx2⟩ | ⟨hlab, hsucc⟩)
    · exact Or.inl ((h u v).mp h1)
    · exact Or.inr (Or.inl ((h v u).mp h1))
    · exact Or.inr (Or.inr (Or.inl ⟨x, hux, hxv, (h u x).mp hx1, (h x v).mp hx2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hlab, fun j => (h _ _).mp (hsucc j)⟩))
  · rintro (h1 | h1 | ⟨x, hux, hxv, hx1, hx2⟩ | ⟨hlab, hsucc⟩)
    · exact Or.inl ((h u v).mpr h1)
    · exact Or.inr (Or.inl ((h v u).mpr h1))
    · exact Or.inr (Or.inr (Or.inl ⟨x, hux, hxv, (h u x).mpr hx1, (h x v).mpr hx2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hlab, fun j => (h _ _).mpr (hsucc j)⟩))


proof_of msCongruenceIterate_fixpoint_step := by
  intro k
  induction k with
  | zero => intro u v; exact hfix u v
  | succ m ih =>
    -- ih : R^{i+m} ↔ R^{i+m+1}; the step is a congruence, so completing
    -- both gives R^{i+m+1} ↔ R^{i+m+2}.
    intro u v
    exact msCongruenceIterateStep_congr G (msCongruenceIterate G R hR (i + m))
      (msCongruenceIterate G R hR (i + m + 1)) ih u v


proof_of msCongruenceIterate_fixpoint_add := by
  intro k
  induction k with
  | zero => intro u v; exact Iff.rfl
  | succ m ih =>
    intro u v
    -- R^i ↔ R^{i+m} (ih) and R^{i+m} ↔ R^{i+m+1} (propagated fixpoint).
    exact (ih u v).trans (msCongruenceIterate_fixpoint_step G R hR i hfix m u v)


proof_of nat_seq_stabilizes := by
  -- If no two consecutive values agree, the sequence strictly increases,
  -- so f i ≥ i for all i; then f (N+1) ≥ N+1 > N, contradicting hbound.
  refine Classical.byContradiction fun hcon => ?_
  have hne : ∀ j, f j ≠ f (j + 1) := fun j hj => hcon ⟨j, hj⟩
  have hstrict : ∀ i, f i < f (i + 1) := fun i =>
    Nat.lt_of_le_of_ne (hmono i) (hne i)
  have hge : ∀ i, i ≤ f i := by
    intro i
    induction i with
    | zero => exact Nat.zero_le _
    | succ k ih => exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih (hstrict k))
  -- f (N+1) ≥ N+1 > N, contradicting f (N+1) ≤ N.
  have h1 : N + 1 ≤ f (N + 1) := hge (N + 1)
  have h2 : f (N + 1) ≤ N := hbound (N + 1)
  omega


proof_of countP_eq_imp_rev := by
  induction l with
  | nil => intro x hx; exact absurd hx (by simp)
  | cons a t ih =>
    rw [List.forall_mem_cons] at himp
    obtain ⟨ha, ht⟩ := himp
    -- p ≤ q on t, so countP p t ≤ countP q t.
    have hle : t.countP p ≤ t.countP q := List.countP_mono_left ht
    -- Case split on the Bool values p a, q a so the counts compute cleanly.
    cases hpa : p a with
    | true =>
      have hqa : q a = true := ha hpa
      rw [List.countP_cons_of_pos (by rw [hpa]),
          List.countP_cons_of_pos (by rw [hqa])] at heq
      have heqt : t.countP p = t.countP q := by omega
      intro x hx hqx
      rcases List.mem_cons.mp hx with rfl | hxt
      · exact hpa
      · exact ih ht heqt x hxt hqx
    | false =>
      rw [List.countP_cons_of_neg (by rw [hpa]; simp)] at heq
      cases hqa : q a with
      | true =>
        -- countP p t = countP q t + 1, but countP p t ≤ countP q t.
        rw [List.countP_cons_of_pos (by rw [hqa])] at heq
        omega
      | false =>
        rw [List.countP_cons_of_neg (by rw [hqa]; simp)] at heq
        intro x hx hqx
        rcases List.mem_cons.mp hx with rfl | hxt
        · rw [hqa] at hqx; exact absurd hqx (by simp)
        · exact ih ht heq x hxt hqx


proof_of msCongruenceIterate_stabilizes := by
  -- BEGIN PROOF
    classical
    -- A finite list `nodes` containing every node.
    obtain ⟨nodes, hnodes⟩ := G.nodeFinite
    have hmem : ∀ a : G.Node, a ∈ nodes := fun a => (hnodes a).mp trivial
    -- The list of all node pairs.
    let pairs : List (G.Node × G.Node) := nodes.flatMap (fun a => nodes.map (fun b => (a, b)))
    have hpairs : ∀ ab : G.Node × G.Node, ab ∈ pairs := by
      intro ⟨a, b⟩
      refine List.mem_flatMap.mpr ⟨a, hmem a, ?_⟩
      exact List.mem_map.mpr ⟨b, hmem b, rfl⟩
    -- The decidable predicate "the pair is related at stage i".
    let P : Nat → G.Node × G.Node → Bool :=
      fun i ab => decide (msCongruenceIterate G R hR i ab.1 ab.2)
    -- The count of related pairs at stage i.
    let f : Nat → Nat := fun i => pairs.countP (P i)
    -- f is monotone (one-step monotonicity of the iterates).
    have hmono : ∀ i, f i ≤ f (i + 1) := by
      intro i
      apply List.countP_mono_left
      intro ⟨a, b⟩ _ hab
      simp only [P, decide_eq_true_eq] at hab ⊢
      exact msCongruenceIterate_succ_mono G R hR i a b hab
    -- f is bounded by the number of pairs.
    have hbound : ∀ i, f i ≤ pairs.length := fun i => List.countP_le_length
    -- A monotone bounded nat sequence has a consecutive repeat.
    obtain ⟨j, hj⟩ := nat_seq_stabilizes f pairs.length hmono hbound
    refine ⟨j, fun u v => ⟨fun h => msCongruenceIterate_succ_mono G R hR j u v h, ?_⟩⟩
    -- Reverse direction: from f j = f (j+1) and P j ⊆ P (j+1), get equivalence.
    intro h
    have himp : ∀ ab ∈ pairs, P j ab → P (j + 1) ab := by
      intro ⟨a, b⟩ _ hab
      simp only [P, decide_eq_true_eq] at hab ⊢
      exact msCongruenceIterate_succ_mono G R hR j a b hab
    have hrev := countP_eq_imp_rev (P j) (P (j + 1)) pairs himp hj
    have := hrev (u, v) (hpairs (u, v)) (by simp only [P, decide_eq_true_eq]; exact h)
    simp only [P, decide_eq_true_eq] at this
    exact this


proof_of msCongruenceClosure_computable := by
  -- BEGIN PROOF
    -- Take the stabilization stage i; then R* = R^i.
    obtain ⟨i, hfix⟩ := msCongruenceIterate_stabilizes G R hR
    refine ⟨i, fun u v => ⟨?_, ?_⟩⟩
    · -- R* u v → R^i u v: the witness stage j is brought to stage i.
      rintro ⟨j, hj⟩
      rcases Nat.lt_or_ge j (i + 1) with hji | hij
      · -- j ≤ i: lift up by monotonicity.
        exact msCongruenceIterate_mono G R hR (Nat.lt_succ_iff.mp hji) hj
      · -- i < j: write j = i + k (k ≥ 1) and bring down via the fixpoint.
        obtain ⟨k, hk⟩ := Nat.le.dest (Nat.le_of_succ_le hij)
        rw [← hk] at hj
        exact (msCongruenceIterate_fixpoint_add G R hR i hfix k u v).mpr hj
    · -- R^i u v → R* u v: witness is i.
      intro h
      exact ⟨i, h⟩


proof_of msCongruenceClosure_least := ⟨msCongruenceClosure_isCongruence G R hR,
  -- BEGIN PROOF
      msCongruenceClosure_contains G R hR,
      msCongruenceClosure_smallest G R hR⟩


end LCS.FirstOrder.ManySorted.CongruenceClosure
