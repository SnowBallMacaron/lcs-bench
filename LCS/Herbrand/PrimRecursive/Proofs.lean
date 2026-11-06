import LCS.Herbrand.PrimRecursive

namespace LCS.Herbrand.PrimRecursive

namespace minimize

proof_of domainIff := open LCS.Herbrand.PrimRecursive.Proofs.minimize in
  by
    classical
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, hy.1, ?_⟩
      intro z hz
      by_cases he : z = y
      · subst z
        exact ⟨0, hy.1⟩
      · obtain ⟨v, hv, _⟩ := hy.2 z (by omega)
        exact ⟨v, hv⟩
    · rintro ⟨y, hy, hp⟩
      induction y using Nat.strongRecOn with
      | ind y ih =>
        by_cases he : ∃ z, z < y ∧
            g (fun i => if h : i.val < n then args ⟨i.val, h⟩ else z) = some 0
        · obtain ⟨z, hz, hzero⟩ := he
          exact ih z hz hzero (fun k hk => hp k (by omega))
        · refine ⟨y, hy, ?_⟩
          intro z hz
          obtain ⟨v, hv⟩ := hp z (by omega)
          refine ⟨v, hv, ?_⟩
          intro hvzero
          exact he ⟨z, hz, hv.trans (congrArg some hvzero)⟩


end minimize

proof_of ackermannIsRecursive := by
  -- REPAIR(T7-114): proof pending
  sorry


proof_of ackermannNotPrimitiveRecursive := by
  -- REPAIR(T7-114): proof pending
  sorry


end LCS.Herbrand.PrimRecursive
