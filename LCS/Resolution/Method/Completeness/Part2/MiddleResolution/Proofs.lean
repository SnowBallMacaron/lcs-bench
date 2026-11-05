import LCS.Resolution.Method.Completeness.Part2.MiddleResolution
import LCS.Resolution.Method.Completeness.Part2.InnerResolution.Proofs

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

helper theorem Completeness.replay_ex436ComputedInner (P Q : Nat) (f : Clause → Clause) :
    replay (ex436ComputedInner P Q) f = ex436ComputedInnerReplay P Q f := by
  have h0 : replayLabel (ex436ComputedInner P Q) f ⟨0, by change 0 < 6; decide⟩ =
      f (Clause.ofList [.neg P]) := by
    rw [replayLabel]
    rfl
  have h1 : replayLabel (ex436ComputedInner P Q) f ⟨1, by change 1 < 6; decide⟩ =
      f (Clause.ofList [.pos P, .pos Q]) := by
    rw [replayLabel]
    rfl
  have h2 : replayLabel (ex436ComputedInner P Q) f ⟨2, by change 2 < 6; decide⟩ =
      GCNF.Clause.union (GCNF.Clause.remove (f (Clause.ofList [.neg P])) (Literal.neg P)) (GCNF.Clause.remove (f (Clause.ofList [.pos P, .pos Q])) (Literal.neg P).conjugate) := by
    rw [replayLabel]
    change GCNF.Clause.union (GCNF.Clause.remove (replayLabel (ex436ComputedInner P Q) f ⟨0, _⟩) (Literal.neg P))
      (GCNF.Clause.remove (replayLabel (ex436ComputedInner P Q) f ⟨1, _⟩) (Literal.neg P).conjugate) = _
    rw [h0, h1]
  have h3 : replayLabel (ex436ComputedInner P Q) f ⟨3, by change 3 < 6; decide⟩ =
      f (Clause.ofList [.neg Q]) := by
    rw [replayLabel]
    rfl
  have h4 : replayLabel (ex436ComputedInner P Q) f ⟨4, by change 4 < 6; decide⟩ =
      f (Clause.ofList [.pos Q]) := by
    rw [replayLabel]
    rfl
  have h5 : replayLabel (ex436ComputedInner P Q) f ⟨5, by change 5 < 6; decide⟩ =
      GCNF.Clause.union (GCNF.Clause.remove (f (Clause.ofList [.neg Q])) (Literal.neg Q)) (GCNF.Clause.remove (GCNF.Clause.union (GCNF.Clause.remove (f (Clause.ofList [.neg P])) (Literal.neg P)) (GCNF.Clause.remove (f (Clause.ofList [.pos P, .pos Q])) (Literal.neg P).conjugate)) (Literal.neg Q).conjugate) := by
    rw [replayLabel]
    change GCNF.Clause.union (GCNF.Clause.remove (replayLabel (ex436ComputedInner P Q) f ⟨3, _⟩) (Literal.neg Q))
      (GCNF.Clause.remove (replayLabel (ex436ComputedInner P Q) f ⟨2, _⟩) (Literal.neg Q).conjugate) = _
    rw [h3, h2]
  simp only [replay, ex436ComputedInner, List.ofFn_succ, List.ofFn_zero]
  change (⟨[⟨replayLabel (ex436ComputedInner P Q) f ⟨0, _⟩, none⟩,
    ⟨replayLabel (ex436ComputedInner P Q) f ⟨1, _⟩, none⟩,
    ⟨replayLabel (ex436ComputedInner P Q) f ⟨2, _⟩, some ⟨.neg P, 0, 1⟩⟩,
    ⟨replayLabel (ex436ComputedInner P Q) f ⟨3, _⟩, none⟩,
    ⟨replayLabel (ex436ComputedInner P Q) f ⟨4, _⟩, none⟩,
    ⟨replayLabel (ex436ComputedInner P Q) f ⟨5, _⟩, some ⟨.neg Q, 3, 2⟩⟩], 5⟩ : FiniteGraph) = _
  rw [h0, h1, h2, h3, h4, h5]
  rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

helper theorem Completeness.replay_ex436NarratedMiddleComputed (P Q R : Nat) (f : Clause → Clause) :
    replay (ex436NarratedMiddleComputed P Q R) f = ex436NarratedMiddleComputedReplay P Q R f := by
  have h0 : replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨0, by change 0 < 9; decide⟩ =
      f (Clause.ofList [.neg P, .pos R]) := by
    rw [replayLabel]
    rfl
  have h1 : replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨1, by change 1 < 9; decide⟩ =
      f (Clause.ofList [.pos P, .pos Q]) := by
    rw [replayLabel]
    rfl
  have h2 : replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨2, by change 2 < 9; decide⟩ =
      GCNF.Clause.union (GCNF.Clause.remove (f (Clause.ofList [.neg P, .pos R])) (Literal.neg P)) (GCNF.Clause.remove (f (Clause.ofList [.pos P, .pos Q])) (Literal.neg P).conjugate) := by
    rw [replayLabel]
    change GCNF.Clause.union (GCNF.Clause.remove (replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨0, _⟩) (Literal.neg P))
      (GCNF.Clause.remove (replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨1, _⟩) (Literal.neg P).conjugate) = _
    rw [h0, h1]
  have h3 : replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨3, by change 3 < 9; decide⟩ =
      f (Clause.ofList [.neg Q]) := by
    rw [replayLabel]
    rfl
  have h4 : replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨4, by change 4 < 9; decide⟩ =
      f (Clause.ofList [.pos Q, .pos R]) := by
    rw [replayLabel]
    rfl
  have h5 : replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨5, by change 5 < 9; decide⟩ =
      GCNF.Clause.union (GCNF.Clause.remove (f (Clause.ofList [.neg Q])) (Literal.neg Q)) (GCNF.Clause.remove (GCNF.Clause.union (GCNF.Clause.remove (f (Clause.ofList [.neg P, .pos R])) (Literal.neg P)) (GCNF.Clause.remove (f (Clause.ofList [.pos P, .pos Q])) (Literal.neg P).conjugate)) (Literal.neg Q).conjugate) := by
    rw [replayLabel]
    change GCNF.Clause.union (GCNF.Clause.remove (replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨3, _⟩) (Literal.neg Q))
      (GCNF.Clause.remove (replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨2, _⟩) (Literal.neg Q).conjugate) = _
    rw [h3, h2]
  have h6 : replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨6, by change 6 < 9; decide⟩ =
      f (Clause.ofList [.neg R]) := by
    rw [replayLabel]
    rfl
  have h7 : replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨7, by change 7 < 9; decide⟩ =
      f (Clause.ofList [.pos R]) := by
    rw [replayLabel]
    rfl
  have h8 : replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨8, by change 8 < 9; decide⟩ =
      GCNF.Clause.union (GCNF.Clause.remove (f (Clause.ofList [.neg R])) (Literal.neg R)) (GCNF.Clause.remove (GCNF.Clause.union (GCNF.Clause.remove (f (Clause.ofList [.neg Q])) (Literal.neg Q)) (GCNF.Clause.remove (GCNF.Clause.union (GCNF.Clause.remove (f (Clause.ofList [.neg P, .pos R])) (Literal.neg P)) (GCNF.Clause.remove (f (Clause.ofList [.pos P, .pos Q])) (Literal.neg P).conjugate)) (Literal.neg Q).conjugate)) (Literal.neg R).conjugate) := by
    rw [replayLabel]
    change GCNF.Clause.union (GCNF.Clause.remove (replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨6, _⟩) (Literal.neg R))
      (GCNF.Clause.remove (replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨5, _⟩) (Literal.neg R).conjugate) = _
    rw [h6, h5]
  simp only [replay, ex436NarratedMiddleComputed, List.ofFn_succ, List.ofFn_zero]
  change (⟨[⟨replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨0, _⟩, none⟩,
    ⟨replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨1, _⟩, none⟩,
    ⟨replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨2, _⟩, some ⟨.neg P, 0, 1⟩⟩,
    ⟨replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨3, _⟩, none⟩,
    ⟨replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨4, _⟩, none⟩,
    ⟨replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨5, _⟩, some ⟨.neg Q, 3, 2⟩⟩,
    ⟨replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨6, _⟩, none⟩,
    ⟨replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨7, _⟩, none⟩,
    ⟨replayLabel (ex436NarratedMiddleComputed P Q R) f ⟨8, _⟩, some ⟨.neg R, 6, 5⟩⟩], 8⟩ : FiniteGraph) = _
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

helper theorem Completeness.replay_ex436DisplayedMiddleComputed (P Q R : Nat) (f : Clause → Clause) :
    replay (ex436DisplayedMiddleComputed P Q R) f = ex436DisplayedMiddleComputedReplay P Q R f := by
  have h0 : replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨0, by change 0 < 9; decide⟩ =
      f (Clause.ofList [.neg R]) := by
    rw [replayLabel]
    rfl
  have h1 : replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨1, by change 1 < 9; decide⟩ =
      f (Clause.ofList [.pos R, .neg P]) := by
    rw [replayLabel]
    rfl
  have h2 : replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨2, by change 2 < 9; decide⟩ =
      GCNF.Clause.union (GCNF.Clause.remove (f (Clause.ofList [.neg R])) (Literal.neg R)) (GCNF.Clause.remove (f (Clause.ofList [.pos R, .neg P])) (Literal.neg R).conjugate) := by
    rw [replayLabel]
    change GCNF.Clause.union (GCNF.Clause.remove (replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨0, _⟩) (Literal.neg R))
      (GCNF.Clause.remove (replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨1, _⟩) (Literal.neg R).conjugate) = _
    rw [h0, h1]
  have h3 : replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨3, by change 3 < 9; decide⟩ =
      f (Clause.ofList [.neg P]) := by
    rw [replayLabel]
    rfl
  have h4 : replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨4, by change 4 < 9; decide⟩ =
      f (Clause.ofList [.pos P, .pos Q]) := by
    rw [replayLabel]
    rfl
  have h5 : replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨5, by change 5 < 9; decide⟩ =
      GCNF.Clause.union (GCNF.Clause.remove (GCNF.Clause.union (GCNF.Clause.remove (f (Clause.ofList [.neg R])) (Literal.neg R)) (GCNF.Clause.remove (f (Clause.ofList [.pos R, .neg P])) (Literal.neg R).conjugate)) (Literal.neg P)) (GCNF.Clause.remove (f (Clause.ofList [.pos P, .pos Q])) (Literal.neg P).conjugate) := by
    rw [replayLabel]
    change GCNF.Clause.union (GCNF.Clause.remove (replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨2, _⟩) (Literal.neg P))
      (GCNF.Clause.remove (replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨4, _⟩) (Literal.neg P).conjugate) = _
    rw [h2, h4]
  have h6 : replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨6, by change 6 < 9; decide⟩ =
      f (Clause.ofList [.neg Q]) := by
    rw [replayLabel]
    rfl
  have h7 : replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨7, by change 7 < 9; decide⟩ =
      f (Clause.ofList [.pos Q]) := by
    rw [replayLabel]
    rfl
  have h8 : replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨8, by change 8 < 9; decide⟩ =
      GCNF.Clause.union (GCNF.Clause.remove (f (Clause.ofList [.neg Q])) (Literal.neg Q)) (GCNF.Clause.remove (GCNF.Clause.union (GCNF.Clause.remove (GCNF.Clause.union (GCNF.Clause.remove (f (Clause.ofList [.neg R])) (Literal.neg R)) (GCNF.Clause.remove (f (Clause.ofList [.pos R, .neg P])) (Literal.neg R).conjugate)) (Literal.neg P)) (GCNF.Clause.remove (f (Clause.ofList [.pos P, .pos Q])) (Literal.neg P).conjugate)) (Literal.neg Q).conjugate) := by
    rw [replayLabel]
    change GCNF.Clause.union (GCNF.Clause.remove (replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨6, _⟩) (Literal.neg Q))
      (GCNF.Clause.remove (replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨5, _⟩) (Literal.neg Q).conjugate) = _
    rw [h6, h5]
  simp only [replay, ex436DisplayedMiddleComputed, List.ofFn_succ, List.ofFn_zero]
  change (⟨[⟨replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨0, _⟩, none⟩,
    ⟨replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨1, _⟩, none⟩,
    ⟨replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨2, _⟩, some ⟨.neg R, 0, 1⟩⟩,
    ⟨replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨3, _⟩, none⟩,
    ⟨replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨4, _⟩, none⟩,
    ⟨replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨5, _⟩, some ⟨.neg P, 2, 4⟩⟩,
    ⟨replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨6, _⟩, none⟩,
    ⟨replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨7, _⟩, none⟩,
    ⟨replayLabel (ex436DisplayedMiddleComputed P Q R) f ⟨8, _⟩, some ⟨.neg Q, 6, 5⟩⟩], 8⟩ : FiniteGraph) = _
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D5_isReplay := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    rw [replay_ex436ComputedInner]
    simp [ex436ComputedInnerReplay, ex436ComputedD5, missingLift, ex436MiddleSequent,
      ClauseSequent.ofList, Clause.single_eq_ofList_singleton, clauseList_eq_iff,
      clauseWithLiteral_list, remove_clauseList, union_clauseList, Literal.conjugate,
      hPQ, Ne.symm hPQ, hPR, Ne.symm hPR, hQR, Ne.symm hQR,
      FiniteGraph.mk.injEq, FiniteGraph.Node.mk.injEq]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436Shorter_isReplay := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    rw [replay_ex436ComputedInner]
    simp [ex436ComputedInnerReplay, ex436ShorterLiftedComputed, missingLift, ex436Sequent,
      ClauseSequent.ofList, Clause.single_eq_ofList_singleton, clauseList_eq_iff,
      clauseWithLiteral_list, remove_clauseList, union_clauseList, Literal.conjugate,
      hPQ, Ne.symm hPQ, hPR, Ne.symm hPR, hQR, Ne.symm hQR,
      FiniteGraph.mk.injEq, FiniteGraph.Node.mk.injEq]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D8_isReplay := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    rw [replay_ex436NarratedMiddleComputed]
    simp [ex436NarratedMiddleComputedReplay, ex436NarratedComputed, missingLift, ex436Sequent,
      ClauseSequent.ofList, Clause.single_eq_ofList_singleton, clauseList_eq_iff,
      clauseWithLiteral_list, remove_clauseList, union_clauseList, Literal.conjugate,
      hPQ, Ne.symm hPQ, hPR, Ne.symm hPR, hQR, Ne.symm hQR,
      FiniteGraph.mk.injEq, FiniteGraph.Node.mk.injEq, methodEmpty_clauseList]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436Displayed_isReplay := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    rw [replay_ex436DisplayedMiddleComputed]
    simp [ex436DisplayedMiddleComputedReplay, ex436DisplayedLiftedComputed, missingLift, ex436Sequent,
      ClauseSequent.ofList, Clause.single_eq_ofList_singleton, clauseList_eq_iff,
      clauseWithLiteral_list, remove_clauseList, union_clauseList, Literal.conjugate,
      hPQ, Ne.symm hPQ, hPR, Ne.symm hPR, hQR, Ne.symm hQR,
      FiniteGraph.mk.injEq, FiniteGraph.Node.mk.injEq]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

helper theorem Completeness.clauseWithLiteral_append (ls : List Literal) (L : Literal) :
    clauseWithLiteral (Clause.ofList ls) L = Clause.ofList (ls ++ [L]) := by
  apply LCS.Finset.ext
  intro M
  simp [clauseWithLiteral, Clause.ofList, or_comm]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

helper theorem Completeness.ex436_pairOrder (P R : Nat) :
    Clause.ofList [.neg P, .pos R] = Clause.ofList [.pos R, .neg P] := by
  simp [clauseList_eq_iff]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

helper @[simp] theorem Completeness.leavesIn_ex436ComputedInner (P Q : Nat) (Γ : ClauseSequent) :
    leavesIn (ex436ComputedInner P Q) Γ =
      (decide (Clause.ofList [.neg Q] ∈ Γ) &&
        (decide (Clause.ofList [.neg P] ∈ Γ) && decide (Clause.ofList [.pos P, .pos Q] ∈ Γ))) := by
  change (decide (Clause.ofList [.neg Q] ∈ Γ) &&
    (decide (Clause.ofList [.neg P] ∈ Γ) && (decide (Clause.ofList [.pos P, .pos Q] ∈ Γ) && true))) = _
  simp

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

helper @[simp] theorem Completeness.leavesIn_ex436NarratedMiddle (P Q R : Nat) (Γ : ClauseSequent) :
    leavesIn (ex436NarratedMiddleComputed P Q R) Γ =
      (decide (Clause.ofList [.neg R] ∈ Γ) && (decide (Clause.ofList [.neg Q] ∈ Γ) &&
        (decide (Clause.ofList [.neg P, .pos R] ∈ Γ) && decide (Clause.ofList [.pos P, .pos Q] ∈ Γ)))) := by
  change (decide (Clause.ofList [.neg R] ∈ Γ) && (decide (Clause.ofList [.neg Q] ∈ Γ) &&
    (decide (Clause.ofList [.neg P, .pos R] ∈ Γ) &&
      (decide (Clause.ofList [.pos P, .pos Q] ∈ Γ) && true)))) = _
  simp

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

helper @[simp] theorem Completeness.leavesIn_ex436DisplayedMiddle (P Q R : Nat) (Γ : ClauseSequent) :
    leavesIn (ex436DisplayedMiddleComputed P Q R) Γ =
      (decide (Clause.ofList [.neg Q] ∈ Γ) && (decide (Clause.ofList [.neg R] ∈ Γ) &&
        (decide (Clause.ofList [.pos R, .neg P] ∈ Γ) && decide (Clause.ofList [.pos P, .pos Q] ∈ Γ)))) := by
  change (decide (Clause.ofList [.neg Q] ∈ Γ) && (decide (Clause.ofList [.neg R] ∈ Γ) &&
    (decide (Clause.ofList [.pos R, .neg P] ∈ Γ) &&
      (decide (Clause.ofList [.pos P, .pos Q] ∈ Γ) && true)))) = _
  simp

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436NarratedMiddleConversion_raw := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    have hseq : LCS.Finset.union
        (ClauseSequent.ofList [Clause.single (.neg R), Clause.single (.neg Q),
          Clause.ofList [.pos P, .pos Q]])
        (ClauseSequent.mapSet (ClauseSequent.single (Clause.single (.neg P)))
          (fun A => clauseWithLiteral A (.pos R))) = ex436MiddleSequent P Q R := by
      apply LCS.Finset.ext
      intro C
      simp [ex436MiddleSequent, ClauseSequent.ofList, ClauseSequent.single,
        ClauseSequent.mapSet, ex436_pairOrder, or_assoc, or_left_comm, or_comm, eq_comm]
    have hl : leavesIn (ex436ComputedInner P Q) (ex436MiddleSequent P Q R) = false := by
      simp [ex436MiddleSequent, ClauseSequent.ofList, Clause.single_eq_ofList_singleton,
        clauseList_eq_iff, hPQ, Ne.symm hPQ, hPR, Ne.symm hPR, hQR, Ne.symm hQR]
    have hr : leavesIn (complementaryGraph (.neg R)) (ex436MiddleSequent P Q R) = false := by
      simp [ex436MiddleSequent, ClauseSequent.ofList, Clause.single_eq_ofList_singleton,
        clauseList_eq_iff, Literal.conjugate, hPR, Ne.symm hPR, hQR, Ne.symm hQR]
    refine (gcnfProofToResolution_transport _ _ _).trans ?_
    refine (gcnfProofToResolution_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans ?_
    simp only [ex436NarratedMiddleProof, gcnfProofToResolution_transport,
      gcnfProofToResolution_rule, convertDisplayedNegativeFirstAxiom,
      ex436InnerConversion_raw P Q hPQ, hseq, hl, hr, Bool.false_eq_true, ↓reduceIte,
      ex436D5_isReplay P Q R hPQ hPR hQR]
    simp [ex436ComputedD5, FiniteGraph.rootLabel, FiniteGraph.label, FiniteGraph.node,
      clauseList_eq_iff, methodEmpty_clauseList, empty_clauseList, List.findIdx_cons, List.findIdx_nil,
      coalesceInputLeaves_compute, FiniteGraph.graft, complementaryGraph, unitInputs,
      FiniteGraph.canonicalInput, ex436NarratedMiddleComputed, Literal.conjugate,
      Clause.single_eq_ofList_singleton, hPQ, Ne.symm hPQ, hPR, Ne.symm hPR, hQR, Ne.symm hQR]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436ShorterConversion_raw := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    have hseq : LCS.Finset.union
        (ClauseSequent.ofList [Clause.single (.neg R), Clause.single (.neg Q)])
        (ClauseSequent.mapSet (ClauseSequent.ofList [Clause.single (.neg P), Clause.ofList [.pos P, .pos Q]])
          (fun A => clauseWithLiteral A (.pos R))) = ex436Sequent P Q R := by
      apply LCS.Finset.ext
      intro C
      simp [ex436Sequent, ClauseSequent.ofList,
        ClauseSequent.mapSet, ex436_pairOrder, clauseWithLiteral_append,
        or_assoc, or_left_comm, or_comm, eq_comm]
    have hl : leavesIn (ex436ComputedInner P Q) (ex436Sequent P Q R) = false := by
      simp [ex436Sequent, ClauseSequent.ofList, Clause.single_eq_ofList_singleton,
        clauseList_eq_iff, hPQ, Ne.symm hPQ, hPR, Ne.symm hPR, hQR, Ne.symm hQR]
    have hr : leavesIn (complementaryGraph (.neg R)) (ex436Sequent P Q R) = false := by
      simp [ex436Sequent, ClauseSequent.ofList, Clause.single_eq_ofList_singleton,
        clauseList_eq_iff, Literal.conjugate, hPR, Ne.symm hPR, hQR, Ne.symm hQR]
    refine (gcnfProofToResolution_transport _ _ _).trans ?_
    refine (gcnfProofToResolution_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans ?_
    simp only [ex436ShorterProof, gcnfProofToResolution_transport,
      gcnfProofToResolution_rule, convertDisplayedNegativeFirstAxiom,
      ex436InnerConversion_raw P Q hPQ, hseq, hl, hr, Bool.false_eq_true, ↓reduceIte,
      ex436Shorter_isReplay P Q R hPQ hPR hQR]
    simp [ex436ShorterLiftedComputed, FiniteGraph.rootLabel, FiniteGraph.label, FiniteGraph.node,
      clauseList_eq_iff, methodEmpty_clauseList, empty_clauseList, List.findIdx_cons, List.findIdx_nil,
      coalesceInputLeaves_compute, FiniteGraph.graft, complementaryGraph, unitInputs,
      FiniteGraph.canonicalInput, ex436NarratedComputed, Literal.conjugate,
      Clause.single_eq_ofList_singleton, hPQ, Ne.symm hPQ, hPR, Ne.symm hPR, hQR, Ne.symm hQR]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436DisplayedFirstLifted_isReplay := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    rw [replay_complementaryGraph]
    simp [missingLift, ex436MiddleSequent, ClauseSequent.ofList,
      Clause.single_eq_ofList_singleton, clauseList_eq_iff, clauseWithLiteral_list,
      remove_clauseList, union_clauseList, Literal.conjugate,
      hPR, Ne.symm hPR, hQR, Ne.symm hQR,
      ex436DisplayedFirstLifted, FiniteGraph.mk.injEq, FiniteGraph.Node.mk.injEq]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436DisplayedMiddleConversion_raw := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    have hseq : LCS.Finset.union
        (ClauseSequent.ofList [Clause.single (.neg R), Clause.single (.neg Q),
          Clause.ofList [.pos P, .pos Q]])
        (ClauseSequent.mapSet (ClauseSequent.single (Clause.single (.pos R)))
          (fun A => clauseWithLiteral A (.neg P))) = ex436MiddleSequent P Q R := by
      apply LCS.Finset.ext
      intro C
      simp [ex436MiddleSequent, ClauseSequent.ofList, ClauseSequent.single,
        ClauseSequent.mapSet, or_assoc, or_left_comm, or_comm, eq_comm]
    have hl : leavesIn (complementaryGraph (.neg R)) (ex436MiddleSequent P Q R) = false := by
      simp [ex436MiddleSequent, ClauseSequent.ofList, Clause.single_eq_ofList_singleton,
        clauseList_eq_iff, Literal.conjugate, hPR, Ne.symm hPR, hQR, Ne.symm hQR]
    have hr : leavesIn (ex436ComputedInner P Q) (ex436MiddleSequent P Q R) = false := by
      simp [ex436MiddleSequent, ClauseSequent.ofList, Clause.single_eq_ofList_singleton,
        clauseList_eq_iff, hPQ, Ne.symm hPQ, hPR, Ne.symm hPR, hQR, Ne.symm hQR]
    refine (gcnfProofToResolution_transport _ _ _).trans ?_
    refine (gcnfProofToResolution_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans ?_
    simp only [ex436MiddleProof, gcnfProofToResolution_transport,
      gcnfProofToResolution_rule, convertDisplayedNegativeFirstAxiom,
      ex436InnerConversion_raw P Q hPQ, hseq, hl, hr, Bool.false_eq_true, ↓reduceIte,
      ex436DisplayedFirstLifted_isReplay P Q R hPQ hPR hQR]
    simp [ex436DisplayedFirstLifted, FiniteGraph.rootLabel, FiniteGraph.label, FiniteGraph.node,
      clauseList_eq_iff, methodEmpty_clauseList, empty_clauseList, List.findIdx_cons, List.findIdx_nil,
      coalesceInputLeaves_compute, FiniteGraph.graft, ex436ComputedInner, unitInputs,
      FiniteGraph.canonicalInput, ex436DisplayedMiddleComputed,
      Clause.single_eq_ofList_singleton, hPQ, Ne.symm hPQ, hPR, Ne.symm hPR, hQR, Ne.symm hQR]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436NarratedConversion_raw := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    set_option backward.isDefEq.respectTransparency false in
      have hseq : LCS.Finset.union
          (ClauseSequent.ofList [Clause.single (.neg R), Clause.single (.neg Q),
            Clause.ofList [.pos R, .neg P]])
          (ClauseSequent.mapSet (ClauseSequent.single (Clause.ofList [.pos P, .pos Q]))
            (fun A => clauseWithLiteral A (.pos R))) = ex436Sequent P Q R := by
        apply LCS.Finset.ext
        intro C
        simp [ex436Sequent, ClauseSequent.ofList, ClauseSequent.single,
          ClauseSequent.mapSet, clauseWithLiteral_append, or_left_comm, or_comm, eq_comm]
      have hl : leavesIn (ex436NarratedMiddleComputed P Q R) (ex436Sequent P Q R) = false := by
        simp [ex436Sequent, ClauseSequent.ofList, Clause.single_eq_ofList_singleton,
          clauseList_eq_iff, hPQ, Ne.symm hPQ, hPR, Ne.symm hPR, hQR, Ne.symm hQR]
      have hr : leavesIn (complementaryGraph (.neg R)) (ex436Sequent P Q R) = false := by
        simp [ex436Sequent, ClauseSequent.ofList, Clause.single_eq_ofList_singleton,
          clauseList_eq_iff, Literal.conjugate, hPR, Ne.symm hPR, hQR, Ne.symm hQR]
      unfold ex436NarratedProof ex436WithMiddleProof
      refine (gcnfProofToResolution_transport hseq _ _).trans ?_
      refine (gcnfProofToResolution_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans ?_
      simp only [ex436NarratedProof, ex436WithMiddleProof, gcnfProofToResolution_transport,
        gcnfProofToResolution_rule, convertDisplayedNegativeFirstAxiom,
        ex436NarratedMiddleConversion_raw P Q R hPQ hPR hQR, hseq, hl, hr,
        Bool.false_eq_true, ↓reduceIte, ex436D8_isReplay P Q R hPQ hPR hQR]
      have he : (ex436NarratedComputed P Q R).rootLabel = some GCNF.Clause.empty := rfl
      rw [ite_eq_left he]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436DisplayedConversion_raw := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    set_option backward.isDefEq.respectTransparency false in
      have hseq : LCS.Finset.union
          (ClauseSequent.ofList [Clause.single (.neg R), Clause.single (.neg Q),
            Clause.ofList [.pos R, .neg P]])
          (ClauseSequent.mapSet (ClauseSequent.single (Clause.ofList [.pos P, .pos Q]))
            (fun A => clauseWithLiteral A (.pos R))) = ex436Sequent P Q R := by
        apply LCS.Finset.ext
        intro C
        simp [ex436Sequent, ClauseSequent.ofList, ClauseSequent.single,
          ClauseSequent.mapSet, clauseWithLiteral_append, or_left_comm, or_comm, eq_comm]
      have hl : leavesIn (ex436DisplayedMiddleComputed P Q R) (ex436Sequent P Q R) = false := by
        simp [ex436Sequent, ClauseSequent.ofList, Clause.single_eq_ofList_singleton,
          clauseList_eq_iff, hPQ, Ne.symm hPQ, hPR, Ne.symm hPR, hQR, Ne.symm hQR]
      have hr : leavesIn (complementaryGraph (.neg R)) (ex436Sequent P Q R) = false := by
        simp [ex436Sequent, ClauseSequent.ofList, Clause.single_eq_ofList_singleton,
          clauseList_eq_iff, Literal.conjugate, hPR, Ne.symm hPR, hQR, Ne.symm hQR]
      unfold ex436Proof ex436WithMiddleProof
      refine (gcnfProofToResolution_transport hseq _ _).trans ?_
      refine (gcnfProofToResolution_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans ?_
      simp only [ex436Proof, ex436WithMiddleProof, gcnfProofToResolution_transport,
        gcnfProofToResolution_rule, convertDisplayedNegativeFirstAxiom,
        ex436DisplayedMiddleConversion_raw P Q R hPQ hPR hQR, hseq, hl, hr,
        Bool.false_eq_true, ↓reduceIte, ex436Displayed_isReplay P Q R hPQ hPR hQR]
      simp [ex436DisplayedLiftedComputed, FiniteGraph.rootLabel, FiniteGraph.label, FiniteGraph.node,
        clauseList_eq_iff, methodEmpty_clauseList, empty_clauseList, List.findIdx_cons, List.findIdx_nil,
        coalesceInputLeaves_compute, FiniteGraph.graft, complementaryGraph, unitInputs,
        FiniteGraph.canonicalInput, ex436DisplayedComputed, Literal.conjugate,
        Clause.single_eq_ofList_singleton, hPQ, Ne.symm hPQ, hPR, Ne.symm hPR, hQR, Ne.symm hQR]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436NarratedComputed_counts := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  ⟨rfl, rfl⟩

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436DisplayedComputed_counts := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  ⟨rfl, rfl⟩

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436DisplayedConversion_counts := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    rw [ex436DisplayedConversion_raw P Q R hPQ hPR hQR]
    exact ex436DisplayedComputed_counts P Q R

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436NarratedConversion_counts := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    rw [ex436NarratedConversion_raw P Q R hPQ hPR hQR]
    exact ex436NarratedComputed_counts P Q R

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436ShorterConversion_counts := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    rw [ex436ShorterConversion_raw P Q R hPQ hPR hQR]
    exact ex436NarratedComputed_counts P Q R

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436NarratedComputed_matches_D8 := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    have hcomp : (ex436NarratedComputed P Q R).vertexIds = [8, 6, 5, 3, 2, 0, 1] := rfl
    have hsource : (ex436D8 P Q R).vertexIds = [6, 5, 4, 0, 1, 2, 3] := rfl
    refine ⟨?_, ?_, rfl, ?_⟩
    · intro i hi
      rw [hcomp] at hi
      rw [hsource]
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [ex436NarratedVertexMap, ex436NarratedVertexMapInv, ex436NarratedComputed,
        ex436D8, FiniteGraph.label, FiniteGraph.node, methodEmpty_clauseList, clauseList_eq_iff]
    · intro j hj
      rw [hsource] at hj
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [hcomp, ex436NarratedVertexMap, ex436NarratedVertexMapInv]
    · intro i hi j hj
      rw [hcomp] at hi hj
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi hj
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [FiniteGraph.hasEdge, ex436NarratedVertexMap, ex436NarratedComputed, ex436D8,
        FiniteGraph.next, FiniteGraph.node]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436NarratedMiddleComputed_matches_D7 := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    have hcomp : (ex436NarratedMiddleComputed P Q R).vertexIds = [8, 6, 5, 3, 2, 0, 1] := rfl
    have hsource : (ex436D7 P Q R).vertexIds = [6, 5, 4, 0, 1, 2, 3] := rfl
    refine ⟨?_, ?_, rfl, ?_⟩
    · intro i hi
      rw [hcomp] at hi
      rw [hsource]
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [ex436NarratedVertexMap, ex436NarratedVertexMapInv, ex436NarratedMiddleComputed,
        ex436D7, FiniteGraph.label, FiniteGraph.node, methodEmpty_clauseList, clauseList_eq_iff]
    · intro j hj
      rw [hsource] at hj
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [hcomp, ex436NarratedVertexMap, ex436NarratedVertexMapInv]
    · intro i hi j hj
      rw [hcomp] at hi hj
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi hj
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [FiniteGraph.hasEdge, ex436NarratedVertexMap, ex436NarratedMiddleComputed, ex436D7,
        FiniteGraph.next, FiniteGraph.node]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436ComputedInner_matches_D4 := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    have hcomp : (ex436ComputedInner P Q).vertexIds = [5, 3, 2, 0, 1] := rfl
    have hsource : (ex436D4 P Q).vertexIds = [4, 3, 0, 1, 2] := rfl
    refine ⟨?_, ?_, rfl, ?_⟩
    · intro i hi
      rw [hcomp] at hi
      rw [hsource]
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl
      all_goals simp [ex436InnerVertexMap, ex436InnerVertexMapInv, ex436ComputedInner,
        ex436D4, FiniteGraph.label, FiniteGraph.node, methodEmpty_clauseList]
    · intro j hj
      rw [hsource] at hj
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl
      all_goals simp [hcomp, ex436InnerVertexMap, ex436InnerVertexMapInv]
    · intro i hi j hj
      rw [hcomp] at hi hj
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi hj
      rcases hi with rfl | rfl | rfl | rfl | rfl
      all_goals rcases hj with rfl | rfl | rfl | rfl | rfl
      all_goals simp [FiniteGraph.hasEdge, ex436InnerVertexMap, ex436ComputedInner, ex436D4,
        FiniteGraph.next, FiniteGraph.node]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436ComputedD5_matches_D5 := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    have hcomp : (ex436ComputedD5 P Q R).vertexIds = [5, 3, 2, 0, 1] := rfl
    have hsource : (ex436D5 P Q R).vertexIds = [4, 3, 0, 1, 2] := rfl
    refine ⟨?_, ?_, rfl, ?_⟩
    · intro i hi
      rw [hcomp] at hi
      rw [hsource]
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl
      all_goals simp [ex436InnerVertexMap, ex436InnerVertexMapInv, ex436ComputedD5,
        ex436D5, FiniteGraph.label, FiniteGraph.node, clauseList_eq_iff]
    · intro j hj
      rw [hsource] at hj
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl
      all_goals simp [hcomp, ex436InnerVertexMap, ex436InnerVertexMapInv]
    · intro i hi j hj
      rw [hcomp] at hi hj
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi hj
      rcases hi with rfl | rfl | rfl | rfl | rfl
      all_goals rcases hj with rfl | rfl | rfl | rfl | rfl
      all_goals simp [FiniteGraph.hasEdge, ex436InnerVertexMap, ex436ComputedD5, ex436D5,
        FiniteGraph.next, FiniteGraph.node]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436NarratedProof_matches_D8 := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    rw [ex436NarratedConversion_raw P Q R hPQ hPR hQR]
    exact ex436NarratedComputed_matches_D8 P Q R

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D3_graft_D2 := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    simp [ex436D3, ex436D2, FiniteGraph.node, clauseList_eq_iff,
      methodEmpty_clauseList, List.findIdx_cons, List.findIdx_nil,
      coalesceInputLeaves_compute, FiniteGraph.graft, unitInputs,
      FiniteGraph.canonicalInput, ex436ComputedInner, hPQ, Ne.symm hPQ,
      Clause.single_eq_ofList_singleton]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D5_graft_D6 := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    simp [ex436ComputedD5, ex436D6, FiniteGraph.node, clauseList_eq_iff,
      methodEmpty_clauseList, List.findIdx_cons, List.findIdx_nil,
      coalesceInputLeaves_compute, FiniteGraph.graft, unitInputs,
      FiniteGraph.canonicalInput, ex436NarratedMiddleComputed,
      hPQ, Ne.symm hPQ, hPR, Ne.symm hPR, hQR, Ne.symm hQR,
      Clause.single_eq_ofList_singleton]

end LCS.Resolution.Method.Completeness
end
end
