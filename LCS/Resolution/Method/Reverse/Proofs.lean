import LCS.Resolution.Method.Reverse

namespace LCS.Resolution.Method

open LCS.Resolution.GCNF

namespace FiniteGraph

proof_of toGCNF_nodeCount_bound := by
  have hOutput := LCS.Resolution.GCNF.Proofs.GCNFProofTree.nodeCount_eq_two_leafCount_sub_one
    (g.toGCNF S hRef hOrdinary)
  have hLeaves := g.toGCNF_leafCount_le_unfold S hRef hOrdinary
  have hInput := g.unfold_steps_add_one_le_nodeCount hRef.1 hTree
  omega


proof_of toGCNF_quotient_nodeCount_bound := by
  rw [LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph.toResolutionDAG_nodeCount g hRef.1]
  exact g.toGCNF_nodeCount_bound S hRef hOrdinary hTree


helper /-- A legal refutation containing a redundant inference at the literal that
the source subsequently asks to delete.  All five input clauses are ordinary,
and none is a unit clause. -/
def deletionCounterexample : FiniteGraph :=
  ⟨[
    ⟨GCNF.Clause.ofList [.pos 0, .pos 2], none⟩,
    ⟨GCNF.Clause.ofList [.pos 0, .neg 2], none⟩,
    ⟨GCNF.Clause.ofList [.neg 0, .pos 1], none⟩,
    ⟨GCNF.Clause.ofList [.neg 0, .neg 1], none⟩,
    ⟨GCNF.Clause.ofList [.pos 0, .neg 0], none⟩,
    ⟨GCNF.Clause.single (.pos 0), some ⟨.pos 2, 0, 1⟩⟩,
    ⟨GCNF.Clause.single (.neg 0), some ⟨.pos 1, 2, 3⟩⟩,
    ⟨GCNF.Clause.single (.neg 0), some ⟨.pos 0, 4, 6⟩⟩,
    ⟨GCNF.Clause.empty, some ⟨.pos 0, 5, 7⟩⟩], 8⟩

helper def deletionCounterexampleInputs : ClauseSequent :=
  ClauseSequent.ofList [
    GCNF.Clause.ofList [.pos 0, .pos 2], GCNF.Clause.ofList [.pos 0, .neg 2],
    GCNF.Clause.ofList [.neg 0, .pos 1], GCNF.Clause.ofList [.neg 0, .neg 1],
    GCNF.Clause.ofList [.pos 0, .neg 0]]

helper theorem deletionCounterexample_inputs_ordinary :
    deletionCounterexampleInputs.isOrdinary := by
  apply ClauseSequent.ordinary_ofList
  intro C hC
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl | rfl <;>
    exact GCNF.Clause.ofList_cons_ordinary _ _

helper theorem deletionCounterexample_wellFormed : deletionCounterexample.WellFormed := by
  apply AllRowsWellFormed.wellFormed
  refine ⟨by decide, ?_⟩
  intro i n hn r hr
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    simp [node, deletionCounterexample] at hn
  all_goals subst n
  all_goals simp at hr
  all_goals subst r
  all_goals simp [node, deletionCounterexample]
  all_goals simp [GCNF.Clause.ofList, GCNF.Clause.single, Literal.conjugate,
    LCS.Finset.mem_ofList, LCS.Finset.mem_singleton]
  all_goals apply LCS.Finset.ext
  all_goals intro L
  all_goals cases L with
    | pos n => simp [GCNF.Clause.ofList, GCNF.Clause.single, GCNF.Clause.empty, GCNF.Clause.union,
        GCNF.Clause.remove, Clause.remove, Clause.empty, Literal.conjugate, LCS.Finset.mem_ofList,
        LCS.Finset.mem_singleton, LCS.Finset.mem_erase, LCS.Finset.mem_empty, LCS.Finset.not_mem_empty] <;> first | exact LCS.Finset.not_mem_empty | omega
    | neg n => simp [GCNF.Clause.ofList, GCNF.Clause.single, GCNF.Clause.empty, GCNF.Clause.union,
        GCNF.Clause.remove, Clause.remove, Clause.empty, Literal.conjugate, LCS.Finset.mem_ofList,
        LCS.Finset.mem_singleton, LCS.Finset.mem_erase, LCS.Finset.mem_empty, LCS.Finset.not_mem_empty] <;> first | exact LCS.Finset.not_mem_empty | omega

helper theorem deletionCounterexample_isRefutation :
    deletionCounterexample.IsRefutationFor deletionCounterexampleInputs := by
  refine ⟨deletionCounterexample_wellFormed, ?_, rfl⟩
  intro i hi
  have hIds : deletionCounterexample.leafIds = [0, 1, 4, 2, 3] := by decide
  rw [hIds] at hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨_, rfl, ?_⟩
  all_goals simp [deletionCounterexampleInputs, ClauseSequent.ofList,
    LCS.Finset.mem_ofList]

helper def deletionCounterexampleRawDeletion : FiniteGraph :=
  (deletionCounterexample.atRoot 7).erasePersistent (.neg 0)

helper theorem deletionCounterexample_persistentIds :
    (deletionCounterexample.atRoot 7).persistentIds (.neg 0) = [7, 4, 6, 2, 3] := by
  decide

helper /-- The literal source operation produces a row resolving {P} and □ at P;
its right premise no longer contains ¬P. -/
theorem deletionCounterexample_raw_pivot_lost :
    deletionCounterexampleRawDeletion.node 7 =
      some ⟨GCNF.Clause.empty, some ⟨.pos 0, 4, 6⟩⟩ ∧
    deletionCounterexampleRawDeletion.node 4 = some ⟨GCNF.Clause.single (.pos 0), none⟩ ∧
    deletionCounterexampleRawDeletion.node 6 =
      some ⟨GCNF.Clause.empty, some ⟨.pos 1, 2, 3⟩⟩ := by
  simp only [deletionCounterexampleRawDeletion, erasePersistent,
    deletionCounterexample_persistentIds]
  simp [mapLabels, node, atRoot, deletionCounterexample]
  refine ⟨?_, ?_, ?_⟩
  all_goals apply LCS.Finset.ext
  all_goals intro L
  all_goals cases L
  all_goals simp [GCNF.Clause.ofList, GCNF.Clause.single, GCNF.Clause.empty,
    GCNF.Clause.remove, LCS.Finset.mem_erase, LCS.Finset.mem_ofList,
    LCS.Finset.mem_singleton, LCS.Finset.not_mem_empty] <;>
      first | exact LCS.Finset.not_mem_empty | omega

helper theorem deletionCounterexample_raw_not_wellFormed :
    ¬ deletionCounterexampleRawDeletion.WellFormed := by
  intro h
  have hn := deletionCounterexample_raw_pivot_lost
  have hr : 7 ∈ deletionCounterexampleRawDeletion.vertexIds := by decide
  obtain ⟨a, b, ha, hb, _, hp, _⟩ := h.2.2 7 hr _ hn.1 _ rfl
  have hbEq : b = ⟨GCNF.Clause.empty, some ⟨.pos 1, 2, 3⟩⟩ := by
    rw [hn.2.2] at hb
    exact Option.some.inj hb.symm
  subst b
  exact LCS.Finset.not_mem_empty hp

helper /-- Both branches of this refutation use the same derived unit at vertex 4.
It witnesses the source's warning that the two recursive subproblems need not
partition the original resolution steps. -/
def sharedStepExample : FiniteGraph :=
  ⟨[
    ⟨GCNF.Clause.ofList [.pos 0, .pos 1], none⟩,
    ⟨GCNF.Clause.ofList [.neg 0, .pos 1], none⟩,
    ⟨GCNF.Clause.ofList [.neg 1, .pos 2], none⟩,
    ⟨GCNF.Clause.ofList [.neg 1, .neg 2], none⟩,
    ⟨GCNF.Clause.single (.pos 1), some ⟨.pos 0, 0, 1⟩⟩,
    ⟨GCNF.Clause.single (.pos 2), some ⟨.pos 1, 4, 2⟩⟩,
    ⟨GCNF.Clause.single (.neg 2), some ⟨.pos 1, 4, 3⟩⟩,
    ⟨GCNF.Clause.empty, some ⟨.pos 2, 5, 6⟩⟩], 7⟩

helper def sharedStepInputs : ClauseSequent :=
  ClauseSequent.ofList [
    GCNF.Clause.ofList [.pos 0, .pos 1], GCNF.Clause.ofList [.neg 0, .pos 1],
    GCNF.Clause.ofList [.neg 1, .pos 2], GCNF.Clause.ofList [.neg 1, .neg 2]]

helper def sharedStepFirst : FiniteGraph :=
  (sharedStepExample.atRoot 5).mapLabels fun i C =>
    if i = 2 ∨ i = 5 then GCNF.Clause.remove C (.pos 2) else C

helper def sharedStepSecond : FiniteGraph := sharedStepExample.prune 5

helper theorem sharedStepExample_wellFormed : sharedStepExample.WellFormed := by
  apply AllRowsWellFormed.wellFormed
  refine ⟨by decide, ?_⟩
  intro i n hn r hr
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    simp [node, sharedStepExample] at hn
  all_goals subst n
  all_goals simp at hr
  all_goals subst r
  all_goals simp [node, sharedStepExample]
  all_goals simp [GCNF.Clause.ofList, GCNF.Clause.single, Literal.conjugate,
    LCS.Finset.mem_ofList, LCS.Finset.mem_singleton]
  all_goals apply LCS.Finset.ext
  all_goals intro L
  all_goals cases L with
    | pos n => simp [GCNF.Clause.ofList, GCNF.Clause.single, GCNF.Clause.empty, GCNF.Clause.union,
        GCNF.Clause.remove, Clause.remove, Clause.empty, Literal.conjugate, LCS.Finset.mem_ofList,
        LCS.Finset.mem_singleton, LCS.Finset.mem_erase, LCS.Finset.mem_empty, LCS.Finset.not_mem_empty] <;> first | exact LCS.Finset.not_mem_empty | omega
    | neg n => simp [GCNF.Clause.ofList, GCNF.Clause.single, GCNF.Clause.empty, GCNF.Clause.union,
        GCNF.Clause.remove, Clause.remove, Clause.empty, Literal.conjugate, LCS.Finset.mem_ofList,
        LCS.Finset.mem_singleton, LCS.Finset.mem_erase, LCS.Finset.mem_empty, LCS.Finset.not_mem_empty] <;> first | exact LCS.Finset.not_mem_empty | omega

helper theorem sharedStepExample_refutes : sharedStepExample.IsRefutationFor sharedStepInputs := by
  refine ⟨sharedStepExample_wellFormed, ?_, rfl⟩
  intro i hi
  have hIds : sharedStepExample.leafIds = [0, 1, 2, 3] := by decide
  rw [hIds] at hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  all_goals refine ⟨_, rfl, ?_⟩
  all_goals simp [sharedStepInputs, ClauseSequent.ofList, LCS.Finset.mem_ofList]

helper /-- The common inference survives in both subproblems, so 2 + 3 > 4. -/
theorem shared_steps_not_additive :
    sharedStepExample.follow [0, 0] = some 4 ∧
    sharedStepExample.follow [1, 0] = some 4 ∧
    sharedStepFirst.stepCount = 2 ∧ sharedStepSecond.stepCount = 3 ∧
    sharedStepExample.stepCount = 4 ∧
    sharedStepExample.stepCount < sharedStepFirst.stepCount + sharedStepSecond.stepCount := by
  decide

helper /-- The broad resolution vocabulary admits its zero-step empty-clause input. -/
theorem singleton_empty_refutation :
    (LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph.singleton GCNF.Clause.empty).IsRefutationFor (ClauseSequent.single GCNF.Clause.empty) := by
  refine ⟨LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph.singleton_wellFormed _, ?_, rfl⟩
  intro i hi
  have hi0 : i = 0 := by
    have hv := (List.mem_filter.mp hi).1
    simpa [vertexIds, reachableFrom, LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph.singleton, next, node] using hv
  subst i
  exact ⟨GCNF.Clause.empty, rfl, (LCS.Finset.mem_singleton _ _).mpr rfl⟩

helper /-- The literal unrestricted reading of Theorem 4.3.3 cannot output a §4.2
proof tree for the input consisting solely of the empty clause. -/
theorem singleton_empty_has_no_gcnf_proof :
    ¬ Nonempty (GCNFProofTree (ClauseSequent.single GCNF.Clause.empty)) := by
  rintro ⟨t⟩
  exact t.ordinary GCNF.Clause.empty ((LCS.Finset.mem_singleton _ _).mpr rfl) rfl

helper /-- Ordinary arithmetic exposes the same boundary in the source size claim:
even the smallest proof tree cannot have n + 3 ≤ 2m when m = 1. -/
theorem singleton_empty_size_obstruction (n : Nat) :
    ¬ n + 3 ≤ 2 * (LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph.singleton GCNF.Clause.empty).nodeCount := by
  simp only [LCS.Resolution.Method.FiniteGraph.Proofs.FiniteGraph.singleton_nodeCount]
  omega

end FiniteGraph

end LCS.Resolution.Method
