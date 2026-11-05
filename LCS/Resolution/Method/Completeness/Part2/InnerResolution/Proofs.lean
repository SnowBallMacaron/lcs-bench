import LCS.Resolution.Method.Completeness.Part2.InnerResolution

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

helper theorem Completeness.gcnfProofToResolution_cast {S T : ClauseSequent} (h : S = T)
    (t : GCNFProofTree S) (pick : AxiomPolicy) :
    gcnfProofToResolution (h ▸ t) pick = gcnfProofToResolution t pick := by
  cases h
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

helper @[simp] theorem Completeness.gcnfProofToResolution_transport {S T : ClauseSequent} (h : S = T)
    (t : GCNFProofTree S) (pick : AxiomPolicy) :
    gcnfProofToResolution (h ▸ t : GCNFProofTree T) pick = gcnfProofToResolution t pick := by
  cases h
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

helper @[simp] theorem Completeness.gcnfProofToResolution_axiom (Γ : ClauseSequent)
    (hOrd : Γ.isOrdinary) (hTriv) (pick : AxiomPolicy) :
    gcnfProofToResolution (.axiom_ Γ hOrd hTriv) pick =
      complementaryGraph (pick Γ hTriv).val := rfl

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

helper theorem Completeness.gcnfProofToResolution_rule (Γ As : ClauseSequent) (B : Literal)
    (Cs Γ1 Γ2 : ClauseSequent) (hΓ : Γ.isOrdinary) (hAs : As.isOrdinary)
    (left : GCNFProofTree (LCS.Finset.union Γ1 Cs))
    (right : GCNFProofTree (LCS.Finset.union Γ2 (ClauseSequent.single (Clause.single B))))
    (hNe) (hCs) (h1) (h2) (pick : AxiomPolicy) :
    gcnfProofToResolution (.rule Γ As B Cs Γ1 Γ2 hΓ hAs left right hNe hCs h1 h2) pick =
      let S := LCS.Finset.union Γ (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B))
      let d1 := gcnfProofToResolution left pick
      let d2 := gcnfProofToResolution right pick
      if leavesIn d1 S then d1 else if leavesIn d2 S then d2 else
        let lifted := replay d1
          (missingLift S B)
        if lifted.rootLabel = some GCNF.Clause.empty then lifted
        else (FiniteGraph.graft lifted d2 (unitInputs d2 B)).coalesceInputLeaves := by
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

helper @[simp] theorem Completeness.leavesIn_complementaryGraph (L : Literal) (Γ : ClauseSequent) :
    leavesIn (complementaryGraph L) Γ =
      (decide (Clause.single L ∈ Γ) && decide (Clause.single L.conjugate ∈ Γ)) := by
  change (decide (Clause.single L ∈ Γ) && (decide (Clause.single L.conjugate ∈ Γ) && true)) = _
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

helper theorem Completeness.coalesceInputLeaves_compute (g : FiniteGraph) :
    g.coalesceInputLeaves =
      ⟨g.table.map (fun n => { n with inference := n.inference.map fun r =>
        { r with left := g.canonicalInput r.left, right := g.canonicalInput r.right } }),
        g.canonicalInput g.root⟩ := rfl

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

helper theorem Completeness.empty_clauseList : GCNF.Clause.empty = Clause.ofList [] := rfl

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

helper theorem Completeness.methodEmpty_clauseList : Clause.empty = Clause.ofList [] := rfl

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

helper theorem Completeness.clauseList_eq_iff (xs ys : List Literal) :
    Clause.ofList xs = Clause.ofList ys ↔
      (∀ x ∈ xs, x ∈ ys) ∧ (∀ y ∈ ys, y ∈ xs) := by
  constructor
  · intro h
    constructor
    · intro x hx
      apply LCS.Finset.mem_ofList.mp
      change x ∈ Clause.ofList ys
      rw [← h]
      exact LCS.Finset.mem_ofList.mpr hx
    · intro y hy
      apply LCS.Finset.mem_ofList.mp
      change y ∈ Clause.ofList xs
      rw [h]
      exact LCS.Finset.mem_ofList.mpr hy
  · intro h
    apply LCS.Finset.ext
    intro L
    exact ⟨fun hm => LCS.Finset.mem_ofList.mpr (h.1 L (LCS.Finset.mem_ofList.mp hm)),
      fun hm => LCS.Finset.mem_ofList.mpr (h.2 L (LCS.Finset.mem_ofList.mp hm))⟩

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

helper theorem Completeness.clauseWithLiteral_list (xs : List Literal) (L : Literal) :
    clauseWithLiteral (Clause.ofList xs) L = Clause.ofList (L :: xs) := by
  apply LCS.Finset.ext
  intro M
  simp [clauseWithLiteral, Clause.ofList]

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

helper theorem Completeness.remove_clauseList (xs : List Literal) (L : Literal) :
    GCNF.Clause.remove (Clause.ofList xs) L =
      Clause.ofList (xs.filter fun M => decide (M ≠ L)) := by
  apply LCS.Finset.ext
  intro M
  simp [GCNF.Clause.remove, Clause.ofList]

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

helper theorem Completeness.union_clauseList (xs ys : List Literal) :
    GCNF.Clause.union (Clause.ofList xs) (Clause.ofList ys) = Clause.ofList (xs ++ ys) := by
  apply LCS.Finset.ext
  intro M
  simp [GCNF.Clause.union, Clause.ofList]

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

helper theorem Completeness.replay_complementaryGraph (L : Literal) (f : Clause → Clause) :
    replay (complementaryGraph L) f =
      ⟨[⟨f (Clause.single L), none⟩, ⟨f (Clause.single L.conjugate), none⟩,
        ⟨GCNF.Clause.union (GCNF.Clause.remove (f (Clause.single L)) L)
          (GCNF.Clause.remove (f (Clause.single L.conjugate)) L.conjugate),
          some ⟨L, 0, 1⟩⟩], 2⟩ := by
  have h0 : replayLabel (complementaryGraph L) f ⟨0, by change 0 < 3; decide⟩ = f (Clause.single L) := by
    rw [replayLabel]
    rfl
  have h1 : replayLabel (complementaryGraph L) f ⟨1, by change 1 < 3; decide⟩ = f (Clause.single L.conjugate) := by
    rw [replayLabel]
    rfl
  have h2 : replayLabel (complementaryGraph L) f ⟨2, by change 2 < 3; decide⟩ =
      GCNF.Clause.union (GCNF.Clause.remove (f (Clause.single L)) L)
        (GCNF.Clause.remove (f (Clause.single L.conjugate)) L.conjugate) := by
    rw [replayLabel]
    change GCNF.Clause.union
      (GCNF.Clause.remove (replayLabel (complementaryGraph L) f ⟨0, _⟩) L)
      (GCNF.Clause.remove (replayLabel (complementaryGraph L) f ⟨1, _⟩) L.conjugate) = _
    rw [h0, h1]
  simp only [replay, complementaryGraph, List.ofFn_succ, List.ofFn_zero]
  change (⟨[⟨replayLabel (complementaryGraph L) f ⟨0, _⟩, none⟩,
    ⟨replayLabel (complementaryGraph L) f ⟨1, _⟩, none⟩,
    ⟨replayLabel (complementaryGraph L) f ⟨2, _⟩, some ⟨L, 0, 1⟩⟩], 2⟩ : FiniteGraph) = _
  rw [h0, h1, h2]

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

helper theorem Completeness.leastAtomPolicy_displayed (P : Nat) (h) :
    (leastAtomPolicy (LCS.Finset.union
      (ClauseSequent.single (Clause.single (.pos P)))
      (ClauseSequent.single (Clause.single (.neg P)))) h).val = .pos P := by
  unfold leastAtomPolicy
  dsimp only
  let w := leastWitness (fun X => Clause.single (.pos X) ∈
    LCS.Finset.union (ClauseSequent.single (Clause.single (.pos P)))
      (ClauseSequent.single (Clause.single (.neg P))) ∧
    Clause.single (.neg X) ∈ LCS.Finset.union
      (ClauseSequent.single (Clause.single (.pos P)))
      (ClauseSequent.single (Clause.single (.neg P)))) h
  have hm := w.property.1
  have he : w.val = P := by
    simpa [ClauseSequent.single, Clause.single_eq_ofList_singleton,
      clauseList_eq_iff, eq_comm] using hm
  exact congrArg Literal.pos he

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

helper @[simp] theorem Completeness.convertDisplayedAxiom (P : Nat) :
    gcnfProofToResolution (displayedAxiom P) leastAtomPolicy =
      complementaryGraph (.pos P) := by
  simp only [displayedAxiom, gcnfProofToResolution_axiom,
    leastAtomPolicy_displayed]

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

proof_of ex435Computed_matches_D7 := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    have hcomp : (ex435Computed P Q S).vertexIds = [8, 6, 5, 3, 2, 0, 1] := rfl
    have hsource : (ex435D7 P Q S).vertexIds = [6, 5, 4, 0, 1, 2, 3] := rfl
    refine ⟨?_, ?_, rfl, ?_⟩
    · intro i hi
      rw [hcomp] at hi
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [hsource, ex435VertexMap, ex435VertexMapInv]
      all_goals simp [ex435Computed, ex435D7, FiniteGraph.label, FiniteGraph.node,
        empty_clauseList]
    · intro j hj
      rw [hsource] at hj
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [hcomp, ex435VertexMap, ex435VertexMapInv]
      all_goals simp
    · intro i hi j hj
      rw [hcomp] at hi hj
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi hj
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [FiniteGraph.hasEdge, ex435VertexMap, ex435Computed, ex435D7,
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

proof_of ex435D1_axiom := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    simp [convertDisplayedAxiom, complementaryGraph, ex435D1,
      Clause.single_eq_ofList_singleton, methodEmpty_clauseList, Literal.conjugate]

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

proof_of ex435D2_axiom := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    simp [convertDisplayedAxiom, complementaryGraph, ex435D2,
      Clause.single_eq_ofList_singleton, methodEmpty_clauseList, Literal.conjugate]

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

proof_of ex435D5_axiom := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    simp [convertDisplayedAxiom, complementaryGraph, ex435D5,
      Clause.single_eq_ofList_singleton, methodEmpty_clauseList, Literal.conjugate]

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

proof_of ex435D1_lift_to_D3 := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    rw [replay_complementaryGraph]
    simp [missingLift, ex435InnerSequent, ClauseSequent.ofList,
      Clause.single_eq_ofList_singleton, clauseList_eq_iff, Literal.conjugate,
      clauseWithLiteral_list, remove_clauseList, union_clauseList, ex435D3,
      hPS, Ne.symm hPS]

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

proof_of ex435InnerProof_execution := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    set_option backward.isDefEq.respectTransparency false in
      have hseq : LCS.Finset.union
          (ClauseSequent.ofList [Clause.single (.pos P), Clause.single (.pos S)])
          (ClauseSequent.mapSet (ClauseSequent.single (Clause.single (.neg P)))
            (fun A => clauseWithLiteral A (.neg S))) = ex435InnerSequent P S := by
        apply LCS.Finset.ext
        intro C
        simp [ex435InnerSequent, ClauseSequent.ofList, ClauseSequent.single,
          ClauseSequent.mapSet, clauseWithLiteral_single, or_left_comm, or_comm, eq_comm]
      have hPLeaves : leavesIn (complementaryGraph (.pos P)) (ex435InnerSequent P S) = false := by
        simp [leavesIn_complementaryGraph, ex435InnerSequent, ClauseSequent.ofList,
          Clause.single_eq_ofList_singleton, clauseList_eq_iff, Literal.conjugate,
          hPS, Ne.symm hPS]
      have hSLeaves : leavesIn (complementaryGraph (.pos S)) (ex435InnerSequent P S) = false := by
        simp [leavesIn_complementaryGraph, ex435InnerSequent, ClauseSequent.ofList,
          Clause.single_eq_ofList_singleton, clauseList_eq_iff, Literal.conjugate,
          hPS, Ne.symm hPS]
      unfold ex435InnerProof
      refine (gcnfProofToResolution_transport hseq _ _).trans ?_
      refine (gcnfProofToResolution_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans ?_
      simp only [ex435InnerProof, gcnfProofToResolution_transport,
        gcnfProofToResolution_rule, convertDisplayedAxiom, hseq, hPLeaves, hSLeaves,
        Bool.false_eq_true, ↓reduceIte]
      rw [ex435D1_lift_to_D3 P S hPS]
      simp [ex435D3, ex435ComputedInner, FiniteGraph.rootLabel, FiniteGraph.label,
        FiniteGraph.node, FiniteGraph.graft, coalesceInputLeaves_compute,
        FiniteGraph.canonicalInput, unitInputs, complementaryGraph,
        Clause.single_eq_ofList_singleton, empty_clauseList, methodEmpty_clauseList,
        List.findIdx_cons, List.findIdx_nil, clauseList_eq_iff, Literal.conjugate, hPS, Ne.symm hPS]

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

proof_of ex435ComputedInner_lift := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    have h0 : replayLabel (ex435ComputedInner P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨0, by change 0 < 6; decide⟩ = Clause.ofList [.pos P, .neg Q] := by
      rw [replayLabel]
      change missingLift (ex435Sequent P Q S) (.neg Q) (Clause.ofList [.pos P]) = _
      simp [missingLift, ex435Sequent, ClauseSequent.ofList,
        Clause.single_eq_ofList_singleton, clauseList_eq_iff, clauseWithLiteral_list,
        hPQ, Ne.symm hPQ, hPS, Ne.symm hPS]
    have h1 : replayLabel (ex435ComputedInner P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨1, by change 1 < 6; decide⟩ = Clause.ofList [.neg P, .neg S] := by
      rw [replayLabel]
      change missingLift (ex435Sequent P Q S) (.neg Q) (Clause.ofList [.neg P, .neg S]) = _
      simp [missingLift, ex435Sequent, ClauseSequent.ofList,
        Clause.single_eq_ofList_singleton, clauseList_eq_iff,
        hPQ, Ne.symm hPQ, hQS, Ne.symm hQS]
    have h2 : replayLabel (ex435ComputedInner P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨2, by change 2 < 6; decide⟩ = Clause.ofList [.neg Q, .neg S] := by
      rw [replayLabel]
      change GCNF.Clause.union (GCNF.Clause.remove (replayLabel (ex435ComputedInner P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨0, by change 0 < 6; decide⟩) (.pos P))
        (GCNF.Clause.remove (replayLabel (ex435ComputedInner P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨1, by change 1 < 6; decide⟩) (Literal.pos P).conjugate) = _
      rw [h0, h1]
      simp [remove_clauseList, union_clauseList, Literal.conjugate,
        Ne.symm hPS]
    have h3 : replayLabel (ex435ComputedInner P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨3, by change 3 < 6; decide⟩ = Clause.ofList [.pos S, .neg Q] := by
      rw [replayLabel]
      change missingLift (ex435Sequent P Q S) (.neg Q) (Clause.ofList [.pos S]) = _
      simp [missingLift, ex435Sequent, ClauseSequent.ofList,
        Clause.single_eq_ofList_singleton, clauseList_eq_iff, clauseWithLiteral_list,
        hPS, Ne.symm hPS, hQS, Ne.symm hQS]
    have h4 : replayLabel (ex435ComputedInner P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨4, by change 4 < 6; decide⟩ = Clause.ofList [.neg S, .neg Q] := by
      rw [replayLabel]
      change missingLift (ex435Sequent P Q S) (.neg Q) (Clause.ofList [.neg S]) = _
      simp [missingLift, ex435Sequent, ClauseSequent.ofList,
        Clause.single_eq_ofList_singleton, clauseList_eq_iff, clauseWithLiteral_list,
        hPS, Ne.symm hPS, hQS, Ne.symm hQS]
    have h5 : replayLabel (ex435ComputedInner P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨5, by change 5 < 6; decide⟩ = Clause.ofList [.neg Q] := by
      rw [replayLabel]
      change GCNF.Clause.union (GCNF.Clause.remove (replayLabel (ex435ComputedInner P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨3, by change 3 < 6; decide⟩) (.pos S))
        (GCNF.Clause.remove (replayLabel (ex435ComputedInner P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨2, by change 2 < 6; decide⟩) (Literal.pos S).conjugate) = _
      rw [h3, h2]
      simp [remove_clauseList, union_clauseList, clauseList_eq_iff, Literal.conjugate,
        hQS]
    simp only [replay, ex435ComputedInner, List.ofFn_succ, List.ofFn_zero]
    change (⟨[⟨replayLabel (ex435ComputedInner P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨0, by change 0 < 6; decide⟩, none⟩,
      ⟨replayLabel (ex435ComputedInner P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨1, by change 1 < 6; decide⟩, none⟩,
      ⟨replayLabel (ex435ComputedInner P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨2, by change 2 < 6; decide⟩, some ⟨.pos P, 0, 1⟩⟩,
      ⟨replayLabel (ex435ComputedInner P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨3, by change 3 < 6; decide⟩, none⟩,
      ⟨replayLabel (ex435ComputedInner P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨4, by change 4 < 6; decide⟩, none⟩,
      ⟨replayLabel (ex435ComputedInner P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨5, by change 5 < 6; decide⟩, some ⟨.pos S, 3, 2⟩⟩], 5⟩ : FiniteGraph) = _
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

proof_of ex435D4_lift_to_D6 := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    have h0 : replayLabel (ex435D4 P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨0, by change 0 < 5; decide⟩ = Clause.ofList [.pos P, .neg Q] := by
      rw [replayLabel]
      change missingLift (ex435Sequent P Q S) (.neg Q) (Clause.ofList [.pos P]) = _
      simp [missingLift, ex435Sequent, ClauseSequent.ofList,
        Clause.single_eq_ofList_singleton, clauseList_eq_iff, clauseWithLiteral_list,
        hPQ, Ne.symm hPQ, hPS, Ne.symm hPS]
    have h1 : replayLabel (ex435D4 P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨1, by change 1 < 5; decide⟩ = Clause.ofList [.neg P, .neg S] := by
      rw [replayLabel]
      change missingLift (ex435Sequent P Q S) (.neg Q) (Clause.ofList [.neg P, .neg S]) = _
      simp [missingLift, ex435Sequent, ClauseSequent.ofList,
        Clause.single_eq_ofList_singleton, clauseList_eq_iff,
        hPQ, Ne.symm hPQ, hQS, Ne.symm hQS]
    have h2 : replayLabel (ex435D4 P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨2, by change 2 < 5; decide⟩ = Clause.ofList [.pos S, .neg Q] := by
      rw [replayLabel]
      change missingLift (ex435Sequent P Q S) (.neg Q) (Clause.ofList [.pos S]) = _
      simp [missingLift, ex435Sequent, ClauseSequent.ofList,
        Clause.single_eq_ofList_singleton, clauseList_eq_iff, clauseWithLiteral_list,
        hPS, Ne.symm hPS, hQS, Ne.symm hQS]
    have h3 : replayLabel (ex435D4 P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨3, by change 3 < 5; decide⟩ = Clause.ofList [.neg Q, .neg S] := by
      rw [replayLabel]
      change GCNF.Clause.union (GCNF.Clause.remove (replayLabel (ex435D4 P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨0, by change 0 < 5; decide⟩) (.pos P))
        (GCNF.Clause.remove (replayLabel (ex435D4 P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨1, by change 1 < 5; decide⟩) (Literal.pos P).conjugate) = _
      rw [h0, h1]
      simp [remove_clauseList, union_clauseList, Literal.conjugate,
        Ne.symm hPS]
    have h4 : replayLabel (ex435D4 P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨4, by change 4 < 5; decide⟩ = Clause.ofList [.neg Q] := by
      rw [replayLabel]
      change GCNF.Clause.union (GCNF.Clause.remove (replayLabel (ex435D4 P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨3, by change 3 < 5; decide⟩) (.neg S))
        (GCNF.Clause.remove (replayLabel (ex435D4 P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨2, by change 2 < 5; decide⟩) (Literal.neg S).conjugate) = _
      rw [h3, h2]
      simp [remove_clauseList, union_clauseList, clauseList_eq_iff, Literal.conjugate,
        hQS]
    simp only [replay, ex435D4, List.ofFn_succ, List.ofFn_zero]
    change (⟨[⟨replayLabel (ex435D4 P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨0, by change 0 < 5; decide⟩, none⟩,
      ⟨replayLabel (ex435D4 P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨1, by change 1 < 5; decide⟩, none⟩,
      ⟨replayLabel (ex435D4 P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨2, by change 2 < 5; decide⟩, none⟩,
      ⟨replayLabel (ex435D4 P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨3, by change 3 < 5; decide⟩, some ⟨.pos P, 0, 1⟩⟩,
      ⟨replayLabel (ex435D4 P S) (missingLift (ex435Sequent P Q S) (.neg Q)) ⟨4, by change 4 < 5; decide⟩, some ⟨.neg S, 3, 2⟩⟩], 4⟩ : FiniteGraph) = _
    rw [h0, h1, h2, h3, h4]
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

proof_of ex435Proof_execution := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    have hseq : LCS.Finset.union
        (ClauseSequent.ofList [Clause.single (.pos Q), Clause.ofList [.neg P, .neg S]])
        (ClauseSequent.mapSet
          (ClauseSequent.ofList [Clause.single (.pos P), Clause.single (.pos S)])
          (fun A => clauseWithLiteral A (.neg Q))) = ex435Sequent P Q S := by
      apply LCS.Finset.ext
      intro C
      simp [ex435Sequent, ClauseSequent.ofList, ClauseSequent.mapSet,
        clauseWithLiteral_single, or_assoc, or_left_comm, or_comm, eq_comm]
    have hLeftLeaves : leavesIn (ex435ComputedInner P S) (ex435Sequent P Q S) = false := by
      have hids : (ex435ComputedInner P S).leafIds = [3, 0, 1] := rfl
      simp only [leavesIn, hids]
      simp [ex435ComputedInner, FiniteGraph.label, FiniteGraph.node,
        ex435Sequent, ClauseSequent.ofList, Clause.single_eq_ofList_singleton,
        clauseList_eq_iff, hPQ, Ne.symm hPQ, hPS, Ne.symm hPS, hQS, Ne.symm hQS]
    have hRightLeaves : leavesIn (complementaryGraph (.pos Q)) (ex435Sequent P Q S) = false := by
      simp [leavesIn_complementaryGraph, ex435Sequent, ClauseSequent.ofList,
        Clause.single_eq_ofList_singleton, clauseList_eq_iff, Literal.conjugate,
        hPQ, Ne.symm hPQ, hQS, Ne.symm hQS]
    refine (gcnfProofToResolution_transport _ _ _).trans ?_
    refine (gcnfProofToResolution_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans ?_
    simp only [ex435Proof, gcnfProofToResolution_transport, gcnfProofToResolution_rule,
      ex435InnerProof_execution P S hPS, convertDisplayedAxiom, hseq,
      hLeftLeaves, hRightLeaves, Bool.false_eq_true, ↓reduceIte]
    rw [ex435ComputedInner_lift P Q S hPQ hPS hQS]
    simp [ex435LiftedInner, ex435Computed, FiniteGraph.rootLabel, FiniteGraph.label,
      FiniteGraph.node, FiniteGraph.graft, coalesceInputLeaves_compute,
      FiniteGraph.canonicalInput, unitInputs, complementaryGraph,
      Clause.single_eq_ofList_singleton, empty_clauseList, methodEmpty_clauseList,
      List.findIdx_cons, List.findIdx_nil, clauseList_eq_iff, Literal.conjugate,
      hPQ, Ne.symm hPQ, hPS, Ne.symm hPS, hQS, Ne.symm hQS]

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

proof_of ex435ComputedInner_matches_D4 := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    have hcomp : (ex435ComputedInner P S).vertexIds = [5, 3, 2, 0, 1] := rfl
    have hsource : (ex435D4 P S).vertexIds = [4, 3, 0, 1, 2] := rfl
    refine ⟨?_, ?_, rfl, ?_⟩
    · intro i hi
      rw [hcomp] at hi
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl
      all_goals simp only [hsource, ex435InnerVertexMap, ex435InnerVertexMapInv]
      all_goals simp [ex435ComputedInner, ex435D4, FiniteGraph.label, FiniteGraph.node,
        empty_clauseList]
    · intro j hj
      rw [hsource] at hj
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl
      all_goals simp only [hcomp, ex435InnerVertexMap, ex435InnerVertexMapInv]
      all_goals simp
    · intro i hi j hj
      rw [hcomp] at hi hj
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi hj
      rcases hi with rfl | rfl | rfl | rfl | rfl
      all_goals rcases hj with rfl | rfl | rfl | rfl | rfl
      all_goals simp [FiniteGraph.hasEdge, ex435InnerVertexMap, ex435ComputedInner, ex435D4,
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

proof_of ex435LiftedInner_matches_D6 := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    have hcomp : (ex435LiftedInner P Q S).vertexIds = [5, 3, 2, 0, 1] := rfl
    have hsource : (ex435D6 P Q S).vertexIds = [4, 3, 0, 1, 2] := rfl
    refine ⟨?_, ?_, rfl, ?_⟩
    · intro i hi
      rw [hcomp] at hi
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl
      all_goals simp only [hsource, ex435InnerVertexMap, ex435InnerVertexMapInv]
      all_goals simp [ex435LiftedInner, ex435D6, FiniteGraph.label, FiniteGraph.node,
        ]
    · intro j hj
      rw [hsource] at hj
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl
      all_goals simp only [hcomp, ex435InnerVertexMap, ex435InnerVertexMapInv]
      all_goals simp
    · intro i hi j hj
      rw [hcomp] at hi hj
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi hj
      rcases hi with rfl | rfl | rfl | rfl | rfl
      all_goals rcases hj with rfl | rfl | rfl | rfl | rfl
      all_goals simp [FiniteGraph.hasEdge, ex435InnerVertexMap, ex435LiftedInner, ex435D6,
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

proof_of ex435Proof_matches_D7 := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    simp only [ex435Proof_execution P Q S hPQ hPS hQS]
    exact ex435Computed_matches_D7 P Q S

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

helper theorem Completeness.replay_graph_congr {g h : FiniteGraph} (e : g = h)
    (hg : g.AllRowsWellFormed) (hh : h.AllRowsWellFormed) (f : Clause → Clause) :
    replay g f = replay h f := by
  cases e
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

proof_of ex435D1_replay := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    have he : ex435D1 P = complementaryGraph (.pos P) := by
      simpa only [convertDisplayedAxiom] using (ex435D1_axiom P).symm
    rw [he]
    exact ex435D1_lift_to_D3 P S hPS

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

proof_of ex435D3_graft_D2 := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    simp [ex435D3, ex435D2, ex435ComputedInner, FiniteGraph.graft,
      coalesceInputLeaves_compute, FiniteGraph.canonicalInput, FiniteGraph.node, unitInputs,
      Clause.single_eq_ofList_singleton, empty_clauseList,
      List.findIdx_cons, List.findIdx_nil, clauseList_eq_iff, hPS, Ne.symm hPS]

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

proof_of ex435LiftedInner_graft_D5 := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    simp [ex435LiftedInner, ex435D5, ex435Computed, FiniteGraph.graft,
      coalesceInputLeaves_compute, FiniteGraph.canonicalInput, FiniteGraph.node, unitInputs,
      Clause.single_eq_ofList_singleton, empty_clauseList,
      List.findIdx_cons, List.findIdx_nil, clauseList_eq_iff,
      hPQ, Ne.symm hPQ, hPS, Ne.symm hPS, hQS, Ne.symm hQS]

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

proof_of ex435Proof_counts := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    rw [ex435Proof_execution P Q S hPQ hPS hQS]
    constructor <;> rfl

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

proof_of ex435InnerProof_matches_D4 := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    simp only [ex435InnerProof_execution P S hPS]
    exact ex435ComputedInner_matches_D4 P S

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

helper theorem Completeness.negativeFirstPolicy_displayed (P : Nat) (h) :
    (negativeFirstPolicy (LCS.Finset.union
      (ClauseSequent.single (Clause.single (.neg P)))
      (ClauseSequent.single (Clause.single (.pos P)))) h).val = .neg P := by
  unfold negativeFirstPolicy
  dsimp only
  let w := leastWitness (fun X => Clause.single (.pos X) ∈
    LCS.Finset.union (ClauseSequent.single (Clause.single (.neg P)))
      (ClauseSequent.single (Clause.single (.pos P))) ∧
    Clause.single (.neg X) ∈ LCS.Finset.union
      (ClauseSequent.single (Clause.single (.neg P)))
      (ClauseSequent.single (Clause.single (.pos P)))) h
  have hm := w.property.1
  have he : w.val = P := by
    have hl : Literal.pos w.val ∈ Clause.single (.neg P) ∨
        Literal.pos w.val ∈ Clause.single (.pos P) := by
      simp only [LCS.Finset.mem_union, ClauseSequent.single,
        LCS.Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · apply Or.inl
        have hh : Literal.pos w.val ∈ Clause.single (.pos w.val) := by simp [Clause.single]
        rw [hm] at hh
        exact hh
      · apply Or.inr
        have hh : Literal.pos w.val ∈ Clause.single (.pos w.val) := by simp [Clause.single]
        rw [hm] at hh
        exact hh
    simpa [Clause.single] using hl
  exact congrArg Literal.neg he

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

helper @[simp] theorem Completeness.convertDisplayedNegativeFirstAxiom (P : Nat) :
    gcnfProofToResolution (displayedNegativeFirstAxiom P) negativeFirstPolicy =
      complementaryGraph (.neg P) := by
  simp only [displayedNegativeFirstAxiom, gcnfProofToResolution_axiom,
    negativeFirstPolicy_displayed]

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

proof_of ex436D1_isAxiomConversion := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    rw [convertDisplayedNegativeFirstAxiom]
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

proof_of ex436D2_isAxiomConversion := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    rw [convertDisplayedNegativeFirstAxiom]
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

proof_of ex436D6_isAxiomConversion := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    rw [convertDisplayedNegativeFirstAxiom]
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

proof_of ex436D3_isReplay := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    rw [replay_complementaryGraph]
    simp [missingLift, ex436InnerSequent, ClauseSequent.ofList,
      Clause.single_eq_ofList_singleton, clauseList_eq_iff, clauseWithLiteral_list,
      remove_clauseList, union_clauseList, Literal.conjugate, hPQ, Ne.symm hPQ,
      ex436D3, FiniteGraph.mk.injEq, FiniteGraph.Node.mk.injEq]

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

proof_of ex436InnerConversion_raw := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    set_option backward.isDefEq.respectTransparency false in
      have hseq : LCS.Finset.union
          (ClauseSequent.ofList [Clause.single (.neg Q), Clause.single (.neg P)])
          (ClauseSequent.mapSet (ClauseSequent.single (Clause.single (.pos P)))
            (fun A => clauseWithLiteral A (.pos Q))) = ex436InnerSequent P Q := by
        apply LCS.Finset.ext
        intro C
        simp [ex436InnerSequent, ClauseSequent.ofList, ClauseSequent.single,
          ClauseSequent.mapSet, or_assoc, or_left_comm, or_comm, eq_comm]
      have hl : leavesIn (complementaryGraph (.neg P)) (ex436InnerSequent P Q) = false := by
        simp [ex436InnerSequent, ClauseSequent.ofList, leavesIn_complementaryGraph,
          Clause.single_eq_ofList_singleton, clauseList_eq_iff, Literal.conjugate, hPQ, Ne.symm hPQ]
      have hr : leavesIn (complementaryGraph (.neg Q)) (ex436InnerSequent P Q) = false := by
        simp [ex436InnerSequent, ClauseSequent.ofList, leavesIn_complementaryGraph,
          Clause.single_eq_ofList_singleton, clauseList_eq_iff, Literal.conjugate, hPQ, Ne.symm hPQ]
      unfold ex436InnerProof
      refine (gcnfProofToResolution_transport hseq _ _).trans ?_
      refine (gcnfProofToResolution_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans ?_
      simp only [ex436InnerProof, gcnfProofToResolution_transport,
        gcnfProofToResolution_rule, convertDisplayedNegativeFirstAxiom, hseq, hl, hr,
        Bool.false_eq_true, ↓reduceIte, ex436D3_isReplay P Q hPQ]
      simp [ex436D3, FiniteGraph.rootLabel, FiniteGraph.label, FiniteGraph.node,
        clauseList_eq_iff, methodEmpty_clauseList, empty_clauseList, List.findIdx_cons, List.findIdx_nil,
        coalesceInputLeaves_compute, FiniteGraph.graft, complementaryGraph, unitInputs,
        FiniteGraph.canonicalInput, ex436ComputedInner, Literal.conjugate,
        Clause.single_eq_ofList_singleton, hPQ, Ne.symm hPQ]

end LCS.Resolution.Method.Completeness
end
end
