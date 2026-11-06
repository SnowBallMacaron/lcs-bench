import LCS.Item
import LCS.Util
import LCS.Resolution.Method.FiniteGraph
import Attach
import LCS.Resolution.Method.Completeness.Conversion
import LCS.Resolution.Method.Completeness.Example435.ProofsStamp

/-! # Example 4.3.5: converting a GCNF'-proof into a resolution refutation

The displayed proof tree, the resolution DAGs D1-D7 of the text, and the
run of the conversion that produces them.
-/
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF

@[blueprint "chap4__example_4_3_5"]
def displayedAxiom (P : Nat) :
    GCNFProofTree (LCS.Finset.union
      (ClauseSequent.single (Clause.single (.pos P)))
      (ClauseSequent.single (Clause.single (.neg P)))) :=
  .axiom_ _ (ClauseSequent.ordinary_union
    (ClauseSequent.ordinary_single (Clause.single_ordinary _))
    (ClauseSequent.ordinary_single (Clause.single_ordinary _)))
    ⟨P, by simp [ClauseSequent.single], by simp [ClauseSequent.single]⟩

@[blueprint "chap4__example_4_3_5"]
def ex435InnerSequent (P S : Nat) : ClauseSequent :=
  ClauseSequent.ofList [Clause.single (.pos P), Clause.single (.pos S),
    Clause.ofList [.neg P, .neg S]]

@[blueprint "chap4__example_4_3_5"]
def ex435Sequent (P Q S : Nat) : ClauseSequent :=
  ClauseSequent.ofList [Clause.ofList [.pos P, .neg Q],
    Clause.ofList [.pos S, .neg Q], Clause.single (.pos Q),
    Clause.ofList [.neg P, .neg S]]

@[blueprint "chap4__example_4_3_5"]
def ex435InnerProof (P S : Nat) : GCNFProofTree (ex435InnerSequent P S) :=
  ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
    apply LCS.Finset.ext
    intro C
    simp [ex435InnerSequent, ClauseSequent.ofList, ClauseSequent.single,
      ClauseSequent.mapSet, clauseWithLiteral_single, or_left_comm, or_comm, eq_comm])
    (.rule (ClauseSequent.ofList [Clause.single (.pos P), Clause.single (.pos S)])
      (ClauseSequent.single (Clause.single (.neg P))) (.neg S)
      (ClauseSequent.single (Clause.single (.neg P)))
      (ClauseSequent.single (Clause.single (.pos P)))
      (ClauseSequent.single (Clause.single (.pos S)))
      (by
        apply ClauseSequent.ordinary_ofList
        intro C hC
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
        rcases hC with rfl | rfl <;> exact Clause.single_ordinary _)
      (ClauseSequent.ordinary_single (Clause.single_ordinary _))
      (displayedAxiom P) (displayedAxiom S)
      ⟨Clause.single (.neg P), by simp [ClauseSequent.single]⟩
      (fun _ h => h)
      (by
        intro C hC
        apply LCS.Finset.mem_union.mpr
        left
        simpa [ClauseSequent.single, ClauseSequent.ofList] using Or.inl hC)
      (by
        intro C hC
        apply LCS.Finset.mem_union.mpr
        left
        simpa [ClauseSequent.single, ClauseSequent.ofList] using Or.inr hC)))

@[blueprint "chap4__example_4_3_5"]
def ex435Proof (P Q S : Nat) : GCNFProofTree (ex435Sequent P Q S) :=
  ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
    apply LCS.Finset.ext
    intro C
    simp [ex435Sequent, ClauseSequent.ofList,
      ClauseSequent.mapSet, clauseWithLiteral_single, or_assoc, or_left_comm, or_comm, eq_comm])
    (.rule
      (ClauseSequent.ofList [Clause.single (.pos Q), Clause.ofList [.neg P, .neg S]])
      (ClauseSequent.ofList [Clause.single (.pos P), Clause.single (.pos S)]) (.neg Q)
      (ClauseSequent.ofList [Clause.single (.pos P), Clause.single (.pos S)])
      (ClauseSequent.single (Clause.ofList [.neg P, .neg S]))
      (ClauseSequent.single (Clause.single (.pos Q)))
      (by
        apply ClauseSequent.ordinary_ofList
        intro C hC
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
        rcases hC with rfl | rfl
        · exact Clause.single_ordinary _
        · exact Clause.ofList_cons_ordinary _ _)
      (by
        apply ClauseSequent.ordinary_ofList
        intro C hC
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
        rcases hC with rfl | rfl <;> exact Clause.single_ordinary _)
      (((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
        apply LCS.Finset.ext
        intro C
        simp [ex435InnerSequent, ClauseSequent.ofList, ClauseSequent.single,
          or_left_comm, or_comm]) (ex435InnerProof P S)))
      (displayedAxiom Q)
      ⟨Clause.single (.pos P), by simp [ClauseSequent.ofList]⟩
      (fun _ h => h)
      (by
        intro C hC
        apply LCS.Finset.mem_union.mpr
        left
        simpa [ClauseSequent.single, ClauseSequent.ofList] using Or.inr hC)
      (by
        intro C hC
        apply LCS.Finset.mem_union.mpr
        left
        simpa [ClauseSequent.single, ClauseSequent.ofList] using Or.inl hC)))

open LCS.Resolution.GCNF
open LCS.Resolution.Method

@[blueprint "chap4__example_4_3_5"]
def ex435D1 (P : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos P], none⟩,
    ⟨Clause.ofList [.neg P], none⟩,
    ⟨Clause.ofList [], some ⟨.pos P, 0, 1⟩⟩], 2⟩

@[blueprint "chap4__example_4_3_5"]
def ex435D2 (S : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos S], none⟩,
    ⟨Clause.ofList [.neg S], none⟩,
    ⟨Clause.ofList [], some ⟨.pos S, 0, 1⟩⟩], 2⟩

@[blueprint "chap4__example_4_3_5"]
def ex435D3 (P S : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos P], none⟩,
    ⟨Clause.ofList [.neg P, .neg S], none⟩,
    ⟨Clause.ofList [.neg S], some ⟨.pos P, 0, 1⟩⟩], 2⟩

@[blueprint "chap4__example_4_3_5"]
def ex435D4 (P S : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos P], none⟩,
    ⟨Clause.ofList [.neg P, .neg S], none⟩,
    ⟨Clause.ofList [.pos S], none⟩,
    ⟨Clause.ofList [.neg S], some ⟨.pos P, 0, 1⟩⟩,
    ⟨Clause.ofList [], some ⟨.neg S, 3, 2⟩⟩], 4⟩

@[blueprint "chap4__example_4_3_5"]
def ex435D5 (Q : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos Q], none⟩,
    ⟨Clause.ofList [.neg Q], none⟩,
    ⟨Clause.ofList [], some ⟨.pos Q, 0, 1⟩⟩], 2⟩

end LCS.Resolution.Method.Completeness
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

@[blueprint "chap4__example_4_3_5"]
def ex435D6 (P Q S : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos P, .neg Q], none⟩,
    ⟨Clause.ofList [.neg P, .neg S], none⟩,
    ⟨Clause.ofList [.pos S, .neg Q], none⟩,
    ⟨Clause.ofList [.neg Q, .neg S], some ⟨.pos P, 0, 1⟩⟩,
    ⟨Clause.ofList [.neg Q], some ⟨.neg S, 3, 2⟩⟩], 4⟩

@[blueprint "chap4__example_4_3_5"]
def ex435D7 (P Q S : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos P, .neg Q], none⟩,
    ⟨Clause.ofList [.neg P, .neg S], none⟩,
    ⟨Clause.ofList [.pos S, .neg Q], none⟩,
    ⟨Clause.ofList [.pos Q], none⟩,
    ⟨Clause.ofList [.neg Q, .neg S], some ⟨.pos P, 0, 1⟩⟩,
    ⟨Clause.ofList [.neg Q], some ⟨.neg S, 4, 2⟩⟩,
    ⟨Clause.ofList [], some ⟨.neg Q, 5, 3⟩⟩], 6⟩

open LCS.Resolution.GCNF
open LCS.Resolution.Method

@[blueprint "chap4__example_4_3_5"]
def ex435ComputedInner (P S : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos P], none⟩,
    ⟨Clause.ofList [.neg P, .neg S], none⟩,
    ⟨Clause.ofList [.neg S], some ⟨.pos P, 0, 1⟩⟩,
    ⟨Clause.ofList [.pos S], none⟩,
    ⟨Clause.ofList [.neg S], none⟩,
    ⟨GCNF.Clause.empty, some ⟨.pos S, 3, 2⟩⟩], 5⟩

/-- The converter retains unused rows; seven IDs remain reachable. -/
@[blueprint "chap4__example_4_3_5"]
def ex435Computed (P Q S : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos P, .neg Q], none⟩,
    ⟨Clause.ofList [.neg P, .neg S], none⟩,
    ⟨Clause.ofList [.neg Q, .neg S], some ⟨.pos P, 0, 1⟩⟩,
    ⟨Clause.ofList [.pos S, .neg Q], none⟩,
    ⟨Clause.ofList [.neg S, .neg Q], none⟩,
    ⟨Clause.ofList [.neg Q], some ⟨.pos S, 3, 2⟩⟩,
    ⟨Clause.ofList [.pos Q], none⟩,
    ⟨Clause.ofList [.neg Q], none⟩,
    ⟨GCNF.Clause.empty, some ⟨.pos Q, 6, 5⟩⟩], 8⟩

@[blueprint "chap4__example_4_3_5"]
def ex435VertexMap : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 5 => 5 | 6 => 3 | 8 => 6 | i => i

@[blueprint "chap4__example_4_3_5"]
def ex435VertexMapInv : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 6 | 4 => 2 | 5 => 5 | 6 => 8 | i => i

/-- An explicit label-preserving bijection of the represented vertices.
The two premise positions may be exchanged by the source drawing. -/
@[blueprint "chap4__example_4_3_5"]
theorem ex435Computed_matches_D7 (P Q S : Nat) :
    (∀ i ∈ (ex435Computed P Q S).vertexIds,
      ex435VertexMap i ∈ (ex435D7 P Q S).vertexIds ∧
      ex435VertexMapInv (ex435VertexMap i) = i ∧
      (ex435Computed P Q S).label i = (ex435D7 P Q S).label (ex435VertexMap i)) ∧
    (∀ j ∈ (ex435D7 P Q S).vertexIds,
      ex435VertexMapInv j ∈ (ex435Computed P Q S).vertexIds ∧
      ex435VertexMap (ex435VertexMapInv j) = j) ∧
    ex435VertexMap (ex435Computed P Q S).root = (ex435D7 P Q S).root ∧
    (∀ i ∈ (ex435Computed P Q S).vertexIds,
      ∀ j ∈ (ex435Computed P Q S).vertexIds,
      FiniteGraph.hasEdge (ex435Computed P Q S) i j ↔
        FiniteGraph.hasEdge (ex435D7 P Q S) (ex435VertexMap i) (ex435VertexMap j)) 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D1_axiom (P : Nat) :
    gcnfProofToResolution (displayedAxiom P) leastAtomPolicy = ex435D1 P 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D2_axiom (S : Nat) :
    gcnfProofToResolution (displayedAxiom S) leastAtomPolicy = ex435D2 S 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D5_axiom (Q : Nat) :
    gcnfProofToResolution (displayedAxiom Q) leastAtomPolicy = ex435D5 Q 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D1_lift_to_D3 (P S : Nat) (hPS : P ≠ S) :
    replay (complementaryGraph (.pos P))
      (missingLift (ex435InnerSequent P S) (.neg S)) = ex435D3 P S 

@[blueprint "chap4__example_4_3_5"]
theorem ex435InnerProof_execution (P S : Nat) (hPS : P ≠ S) :
    gcnfProofToResolution (ex435InnerProof P S) leastAtomPolicy =
      ex435ComputedInner P S 

@[blueprint "chap4__example_4_3_5"]
def ex435LiftedInner (P Q S : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos P, .neg Q], none⟩,
    ⟨Clause.ofList [.neg P, .neg S], none⟩,
    ⟨Clause.ofList [.neg Q, .neg S], some ⟨.pos P, 0, 1⟩⟩,
    ⟨Clause.ofList [.pos S, .neg Q], none⟩,
    ⟨Clause.ofList [.neg S, .neg Q], none⟩,
    ⟨Clause.ofList [.neg Q], some ⟨.pos S, 3, 2⟩⟩], 5⟩

@[blueprint "chap4__example_4_3_5"]
theorem ex435ComputedInner_lift (P Q S : Nat) (hPQ : P ≠ Q) (hPS : P ≠ S) (hQS : Q ≠ S) :
    replay (ex435ComputedInner P S) (missingLift (ex435Sequent P Q S) (.neg Q)) = ex435LiftedInner P Q S 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D4_lift_to_D6 (P Q S : Nat) (hPQ : P ≠ Q) (hPS : P ≠ S) (hQS : Q ≠ S) :
    replay (ex435D4 P S) (missingLift (ex435Sequent P Q S) (.neg Q)) = ex435D6 P Q S 

@[blueprint "chap4__example_4_3_5"]
theorem ex435Proof_execution (P Q S : Nat) (hPQ : P ≠ Q) (hPS : P ≠ S) (hQS : Q ≠ S) :
    gcnfProofToResolution (ex435Proof P Q S) leastAtomPolicy = ex435Computed P Q S 

@[blueprint "chap4__example_4_3_5"]
def ex435InnerVertexMap : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 5 => 4 | i => i

@[blueprint "chap4__example_4_3_5"]
def ex435InnerVertexMapInv : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | i => i

@[blueprint "chap4__example_4_3_5"]
theorem ex435ComputedInner_matches_D4 (P S : Nat) :
    (∀ i ∈ (ex435ComputedInner P S).vertexIds,
      ex435InnerVertexMap i ∈ (ex435D4 P S).vertexIds ∧
      ex435InnerVertexMapInv (ex435InnerVertexMap i) = i ∧
      (ex435ComputedInner P S).label i = (ex435D4 P S).label (ex435InnerVertexMap i)) ∧
    (∀ j ∈ (ex435D4 P S).vertexIds,
      ex435InnerVertexMapInv j ∈ (ex435ComputedInner P S).vertexIds ∧
      ex435InnerVertexMap (ex435InnerVertexMapInv j) = j) ∧
    ex435InnerVertexMap (ex435ComputedInner P S).root = (ex435D4 P S).root ∧
    (∀ i ∈ (ex435ComputedInner P S).vertexIds,
      ∀ j ∈ (ex435ComputedInner P S).vertexIds,
      FiniteGraph.hasEdge (ex435ComputedInner P S) i j ↔
        FiniteGraph.hasEdge (ex435D4 P S) (ex435InnerVertexMap i) (ex435InnerVertexMap j)) 

@[blueprint "chap4__example_4_3_5" (main := true)]
theorem ex435Proof_matches_D7 (P Q S : Nat)
    (hPQ : P ≠ Q) (hPS : P ≠ S) (hQS : Q ≠ S) :
    (∀ i ∈ (gcnfProofToResolution (ex435Proof P Q S) leastAtomPolicy).vertexIds,
      ex435VertexMap i ∈ (ex435D7 P Q S).vertexIds ∧
      ex435VertexMapInv (ex435VertexMap i) = i ∧
      (gcnfProofToResolution (ex435Proof P Q S) leastAtomPolicy).label i = (ex435D7 P Q S).label (ex435VertexMap i)) ∧
    (∀ j ∈ (ex435D7 P Q S).vertexIds,
      ex435VertexMapInv j ∈ (gcnfProofToResolution (ex435Proof P Q S) leastAtomPolicy).vertexIds ∧
      ex435VertexMap (ex435VertexMapInv j) = j) ∧
    ex435VertexMap (gcnfProofToResolution (ex435Proof P Q S) leastAtomPolicy).root = (ex435D7 P Q S).root ∧
    (∀ i ∈ (gcnfProofToResolution (ex435Proof P Q S) leastAtomPolicy).vertexIds,
      ∀ j ∈ (gcnfProofToResolution (ex435Proof P Q S) leastAtomPolicy).vertexIds,
      FiniteGraph.hasEdge (gcnfProofToResolution (ex435Proof P Q S) leastAtomPolicy) i j ↔
        FiniteGraph.hasEdge (ex435D7 P Q S) (ex435VertexMap i) (ex435VertexMap j)) 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D1_replay (P S : Nat) (hPS : P ≠ S) :
    replay (ex435D1 P) (missingLift (ex435InnerSequent P S) (.neg S)) =
      ex435D3 P S 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D3_graft_D2 (P S : Nat) (hPS : P ≠ S) :
    (FiniteGraph.graft (ex435D3 P S) (ex435D2 S)
      (unitInputs (ex435D2 S) (.neg S))).coalesceInputLeaves = ex435ComputedInner P S 

@[blueprint "chap4__example_4_3_5"]
theorem ex435LiftedInner_graft_D5 (P Q S : Nat)
    (hPQ : P ≠ Q) (hPS : P ≠ S) (hQS : Q ≠ S) :
    (FiniteGraph.graft (ex435LiftedInner P Q S) (ex435D5 Q)
      (unitInputs (ex435D5 Q) (.neg Q))).coalesceInputLeaves = ex435Computed P Q S 

end LCS.Resolution.Method.Completeness
end
end
