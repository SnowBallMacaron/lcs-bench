import LCS.Item
import LCS.Util
import LCS.Resolution.Method.FiniteGraph
import Attach
import LCS.Resolution.Method.Completeness.Part2.InnerResolution.ProofsStamp
import LCS.Resolution.Method.Completeness.Part1
import LCS.Resolution.Method.Completeness.Part2.ResolutionExamples
attach_helper_namespace LCS.Resolution.Method.Completeness.Proofs

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

private theorem and_rec_eq {a b : Prop} {motive : a ∧ b → Sort u}
    (f : ∀ ha hb, motive ⟨ha, hb⟩) (h : a ∧ b) :
    @And.rec a b motive f h = f h.1 h.2 := by
  cases h
  rfl



























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


@[blueprint "chap4__example_4_3_5"]
theorem ex435LiftedInner_matches_D6 (P Q S : Nat) :
    (∀ i ∈ (ex435LiftedInner P Q S).vertexIds,
      ex435InnerVertexMap i ∈ (ex435D6 P Q S).vertexIds ∧
      ex435InnerVertexMapInv (ex435InnerVertexMap i) = i ∧
      (ex435LiftedInner P Q S).label i = (ex435D6 P Q S).label (ex435InnerVertexMap i)) ∧
    (∀ j ∈ (ex435D6 P Q S).vertexIds,
      ex435InnerVertexMapInv j ∈ (ex435LiftedInner P Q S).vertexIds ∧
      ex435InnerVertexMap (ex435InnerVertexMapInv j) = j) ∧
    ex435InnerVertexMap (ex435LiftedInner P Q S).root = (ex435D6 P Q S).root ∧
    (∀ i ∈ (ex435LiftedInner P Q S).vertexIds,
      ∀ j ∈ (ex435LiftedInner P Q S).vertexIds,
      FiniteGraph.hasEdge (ex435LiftedInner P Q S) i j ↔
        FiniteGraph.hasEdge (ex435D6 P Q S) (ex435InnerVertexMap i) (ex435InnerVertexMap j)) 


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

@[blueprint "chap4__example_4_3_5"]
theorem ex435Proof_counts (P Q S : Nat) (hPQ : P ≠ Q) (hPS : P ≠ S) (hQS : Q ≠ S) :
    (gcnfProofToResolution (ex435Proof P Q S) leastAtomPolicy).stepCount = 3 ∧
    (gcnfProofToResolution (ex435Proof P Q S) leastAtomPolicy).nodeCount = 7 

@[blueprint "chap4__example_4_3_5"]
theorem ex435InnerProof_matches_D4 (P S : Nat) (hPS : P ≠ S) :
    (∀ i ∈ (gcnfProofToResolution (ex435InnerProof P S) leastAtomPolicy).vertexIds,
      ex435InnerVertexMap i ∈ (ex435D4 P S).vertexIds ∧
      ex435InnerVertexMapInv (ex435InnerVertexMap i) = i ∧
      (gcnfProofToResolution (ex435InnerProof P S) leastAtomPolicy).label i = (ex435D4 P S).label (ex435InnerVertexMap i)) ∧
    (∀ j ∈ (ex435D4 P S).vertexIds,
      ex435InnerVertexMapInv j ∈ (gcnfProofToResolution (ex435InnerProof P S) leastAtomPolicy).vertexIds ∧
      ex435InnerVertexMap (ex435InnerVertexMapInv j) = j) ∧
    ex435InnerVertexMap (gcnfProofToResolution (ex435InnerProof P S) leastAtomPolicy).root = (ex435D4 P S).root ∧
    (∀ i ∈ (gcnfProofToResolution (ex435InnerProof P S) leastAtomPolicy).vertexIds,
      ∀ j ∈ (gcnfProofToResolution (ex435InnerProof P S) leastAtomPolicy).vertexIds,
      FiniteGraph.hasEdge (gcnfProofToResolution (ex435InnerProof P S) leastAtomPolicy) i j ↔
        FiniteGraph.hasEdge (ex435D4 P S) (ex435InnerVertexMap i) (ex435InnerVertexMap j)) 






@[blueprint "chap4__example_4_3_6"]
theorem ex436D1_isAxiomConversion (P : Nat) :
    gcnfProofToResolution (displayedNegativeFirstAxiom P) negativeFirstPolicy = ex436D1 P 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D2_isAxiomConversion (Q : Nat) :
    gcnfProofToResolution (displayedNegativeFirstAxiom Q) negativeFirstPolicy = ex436D2 Q 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D6_isAxiomConversion (R : Nat) :
    gcnfProofToResolution (displayedNegativeFirstAxiom R) negativeFirstPolicy = ex436D6 R 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D3_isReplay (P Q : Nat) (hPQ : P ≠ Q) :
    replay (complementaryGraph (.neg P))
      (missingLift (ex436InnerSequent P Q) (.pos Q)) = ex436D3 P Q 

@[blueprint "chap4__example_4_3_6"]
def ex436ComputedInner (P Q : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.neg P], none⟩,
    ⟨Clause.ofList [.pos P, .pos Q], none⟩,
    ⟨Clause.ofList [.pos Q], some ⟨.neg P, 0, 1⟩⟩,
    ⟨Clause.ofList [.neg Q], none⟩,
    ⟨Clause.ofList [.pos Q], none⟩,
    ⟨Clause.empty, some ⟨.neg Q, 3, 2⟩⟩], 5⟩

@[blueprint "chap4__example_4_3_6"]
theorem ex436InnerConversion_raw (P Q : Nat) (hPQ : P ≠ Q) :
    gcnfProofToResolution (ex436InnerProof P Q) negativeFirstPolicy =
      ex436ComputedInner P Q 

@[blueprint "chap4__example_4_3_6"]
def ex436ComputedD5 (P Q R : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.neg P, .pos R], none⟩,
    ⟨Clause.ofList [.pos P, .pos Q], none⟩,
    ⟨Clause.ofList [.pos Q, .pos R], some ⟨.neg P, 0, 1⟩⟩,
    ⟨Clause.ofList [.neg Q], none⟩,
    ⟨Clause.ofList [.pos Q, .pos R], none⟩,
    ⟨Clause.ofList [.pos R], some ⟨.neg Q, 3, 2⟩⟩], 5⟩

@[blueprint "chap4__example_4_3_6"]
def ex436NarratedMiddleComputed (P Q R : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.neg P, .pos R], none⟩,
    ⟨Clause.ofList [.pos P, .pos Q], none⟩,
    ⟨Clause.ofList [.pos Q, .pos R], some ⟨.neg P, 0, 1⟩⟩,
    ⟨Clause.ofList [.neg Q], none⟩,
    ⟨Clause.ofList [.pos Q, .pos R], none⟩,
    ⟨Clause.ofList [.pos R], some ⟨.neg Q, 3, 2⟩⟩,
    ⟨Clause.ofList [.neg R], none⟩,
    ⟨Clause.ofList [.pos R], none⟩,
    ⟨Clause.empty, some ⟨.neg R, 6, 5⟩⟩], 8⟩

@[blueprint "chap4__example_4_3_6"]
def ex436DisplayedMiddleComputed (P Q R : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.neg R], none⟩,
    ⟨Clause.ofList [.pos R, .neg P], none⟩,
    ⟨Clause.ofList [.neg P], some ⟨.neg R, 0, 1⟩⟩,
    ⟨Clause.ofList [.neg P], none⟩,
    ⟨Clause.ofList [.pos P, .pos Q], none⟩,
    ⟨Clause.ofList [.pos Q], some ⟨.neg P, 2, 4⟩⟩,
    ⟨Clause.ofList [.neg Q], none⟩,
    ⟨Clause.ofList [.pos Q], none⟩,
    ⟨Clause.empty, some ⟨.neg Q, 6, 5⟩⟩], 8⟩

@[blueprint "chap4__example_4_3_6"]
def ex436NarratedComputed (P Q R : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.neg P, .pos R], none⟩,
    ⟨Clause.ofList [.pos P, .pos Q, .pos R], none⟩,
    ⟨Clause.ofList [.pos Q, .pos R], some ⟨.neg P, 0, 1⟩⟩,
    ⟨Clause.ofList [.neg Q], none⟩,
    ⟨Clause.ofList [.pos Q, .pos R], none⟩,
    ⟨Clause.ofList [.pos R], some ⟨.neg Q, 3, 2⟩⟩,
    ⟨Clause.ofList [.neg R], none⟩,
    ⟨Clause.ofList [.pos R], none⟩,
    ⟨Clause.empty, some ⟨.neg R, 6, 5⟩⟩], 8⟩

@[blueprint "chap4__example_4_3_6"]
def ex436DisplayedComputed (P Q R : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.neg R], none⟩,
    ⟨Clause.ofList [.pos R, .neg P], none⟩,
    ⟨Clause.ofList [.neg P], some ⟨.neg R, 0, 1⟩⟩,
    ⟨Clause.ofList [.neg P, .pos R], none⟩,
    ⟨Clause.ofList [.pos P, .pos Q, .pos R], none⟩,
    ⟨Clause.ofList [.pos Q, .pos R], some ⟨.neg P, 2, 4⟩⟩,
    ⟨Clause.ofList [.neg Q], none⟩,
    ⟨Clause.ofList [.pos Q, .pos R], none⟩,
    ⟨Clause.ofList [.pos R], some ⟨.neg Q, 6, 5⟩⟩,
    ⟨Clause.ofList [.neg R], none⟩,
    ⟨Clause.ofList [.pos R], none⟩,
    ⟨Clause.empty, some ⟨.neg R, 0, 8⟩⟩], 11⟩

@[blueprint "chap4__example_4_3_6"]
def ex436ComputedInnerReplay (P Q : Nat) (f : Clause → Clause) : FiniteGraph :=
  let c0 := f (Clause.ofList [.neg P])
  let c1 := f (Clause.ofList [.pos P, .pos Q])
  let c2 := GCNF.Clause.union (GCNF.Clause.remove c0 (Literal.neg P)) (GCNF.Clause.remove c1 (Literal.neg P).conjugate)
  let c3 := f (Clause.ofList [.neg Q])
  let c4 := f (Clause.ofList [.pos Q])
  let c5 := GCNF.Clause.union (GCNF.Clause.remove c3 (Literal.neg Q)) (GCNF.Clause.remove c2 (Literal.neg Q).conjugate)
  ⟨[⟨c0, none⟩,
    ⟨c1, none⟩,
    ⟨c2, some ⟨.neg P, 0, 1⟩⟩,
    ⟨c3, none⟩,
    ⟨c4, none⟩,
    ⟨c5, some ⟨.neg Q, 3, 2⟩⟩], 5⟩

end LCS.Resolution.Method.Completeness
end
end

