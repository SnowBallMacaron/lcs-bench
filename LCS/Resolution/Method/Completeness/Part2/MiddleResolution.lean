import LCS.Item
import LCS.Util
import LCS.Resolution.Method.FiniteGraph
import Attach
import LCS.Resolution.Method.Completeness.Part2.MiddleResolution.ProofsStamp
import LCS.Resolution.Method.Completeness.Part1
import LCS.Resolution.Method.Completeness.Part2.ResolutionExamples
import LCS.Resolution.Method.Completeness.Part2.InnerResolution
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

@[blueprint "chap4__example_4_3_6"]
def ex436NarratedMiddleComputedReplay (P Q R : Nat) (f : Clause → Clause) : FiniteGraph :=
  let c0 := f (Clause.ofList [.neg P, .pos R])
  let c1 := f (Clause.ofList [.pos P, .pos Q])
  let c2 := GCNF.Clause.union (GCNF.Clause.remove c0 (Literal.neg P)) (GCNF.Clause.remove c1 (Literal.neg P).conjugate)
  let c3 := f (Clause.ofList [.neg Q])
  let c4 := f (Clause.ofList [.pos Q, .pos R])
  let c5 := GCNF.Clause.union (GCNF.Clause.remove c3 (Literal.neg Q)) (GCNF.Clause.remove c2 (Literal.neg Q).conjugate)
  let c6 := f (Clause.ofList [.neg R])
  let c7 := f (Clause.ofList [.pos R])
  let c8 := GCNF.Clause.union (GCNF.Clause.remove c6 (Literal.neg R)) (GCNF.Clause.remove c5 (Literal.neg R).conjugate)
  ⟨[⟨c0, none⟩,
    ⟨c1, none⟩,
    ⟨c2, some ⟨.neg P, 0, 1⟩⟩,
    ⟨c3, none⟩,
    ⟨c4, none⟩,
    ⟨c5, some ⟨.neg Q, 3, 2⟩⟩,
    ⟨c6, none⟩,
    ⟨c7, none⟩,
    ⟨c8, some ⟨.neg R, 6, 5⟩⟩], 8⟩



@[blueprint "chap4__example_4_3_6"]
def ex436DisplayedMiddleComputedReplay (P Q R : Nat) (f : Clause → Clause) : FiniteGraph :=
  let c0 := f (Clause.ofList [.neg R])
  let c1 := f (Clause.ofList [.pos R, .neg P])
  let c2 := GCNF.Clause.union (GCNF.Clause.remove c0 (Literal.neg R)) (GCNF.Clause.remove c1 (Literal.neg R).conjugate)
  let c3 := f (Clause.ofList [.neg P])
  let c4 := f (Clause.ofList [.pos P, .pos Q])
  let c5 := GCNF.Clause.union (GCNF.Clause.remove c2 (Literal.neg P)) (GCNF.Clause.remove c4 (Literal.neg P).conjugate)
  let c6 := f (Clause.ofList [.neg Q])
  let c7 := f (Clause.ofList [.pos Q])
  let c8 := GCNF.Clause.union (GCNF.Clause.remove c6 (Literal.neg Q)) (GCNF.Clause.remove c5 (Literal.neg Q).conjugate)
  ⟨[⟨c0, none⟩,
    ⟨c1, none⟩,
    ⟨c2, some ⟨.neg R, 0, 1⟩⟩,
    ⟨c3, none⟩,
    ⟨c4, none⟩,
    ⟨c5, some ⟨.neg P, 2, 4⟩⟩,
    ⟨c6, none⟩,
    ⟨c7, none⟩,
    ⟨c8, some ⟨.neg Q, 6, 5⟩⟩], 8⟩



@[blueprint "chap4__example_4_3_6"]
def ex436ShorterLiftedComputed (P Q R : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.neg P, .pos R], none⟩,
    ⟨Clause.ofList [.pos P, .pos Q, .pos R], none⟩,
    ⟨Clause.ofList [.pos Q, .pos R], some ⟨.neg P, 0, 1⟩⟩,
    ⟨Clause.ofList [.neg Q], none⟩,
    ⟨Clause.ofList [.pos Q, .pos R], none⟩,
    ⟨Clause.ofList [.pos R], some ⟨.neg Q, 3, 2⟩⟩], 5⟩

@[blueprint "chap4__example_4_3_6"]
def ex436DisplayedLiftedComputed (P Q R : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.neg R], none⟩,
    ⟨Clause.ofList [.pos R, .neg P], none⟩,
    ⟨Clause.ofList [.neg P], some ⟨.neg R, 0, 1⟩⟩,
    ⟨Clause.ofList [.neg P, .pos R], none⟩,
    ⟨Clause.ofList [.pos P, .pos Q, .pos R], none⟩,
    ⟨Clause.ofList [.pos Q, .pos R], some ⟨.neg P, 2, 4⟩⟩,
    ⟨Clause.ofList [.neg Q], none⟩,
    ⟨Clause.ofList [.pos Q, .pos R], none⟩,
    ⟨Clause.ofList [.pos R], some ⟨.neg Q, 6, 5⟩⟩], 8⟩

@[blueprint "chap4__example_4_3_6"]
theorem ex436D5_isReplay (P Q R : Nat) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    replay (ex436ComputedInner P Q) (missingLift (ex436MiddleSequent P Q R) (.pos R)) =
      ex436ComputedD5 P Q R 

@[blueprint "chap4__example_4_3_6"]
theorem ex436Shorter_isReplay (P Q R : Nat) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    replay (ex436ComputedInner P Q) (missingLift (ex436Sequent P Q R) (.pos R)) =
      ex436ShorterLiftedComputed P Q R 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D8_isReplay (P Q R : Nat) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    replay (ex436NarratedMiddleComputed P Q R) (missingLift (ex436Sequent P Q R) (.pos R)) =
      ex436NarratedComputed P Q R 

@[blueprint "chap4__example_4_3_6"]
theorem ex436Displayed_isReplay (P Q R : Nat) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    replay (ex436DisplayedMiddleComputed P Q R) (missingLift (ex436Sequent P Q R) (.pos R)) =
      ex436DisplayedLiftedComputed P Q R 











@[blueprint "chap4__example_4_3_6"]
theorem ex436NarratedMiddleConversion_raw (P Q R : Nat)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    gcnfProofToResolution (ex436NarratedMiddleProof P Q R) negativeFirstPolicy =
      ex436NarratedMiddleComputed P Q R 

@[blueprint "chap4__example_4_3_6"]
theorem ex436ShorterConversion_raw (P Q R : Nat)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    gcnfProofToResolution (ex436ShorterProof P Q R) negativeFirstPolicy =
      ex436NarratedComputed P Q R 

@[blueprint "chap4__example_4_3_6"]
def ex436DisplayedFirstLifted (P R : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.neg R], none⟩,
    ⟨Clause.ofList [.pos R, .neg P], none⟩,
    ⟨Clause.ofList [.neg P], some ⟨.neg R, 0, 1⟩⟩], 2⟩

@[blueprint "chap4__example_4_3_6"]
theorem ex436DisplayedFirstLifted_isReplay (P Q R : Nat)
    (_hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    replay (complementaryGraph (.neg R))
      (missingLift (ex436MiddleSequent P Q R) (.neg P)) = ex436DisplayedFirstLifted P R 

@[blueprint "chap4__example_4_3_6"]
theorem ex436DisplayedMiddleConversion_raw (P Q R : Nat)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    gcnfProofToResolution (ex436MiddleProof P Q R) negativeFirstPolicy =
      ex436DisplayedMiddleComputed P Q R 

@[blueprint "chap4__example_4_3_6"]
theorem ex436NarratedConversion_raw (P Q R : Nat)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    gcnfProofToResolution (ex436NarratedProof P Q R) negativeFirstPolicy =
      ex436NarratedComputed P Q R 

@[blueprint "chap4__example_4_3_6"]
theorem ex436DisplayedConversion_raw (P Q R : Nat)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    gcnfProofToResolution (ex436Proof P Q R) negativeFirstPolicy =
      ex436DisplayedComputed P Q R 

@[blueprint "chap4__example_4_3_6"]
theorem ex436NarratedComputed_counts (P Q R : Nat) :
    (ex436NarratedComputed P Q R).stepCount = 3 ∧
      (ex436NarratedComputed P Q R).nodeCount = 7 

@[blueprint "chap4__example_4_3_6"]
theorem ex436DisplayedComputed_counts (P Q R : Nat) :
    (ex436DisplayedComputed P Q R).stepCount = 4 ∧
      (ex436DisplayedComputed P Q R).nodeCount = 8 

@[blueprint "chap4__example_4_3_6"]
theorem ex436DisplayedConversion_counts (P Q R : Nat)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    (gcnfProofToResolution (ex436Proof P Q R) negativeFirstPolicy).stepCount = 4 ∧
      (gcnfProofToResolution (ex436Proof P Q R) negativeFirstPolicy).nodeCount = 8 

@[blueprint "chap4__example_4_3_6"]
theorem ex436NarratedConversion_counts (P Q R : Nat)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    (gcnfProofToResolution (ex436NarratedProof P Q R) negativeFirstPolicy).stepCount = 3 ∧
      (gcnfProofToResolution (ex436NarratedProof P Q R) negativeFirstPolicy).nodeCount = 7 

@[blueprint "chap4__example_4_3_6"]
theorem ex436ShorterConversion_counts (P Q R : Nat)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    (gcnfProofToResolution (ex436ShorterProof P Q R) negativeFirstPolicy).stepCount = 3 ∧
      (gcnfProofToResolution (ex436ShorterProof P Q R) negativeFirstPolicy).nodeCount = 7 

@[blueprint "chap4__example_4_3_6"]
def ex436NarratedVertexMap : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 5 => 5 | 6 => 3 | 8 => 6 | i => i

@[blueprint "chap4__example_4_3_6"]
def ex436NarratedVertexMapInv : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 6 | 4 => 2 | 5 => 5 | 6 => 8 | i => i

/-- An explicit label-preserving bijection of the represented vertices.
The two premise positions may be exchanged by the source drawing. -/
@[blueprint "chap4__example_4_3_6"]
theorem ex436NarratedComputed_matches_D8 (P Q R : Nat) :
    (∀ i ∈ (ex436NarratedComputed P Q R).vertexIds,
      ex436NarratedVertexMap i ∈ (ex436D8 P Q R).vertexIds ∧
      ex436NarratedVertexMapInv (ex436NarratedVertexMap i) = i ∧
      (ex436NarratedComputed P Q R).label i = (ex436D8 P Q R).label (ex436NarratedVertexMap i)) ∧
    (∀ j ∈ (ex436D8 P Q R).vertexIds,
      ex436NarratedVertexMapInv j ∈ (ex436NarratedComputed P Q R).vertexIds ∧
      ex436NarratedVertexMap (ex436NarratedVertexMapInv j) = j) ∧
    ex436NarratedVertexMap (ex436NarratedComputed P Q R).root = (ex436D8 P Q R).root ∧
    (∀ i ∈ (ex436NarratedComputed P Q R).vertexIds,
      ∀ j ∈ (ex436NarratedComputed P Q R).vertexIds,
      FiniteGraph.hasEdge (ex436NarratedComputed P Q R) i j ↔
        FiniteGraph.hasEdge (ex436D8 P Q R) (ex436NarratedVertexMap i) (ex436NarratedVertexMap j)) 


/-- An explicit label-preserving bijection of the represented vertices.
The two premise positions may be exchanged by the source drawing. -/
@[blueprint "chap4__example_4_3_6"]
theorem ex436NarratedMiddleComputed_matches_D7 (P Q R : Nat) :
    (∀ i ∈ (ex436NarratedMiddleComputed P Q R).vertexIds,
      ex436NarratedVertexMap i ∈ (ex436D7 P Q R).vertexIds ∧
      ex436NarratedVertexMapInv (ex436NarratedVertexMap i) = i ∧
      (ex436NarratedMiddleComputed P Q R).label i = (ex436D7 P Q R).label (ex436NarratedVertexMap i)) ∧
    (∀ j ∈ (ex436D7 P Q R).vertexIds,
      ex436NarratedVertexMapInv j ∈ (ex436NarratedMiddleComputed P Q R).vertexIds ∧
      ex436NarratedVertexMap (ex436NarratedVertexMapInv j) = j) ∧
    ex436NarratedVertexMap (ex436NarratedMiddleComputed P Q R).root = (ex436D7 P Q R).root ∧
    (∀ i ∈ (ex436NarratedMiddleComputed P Q R).vertexIds,
      ∀ j ∈ (ex436NarratedMiddleComputed P Q R).vertexIds,
      FiniteGraph.hasEdge (ex436NarratedMiddleComputed P Q R) i j ↔
        FiniteGraph.hasEdge (ex436D7 P Q R) (ex436NarratedVertexMap i) (ex436NarratedVertexMap j)) 

@[blueprint "chap4__example_4_3_6"]
def ex436InnerVertexMap : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 5 => 4 | i => i

@[blueprint "chap4__example_4_3_6"]
def ex436InnerVertexMapInv : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | i => i

/-- An explicit label-preserving bijection of the represented vertices.
The two premise positions may be exchanged by the source drawing. -/
@[blueprint "chap4__example_4_3_6"]
theorem ex436ComputedInner_matches_D4 (P Q : Nat) :
    (∀ i ∈ (ex436ComputedInner P Q).vertexIds,
      ex436InnerVertexMap i ∈ (ex436D4 P Q).vertexIds ∧
      ex436InnerVertexMapInv (ex436InnerVertexMap i) = i ∧
      (ex436ComputedInner P Q).label i = (ex436D4 P Q).label (ex436InnerVertexMap i)) ∧
    (∀ j ∈ (ex436D4 P Q).vertexIds,
      ex436InnerVertexMapInv j ∈ (ex436ComputedInner P Q).vertexIds ∧
      ex436InnerVertexMap (ex436InnerVertexMapInv j) = j) ∧
    ex436InnerVertexMap (ex436ComputedInner P Q).root = (ex436D4 P Q).root ∧
    (∀ i ∈ (ex436ComputedInner P Q).vertexIds,
      ∀ j ∈ (ex436ComputedInner P Q).vertexIds,
      FiniteGraph.hasEdge (ex436ComputedInner P Q) i j ↔
        FiniteGraph.hasEdge (ex436D4 P Q) (ex436InnerVertexMap i) (ex436InnerVertexMap j)) 

/-- An explicit label-preserving bijection of the represented vertices.
The two premise positions may be exchanged by the source drawing. -/
@[blueprint "chap4__example_4_3_6"]
theorem ex436ComputedD5_matches_D5 (P Q R : Nat) :
    (∀ i ∈ (ex436ComputedD5 P Q R).vertexIds,
      ex436InnerVertexMap i ∈ (ex436D5 P Q R).vertexIds ∧
      ex436InnerVertexMapInv (ex436InnerVertexMap i) = i ∧
      (ex436ComputedD5 P Q R).label i = (ex436D5 P Q R).label (ex436InnerVertexMap i)) ∧
    (∀ j ∈ (ex436D5 P Q R).vertexIds,
      ex436InnerVertexMapInv j ∈ (ex436ComputedD5 P Q R).vertexIds ∧
      ex436InnerVertexMap (ex436InnerVertexMapInv j) = j) ∧
    ex436InnerVertexMap (ex436ComputedD5 P Q R).root = (ex436D5 P Q R).root ∧
    (∀ i ∈ (ex436ComputedD5 P Q R).vertexIds,
      ∀ j ∈ (ex436ComputedD5 P Q R).vertexIds,
      FiniteGraph.hasEdge (ex436ComputedD5 P Q R) i j ↔
        FiniteGraph.hasEdge (ex436D5 P Q R) (ex436InnerVertexMap i) (ex436InnerVertexMap j)) 

/-- Example 4.3.6: the narrated premise ordering executes to the displayed D8,
with an explicit bijection preserving the root, vertex labels, and graph edges. -/
@[blueprint "chap4__example_4_3_6" (main := true)]
theorem ex436NarratedProof_matches_D8 (P Q R : Nat)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    (∀ i ∈ (gcnfProofToResolution (ex436NarratedProof P Q R) negativeFirstPolicy).vertexIds,
      ex436NarratedVertexMap i ∈ (ex436D8 P Q R).vertexIds ∧
      ex436NarratedVertexMapInv (ex436NarratedVertexMap i) = i ∧
      (gcnfProofToResolution (ex436NarratedProof P Q R) negativeFirstPolicy).label i = (ex436D8 P Q R).label (ex436NarratedVertexMap i)) ∧
    (∀ j ∈ (ex436D8 P Q R).vertexIds,
      ex436NarratedVertexMapInv j ∈ (gcnfProofToResolution (ex436NarratedProof P Q R) negativeFirstPolicy).vertexIds ∧
      ex436NarratedVertexMap (ex436NarratedVertexMapInv j) = j) ∧
    ex436NarratedVertexMap (gcnfProofToResolution (ex436NarratedProof P Q R) negativeFirstPolicy).root = (ex436D8 P Q R).root ∧
    (∀ i ∈ (gcnfProofToResolution (ex436NarratedProof P Q R) negativeFirstPolicy).vertexIds,
      ∀ j ∈ (gcnfProofToResolution (ex436NarratedProof P Q R) negativeFirstPolicy).vertexIds,
      FiniteGraph.hasEdge (gcnfProofToResolution (ex436NarratedProof P Q R) negativeFirstPolicy) i j ↔
        FiniteGraph.hasEdge (ex436D8 P Q R) (ex436NarratedVertexMap i) (ex436NarratedVertexMap j)) 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D3_graft_D2 (P Q : Nat) (hPQ : P ≠ Q) :
    (FiniteGraph.graft (ex436D3 P Q) (ex436D2 Q)
      (unitInputs (ex436D2 Q) (.pos Q))).coalesceInputLeaves = ex436ComputedInner P Q 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D5_graft_D6 (P Q R : Nat)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    (FiniteGraph.graft (ex436ComputedD5 P Q R) (ex436D6 R)
      (unitInputs (ex436D6 R) (.pos R))).coalesceInputLeaves =
      ex436NarratedMiddleComputed P Q R 

end LCS.Resolution.Method.Completeness
end
end

