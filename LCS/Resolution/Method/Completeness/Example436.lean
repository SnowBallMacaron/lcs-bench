import LCS.Item
import LCS.Util
import LCS.Resolution.Method.FiniteGraph
import Attach
import LCS.Resolution.Method.Completeness.Conversion
import LCS.Resolution.Method.Completeness.Example436.ProofsStamp

/-! # Example 4.3.6: conversions of a GCNF'-proof with the negative-first axiom policy

The displayed, narrated and shorter proof trees, the resolution DAGs D1-D8
of the text, and the runs of the conversion that produce them.
-/
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method

/-- Choose the same atom while reversing the two complementary input positions. -/
@[blueprint "chap4__example_4_3_6"]
def negativeFirstPolicy : AxiomPolicy := fun S h =>
  let witness := leastWitness
    (fun P => Clause.single (.pos P) ∈ S ∧ Clause.single (.neg P) ∈ S) h
  ⟨.neg witness.val, witness.property.2, witness.property.1⟩

open LCS.Resolution.GCNF

@[blueprint "chap4__example_4_3_6"]
def displayedNegativeFirstAxiom (P : Nat) :
    GCNFProofTree (LCS.Finset.union
      (ClauseSequent.single (Clause.single (.neg P)))
      (ClauseSequent.single (Clause.single (.pos P)))) :=
  .axiom_ _ (ClauseSequent.ordinary_union
    (ClauseSequent.ordinary_single (Clause.single_ordinary _))
    (ClauseSequent.ordinary_single (Clause.single_ordinary _)))
    ⟨P, by simp [ClauseSequent.single], by simp [ClauseSequent.single]⟩

/-- The innermost conclusion in the displayed proof of Example 4.3.6. -/
@[blueprint "chap4__example_4_3_6"]
def ex436InnerSequent (P Q : Nat) : ClauseSequent :=
  ClauseSequent.ofList [Clause.single (.neg Q), Clause.single (.neg P),
    Clause.ofList [.pos P, .pos Q]]

/-- The left premise of the root rule in Example 4.3.6. -/
@[blueprint "chap4__example_4_3_6"]
def ex436MiddleSequent (P Q R : Nat) : ClauseSequent :=
  ClauseSequent.ofList [Clause.single (.neg R), Clause.single (.neg Q),
    Clause.ofList [.pos R, .neg P], Clause.ofList [.pos P, .pos Q]]

@[blueprint "chap4__example_4_3_6"]
def ex436Sequent (P Q R : Nat) : ClauseSequent :=
  ClauseSequent.ofList [Clause.single (.neg R), Clause.single (.neg Q),
    Clause.ofList [.pos R, .neg P], Clause.ofList [.pos P, .pos Q, .pos R]]

/-- The two-axiom subtree with leaves ¬P,P and ¬Q,Q, in that order. -/
@[blueprint "chap4__example_4_3_6"]
def ex436InnerProof (P Q : Nat) : GCNFProofTree (ex436InnerSequent P Q) :=
  ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
    apply LCS.Finset.ext
    intro C
    simp [ex436InnerSequent, ClauseSequent.ofList, ClauseSequent.single,
      ClauseSequent.mapSet, clauseWithLiteral_single, or_assoc, or_left_comm, or_comm, eq_comm])
    (.rule (ClauseSequent.ofList [Clause.single (.neg Q), Clause.single (.neg P)])
      (ClauseSequent.single (Clause.single (.pos P))) (.pos Q)
      (ClauseSequent.single (Clause.single (.pos P)))
      (ClauseSequent.single (Clause.single (.neg P)))
      (ClauseSequent.single (Clause.single (.neg Q)))
      (by
        apply ClauseSequent.ordinary_ofList
        intro C hC
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
        rcases hC with rfl | rfl <;> exact Clause.single_ordinary _)
      (ClauseSequent.ordinary_single (Clause.single_ordinary _))
      (displayedNegativeFirstAxiom P) (displayedNegativeFirstAxiom Q)
      ⟨Clause.single (.pos P), by simp [ClauseSequent.single]⟩
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

/-- The middle rule in the order used by the Example 4.3.6 conversion narrative:
the P,Q subtree supplies ¬P and the other premise supplies R. -/
@[blueprint "chap4__example_4_3_6"]
def ex436NarratedMiddleProof (P Q R : Nat) : GCNFProofTree (ex436MiddleSequent P Q R) :=
  ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
    apply LCS.Finset.ext
    intro C
    simp [ex436MiddleSequent, ClauseSequent.ofList, ClauseSequent.single,
      ClauseSequent.mapSet, clauseWithLiteral_single,
      GCNF.clauseOfList_swap (.neg P) (.pos R), or_assoc, or_left_comm, or_comm, eq_comm])
    (.rule
      (ClauseSequent.ofList [Clause.single (.neg R), Clause.single (.neg Q),
        Clause.ofList [.pos P, .pos Q]])
      (ClauseSequent.single (Clause.single (.neg P))) (.pos R)
      (ClauseSequent.single (Clause.single (.neg P)))
      (ClauseSequent.ofList [Clause.single (.neg Q), Clause.ofList [.pos P, .pos Q]])
      (ClauseSequent.single (Clause.single (.neg R)))
      (by
        apply ClauseSequent.ordinary_ofList
        intro C hC
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
        rcases hC with rfl | rfl | rfl
        · exact Clause.single_ordinary _
        · exact Clause.single_ordinary _
        · exact Clause.ofList_cons_ordinary _ _)
      (ClauseSequent.ordinary_single (Clause.single_ordinary _))
      (((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
        apply LCS.Finset.ext
        intro C
        simp [ex436InnerSequent, ClauseSequent.ofList, ClauseSequent.single,
          or_left_comm, or_comm]) (ex436InnerProof P Q)))
      (displayedNegativeFirstAxiom R)
      ⟨Clause.single (.neg P), by simp [ClauseSequent.single]⟩
      (fun _ h => h)
      (by
        intro C hC
        apply LCS.Finset.mem_union.mpr
        left
        simpa [ClauseSequent.ofList] using Or.inr hC)
      (by
        intro C hC
        apply LCS.Finset.mem_union.mpr
        left
        simpa [ClauseSequent.single, ClauseSequent.ofList] using Or.inl hC)))

/-- Complete the common root rule from either middle premise ordering. -/
@[blueprint "chap4__example_4_3_6"]
def ex436WithMiddleProof (P Q R : Nat)
    (middle : GCNFProofTree (ex436MiddleSequent P Q R)) : GCNFProofTree (ex436Sequent P Q R) :=
  ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
    apply LCS.Finset.ext
    intro C
    simp [ex436Sequent, ClauseSequent.ofList, ClauseSequent.single,
      ClauseSequent.mapSet, GCNF.clauseWithLiteral_ofList, or_left_comm, or_comm, eq_comm])
    (.rule
      (ClauseSequent.ofList [Clause.single (.neg R), Clause.single (.neg Q),
        Clause.ofList [.pos R, .neg P]])
      (ClauseSequent.single (Clause.ofList [.pos P, .pos Q])) (.pos R)
      (ClauseSequent.single (Clause.ofList [.pos P, .pos Q]))
      (ClauseSequent.ofList [Clause.single (.neg R), Clause.single (.neg Q),
        Clause.ofList [.pos R, .neg P]])
      (ClauseSequent.single (Clause.single (.neg R)))
      (by
        apply ClauseSequent.ordinary_ofList
        intro C hC
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
        rcases hC with rfl | rfl | rfl
        · exact Clause.single_ordinary _
        · exact Clause.single_ordinary _
        · exact Clause.ofList_cons_ordinary _ _)
      (ClauseSequent.ordinary_single (Clause.ofList_cons_ordinary _ _))
      (((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
        apply LCS.Finset.ext
        intro C
        simp [ex436MiddleSequent, ClauseSequent.ofList, ClauseSequent.single,
          or_left_comm, or_comm]) middle))
      (displayedNegativeFirstAxiom R)
      ⟨Clause.ofList [.pos P, .pos Q], by simp [ClauseSequent.single]⟩
      (fun _ h => h)
      (fun _ h => LCS.Finset.mem_union.mpr (Or.inl h))
      (by
        intro C hC
        apply LCS.Finset.mem_union.mpr
        left
        simpa [ClauseSequent.single, ClauseSequent.ofList] using Or.inl hC)))

/-- The premise ordering used by the narrated D1–D8 construction. -/
@[blueprint "chap4__example_4_3_6"]
def ex436NarratedProof (P Q R : Nat) : GCNFProofTree (ex436Sequent P Q R) :=
  ex436WithMiddleProof P Q R (ex436NarratedMiddleProof P Q R)

@[blueprint "chap4__example_4_3_6"]
theorem ex436NarratedProof_leafCount (P Q R : Nat) :
    (ex436NarratedProof P Q R).leafCount = 4 

/-- The shorter proof uses one grouped rule for {¬P,R} and {P,Q,R}. -/
@[blueprint "chap4__example_4_3_6"]
def ex436ShorterProof (P Q R : Nat) : GCNFProofTree (ex436Sequent P Q R) :=
  ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
    apply LCS.Finset.ext
    intro C
    simp [ex436Sequent, ClauseSequent.ofList,
      ClauseSequent.mapSet, clauseWithLiteral_single, GCNF.clauseWithLiteral_ofList,
      GCNF.clauseOfList_swap (.neg P) (.pos R), or_assoc, or_left_comm, or_comm, eq_comm])
    (.rule
      (ClauseSequent.ofList [Clause.single (.neg R), Clause.single (.neg Q)])
      (ClauseSequent.ofList [Clause.single (.neg P), Clause.ofList [.pos P, .pos Q]]) (.pos R)
      (ClauseSequent.ofList [Clause.single (.neg P), Clause.ofList [.pos P, .pos Q]])
      (ClauseSequent.single (Clause.single (.neg Q)))
      (ClauseSequent.single (Clause.single (.neg R)))
      (by
        apply ClauseSequent.ordinary_ofList
        intro C hC
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
        rcases hC with rfl | rfl <;> exact Clause.single_ordinary _)
      (by
        apply ClauseSequent.ordinary_ofList
        intro C hC
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hC
        rcases hC with rfl | rfl
        · exact Clause.single_ordinary _
        · exact Clause.ofList_cons_ordinary _ _)
      (((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) (by
        apply LCS.Finset.ext
        intro C
        simp [ex436InnerSequent, ClauseSequent.ofList, ClauseSequent.single,
          or_left_comm, or_comm]) (ex436InnerProof P Q)))
      (displayedNegativeFirstAxiom R)
      ⟨Clause.single (.neg P), by simp [ClauseSequent.ofList]⟩
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

@[blueprint "chap4__example_4_3_6"]
theorem ex436ShorterProof_leafCount (P Q R : Nat) : (ex436ShorterProof P Q R).leafCount = 3 

end LCS.Resolution.Method.Completeness
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

@[blueprint "chap4__example_4_3_6"]
def ex436D1 (P : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.neg P], none⟩,
    ⟨Clause.ofList [.pos P], none⟩,
    ⟨Clause.ofList [], some ⟨.neg P, 0, 1⟩⟩], 2⟩

@[blueprint "chap4__example_4_3_6"]
def ex436D2 (Q : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.neg Q], none⟩,
    ⟨Clause.ofList [.pos Q], none⟩,
    ⟨Clause.ofList [], some ⟨.neg Q, 0, 1⟩⟩], 2⟩

@[blueprint "chap4__example_4_3_6"]
def ex436D3 (P Q : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.neg P], none⟩,
    ⟨Clause.ofList [.pos P, .pos Q], none⟩,
    ⟨Clause.ofList [.pos Q], some ⟨.neg P, 0, 1⟩⟩], 2⟩

@[blueprint "chap4__example_4_3_6"]
def ex436D4 (P Q : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.neg P], none⟩,
    ⟨Clause.ofList [.pos P, .pos Q], none⟩,
    ⟨Clause.ofList [.neg Q], none⟩,
    ⟨Clause.ofList [.pos Q], some ⟨.neg P, 0, 1⟩⟩,
    ⟨Clause.ofList [], some ⟨.pos Q, 3, 2⟩⟩], 4⟩

@[blueprint "chap4__example_4_3_6"]
def ex436D5 (P Q R : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos R, .neg P], none⟩,
    ⟨Clause.ofList [.pos P, .pos Q], none⟩,
    ⟨Clause.ofList [.neg Q], none⟩,
    ⟨Clause.ofList [.pos R, .pos Q], some ⟨.neg P, 0, 1⟩⟩,
    ⟨Clause.ofList [.pos R], some ⟨.pos Q, 3, 2⟩⟩], 4⟩

@[blueprint "chap4__example_4_3_6"]
def ex436D6 (R : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.neg R], none⟩,
    ⟨Clause.ofList [.pos R], none⟩,
    ⟨Clause.ofList [], some ⟨.neg R, 0, 1⟩⟩], 2⟩

@[blueprint "chap4__example_4_3_6"]
def ex436D7 (P Q R : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos R, .neg P], none⟩,
    ⟨Clause.ofList [.pos P, .pos Q], none⟩,
    ⟨Clause.ofList [.neg Q], none⟩,
    ⟨Clause.ofList [.neg R], none⟩,
    ⟨Clause.ofList [.pos R, .pos Q], some ⟨.neg P, 0, 1⟩⟩,
    ⟨Clause.ofList [.pos R], some ⟨.pos Q, 4, 2⟩⟩,
    ⟨Clause.ofList [], some ⟨.pos R, 5, 3⟩⟩], 6⟩

@[blueprint "chap4__example_4_3_6"]
def ex436D8 (P Q R : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos R, .neg P], none⟩,
    ⟨Clause.ofList [.pos P, .pos Q, .pos R], none⟩,
    ⟨Clause.ofList [.neg Q], none⟩,
    ⟨Clause.ofList [.neg R], none⟩,
    ⟨Clause.ofList [.pos R, .pos Q], some ⟨.neg P, 0, 1⟩⟩,
    ⟨Clause.ofList [.pos R], some ⟨.pos Q, 4, 2⟩⟩,
    ⟨Clause.ofList [], some ⟨.pos R, 5, 3⟩⟩], 6⟩

@[blueprint "chap4__example_4_3_6"]
theorem ex436D8_wellFormed (P Q R : Nat) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    (ex436D8 P Q R).WellFormed 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D8_counts (P Q R : Nat) :
    (ex436D8 P Q R).stepCount = 3 ∧ (ex436D8 P Q R).nodeCount = 7 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D8_leavesFrom (P Q R : Nat) :
    (ex436D8 P Q R).LeavesFrom (ClauseSequent.ofList [Clause.ofList [.pos R, .neg P],
      Clause.ofList [.pos P, .pos Q, .pos R],
      Clause.ofList [.neg Q],
      Clause.ofList [.neg R]]) 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D8_isRefutationFor (P Q R : Nat) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    (ex436D8 P Q R).IsRefutationFor (ex436Sequent P Q R) 

open LCS.Resolution.GCNF
open LCS.Resolution.Method

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
def ex436ShorterLiftedComputed (P Q R : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.neg P, .pos R], none⟩,
    ⟨Clause.ofList [.pos P, .pos Q, .pos R], none⟩,
    ⟨Clause.ofList [.pos Q, .pos R], some ⟨.neg P, 0, 1⟩⟩,
    ⟨Clause.ofList [.neg Q], none⟩,
    ⟨Clause.ofList [.pos Q, .pos R], none⟩,
    ⟨Clause.ofList [.pos R], some ⟨.neg Q, 3, 2⟩⟩], 5⟩

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
theorem ex436NarratedConversion_raw (P Q R : Nat)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    gcnfProofToResolution (ex436NarratedProof P Q R) negativeFirstPolicy =
      ex436NarratedComputed P Q R 

@[blueprint "chap4__example_4_3_6"]
theorem ex436NarratedComputed_counts (P Q R : Nat) :
    (ex436NarratedComputed P Q R).stepCount = 3 ∧
      (ex436NarratedComputed P Q R).nodeCount = 7 

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
