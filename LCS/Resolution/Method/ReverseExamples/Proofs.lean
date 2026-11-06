import LCS.Resolution.Method.ReverseExamples

namespace LCS.Resolution.Method

open LCS.Resolution.GCNF

namespace ReverseExamples

proof_of ex437Graphs_counts := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


proof_of ex437D_shared := by
  exact ⟨rfl, rfl, rfl⟩


proof_of ex438Graphs_counts := by
  exact ⟨rfl, rfl, rfl, rfl⟩


helper theorem finiteSetEq {S T : Clause}
    (h : ∀ L, L ∈ S ↔ L ∈ T) : S = T := LCS.Finset.ext h

proof_of ex437D_wellFormed := by
  refine ⟨Nat.lt_succ_self 7, ?_, ?_⟩
  · intro i n hi r hr
    have hiBound : i < 8 := (List.getElem?_eq_some_iff.mp hi).1
    have hCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [FiniteGraph.node, ex437D, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.some.injEq] at hi <;>
      subst n <;> simp at hr
    all_goals subst r; simp
  · intro i _ n hi r hr
    have hiBound : i < 8 := by
      have := List.getElem?_eq_some_iff.mp hi
      exact this.1
    have hCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [FiniteGraph.node, ex437D, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.some.injEq] at hi <;>
      subst n <;> simp at hr
    all_goals subst r
    all_goals refine ⟨_, _, rfl, rfl, ?_, ?_, ?_⟩
    all_goals try { simp [Clause.ofList, Literal.conjugate] }
    all_goals apply finiteSetEq; intro L
    all_goals cases L <;> simp_all [Clause.ofList, Clause.union,
      GCNF.Clause.remove, Literal.conjugate, or_comm, or_assoc, and_or_left] <;> omega

proof_of ex437D2_wellFormed := by
  refine ⟨by change 4 < 8; decide, ?_, ?_⟩
  · intro i n hi r hr
    have hiBound : i < 8 := (List.getElem?_eq_some_iff.mp hi).1
    have hCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [FiniteGraph.node, ex437D2, ex437D1, ex437D, FiniteGraph.mapLabels, FiniteGraph.atRoot, FiniteGraph.prune] at hi <;>
      subst n <;> simp at hr
    all_goals subst r; simp
  · intro i hiMem n hi r hr
    have hIds : (ex437D2 P Q).vertexIds = [4, 0, 1] := rfl
    rw [hIds] at hiMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hiMem
    rcases hiMem with rfl | rfl | rfl <;>
      simp [FiniteGraph.node, ex437D2, ex437D1, ex437D, FiniteGraph.mapLabels, FiniteGraph.atRoot, FiniteGraph.prune] at hi <;>
      subst n <;> simp at hr
    all_goals subst r
    all_goals refine ⟨_, _, rfl, rfl, ?_, ?_, ?_⟩
    all_goals try { simp [Clause.ofList, Literal.conjugate,
      GCNF.Clause.remove, hPQ, Ne.symm hPQ] }
    all_goals apply finiteSetEq; intro L
    all_goals cases L <;> simp_all [Clause.ofList, Clause.union,
      GCNF.Clause.remove, Literal.conjugate, or_comm] <;> omega


proof_of ex437D3_wellFormed := by
  refine ⟨by change 7 < 8; decide, ?_, ?_⟩
  · intro i n hi r hr
    have hiBound : i < 8 := (List.getElem?_eq_some_iff.mp hi).1
    have hCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [FiniteGraph.node, ex437D3, ex437D2, ex437D1, ex437D, FiniteGraph.mapLabels, FiniteGraph.atRoot, FiniteGraph.prune] at hi <;>
      subst n <;> simp at hr
    all_goals subst r; simp
  · intro i hiMem n hi r hr
    have hIds : (ex437D3 P Q).vertexIds = [7, 4, 6, 5, 0, 2, 3] := rfl
    rw [hIds] at hiMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hiMem
    rcases hiMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [FiniteGraph.node, ex437D3, ex437D2, ex437D1, ex437D, FiniteGraph.mapLabels, FiniteGraph.atRoot, FiniteGraph.prune] at hi <;>
      subst n <;> simp at hr
    all_goals subst r
    all_goals refine ⟨_, _, rfl, rfl, ?_, ?_, ?_⟩
    all_goals try { simp [Clause.ofList, Literal.conjugate,
      GCNF.Clause.remove, hPQ, Ne.symm hPQ] }
    all_goals apply finiteSetEq; intro L
    all_goals cases L <;> simp_all [Clause.ofList, Clause.union,
      GCNF.Clause.remove, Literal.conjugate, or_comm] <;> omega


proof_of ex437D4_wellFormed := by
  refine ⟨by change 6 < 8; decide, ?_, ?_⟩
  · intro i n hi r hr
    have hiBound : i < 8 := (List.getElem?_eq_some_iff.mp hi).1
    have hCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [FiniteGraph.node, ex437D4, ex437D3, ex437D2, ex437D1, ex437D, FiniteGraph.mapLabels, FiniteGraph.atRoot, FiniteGraph.prune] at hi <;>
      subst n <;> simp at hr
    all_goals subst r; simp
  · intro i hiMem n hi r hr
    have hIds : (ex437D4 P Q).vertexIds = [6, 5, 0, 2, 3] := rfl
    rw [hIds] at hiMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hiMem
    rcases hiMem with rfl | rfl | rfl | rfl | rfl <;>
      simp [FiniteGraph.node, ex437D4, ex437D3, ex437D2, ex437D1, ex437D, FiniteGraph.mapLabels, FiniteGraph.atRoot, FiniteGraph.prune] at hi <;>
      subst n <;> simp at hr
    all_goals subst r
    all_goals refine ⟨_, _, rfl, rfl, ?_, ?_, ?_⟩
    all_goals try { simp [Clause.ofList, Literal.conjugate,
      GCNF.Clause.remove, hPQ, Ne.symm hPQ] }
    all_goals apply finiteSetEq; intro L
    all_goals cases L <;> simp_all [Clause.ofList, Clause.union,
      GCNF.Clause.remove, Literal.conjugate, or_comm] <;> omega

proof_of ex437D6_wellFormed := by
  refine ⟨by change 5 < 8; decide, ?_, ?_⟩
  · intro i n hi r hr
    have hiBound : i < 8 := (List.getElem?_eq_some_iff.mp hi).1
    have hCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [FiniteGraph.node, ex437D6, ex437D5, ex437D4, ex437D3, ex437D2, ex437D1, ex437D, FiniteGraph.mapLabels, FiniteGraph.atRoot, FiniteGraph.prune] at hi <;>
      subst n <;> simp at hr
    all_goals subst r; simp
  · intro i hiMem n hi r hr
    have hIds : (ex437D6 P Q).vertexIds = [5, 0, 2] := rfl
    rw [hIds] at hiMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hiMem
    rcases hiMem with rfl | rfl | rfl <;>
      simp [FiniteGraph.node, ex437D6, ex437D5, ex437D4, ex437D3, ex437D2, ex437D1, ex437D, FiniteGraph.mapLabels, FiniteGraph.atRoot, FiniteGraph.prune] at hi <;>
      subst n <;> simp at hr
    all_goals subst r
    all_goals refine ⟨_, _, rfl, rfl, ?_, ?_, ?_⟩
    all_goals try { simp [Clause.ofList, Literal.conjugate,
      GCNF.Clause.remove, hPQ, Ne.symm hPQ] }
    all_goals apply finiteSetEq; intro L
    all_goals cases L <;> simp_all [Clause.ofList, Clause.union,
      GCNF.Clause.remove, Literal.conjugate, or_comm] <;> omega


proof_of ex438D_wellFormed := by
  refine ⟨by change 8 < 9; decide, ?_, ?_⟩
  · intro i n hi r hr
    have hiBound : i < 9 := (List.getElem?_eq_some_iff.mp hi).1
    have hCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
    rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [FiniteGraph.node, ex438D, FiniteGraph.mapLabels, FiniteGraph.atRoot, FiniteGraph.prune] at hi <;>
      subst n <;> simp at hr
    all_goals subst r; simp
  · intro i hiMem n hi r hr
    have hiBound : i < 9 := (List.getElem?_eq_some_iff.mp hi).1
    have hCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
    rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [FiniteGraph.node, ex438D, FiniteGraph.mapLabels, FiniteGraph.atRoot, FiniteGraph.prune] at hi <;>
      subst n <;> simp at hr
    all_goals subst r
    all_goals refine ⟨_, _, rfl, rfl, ?_, ?_, ?_⟩
    all_goals try { simp [Clause.ofList, Literal.conjugate,
      GCNF.Clause.remove, hPQ, Ne.symm hPQ, hQR, Ne.symm hQR] }
    all_goals apply finiteSetEq; intro L
    all_goals cases L <;> simp_all [Clause.ofList, Clause.union,
      GCNF.Clause.remove, Literal.conjugate, or_comm] <;> omega

proof_of ex438D2_wellFormed := by
  refine ⟨by change 6 < 9; decide, ?_, ?_⟩
  · intro i n hi r hr
    have hiBound : i < 9 := (List.getElem?_eq_some_iff.mp hi).1
    have hCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
    rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [FiniteGraph.node, ex438D2, ex438D1, ex438D, FiniteGraph.mapLabels, FiniteGraph.atRoot, FiniteGraph.prune] at hi <;>
      subst n <;> simp at hr
    all_goals subst r; simp
  · intro i hiMem n hi r hr
    have hIds : (ex438D2 P Q R).vertexIds = [6, 5, 0, 1, 2] := rfl
    rw [hIds] at hiMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hiMem
    rcases hiMem with rfl | rfl | rfl | rfl | rfl <;>
      simp [FiniteGraph.node, ex438D2, ex438D1, ex438D, FiniteGraph.mapLabels, FiniteGraph.atRoot, FiniteGraph.prune] at hi <;>
      subst n <;> simp at hr
    all_goals subst r
    all_goals refine ⟨_, _, rfl, rfl, ?_, ?_, ?_⟩
    all_goals try { simp [Clause.ofList, Literal.conjugate,
      GCNF.Clause.remove, hPQ, Ne.symm hPQ, hQR, Ne.symm hQR] }
    all_goals apply finiteSetEq; intro L
    all_goals cases L <;> simp_all [Clause.ofList, Clause.union,
      GCNF.Clause.remove, Literal.conjugate, or_comm] <;> omega


proof_of ex437Trees_counts := by
  simp [ex437T1, ex437T2, ex437T3, ex437T4, GCNFProofTree.leafCount_cast, GCNFProofTree.nodeCount_cast, unitAxiom,
    GCNFProofTree.leafCount, GCNFProofTree.nodeCount,
    (ex437Graphs_counts P Q).2.1]
  repeat first | erw [GCNFProofTree.leafCount_cast] | erw [GCNFProofTree.nodeCount_cast]
  simp [GCNFProofTree.leafCount, GCNFProofTree.nodeCount]


proof_of ex438Trees_fewer_leaves := by
  simp [ex438T1, ex438T2, GCNFProofTree.leafCount_cast, GCNFProofTree.nodeCount_cast, unitAxiom,
    GCNFProofTree.leafCount, GCNFProofTree.nodeCount,
    (ex438Graphs_counts P Q R).2.1]


helper theorem proofDisplay_cast {S T : ClauseSequent} (h : S = T)
    (t : GCNFProofTree S) : proofDisplay (h ▸ t) = proofDisplay t := by
  cases h
  rfl

proof_of ex437D_refutes := by
  refine ⟨ex437D_wellFormed P Q hPQ, ?_, rfl⟩
  intro i hi
  change i ∈ [0, 1, 2, 3] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  all_goals refine ⟨_, rfl, ?_⟩
  all_goals change _ ∈ ClauseSequent.ofList [Clause.ofList [Literal.pos P, Literal.pos Q], Clause.ofList [Literal.pos P, Literal.neg Q],
    Clause.ofList [Literal.neg P, Literal.pos Q], Clause.ofList [Literal.neg P, Literal.neg Q]]
  all_goals simp [ClauseSequent.ofList]


proof_of ex438D_refutes := by
  refine ⟨ex438D_wellFormed P Q R hPQ hQR, ?_, rfl⟩
  intro i hi
  change i ∈ [0, 1, 2, 3, 4] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨_, rfl, ?_⟩
  all_goals change _ ∈ ClauseSequent.ofList [Clause.ofList [Literal.pos P, Literal.pos Q], Clause.ofList [Literal.neg P, Literal.pos R],
    Clause.ofList [Literal.neg Q], Clause.ofList [Literal.neg R, Literal.pos P], Clause.ofList [Literal.neg P]]
  all_goals simp [ClauseSequent.ofList]


helper theorem memCl (L : Literal) (ls : List Literal) : L ∈ Clause.ofList ls ↔ L ∈ ls := by
  simp [Clause.ofList]

helper theorem removeList (ls : List Literal) (L : Literal) :
    GCNF.Clause.remove (Clause.ofList ls) L = Clause.ofList (ls.filter (fun K => decide (K ≠ L))) := by
  apply LCS.Finset.ext
  intro K
  simp [Clause.ofList, GCNF.Clause.remove, List.mem_filter]

helper theorem unionList {α : Type} [DecidableEq α] (xs ys : List α) :
    LCS.Finset.union (LCS.Finset.ofList xs) (LCS.Finset.ofList ys) =
      LCS.Finset.ofList (xs ++ ys) := by
  apply LCS.Finset.ext
  intro x
  simp

helper theorem singleList {α : Type} [DecidableEq α] (x : α) :
    LCS.Finset.singleton x = LCS.Finset.ofList [x] := by
  apply LCS.Finset.ext
  intro y
  simp

helper theorem filterList {α : Type} [DecidableEq α] (p : α → Bool)
    (xs : List α) : LCS.Finset.filter p (LCS.Finset.ofList xs) =
      LCS.Finset.ofList (xs.filter p) := by
  apply LCS.Finset.ext
  intro x
  simp [List.mem_filter]

helper theorem singletonPairEq (A B C : Literal) :
    Clause.ofList [A] = Clause.ofList [B, C] ↔ A = B ∧ A = C := by
  constructor
  · intro h
    have hB : B ∈ Clause.ofList [A] := h.symm ▸ (by simp [Clause.ofList] : B ∈ Clause.ofList [B, C])
    have hC : C ∈ Clause.ofList [A] := h.symm ▸ (by simp [Clause.ofList] : C ∈ Clause.ofList [B, C])
    simpa [Clause.ofList, eq_comm] using And.intro hB hC
  · rintro ⟨rfl, rfl⟩
    apply LCS.Finset.ext
    intro L
    simp [Clause.ofList]

helper theorem singletonEq (A B : Literal) : Clause.ofList [A] = Clause.ofList [B] ↔ A = B := by
  constructor
  · intro h
    have hB : B ∈ Clause.ofList [A] := h.symm ▸ (by simp [Clause.ofList] : B ∈ Clause.ofList [B])
    simpa [Clause.ofList, eq_comm] using hB
  · rintro rfl
    rfl

helper /-- The recursive tree obtained by unfolding the shared input graph. -/
def ex437Tree (P Q : Nat) : ResolutionTree :=
  .resolve
    (.resolve (.axiom_ (Clause.ofList [Literal.pos P, Literal.pos Q])) (.axiom_ (Clause.ofList [Literal.pos P, Literal.neg Q])) (Literal.pos Q))
    (.resolve
      (.resolve (.axiom_ (Clause.ofList [Literal.pos P, Literal.pos Q])) (.axiom_ (Clause.ofList [Literal.neg P, Literal.pos Q])) (Literal.pos P))
      (.axiom_ (Clause.ofList [Literal.neg P, Literal.neg Q])) (Literal.pos Q)) (Literal.pos P)

helper def ex437Tree2 (Q : Nat) : ResolutionTree :=
  .resolve (.axiom_ (Clause.ofList [Literal.pos Q])) (.axiom_ (Clause.ofList [Literal.neg Q])) (Literal.pos Q)

helper def ex437Tree3 (P Q : Nat) : ResolutionTree :=
  .resolve (.axiom_ (Clause.ofList [Literal.pos P]))
    (.resolve
      (.resolve (.axiom_ (Clause.ofList [Literal.pos P, Literal.pos Q])) (.axiom_ (Clause.ofList [Literal.neg P, Literal.pos Q])) (Literal.pos P))
      (.axiom_ (Clause.ofList [Literal.neg P, Literal.neg Q])) (Literal.pos Q)) (Literal.pos P)

helper def ex437Tree4 (P Q : Nat) : ResolutionTree :=
  .resolve
    (.resolve (.axiom_ (Clause.ofList [Literal.pos P, Literal.pos Q])) (.axiom_ (Clause.ofList [Literal.neg P, Literal.pos Q])) (Literal.pos P))
    (.axiom_ (Clause.ofList [Literal.neg Q])) (Literal.pos Q)

helper def ex438Tree (P Q R : Nat) : ResolutionTree :=
  .resolve
    (.resolve
      (.resolve (.axiom_ (Clause.ofList [Literal.pos P, Literal.pos Q])) (.axiom_ (Clause.ofList [Literal.neg P, Literal.pos R])) (Literal.pos P))
      (.axiom_ (Clause.ofList [Literal.neg Q])) (Literal.pos Q))
    (.resolve (.axiom_ (Clause.ofList [Literal.neg R, Literal.pos P])) (.axiom_ (Clause.ofList [Literal.neg P])) (Literal.pos P)) (Literal.pos R)

helper def ex438Tree2 (P Q : Nat) : ResolutionTree :=
  .resolve
    (.resolve (.axiom_ (Clause.ofList [Literal.pos P, Literal.pos Q])) (.axiom_ (Clause.ofList [Literal.neg P])) (Literal.pos P))
    (.axiom_ (Clause.ofList [Literal.neg Q])) (Literal.pos Q)

helper theorem ex437D_unfold (P Q : Nat) (hPQ : P ≠ Q) :
    (ex437D P Q).unfold (ex437D_wellFormed P Q hPQ) = ex437Tree P Q := by
  simp [FiniteGraph.unfold, FiniteGraph.unfoldAt, ex437D, ex437Tree]

helper theorem ex437D3_unfold (P Q : Nat) (hPQ : P ≠ Q) :
    (ex437D3 P Q).unfold (ex437D3_wellFormed P Q hPQ) = ex437Tree3 P Q := by
  simp [FiniteGraph.unfold, FiniteGraph.unfoldAt, ex437D3, ex437D,
    FiniteGraph.prune, ex437Tree3]

helper theorem ex438D_unfold (P Q R : Nat) (hPQ : P ≠ Q) (hQR : Q ≠ R) :
    (ex438D P Q R).unfold (ex438D_wellFormed P Q R hPQ hQR) = ex438Tree P Q R := by
  simp [FiniteGraph.unfold, FiniteGraph.unfoldAt, ex438D, ex438Tree]

helper theorem proofDisplay_cast_reverse {S T : ClauseSequent} (h : S = T)
    (t : GCNFProofTree T) : proofDisplay (h ▸ t : GCNFProofTree S) = proofDisplay t := by
  cases h
  rfl

helper theorem proofDisplay_weakenTo {S : ClauseSequent} (t : GCNFProofTree S)
    (T : ClauseSequent) (hT : T.isOrdinary) (hSub : LCS.Finset.Subset S T) :
    proofDisplay (weakenTo t T hT hSub) = (proofDisplay t).withRoot T := by
  cases t with
  | axiom_ S hS hTriv =>
    simp only [weakenTo, GCNFProofTree.weaken, proofDisplay_cast,
      proofDisplay_cast_reverse, proofDisplay, ProofDisplay.withRoot]
    congr 1
    apply LCS.Finset.ext
    intro C
    simp only [LCS.Finset.mem_union]
    exact ⟨fun h => h.elim (hSub C) id, Or.inr⟩
  | rule Gamma As B Cs Gamma1 Gamma2 hGamma hAs left right hNe hCs hG1 hG2 =>
    simp only [weakenTo, GCNFProofTree.weaken, proofDisplay_cast,
      proofDisplay_cast_reverse, proofDisplay, ProofDisplay.withRoot]
    congr 1
    apply LCS.Finset.ext
    intro C
    simp only [LCS.Finset.mem_union]
    exact ⟨fun h => h.elim (fun h => h.elim
      (fun h => hSub C (LCS.Finset.mem_union.mpr (Or.inl h))) id)
      (fun h => hSub C (LCS.Finset.mem_union.mpr (Or.inr h))),
      fun h => Or.inl (Or.inr h)⟩

helper theorem proofDisplay_cast_withRoot {S T : ClauseSequent} (h : S = T)
    (t : GCNFProofTree S) : proofDisplay (h ▸ t) = (proofDisplay t).withRoot T := by
  cases h
  cases t <;> rfl

open ResolutionTree

helper theorem convertSplit_display_eq (A B : ResolutionTree) (L : Literal)
    (S : ClauseSequent) (hS : S.isOrdinary)
    (hAS : LCS.Finset.Subset A.inputs S) (hBS : LCS.Finset.Subset B.inputs S)
    (hA : A.IsWellFormed) (hB : B.IsWellFormed)
    (hALabel : A.label = GCNF.Clause.single L)
    (hBLabel : B.label = GCNF.Clause.single L.conjugate)
    (hPos : 0 < A.treeStepCount)
    (rec : ∀ U : ResolutionTree,
      U.treeStepCount < 1 + A.treeStepCount + B.treeStepCount →
      U.IsWellFormed → U.label = GCNF.Clause.empty →
      U.inputs.isOrdinary → Conversion U)
    (hrec : ∀ U hu hU he ho,
      proofDisplay (rec U hu hU he ho).val = conversionDisplay U) :
    proofDisplay (convertSplit A B L S hS hAS hBS hA hB hALabel hBLabel hPos rec).val =
      combineConversionDisplays A L S
        (conversionDisplay (A.eraseLiteral L))
        (conversionDisplay (.resolve (.axiom_ (GCNF.Clause.single L)) B L)) := by
  unfold convertSplit combineConversionDisplays
  split
  · rename_i hUnit
    simp only [dif_pos hUnit, proofDisplay_weakenTo]
    refine (proofDisplay_weakenTo _ _ _ _).trans ?_
    exact congrArg (ProofDisplay.withRoot S) (hrec _ _ _ _ _)
  · rename_i hUnit
    simp only [dif_neg hUnit]
    split
    · rename_i hOld
      simp only [proofDisplay_weakenTo]
      rw [hrec]
    · rename_i hOld
      dsimp only
      rw [proofDisplay_cast_withRoot]
      simp only [proofDisplay, ProofDisplay.withRoot, proofDisplay_cast,
        proofDisplay_cast_reverse, hrec]
      exact congrArg (ProofDisplay.fork S _) (hrec _ _ _ _ _)

helper /-- The displayed recursive construction is the exact output of the proof-producing
algorithm, including both root-weakening cases. -/
theorem toGCNF_display_eq_conversionDisplay (T : ResolutionTree)
    (hWF : T.IsWellFormed) (hEmpty : T.label = GCNF.Clause.empty)
    (hOrdinary : T.inputs.isOrdinary) :
    proofDisplay (toGCNF T hWF hEmpty hOrdinary).val = conversionDisplay T := by
  have aux : ∀ n (T : ResolutionTree), T.treeStepCount = n →
      ∀ (hWF : T.IsWellFormed) (hEmpty : T.label = GCNF.Clause.empty)
        (hOrdinary : T.inputs.isOrdinary),
      proofDisplay (toGCNF T hWF hEmpty hOrdinary).val = conversionDisplay T := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro T hn hWF hEmpty hOrdinary
      cases T with
      | axiom_ C =>
        exact (hOrdinary C ((LCS.Finset.mem_singleton _ _).mpr rfl) hEmpty).elim
      | resolve A B L =>
        cases A with
        | axiom_ C =>
          cases B with
          | axiom_ D =>
            rw [toGCNF, conversionDisplay]
            cases L <;> rfl
          | resolve B₁ B₂ P =>
            rw [toGCNF, conversionDisplay]
            apply convertSplit_display_eq
            intro U hu hU he ho
            apply ih U.treeStepCount _ U rfl hU he ho
            simp only [treeStepCount] at hn hu
            omega
        | resolve A₁ A₂ P =>
          rw [toGCNF, conversionDisplay]
          apply convertSplit_display_eq
          intro U hu hU he ho
          apply ih U.treeStepCount _ U rfl hU he ho
          exact hn ▸ hu
  exact aux T.treeStepCount T rfl hWF hEmpty hOrdinary

helper theorem ex437D2_unfold (P Q : Nat) (hPQ : P ≠ Q) :
    (ex437D2 P Q).unfold (ex437D2_wellFormed P Q hPQ) = ex437Tree2 Q := by
  simp [FiniteGraph.unfold, FiniteGraph.unfoldAt, ex437D2, ex437D1, ex437D,
    FiniteGraph.atRoot, FiniteGraph.mapLabels, ex437Tree2,
    removeList, hPQ, Ne.symm hPQ]

helper theorem ex437D4_unfold (P Q : Nat) (hPQ : P ≠ Q) :
    (ex437D4 P Q).unfold (ex437D4_wellFormed P Q hPQ) = ex437Tree4 P Q := by
  simp [FiniteGraph.unfold, FiniteGraph.unfoldAt, ex437D4, ex437D3, ex437D,
    FiniteGraph.atRoot, FiniteGraph.prune, FiniteGraph.mapLabels,
    ex437Tree4, removeList, hPQ, Ne.symm hPQ]

helper theorem ex438D2_unfold (P Q R : Nat) (hPQ : P ≠ Q) (hQR : Q ≠ R) :
    (ex438D2 P Q R).unfold (ex438D2_wellFormed P Q R hPQ hQR) = ex438Tree2 P Q := by
  simp [FiniteGraph.unfold, FiniteGraph.unfoldAt, ex438D2, ex438D1, ex438D,
    FiniteGraph.atRoot, FiniteGraph.mapLabels, ex438Tree2,
    removeList, hPQ, Ne.symm hPQ, hQR, Ne.symm hQR]

helper theorem ex437EraseQ (P Q : Nat) (hPQ : P ≠ Q) :
    (ResolutionTree.resolve (.axiom_ (Clause.ofList [Literal.pos P, Literal.pos Q]))
      (.axiom_ (Clause.ofList [Literal.neg P, Literal.pos Q])) (Literal.pos P)).eraseLiteral (Literal.pos Q) = ex437Tree2 P := by
  simp [ResolutionTree.eraseLiteral, ResolutionTree.replayResolve, ResolutionTree.label,
    GCNF.Clause.union, removeList, Literal.conjugate, ex437Tree2,
    memCl, hPQ, Ne.symm hPQ]

helper theorem ex437Tree4_display (P Q : Nat) (hPQ : P ≠ Q) :
    conversionDisplay (ex437Tree4 P Q) = proofDisplay (ex437T2 P Q) := by
  have hUnit : GCNF.Clause.single (Literal.pos Q) ∉ (ex437Tree4 P Q).inputs := by
    simp only [ex437Tree4, ResolutionTree.inputs, ClauseSequent.single,
      LCS.Finset.mem_union, LCS.Finset.mem_singleton]
    rw [← Clause.ofList_singleton_eq_single]
    simp [singletonPairEq, singletonEq, hPQ, Ne.symm hPQ]
  have hNew : ResolutionTree.newInputs (ex437Tree2 P) (ex437Tree4 P Q).inputs ≠
      LCS.Finset.empty := by
    intro h
    have hc : Clause.ofList [Literal.pos P] ∈ ResolutionTree.newInputs (ex437Tree2 P)
        (ex437Tree4 P Q).inputs := by
      simp [ResolutionTree.newInputs, ex437Tree2, ex437Tree4, ResolutionTree.inputs,
        ClauseSequent.single, singletonPairEq, singletonEq, hPQ, Ne.symm hPQ]
    exact LCS.Finset.not_mem_empty (h ▸ hc)
  unfold ex437Tree4 at hUnit hNew ⊢
  rw [conversionDisplay, combineConversionDisplays, if_neg hUnit, ex437EraseQ P Q hPQ,
    if_neg hNew]
  simp only [ex437Tree2, conversionDisplay, ex437T2, proofDisplay_cast,
    proofDisplay, unitAxiom, ProofDisplay.fork.injEq, ProofDisplay.leaf.injEq]
  refine ⟨?_, ?_, ?_⟩
  all_goals apply LCS.Finset.ext
  all_goals intro C
  all_goals simp [ResolutionTree.inputs, ClauseSequent.ofList,
    ClauseSequent.single, ClauseSequent.mapSet, GCNF.clauseWithLiteral_ofList, ← Clause.ofList_singleton_eq_single,
    or_assoc, or_comm, or_left_comm, eq_comm]

helper theorem memRemove (L K : Literal) (C : GCNF.Clause) :
    L ∈ GCNF.Clause.remove C K ↔ L ∈ C ∧ L ≠ K := by
  simp [GCNF.Clause.remove]

helper theorem pairSwap (A B : Literal) : Clause.ofList [A, B] = Clause.ofList [B, A] := by
  apply LCS.Finset.ext
  intro L
  simp [Clause.ofList, or_comm]

helper theorem ex437EraseNegP (P Q : Nat) (hPQ : P ≠ Q) :
    (ResolutionTree.resolve
      (.resolve (.axiom_ (Clause.ofList [Literal.pos P, Literal.pos Q])) (.axiom_ (Clause.ofList [Literal.neg P, Literal.pos Q])) (Literal.pos P))
      (.axiom_ (Clause.ofList [Literal.neg P, Literal.neg Q])) (Literal.pos Q)).eraseLiteral (Literal.neg P) = ex437Tree4 P Q := by
  simp [ResolutionTree.eraseLiteral, ResolutionTree.replayResolve, ResolutionTree.label,
    GCNF.Clause.union, removeList, memRemove, Literal.conjugate, ex437Tree4,
    memCl, hPQ, Ne.symm hPQ]

helper theorem ex437Tree3_display (P Q : Nat) (hPQ : P ≠ Q) :
    conversionDisplay (ex437Tree3 P Q) = proofDisplay (ex437T3 P Q) := by
  have hUnit : GCNF.Clause.single (Literal.neg P) ∉ (ex437Tree3 P Q).inputs := by
    simp only [ex437Tree3, ResolutionTree.inputs, ClauseSequent.single,
      LCS.Finset.mem_union, LCS.Finset.mem_singleton]
    rw [← Clause.ofList_singleton_eq_single]
    simp [singletonPairEq, singletonEq, hPQ, Ne.symm hPQ]
  have hNew : ResolutionTree.newInputs (ex437Tree4 P Q) (ex437Tree3 P Q).inputs ≠
      LCS.Finset.empty := by
    intro h
    have hc : Clause.ofList [Literal.neg Q] ∈ ResolutionTree.newInputs (ex437Tree4 P Q)
        (ex437Tree3 P Q).inputs := by
      simp [ResolutionTree.newInputs, ex437Tree4, ex437Tree3, ResolutionTree.inputs,
        ClauseSequent.single, singletonPairEq, singletonEq, hPQ, Ne.symm hPQ]
    exact LCS.Finset.not_mem_empty (h ▸ hc)
  unfold ex437Tree3 at hUnit hNew ⊢
  rw [conversionDisplay]
  simp only [Literal.conjugate]
  rw [combineConversionDisplays, if_neg hUnit, ex437EraseNegP P Q hPQ,
    if_neg hNew, ex437Tree4_display P Q hPQ]
  simp only [conversionDisplay, ex437T3, proofDisplay_cast, proofDisplay,
    unitAxiom, ProofDisplay.fork.injEq, ProofDisplay.leaf.injEq]
  refine ⟨?_, rfl, ?_⟩
  all_goals apply LCS.Finset.ext
  all_goals intro C
  all_goals simp [ResolutionTree.inputs, ClauseSequent.ofList,
    ClauseSequent.single, ClauseSequent.mapSet, GCNF.clauseWithLiteral_ofList, ← Clause.ofList_singleton_eq_single,
    pairSwap, or_assoc, or_comm, or_left_comm, eq_comm]

helper theorem ex437EraseP (P Q : Nat) (hPQ : P ≠ Q) :
    (ResolutionTree.resolve (.axiom_ (Clause.ofList [Literal.pos P, Literal.pos Q]))
      (.axiom_ (Clause.ofList [Literal.pos P, Literal.neg Q])) (Literal.pos Q)).eraseLiteral (Literal.pos P) = ex437Tree2 Q := by
  simp [ResolutionTree.eraseLiteral, ResolutionTree.replayResolve, ResolutionTree.label,
    GCNF.Clause.union, removeList, memRemove, Literal.conjugate, ex437Tree2,
    memCl, hPQ, Ne.symm hPQ]

helper theorem ex437Tree_display (P Q : Nat) (hPQ : P ≠ Q) :
    conversionDisplay (ex437Tree P Q) = proofDisplay (ex437T4 P Q) := by
  have hUnit : GCNF.Clause.single (Literal.pos P) ∉ (ex437Tree P Q).inputs := by
    simp only [ex437Tree, ResolutionTree.inputs, ClauseSequent.single,
      LCS.Finset.mem_union, LCS.Finset.mem_singleton]
    rw [← Clause.ofList_singleton_eq_single]
    simp [singletonPairEq, singletonEq, hPQ, Ne.symm hPQ]
  have hNew : ResolutionTree.newInputs (ex437Tree2 Q) (ex437Tree P Q).inputs ≠
      LCS.Finset.empty := by
    intro h
    have hc : Clause.ofList [Literal.pos Q] ∈ ResolutionTree.newInputs (ex437Tree2 Q)
        (ex437Tree P Q).inputs := by
      simp [ResolutionTree.newInputs, ex437Tree2, ex437Tree, ResolutionTree.inputs,
        ClauseSequent.single, singletonPairEq, singletonEq, hPQ, Ne.symm hPQ]
    exact LCS.Finset.not_mem_empty (h ▸ hc)
  unfold ex437Tree at hUnit hNew ⊢
  rw [conversionDisplay, combineConversionDisplays, if_neg hUnit,
    ex437EraseP P Q hPQ, if_neg hNew]
  rw [← Clause.ofList_singleton_eq_single]
  change ProofDisplay.fork _ (conversionDisplay (ex437Tree2 Q))
    (conversionDisplay (ex437Tree3 P Q)) = _
  rw [ex437Tree3_display P Q hPQ]
  simp only [ex437Tree2, conversionDisplay, ex437T4, proofDisplay_cast,
    proofDisplay, unitAxiom, ProofDisplay.fork.injEq, ProofDisplay.leaf.injEq]
  refine ⟨?_, ?_, True.intro⟩
  all_goals apply LCS.Finset.ext
  all_goals intro C
  all_goals simp [ResolutionTree.inputs, ClauseSequent.ofList,
    ClauseSequent.single, ClauseSequent.mapSet, GCNF.clauseWithLiteral_ofList, ← Clause.ofList_singleton_eq_single,
    pairSwap, or_assoc, or_comm, or_left_comm, eq_comm]

helper theorem ex438EraseQ (P Q : Nat) (hPQ : P ≠ Q) :
    (ResolutionTree.resolve (.axiom_ (Clause.ofList [Literal.pos P, Literal.pos Q]))
      (.axiom_ (Clause.ofList [Literal.neg P])) (Literal.pos P)).eraseLiteral (Literal.pos Q) = ex437Tree2 P := by
  simp [ResolutionTree.eraseLiteral, ResolutionTree.replayResolve, ResolutionTree.label,
    GCNF.Clause.union, removeList, Literal.conjugate, ex437Tree2,
    memCl, hPQ, Ne.symm hPQ]

helper theorem ex438Tree2_conversionDisplay (P Q : Nat) (hPQ : P ≠ Q) :
    conversionDisplay (ex438Tree2 P Q) = proofDisplay (ex438T1 P Q) := by
  rw [ex438Tree2, conversionDisplay]
  simp only [ex438EraseQ P Q hPQ]
  simp [combineConversionDisplays, ex438EraseQ P Q hPQ, ResolutionTree.inputs, ClauseSequent.single,
    ← Clause.ofList_singleton_eq_single, singletonPairEq, singletonEq, hPQ, Ne.symm hPQ,
    ResolutionTree.newInputs, ResolutionTree.oldInputs,
    ex437Tree2, conversionDisplay, ex438T1, proofDisplay_cast, proofDisplay,
    unitAxiom, clauseWithLiteral_single, filterList, unionList, singleList]
  have hNotEmpty : LCS.Finset.ofList [Clause.ofList [Literal.pos P]] ≠ LCS.Finset.empty := by
    intro h
    have hm : Clause.ofList [Literal.pos P] ∈ LCS.Finset.ofList [Clause.ofList [Literal.pos P]] := by simp
    exact LCS.Finset.not_mem_empty (h ▸ hm)
  rw [if_neg hNotEmpty]
  congr 1
  apply LCS.Finset.ext
  intro C
  simp [ClauseSequent.ofList, ClauseSequent.mapSet, GCNF.clauseWithLiteral_ofList,
    or_assoc, or_comm, or_left_comm, eq_comm]
  all_goals
    symm
    refine (proofDisplay_cast _ _).trans ?_
    rfl

proof_of ex437D2_refutes := by
  refine ⟨ex437D2_wellFormed P Q hPQ, ?_, ?_⟩
  · intro i hi
    change i ∈ [0, 1] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals change _ ∈ ClauseSequent.ofList [Clause.ofList [Literal.pos Q], Clause.ofList [Literal.neg Q]]
    all_goals simp [ex437D2, ex437D1, ex437D, FiniteGraph.mapLabels,
      FiniteGraph.atRoot, removeList, hPQ, Ne.symm hPQ, ClauseSequent.ofList]
  · change some (GCNF.Clause.remove (Clause.ofList [Literal.pos P]) (Literal.pos P)) = some GCNF.Clause.empty
    rw [removeList]
    simp
    rfl


proof_of ex437D3_refutes := by
  refine ⟨ex437D3_wellFormed P Q hPQ, ?_, rfl⟩
  intro i hi
  change i ∈ [4, 0, 2, 3] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  all_goals refine ⟨_, rfl, ?_⟩
  all_goals change _ ∈ ClauseSequent.ofList [Clause.ofList [Literal.pos P], Clause.ofList [Literal.pos P, Literal.pos Q],
    Clause.ofList [Literal.neg P, Literal.pos Q], Clause.ofList [Literal.neg P, Literal.neg Q]]
  all_goals simp [ClauseSequent.ofList]


proof_of ex437D4_refutes := by
  refine ⟨ex437D4_wellFormed P Q hPQ, ?_, ?_⟩
  · intro i hi
    change i ∈ [0, 2, 3] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals change _ ∈ ClauseSequent.ofList [Clause.ofList [Literal.pos P, Literal.pos Q], Clause.ofList [Literal.neg P, Literal.pos Q], Clause.ofList [Literal.neg Q]]
    all_goals simp [removeList, hPQ, Ne.symm hPQ, ClauseSequent.ofList]
  · change some (GCNF.Clause.remove (Clause.ofList [Literal.neg P]) (Literal.neg P)) = some GCNF.Clause.empty
    rw [removeList]
    simp
    rfl


proof_of ex438D2_refutes := by
  refine ⟨ex438D2_wellFormed P Q R hPQ hQR, ?_, ?_⟩
  · intro i hi
    change i ∈ [0, 1, 2] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals change _ ∈ ClauseSequent.ofList [Clause.ofList [Literal.pos P, Literal.pos Q], Clause.ofList [Literal.neg P], Clause.ofList [Literal.neg Q]]
    all_goals simp [removeList, hPQ, Ne.symm hPQ, ClauseSequent.ofList]
  · change some (GCNF.Clause.remove (Clause.ofList [Literal.pos R]) (Literal.pos R)) = some GCNF.Clause.empty
    rw [removeList]
    simp
    rfl


helper theorem ex438EraseR (P Q R : Nat) (hPQ : P ≠ Q)
    (hPR : P ≠ R) (hQR : Q ≠ R) :
    (ResolutionTree.resolve
      (.resolve (.axiom_ (Clause.ofList [Literal.pos P, Literal.pos Q])) (.axiom_ (Clause.ofList [Literal.neg P, Literal.pos R])) (Literal.pos P))
      (.axiom_ (Clause.ofList [Literal.neg Q])) (Literal.pos Q)).eraseLiteral (Literal.pos R) = ex438Tree2 P Q := by
  simp [ResolutionTree.eraseLiteral, ResolutionTree.replayResolve, ResolutionTree.label,
    GCNF.Clause.union, removeList, Literal.conjugate, ex438Tree2,
    memCl, memRemove, hPQ, Ne.symm hPQ, hPR, Ne.symm hPR, hQR, Ne.symm hQR]

helper theorem ex438Tree_conversionDisplay (P Q R : Nat) (hPQ : P ≠ Q)
    (hPR : P ≠ R) (hQR : Q ≠ R) :
    conversionDisplay (ex438Tree P Q R) = proofDisplay (ex438T2 P Q R) := by
  have hUnit : GCNF.Clause.single (Literal.pos R) ∉ (ex438Tree P Q R).inputs := by
    simp [ex438Tree, ResolutionTree.inputs, ClauseSequent.single,
      ← Clause.ofList_singleton_eq_single, singletonPairEq, singletonEq, hPR, Ne.symm hPR,
      hQR, Ne.symm hQR]
  have hNew : newInputs (ex438Tree2 P Q) (ex438Tree P Q R).inputs = LCS.Finset.empty := by
    apply LCS.Finset.ext
    intro C
    simp [newInputs, ex438Tree2, ex438Tree, ResolutionTree.inputs,
      ClauseSequent.single, LCS.Finset.mem_filter, LCS.Finset.mem_empty]
    constructor
    · rintro ⟨h, hn⟩
      rcases h with (h | h) | h <;> simp_all
    · intro h
      exact (LCS.Finset.not_mem_empty h).elim
  dsimp only [ex438Tree] at hUnit hNew
  rw [ex438Tree, conversionDisplay]
  rw [combineConversionDisplays, if_neg hUnit, ex438EraseR P Q R hPQ hPR hQR,
    if_pos hNew, ex438Tree2_conversionDisplay P Q hPQ]
  simp only [ex438T1, ex438T2, proofDisplay_cast, proofDisplay,
    ProofDisplay.withRoot]
  congr 1
  apply LCS.Finset.ext
  intro C
  simp [ResolutionTree.inputs, ClauseSequent.single, ClauseSequent.ofList,
    ClauseSequent.mapSet, GCNF.clauseWithLiteral_ofList, or_assoc, or_comm, or_left_comm, eq_comm]

helper theorem graph_toGCNF_display (g : FiniteGraph) (S : ClauseSequent)
    (hRef : g.IsRefutationFor S) (hOrd : S.isOrdinary) :
    proofDisplay (g.toGCNF S hRef hOrd) = (conversionDisplay (g.unfold hRef.1)).withRoot S := by
  simp only [FiniteGraph.toGCNF, proofDisplay_weakenTo, toGCNF_display_eq_conversionDisplay]

helper theorem proofDisplay_withRoot_self {S : ClauseSequent} (t : GCNFProofTree S) :
    (proofDisplay t).withRoot t.conclusion = proofDisplay t := by
  cases t <;> rfl

helper theorem ex437Tree2_display (Q : Nat) :
    conversionDisplay (ex437Tree2 Q) = proofDisplay (ex437T1 Q) := by
  simp [ex437Tree2, conversionDisplay, ex437T1, unitAxiom, proofDisplay,
    ResolutionTree.inputs, ClauseSequent.single, singleList, unionList, ClauseSequent.ofList]

proof_of ex437D2_toGCNF := by
  refine (graph_toGCNF_display _ _ _ _).trans ?_
  rw [ex437D2_unfold P Q hPQ, ex437Tree2_display, proofDisplay_withRoot_self]


proof_of ex437D4_toGCNF := by
  refine (graph_toGCNF_display _ _ _ _).trans ?_
  rw [ex437D4_unfold P Q hPQ, ex437Tree4_display P Q hPQ,
    proofDisplay_withRoot_self]


proof_of ex437D3_toGCNF := by
  refine (graph_toGCNF_display _ _ _ _).trans ?_
  rw [ex437D3_unfold P Q hPQ, ex437Tree3_display P Q hPQ,
    proofDisplay_withRoot_self]


proof_of ex437D_toGCNF := by
  refine (graph_toGCNF_display _ _ _ _).trans ?_
  rw [ex437D_unfold P Q hPQ, ex437Tree_display P Q hPQ,
    proofDisplay_withRoot_self]


proof_of ex438D2_toGCNF := by
  refine (graph_toGCNF_display _ _ _ _).trans ?_
  rw [ex438D2_unfold P Q R hPQ hQR, ex438Tree2_conversionDisplay P Q hPQ,
    proofDisplay_withRoot_self]


proof_of ex438D_toGCNF := by
  refine (graph_toGCNF_display _ _ _ _).trans ?_
  rw [ex438D_unfold P Q R hPQ hQR,
    ex438Tree_conversionDisplay P Q R hPQ hPR hQR, proofDisplay_withRoot_self]

end ReverseExamples

end LCS.Resolution.Method
