import LCS.Resolution.Method.Reverse
import Attach
import LCS.Resolution.Method.ReverseExamples.ProofsStamp

/-! # The worked reverse-conversion examples

The graph tables retain the vertex identities in the printed diagrams. The
letters are parameters. Proof trees exist for every substitution of letters;
where coincident letters change a printed resolvent, graph-validity lemmas state
exactly the required inequalities. The correspondence theorems execute
`FiniteGraph.toGCNF` and compare every displayed sequent and branch. The final
correspondence for Example 4.3.8 is stated for pairwise distinct letters.
-/

namespace LCS.Resolution.Method

open LCS.Resolution.GCNF

namespace ReverseExamples

/-- Example 4.3.7: the shared leaf at row 0 feeds both unit derivations. -/
@[blueprint "chap4__example_4_3_7" (main := true)]
def ex437D (P Q : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [Literal.pos P, Literal.pos Q], none⟩, ⟨Clause.ofList [Literal.pos P, Literal.neg Q], none⟩,
    ⟨Clause.ofList [Literal.neg P, Literal.pos Q], none⟩, ⟨Clause.ofList [Literal.neg P, Literal.neg Q], none⟩,
    ⟨Clause.ofList [Literal.pos P], some ⟨Literal.pos Q, 0, 1⟩⟩, ⟨Clause.ofList [Literal.pos Q], some ⟨Literal.pos P, 0, 2⟩⟩,
    ⟨Clause.ofList [Literal.neg P], some ⟨Literal.pos Q, 5, 3⟩⟩, ⟨Clause.ofList [], some ⟨Literal.pos P, 4, 6⟩⟩], 7⟩

/-- Descendants keep their original identifiers, including the common input 0. -/
@[blueprint "chap4__example_4_3_7"]
def ex437D1 (P Q : Nat) : FiniteGraph := (ex437D P Q).atRoot 4

@[blueprint "chap4__example_4_3_7"]
def ex437D2 (P Q : Nat) : FiniteGraph :=
  (ex437D1 P Q).mapLabels fun i C =>
    if i = 0 ∨ i = 1 ∨ i = 4 then C.remove (Literal.pos P) else C

/-- Pruning row 4 retains row 0 because row 5 also uses it. -/
@[blueprint "chap4__example_4_3_7"]
def ex437D3 (P Q : Nat) : FiniteGraph := (ex437D P Q).prune 4

@[blueprint "chap4__example_4_3_7"]
def ex437D4 (P Q : Nat) : FiniteGraph :=
  ((ex437D3 P Q).atRoot 6).mapLabels fun i C =>
    if i = 3 ∨ i = 6 then C.remove (Literal.neg P) else C

@[blueprint "chap4__example_4_3_7"]
def ex437D5 (P Q : Nat) : FiniteGraph := (ex437D4 P Q).atRoot 5

@[blueprint "chap4__example_4_3_7"]
def ex437D6 (P Q : Nat) : FiniteGraph :=
  (ex437D5 P Q).mapLabels fun i C =>
    if i = 0 ∨ i = 2 ∨ i = 5 then C.remove (Literal.pos Q) else C

/-- All six diagram transformations preserve explicit vertex identity. -/
@[blueprint "chap4__example_4_3_7"]
theorem ex437Graphs_counts (P Q : Nat) :
    (ex437D P Q).nodeCount = 8 ∧ (ex437D P Q).stepCount = 4 ∧
    (ex437D1 P Q).nodeCount = 3 ∧ (ex437D2 P Q).stepCount = 1 ∧
    (ex437D3 P Q).nodeCount = 7 ∧ (ex437D3 P Q).stepCount = 3 ∧
    (ex437D4 P Q).nodeCount = 5 ∧ (ex437D4 P Q).stepCount = 2 ∧
    (ex437D5 P Q).nodeCount = 3 ∧ (ex437D6 P Q).stepCount = 1 

@[blueprint "chap4__example_4_3_7"]
theorem ex437D_shared (P Q : Nat) :
    (ex437D P Q).follow [0, 0] = some 0 ∧
    (ex437D P Q).follow [1, 0, 0] = some 0 ∧
    (ex437D3 P Q).leafIds = [4, 0, 2, 3] 

/-- Example 4.3.8: four resolution steps, with five input clauses. -/
@[blueprint "chap4__example_4_3_8" (main := true)]
def ex438D (P Q R : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [Literal.pos P, Literal.pos Q], none⟩, ⟨Clause.ofList [Literal.neg P, Literal.pos R], none⟩, ⟨Clause.ofList [Literal.neg Q], none⟩,
    ⟨Clause.ofList [Literal.neg R, Literal.pos P], none⟩, ⟨Clause.ofList [Literal.neg P], none⟩,
    ⟨Clause.ofList [Literal.pos Q, Literal.pos R], some ⟨Literal.pos P, 0, 1⟩⟩, ⟨Clause.ofList [Literal.pos R], some ⟨Literal.pos Q, 5, 2⟩⟩,
    ⟨Clause.ofList [Literal.neg R], some ⟨Literal.pos P, 3, 4⟩⟩, ⟨Clause.ofList [], some ⟨Literal.pos R, 6, 7⟩⟩], 8⟩

@[blueprint "chap4__example_4_3_8"]
def ex438D1 (P Q R : Nat) : FiniteGraph := (ex438D P Q R).atRoot 6

@[blueprint "chap4__example_4_3_8"]
def ex438D2 (P Q R : Nat) : FiniteGraph :=
  (ex438D1 P Q R).mapLabels fun i C =>
    if i = 1 ∨ i = 5 ∨ i = 6 then C.remove (Literal.pos R) else C

@[blueprint "chap4__example_4_3_8"]
theorem ex438Graphs_counts (P Q R : Nat) :
    (ex438D P Q R).nodeCount = 9 ∧ (ex438D P Q R).stepCount = 4 ∧
    (ex438D1 P Q R).nodeCount = 5 ∧ (ex438D2 P Q R).stepCount = 2 



@[blueprint "chap4__example_4_3_7"]
theorem ex437D_wellFormed (P Q : Nat) (hPQ : P ≠ Q) : (ex437D P Q).WellFormed 

@[blueprint "chap4__example_4_3_7"]
theorem ex437D1_wellFormed (P Q : Nat) (hPQ : P ≠ Q) : (ex437D1 P Q).WellFormed 

@[blueprint "chap4__example_4_3_7"]
theorem ex437D2_wellFormed (P Q : Nat) (hPQ : P ≠ Q) : (ex437D2 P Q).WellFormed 

@[blueprint "chap4__example_4_3_7"]
theorem ex437D3_wellFormed (P Q : Nat) (hPQ : P ≠ Q) : (ex437D3 P Q).WellFormed 

@[blueprint "chap4__example_4_3_7"]
theorem ex437D4_wellFormed (P Q : Nat) (hPQ : P ≠ Q) : (ex437D4 P Q).WellFormed 

@[blueprint "chap4__example_4_3_7"]
theorem ex437D5_wellFormed (P Q : Nat) (hPQ : P ≠ Q) : (ex437D5 P Q).WellFormed 

@[blueprint "chap4__example_4_3_7"]
theorem ex437D6_wellFormed (P Q : Nat) (hPQ : P ≠ Q) : (ex437D6 P Q).WellFormed 

@[blueprint "chap4__example_4_3_8"]
theorem ex438D_wellFormed (P Q R : Nat) (hPQ : P ≠ Q) (hQR : Q ≠ R) : (ex438D P Q R).WellFormed 

@[blueprint "chap4__example_4_3_8"]
theorem ex438D1_wellFormed (P Q R : Nat) (hPQ : P ≠ Q) (hQR : Q ≠ R) : (ex438D1 P Q R).WellFormed 

@[blueprint "chap4__example_4_3_8"]
theorem ex438D2_wellFormed (P Q R : Nat) (hPQ : P ≠ Q) (hQR : Q ≠ R) : (ex438D2 P Q R).WellFormed 

@[blueprint "chap4__example_4_3_7"]
def unitAxiom (P : Nat) : GCNFProofTree (ClauseSequent.ofList [Clause.ofList [Literal.pos P], Clause.ofList [Literal.neg P]]) :=
  .axiom_ _
    (ClauseSequent.ordinary_ofList (by
      intro C hC
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl | rfl <;> exact Clause.ofList_cons_ordinary _ _))
    ⟨P, by simp [ClauseSequent.ofList, Clause.ofList_singleton_eq_single], by simp [ClauseSequent.ofList, Clause.ofList_singleton_eq_single]⟩

@[blueprint "chap4__example_4_3_7"]
def ex437T1 (Q : Nat) : GCNFProofTree (ClauseSequent.ofList [Clause.ofList [Literal.pos Q], Clause.ofList [Literal.neg Q]]) := unitAxiom Q

/-- The printed T₂ inference, with the two premises in the rule constructor's
canonical order (the source diagram places its unit-Q premise first). -/
@[blueprint "chap4__example_4_3_7"]
def ex437T2 (P Q : Nat) :
    GCNFProofTree (ClauseSequent.ofList [Clause.ofList [Literal.pos P, Literal.pos Q], Clause.ofList [Literal.neg P, Literal.pos Q], Clause.ofList [Literal.neg Q]]) := by
  let Gamma := ClauseSequent.ofList [Clause.ofList [Literal.neg Q]]
  let As := ClauseSequent.ofList [Clause.ofList [Literal.pos P], Clause.ofList [Literal.neg P]]
  let Gamma1 := ClauseSequent.ofList []
  let Gamma2 := ClauseSequent.ofList [Clause.ofList [Literal.neg Q]]
  refine (fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) ?_ (.rule Gamma As (Literal.pos Q) As Gamma1 Gamma2
    ?_ ?_ ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) ?_ (unitAxiom P)) ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) ?_ (unitAxiom Q)) ?_ ?_ ?_ ?_)
  · apply LCS.Finset.ext; intro C
    simp [Gamma, As, ClauseSequent.ofList, ClauseSequent.mapSet, GCNF.clauseWithLiteral_ofList,
      or_assoc, or_comm, or_left_comm, eq_comm]
  · exact ClauseSequent.ordinary_ofList (by simp)
  · exact ClauseSequent.ordinary_ofList (by simp)
  · apply LCS.Finset.ext; intro C; simp [Gamma1, As, ClauseSequent.ofList]
  · apply LCS.Finset.ext; intro C
    simp [Gamma2, ClauseSequent.ofList, ClauseSequent.single, Clause.ofList_singleton_eq_single, or_comm]
  · exact ⟨Clause.ofList [Literal.pos P], by simp [As, ClauseSequent.ofList]⟩
  · exact fun _ h => h
  · intro C hC; simp [Gamma1, ClauseSequent.ofList] at hC
  · intro C hC; exact LCS.Finset.mem_union.mpr (Or.inl hC)

@[blueprint "chap4__example_4_3_7"]
def ex437T3 (P Q : Nat) :
    GCNFProofTree (ClauseSequent.ofList [Clause.ofList [Literal.pos P], Clause.ofList [Literal.pos P, Literal.pos Q],
      Clause.ofList [Literal.neg P, Literal.pos Q], Clause.ofList [Literal.neg P, Literal.neg Q]]) := by
  let Gamma := ClauseSequent.ofList [Clause.ofList [Literal.pos P], Clause.ofList [Literal.pos P, Literal.pos Q], Clause.ofList [Literal.neg P, Literal.pos Q]]
  let As := ClauseSequent.ofList [Clause.ofList [Literal.neg Q]]
  let Gamma1 := ClauseSequent.ofList [Clause.ofList [Literal.pos P, Literal.pos Q], Clause.ofList [Literal.neg P, Literal.pos Q]]
  let Gamma2 := ClauseSequent.ofList [Clause.ofList [Literal.pos P]]
  refine (fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) ?_ (.rule Gamma As (Literal.neg P) As Gamma1 Gamma2
    ?_ ?_ ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) ?_ (ex437T2 P Q)) ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) ?_ (unitAxiom P)) ?_ ?_ ?_ ?_)
  · apply LCS.Finset.ext; intro C
    have hSwap : Clause.ofList [Literal.neg Q, Literal.neg P] = Clause.ofList [Literal.neg P, Literal.neg Q] := by
      apply LCS.Finset.ext; intro L; simp [Clause.ofList, or_comm]
    simp [Gamma, As, ClauseSequent.ofList, ClauseSequent.mapSet, GCNF.clauseWithLiteral_ofList,
      hSwap, or_assoc, eq_comm]
  · exact ClauseSequent.ordinary_ofList (by simp)
  · exact ClauseSequent.ordinary_ofList (by simp)
  · apply LCS.Finset.ext; intro C; simp [Gamma1, As, ClauseSequent.ofList, or_assoc]
  · apply LCS.Finset.ext; intro C; simp [Gamma2, ClauseSequent.ofList, ClauseSequent.single, Clause.ofList_singleton_eq_single]
  · exact ⟨Clause.ofList [Literal.neg Q], by simp [As, ClauseSequent.ofList]⟩
  · exact fun _ h => h
  · intro C hC
    apply LCS.Finset.mem_union.mpr; apply Or.inl
    simp [Gamma1, Gamma, ClauseSequent.ofList] at hC ⊢
    exact Or.inr hC
  · intro C hC
    apply LCS.Finset.mem_union.mpr; apply Or.inl
    simp [Gamma2, Gamma, ClauseSequent.ofList] at hC ⊢
    exact Or.inl hC

@[blueprint "chap4__example_4_3_7"]
def ex437T4 (P Q : Nat) :
    GCNFProofTree (ClauseSequent.ofList [Clause.ofList [Literal.pos P, Literal.pos Q], Clause.ofList [Literal.pos P, Literal.neg Q],
      Clause.ofList [Literal.neg P, Literal.pos Q], Clause.ofList [Literal.neg P, Literal.neg Q]]) := by
  let Gamma := ClauseSequent.ofList [Clause.ofList [Literal.neg P, Literal.pos Q], Clause.ofList [Literal.neg P, Literal.neg Q]]
  let As := ClauseSequent.ofList [Clause.ofList [Literal.pos Q], Clause.ofList [Literal.neg Q]]
  let Gamma1 := ClauseSequent.ofList []
  let Gamma2 := ClauseSequent.ofList [Clause.ofList [Literal.pos P, Literal.pos Q], Clause.ofList [Literal.neg P, Literal.pos Q], Clause.ofList [Literal.neg P, Literal.neg Q]]
  refine (fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) ?_ (.rule Gamma As (Literal.pos P) As Gamma1 Gamma2
    ?_ ?_ ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) ?_ (unitAxiom Q)) ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) ?_ (ex437T3 P Q)) ?_ ?_ ?_ ?_)
  · apply LCS.Finset.ext; intro C
    have hSwap (L : Literal) : Clause.ofList [L, Literal.pos P] = Clause.ofList [Literal.pos P, L] := by
      apply LCS.Finset.ext; intro l; simp [Clause.ofList, or_comm]
    simp [Gamma, As, ClauseSequent.ofList, ClauseSequent.mapSet, GCNF.clauseWithLiteral_ofList,
      hSwap, or_assoc, or_comm, or_left_comm, eq_comm]
  · exact ClauseSequent.ordinary_ofList (by simp)
  · exact ClauseSequent.ordinary_ofList (by simp)
  · apply LCS.Finset.ext; intro C; simp [Gamma1, As, ClauseSequent.ofList]
  · apply LCS.Finset.ext; intro C
    simp [Gamma2, ClauseSequent.ofList, ClauseSequent.single, Clause.ofList_singleton_eq_single,
      or_assoc, or_comm, or_left_comm]
  · exact ⟨Clause.ofList [Literal.pos Q], by simp [As, ClauseSequent.ofList]⟩
  · exact fun _ h => h
  · intro C hC; simp [Gamma1, ClauseSequent.ofList] at hC
  · intro C hC
    simp only [Gamma2, ClauseSequent.ofList, LCS.Finset.mem_ofList, List.mem_cons,
      List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl
    · apply LCS.Finset.mem_union.mpr; apply Or.inr
      apply LCS.Finset.mem_image.mpr
      refine ⟨Clause.ofList [Literal.pos Q], by simp [As, ClauseSequent.ofList], ?_⟩
      rw [Clause.ofList_singleton_eq_single, clauseWithLiteral_single]
      apply LCS.Finset.ext; intro L; simp [Clause.ofList, or_comm]
    · apply LCS.Finset.mem_union.mpr; apply Or.inl; simp [Gamma, ClauseSequent.ofList]
    · apply LCS.Finset.mem_union.mpr; apply Or.inl; simp [Gamma, ClauseSequent.ofList]

/-- The recursive proof obtained from D₂ in Example 4.3.8. -/
@[blueprint "chap4__example_4_3_8"]
def ex438T1 (P Q : Nat) :
    GCNFProofTree (ClauseSequent.ofList [Clause.ofList [Literal.pos P, Literal.pos Q], Clause.ofList [Literal.neg P], Clause.ofList [Literal.neg Q]]) := by
  let Gamma := ClauseSequent.ofList [Clause.ofList [Literal.neg P], Clause.ofList [Literal.neg Q]]
  let As := ClauseSequent.ofList [Clause.ofList [Literal.pos P]]
  let Gamma1 := ClauseSequent.ofList [Clause.ofList [Literal.neg P]]
  let Gamma2 := ClauseSequent.ofList [Clause.ofList [Literal.neg Q]]
  refine (fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) ?_ (.rule Gamma As (Literal.pos Q) As Gamma1 Gamma2
    ?_ ?_ ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) ?_ (unitAxiom P)) ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) ?_ (unitAxiom Q)) ?_ ?_ ?_ ?_)
  · apply LCS.Finset.ext; intro C
    simp [Gamma, As, ClauseSequent.ofList, ClauseSequent.mapSet, GCNF.clauseWithLiteral_ofList,
      or_assoc, or_comm, or_left_comm, eq_comm]
  · exact ClauseSequent.ordinary_ofList (by simp)
  · exact ClauseSequent.ordinary_ofList (by simp)
  · apply LCS.Finset.ext; intro C; simp [Gamma1, As, ClauseSequent.ofList, or_comm]
  · apply LCS.Finset.ext; intro C
    simp [Gamma2, ClauseSequent.ofList, ClauseSequent.single, Clause.ofList_singleton_eq_single, or_comm]
  · exact ⟨Clause.ofList [Literal.pos P], by simp [As, ClauseSequent.ofList]⟩
  · exact fun _ h => h
  · intro C hC
    apply LCS.Finset.mem_union.mpr; apply Or.inl
    simp [Gamma1, Gamma, ClauseSequent.ofList] at hC ⊢
    exact Or.inl hC
  · intro C hC
    apply LCS.Finset.mem_union.mpr; apply Or.inl
    simp [Gamma2, Gamma, ClauseSequent.ofList] at hC ⊢
    exact Or.inr hC

/-- The final inference retains both extra clauses as weakening context. -/
@[blueprint "chap4__example_4_3_8"]
def ex438T2 (P Q R : Nat) :
    GCNFProofTree (ClauseSequent.ofList [Clause.ofList [Literal.pos P, Literal.pos Q], Clause.ofList [Literal.neg P, Literal.pos R],
      Clause.ofList [Literal.neg Q], Clause.ofList [Literal.neg R, Literal.pos P], Clause.ofList [Literal.neg P]]) := by
  let Gamma := ClauseSequent.ofList [Clause.ofList [Literal.neg P, Literal.pos R], Clause.ofList [Literal.neg Q], Clause.ofList [Literal.neg R, Literal.pos P], Clause.ofList [Literal.neg P]]
  let As := ClauseSequent.ofList [Clause.ofList [Literal.pos P]]
  let Gamma1 := ClauseSequent.ofList [Clause.ofList [Literal.neg P]]
  let Gamma2 := ClauseSequent.ofList [Clause.ofList [Literal.neg Q]]
  refine (fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) ?_ (.rule Gamma As (Literal.pos Q) As Gamma1 Gamma2
    ?_ ?_ ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) ?_ (unitAxiom P)) ((fun {S T : ClauseSequent} (h : S = T) (t : GCNFProofTree S) => (h ▸ t : GCNFProofTree T)) ?_ (unitAxiom Q)) ?_ ?_ ?_ ?_)
  · apply LCS.Finset.ext; intro C
    simp [Gamma, As, ClauseSequent.ofList, ClauseSequent.mapSet, GCNF.clauseWithLiteral_ofList,
      or_assoc, or_comm, or_left_comm, eq_comm]
  · exact ClauseSequent.ordinary_ofList (by simp)
  · exact ClauseSequent.ordinary_ofList (by simp)
  · apply LCS.Finset.ext; intro C; simp [Gamma1, As, ClauseSequent.ofList, or_comm]
  · apply LCS.Finset.ext; intro C
    simp [Gamma2, ClauseSequent.ofList, ClauseSequent.single, Clause.ofList_singleton_eq_single, or_comm]
  · exact ⟨Clause.ofList [Literal.pos P], by simp [As, ClauseSequent.ofList]⟩
  · exact fun _ h => h
  · intro C hC
    apply LCS.Finset.mem_union.mpr; apply Or.inl
    simp [Gamma1, Gamma, ClauseSequent.ofList] at hC ⊢
    exact Or.inr (Or.inr (Or.inr hC))
  · intro C hC
    apply LCS.Finset.mem_union.mpr; apply Or.inl
    simp [Gamma2, Gamma, ClauseSequent.ofList] at hC ⊢
    exact Or.inr (Or.inl hC)

@[blueprint "chap4__example_4_3_7"]
theorem ex437Trees_counts (P Q : Nat) :
    (ex437T1 Q).leafCount = 1 ∧ (ex437T2 P Q).leafCount = 2 ∧
    (ex437T3 P Q).leafCount = 3 ∧ (ex437T4 P Q).leafCount = 4 ∧
    (ex437T4 P Q).nodeCount = 7 ∧
    (ex437T4 P Q).leafCount = (ex437D P Q).stepCount 

@[blueprint "chap4__example_4_3_8"]
theorem ex438Trees_fewer_leaves (P Q R : Nat) :
    (ex438T1 P Q).leafCount = 2 ∧ (ex438T2 P Q R).leafCount = 2 ∧
    (ex438T2 P Q R).nodeCount = 3 ∧
    (ex438T2 P Q R).leafCount < (ex438D P Q R).stepCount 

/-- Forget rule witnesses while preserving every sequent and branch. -/
@[blueprint "chap4__example_4_3_7"]
inductive ProofDisplay where
  | leaf : ClauseSequent → ProofDisplay
  | fork : ClauseSequent → ProofDisplay → ProofDisplay → ProofDisplay
  deriving DecidableEq

@[blueprint "chap4__example_4_3_7"]
def proofDisplay : {S : ClauseSequent} → GCNFProofTree S → ProofDisplay
  | S, .axiom_ _ _ _ => .leaf S
  | _, .rule Gamma As B _ _ _ _ _ left right _ _ _ _ =>
      .fork (LCS.Finset.union Gamma (As.mapSet (fun A => clauseWithLiteral A B)))
        (proofDisplay left) (proofDisplay right)



/-- A sequent-labeled DAG with explicit vertex identities. -/
@[blueprint "chap4__example_4_3_7"]
structure ProofDag where
  table : List (ClauseSequent × Option (Nat × Nat))
  root : Nat

@[blueprint "chap4__example_4_3_7"]
def ProofDag.unfoldAt (g : ProofDag) : Nat → Nat → Option ProofDisplay
  | 0, _ => none
  | depth + 1, i => do
      let (S, children) ← g.table[i]?
      match children with
      | none => some (.leaf S)
      | some (left, right) =>
          return .fork S (← g.unfoldAt depth left) (← g.unfoldAt depth right)

/-- The repeated Q-axiom is row 1; the repeated P-axiom is row 0. -/
@[blueprint "chap4__example_4_3_7"]
def ex437ProofDag (P Q : Nat) : ProofDag :=
  ⟨[(ClauseSequent.ofList [Clause.ofList [Literal.pos P], Clause.ofList [Literal.neg P]], none),
    (ClauseSequent.ofList [Clause.ofList [Literal.pos Q], Clause.ofList [Literal.neg Q]], none),
    ((ex437T2 P Q).conclusion, some (0, 1)),
    ((ex437T3 P Q).conclusion, some (2, 0)),
    ((ex437T4 P Q).conclusion, some (1, 3))], 4⟩

@[blueprint "chap4__example_4_3_7"]
theorem ex437ProofDag_five_vertices (P Q : Nat) :
    (ex437ProofDag P Q).table.length = 5 ∧
    (ex437T4 P Q).nodeCount = 7 ∧ (ex437D P Q).nodeCount = 8 

/-- Unfolding the five actual vertices gives the seven-node proof tree. -/
@[blueprint "chap4__example_4_3_7"]
theorem ex437ProofDag_unfolds (P Q : Nat) :
    (ex437ProofDag P Q).unfoldAt 5 4 = some (proofDisplay (ex437T4 P Q)) 

/-- The original D refutes exactly the antecedent of T₄. -/
@[blueprint "chap4__example_4_3_7"]
theorem ex437D_refutes (P Q : Nat) (hPQ : P ≠ Q) :
    (ex437D P Q).IsRefutationFor (ex437T4 P Q).conclusion 

@[blueprint "chap4__example_4_3_8"]
theorem ex438D_refutes (P Q R : Nat) (hPQ : P ≠ Q) (hQR : Q ≠ R) :
    (ex438D P Q R).IsRefutationFor (ex438T2 P Q R).conclusion 



































-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Replace only the displayed conclusion; retain the premise displays. -/
def ProofDisplay.withRoot (S : ClauseSequent) : ProofDisplay → ProofDisplay
  | .leaf _ => .leaf S
  | .fork _ left right => .fork S left right





open ResolutionTree

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The display operation follows exactly the weakening and inference choices
of the constructive reverse conversion. -/
def combineConversionDisplays (A : ResolutionTree) (L : Literal)
    (S : ClauseSequent) (first second : ProofDisplay) : ProofDisplay :=
  if GCNF.Clause.single L ∈ S then second.withRoot S
  else if newInputs (A.eraseLiteral L) S = LCS.Finset.empty then first.withRoot S
  else .fork S first second

-- ATTACH-BLOCKER: termination suffix
def conversionDisplay (T : ResolutionTree) : ProofDisplay :=
  match T with
  | .axiom_ _ => .leaf T.inputs
  | .resolve (.axiom_ _) (.axiom_ _) _ => .leaf T.inputs
  | .resolve (.axiom_ C) (.resolve B₁ B₂ P) L =>
      combineConversionDisplays (.resolve B₁ B₂ P) L.conjugate T.inputs
        (conversionDisplay ((resolve B₁ B₂ P).eraseLiteral L.conjugate))
        (conversionDisplay (.resolve (.axiom_ (GCNF.Clause.single L.conjugate))
          (.axiom_ C) L.conjugate))
  | .resolve (.resolve A₁ A₂ P) B L =>
      combineConversionDisplays (.resolve A₁ A₂ P) L T.inputs
        (conversionDisplay ((resolve A₁ A₂ P).eraseLiteral L))
        (conversionDisplay (.resolve (.axiom_ (GCNF.Clause.single L)) B L))
termination_by T.treeStepCount
decreasing_by
  all_goals first
    | (simp only [treeStepCount]; omega)
    | (apply Nat.lt_of_le_of_lt (eraseLiteral_treeStepCount_le _ _)
       simp only [treeStepCount]; omega)



































@[blueprint "chap4__example_4_3_7"]
theorem ex437D2_refutes (P Q : Nat) (hPQ : P ≠ Q) :
    (ex437D2 P Q).IsRefutationFor (ex437T1 Q).conclusion 

@[blueprint "chap4__example_4_3_7"]
theorem ex437D3_refutes (P Q : Nat) (hPQ : P ≠ Q) :
    (ex437D3 P Q).IsRefutationFor (ex437T3 P Q).conclusion 

@[blueprint "chap4__example_4_3_7"]
theorem ex437D4_refutes (P Q : Nat) (hPQ : P ≠ Q) :
    (ex437D4 P Q).IsRefutationFor (ex437T2 P Q).conclusion 

@[blueprint "chap4__example_4_3_8"]
theorem ex438D2_refutes (P Q R : Nat) (hPQ : P ≠ Q) (hQR : Q ≠ R) :
    (ex438D2 P Q R).IsRefutationFor (ex438T1 P Q).conclusion 











/-- Executing the graph converter on D₂ gives exactly the printed axiom T₁. -/
@[blueprint "chap4__example_4_3_7"]
theorem ex437D2_toGCNF (P Q : Nat) (hPQ : P ≠ Q) :
    proofDisplay ((ex437D2 P Q).toGCNF (ex437T1 Q).conclusion
      (ex437D2_refutes P Q hPQ) (ex437T1 Q).ordinary) = proofDisplay (ex437T1 Q) 

/-- Executing the graph converter on D₄ gives T₂ in the rule's premise order. -/
@[blueprint "chap4__example_4_3_7"]
theorem ex437D4_toGCNF (P Q : Nat) (hPQ : P ≠ Q) :
    proofDisplay ((ex437D4 P Q).toGCNF (ex437T2 P Q).conclusion
      (ex437D4_refutes P Q hPQ) (ex437T2 P Q).ordinary) = proofDisplay (ex437T2 P Q) 

@[blueprint "chap4__example_4_3_7"]
theorem ex437D3_toGCNF (P Q : Nat) (hPQ : P ≠ Q) :
    proofDisplay ((ex437D3 P Q).toGCNF (ex437T3 P Q).conclusion
      (ex437D3_refutes P Q hPQ) (ex437T3 P Q).ordinary) = proofDisplay (ex437T3 P Q) 

/-- The actual converter preserves every displayed sequent and premise of T₄. -/
@[blueprint "chap4__example_4_3_7"]
theorem ex437D_toGCNF (P Q : Nat) (hPQ : P ≠ Q) :
    proofDisplay ((ex437D P Q).toGCNF (ex437T4 P Q).conclusion
      (ex437D_refutes P Q hPQ) (ex437T4 P Q).ordinary) = proofDisplay (ex437T4 P Q) 

@[blueprint "chap4__example_4_3_8"]
theorem ex438D2_toGCNF (P Q R : Nat) (hPQ : P ≠ Q) (hQR : Q ≠ R) :
    proofDisplay ((ex438D2 P Q R).toGCNF (ex438T1 P Q).conclusion
      (ex438D2_refutes P Q R hPQ hQR) (ex438T1 P Q).ordinary) = proofDisplay (ex438T1 P Q) 

/-- For distinct schematic letters, the converter returns the printed T₂,
including the weakening that changes only its final sequent. -/
@[blueprint "chap4__example_4_3_8"]
theorem ex438D_toGCNF (P Q R : Nat) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    proofDisplay ((ex438D P Q R).toGCNF (ex438T2 P Q R).conclusion
      (ex438D_refutes P Q R hPQ hQR) (ex438T2 P Q R).ordinary) = proofDisplay (ex438T2 P Q R) 

/-- The five-vertex display DAG unfolds to the converter's actual output. -/
@[blueprint "chap4__example_4_3_7"]
theorem ex437ProofDag_unfolds_conversion (P Q : Nat) (hPQ : P ≠ Q) :
    (ex437ProofDag P Q).unfoldAt 5 4 = some
      (proofDisplay ((ex437D P Q).toGCNF (ex437T4 P Q).conclusion
        (ex437D_refutes P Q hPQ) (ex437T4 P Q).ordinary)) 

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Count axiom occurrences in a fully labeled proof display. -/
def ProofDisplay.leafCount : ProofDisplay → Nat
  | .leaf _ => 1
  | .fork _ left right => left.leafCount + right.leafCount

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
def ProofDisplay.nodeCount : ProofDisplay → Nat
  | .leaf _ => 1
  | .fork _ left right => 1 + left.nodeCount + right.nodeCount





/-- Four axiom occurrences and seven vertices belong to the actual output tree. -/
@[blueprint "chap4__example_4_3_7"]
theorem ex437Conversion_counts (P Q : Nat) (hPQ : P ≠ Q) :
    let T := (ex437D P Q).toGCNF (ex437T4 P Q).conclusion
      (ex437D_refutes P Q hPQ) (ex437T4 P Q).ordinary
    T.leafCount = 4 ∧ T.nodeCount = 7 ∧ T.leafCount = (ex437D P Q).stepCount 

/-- The actual output has two axioms, strictly fewer than D's four steps. -/
@[blueprint "chap4__example_4_3_8"]
theorem ex438Conversion_fewer_leaves (P Q R : Nat)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    let T := (ex438D P Q R).toGCNF (ex438T2 P Q R).conclusion
      (ex438D_refutes P Q R hPQ hQR) (ex438T2 P Q R).ordinary
    T.leafCount = 2 ∧ T.nodeCount = 3 ∧ T.leafCount < (ex438D P Q R).stepCount 

end ReverseExamples
end LCS.Resolution.Method
