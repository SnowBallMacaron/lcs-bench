import LCS.Item
import LCS.Util
import LCS.Resolution.GCNF
import Attach
import LCS.SLD.SLDForm.ProofsStamp

/-! # SLD.SLDForm
    Formalization of Chapter 9, Section 9.2.
    Horn clauses, definite clauses, and GCNF'-proofs in SLD-form.
    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.SLD.SLDForm

open LCS.Resolution.GCNF

-- ========= Definition 9.2.1: Horn clauses and related predicates =========

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Polarity kernel on the resolution carrier, including the empty clause. -/
def atMostOnePositive (C : Clause) : Prop :=
  ∀ P Q, Literal.pos P ∈ C → Literal.pos Q ∈ C → P = Q

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- All-negative resolution clauses, including the empty final goal. -/
@[blueprint "chap9__definition_9_2_1"]
def allNegative (C : Clause) : Prop :=
  ∀ l ∈ C, match l with | Literal.neg _ => True | _ => False

/-- Definition 9.2.1: An ordinary (nonempty) clause is Horn iff it contains
    at most one positive literal. -/
@[blueprint "chap9__definition_9_2_1" (main := true)]
def isHornClause (C : Clause) : Prop :=
  C.isOrdinary ∧ atMostOnePositive C

/-- Definition 9.2.1: A Horn clause that contains a (single) positive
    literal is a definite clause. -/
@[blueprint "chap9__definition_9_2_1" (main := true)]
def isDefiniteClause (C : Clause) : Prop :=
  isHornClause C ∧
  ∃ P, Literal.pos P ∈ C

/-- Definition 9.2.1: A Horn clause of the form {neg P_1,...,neg P_m} (containing only
    negative literals, no positive literal) is called a negative clause or goal clause.
    The ordinary §9.2 domain excludes the empty resolution goal. -/
@[blueprint "chap9__definition_9_2_1" (main := true)]
def isGoalClause (C : Clause) : Prop :=
  isHornClause C ∧ allNegative C

/-- Definition 9.2.2 (companion): the cancellation node has exactly the
    complementary singleton pair for P as its label. Ordinary axiom labels
    elsewhere may have side context, independently of the tree constructor. -/
@[blueprint "chap9__definition_9_2_2"]
def isAxiomNodeWith (P : Nat) : {S : ClauseSequent} → GCNFProofTree S → Prop
  | S, _ => S = pairSet P

/-- Definition 9.2.2 (companion): finite equality test for the exact
    complementary-pair cancellation label. -/
@[blueprint "chap9__definition_9_2_2"]
def isAxiomNodeWithB (P : Nat) : {S : ClauseSequent} → GCNFProofTree S → Bool
  | S, _ => decide (S = pairSet P)



-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Helper: isAxiomNodeWithB soundness. -/
theorem isAxiomNodeWithB_sound (P : Nat) :
    {S : ClauseSequent} → (T : GCNFProofTree S) →
    isAxiomNodeWithB P T = true → isAxiomNodeWith P T
  | _, _, h => by
    simpa only [isAxiomNodeWithB, isAxiomNodeWith, decide_eq_true_eq] using h

/-- Definition 9.2.2 (companion): a literal is negative. -/
@[blueprint "chap9__definition_9_2_2"]
def isNegLit : Literal → Prop
  | .neg _ => True
  | .pos _ => False

/-- Definition 9.2.2 (companion): an exposed singleton-goal branch of the
    compressed binary goal expansion has exactly {neg Q} as its goal clause.
    A trivial label is exempt from the local split condition even at a rule
    constructor. Recursive SLD conditions are checked by isSLDForm. -/
@[blueprint "chap9__definition_9_2_2"]
def isSLDForm_goalSplit (Q : Nat) : {S : ClauseSequent} → GCNFProofTree S → Prop
  | S, T =>
    Clause.single (Literal.neg Q) ∈ S ∧
    (∀ C ∈ S, isGoalClause C → C = Clause.single (Literal.neg Q)) ∧
    (S.isTrivial ∨
      match T with
      | .axiom_ _ _ _ => True
      | .rule _ _ B' _ _ _ _ _ _ innerRight _ _ _ _ =>
        B' = Literal.pos Q ∧ isAxiomNodeWith Q innerRight)

/-- Definition 9.2.2: SLD form on a GCNF' proof with one ordinary goal.
    Every child is checked recursively. At a node with an axiom label the local
    split condition is exempt, including when that node has a rule constructor.

    A positive split cancels the selected singleton goal against its matching
    head at an exact complementary-pair label. The continuation drops the old
    goal from its context and has the nonempty negative body as its unique goal;
    that body may itself contain the selected negative literal.

    A negative split expands a nonsingleton goal as a binary chain. Its left
    branch has the proper negative remainder as its unique goal, and its right
    branch has exactly the selected negative singleton as its goal. The exposed
    singleton branches give the compressed observation; primitive rules and
    edge depth remain those of GCNF'. -/
@[blueprint "chap9__definition_9_2_2" (main := true)]
def isSLDForm : {S : ClauseSequent} → GCNFProofTree S → Prop
  | _, .axiom_ _ _ _ => True
  | _, .rule Gamma As B Cs Gamma1 _ _ _ leftTree rightTree _hNe _hSub _ _ =>
    isSLDForm leftTree ∧ isSLDForm rightTree ∧
    (ClauseSequent.isTrivial (LCS.Finset.union Gamma (ClauseSequent.mapSet As
        (fun A => clauseWithLiteral A B))) ∨
      match B with
      | Literal.pos P =>
        (∀ C ∈ Cs, ∀ l ∈ C, isNegLit l) ∧
        isAxiomNodeWith P rightTree ∧
        Clause.single (Literal.neg P) ∈ Gamma ∧
        Clause.single (Literal.neg P) ∉ Gamma1 ∧
        (∃ G, G ∈ Cs ∧ isGoalClause G ∧
          ∀ C, C ∈ LCS.Finset.union Gamma1 Cs → isGoalClause C → C = G)
      | Literal.neg Q =>
        isSLDForm_goalSplit Q rightTree ∧
        (∀ C ∈ Cs, ∀ l ∈ C, isNegLit l) ∧
        (∃ G, G ∈ Cs ∧ isGoalClause G ∧ Literal.neg Q ∉ G ∧
          ∀ C, C ∈ LCS.Finset.union Gamma1 Cs → isGoalClause C → C = G))

-- ========= Example 9.2.1: Horn clause set and SLD-form proof =========

/-- Example 9.2.1: The concrete set S = {{P_3}, {P_4}, {neg P_1, neg P_2}, {neg P_3,
    neg P_4, P_1}, {neg P_3, P_2}} using Nat-indexed propositional symbols (P_i = i). -/
@[blueprint "chap9__example_9_2_1" (main := true)]
def exHornClauseSet : List Clause :=
  [Clause.ofList [Literal.pos 3],
   Clause.ofList [Literal.pos 4],
   Clause.ofList [Literal.neg 1, Literal.neg 2],
   Clause.ofList [Literal.neg 3, Literal.neg 4, Literal.pos 1],
   Clause.ofList [Literal.neg 3, Literal.pos 2]]

/-- Example 9.2.1 (companion): The goal clause {neg P_1, neg P_2}. -/
@[blueprint "chap9__example_9_2_1"]
def exGoalClause : Clause :=
  Clause.ofList [Literal.neg 1, Literal.neg 2]

/-- Example 9.2.1: The first printed proof (PDF p.396), with its displayed
    premise order. Its root splits the definite clause with head P₁;
    the two P₃/¬P₃ axiom leaves remain separate occurrences. -/
@[blueprint "chap9__example_9_2_1"]
def exFirstGCNFProof : GCNFProofTree (ClauseSequent.ofList exHornClauseSet) := by
  let p := fun i => Clause.single (Literal.pos i)
  let n := fun i => Clause.single (Literal.neg i)
  let body := Clause.ofList [Literal.neg 3, Literal.neg 4]
  let rule2 := Clause.ofList [Literal.neg 3, Literal.pos 2]
  let L := ClauseSequent.ofList [p 3, p 4, body]
  let RR := ClauseSequent.ofList [p 3, n 2, rule2]
  let R := ClauseSequent.ofList [p 3, exGoalClause, p 1, rule2]
  let left : GCNFProofTree L := by
    let G := ClauseSequent.ofList [p 3, p 4]
    let A := ClauseSequent.single (n 3)
    let G1 := ClauseSequent.ofList [p 3]
    let G2 := ClauseSequent.ofList [p 4]
    have hRoot : LCS.Finset.union G (ClauseSequent.mapSet A
        (fun C => clauseWithLiteral C (Literal.neg 4))) = L := by native_decide
    rw [← hRoot]
    refine GCNFProofTree.rule G A (Literal.neg 4) A G1 G2 ?_ ?_ ?_ ?_
      ⟨n 3, by native_decide⟩ (fun _ h => h) ?_ ?_
    · simp [ClauseSequent.isOrdinary, Clause.isOrdinary, G,
        ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
        LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
    · simp [ClauseSequent.isOrdinary, Clause.isOrdinary, A,
        ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
        LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
    · refine GCNFProofTree.axiom_ _ ?_ ⟨3, by native_decide, by native_decide⟩
      simp [ClauseSequent.isOrdinary, Clause.isOrdinary, G1, A,
        ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
        LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
    · refine GCNFProofTree.axiom_ _ ?_ ⟨4, by native_decide, by native_decide⟩
      simp [ClauseSequent.isOrdinary, Clause.isOrdinary, G2, A,
        ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
        LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
    · simp [LCS.Finset.Subset, G1, ClauseSequent.ofList,
        LCS.Finset.mem_ofList, or_imp, forall_and] <;> native_decide
    · simp [LCS.Finset.Subset, G2, ClauseSequent.ofList,
        LCS.Finset.mem_ofList, or_imp, forall_and] <;> native_decide
  let rightRight : GCNFProofTree RR := by
    let G := ClauseSequent.ofList [p 3, n 2]
    let A := ClauseSequent.single (p 2)
    let G1 := ClauseSequent.ofList [n 2]
    let G2 := ClauseSequent.ofList [p 3]
    have hRoot : LCS.Finset.union G (ClauseSequent.mapSet A
        (fun C => clauseWithLiteral C (Literal.neg 3))) = RR := by native_decide
    rw [← hRoot]
    refine GCNFProofTree.rule G A (Literal.neg 3) A G1 G2 ?_ ?_ ?_ ?_
      ⟨p 2, by native_decide⟩ (fun _ h => h) ?_ ?_
    · simp [ClauseSequent.isOrdinary, Clause.isOrdinary, G,
        ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
        LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
    · simp [ClauseSequent.isOrdinary, Clause.isOrdinary, A,
        ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
        LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
    · refine GCNFProofTree.axiom_ _ ?_ ⟨2, by native_decide, by native_decide⟩
      simp [ClauseSequent.isOrdinary, Clause.isOrdinary, G1, A,
        ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
        LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
    · refine GCNFProofTree.axiom_ _ ?_ ⟨3, by native_decide, by native_decide⟩
      simp [ClauseSequent.isOrdinary, Clause.isOrdinary, G2, A,
        ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
        LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
    · simp [LCS.Finset.Subset, G1, ClauseSequent.ofList,
        LCS.Finset.mem_ofList, or_imp, forall_and] <;> native_decide
    · simp [LCS.Finset.Subset, G2, ClauseSequent.ofList,
        LCS.Finset.mem_ofList, or_imp, forall_and] <;> native_decide
  let right : GCNFProofTree R := by
    let G := ClauseSequent.ofList [p 3, p 1, rule2]
    let A := ClauseSequent.single (n 1)
    let G1 := ClauseSequent.ofList [p 1]
    let G2 := ClauseSequent.ofList [p 3, rule2]
    have hRoot : LCS.Finset.union G (ClauseSequent.mapSet A
        (fun C => clauseWithLiteral C (Literal.neg 2))) = R := by native_decide
    rw [← hRoot]
    refine GCNFProofTree.rule G A (Literal.neg 2) A G1 G2 ?_ ?_ ?_ ?_
      ⟨n 1, by native_decide⟩ (fun _ h => h) ?_ ?_
    · simp [ClauseSequent.isOrdinary, Clause.isOrdinary, G,
        ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
        LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
    · simp [ClauseSequent.isOrdinary, Clause.isOrdinary, A,
        ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
        LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
    · refine GCNFProofTree.axiom_ _ ?_ ⟨1, by native_decide, by native_decide⟩
      simp [ClauseSequent.isOrdinary, Clause.isOrdinary, G1, A,
        ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
        LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
    · have h : LCS.Finset.union G2 (ClauseSequent.single
          (Clause.single (Literal.neg 2))) = RR := by native_decide
      exact h.symm ▸ rightRight
    · simp [LCS.Finset.Subset, G1, ClauseSequent.ofList,
        LCS.Finset.mem_ofList, or_imp, forall_and] <;> native_decide
    · simp [LCS.Finset.Subset, G2, ClauseSequent.ofList,
        LCS.Finset.mem_ofList, or_imp, forall_and] <;> native_decide
  let G := ClauseSequent.ofList [p 3, p 4, exGoalClause, rule2]
  let A := ClauseSequent.single body
  let G1 := ClauseSequent.ofList [p 3, p 4]
  let G2 := ClauseSequent.ofList [p 3, exGoalClause, rule2]
  have hRoot : LCS.Finset.union G (ClauseSequent.mapSet A
      (fun C => clauseWithLiteral C (Literal.pos 1))) =
      ClauseSequent.ofList exHornClauseSet := by native_decide
  rw [← hRoot]
  refine GCNFProofTree.rule G A (Literal.pos 1) A G1 G2 ?_ ?_ ?_ ?_
    ⟨body, by native_decide⟩ (fun _ h => h) ?_ ?_
  · simp [ClauseSequent.isOrdinary, Clause.isOrdinary, G,
      ClauseSequent.ofList, LCS.Finset.mem_ofList, or_imp, forall_and] <;> native_decide
  · simp [ClauseSequent.isOrdinary, Clause.isOrdinary, A,
      ClauseSequent.single, LCS.Finset.mem_singleton] <;> native_decide
  · have h : LCS.Finset.union G1 A = L := by native_decide
    exact h.symm ▸ left
  · have h : LCS.Finset.union G2 (ClauseSequent.single
        (Clause.single (Literal.pos 1))) = R := by native_decide
    exact h.symm ▸ right
  · simp [LCS.Finset.Subset, G1, ClauseSequent.ofList,
      LCS.Finset.mem_ofList, or_imp, forall_and] <;> native_decide
  · simp [LCS.Finset.Subset, G2, ClauseSequent.ofList,
      LCS.Finset.mem_ofList, or_imp, forall_and] <;> native_decide

-- ATTACH-BLOCKER: unsupported untagged structure
/-- A primitive GCNF derivation with explicit local premise-order choices.
    Paths identify nodes of the kernel; swapping changes only their display. -/
@[blueprint "chap9__example_9_2_1"]
structure OrderedGCNFProof (S : ClauseSequent) where
  kernel : GCNFProofTree S
  swapPaths : List (List Bool)

/-- Example 9.2.1: The second printed tree, with exact contexts and
    cancellation-first definite branches. The kernel retains the primitive
    literal-B rule; the two explicit swaps give the PDF's premise order. -/
@[blueprint "chap9__example_9_2_1" (main := true)]
def exSLDFormProof : OrderedGCNFProof (ClauseSequent.ofList exHornClauseSet) where
  swapPaths := [[false], [true]]
  kernel := by
    let p := fun i => Clause.single (Literal.pos i)
    let n := fun i => Clause.single (Literal.neg i)
    let body := Clause.ofList [Literal.neg 3, Literal.neg 4]
    let rule1 := Clause.ofList [Literal.neg 3, Literal.neg 4, Literal.pos 1]
    let rule2 := Clause.ofList [Literal.neg 3, Literal.pos 2]
    let Bdy := ClauseSequent.ofList [p 3, p 4, body]
    let L := ClauseSequent.ofList [p 3, p 4, n 1, rule1]
    let R := ClauseSequent.ofList [p 3, n 2, rule2]
    let bodyTree : GCNFProofTree (Bdy) := by
      let G := ClauseSequent.ofList [p 3,p 4]
      let A := ClauseSequent.single (n 3)
      let G1 := ClauseSequent.ofList [p 3]
      let G2 := ClauseSequent.ofList [p 4]
      have hRoot : LCS.Finset.union G (ClauseSequent.mapSet A
          (fun C => clauseWithLiteral C (Literal.neg 4))) = Bdy := by native_decide
      rw [← hRoot]
      refine GCNFProofTree.rule G A (Literal.neg 4) A G1 G2 ?_ ?_ ?_ ?_
        ⟨n 3, by native_decide⟩ (fun _ h => h) ?_ ?_
      · simp [ClauseSequent.isOrdinary, Clause.isOrdinary, G,
          ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
          LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
      · simp [ClauseSequent.isOrdinary, Clause.isOrdinary, A,
          ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
          LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
      · refine GCNFProofTree.axiom_ _ ?_ ⟨3, by native_decide, by native_decide⟩
        simp [ClauseSequent.isOrdinary, Clause.isOrdinary, G1, A,
          ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
          LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
      · refine GCNFProofTree.axiom_ _ ?_ ⟨4, by native_decide, by native_decide⟩
        simp [ClauseSequent.isOrdinary, Clause.isOrdinary, G2, A,
          ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
          LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
      · simp [LCS.Finset.Subset, G1, ClauseSequent.ofList,
          LCS.Finset.mem_ofList, or_imp, forall_and] <;> native_decide
      · simp [LCS.Finset.Subset, G2, ClauseSequent.ofList,
          LCS.Finset.mem_ofList, or_imp, forall_and] <;> native_decide
    let leftTree : GCNFProofTree (L) := by
      let G := ClauseSequent.ofList [p 3,p 4,n 1]
      let A := ClauseSequent.single (body)
      let G1 := ClauseSequent.ofList [p 3,p 4]
      let G2 := ClauseSequent.ofList [n 1]
      have hRoot : LCS.Finset.union G (ClauseSequent.mapSet A
          (fun C => clauseWithLiteral C (Literal.pos 1))) = L := by native_decide
      rw [← hRoot]
      refine GCNFProofTree.rule G A (Literal.pos 1) A G1 G2 ?_ ?_ ?_ ?_
        ⟨body, by native_decide⟩ (fun _ h => h) ?_ ?_
      · simp [ClauseSequent.isOrdinary, Clause.isOrdinary, G,
          ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
          LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
      · simp [ClauseSequent.isOrdinary, Clause.isOrdinary, A,
          ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
          LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
      · have h : LCS.Finset.union G1 A = Bdy := by native_decide
        exact h.symm ▸ bodyTree
      · refine GCNFProofTree.axiom_ _ ?_ ⟨1, by native_decide, by native_decide⟩
        simp [ClauseSequent.isOrdinary, Clause.isOrdinary, G2, A,
          ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
          LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
      · simp [LCS.Finset.Subset, G1, ClauseSequent.ofList,
          LCS.Finset.mem_ofList, or_imp, forall_and] <;> native_decide
      · simp [LCS.Finset.Subset, G2, ClauseSequent.ofList,
          LCS.Finset.mem_ofList, or_imp, forall_and] <;> native_decide
    let rightTree : GCNFProofTree (R) := by
      let G := ClauseSequent.ofList [p 3,n 2]
      let A := ClauseSequent.single (n 3)
      let G1 := ClauseSequent.ofList [p 3]
      let G2 := ClauseSequent.ofList [n 2]
      have hRoot : LCS.Finset.union G (ClauseSequent.mapSet A
          (fun C => clauseWithLiteral C (Literal.pos 2))) = R := by native_decide
      rw [← hRoot]
      refine GCNFProofTree.rule G A (Literal.pos 2) A G1 G2 ?_ ?_ ?_ ?_
        ⟨n 3, by native_decide⟩ (fun _ h => h) ?_ ?_
      · simp [ClauseSequent.isOrdinary, Clause.isOrdinary, G,
          ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
          LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
      · simp [ClauseSequent.isOrdinary, Clause.isOrdinary, A,
          ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
          LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
      · refine GCNFProofTree.axiom_ _ ?_ ⟨3, by native_decide, by native_decide⟩
        simp [ClauseSequent.isOrdinary, Clause.isOrdinary, G1, A,
          ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
          LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
      · refine GCNFProofTree.axiom_ _ ?_ ⟨2, by native_decide, by native_decide⟩
        simp [ClauseSequent.isOrdinary, Clause.isOrdinary, G2, A,
          ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
          LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
      · simp [LCS.Finset.Subset, G1, ClauseSequent.ofList,
          LCS.Finset.mem_ofList, or_imp, forall_and] <;> native_decide
      · simp [LCS.Finset.Subset, G2, ClauseSequent.ofList,
          LCS.Finset.mem_ofList, or_imp, forall_and] <;> native_decide
    let result : GCNFProofTree (ClauseSequent.ofList exHornClauseSet) := by
      let G := ClauseSequent.ofList [p 3,p 4,rule1,rule2]
      let A := ClauseSequent.single (n 1)
      let G1 := ClauseSequent.ofList [p 3,p 4,rule1]
      let G2 := ClauseSequent.ofList [p 3,rule2]
      have hRoot : LCS.Finset.union G (ClauseSequent.mapSet A
          (fun C => clauseWithLiteral C (Literal.neg 2))) = ClauseSequent.ofList exHornClauseSet := by native_decide
      rw [← hRoot]
      refine GCNFProofTree.rule G A (Literal.neg 2) A G1 G2 ?_ ?_ ?_ ?_
        ⟨n 1, by native_decide⟩ (fun _ h => h) ?_ ?_
      · simp [ClauseSequent.isOrdinary, Clause.isOrdinary, G,
          ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
          LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
      · simp [ClauseSequent.isOrdinary, Clause.isOrdinary, A,
          ClauseSequent.ofList, ClauseSequent.single, LCS.Finset.mem_ofList,
          LCS.Finset.mem_singleton, or_imp, forall_and] <;> native_decide
      · have h : LCS.Finset.union G1 A = L := by native_decide
        exact h.symm ▸ leftTree
      · have h : LCS.Finset.union G2 (ClauseSequent.single (Clause.single (Literal.neg 2))) = R := by native_decide
        exact h.symm ▸ rightTree
      · simp [LCS.Finset.Subset, G1, ClauseSequent.ofList,
          LCS.Finset.mem_ofList, or_imp, forall_and] <;> native_decide
      · simp [LCS.Finset.Subset, G2, ClauseSequent.ofList,
          LCS.Finset.mem_ofList, or_imp, forall_and] <;> native_decide
    exact result

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Helper: Bool-valued check that all literals in a clause are negative.
    Used to verify that no clause in As is a definite clause. -/
def allNegativeB (C : Clause) : Bool :=
  C.val.all (fun l => match l with | Literal.neg _ => true | _ => false)



-- retained: used by LCS.SLD.SLDForm.Completeness.RootPartition
/-- Helper: allNegativeB C = true implies all literals in C are negative. -/
theorem allNegativeB_spec (C : Clause) (h : allNegativeB C = true) :
    ∀ l ∈ C, match l with | Literal.neg _ => True | _ => False := by
-- BEGIN PROOF
  intro l hl
  have := Multiset.all_eq_true.mp h l hl
  cases l with
  | neg _ => trivial
  | pos _ => simp at this





-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A finite search for a complementary singleton pair in a sequent label. -/
def axiomLabelB (S : ClauseSequent) : Bool :=
  S.val.any fun C => C.val.any fun l =>
    match l with
    | .pos P => decide (Clause.single (.pos P) ∈ S) &&
        decide (Clause.single (.neg P) ∈ S)
    | .neg _ => false

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The label search recognizes contextual axioms. -/
theorem axiomLabelB_sound (S : ClauseSequent) (h : axiomLabelB S = true) :
    S.isTrivial := by
  obtain ⟨C, _, hC⟩ := Multiset.any_eq_true.mp h
  obtain ⟨l, _, hl⟩ := Multiset.any_eq_true.mp hC
  cases l with
  | neg P => simp at hl
  | pos P =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
    exact ⟨P, hl⟩



-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- All-negative ordinary goals pass the finite polarity test. -/
theorem allNegativeB_of_goal {C : Clause} (h : isGoalClause C) :
    allNegativeB C = true := by
  apply Multiset.all_eq_true.mpr
  intro l hl
  have hn := h.2 l hl
  cases l with
  | neg _ => rfl
  | pos _ => exact False.elim hn

/-- Definition 9.2.2 (companion): check the selected singleton goal, its
    uniqueness, and the label-exempt local condition of isSLDForm_goalSplit. -/
@[blueprint "chap9__definition_9_2_2"]
def isSLDForm_goalSplitB (Q : Nat) : {S : ClauseSequent} → GCNFProofTree S → Bool
  | S, T =>
    decide (Clause.single (Literal.neg Q) ∈ S) &&
    S.val.all (fun C => if allNegativeB C then
      decide (C = Clause.single (Literal.neg Q)) else true) &&
    (axiomLabelB S || match T with
      | .axiom_ _ _ _ => true
      | .rule _ _ B' _ _ _ _ _ _ innerRight _ _ _ _ =>
        (B' == Literal.pos Q) && isAxiomNodeWithB Q innerRight)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Finite SLD-form check: inspect both children, exempt trivial labels from
    the local rule condition, and test the exact cancellation and goal branches. -/
def isSLDFormB : {S : ClauseSequent} → GCNFProofTree S → Bool
  | _, .axiom_ _ _ _ => true
  | _, .rule Gamma As B Cs Gamma1 _ _ _ leftTree rightTree _hNe _hSub _ _ =>
    isSLDFormB leftTree && isSLDFormB rightTree &&
    (axiomLabelB (LCS.Finset.union Gamma (ClauseSequent.mapSet As
      (fun A => clauseWithLiteral A B))) || match B with
    | Literal.pos P =>
      Cs.val.all (fun C => C.val.all (fun l =>
        match l with | Literal.neg _ => true | _ => false)) &&
      isAxiomNodeWithB P rightTree &&
      decide (Clause.single (Literal.neg P) ∈ Gamma) &&
      !decide (Clause.single (Literal.neg P) ∈ Gamma1) &&
      -- ∃ G ∈ Cs, G all-negative ∧ G is the unique goal clause in Gamma1 ∪ Cs
      Cs.val.any (fun G =>
        G.val.all (fun l => match l with | Literal.neg _ => true | _ => false) &&
        (LCS.Finset.union Gamma1 Cs).val.all (fun C =>
          if C.val.all (fun l => match l with | Literal.neg _ => true | _ => false) then
            decide (C = G)
          else true))
    | Literal.neg Q =>
      isSLDForm_goalSplitB Q rightTree &&
      -- Cs is all-negative
      Cs.val.all (fun C => C.val.all (fun l =>
        match l with | Literal.neg _ => true | _ => false)) &&
      Cs.val.any (fun G =>
        -- G ∈ Cs and is a goal clause (all negative)
        G.val.all (fun l => match l with | Literal.neg _ => true | _ => false) &&
        -- neg Q ∉ G
        !decide (Literal.neg Q ∈ G) &&
        -- G is the unique goal clause in Gamma1 ∪ Cs
        (LCS.Finset.union Gamma1 Cs).val.all (fun C =>
          -- If C is a goal clause (all negative), then C = G
          if C.val.all (fun l => match l with | Literal.neg _ => true | _ => false) then
            decide (C = G)
          else true)))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Helper: Bool literal negativity check implies isNegLit. -/
theorem isNegLit_of_bool (l : Literal)
    (h : (match l with | .neg _ => true | _ => false) = true) :
    isNegLit l := by
-- BEGIN PROOF
  cases l with
  | neg _ => trivial
  | pos _ => simp at h

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Helper: isSLDForm_goalSplitB soundness. -/
theorem isSLDForm_goalSplitB_sound (Q : Nat) :
    {S : ClauseSequent} → (T : GCNFProofTree S) →
    isSLDForm_goalSplitB Q T = true → isSLDForm_goalSplit Q T
  | S, T, h => by
    simp only [isSLDForm_goalSplitB, Bool.and_eq_true, Bool.or_eq_true] at h
    refine ⟨of_decide_eq_true h.1.1, ?_, ?_⟩
    · intro C hC hGoal
      have hc := Multiset.all_eq_true.mp h.1.2 C hC
      rw [allNegativeB_of_goal hGoal] at hc
      exact of_decide_eq_true hc
    · rcases h.2 with hAx | hRule
      · exact Or.inl (axiomLabelB_sound S hAx)
      · apply Or.inr
        cases T with
        | axiom_ => trivial
        | rule _ _ B _ _ _ _ _ _ right _ _ _ _ =>
          simp only [Bool.and_eq_true, beq_iff_eq] at hRule
          exact ⟨hRule.1, isAxiomNodeWithB_sound Q right hRule.2⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Helper: isSLDFormB soundness — if the Bool check passes, the Prop holds. -/
theorem isSLDFormB_sound :
    {S : ClauseSequent} → (T : GCNFProofTree S) →
    isSLDFormB T = true → isSLDForm T
  | _, .axiom_ _ _ _, _ => trivial
  | _, .rule Gamma _As B Cs Gamma1 _G2 _ _ leftTree rightTree _hNe _hSub _hG1 _hG2, h => by
    simp only [isSLDFormB, Bool.and_eq_true] at h
    obtain ⟨⟨hLeft, hRight⟩, hB⟩ := h
    refine ⟨isSLDFormB_sound leftTree hLeft, isSLDFormB_sound rightTree hRight, ?_⟩
    rw [Bool.or_eq_true] at hB
    rcases hB with hAx | hB
    · exact Or.inl (axiomLabelB_sound _ hAx)
    apply Or.inr
    cases B with
    | pos P =>
      simp only at hB
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hB
      obtain ⟨⟨⟨⟨hAllNeg, hAxiom⟩, hGamma⟩, hDrop⟩, hWit⟩ := hB
      refine ⟨fun C hC l hl => by
        have h1 := Multiset.all_eq_true.mp hAllNeg C hC
        have h2 := Multiset.all_eq_true.mp h1 l hl
        exact isNegLit_of_bool l h2,
       isAxiomNodeWithB_sound P rightTree hAxiom,
       of_decide_eq_true hGamma,
       by simpa using hDrop,
       ?_⟩
      -- Extract witness G
      rw [Multiset.any_eq_true] at hWit
      obtain ⟨G, hGmem, hGconj⟩ := hWit
      rw [Bool.and_eq_true] at hGconj
      obtain ⟨hGneg, hUnique⟩ := hGconj
      refine ⟨G, hGmem, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · refine ⟨leftTree.ordinary G (Finset.mem_union.mpr (Or.inr hGmem)), ?_⟩
          intro P1 P2 hP1 _
          have h1 := Multiset.all_eq_true.mp hGneg (Literal.pos P1) hP1
          simp at h1
        · intro l hl
          have h1 := Multiset.all_eq_true.mp hGneg l hl
          cases l with
          | neg _ => trivial
          | pos _ => simp at h1
      · intro C hCmem hCgoal
        have hMem : C ∈ (LCS.Finset.union Gamma1 Cs).val := hCmem
        have h1 := Multiset.all_eq_true.mp hUnique C hMem
        have hCneg : C.val.all (fun l =>
            match l with | Literal.neg _ => true | _ => false) = true := by
          rw [Multiset.all_eq_true]
          intro l hl
          have := hCgoal.2 l hl
          cases l with
          | neg _ => rfl
          | pos _ => simp at this
        rw [hCneg] at h1
        simp only [if_true] at h1
        exact of_decide_eq_true h1
    | neg Q =>
      simp only at hB
      rw [Bool.and_eq_true, Bool.and_eq_true] at hB
      obtain ⟨⟨hGoalSplit, hCsAllNeg⟩, hWit⟩ := hB
      refine ⟨isSLDForm_goalSplitB_sound Q rightTree hGoalSplit, ?_, ?_⟩
      · -- Cs all-neg
        intro C hC l hl
        have h1 := Multiset.all_eq_true.mp hCsAllNeg C hC
        have h2 := Multiset.all_eq_true.mp h1 l hl
        exact isNegLit_of_bool l h2
      · -- Extract the witness G from Cs.val.any
        rw [Multiset.any_eq_true] at hWit
        obtain ⟨G, hGmem, hGconj⟩ := hWit
        rw [Bool.and_eq_true, Bool.and_eq_true] at hGconj
        obtain ⟨⟨hGneg, hGNoNegQ⟩, hUnique⟩ := hGconj
        refine ⟨G, hGmem, ?_, ?_, ?_⟩
        · -- isGoalClause G
          refine ⟨?_, ?_⟩
          · refine ⟨leftTree.ordinary G (Finset.mem_union.mpr (Or.inr hGmem)), ?_⟩
            intro P1 P2 hP1 _
            have h1 := Multiset.all_eq_true.mp hGneg (Literal.pos P1) hP1
            simp at h1
          · intro l hl
            have h1 := Multiset.all_eq_true.mp hGneg l hl
            cases l with
            | neg _ => trivial
            | pos _ => simp at h1
        · -- neg Q ∉ G
          intro hMem
          have : decide (Literal.neg Q ∈ G) = true := decide_eq_true hMem
          rw [this] at hGNoNegQ
          simp at hGNoNegQ
        · -- uniqueness
          intro C hCmem hCgoal
          have hMem : C ∈ (LCS.Finset.union Gamma1 Cs).val := hCmem
          have h1 := Multiset.all_eq_true.mp hUnique C hMem
          have hCneg : C.val.all (fun l =>
              match l with | Literal.neg _ => true | _ => false) = true := by
            rw [Multiset.all_eq_true]
            intro l hl
            have := hCgoal.2 l hl
            cases l with
            | neg _ => rfl
            | pos _ => simp at this
          rw [hCneg] at h1
          simp only [if_true] at h1
          exact of_decide_eq_true h1

-- ATTACH-KEEP: native decision certificate must retain its front owner
/-- The finite SLD-form checker accepts the exact displayed tree. -/
theorem exSLDFormProof_check : isSLDFormB exSLDFormProof.kernel = true := by
  native_decide

/-- Example 9.2.1 (companion): Proof that the example proof tree satisfies the
    SLD-form property of Definition 9.2.2. Verified via the Bool decision
    procedure `isSLDFormB` and the soundness lemma `isSLDFormB_sound`. -/
@[blueprint "chap9__example_9_2_1"]
theorem exSLDFormProof_isSLDForm :
    isSLDForm exSLDFormProof.kernel 
end LCS.SLD.SLDForm
