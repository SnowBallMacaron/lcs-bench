import LCS.Item
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Gentzen.Search.NoFunction.Search
import Attach
import LCS.FirstOrder.Gentzen.Search.NoFunction.Examples.ProofsStamp

/-! # Examples 5.4.3 and 5.4.4 (Section 5.4.7)

Runs of procedure search on the sequents of Examples 5.4.3 and 5.4.4.
Source: Logic for Computer Science, Gallier 2015
-/

section
namespace LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.Search.NoFunction

/-- Example 5.4.3: The input sequent for the traced search. -/
@[blueprint "chap5__example_5_4_3"]
def exSearchSeq_5_4_3 : Sequent exampleLangPQ := ⟨[], [exSearchFormula_5_4_3]⟩

theorem exSearchCross_5_4_3 : crossNoFreeBound exSearchSeq_5_4_3 := by
  intro x ⟨A, hA, hx⟩
  simp only [exSearchSeq_5_4_3, List.nil_append, List.mem_singleton] at hA
  subst A
  simp [exSearchFormula_5_4_3, exFormulaExistentialImpl, formulaFVN, termFV,
    exampleLangPQ] at hx
  rcases hx with ⟨h, hn⟩ | h | ⟨h, hn⟩
  · rcases h with ⟨i, _⟩ | ⟨_, hi⟩
    · exact Fin.elim0 i
    · exact False.elim (hn hi)
  · obtain ⟨i, _⟩ := h
    exact Fin.elim0 i
  · obtain ⟨_, hi⟩ := h
    exact False.elim (hn hi)

/-- Example 5.4.3: Round-k approximants with the canonical admissible initialization. -/
@[blueprint "chap5__example_5_4_3"]
noncomputable def exSearchRun_5_4_3 (k : Nat) :=
  search rfl (fun f => Empty.elim f) exSearchSeq_5_4_3 exSearchCross_5_4_3
    (Init.default exSearchSeq_5_4_3) k

/-- Example 5.4.3: The first-round diagram consists of the outer
    implication-right inference and its single open premise. -/
@[blueprint "chap5__example_5_4_3"]
def exSearchExpectedRoundOne_5_4_3 : GDeductionTreeExt exSearchSeq_5_4_3 :=
  let p : FormulaN exampleLangPQ := .predN ExPredPQ.P (fun i => Fin.elim0 i)
  let q (n : Nat) : FormulaN exampleLangPQ := .predN ExPredPQ.Q (fun _ => .var n)
  let antecedent := FormulaN.ex 0 (.impl p (q 0))
  let consequent := FormulaN.impl p (.ex 2 (q 2))
  .onePremise (.implRight [] [] [] antecedent consequent)
    (.leaf ⟨[antecedent], [consequent]⟩)

/-- Example 5.4.3: The second-round diagram has, from its root upward,
    implication-right, existential-left with y₁ = x₄, and implication-right.
    Its open leaf is P, P ⊃ Q(y₁) → ∃z Q(z). -/
@[blueprint "chap5__example_5_4_3"]
def exSearchExpectedRoundTwo_5_4_3 : GDeductionTreeExt exSearchSeq_5_4_3 :=
  let p : FormulaN exampleLangPQ := .predN ExPredPQ.P (fun i => Fin.elim0 i)
  let q (n : Nat) : FormulaN exampleLangPQ := .predN ExPredPQ.Q (fun _ => .var n)
  let exZQz := FormulaN.ex 2 (q 2)
  let antecedent := FormulaN.ex 0 (.impl p (q 0))
  let consequent := FormulaN.impl p exZQz
  let inst := LCS.FirstOrder.SyntaxN.Substitution.formulaSubstN
    (.impl p (q 0)) (.var 4) 0
  .onePremise (.implRight [] [] [] antecedent consequent)
    (.onePremise
      (.exLeft 4 [] [] [consequent] 0 (.impl p (q 0))
        (by
          intro F hF
          simp at hF
          rcases hF with rfl | rfl
          · intro h
            simp [formulaFVN, p, q, termFV] at h
            obtain ⟨h1, h2⟩ := h
            rcases h1 with ⟨i, _⟩ | ⟨_j, hj⟩
            · exact Fin.elim0 i
            · exact (by decide : (4 : Nat) ≠ 0) hj
          · intro h
            simp [consequent, formulaFVN, p, exZQz, q, termFV] at h
            rcases h with ⟨i, _⟩ | ⟨hSet, _h2⟩
            · exact Fin.elim0 i
            · rcases hSet with ⟨_j, hj⟩
              exact (by decide : (4 : Nat) ≠ 2) hj)
        (by simp [LCS.FirstOrder.SyntaxN.Substitution.isFreeForN, p, q]))
      (.onePremise (.implRight [inst] [] [] p exZQz)
        (.leaf ⟨[p, inst], [exZQz]⟩)))

/-- Example 5.4.3: The actual first search round is the displayed
    two-node deduction tree. -/
theorem exSearchRoundOne_5_4_3 :
    (exSearchRun_5_4_3 1).1.toDeductionTree = exSearchExpectedRoundOne_5_4_3 := by
  -- REPAIR(T137): proof pending
  sorry

/-- Example 5.4.3: The actual second search round is the displayed
    four-node deduction tree, with the same inference order and sequents. -/
theorem exSearchRoundTwo_5_4_3 :
    (exSearchRun_5_4_3 2).1.toDeductionTree = exSearchExpectedRoundTwo_5_4_3 := by
  -- REPAIR(T137): proof pending
  sorry

/-- Example 5.4.3: TERM₀ and the entire remaining AVAIL₀ stream after
    rounds 0, 1, 2, and 3. The first eigenvariable is x₄, distinct from y₀ = x₁. -/
theorem exSearchSnapshots_5_4_3 :
    ([0, 1, 2, 3].map (fun k => (exSearchRun_5_4_3 k).2.TERM0) =
      [[.var 1], [.var 1], [.var 1, .var 4], [.var 1, .var 4]]) ∧
    (∀ n, [0, 1, 2, 3].map (fun k => (Init.default exSearchSeq_5_4_3).avail0.entries
      ((exSearchRun_5_4_3 k).2.availNext + n)) =
      [some (.var (4 + n)), some (.var (4 + n)), some (.var (5 + n)), some (.var (5 + n))]) := by
  -- REPAIR(T91): proof pending
  sorry

/-- Example 5.4.3: FORM₀ at the actual leaf occurrences after rounds two
    and three. Term positions 0 and 1 are y₀ = x₁ and y₁ = x₄. The round-two
    leaf at 000 has two empty histories. In round three, the expanded leaf
    at 00010 records ∃z Q(z) at both positions, while the axiom sibling at
    0000 retains its two empty histories. Addresses use 0 for a unary or
    left edge and 1 for a right edge. -/
theorem exSearchHistories_5_4_3 :
    let p : FormulaN exampleLangPQ := .predN ExPredPQ.P (fun i => Fin.elim0 i)
    let q (n : Nat) : FormulaN exampleLangPQ := .predN ExPredPQ.Q (fun _ => .var n)
    let principal := FormulaN.ex 2 (q 2)
    (exSearchRun_5_4_3 2).2.TERM0 = [.var 1, .var 4] ∧
    (exSearchRun_5_4_3 3).2.TERM0 = [.var 1, .var 4] ∧
    ∃ (roundTwo expanded sibling : BranchRecords exampleLangPQ),
      SearchTree.LeafAt ⟨[p, .impl p (q 4)], [principal]⟩ roundTwo
        (exSearchRun_5_4_3 2).1 [false, false, false] ∧
      roundTwo.form0 = [[], []] ∧
      SearchTree.LeafAt ⟨[q 4, p], [q 1, q 4, principal]⟩ expanded
        (exSearchRun_5_4_3 3).1 [false, false, false, true, false] ∧
      expanded.form0 = [[principal], [principal]] ∧
      SearchTree.LeafAt ⟨[p], [p, principal]⟩ sibling
        (exSearchRun_5_4_3 3).1 [false, false, false, false] ∧
      sibling.form0 = [[], []] := by
  -- REPAIR(T138): proof pending
  sorry

/-- Example 5.4.3: The third round is a proof, with exactly the displayed
    inference tree (including the single two-term ∃:right inference). -/
@[attach_debt, blueprint "chap5__example_5_4_3" (main := true)]
theorem exSearchRoundThree_5_4_3 :
    ∃ h : (exSearchRun_5_4_3 3).1.toDeductionTree.isProof,
      (exSearchRun_5_4_3 3).1.toDeductionTree.toProofTree h = exSearchProofTree_5_4_3 

end LCS.FirstOrder.Gentzen.Hintikka

namespace LCS.FirstOrder.Gentzen.Search.NoFunction
open LCS.FirstOrder.Basic LCS.FirstOrder.Gentzen

/-- Example 5.4.4 (companion): The complete ordered tree diagram, with
    every node's address and sequent and every leaf's formula-use records. -/
@[blueprint "chap5__example_5_4_4"]
def SearchTree.traceNodes {L : Language} : {s : Sequent L} → SearchTree s →
    List (List Bool × Sequent L × Option (BranchRecords L))
  | s, .leaf _ r => [([], s, some r)]
  | s, .onePremise _ t => ([], s, none) ::
      t.traceNodes.map (fun (p, l, r) => (false :: p, l, r))
  | s, .twoPremise _ t1 t2 => ([], s, none) ::
      (t1.traceNodes.map (fun (p, l, r) => (false :: p, l, r)) ++
       t2.traceNodes.map (fun (p, l, r) => (true :: p, l, r)))

end LCS.FirstOrder.Gentzen.Search.NoFunction

namespace LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.Search.NoFunction

/-- Example 5.4.4: The input sequent for the traced search. -/
@[blueprint "chap5__example_5_4_4"]
def exSearchSeq_5_4_4 : Sequent exampleLangPQ := ⟨[], [exSearchFormula_5_4_4]⟩

theorem exSearchCross_5_4_4 : crossNoFreeBound exSearchSeq_5_4_4 := by
  intro x ⟨A, hA, hx⟩
  simp only [exSearchSeq_5_4_4, List.nil_append, List.mem_singleton] at hA
  subst A
  simp [exSearchFormula_5_4_4, formulaFVN, termFV, exampleLangPQ] at hx
  rcases hx with ⟨h, hn⟩ | h | ⟨h, hn⟩
  · rcases h with ⟨i, _⟩ | ⟨_, hi⟩
    · exact Fin.elim0 i
    · exact False.elim (hn hi)
  · obtain ⟨i, _⟩ := h
    exact Fin.elim0 i
  · obtain ⟨_, hi⟩ := h
    exact False.elim (hn hi)

/-- Example 5.4.4: The canonical run, with y₀ = x₁, y₁ = x₄, y₂ = x₅. -/
@[blueprint "chap5__example_5_4_4"]
noncomputable def exSearchRun_5_4_4 (k : Nat) :=
  search rfl (fun f => Empty.elim f) exSearchSeq_5_4_4 exSearchCross_5_4_4
    (Init.default exSearchSeq_5_4_4) k

/-- Example 5.4.4: Q(y₁), P → Q(y₂), the open leaf after round three. -/
@[blueprint "chap5__example_5_4_4"]
def exSearchOpenLeaf_5_4_4 : Sequent exampleLangPQ :=
  ⟨[.predN ExPredPQ.Q (fun _ => .var 4), .predN ExPredPQ.P (fun i => Fin.elim0 i)],
   [.predN ExPredPQ.Q (fun _ => .var 5)]⟩

/-- Example 5.4.4: Ordered tree diagrams and branch records at rounds 0–3.
    Each list enumerates all nodes in preorder, with root-to-node addresses. -/
@[blueprint "chap5__example_5_4_4"]
def exSearchExpectedNodes_5_4_4 :
    List (List (List Bool × Sequent exampleLangPQ × Option (BranchRecords exampleLangPQ))) :=
  let P : FormulaN exampleLangPQ := .predN ExPredPQ.P (fun i => Fin.elim0 i)
  let Q := fun (n : Nat) => FormulaN.predN (L := exampleLangPQ) ExPredPQ.Q (fun _ => .var n)
  let E := FormulaN.ex 0 (.impl P (Q 0))
  let U := FormulaN.all 2 (Q 2)
  let s0 := exSearchSeq_5_4_4
  let s1 : Sequent exampleLangPQ := ⟨[E], [.impl P U]⟩
  let s2 : Sequent exampleLangPQ := ⟨[.impl P (Q 4)], [.impl P U]⟩
  let s3 : Sequent exampleLangPQ := ⟨[P, .impl P (Q 4)], [U]⟩
  let s4 : Sequent exampleLangPQ := ⟨[P], [P, U]⟩
  let s5 : Sequent exampleLangPQ := ⟨[Q 4, P], [U]⟩
  let r1 : BranchRecords exampleLangPQ := ⟨[[]], [[]]⟩
  let r2 : BranchRecords exampleLangPQ := ⟨[[], []], [[], []]⟩
  let r3 : BranchRecords exampleLangPQ := ⟨[[], [], []], [[], [], []]⟩
  [[([], s0, some r1)],
   [([], s0, none), ([false], s1, some r1)],
   [([], s0, none), ([false], s1, none), ([false, false], s2, none),
     ([false, false, false], s3, some r2)],
   [([], s0, none), ([false], s1, none), ([false, false], s2, none),
     ([false, false, false], s3, none), ([false, false, false, false], s4, some r3),
     ([false, false, false, true], s5, none),
     ([false, false, false, true, false], exSearchOpenLeaf_5_4_4, some r3)]]

/-- Example 5.4.4: The actual search rounds have these diagrams and records. -/
@[attach_debt, blueprint "chap5__example_5_4_4" (main := true)]
theorem exSearchTrace_5_4_4 :
    [0, 1, 2, 3].map (fun k => (exSearchRun_5_4_4 k).1.traceNodes) =
      exSearchExpectedNodes_5_4_4 

/-- Example 5.4.4: TERM₀ and all remaining AVAIL₀ entries after rounds 0–3. -/
theorem exSearchSnapshots_5_4_4 :
    ([0, 1, 2, 3].map (fun k => (exSearchRun_5_4_4 k).2.TERM0) =
      [[.var 1], [.var 1], [.var 1, .var 4], [.var 1, .var 4, .var 5]]) ∧
    (∀ n, [0, 1, 2, 3].map (fun k => (Init.default exSearchSeq_5_4_4).avail0.entries
      ((exSearchRun_5_4_4 k).2.availNext + n)) =
      [some (.var (4 + n)), some (.var (4 + n)), some (.var (5 + n)), some (.var (6 + n))]) := by
  -- REPAIR(T92): proof pending
  sorry

end LCS.FirstOrder.Gentzen.Hintikka
end
