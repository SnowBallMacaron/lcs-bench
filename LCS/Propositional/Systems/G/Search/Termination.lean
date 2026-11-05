import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import Attach
import LCS.Propositional.Systems.G.Search.Termination.ProofsStamp
import LCS.Propositional.Systems.G.Search.LeafExpansion
import LCS.Propositional.Systems.G.Search.SearchRounds
import LCS.Propositional.Systems.G.Search.Validity
import LCS.Propositional.Systems.G.Search.Falsification
attach_helper_namespace LCS.Propositional.Systems.G.Search.Proofs

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
variable {mode : SearchMode}

theorem findFirstNonatomic_spec_aux (L : List PropFormulaNormalized) (k : Nat)
    (A : PropFormulaNormalized) (i : Nat)
    (h : findFirstNonatomic L k = some (A, i)) :
    k ≤ i ∧ L[i - k]? = some A ∧ isNonatomicBool A = true := by
-- BEGIN PROOF
  induction L generalizing k with
  | nil => simp [findFirstNonatomic] at h
  | cons x xs ih =>
    simp only [findFirstNonatomic] at h; split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; simp [Nat.sub_self, *]
    · have step := ih (k + 1) h; refine ⟨by omega, ?_, step.2.2⟩
      rw [show i - k = (i - (k + 1)) + 1 from by omega]
      simp [List.getElem?_cons_succ]; exact step.2.1

-- ATTACH-BLOCKER: used by LCS.Propositional.Systems.G.Search (expandFirstFormula_eq_scheduled_ante)
theorem findFirstNonatomic_spec (L : List PropFormulaNormalized) (A : PropFormulaNormalized) (i : Nat)
    (h : findFirstNonatomic L = some (A, i)) :
    i < L.length ∧ L[i]? = some A ∧ isNonatomicBool A = true := by
-- BEGIN PROOF
  have aux := findFirstNonatomic_spec_aux L 0 A i h
  obtain ⟨_, hget, hna⟩ := aux; simp at hget
  exact ⟨Classical.byContradiction fun hge => by
    rw [List.getElem?_eq_none (by omega)] at hget; simp at hget, hget, hna⟩

-- ATTACH-BLOCKER: used by LCS.Propositional.Systems.G.Search (expandLeaf_eq_full_schedule)
theorem findFirstNonatomic_none_all_atomic (L : List PropFormulaNormalized) (k : Nat)
    (h : findFirstNonatomic L k = none) :
    ∀ A ∈ L, isAtomicFormula A := by
-- BEGIN PROOF
  induction L generalizing k with
  | nil => intro A hA; simp at hA
  | cons x xs ih =>
    simp only [findFirstNonatomic] at h
    split at h
    · simp at h
    · case isFalse hna =>
      intro A hA
      cases List.mem_cons.mp hA with
      | inl heq =>
        subst heq
        cases A with
        | var _ => exact trivial
        | _ => simp [isNonatomicBool] at hna
      | inr hmem => exact ih (k + 1) h A hmem

-- ATTACH-BLOCKER: used by LCS.Propositional.Systems.G.Search (expandLeaf_eq_full_schedule)
/-- Finished leaves are preserved by expansion. -/
theorem expandLeaf_of_finished (s : Sequent) (h : isFinishedLeafBool mode s = true) :
    expandLeaf mode s = .leaf s := by simp [expandLeaf, h]

/-- searchRound strictly decreases maxUnfinishedLeafComplexity when
    the tree has unfinished leaves. This is the key termination argument. -/
@[blueprint "chap3__theorem_3_4_1"]
theorem searchRound_complexity_decrease {c : Sequent} (dt : DeductionTree c)
    (hunf : ¬isFinishedTreeBool mode dt = true) :
    maxUnfinishedLeafComplexity mode (searchRound mode dt) <
      maxUnfinishedLeafComplexity mode dt 

/-- Definition 3.4.6: Procedure search. The input to search is a one-node
    tree labeled with a sequent Γ → Δ; the output is a finished tree T
    called a systematic or atomically closed deduction tree. Implements the while-loop of
    Definition 3.4.6: repeatedly applies searchRound until all leaves
    are finished (isFinishedTree). Terminates because maxUnfinishedLeafComplexity
    strictly decreases each round — each round decomposes at least one
    nonatomic formula in every unfinished leaf.

    The strict decrease theorem supplies the recursive termination proof. -/
@[blueprint "chap3__definition_3_4_6" (main := true)]
def search (mode : SearchMode) {s : Sequent} (dt : DeductionTree s) : DeductionTree s :=
  if _h : isFinishedTreeBool mode dt then dt
  else search mode (searchRound mode dt)
termination_by maxUnfinishedLeafComplexity mode dt
decreasing_by exact searchRound_complexity_decrease dt _h

/-- Definition 3.4.6 (companion): Entry point for the search procedure:
    starts with a one-node tree labeled with the input sequent, then
    applies search to repeatedly expand leaves until all are finished. -/
@[blueprint "chap3__definition_3_4_6"]
def searchStart (mode : SearchMode) (s : Sequent) : DeductionTree s :=
  search mode (DeductionTree.leaf s)

-- search returns the input when it's already finished


/-- Example 3.4.4 (companion): For the example sequent from Example 3.4.4,
    the search procedure produces a finished tree. Verified computationally. -/
@[blueprint "chap3__example_3_4_4"]
theorem search_produces_finished_tree_example :
    isFinishedTree .systematic (searchStart .systematic exSearchTraceSequent) 

-- ========= Theorem 2: search_terminates =========



-- ========= Theorems 7-8: search_conclusion, search_wf =========





/-- The atomic stopping convention produces an atomically closed tree,
    including when the input is a compound axiom. -/
@[blueprint "chap3__definition_3_4_6"]
theorem searchStart_atomic_closed (s : Sequent) :
    ∀ leaf ∈ (searchStart .atomic s).leaves,
      ∀ A ∈ leaf.antecedent ++ leaf.succedent, isAtomicFormula A 

-- ========= Theorem 3.4.1: Main theorem and corollary =========

/-- Theorem 3.4.1: The procedure search terminates for every finite input
    sequent. If the input sequent Γ → Δ is valid, procedure search produces
    a proof tree for Γ → Δ; if Γ → Δ is falsifiable, search produces a tree
    from which all falsifying valuations can be found.

    Formally: let T = searchStart s. Then:
    (1) T is a finished deduction tree (all leaves are axioms or all-atomic).
    (2) If s is valid, T is a proof tree (all leaves are axioms).
    (3) If s is falsifiable, every falsifying valuation v for s also
        falsifies some non-axiom leaf of T. -/
@[blueprint "chap3__theorem_3_4_1" (main := true)]
theorem search_theorem_3_4_1 (s : Sequent) :
    let T := searchStart mode s
    isFinishedTree mode T ∧
    (sequentValid s → isProofTree T) ∧
    (¬sequentValid s → ∀ v, sequentFalsifiedBy s v →
      ∃ leaf ∈ nonAxiomLeaves T, sequentFalsifiedBy leaf v) 

/-- Corollary of Theorem 3.4.1: Completeness of G'. Every valid sequent
    is provable. Furthermore, there is an algorithm for deciding whether
    a sequent is valid and if so, a proof tree is obtained. -/
@[blueprint "chap3__theorem_3_4_1"]
theorem corollary_completeness_G (s : Sequent) :
    sequentValid s ↔ sequentProvable s 

end LCS.Propositional.Systems.G.Search
end

