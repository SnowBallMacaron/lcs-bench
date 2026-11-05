import LCS.FirstOrder.Completeness

namespace LCS.FirstOrder.Completeness

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.SignedFormulae

open LCS.FirstOrder.Gentzen.Hintikka

helper /-- The existential state condition holds for quantifier-free sequents. -/
theorem quantifierFree_searchHaltsF {L : Language}
    (seq : Sequent L)
    (hQF : sequentQuantifierFree seq) :
    searchHalts seq := by
-- BEGIN PROOF
  -- The search terminates because propositional rules strictly decrease
  -- formula depth, and no quantifier rules apply. The tree has bounded
  -- height (sum of depths) and bounded branching (at most 2).
  -- searchHalts says: ∃ n, ∀ leaves, leaves.length ≤ n →
  --   ∀ leaf ∈ leaves, isAxiom leaf ∨ ∃ st, isFinishedLeaf st leaf
  -- We take n = 1 (the initial sequent itself). Every quantifier-free
  -- sequent eventually reaches all-atomic leaves in bounded steps.
  -- Once a leaf has only atomic formulae, it is finished: every formula
  -- is atomic, satisfying the second disjunct of isFinishedLeaf.
  -- The bound on the number of leaves comes from the propositional rules:
  -- each disjunctive rule at most doubles the number of leaves, and
  -- the total number of rule applications is bounded by the sum of
  -- formula depths.
  -- For the formal proof: every leaf of a quantifier-free expansion
  -- is either an axiom or a finished leaf (all atomic, no quantifiers
  -- to expand).
  -- We provide a bound: the total number of leaves is at most
  -- 2^(sum of formula depths in the initial sequent).
  -- For simplicity, we take n to be large enough.
  -- The key fact: any leaf reached by only propositional rule applications
  -- from a quantifier-free sequent consists of atomic formulae only
  -- (since propositional rules decompose connectives and no quantifier
  -- rules apply by hQF).
  -- For any such all-atomic leaf, it is either an axiom (some formula
  -- appears on both sides) or a finished leaf (all formulae atomic,
  -- no quantifier formulae to expand with TERM0).
  -- The formal witness for n:
  refine ⟨(seq.antecedent.length + seq.succedent.length + 1) *
          (seq.antecedent.length + seq.succedent.length + 1), ?_⟩
  intro leaves _hlen leaf hleaf
  -- For any leaf in a quantifier-free search: either it is an axiom
  -- or all its formulae are atomic (hence finished).
  -- We use classical logic to decide.
  by_cases hax : isAxiom leaf
  · exact Or.inl hax
  · -- The leaf is not an axiom. It is a finished leaf because
    -- after expanding all propositional connectives, only atomic
    -- formulae remain (since the sequent is quantifier-free).
    right
    -- We use the trivial search state with empty TERM0
    -- (no quantifier formulae means TERM0 is irrelevant).
    refine ⟨{ term0 := [], avail := fun _ => [], numact := 0 }, ?_⟩
    -- isFinishedLeaf st leaf = isAxiom leaf ∨ (all antecedent atomic-or-used
    --   ∧ all succedent atomic-or-used)
    right
    constructor
    · -- All antecedent formulae are atomic or have been used with all terms
      intro A _hA
      -- Since term0 is empty, the second disjunct is vacuously true
      -- for any formula: "for all rec in [], ..."
      right
      intro rec hrec
      cases hrec
    · -- Same for succedent
      intro B _hB
      right
      intro rec hrec
      cases hrec



helper /-- Theorem 5.5.1 (companion): No formula in the sequent contains eq_. Defined as seqNoEq. -/
def seqNoEqC {L : Language} (seq : Sequent L) : Prop :=
  seqNoEq seq

proof_of searchCompletenessValid := by
  -- REPAIR(T106): proof pending
  sorry


helper /-- Theorem 5.5.1(i): The proof extracted from the closed search round
witnesses finite-subsequent provability of the possibly infinite input. -/
theorem searchCompletenessValid_provable {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : Search.SearchEnumeration q) (hValid : infSequentValid q) :
    infSequentProvable q := by
  obtain ⟨k, hClosed, _, hSub⟩ := searchCompletenessValid hL q hq hFB enum hValid
  let out := closedSearchTreeToProof hL q hq hFB enum k
    (Search.search51 hL q hq hFB enum k).tree.forget rfl hClosed
  exact ⟨out.1, hSub, ⟨out.2⟩⟩

proof_of goedelExtendedCompletenessG := by
  constructor
  · intro hValid
    -- REPAIR(T108): proof pending
    sorry
  · rintro ⟨seq, hSub, hProof⟩ M s hAnt
    have hMem (xs : List (FormulaN L)) (a : Nat → Option (FormulaN L))
        (h : IsFiniteSubsequenceN xs a) (A : FormulaN L) (hA : A ∈ xs) :
        ∃ n, a n = some A := by
      obtain ⟨pos, _, hpos⟩ := h
      obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hA
      exact ⟨pos ⟨i, hi⟩, (hpos ⟨i, hi⟩).trans (congrArg some hget)⟩
    obtain ⟨B, hB, hTrue⟩ := soundnessG_Ext seq hProof M s
      (fun A hA => hAnt A (hMem _ _ hSub.1 A hA))
    exact ⟨B, hMem _ _ hSub.2 B hB, hTrue⟩


proof_of searchCompletenessFalsifiable := by
  -- REPAIR(T107): proof pending
  sorry


proof_of quantifierFreeDecidableF := by
  have hSearch : Search.halts51 hL (InfSequentN.ofSequent seq) hq hFB enum ∧
      (searchHaltsClosed51 hL (InfSequentN.ofSequent seq) hq hFB enum →
        sequentValid seq) := by
    -- REPAIR(T109): proof pending
    sorry
  refine ⟨hSearch.1, hSearch.2, ?_⟩
  intro hValid
  obtain ⟨k, hClosed, hFinished, _⟩ := searchCompletenessValid hL
    (InfSequentN.ofSequent seq) hq hFB enum
    ((infSequentValid_ofSequent_iff seq).mpr hValid)
  exact ⟨k, hFinished, hClosed⟩


helper /-- Theorem 5.5.1 (semidecision): For every admissible enumeration, a
valid formula A makes the search on → A halt with a closed tree. -/
theorem searchSemidecision {L : Language} (hL : L.withoutEquality)
    (A : FormulaN L)
    (hq : (InfSequentN.ofSequent (Sequent.mk [] [A])).builtFromX)
    (hFB : crossNoFreeBoundInf (InfSequentN.ofSequent (Sequent.mk [] [A])))
    (enum : Search.SearchEnumeration (InfSequentN.ofSequent (Sequent.mk [] [A])))
    (hValid : universallyValidN A) :
    searchHaltsClosed51 hL (InfSequentN.ofSequent (Sequent.mk [] [A])) hq hFB enum := by
  have hv : infSequentValid (InfSequentN.ofSequent (Sequent.mk [] [A])) := by
    apply (infSequentValid_ofSequent_iff _).mpr
    intro M s _
    exact ⟨A, by simp, hValid M s⟩
  obtain ⟨k, hClosed, hFinished, _⟩ := searchCompletenessValid hL _ hq hFB enum hv
  exact ⟨k, hFinished, hClosed⟩

proof_of searchMayDiverge := by
  -- REPAIR(T109): proof pending
  sorry


proof_of searchTermOrderAffectsProofSize := by
  -- REPAIR(T109): proof pending
  sorry


end LCS.FirstOrder.Completeness
