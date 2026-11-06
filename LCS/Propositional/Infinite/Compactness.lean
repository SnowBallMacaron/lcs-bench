import LCS.Item
import LCS.Util
import LCS.Propositional.Infinite
import LCS.Propositional.Infinite.SignedFormulae
import Attach
import LCS.Propositional.Infinite.Compactness.ProofsStamp

/-! # Propositional.Infinite.Compactness
    Formalization of Chapter 3, Sections 3.5.7-3.5.8.
    Covers compactness, model existence, consistency,
    and maximal consistent sets.
-/

namespace LCS.Propositional.Infinite.Compactness

open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search
open LCS.Propositional.Infinite
open Classical

-- ========= Succedent Weakening for G' Proof Trees =========





-- ========= Definition 3.5.8: Satisfiable Set of Propositions =========

/-- Definition 3.5.8 (companion): A valuation v satisfies a set Gamma
    of propositions iff v makes every proposition in Gamma true. -/
@[blueprint "chap3__definition_3_5_8"]
def setSatisfiedBy (Gamma : Set PropFormulaNormalized) (v : Valuation) : Prop :=
  ∀ A, A ∈ Gamma → evalExtN v A = BoolVal.T

/-- Definition 3.5.8: A set Gamma of propositions is satisfiable iff
    some valuation makes all propositions in Gamma true. -/
@[blueprint "chap3__definition_3_5_8" (main := true)]
def setSatisfiable (Gamma : Set PropFormulaNormalized) : Prop :=
  ∃ v : Valuation, setSatisfiedBy Gamma v

-- ========= Definition 3.5.9: Consistent Set of Propositions =========

/-- Definition 3.5.9 (companion): Provability from a set of
    propositions. setProvable Gamma B holds when there exists a finite
    list of propositions from Gamma such that the sequent
    A1, ..., Am -> B is provable. -/
@[blueprint "chap3__definition_3_5_9"]
def setProvable (Gamma : Set PropFormulaNormalized) (B : PropFormulaNormalized) : Prop :=
  ∃ (Gamma_fin : List PropFormulaNormalized),
    (∀ A ∈ Gamma_fin, A ∈ Gamma) ∧
    sequentProvable (Sequent.mk Gamma_fin [B])

/-- Definition 3.5.9: A set Gamma of propositions is consistent if
    there exists some proposition B such that the sequent Gamma -> B
    is not provable (i.e., A1, ..., Am -> B is not provable for any
    finite subsequence A1, ..., Am of Gamma). -/
@[blueprint "chap3__definition_3_5_9" (main := true)]
def setConsistent (Gamma : Set PropFormulaNormalized) : Prop :=
  ∃ B : PropFormulaNormalized, ¬ setProvable Gamma B

/-- Definition 3.5.9: A set Gamma is inconsistent iff it
    is not consistent, i.e., for every proposition B, the sequent
    Gamma -> B is provable from some finite subsequence. -/
@[blueprint "chap3__definition_3_5_9" (main := true)]
def setInconsistent (Gamma : Set PropFormulaNormalized) : Prop :=
  ¬ setConsistent Gamma

-- ========= Definition 3.5.10: Maximally Consistent Sets =========

/-- Definition 3.5.10: A consistent set Gamma of propositions is
    maximally consistent iff, for every consistent set Delta, if Gamma
    is a subset of Delta then Gamma = Delta. Equivalently, every proper
    superset of Gamma is inconsistent. -/
@[blueprint "chap3__definition_3_5_10" (main := true)]
def maximallyConsistent (Gamma : Set PropFormulaNormalized) : Prop :=
  setConsistent Gamma ∧
  (∀ Delta : Set PropFormulaNormalized, setConsistent Delta → Gamma ⊆ Delta →
    Gamma = Delta)

-- ========= Theorem 3.5.3 (required def): Finite Subset Satisfiability =========

/-- Theorem 3.5.3 (required): The hypothesis that every finite nonempty
    subset of Gamma is satisfiable. Used as the antecedent of the
    compactness theorem. -/
@[blueprint "chap3__theorem_3_5_3"]
def finiteSubsetSatisfiable (Gamma : Set PropFormulaNormalized) : Prop :=
  ∀ (S : Set PropFormulaNormalized),
    S ⊆ Gamma → Set.Finite S → (∃ A, A ∈ S) → setSatisfiable S

-- ========= Lemma 3.5.5 (required def): All Satisfied Propositions =========

/-- Lemma 3.5.5 (required): The set Delta = {A | evalExtN v A = T} of
    all propositions satisfied by a valuation v. This is the set used
    in the proof that every consistent set extends to a maximal
    consistent set. -/
@[blueprint "chap3__lemma_3_5_5"]
def allSatisfiedPropositions (v : Valuation) : Set PropFormulaNormalized :=
  fun A => evalExtN v A = BoolVal.T

-- ========= Helpers for Compactness =========











-- ========= Helpers for compactness proof =========









-- ========= Theorem 3.5.3: Compactness Theorem for G' =========

/-- Theorem 3.5.3 (Compactness theorem for G'): For any (possibly
    infinite) set Gamma of propositions, if every finite nonempty subset
    of Gamma is satisfiable, then Gamma is satisfiable. The proof builds
    a valuation v variable-by-variable, at each step choosing T or F to
    preserve finite-subset satisfiability. Then evalExt_depends_on_vars
    lifts to the limit. -/
@[blueprint "chap3__theorem_3_5_3" (main := true)]
theorem compactness_G (Gamma : Set PropFormulaNormalized)
    (h : finiteSubsetSatisfiable Gamma) : setSatisfiable Gamma 

-- ========= Theorem 3.5.4: Model Existence Theorem for G' =========

/-- Theorem 3.5.4 (Model existence theorem for G'): If a set Gamma of
    propositions is consistent then it is satisfiable. The proof shows
    that consistency implies finite-subset satisfiability (using soundness
    and completeness), then applies compactness_G. -/
@[blueprint "chap3__theorem_3_5_4" (main := true)]
theorem model_existence_G (Gamma : Set PropFormulaNormalized)
    (hCon : setConsistent Gamma)
    : setSatisfiable Gamma 

-- ========= Lemma 3.5.4: Consistency Lemma for G' =========

/-- Lemma 3.5.4 (Consistency lemma for G'): If a set Gamma of
    propositions is satisfiable then it is consistent. By contradiction:
    assume Gamma is inconsistent, so for all B, Gamma -> B is provable.
    By soundness of G', these finite sequents are valid. But Gamma is
    satisfiable by hypothesis, so there is a valuation v making all of
    Gamma true. This valuation falsifies the sequent Gamma -> B for a
    suitably chosen B, contradicting validity. -/
@[blueprint "chap3__lemma_3_5_4" (main := true)]
theorem consistency_lemma_G (Gamma : Set PropFormulaNormalized)
    (hSat : setSatisfiable Gamma) : setConsistent Gamma 

-- ========= Definition 3.5.10 (companion theorem): Maximal Consistency Equivalence =========

/-- Definition 3.5.10 (companion): A set Gamma is maximally consistent
    if and only if Gamma is consistent and every proper superset of Gamma
    is inconsistent. -/
@[blueprint "chap3__definition_3_5_10" (main := true)]
theorem maximallyConsistent_iff_proper_superset_inconsistent
    (Gamma : Set PropFormulaNormalized) :
    maximallyConsistent Gamma ↔
    (setConsistent Gamma ∧
     (∀ Delta : Set PropFormulaNormalized, Gamma ⊆ Delta → Gamma ≠ Delta →
       setInconsistent Delta)) 

-- ========= Lemma 3.5.5: Maximal Consistent Extension =========

/-- Lemma 3.5.5: Every consistent set of propositions is a subset of
    some maximal consistent set Delta. From consistency of Gamma, apply
    model_existence_G to get a satisfying valuation v. Define
    Delta = allSatisfiedPropositions v = {A | evalExtN v A = T}. Then
    Gamma is a subset of Delta (because v satisfies all of Gamma), Delta
    is consistent (by consistency_lemma_G), and Delta is maximally
    consistent (any proper consistent superset leads to contradiction
    since v determines a unique complete truth assignment). -/
@[blueprint "chap3__lemma_3_5_5" (main := true)]
theorem maximal_consistent_extension (Gamma : Set PropFormulaNormalized)
    (hCon : setConsistent Gamma) :
    ∃ Delta : Set PropFormulaNormalized,
      Gamma ⊆ Delta ∧ maximallyConsistent Delta 

end LCS.Propositional.Infinite.Compactness

-- ========= Extended Completeness via Compactness =========
-- These theorems were originally in SignedFormulae.lean but require
-- compactness_G from Compactness.lean to prove. They live in the
-- SignedFormulae namespace for compatibility.

namespace LCS.Propositional.Infinite.SignedFormulae

open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search
open LCS.Propositional.Infinite
open LCS.Propositional.Infinite.Compactness
open Classical

-- Helper: extract the underlying formula from a negation, if present


-- Helper: classically filter a list by a predicate
noncomputable def classicalFilter (p : α → Prop) : List α → List α
  | [] => []
  | a :: as => if p a then a :: classicalFilter p as else classicalFilter p as

theorem mem_classicalFilter (p : α → Prop) (L : List α) (a : α) :
    a ∈ classicalFilter p L ↔ a ∈ L ∧ p a := by
-- BEGIN PROOF
  induction L with
  | nil => simp [classicalFilter]
  | cons b bs ih =>
    simp only [classicalFilter]
    split
    · rename_i hb
      constructor
      · intro h
        rw [List.mem_cons] at h
        rcases h with rfl | h
        · exact ⟨List.mem_cons_self, hb⟩
        · exact ⟨List.mem_cons_of_mem _ (ih.mp h).1, (ih.mp h).2⟩
      · intro ⟨h1, h2⟩
        rw [List.mem_cons] at h1
        rcases h1 with rfl | h1
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih.mpr ⟨h1, h2⟩)
    · rename_i hb
      constructor
      · intro h; exact ⟨List.mem_cons_of_mem _ (ih.mp h).1, (ih.mp h).2⟩
      · intro ⟨h1, h2⟩
        rw [List.mem_cons] at h1
        rcases h1 with rfl | h1
        · exact absurd h2 hb
        · exact ih.mpr ⟨h1, h2⟩

-- Helper: classically filterMap a list
noncomputable def classicalFilterMap (f : α → Option β) : List α → List β
  | [] => []
  | a :: as =>
    match f a with
    | some b => b :: classicalFilterMap f as
    | none => classicalFilterMap f as

theorem mem_classicalFilterMap (f : α → Option β) (L : List α) (b : β) :
    b ∈ classicalFilterMap f L ↔ ∃ a ∈ L, f a = some b := by
-- BEGIN PROOF
  induction L with
  | nil => simp [classicalFilterMap]
  | cons x xs ih =>
    simp only [classicalFilterMap]
    cases hfx : f x with
    | none =>
      simp only [hfx]
      constructor
      · intro h; obtain ⟨a, ha, hfa⟩ := ih.mp h
        exact ⟨a, List.mem_cons_of_mem _ ha, hfa⟩
      · intro ⟨a, ha, hfa⟩
        rw [List.mem_cons] at ha
        rcases ha with rfl | ha'
        · rw [hfa] at hfx; exact absurd hfx (by simp)
        · exact ih.mpr ⟨a, ha', hfa⟩
    | some b' =>
      simp only [hfx]
      constructor
      · intro h
        rw [List.mem_cons] at h
        rcases h with rfl | h
        · exact ⟨x, List.mem_cons_self, hfx⟩
        · obtain ⟨a, ha, hfa⟩ := ih.mp h
          exact ⟨a, List.mem_cons_of_mem _ ha, hfa⟩
      · intro ⟨a, ha, hfa⟩
        rw [List.mem_cons] at ha
        rcases ha with rfl | ha'
        · rw [hfa] at hfx
          rw [List.mem_cons]
          left; exact Option.some.inj hfx
        · rw [List.mem_cons]
          right; exact ih.mpr ⟨a, ha', hfa⟩

-- ========= Theorem 3.5.1 infrastructure: Valid-or-falsifiable dichotomy =========









-- ========= Theorem 3.5.1: Sub-lemmas for search_theorem_3_5_1 =========















































-- ========= Theorem 3.5.1: Main Statement =========

/-- Theorem 3.5.1: Search either produces a countermodel from an actual
    path, or closes and proves the consumed finite subsequent.

    For infinite falsifiable input the address-domain limit is infinite,
    and a coherent infinite path yields a Hintikka union and its canonical
    countermodel. For finite falsifiable input a terminal path in a finished
    stage supplies the corresponding Hintikka union and canonical countermodel. -/
@[blueprint "chap3__theorem_3_5_1" (main := true)]
theorem search_theorem_3_5_1 (seq : InfSequent) :
    (infSeqFalsifiable seq ∧
      (¬ infSeqIsFinite seq →
        ¬ infSearchHalts seq ∧ ¬ Set.Finite (infSearchTreeDomain seq).isNode ∧
        ∃ (address : Nat → List Nat) (label : Nat → Sequent),
          (infSearchTreeDomain seq).InfinitePath address ∧
          (∀ n, infSearchLimit seq (address n) (label n)) ∧
          IsHintikkaSet (fun sf => ∃ n, occurs (label n) sf) ∧
          infSeqFalsifies
            (hintikkaCanonicalValuation (fun sf => ∃ n, occurs (label n) sf)) seq) ∧
      (infSeqIsFinite seq → ∃ k leaf labels,
        infIsFinishedTree (infSearchSteps seq k) ∧
        SearchTreePath (infSearchSteps seq k).tree leaf labels ∧
        ¬ isAxiom leaf ∧ IsHintikkaSet (sequentListSignedSet labels) ∧
        infSeqFalsifies (hintikkaCanonicalValuation (sequentListSignedSet labels)) seq))
    ∨
    (infSeqValid seq ∧
      ∃ k, infIsFinishedTree (infSearchSteps seq k) ∧
        isClosedTree (infSearchSteps seq k).tree ∧
        sequentProvable (Sequent.mk
          (initialPrefix seq.antecedent (k + 1))
          (initialPrefix seq.succedent (k + 1)))) 

-- ========= Theorem 3.5.2: Extended Completeness for G' =========

/-- Theorem 3.5.2 (Extended completeness theorem for G'): For every
    (possibly infinite) sequent Gamma -> Delta, the sequent is valid
    if and only if it is provable (in the extended sense for infinite
    sequents). The forward direction uses valid_sequent_provable from
    Theorem 3.5.1. The reverse direction uses soundness of G' plus the
    definition of infinite sequent provability. -/
@[blueprint "chap3__theorem_3_5_2" (main := true)]
theorem extended_completeness_G (seq : InfSequent)
    : infSeqValid seq ↔ infSeqProvable seq 

end LCS.Propositional.Infinite.SignedFormulae
