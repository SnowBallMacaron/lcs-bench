import LCS.Propositional.Systems.G.Search.Termination
import LCS.Propositional.Systems.G.Search.SearchRounds.Proofs
import LCS.Propositional.Systems.G.Search.Validity.Proofs

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- Collects all sequents along a path in a deduction tree, from root
    to the node reached by following the path directions. -/
def sequentsAlongPath' : {s : Sequent} → DeductionTree s → Path' → List Sequent
  | _, .leaf s, _ => [s]
  | _, .onePremise _ child, dirs => child.conclusion :: sequentsAlongPath' child dirs
  | _, .twoPremise _ left _, [] => [left.conclusion]
  | _, .twoPremise _ left _, .left :: rest =>
    left.conclusion :: sequentsAlongPath' left rest
  | _, .twoPremise _ _ right, .right :: rest =>
    right.conclusion :: sequentsAlongPath' right rest

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- The last sequent reached by following a path. This is the leaf or
    the node where the path ends. -/
def sequentAtEndOfPath {s : Sequent} (dt : DeductionTree s) (p : Path') : Sequent :=
  match (sequentsAlongPath' dt p).getLast? with
  | some s => s
  | none => dt.conclusion

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- The antecedent union along a path: all antecedent formulae from all
    sequents along the path. -/
def pathAntecedentUnion' {s : Sequent} (dt : DeductionTree s) (p : Path') :
    Set PropFormulaNormalized :=
  fun A => ∃ s ∈ sequentsAlongPath' dt p, A ∈ s.antecedent

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- The succedent union along a path: all succedent formulae from all
    sequents along the path. -/
def pathSuccedentUnion' {s : Sequent} (dt : DeductionTree s) (p : Path') :
    Set PropFormulaNormalized :=
  fun B => ∃ s ∈ sequentsAlongPath' dt p, B ∈ s.succedent

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- Given a deduction tree and evidence that a sequent s is among its
    leaves, produce a path from root to that leaf. For a leaf tree, the
    path is []. For onePremise, recurse into the subtree. For twoPremise,
    determine which subtree contains the leaf and go left or right. -/
def pathToLeaf : {c : Sequent} → (dt : DeductionTree c) → (s : Sequent) →
    (h : s ∈ dt.leaves) → Path'
  | _, .leaf _, _, _ => []
  | _, .onePremise _ child, s, h => pathToLeaf child s h
  | _, .twoPremise _ left right, s, h =>
    if hmem : s ∈ left.leaves then
      .left :: pathToLeaf left s hmem
    else
      have : s ∈ right.leaves := by
        simp only [DeductionTree.leaves] at h
        rcases List.mem_append.mp h with hL | hR
        · exact absurd hL hmem
        · exact hR
      .right :: pathToLeaf right s this

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem sequentsAlongPath'_ne_nil {s : Sequent} (dt : DeductionTree s) (p : Path') :
    sequentsAlongPath' dt p ≠ [] := by
-- BEGIN PROOF
  cases dt with
  | leaf s => simp [sequentsAlongPath']
  | onePremise _ child => simp [sequentsAlongPath']
  | twoPremise _ left right =>
    cases p with
    | nil => simp [sequentsAlongPath']
    | cons d rest =>
      cases d with
      | left => simp [sequentsAlongPath']
      | right => simp [sequentsAlongPath']

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- The last sequent along the path constructed by pathToLeaf is exactly
    the target leaf sequent. -/
theorem pathToLeaf_reaches_leaf {c : Sequent} (dt : DeductionTree c) (s : Sequent)
    (h : s ∈ dt.leaves) :
    (sequentsAlongPath' dt (pathToLeaf dt s h)).getLast
      (sequentsAlongPath'_ne_nil dt (pathToLeaf dt s h)) = s := by
-- BEGIN PROOF
  induction dt with
  | leaf s' =>
    simp [DeductionTree.leaves] at h
    subst h
    simp [sequentsAlongPath']
  | onePremise rule child ih =>
    simp only [DeductionTree.leaves] at h
    simp only [pathToLeaf, sequentsAlongPath']
    rw [List.getLast_cons]
    exact ih h
  | twoPremise rule left right ihL ihR =>
    simp only [DeductionTree.leaves] at h
    simp only [pathToLeaf]
    split
    · case isTrue hmem =>
      simp only [sequentsAlongPath']
      rw [List.getLast_cons]
      exact ihL hmem
    · case isFalse hmem =>
      have hright : s ∈ right.leaves := by
        rcases List.mem_append.mp h with hL | hR
        · exact absurd hL hmem
        · exact hR
      simp only [sequentsAlongPath']
      rw [List.getLast_cons]
      exact ihR hright

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem leaf_mem_sequentsAlongPath' {c : Sequent} (dt : DeductionTree c) (s : Sequent)
    (h : s ∈ dt.leaves) :
    s ∈ sequentsAlongPath' dt (pathToLeaf dt s h) := by
-- BEGIN PROOF
  have heq := pathToLeaf_reaches_leaf dt s h
  have hmem := List.getLast_mem (sequentsAlongPath'_ne_nil dt (pathToLeaf dt s h))
  rw [heq] at hmem
  exact hmem

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- Every antecedent formula of the target leaf sequent appears in the
    antecedent union along the path, and every succedent formula appears
    in the succedent union. This is the content of
    leaf_signedSet_subset_pathSignedSet stated without importing
    SignedFormula. -/
theorem leaf_signedSet_subset_pathSignedSet {c : Sequent} (dt : DeductionTree c) (s : Sequent)
    (h : s ∈ dt.leaves) :
    (∀ A ∈ s.antecedent, pathAntecedentUnion' dt (pathToLeaf dt s h) A) ∧
    (∀ B ∈ s.succedent, pathSuccedentUnion' dt (pathToLeaf dt s h) B) := by
-- BEGIN PROOF
  have hmem := leaf_mem_sequentsAlongPath' dt s h
  exact ⟨
    fun A hA => ⟨s, hmem, hA⟩,
    fun B hB => ⟨s, hmem, hB⟩
  ⟩

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem foldl_max_shift (L : List Nat) (a : Nat) :
    L.foldl max a = max a (L.foldl max 0) := by
-- BEGIN PROOF
  induction L generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (max a x), ih (max 0 x)]
    omega

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem le_foldl_max_of_mem {L : List Nat} {x : Nat}
    (hx : x ∈ L) : x ≤ L.foldl max 0 := by
  induction L with
  | nil => simp_all
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rw [foldl_max_shift]
    cases List.mem_cons.mp hx with
    | inl h => subst h; omega
    | inr h => have := ih h; omega

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem foldl_max_lt_of_all_lt {L : List Nat} {bound : Nat}
    (hne : L ≠ [])
    (hall : ∀ x ∈ L, x < bound) :
    L.foldl max 0 < bound := by
-- BEGIN PROOF
  induction L with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [foldl_max_shift]
    have hx := hall x (List.Mem.head _)
    cases xs with
    | nil => simp; omega
    | cons y ys =>
      have hxs := ih (List.cons_ne_nil y ys)
        (fun z hz => hall z (List.Mem.tail _ hz))
      omega

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem unfinished_pos_complexity (s : Sequent)
    (hunf : ¬isFinishedLeafBool mode s = true) :
    sequentComplexity s > 0 :=
-- BEGIN PROOF
  Classical.byContradiction fun hle => by
    have hzero : sequentComplexity s = 0 := by omega
    have ⟨hAnt0, hSucc0⟩ := sequentComplexity_zero_all_zero s hzero
    have hAllVar : ∀ A ∈ s.antecedent ++ s.succedent, isAtomicFormula A := by
      intro A hA
      cases List.mem_append.mp hA with
      | inl hAntA =>
        obtain ⟨n, rfl⟩ := complexity_zero_is_var A (hAnt0 A hAntA)
        exact trivial
      | inr hSuccA =>
        obtain ⟨n, rfl⟩ := complexity_zero_is_var A (hSucc0 A hSuccA)
        exact trivial
    exact hunf ((isFinishedLeafBool_iff s).mpr (Or.inr hAllVar))

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem sequent_ant_eq (s : Sequent) (i : Nat) (A : PropFormulaNormalized)
    (hi : i < s.antecedent.length) (hA : s.antecedent[i] = A) :
    s = Sequent.mk (s.antecedent.take i ++ [A] ++ s.antecedent.drop (i + 1)) s.succedent := by
-- BEGIN PROOF
  rcases s with ⟨ant, succ⟩; subst hA
  exact congrArg (Sequent.mk · succ) (take_elem_drop ant i hi).symm

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem sequent_succ_eq (s : Sequent) (j : Nat) (B : PropFormulaNormalized)
    (hj : j < s.succedent.length) (hB : s.succedent[j] = B) :
    s = Sequent.mk s.antecedent (s.succedent.take j ++ [B] ++ s.succedent.drop (j + 1)) := by
-- BEGIN PROOF
  rcases s with ⟨ant, succ⟩; subst hB
  exact congrArg (Sequent.mk ant) (take_elem_drop succ j hj).symm

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- The conclusion (root label) of expandLeaf s is s itself. Under the
    indexed form, the conclusion is the type index, so this is `rfl`. -/
theorem expandLeaf_conclusion (s : Sequent) :
    (expandLeaf mode s).conclusion = s := rfl

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- The deduction tree produced by expandLeaf is well-formed (WFTree).
    Under the indexed `DeductionTree : Sequent → Type`, the rule's premise/
    conclusion are recorded as type indices, so `WFTree` well-formedness
    reduces to a trivial structural induction: every `.leaf`, `.onePremise`,
    `.twoPremise` is automatically well-formed because its children are. -/
theorem expandLeaf_wf (s : Sequent) : WFTree (expandLeaf mode s) := by
-- BEGIN PROOF
  -- Generic helper: every DeductionTree is automatically well-formed.
  suffices h : ∀ {c : Sequent} (dt : DeductionTree c), WFTree dt by exact h _
  intro c dt
  induction dt with
  | leaf _ => exact WFTree.leaf _
  | onePremise rule _ ih => exact WFTree.step1 rule ih
  | twoPremise rule _ _ ih1 ih2 => exact WFTree.step2 rule ih1 ih2

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem nonatomic_pos_complexity (A : PropFormulaNormalized)
    (h : isNonatomicBool A = true) : formulaComplexity A > 0 := by
-- BEGIN PROOF
  cases A with
  | var _ => simp [isNonatomicBool] at h
  | neg _ => simp [formulaComplexity]; omega
  | conj _ _ => simp [formulaComplexity]; omega
  | disj _ _ => simp [formulaComplexity]; omega
  | impl _ _ => simp [formulaComplexity]; omega

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- Every leaf of expandLeaf s has strictly smaller sequent complexity than s,
    provided s is not a finished leaf. -/
theorem expandFirstFormula_leaves_complexity_lt (s : Sequent)
    (hunf : ¬isFinishedLeafBool mode s = true) :
    ∀ leaf ∈ (expandFirstFormula s).leaves,
      sequentComplexity leaf < sequentComplexity s := by
-- BEGIN PROOF
  unfold expandFirstFormula expandSelected
  split
  · case h_1 A i hfind =>
    have ⟨hi, hget, hna⟩ := findFirstNonatomic_spec s.antecedent A i hfind
    have hA : s.antecedent[i] = A := by
      rw [List.getElem?_eq_getElem hi] at hget; exact Option.some.inj hget
    have hs := sequent_ant_eq s i A hi hA
    cases A with
    | neg C =>
      dsimp only []; simp only [DeductionTree.leaves_eq_rec, DeductionTree.leaves]
      intro leaf hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; subst hmem
      rw [congrArg sequentComplexity hs]
      exact step1_complexity_decrease (GentzenStep1.negLeft (s.antecedent.take i) (s.antecedent.drop (i + 1)) s.succedent C)
    | conj C D =>
      dsimp only []; simp only [DeductionTree.leaves_eq_rec, DeductionTree.leaves]
      intro leaf hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; subst hmem
      rw [congrArg sequentComplexity hs]
      exact step1_complexity_decrease (GentzenStep1.andLeft (s.antecedent.take i) (s.antecedent.drop (i + 1)) s.succedent C D)
    | disj C D =>
      dsimp only []; simp only [DeductionTree.leaves_eq_rec, DeductionTree.leaves]
      intro leaf hmem
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · rw [congrArg sequentComplexity hs]
        exact (step2_complexity_decrease (GentzenStep2.orLeft (s.antecedent.take i) (s.antecedent.drop (i + 1)) s.succedent C D)).1
      · rw [congrArg sequentComplexity hs]
        exact (step2_complexity_decrease (GentzenStep2.orLeft (s.antecedent.take i) (s.antecedent.drop (i + 1)) s.succedent C D)).2
    | impl C D =>
      dsimp only []; simp only [DeductionTree.leaves_eq_rec, DeductionTree.leaves]
      intro leaf hmem
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · rw [congrArg sequentComplexity hs]
        exact (step2_complexity_decrease (GentzenStep2.implLeft (s.antecedent.take i) (s.antecedent.drop (i + 1)) s.succedent C D)).1
      · rw [congrArg sequentComplexity hs]
        exact (step2_complexity_decrease (GentzenStep2.implLeft (s.antecedent.take i) (s.antecedent.drop (i + 1)) s.succedent C D)).2
    | var n => simp [isNonatomicBool] at hna
  · case h_2 hno_ant =>
    split
    · case h_1 B j hfind =>
      have ⟨hj, hget, hna⟩ := findFirstNonatomic_spec s.succedent B j hfind
      have hB : s.succedent[j] = B := by
        rw [List.getElem?_eq_getElem hj] at hget; exact Option.some.inj hget
      have hs := sequent_succ_eq s j B hj hB
      cases B with
      | neg C =>
        dsimp only []; simp only [DeductionTree.leaves_eq_rec, DeductionTree.leaves]
        intro leaf hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; subst hmem
        rw [congrArg sequentComplexity hs]
        exact step1_complexity_decrease (GentzenStep1.negRight s.antecedent (s.succedent.take j) (s.succedent.drop (j + 1)) C)
      | conj C D =>
        dsimp only []; simp only [DeductionTree.leaves_eq_rec, DeductionTree.leaves]
        intro leaf hmem
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · rw [congrArg sequentComplexity hs]
          exact (step2_complexity_decrease (GentzenStep2.andRight s.antecedent (s.succedent.take j) (s.succedent.drop (j + 1)) C D)).1
        · rw [congrArg sequentComplexity hs]
          exact (step2_complexity_decrease (GentzenStep2.andRight s.antecedent (s.succedent.take j) (s.succedent.drop (j + 1)) C D)).2
      | disj C D =>
        dsimp only []; simp only [DeductionTree.leaves_eq_rec, DeductionTree.leaves]
        intro leaf hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; subst hmem
        rw [congrArg sequentComplexity hs]
        exact step1_complexity_decrease (GentzenStep1.orRight s.antecedent (s.succedent.take j) (s.succedent.drop (j + 1)) C D)
      | impl C D =>
        dsimp only []; simp only [DeductionTree.leaves_eq_rec, DeductionTree.leaves]
        intro leaf hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; subst hmem
        rw [congrArg sequentComplexity hs]
        exact step1_complexity_decrease (GentzenStep1.implRight s.antecedent (s.succedent.take j) (s.succedent.drop (j + 1)) C D)
      | var n => simp [isNonatomicBool] at hna
    · case h_2 hno_succ =>
      -- Both findFirstNonatomic return none: all formulas are atomic
      -- But hunf says s is not finished, contradiction
      exfalso; apply hunf
      rw [isFinishedLeafBool_iff s]
      right
      intro A hA
      cases List.mem_append.mp hA with
      | inl hAnt => exact findFirstNonatomic_none_all_atomic _ _ hno_ant A hAnt
      | inr hSucc => exact findFirstNonatomic_none_all_atomic _ _ hno_succ A hSucc

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- All indexed deduction trees satisfy the structural well-formedness
    predicate. -/
theorem deductionTree_wf {c : Sequent} (dt : DeductionTree c) : WFTree dt := by
  induction dt with
  | leaf s => exact WFTree.leaf s
  | onePremise rule _ ih => exact WFTree.step1 rule ih
  | twoPremise rule _ _ ihL ihR => exact WFTree.step2 rule ihL ihR

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- Substitution preserves the root label. -/
theorem doSubstitution_conclusion {c target : Sequent} {dt : DeductionTree c}
    (address : NodeAddress dt target) (repl : DeductionTree target) :
    (doSubstitution address repl).conclusion = dt.conclusion := rfl

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- Substitution at an address gives a well-formed deduction tree. -/
theorem doSubstitution_wf {c target : Sequent} {dt : DeductionTree c}
    (address : NodeAddress dt target) (repl : DeductionTree target) :
    WFTree (doSubstitution address repl) := deductionTree_wf _

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- The leaves produced by structural substitution descend from one
    particular leaf of the input tree. -/
theorem mapLeaves_leaves {c : Sequent} (dt : DeductionTree c)
    (expand : (s : Sequent) → DeductionTree s) :
    ∀ leaf ∈ (mapLeaves expand dt).leaves,
      ∃ original ∈ dt.leaves, leaf ∈ (expand original).leaves := by
  induction dt with
  | leaf s =>
    intro leaf h
    exact ⟨s, by simp [DeductionTree.leaves], h⟩
  | onePremise rule child ih => exact ih
  | twoPremise rule left right ihL ihR =>
    intro leaf h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨s, hs, hleaf⟩ := ihL leaf h
      exact ⟨s, List.mem_append_left _ hs, hleaf⟩
    · obtain ⟨s, hs, hleaf⟩ := ihR leaf h
      exact ⟨s, List.mem_append_right _ hs, hleaf⟩

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- Every rule decreases complexity, so every leaf is bounded by its
    tree's root, independently of the schedule used to construct it. -/
theorem deductionTree_leaf_complexity_le {c : Sequent} (dt : DeductionTree c) :
    ∀ leaf ∈ dt.leaves, sequentComplexity leaf ≤ sequentComplexity c := by
  induction dt with
  | leaf s =>
    intro leaf h
    simp only [DeductionTree.leaves, List.mem_singleton] at h
    subst leaf
    exact Nat.le_refl _
  | onePremise rule child ih =>
    intro leaf h
    exact Nat.le_trans (ih leaf h) (Nat.le_of_lt (step1_complexity_decrease rule))
  | twoPremise rule left right ihL ihR =>
    intro leaf h
    rcases List.mem_append.mp h with h | h
    · exact Nat.le_trans (ihL leaf h) (Nat.le_of_lt (step2_complexity_decrease rule).1)
    · exact Nat.le_trans (ihR leaf h) (Nat.le_of_lt (step2_complexity_decrease rule).2)

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem expandSchedule_leaves_bound {c : Sequent}
    (schedule : List (Bool × Nat)) (dt : DeductionTree c) :
    ∀ leaf ∈ (expandSchedule mode schedule dt).leaves,
      ∃ original ∈ dt.leaves, sequentComplexity leaf ≤ sequentComplexity original := by
  induction schedule generalizing dt with
  | nil =>
    intro leaf h
    exact ⟨leaf, h, Nat.le_refl _⟩
  | cons entry rest ih =>
    intro leaf h
    obtain ⟨mid, hmid, hle⟩ := ih (mapLeaves (expandScheduled mode entry.1 entry.2) dt) leaf h
    obtain ⟨original, horiginal, hdesc⟩ := mapLeaves_leaves dt _ mid hmid
    exact ⟨original, horiginal,
      Nat.le_trans hle (deductionTree_leaf_complexity_le _ mid hdesc)⟩

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- A round strictly reduces the complexity of every descendant of an
    unfinished leaf. Its first effective rule decreases complexity; all
    remaining scheduled rules preserve that strict upper bound. -/
theorem expandLeaf_leaves_complexity_lt (s : Sequent)
    (hunf : ¬isFinishedLeafBool mode s = true) :
    ∀ leaf ∈ (expandLeaf mode s).leaves,
      sequentComplexity leaf < sequentComplexity s := by
  simp only [expandLeaf, hunf, Bool.false_eq_true, ↓reduceIte]
  intro leaf h
  obtain ⟨original, horiginal, hle⟩ := expandSchedule_leaves_bound _ _ leaf h
  exact Nat.lt_of_le_of_lt hle
    (expandFirstFormula_leaves_complexity_lt s hunf original horiginal)

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- searchRound preserves the root conclusion. -/
theorem searchRound_conclusion {c : Sequent} (dt : DeductionTree c) :
    (searchRound mode dt).conclusion = dt.conclusion := rfl

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- searchRound preserves well-formedness. -/
theorem searchRound_wf {c : Sequent} (dt : DeductionTree c) (_hwf : WFTree dt) :
    WFTree (searchRound mode dt) := deductionTree_wf _

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem unfinished_le_max {c : Sequent} (dt : DeductionTree c) (s : Sequent)
    (hs : s ∈ unfinishedLeaves mode dt) :
    sequentComplexity s ≤ maxUnfinishedLeafComplexity mode dt := by
  simp only [maxUnfinishedLeafComplexity]
  apply le_foldl_max_of_mem
  exact List.mem_map_of_mem (f := sequentComplexity) hs

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem not_finished_of_mem_unfinished {c : Sequent} {s : Sequent}
    {dt : DeductionTree c}
    (h : s ∈ unfinishedLeaves mode dt) : ¬isFinishedLeafBool mode s = true := by
-- BEGIN PROOF
  simp only [unfinishedLeaves, List.mem_filter] at h
  obtain ⟨_, hfilt⟩ := h
  intro htrue; rw [htrue] at hfilt; simp at hfilt

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem unfinishedLeaves_ne_nil {c : Sequent} (dt : DeductionTree c)
    (hunf : ¬isFinishedTreeBool mode dt = true) :
    unfinishedLeaves mode dt ≠ [] := by
-- BEGIN PROOF
  intro hempty; apply hunf
  simp only [isFinishedTreeBool, List.all_eq_true]
  intro s hs
  simp only [unfinishedLeaves] at hempty
  have := List.filter_eq_nil_iff.mp hempty s hs
  simp at this; exact this

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem searchRound_unfinished_lt_max {c : Sequent} (dt : DeductionTree c)
    (_hunf : ¬isFinishedTreeBool mode dt = true) :
    ∀ s ∈ unfinishedLeaves mode (searchRound mode dt),
      sequentComplexity s < maxUnfinishedLeafComplexity mode dt := by
-- BEGIN PROOF
  intro s hs
  have hs_leaf : s ∈ (searchRound mode dt).leaves := by
    simp only [unfinishedLeaves, List.mem_filter] at hs; exact hs.1
  have hs_unf : ¬isFinishedLeafBool mode s = true := not_finished_of_mem_unfinished hs
  obtain ⟨original, horiginal, hdesc⟩ := mapLeaves_leaves dt (expandLeaf mode) s hs_leaf
  by_cases hfin : isFinishedLeafBool mode original = true
  · rw [expandLeaf_of_finished original hfin] at hdesc
    simp only [DeductionTree.leaves, List.mem_singleton] at hdesc
    subst original
    exact False.elim (hs_unf hfin)
  · have hmem : original ∈ unfinishedLeaves mode dt := by
      simp [unfinishedLeaves, horiginal, hfin]
    exact Nat.lt_of_lt_of_le
      (expandLeaf_leaves_complexity_lt original hfin s hdesc)
      (unfinished_le_max dt original hmem)

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem max_pos_of_unfinished {c : Sequent} (dt : DeductionTree c)
    (hunf : ¬isFinishedTreeBool mode dt = true) :
    maxUnfinishedLeafComplexity mode dt > 0 := by
-- BEGIN PROOF
  have hne := unfinishedLeaves_ne_nil dt hunf
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ hne
  exact Nat.lt_of_lt_of_le
    (unfinished_pos_complexity s (not_finished_of_mem_unfinished hs))
    (unfinished_le_max dt s hs)

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of searchRound_complexity_decrease := by
  -- BEGIN PROOF
    have hmax_pos := max_pos_of_unfinished dt hunf
    simp only [maxUnfinishedLeafComplexity]
    by_cases hne :
      (unfinishedLeaves mode (searchRound mode dt)).map sequentComplexity = []
    · simp [hne]; exact hmax_pos
    · exact foldl_max_lt_of_all_lt hne (fun x hx => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
        exact searchRound_unfinished_lt_max dt hunf s hs)

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper theorem search_of_finished {c : Sequent} (dt : DeductionTree c)
    (h : isFinishedTreeBool mode dt = true) :
    search mode dt = dt := by
-- BEGIN PROOF
  simp [search, h]

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of search_produces_finished_tree_example := by
  -- BEGIN PROOF
    have h0 : isFinishedTreeBool .systematic (DeductionTree.leaf exSearchTraceSequent) = false := by decide
    have h1 : isFinishedTreeBool .systematic exSearchTraceRound1 = false := by decide
    have h2 : isFinishedTreeBool .systematic exSearchTraceRound2 = true := by decide
    apply (isFinishedTreeBool_iff_isFinishedTree _).mp
    unfold searchStart
    rw [search, h0]
    change isFinishedTreeBool .systematic (search .systematic exSearchTraceRound1) = true
    rw [search, h1]
    change isFinishedTreeBool .systematic (search .systematic exSearchTraceRound2) = true
    rw [search_of_finished _ h2]
    exact h2

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- The search procedure terminates: starting from any sequent, search
    produces a finished tree. Proved by strong induction on
    maxUnfinishedLeafComplexity. -/
theorem search_terminates (s : Sequent) :
    isFinishedTree mode (search mode (DeductionTree.leaf s)) := by
-- BEGIN PROOF
  suffices h : ∀ (n : Nat) {c : Sequent} (dt : DeductionTree c),
      maxUnfinishedLeafComplexity mode dt = n →
      isFinishedTree mode (search mode dt) by
    exact h _ _ rfl
  intro n; induction n using Nat.strongRecOn with | ind n ih =>
  intro c dt hn
  by_cases hfin : isFinishedTreeBool mode dt = true
  · rw [search_of_finished dt hfin]
    exact (isFinishedTreeBool_iff_isFinishedTree dt).mp hfin
  · have hprog := searchRound_complexity_decrease dt hfin
    rw [search.eq_1 mode dt]
    simp only [hfin]
    exact ih _ (by omega) _ rfl

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- search preserves the root conclusion of the deduction tree. Under the
    indexed form, this is `rfl`. -/
theorem search_conclusion {c : Sequent} (dt : DeductionTree c) :
    (search mode dt).conclusion = dt.conclusion := rfl

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- search preserves WFTree. -/
theorem search_wf {c : Sequent} (dt : DeductionTree c) (_hwf : WFTree dt) :
    WFTree (search mode dt) := deductionTree_wf _

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of searchStart_atomic_closed := by
  simpa [isFinishedTree, isFinishedLeaf, searchStart] using
    (search_terminates (mode := .atomic) s)

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of search_theorem_3_4_1 := by
  -- BEGIN PROOF
    intro T
    have hwf : WFTree T := search_wf _ (WFTree.leaf s)
    have hconc : T.conclusion = s := search_conclusion _
    have hfin : isFinishedTree mode T := search_terminates s
    refine ⟨hfin, ?_, ?_⟩
    · -- Part 2: valid → isProofTree
      -- For each leaf l, if it were not an axiom, then since it's finished it
      -- must be all-atomic. By the contrapositive of valid_atomic_is_axiom,
      -- it is not valid, hence falsifiable. But by deductionTree_falsification_iff,
      -- any falsification of a leaf propagates to the root, contradicting validity.
      intro hv l hl
      exact Classical.byContradiction fun hna => by
        rcases hfin l hl with hax | hallat
        · exact hna hax.2
        · have hAllVar : ∀ A ∈ l.antecedent ++ l.succedent, ∃ n, A = .var n := by
            intro A hA; have hat := hallat A hA
            cases A with | var n => exact ⟨n, rfl⟩ | _ => simp [isAtomicFormula] at hat
          have hnv_l : ¬sequentValid l := fun hvl => hna (valid_atomic_is_axiom l hvl hAllVar)
          obtain ⟨v, hfals_l⟩ := search_falsifying_extraction l hnv_l
          have hfals_root := (deductionTree_falsification_iff v T hwf).mpr ⟨l, hl, hfals_l⟩
          rw [hconc] at hfals_root
          obtain ⟨hAnt, hSucc⟩ := hfals_root
          obtain ⟨B, hBmem, hBT⟩ := hv v hAnt
          have hBF := hSucc B hBmem; rw [hBT] at hBF; exact absurd hBF (by decide)
    · -- Part 3: ¬valid → falsifying valuations found in nonAxiomLeaves
      -- Given v falsifying s, propagate through the tree to find a leaf l
      -- falsified by v. Since l is falsified, it cannot be an axiom (an axiom
      -- has a shared formula evaluated both T and F). So l ∈ nonAxiomLeaves.
      intro _hnv v hfals_s
      have hfals_root : sequentFalsifiedBy T.conclusion v := by rw [hconc]; exact hfals_s
      obtain ⟨l, hl, hfals_l⟩ := (deductionTree_falsification_iff v T hwf).mp hfals_root
      have hna : ¬isAxiom l := by
        intro ⟨A, hA_ant, hA_succ⟩
        obtain ⟨hAnt, hSucc⟩ := hfals_l
        have hT := hAnt A hA_ant; have hF := hSucc A hA_succ
        rw [hT] at hF; exact absurd hF (by decide)
      have hl_na : l ∈ nonAxiomLeaves T := by
        simp only [nonAxiomLeaves, List.mem_filter]; refine ⟨hl, ?_⟩
        simp only [Bool.not_eq_true']; rw [Bool.eq_false_iff]; intro htrue
        apply hna; rw [List.any_eq_true] at htrue; obtain ⟨A, hA, htrue2⟩ := htrue
        rw [List.any_eq_true] at htrue2; obtain ⟨B, hB, hab⟩ := htrue2
        rw [beq_iff_eq] at hab; exact ⟨A, hA, hab ▸ hB⟩
      exact ⟨l, hl_na, hfals_l⟩

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

proof_of corollary_completeness_G := search_valid_iff_proofTree s

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

helper /-- Split a frozen schedule into consecutive passes. -/
theorem expandSchedule_append {c : Sequent} (xs ys : List (Bool × Nat))
    (dt : DeductionTree c) :
    expandSchedule mode (xs ++ ys) dt =
      expandSchedule mode ys (expandSchedule mode xs dt) := by
  simp [expandSchedule, List.foldl_append]

end LCS.Propositional.Systems.G.Search
end
