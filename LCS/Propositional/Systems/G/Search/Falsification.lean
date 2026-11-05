import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import Attach
import LCS.Propositional.Systems.G.Search.Falsification.ProofsStamp
import LCS.Propositional.Systems.G.Search.LeafExpansion
import LCS.Propositional.Systems.G.Search.SearchRounds
import LCS.Propositional.Systems.G.Search.Validity
attach_helper_namespace LCS.Propositional.Systems.G.Search.Proofs

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
variable {mode : SearchMode}

/-- Theorem 3.4.1 (companion): checkSequentValid is correct: it returns
    true if and only if the sequent is valid. -/
@[blueprint "chap3__theorem_3_4_1"]
theorem checkSequentValid_correct (s : Sequent) :
    checkSequentValid s = true ↔ sequentValid s 

/-- Theorem 3.4.1 (companion): Decidability of sequent validity.
    Computable instance using checkSequentValid which enumerates all
    valuations over the sequent's variable indices. -/
@[blueprint "chap3__theorem_3_4_1"]
instance decidability_sequent_validity (s : Sequent) :
    Decidable (sequentValid s) :=
  decidable_of_iff (checkSequentValid s = true) (checkSequentValid_correct s)

-- ========= Theorem 3.4.1: Constructive falsifying extraction =========

-- Helper: extract falsification evidence from checkSequentValidFor = false


/-- Theorem 3.4.1 (companion): A sequent that is not valid is falsifiable.
    If the sequent is not valid, there exists a valuation falsifying it.

    The falsifying valuation is extracted constructively from the truth-table
    enumeration: checkSequentValid enumerates all valuations over the sequent's
    variable indices, and from ¬sequentValid s we derive that the check fails,
    yielding a specific valuation in the enumeration where all antecedent
    formulas evaluate to T and all succedent formulas evaluate to F. This
    avoids the classical extraction pattern (Classical.not_forall /
    Classical.not_imp) used in the previous version; the witness comes
    from the computable enumeration, not from double-negation elimination. -/
@[blueprint "chap3__theorem_3_4_1"]
theorem search_falsifying_extraction (s : Sequent)
    (hf : ¬sequentValid s) :
    sequentFalsifiable s 

/-- Theorem 3.4.1 (companion): For every standard sequent, either it is
    provable in G' (if valid) or it is falsifiable (if not valid). This
    captures the content of the textbook's Theorem 3.4.1 -- that the search
    procedure terminates and decides validity -- in a search-independent
    formulation. -/
@[blueprint "chap3__theorem_3_4_1"]
theorem search_termination_and_completeness (s : Sequent) :
    (sequentValid s → sequentProvable s) ∧
    (¬sequentValid s → sequentFalsifiable s) 

-- ========= Lemma 3.4.1: Per-valuation rule falsification =========

/-- Lemma 3.4.1: For each G' one-premise rule and any valuation `v`,
    `v` falsifies the conclusion iff `v` falsifies the premise. The
    textbook lemma is one uniform "conclusion falsifiable iff some
    premise falsifiable" statement over ALL G' rules; we split it by
    premise-count because `GentzenStep1` and `GentzenStep2` have
    different arities. This is the one-premise half; see
    `rule_falsification_step2_iff` for the two-premise half. -/
@[blueprint "chap3__lemma_3_4_1" (main := true)]
theorem rule_falsification_step1_iff {prem conc : Sequent}
    (rule : GentzenStep1 prem conc) (v : Valuation) :
    sequentFalsifiedBy conc v ↔ sequentFalsifiedBy prem v 

/-- Lemma 3.4.1: For each G' two-premise rule and any valuation `v`,
    `v` falsifies the conclusion iff `v` falsifies at least one premise.
    Two-premise half of Lemma 3.4.1; see `rule_falsification_step1_iff`
    for the one-premise half. -/
@[blueprint "chap3__lemma_3_4_1" (main := true)]
theorem rule_falsification_step2_iff {p1 p2 conc : Sequent}
    (rule : GentzenStep2 p1 p2 conc) (v : Valuation) :
    sequentFalsifiedBy conc v ↔
    (sequentFalsifiedBy p1 v ∨ sequentFalsifiedBy p2 v) 

-- ========= Example 3.4.4: Companion theorems =========

/-- Example 3.4.4 (companion): After the first round of search applied to
    exSearchTraceSequent, the deduction tree has exactly three leaves. -/
@[blueprint "chap3__example_3_4_4"]
theorem exSearchTraceRound1_leaf_count :
    exSearchTraceRound1.leaves.length = 3 

/-- Example 3.4.4: The three leaves after the first complete formula pass,
    in the order displayed by the textbook. The first is already an axiom. -/
@[blueprint "chap3__example_3_4_4"]
theorem exSearchTraceRound1_leaves :
    let p := PropFormulaNormalized.var 0
    let q := PropFormulaNormalized.var 1
    let r := PropFormulaNormalized.var 2
    let s := PropFormulaNormalized.var 3
    let t := PropFormulaNormalized.var 4
    exSearchTraceRound1.leaves =
      [⟨[p, .neg q, .impl t r, .conj p s], [p, t]⟩,
       ⟨[q, p, .neg q, p, s], [t, t]⟩,
       ⟨[r, q, p, .neg q, p, s], [t]⟩] 

/-- Example 3.4.4: The second pass expands the surviving negations and
    preserves the first axiom leaf. -/
@[blueprint "chap3__example_3_4_4"]
theorem exSearchTraceRound2_leaves :
    let p := PropFormulaNormalized.var 0
    let q := PropFormulaNormalized.var 1
    let r := PropFormulaNormalized.var 2
    let s := PropFormulaNormalized.var 3
    let t := PropFormulaNormalized.var 4
    exSearchTraceRound2.leaves =
      [⟨[p, .neg q, .impl t r, .conj p s], [p, t]⟩,
       ⟨[q, p, p, s], [q, t, t]⟩,
       ⟨[r, q, p, p, s], [q, t]⟩] 

-- ATTACH-BLOCKER: unsupported untagged example
/-- Distinct equal leaves remain distinct substitution targets. -/
example :
    let a := PropFormulaNormalized.disj (.var 0) (.var 1)
    let leaf : DeductionTree ⟨[a], []⟩ := .leaf _
    let tree := DeductionTree.twoPremise (GentzenStep2.orLeft [] [] [] a a) leaf leaf
    (doSubstitution (tree := tree) (NodeAddress.left (right := leaf) (.here leaf))
      (expandLeaf .systematic ⟨[a], []⟩)).leaves =
      [⟨[.var 0], []⟩, ⟨[.var 1], []⟩, ⟨[a], []⟩] := by decide

-- ATTACH-BLOCKER: unsupported untagged example
/-- An introduced formula equal to a scheduled original occurrence waits
    for the next round; only the original occurrence is expanded. -/
example :
    let a := PropFormulaNormalized.disj (.var 0) (.var 1)
    let s : Sequent := ⟨[.conj a (.var 2), a], []⟩
    (expandLeaf .systematic s).leaves =
      [⟨[a, .var 2, .var 0], []⟩, ⟨[a, .var 2, .var 1], []⟩] := by decide

/-- Example 3.4.4 (companion): After the first round, each nonaxiom leaf
    contains var 0 (P) in its antecedent (from decomposing P ∧ ¬Q). -/
@[blueprint "chap3__example_3_4_4"]
theorem exSearchTrace_descendant_demo :
    ∀ leaf ∈ nonAxiomLeaves exSearchTraceRound1,
      .var 0 ∈ leaf.antecedent 

-- ========= Path-finding infrastructure =========

-- Local definitions matching SignedFormulae.lean types, defined here to
-- avoid a circular import (SignedFormulae -> Infinite -> Search).

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- A direction in a deduction tree: left or right at a two-premise node. -/
inductive PathDir' where
  | left : PathDir'
  | right : PathDir'
  deriving DecidableEq, Repr

-- ATTACH-BLOCKER: unsupported untagged abbrev
/-- A path through a deduction tree is a list of directional choices. -/
abbrev Path' := List PathDir'



  -- unreachable: sequentsAlongPath' is never empty





-- ========= pathToLeaf: construct a path from root to a given leaf =========



-- ========= sequentsAlongPath' never empty =========



-- ========= pathToLeaf_reaches_leaf =========



-- ========= leaf is in sequentsAlongPath' =========



-- ========= leaf_signedSet_subset_pathSignedSet =========



-- ========= Theorem 3.4.1: search produces a finished tree =========

-- Bridge: isAtomicBool reflects isAtomicFormula
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem isAtomicBool_iff (A : PropFormulaNormalized) :
    isAtomicBool A = true ↔ isAtomicFormula A := by
-- BEGIN PROOF
  cases A <;> simp_all [isAtomicBool, isAtomicFormula]

-- Bridge: isFinishedLeafBool reflects isFinishedLeaf
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem isFinishedLeafBool_iff (s : Sequent) :
    isFinishedLeafBool mode s = true ↔ isFinishedLeaf mode s := by
-- BEGIN PROOF
  simp only [isFinishedLeafBool, isFinishedLeaf, Bool.or_eq_true, Bool.and_eq_true,
             List.any_eq_true, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h
    rcases h with ⟨hmode, A, hA, B, hB, rfl⟩ | hall
    · exact Or.inl ⟨hmode, A, hA, hB⟩
    · exact Or.inr (fun A hA => (isAtomicBool_iff A).mp (hall A hA))
  · intro h
    rcases h with ⟨hmode, A, hA, hB⟩ | hall
    · exact Or.inl ⟨hmode, A, hA, A, hB, rfl⟩
    · exact Or.inr (fun A hA => (isAtomicBool_iff A).mpr (hall A hA))

-- Bridge: isFinishedTreeBool reflects isFinishedTree
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem isFinishedTreeBool_iff_isFinishedTree {c : Sequent} (dt : DeductionTree c) :
    isFinishedTreeBool mode dt = true ↔ isFinishedTree mode dt := by
-- BEGIN PROOF
  simp only [isFinishedTreeBool, isFinishedTree, List.all_eq_true]
  exact forall_congr' (fun s => forall_congr' (fun _ => isFinishedLeafBool_iff s))

-- Decidable instance for isFinishedTree (via the Bool version)
-- ATTACH-BLOCKER: unsupported untagged instance
instance decidableFinishedTree {c : Sequent} (dt : DeductionTree c) :
    Decidable (isFinishedTree mode dt) :=
  decidable_of_iff _ (isFinishedTreeBool_iff_isFinishedTree dt)

end LCS.Propositional.Systems.G.Search
end

