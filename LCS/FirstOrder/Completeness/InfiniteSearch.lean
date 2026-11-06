import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.Completeness.Basic
import Attach
import LCS.FirstOrder.Completeness.InfiniteSearch.ProofsStamp

/-! # FirstOrder.Completeness.InfiniteSearch
    Infinite sequent search infrastructure for first-order logic.
    Proves consistent_implies_satisfiable via the search tree approach,
    avoiding the Lindenbaum lemma and truth lemma.

    The selected closure renames input variables to even indices,
    reserves fresh odd witnesses, and selects one type-B component per
    occurrence. A nonclosing branch yields a signed limit set; its
    Hintikka and renaming transport lemmas support model construction.
-/

namespace LCS.FirstOrder.Completeness.InfiniteSearch

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Completeness
open Classical

-- ===================================================================
-- Consistency for normalized formulas
-- ===================================================================

/-- General G-consistency: some normalized formula cannot be proved from
any finite list of members of Gamma. The equality model-existence bridges
also use this predicate. -/
@[blueprint "chap5__theorem_5_5_4"]
def isConsistentSet {L : Language} (Gamma : Set (FormulaN L)) : Prop :=
  ∃ A : FormulaN L, ∀ cs : List (FormulaN L),
    (∀ c ∈ cs, c ∈ Gamma) →
    ¬ sequentProvableExt (Sequent.mk cs [A])

/-- Consistency (§5.5.4 definition) in a language without equality. -/
@[blueprint "chap5__theorem_5_5_4"]
def isConsistentSetNoEq {L : Language} (hL : L.withoutEquality)
    (Gamma : Set (FormulaN L)) : Prop :=
  isConsistentSet Gamma

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- No finite list of members of Gamma proves the empty succedent. -/
def isConsistentSetEmptySucc {L : Language} (Gamma : Set (FormulaN L)) : Prop :=
  ∀ (cs : List (FormulaN L)),
    (∀ c, c ∈ cs → c ∈ Gamma) →
    ¬ (sequentProvableExt (Sequent.mk cs []))

/-- For languages with at least one normalized formula, consistency is
equivalent to unprovability of the empty succedent from finite subsets. -/
theorem isConsistentSet_iff_emptySucc {L : Language}
    [Nonempty (FormulaN L)] (Gamma : Set (FormulaN L)) :
    isConsistentSet Gamma ↔ isConsistentSetEmptySucc Gamma := by
  -- REPAIR(T20): proof pending
  sorry



-- formulaNoEq and formulaSubstN_noEq are imported from SemanticsN

-- ===================================================================
-- Decomposition functions for the growing closure
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 5.5.1 (required companion): Decompose one antecedent
FormulaN for the growing closure. Includes type-B decomposition
(disj and impl in antecedent are also decomposed). For T(disj X Y),
both X and Y go to the antecedent (overdecomposition). For
T(impl X Y), Y goes to the antecedent and X goes to the succedent
(matching F(X) and T(Y)). -/
def decompAntGrowing {L : Language} (A : FormulaN L) (t_c t_d : Term L) :
    List (FormulaN L) × List (FormulaN L) :=
  match A with
  | .conj X Y => ([X, Y], [])
  | .disj X Y => ([X, Y], [])
  | .impl X Y => ([Y], [X])
  | .neg X => ([], [X])
  | .all x B => ([formulaSubstN B t_c x], [])
  | .ex x B => ([formulaSubstN B t_d x], [])
  | .predN _ _ => ([], [])
  | .eq_ _ _ _ => ([], [])

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 5.5.1 (required companion): Decompose one succedent
FormulaN for the growing closure. Includes type-B decomposition
(conj in succedent is also decomposed). For F(conj X Y), both X
and Y go to the succedent (overdecomposition). -/
def decompSuccGrowing {L : Language} (B : FormulaN L) (t_c t_d : Term L) :
    List (FormulaN L) × List (FormulaN L) :=
  match B with
  | .conj X Y => ([], [X, Y])
  | .disj X Y => ([], [X, Y])
  | .impl X Y => ([X], [Y])
  | .neg X => ([X], [])
  | .ex x A => ([], [formulaSubstN A t_c x])
  | .all x A => ([], [formulaSubstN A t_d x])
  | .predN _ _ => ([], [])
  | .eq_ _ _ _ => ([], [])

-- ===================================================================
-- Parity renaming and selected branches
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Rename every term variable to an even index. -/
def evenTerm {L : Language} : Term L → Term L
  | .var x => .var (2 * x)
  | .const c => .const c
  | .func f ts => .func f (fun i => evenTerm (ts i))

/-- Rename free and bound formula variables to even indices. -/
@[blueprint "chap5__theorem_5_5_1"]
def evenFormula {L : Language} : FormulaN L → FormulaN L
  | .predN P ts => .predN P (fun i => evenTerm (ts i))
  | .eq_ h t u => .eq_ h (evenTerm t) (evenTerm u)
  | .neg A => .neg (evenFormula A)
  | .conj A B => .conj (evenFormula A) (evenFormula B)
  | .disj A B => .disj (evenFormula A) (evenFormula B)
  | .impl A B => .impl (evenFormula A) (evenFormula B)
  | .all x A => .all (2 * x) (evenFormula A)
  | .ex x A => .ex (2 * x) (evenFormula A)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The image of a set of formulae under even-index renaming. -/
def evenSet {L : Language} (Gamma : Set (FormulaN L)) : Set (FormulaN L) :=
  fun B => ∃ A ∈ Gamma, evenFormula A = B

/-- Injective variable renaming preserves and reflects consistency. -/
theorem isConsistentSet_iff_evenSet {L : Language} (Gamma : Set (FormulaN L)) :
    isConsistentSet Gamma ↔ isConsistentSet (evenSet Gamma) := by
  -- REPAIR(T22): proof pending
  sorry

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Decompose one signed formula, choosing one type-B component.
Type-C instances are added only when substitution is free-for. -/
noncomputable def decompAlong {L : Language} (bit : Bool) (tc td : Term L)
    (sf : SignedFormula L) : List (FormulaN L) × List (FormulaN L) :=
  match sf with
  | .trueF (.disj A B) => (if bit then [A] else [B], [])
  | .trueF (.impl A B) => if bit then ([], [A]) else ([B], [])
  | .falseF (.conj A B) => ([], if bit then [A] else [B])
  | .trueF (.all x A) =>
    if isFreeForN tc x A then ([formulaSubstN A tc x], []) else ([], [])
  | .falseF (.ex x A) =>
    if isFreeForN tc x A then ([], [formulaSubstN A tc x]) else ([], [])
  | .trueF A => decompAntGrowing A tc td
  | .falseF A => decompSuccGrowing A tc td

-- ATTACH-BLOCKER: unsupported untagged structure
/-- A branch state stores its sequent, next choice index, and variable bound. -/
structure BranchClosureState (L : Language) where
  seq : Sequent L
  nextChoice : Nat
  varBound : Nat

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Process one occurrence, reserving an odd witness above all variables
in the current sequent, the current term, and previous witnesses. -/
noncomputable def branchClosureStep {L : Language} (choice : Nat → Bool)
    (tc : Term L) (st : BranchClosureState L) (sf : SignedFormula L) :
    BranchClosureState L :=
  let vars := (st.seq.antecedent ++ st.seq.succedent).flatMap
    (fun A => formulaFreeVarIndices A ++ formulaBoundVarIndices A)
  let bound := (vars ++ termVarIndicesList tc).foldl Nat.max st.varBound
  let witness := 2 * bound + 1
  let parts := decompAlong (choice st.nextChoice) tc (.var witness) sf
  { seq := ⟨st.seq.antecedent ++ parts.1, st.seq.succedent ++ parts.2⟩
    nextChoice := st.nextChoice + 1
    varBound := witness }

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Process a snapshot of every signed occurrence for one type-C term. -/
noncomputable def branchClosureRound {L : Language} (choice : Nat → Bool)
    (st : BranchClosureState L) (tc : Term L) : BranchClosureState L :=
  let formulas := st.seq.antecedent.map SignedFormula.trueF ++
    st.seq.succedent.map SignedFormula.falseF
  formulas.foldl (branchClosureStep choice tc) st

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Enumerate the even-renamed input and fairly revisit formulae and terms.
Each occurrence uses its own choice position and fresh odd witness. -/
noncomputable def growingClosureAlongState {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (choice : Nat → Bool) : Nat → BranchClosureState L
  | 0 => { seq := ⟨if Gamma (Countable.enumerate 0)
                    then [evenFormula (Countable.enumerate 0)] else [], []⟩
           nextChoice := 0, varBound := 0 }
  | n + 1 =>
    let prev := growingClosureAlongState Gamma choice n
    let A := Countable.enumerate (n + 1)
    let start := if Gamma A then
      { prev with seq := ⟨prev.seq.antecedent ++ [evenFormula A], prev.seq.succedent⟩ }
      else prev
    ((List.range (n + 2)).map (Countable.enumerate (α := Term L))).foldl
      (branchClosureRound choice) start

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The selected growing closure of the even-renamed input. -/
noncomputable def growingClosureAlong {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (choice : Nat → Bool) (n : Nat) : Sequent L :=
  (growingClosureAlongState Gamma choice n).seq

-- ===================================================================
-- Monotonicity lemmas for closureStep1 / closureStep
-- ===================================================================









-- ===================================================================
-- Monotonicity lemmas for growingClosure
-- ===================================================================

-- ===================================================================
-- Decomposition membership lemmas
-- ===================================================================











-- ===================================================================
-- Decomposition transfer lemmas for growingClosure
-- ===================================================================









-- ===================================================================
-- Limit set membership helpers
-- ===================================================================





-- ===================================================================
-- noEq preservation through growing closure
-- ===================================================================















/-- A consistent even-renamed input has a selected branch with no axiom node. -/
theorem exists_consistent_branch {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (hCon : isConsistentSet (evenSet Gamma)) :
    ∃ choice, ∀ n, ¬ isAxiom (growingClosureAlong Gamma choice n) := by
  -- REPAIR(T22): proof pending
  sorry

-- ===================================================================
-- Hintikka set via SearchTreeData (branching tree)
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 5.5.1 (required companion): The signed set collected
along an infinite path through a search tree. Given a SearchTreeData
with path function f, this is the union of signed formulae from the
sequents along the path [f 0, ..., f (n-1)] for all n. This replaces
signedLimitSet (which uses the linear growingClosure) with the
branching tree's path-collected set. -/
def pathSignedSet {L : Language} [Countable (Term L)] {seq : Sequent L}
    (w : SearchTreeData L seq)
    (f : Nat → Nat) : Set (SignedFormula L) :=
  fun sf =>
    ∃ n : Nat, ∃ (h : (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom),
      let seq_n := w.nodeSequent (List.ofFn (fun i : Fin n => f i)) h
      (∃ A ∈ seq_n.antecedent, sf = SignedFormula.trueF A) ∨
      (∃ B ∈ seq_n.succedent, sf = SignedFormula.falseF B)

end LCS.FirstOrder.Completeness.InfiniteSearch
