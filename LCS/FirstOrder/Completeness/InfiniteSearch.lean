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
-- Growing closure step functions
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 5.5.1 (required helper): One step of the growing closure --
decompose all formulas with a single type-c term and a type-d witness.
Appends decompositions to the sequent. -/
def closureStep1 {L : Language} (prev : Sequent L)
    (t_c t_d : Term L) : Sequent L :=
  let newAnt := prev.antecedent.flatMap (fun A => (decompAntGrowing A t_c t_d).1)
  let antToSucc := prev.antecedent.flatMap (fun A => (decompAntGrowing A t_c t_d).2)
  let succToAnt := prev.succedent.flatMap (fun B => (decompSuccGrowing B t_c t_d).1)
  let newSucc := prev.succedent.flatMap (fun B => (decompSuccGrowing B t_c t_d).2)
  { antecedent := prev.antecedent ++ newAnt ++ succToAnt
    succedent := prev.succedent ++ antToSucc ++ newSucc }

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 5.5.1 (required helper): One step of the growing closure
with a list of type-c terms. -/
def closureStep {L : Language} (prev : Sequent L)
    (t_cs : List (Term L)) (t_d : Term L) : Sequent L :=
  t_cs.foldl (fun acc t_c => closureStep1 acc t_c t_d) prev

-- ===================================================================
-- The growing search closure
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 5.5.1 (required companion): The growing search closure
for a consistent set Gamma of normalized formulas. At step n, the
antecedent includes gammaEnum(0),...,gammaEnum(n) (those in Gamma).
The succedent starts empty.

Decomposition includes all formula types (A, B, C, D):
type-A (conj in ant, neg), type-B (disj/impl in ant, conj in succ),
type-C (all in ant, ex in succ), type-D (ex in ant, all in succ).
For type-B, both components are added (overdecomposition) to ensure
the signed limit set satisfies the Hintikka H2 condition. -/
noncomputable def growingClosure {L : Language} [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) : Nat → Sequent L
  | 0 =>
    Sequent.mk
      (if Gamma (Countable.enumerate 0) then [Countable.enumerate 0] else [])
      []
  | n + 1 =>
    let prev := growingClosure Gamma n
    let terms := (List.range (n + 2)).map (Countable.enumerate (α := Term L))
    let t_d := Term.var (n + 1)
    let decomped := closureStep prev terms t_d
    if Gamma (Countable.enumerate (n + 1))
    then Sequent.mk (decomped.antecedent ++ [Countable.enumerate (n + 1)]) decomped.succedent
    else decomped

-- ===================================================================
-- The signed limit set
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 5.5.1 (required companion): The signed limit set -- the
union of all signed formulas across all levels of the growing
closure. -/
def signedLimitSet {L : Language} [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) : Set (SignedFormula L) :=
  fun sf =>
    ∃ n, (∃ A ∈ (growingClosure Gamma n).antecedent, sf = SignedFormula.trueF A) ∨
         (∃ B ∈ (growingClosure Gamma n).succedent, sf = SignedFormula.falseF B)

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

/-- Even-index renaming preserves satisfiability in the same structure. -/
theorem satisfiableSetInN_iff_evenSet {L : Language} (M : Structure L)
    (Gamma : Set (FormulaN L)) :
    satisfiableSetInN M Gamma ↔ satisfiableSetInN M (evenSet Gamma) := by
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

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The union of the signed sequents along a selected branch. -/
def signedLimitSetAlong {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (choice : Nat → Bool) : Set (SignedFormula L) :=
  fun sf => ∃ n,
    (∃ A ∈ (growingClosureAlong Gamma choice n).antecedent, sf = .trueF A) ∨
    (∃ A ∈ (growingClosureAlong Gamma choice n).succedent, sf = .falseF A)

/-- Signed formulae persist along a selected branch. -/
theorem growingClosureAlong_mono {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (choice : Nat → Bool) {n m : Nat} (h : n ≤ m) :
    (∀ A ∈ (growingClosureAlong Gamma choice n).antecedent,
      A ∈ (growingClosureAlong Gamma choice m).antecedent) ∧
    (∀ A ∈ (growingClosureAlong Gamma choice n).succedent,
      A ∈ (growingClosureAlong Gamma choice m).succedent) := by
  -- REPAIR(T22): proof pending
  sorry

/-- The selected signed limit contains every even-renamed input formula. -/
theorem gamma_in_limitSetAlong {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (choice : Nat → Bool) (A : FormulaN L)
    (hA : A ∈ evenSet Gamma) : SignedFormula.trueF A ∈ signedLimitSetAlong Gamma choice := by
  -- REPAIR(T22): proof pending
  sorry

-- ===================================================================
-- Monotonicity lemmas for closureStep1 / closureStep
-- ===================================================================









-- ===================================================================
-- Monotonicity lemmas for growingClosure
-- ===================================================================









-- ===================================================================
-- Gamma inclusion in the limit set
-- ===================================================================

-- retained: used by LCS.FirstOrder.Completeness.MetaTheorems, LCS.FirstOrder.Equality.Completeness.Part1
/-- Theorem 5.5.1 (required helper): At step k, if enumerate(k) is
in Gamma, it appears in the antecedent of growingClosure k. -/
theorem enumerate_in_closure {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (k : Nat)
    (hk : Gamma (Countable.enumerate k)) :
    Countable.enumerate k ∈ (growingClosure Gamma k).antecedent := by
-- BEGIN PROOF
  induction k with
  | zero =>
    simp only [growingClosure]
    rw [if_pos hk]
    exact List.Mem.head _
  | succ n _ih =>
    simp only [growingClosure]
    simp only [if_pos hk]
    exact List.mem_append_right _ (List.Mem.head _)

-- retained: used by LCS.FirstOrder.Completeness.MetaTheorems, LCS.FirstOrder.Equality.Completeness.Part1
/-- Theorem 5.5.1 (required helper): Every formula in Gamma appears
in the signed limit set as trueF. -/
theorem gamma_in_limitSet {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (A : FormulaN L) (hA : A ∈ Gamma) :
    SignedFormula.trueF A ∈ signedLimitSet Gamma := by
-- BEGIN PROOF
  obtain ⟨k, hk⟩ := Countable.enumerate_surj A
  rw [← hk]
  rw [← hk] at hA
  refine ⟨k, Or.inl ⟨Countable.enumerate k, enumerate_in_closure Gamma k hA, rfl⟩⟩

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

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A branch with no axiom nodes has no complementary atomic pair in its limit. -/
theorem limitSet_isHintikka_h0 {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (choice : Nat → Bool)
    (hBranch : ∀ n, ¬ isAxiom (growingClosureAlong Gamma choice n)) :
    ∀ (A : FormulaN L), A.isAtomic = true →
      ¬(SignedFormula.trueF A ∈ signedLimitSetAlong Gamma choice ∧
        SignedFormula.falseF A ∈ signedLimitSetAlong Gamma choice) := by
  intro A _hAtom ⟨⟨k, hk⟩, ⟨m, hm⟩⟩
  rcases hk with ⟨F, hF, hEq⟩ | ⟨F, hF, hEq⟩
  · cases hEq
    rcases hm with ⟨G, hG, hEq⟩ | ⟨G, hG, hEq⟩
    · cases hEq
    · cases hEq
      exact hBranch (max k m) ⟨A,
        (growingClosureAlong_mono Gamma choice (Nat.le_max_left k m)).1 A hF,
        (growingClosureAlong_mono Gamma choice (Nat.le_max_right k m)).2 A hG⟩
  · cases hEq















/-- The selected limit of an even-renamed, equality-free input is Hintikka
when its branch has no axiom nodes and all quantified substitutions are free-for.
This proof step of Theorem 5.5.1 uses the term algebra of the reduct L_S:
its terms use the function and constant symbols occurring in the signed set.
Components carry evidence that substitution is free for the bound variable. -/
theorem limitSet_isHintikka {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)] (hL : L.withoutEquality)
    (Gamma : Set (FormulaN L)) (choice : Nat → Bool)
    (hBranch : ∀ n, ¬ isAxiom (growingClosureAlong Gamma choice n))
    (hNoEq : ∀ A ∈ evenSet Gamma, formulaNoEq A)
    (hNFB : ∀ (x : Nat) (A : FormulaN L) (t : Term L),
      (SignedFormula.trueF (FormulaN.all x A) ∈ signedLimitSetAlong Gamma choice ∨
       SignedFormula.falseF (FormulaN.all x A) ∈ signedLimitSetAlong Gamma choice ∨
       SignedFormula.trueF (FormulaN.ex x A) ∈ signedLimitSetAlong Gamma choice ∨
       SignedFormula.falseF (FormulaN.ex x A) ∈ signedLimitSetAlong Gamma choice) →
      isFreeForN t x A) :
    IsHintikkaSet L hL
      (fun t => termFunSyms t ⊆ signedSetFunSyms (signedLimitSetAlong Gamma choice) ∧
        termConstSyms t ⊆ signedSetConstSyms (signedLimitSetAlong Gamma choice))
      (signedLimitSetAlong Gamma choice) := by
  refine {
    hTA := occurrenceTerms_isTermAlgebraOver (signedLimitSetAlong Gamma choice)
    h0 := limitSet_isHintikka_h0 Gamma choice hBranch
    h1 := ?_
    h2 := ?_
    h3 := ?_
    h4 := ?_
    h5 := fun _ _ _ _ => ⟨fun _ h => h.elim, fun _ h => by cases h⟩
    h6 := fun x A t _ h => hNFB x A t h } <;>
    -- REPAIR(T34): proof pending
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











/-- Theorem 5.5.1 (companion, witness H5): Free variable terms of path
formulas lie in safeTermsN.
BLOCKED: requires either (a) strengthening noFreeBound to
cross-formula: ∀ x, (∃ A ∈ seq, x ∈ FV(A)) → (∀ B ∈ seq, x ∉ BV(B)),
or (b) restricting type-C substitution terms to safeTermsN.
See Hintikka.lean for detailed analysis. -/
theorem limitSet_isHintikka_via_witness_h5 {L : Language} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeData L seq)
    (f : Nat → Nat) (_hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    ∀ (sf : SignedFormula L), sf ∈ pathSignedSet w f →
      ∀ (x : Nat), x ∈ signedFormulaFreeVars sf →
        (Term.var x : Term L) ∈ safeTermsN seq := by
-- BEGIN PROOF
  intro sf hsf x hx
  -- DEBT(Theorem 5.5.1 companion H5: needs cross-formula free/bound disjointness or the safe-term restriction; see docstring)
  sorry









end LCS.FirstOrder.Completeness.InfiniteSearch
