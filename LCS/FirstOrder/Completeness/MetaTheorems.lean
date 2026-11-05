import LCS.Item
import LCS.Util
import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Completeness.InfiniteSearch
import Attach
import LCS.FirstOrder.Completeness.MetaTheorems.ProofsStamp

/-! # FirstOrder.Completeness.MetaTheorems
    Formalization of Chapter 5, Sections 5.5.4-5.5.5.
    Lowenheim-Skolem, compactness, model existence theorems,
    and maximal consistent sets (languages without equality).

    Model existence (consistent_implies_satisfiableN) delegates to
    InfiniteSearch, using a selected branch of the even-renamed input
    and transporting its model back to the original variables.
    Lowenheim-Skolem uses the countable term domain.
-/

namespace LCS.FirstOrder.Completeness.MetaTheorems

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN (formulaEvalN formulaNoEq
  satisfiableSetN satisfiableSetInN finiteSubsetSatisfiableN isCountableDomain)
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Completeness.InfiniteSearch (
  signedLimitSet limitSet_isHintikka gamma_in_limitSet)
open LCS.FirstOrder.Gentzen.SignedFormulae
  (SignedFormula)
open LCS.FirstOrder.Gentzen.Hintikka
  (hintikkaStructure identityAssignment IsHintikkaSet
   hintikka_set_satisfiable hintikka_set_satisfiable_concrete)
open LCS.FirstOrder.SyntaxN.Substitution (isFreeForN)
open Classical

-- retained: used by LCS.FirstOrder.Equality.MetaTheorems
/-- The globally-rectified condition for FormulaN. Captures Gallier's
standing convention that all substitutions in the signed limit set
are free-for (bound variables chosen fresh enough that variable
capture never occurs). This is the isFreeFor condition required
by limitSet_isHintikka. -/
def globallyRectifiedN {L : Language} [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) : Prop :=
  ∀ (x : Nat) (A : FormulaN L) (t : Term L),
    (SignedFormula.trueF (FormulaN.all x A) ∈ signedLimitSet Gamma ∨
     SignedFormula.falseF (FormulaN.all x A) ∈ signedLimitSet Gamma ∨
     SignedFormula.trueF (FormulaN.ex x A) ∈ signedLimitSet Gamma ∨
     SignedFormula.falseF (FormulaN.ex x A) ∈ signedLimitSet Gamma) →
    isFreeForN t x A

-- ===================================================================
-- Lemma 5.5.1 (normalized): satisfiable_implies_consistentN
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lemma 5.5.1: In a language with at least one normalized formula,
a satisfiable set Gamma is consistent: some formula cannot be proved
from any finite list of members of Gamma. -/
theorem satisfiable_implies_consistentN {L : Language}
    [Nonempty (FormulaN L)]
    (Gamma : Set (FormulaN L))
    (hSat : satisfiableSetN Gamma) :
    InfiniteSearch.isConsistentSet Gamma :=
-- BEGIN PROOF
by
  obtain ⟨M, s, hsat⟩ := hSat
  obtain ⟨C⟩ := ‹Nonempty (FormulaN L)›
  have hFalse : ∃ A : FormulaN L, ¬ formulaEvalN M A s := by
    by_cases hC : formulaEvalN M C s
    · exact ⟨FormulaN.neg C, fun h => h hC⟩
    · exact ⟨C, hC⟩
  obtain ⟨A, hA⟩ := hFalse
  refine ⟨A, ?_⟩
  intro cs hcs hprov
  have hvalid := soundnessG_Ext (Sequent.mk cs [A]) hprov
  obtain ⟨B, hB, hEval⟩ := hvalid M s (fun D hD => hsat D (hcs D hD))
  have hBA : B = A := by simpa using hB
  subst B
  exact hA hEval

-- ===================================================================
-- Theorem 5.5.4 (normalized): consistent_implies_satisfiableN
-- ===================================================================

/-- Theorem 5.5.4: A consistent set Gamma of equality-free formulae is satisfiable
under the §5.5 set-wide free/bound convention required for model existence. -/
theorem consistent_implies_satisfiableN {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (hCon : InfiniteSearch.isConsistentSet Gamma)
    (hFB : setCrossNoFreeBound Gamma)
    (hNoEq : ∀ A ∈ Gamma, formulaNoEq A) :
    satisfiableSetN Gamma :=
-- BEGIN PROOF
by
  have hRenamed := (InfiniteSearch.isConsistentSet_iff_evenSet Gamma).mp hCon
  obtain ⟨choice, hBranch⟩ := InfiniteSearch.exists_consistent_branch Gamma hRenamed
  -- REPAIR(T23b): proof pending
  sorry

-- ===================================================================
-- Theorem 5.5.2 (normalized): lowenheim_skolem
-- ===================================================================

/-- Theorem 5.5.2: Lowenheim-Skolem -- if a set of formulae is satisfiable,
then it is satisfiable in a structure whose domain is at most countably infinite. -/
theorem lowenheim_skolem {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L)) (hSat : satisfiableSetN Gamma)
    (hNoEq : ∀ A ∈ Gamma, formulaNoEq A) :
    ∃ (M : Structure L),
      satisfiableSetInN M Gamma ∧ isCountableDomain M :=
-- BEGIN PROOF
by
  letI : Nonempty (FormulaN L) := ⟨Countable.enumerate 0⟩
  have hCon := satisfiable_implies_consistentN Gamma hSat
  have hRenamed := (InfiniteSearch.isConsistentSet_iff_evenSet Gamma).mp hCon
  obtain ⟨choice, hBranch⟩ := InfiniteSearch.exists_consistent_branch Gamma hRenamed
  -- REPAIR(T23): proof pending
  sorry

-- ===================================================================
-- Theorem 5.5.3 (normalized): compactness
-- ===================================================================

/-- Theorem 5.5.3: Compactness -- a set Gamma of formulae is satisfiable
iff every finite subset of Gamma is satisfiable. -/
theorem compactness {L : Language}
    [Countable (FormulaN L)] [Countable (Term L)]
    (Gamma : Set (FormulaN L))
    (hFSS : finiteSubsetSatisfiableN Gamma)
    (hNoEq : ∀ A ∈ Gamma, formulaNoEq A) :
    satisfiableSetN Gamma :=
-- BEGIN PROOF
by
  letI : Nonempty (FormulaN L) := ⟨Countable.enumerate 0⟩
  have hCon : InfiniteSearch.isConsistentSet Gamma := by
    apply (InfiniteSearch.isConsistentSet_iff_emptySucc Gamma).mpr
    intro cs hcs hprov
    have hvalid := soundnessG_Ext (Sequent.mk cs []) hprov
    by_cases hne : cs = []
    · subst hne
      let Munit : Structure L := {
        carrier := Unit
        carrierNonempty := ⟨()⟩
        interpFunc := fun _ _ => ()
        interpConst := fun _ => ()
        interpPred := fun _ _ => True
      }
      obtain ⟨B, hB, _⟩ := hvalid Munit (fun _ => ())
        (fun _ hF => by simp at hF)
      simp at hB
    · obtain ⟨M, s, hMs⟩ := hFSS cs hne hcs
      obtain ⟨B, hB, _⟩ := hvalid M s (fun A hA => hMs A hA)
      simp at hB
  by_cases hFB : setCrossNoFreeBound Gamma
  · exact consistent_implies_satisfiableN Gamma hCon hFB hNoEq
  · -- REPAIR(T23b): proof pending
    sorry

-- ===================================================================
-- Lemma 5.5.2: Maximal Consistent Extension (Lindenbaum's Lemma)
-- ===================================================================

















/-- Lemma 5.5.2 (companion): A set is maximally consistent iff it is
consistent and equal to every consistent superset. -/
@[blueprint "chap5__lemma_5_5_2"]
def isMaximalConsistentSet {L : Language}
    (Delta : Set (FormulaN L)) : Prop :=
  InfiniteSearch.isConsistentSet Delta ∧
  ∀ (Sigma : Set (FormulaN L)),
    InfiniteSearch.isConsistentSet Sigma →
    Set.subset Delta Sigma → Delta = Sigma







/-- Maximal consistency in a language without equality. -/
@[blueprint "chap5__lemma_5_5_2"]
def isMaximalConsistentSetNoEq {L : Language} (hL : L.withoutEquality)
    (Delta : Set (FormulaN L)) : Prop :=
  isMaximalConsistentSet Delta

/-- Lemma 5.5.2 (companion): In a language without equality, a consistent
set is maximally consistent exactly when every proper superset is inconsistent. -/
@[blueprint "chap5__lemma_5_5_2"]
theorem isMaximalConsistentSet_iff_proper_supersetNoEq {L : Language}
    (hL : L.withoutEquality) (Gamma : Set (FormulaN L))
    (hCon : InfiniteSearch.isConsistentSetNoEq hL Gamma) :
    isMaximalConsistentSetNoEq hL Gamma ↔
      ∀ Delta, Set.subset Gamma Delta → Gamma ≠ Delta →
        ¬ InfiniteSearch.isConsistentSetNoEq hL Delta 

/-- Lemma 5.5.1: A satisfiable set in a language without equality is
consistent. Nonempty formula syntax excludes the language with no predicate symbols. -/
@[blueprint "chap5__lemma_5_5_1" (main := true)]
theorem satisfiable_implies_consistentNNoEq {L : Language}
    [Nonempty (FormulaN L)] (hL : L.withoutEquality)
    (Gamma : Set (FormulaN L)) (hSat : satisfiableSetN Gamma) :
    InfiniteSearch.isConsistentSetNoEq hL Gamma 

/-- Theorem 5.5.4: With at-most-countable formula syntax, a consistent set in a
language without equality is satisfiable under the §5.5 set-wide free/bound convention. -/
@[blueprint "chap5__theorem_5_5_4" (main := true)]
theorem consistent_implies_satisfiableNNoEq {L : Language}
    [AtMostCountable (FormulaN L)] [Countable (Term L)] (hL : L.withoutEquality)
    (Gamma : Set (FormulaN L)) (hCon : InfiniteSearch.isConsistentSetNoEq hL Gamma)
    (hFB : setCrossNoFreeBound Gamma) :
    satisfiableSetN Gamma 

/-- Theorem 5.5.2: With at-most-countable formula syntax, a satisfiable set in a
language without equality has an at-most-countable model, including empty syntax. -/
@[blueprint "chap5__theorem_5_5_2" (main := true)]
theorem lowenheim_skolemNoEq {L : Language}
    [AtMostCountable (FormulaN L)] [Countable (Term L)] (hL : L.withoutEquality)
    (Gamma : Set (FormulaN L)) (hSat : satisfiableSetN Gamma) :
    ∃ (M : Structure L), satisfiableSetInN M Gamma ∧ isCountableDomain M 

/-- Theorem 5.5.3: With at-most-countable formula syntax, a finitely satisfiable
set in a language without equality is satisfiable, including empty syntax. -/
@[blueprint "chap5__theorem_5_5_3" (main := true)]
theorem compactnessNoEq {L : Language}
    [AtMostCountable (FormulaN L)] [Countable (Term L)] (hL : L.withoutEquality)
    (Gamma : Set (FormulaN L)) (hFSS : finiteSubsetSatisfiableN Gamma) :
    satisfiableSetN Gamma 

/-- Lemma 5.5.2: With at-most-countable formula syntax, every consistent set in
a language without equality has a maximal consistent extension. -/
@[blueprint "chap5__lemma_5_5_2" (main := true), blueprint "chap5__lemma_5_6_5" (main := true)]
theorem maximal_consistent_extensionNoEq {L : Language}
    [AtMostCountable (FormulaN L)] (hL : L.withoutEquality)
    (Gamma : Set (FormulaN L)) (hCon : InfiniteSearch.isConsistentSetNoEq hL Gamma) :
    ∃ (Delta : Set (FormulaN L)),
      isMaximalConsistentSetNoEq hL Delta ∧ Set.subset Gamma Delta 





/-- Theorem 5.5.4 (search-model remark): A nonclosed maximal path is
either a path to a nonaxiom leaf of a finished round, or an infinite
path whose every label in the limit tree is nonaxiomatic. -/
@[blueprint "chap5__theorem_5_5_1"]
inductive SearchNonclosedPath {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : Search.SearchEnumeration q) : Type where
  | finite (k : Nat) (address : List Nat) (leaf : Sequent L)
      (finished : Search.allFinished hL (Search.search51 hL q hq hFB enum k))
      (atLeaf : address ∈ (Search.search51 hL q hq hFB enum k).tree.leafAddresses)
      (label : (Search.search51 hL q hq hFB enum k).tree.forget.labelAt address = some leaf)
      (nonaxiom : ¬ isAxiom leaf)
  | infinite (path : Nat → Nat)
      (inTree : Search.InfinitePath51 hL q hq hFB enum path)
      (nonaxiom : ∀ n label,
        Search.searchLimit51 hL q hq hFB enum ((List.range n).map path) label →
          ¬ isAxiom label)

/-- Theorem 5.5.4 (search-model remark): The signed set of a nonclosed
path consists exactly of the signed formulae in its actual tree labels. -/
@[blueprint "chap5__theorem_5_5_1"]
def SearchNonclosedPath.signedSet {L : Language} {hL : L.withoutEquality}
    {q : InfSequentN L} {hq : q.builtFromX} {hFB : crossNoFreeBoundInf q}
    {enum : Search.SearchEnumeration q} :
    SearchNonclosedPath hL q hq hFB enum → Set (SignedFormula L)
  | .finite k address _ _ _ _ _ =>
      finiteSearchPathSet (Search.search51 hL q hq hFB enum k).tree.forget address
  | .infinite path _ _ => infiniteSearchPathSet hL q hq hFB enum path

/-- Theorem 5.5.4 (search-model remark): H_S is the stopping round's
TERM₀ plus remaining active AVAIL entries for a finite path, and the
union of the run's TERM₀ entries for an infinite path. -/
@[blueprint "chap5__theorem_5_5_1"]
def SearchNonclosedPath.termDomain {L : Language} {hL : L.withoutEquality}
    {q : InfSequentN L} {hq : q.builtFromX} {hFB : crossNoFreeBoundInf q}
    {enum : Search.SearchEnumeration q} :
    SearchNonclosedPath hL q hq hFB enum → Set (Term L)
  | .finite k _ _ _ _ _ _ =>
      finiteSearchTermDomain (Search.search51 hL q hq hFB enum k)
  | .infinite _ _ _ => Search.eventuallyActivated51 hL q hq hFB enum

/-- Theorem 5.5.4 (search-model remark): In a countable first-order
language without equality, searching Γ → for a consistent Γ has a
nonclosed maximal path for every admissible enumeration. The antecedent
enumerates exactly Γ and the succedent is empty. -/
theorem consistent_search_has_nonclosed_path (L : FirstOrderLanguage)
    (hL : L.toLanguage.withoutEquality)
    (Gamma : Set (FormulaN L.toLanguage))
    (hCon : InfiniteSearch.isConsistentSetNoEq hL Gamma)
    (q : InfSequentN L.toLanguage)
    (hGamma : ∀ A, q.memAntecedent A ↔ A ∈ Gamma)
    (hEmpty : ∀ n, q.succedent n = none)
    (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : Search.SearchEnumeration q) :
    Nonempty (SearchNonclosedPath hL q hq hFB enum) := by
  -- REPAIR(T110): proof pending
  sorry

/-- Theorem 5.5.4 (search-model remark): For every nonclosed maximal
path of the search on Γ →, if its signed set S is Hintikka over its
run-defined H_S, the Lemma 5.4.5 structure on H_S and its identity
assignment satisfy every member of S and every formula of Γ. -/
@[attach_debt, blueprint "chap5__theorem_5_5_4"]
theorem nonclosed_search_path_hintikka_model {L : Language}
    (hL : L.withoutEquality) (Gamma : Set (FormulaN L))
    (q : InfSequentN L) (hGamma : ∀ A, q.memAntecedent A ↔ A ∈ Gamma)
    (hEmpty : ∀ n, q.succedent n = none)
    (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : Search.SearchEnumeration q)
    (path : SearchNonclosedPath hL q hq hFB enum)
    (S : Set (SignedFormula L)) (hS : S = path.signedSet)
    (hHS : IsHintikkaSet L hL path.termDomain S) :
    (∀ sf ∈ S, SignedFormula.satisfiedBy
      (hintikkaStructure path.termDomain S hHS)
      (identityAssignment path.termDomain S hHS) sf) ∧
    (∀ A ∈ Gamma, formulaEvalN (hintikkaStructure path.termDomain S hHS) A
      (identityAssignment path.termDomain S hHS)) 

end LCS.FirstOrder.Completeness.MetaTheorems
