import LCS.FirstOrder.Completeness.Basic
import LCS.FirstOrder.Completeness.Search
import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.FirstOrder.Gentzen.Hintikka
import Attach
import LCS.FirstOrder.Completeness.ProofsStamp

/-! # FirstOrder.Completeness
    Formalization of Chapter 5, Sections 5.5.1-5.5.3.
    Organizing terms, search procedure, and completeness of G
    for languages with function symbols and no equality.
    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.FirstOrder.Completeness

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Gentzen.Hintikka

-- ===================================================================
-- FormulaN-native completeness infrastructure (Round 3)
-- ===================================================================

-- ===================================================================
-- seqNoEqC: No-equality condition for Sequent
-- ===================================================================



-- ===================================================================
-- Theorem 5.5.1 (normalized): searchCompletenessValid
-- ===================================================================

/-- Theorem 5.5.1(i): Extract a G-proof from a closed finite-round search
tree by propagating the introduced input formulae toward the root and
contracting the input-introduction edges. The equality argument identifies
the supplied tree with the specified round of the fixed admissible run. -/
@[blueprint "chap5__theorem_5_5_1"]
noncomputable def closedSearchTreeToProof {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : Search.SearchEnumeration q) (k : Nat)
    (tree : Search.InfGDeductionTreeExt
      (Sequent.mk (q.antecedent 0).toList (q.succedent 0).toList))
    (hTree : tree = (Search.search51 hL q hq hFB enum k).tree.forget)
    (hClosed : ∀ leaf ∈ tree.leaves, isAxiom leaf) :
    Σ s : Sequent L, GProofTreeExt s := by
  -- REPAIR(T106): proof pending
  sorry

/-- Theorem 5.5.1(i): For every admissible enumeration of an equality-free
input built from the x variables and satisfying the sequent-wide free/bound
convention, validity implies that a finite round of search is closed and
finished. The explicit extraction function applied to that very tree
returns a G-proof whose conclusion is a finite subsequent of the input. -/
@[attach_debt, blueprint "chap5__theorem_5_5_1" (main := true)]
theorem searchCompletenessValid {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : Search.SearchEnumeration q) (hValid : infSequentValid q) :
    ∃ k, ∃ hClosed : ∀ leaf ∈ (Search.search51 hL q hq hFB enum k).tree.forget.leaves,
      isAxiom leaf,
      Search.allFinished hL (Search.search51 hL q hq hFB enum k) ∧
      IsFiniteSubsequentInf
        (closedSearchTreeToProof hL q hq hFB enum k
          (Search.search51 hL q hq hFB enum k).tree.forget rfl hClosed).1 q 

-- ===================================================================
-- Theorem 5.5.1 (normalized): searchCompletenessFalsifiable
-- ===================================================================

/-- Theorem 5.5.1(ii)(a): The domain at a finite stopping round consists
of the TERM₀ entries and all remaining entries of AVAIL₀ through AVAIL_NUMACT. -/
@[blueprint "chap5__theorem_5_5_1"]
def finiteSearchTermDomain {L : Language} {root : Sequent L}
    (st : Search.SearchState L root) : Set (Term L) := fun t =>
  t ∈ st.TERM0 ∨ ∃ i, i ≤ st.numact ∧ ∃ n, (st.avail i).entries n = some t

/-- Theorem 5.5.1(ii)(a): The signed set along the root-to-leaf path at
an address of a finite search tree contains exactly the signed formulae
in the labels at prefixes of that address, including both endpoints. -/
@[blueprint "chap5__theorem_5_5_1"]
def finiteSearchPathSet {L : Language} {root : Sequent L}
    (tree : Search.InfGDeductionTreeExt root) (address : List Nat) :
    Set (SignedFormula L) := fun sf =>
  ∃ n, n ≤ address.length ∧ ∃ label,
    tree.labelAt (address.take n) = some label ∧
    sf ∈ Search.inputSignedSet (InfSequentN.ofSequent label)

/-- Theorem 5.5.1(ii)(b): The signed set of an infinite path contains
exactly the signed formulae in limit-tree labels at its finite prefixes. -/
@[blueprint "chap5__theorem_5_5_1"]
def infiniteSearchPathSet {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : Search.SearchEnumeration q) (path : Nat → Nat) :
    Set (SignedFormula L) := fun sf =>
  ∃ n label, Search.searchLimit51 hL q hq hFB enum ((List.range n).map path) label ∧
    sf ∈ Search.inputSignedSet (InfSequentN.ofSequent label)

/-- Theorem 5.5.1(ii): For each admissible enumeration, a falsifiable
possibly infinite input has either a finished finite search tree with a
nonaxiom leaf, or an infinite nonclosed path in the limit tree.
The Hintikka set is exactly the signed set on the selected path. In the
finite case H_S consists of TERM₀ and the remaining active AVAIL entries;
in the infinite case it consists of the terms eventually entering TERM₀.
H_S is a countable term algebra over L_S, and a structure whose carrier is
exactly H_S satisfies the path set and falsifies the input sequent. -/
@[attach_debt, blueprint "chap5__theorem_5_5_1" (main := true)]
theorem searchCompletenessFalsifiable {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : Search.SearchEnumeration q) (hFals : infSequentFalsifiable q) :
    ∃ (S : Set (SignedFormula L)) (H : Set (Term L)),
      ((∃ k address leaf,
          Search.allFinished hL (Search.search51 hL q hq hFB enum k) ∧
          address ∈ (Search.search51 hL q hq hFB enum k).tree.leafAddresses ∧
          (Search.search51 hL q hq hFB enum k).tree.forget.labelAt address = some leaf ∧
          ¬ isAxiom leaf ∧
          H = finiteSearchTermDomain (Search.search51 hL q hq hFB enum k) ∧
          S = finiteSearchPathSet (Search.search51 hL q hq hFB enum k).tree.forget address) ∨
        (¬ Search.halts51 hL q hq hFB enum ∧ ∃ path,
          Search.InfinitePath51 hL q hq hFB enum path ∧
          (∀ n label,
            Search.searchLimit51 hL q hq hFB enum ((List.range n).map path) label →
            ¬ isAxiom label) ∧
          H = Search.eventuallyActivated51 hL q hq hFB enum ∧
          S = infiniteSearchPathSet hL q hq hFB enum path)) ∧
      Hintikka.IsHintikkaSet L hL H S ∧
      AtMostCountable {t : Term L // t ∈ H} ∧
      ∃ M : Structure L, M.carrier = {t : Term L // t ∈ H} ∧
        isCountableDomain M ∧ ∃ s : Assignment M,
          (∀ sf ∈ S, SignedFormula.satisfiedBy M s sf) ∧
          (∀ A, q.memAntecedent A → formulaEvalN M A s) ∧
          (∀ B, q.memSuccedent B → ¬ formulaEvalN M B s) 

end LCS.FirstOrder.Completeness
