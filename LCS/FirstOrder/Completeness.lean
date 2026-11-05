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
-- Bridge axioms for the search / Hintikka set connection (Section 5.5)
-- ===================================================================

/-- Theorem 5.5.1 (bridge): When the search tree for a falsifiable sequent
is infinite, extract a Hintikka set S and infinite term algebra H from
the infinite path given by Koenig's lemma. H = t(TERM0_infinity) grows
without bound as new eigenvariables are activated and new terms are added
each round.

Proof sketch: The infinite path gives an infinite sequence of sequents.
S = pathSignedSet of this infinite path satisfies H0-H6 by the same
argument as infinitePath_yields_hintikkaSet. H = t(TERM0_infinity) is
the union of all TERM0 sets across all rounds. H is infinite because
each round's roundEndUpdate adds at least one new term from AVAIL, and
the AVAIL streams are infinite. searchHalts fails because the infinite
path witnesses a non-terminating branch. -/
theorem searchCompletenessFalsifiable_infiniteF {L : Language}
    (seq : Sequent L)
    (_hFree : noFreeBound seq)
    (_hFals : sequentFalsifiable seq) :
    ∃ (S : Set (SignedFormula L)) (H : Set (Term L)),
      IsGeneratedTermAlgebra L H ∧
      (∀ A ∈ seq.antecedent, SignedFormula.trueF A ∈ S) ∧
      (∀ B ∈ seq.succedent, SignedFormula.falseF B ∈ S) := by
-- BEGIN PROOF
  -- DEBT(Theorem 5.5.1 bridge: Hintikka set from the infinite search path; superseded by searchCompletenessFalsifiable, T107)
  sorry

/-- Theorem 5.5.1 (bridge): The search procedure applied to a valid
sequent produces a well-formed proof tree (a `GProofTreeExt` under the
§5.4.8 standing assumption, with the right conclusion and satisfying
the WellFormed inductive predicate). The search construction applies
G's rules from axiom leaves
upward; each rule application satisfies the WellFormed constructor
conditions because:
- Propositional rules decompose connectives correctly.
- Quantifier rules use terms from TERM0 that are free for x in A
  (guaranteed by h6 from the Hintikka conditions).
- Eigenvariables are fresh (from the AVAIL stream).

Proof sketch: The proof tree t is produced by the search procedure.
Each node in the search tree corresponds to a rule application.
Propositional nodes (andLeft, andRight, orLeft, orRight, implLeft,
implRight, negLeft, negRight) decompose their principal formula into
sub-formulae; the WellFormed constructors match exactly. Quantifier
nodes (allLeft, allRight, exLeft, exRight) use terms from TERM0 or
eigenvariables from AVAIL. For allLeft/exRight, the term t is free
for x in A by the noFreeBound condition on the original sequent plus
the Hintikka condition h6. For allRight/exLeft, the eigenvariable y
is fresh (not occurring in the conclusion sequent) by construction
of the AVAIL stream. -/
theorem searchProducesWellFormedTreeF {L : Language} [Countable (Term L)]
    (seq : Sequent L)
    (hFree : noFreeBound seq)
    (hNoEq : seqNoEq seq)
    (hValid : sequentValid seq) :
    sequentProvableExt seq := by
-- BEGIN PROOF
  -- DEBT(Theorem 5.5.1 bridge: well-formed proof tree from the search; superseded by searchCompletenessValid, T106)
  sorry



-- ===================================================================
-- Theorem 5.5.1 (companion): goedelExtendedCompletenessGF
-- ===================================================================

-- retained: used by LCS.FirstOrder.Equality.Completeness.Part1
/-- Finite-sequent completeness for equality-free formulae with free/bound
separation in each individual formula, using the §5.4.8 extended G rules. -/
theorem goedelExtendedCompletenessGF {L : Language} [Countable (Term L)]
    (seq : Sequent L)
    (hFree : noFreeOccursBound seq)
    (hNoEq : seqNoEq seq) :
    sequentValid seq ↔ sequentProvableExt seq :=
-- BEGIN PROOF
by
  constructor
  · exact searchProducesWellFormedTreeF seq (fun A hA x => hFree A hA x) hNoEq
  · exact soundnessG_Ext seq

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
-- Theorem 5.5.1 (normalized): goedelExtendedCompletenessG
-- ===================================================================

/-- Corollary of Theorem 5.5.1 (Gödel extended completeness): Over a
language without equality, a possibly infinite sequent satisfying the
sequent-wide free/bound convention is valid if and only if some finite
subsequent has a G-proof under the §5.4.8 extended-rule convention. -/
@[attach_debt, blueprint "chap5__theorem_5_5_1"]
theorem goedelExtendedCompletenessG {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hFB : crossNoFreeBoundInf q) :
    infSequentValid q ↔ infSequentProvable q 

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

/-- Corollaries of Theorem 5.5.1: A fixed admissible run halts closed
when a finite round is finished and every leaf of its actual tree is an axiom. -/
@[blueprint "chap5__theorem_5_5_1"]
def searchHaltsClosed51 {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : Search.SearchEnumeration q) : Prop :=
  ∃ k, Search.allFinished hL (Search.search51 hL q hq hFB enum k) ∧
    ∀ leaf ∈ (Search.search51 hL q hq hFB enum k).tree.forget.leaves, isAxiom leaf

/-- Corollary of Theorem 5.5.1: For every admissible enumeration, search
halts on a finite quantifier-free input and halts with a closed tree exactly
when that input is valid. The input follows the x-variable supply and the
sequent-wide free/bound convention. -/
@[attach_debt, blueprint "chap5__theorem_5_5_1"]
theorem quantifierFreeDecidableF {L : Language} (hL : L.withoutEquality)
    (seq : Sequent L) (hq : (InfSequentN.ofSequent seq).builtFromX)
    (hFB : crossNoFreeBoundInf (InfSequentN.ofSequent seq))
    (enum : Search.SearchEnumeration (InfSequentN.ofSequent seq))
    (hQF : sequentQuantifierFree seq) :
    Search.halts51 hL (InfSequentN.ofSequent seq) hq hFB enum ∧
      (searchHaltsClosed51 hL (InfSequentN.ofSequent seq) hq hFB enum ↔
        sequentValid seq) 



/-- Theorem 5.5.1 (divergence): In the language with P, Q and unary f,
some falsifiable formula has an admissible search run that never finishes. -/
@[attach_debt, blueprint "chap5__theorem_5_5_1"]
theorem searchMayDiverge :
    ∃ (A : FormulaN exLangPQf2)
      (hq : (InfSequentN.ofSequent (Sequent.mk [] [A])).builtFromX)
      (hFB : crossNoFreeBoundInf (InfSequentN.ofSequent (Sequent.mk [] [A])))
      (enum : Search.SearchEnumeration (InfSequentN.ofSequent (Sequent.mk [] [A]))),
      infSequentFalsifiable (InfSequentN.ofSequent (Sequent.mk [] [A])) ∧
      ¬ Search.halts51 (L := exLangPQf2) rfl (InfSequentN.ofSequent (Sequent.mk [] [A])) hq hFB enum 

/-- Theorem 5.5.1 (term-order remark): Size of an extracted G-proof,
counting axiom leaves and inference nodes once each. -/
@[blueprint "chap5__theorem_5_5_1"]
def proofTreeSize {L : Language} : {s : Sequent L} → GProofTreeExt s → Nat
  | _, .axiom_ _ _ => 1
  | _, .onePremise _ t => 1 + proofTreeSize t
  | _, .twoPremise _ left right => 1 + proofTreeSize left + proofTreeSize right

/-- Theorem 5.5.1 (term-order remark): The Example 5.5.2 input admits
two different admissible enumerations whose closed, finished search rounds
yield G-proofs of different sizes through the fixed extraction function. -/
@[attach_debt, blueprint "chap5__theorem_5_5_1"]
theorem searchTermOrderAffectsProofSize :
    ∃ (q : InfSequentN exLangPQf2) (hq : q.builtFromX)
      (hFB : crossNoFreeBoundInf q)
      (enum₁ enum₂ : Search.SearchEnumeration q) (k₁ k₂ : Nat),
      q = exProofInput ∧ enum₁ ≠ enum₂ ∧
      ∃ (hClosed₁ : ∀ leaf ∈ (Search.search51 (L := exLangPQf2) rfl q hq hFB enum₁ k₁).tree.forget.leaves,
          isAxiom leaf)
        (hClosed₂ : ∀ leaf ∈ (Search.search51 (L := exLangPQf2) rfl q hq hFB enum₂ k₂).tree.forget.leaves,
          isAxiom leaf),
        Search.allFinished (L := exLangPQf2) rfl (Search.search51 (L := exLangPQf2) rfl q hq hFB enum₁ k₁) ∧
        Search.allFinished (L := exLangPQf2) rfl (Search.search51 (L := exLangPQf2) rfl q hq hFB enum₂ k₂) ∧
        let out₁ := closedSearchTreeToProof (L := exLangPQf2) rfl q hq hFB enum₁ k₁
          (Search.search51 (L := exLangPQf2) rfl q hq hFB enum₁ k₁).tree.forget rfl hClosed₁
        let out₂ := closedSearchTreeToProof (L := exLangPQf2) rfl q hq hFB enum₂ k₂
          (Search.search51 (L := exLangPQf2) rfl q hq hFB enum₂ k₂).tree.forget rfl hClosed₂
        IsFiniteSubsequentInf out₁.1 q ∧ IsFiniteSubsequentInf out₂.1 q ∧
          proofTreeSize out₁.2 ≠ proofTreeSize out₂.2 

end LCS.FirstOrder.Completeness
