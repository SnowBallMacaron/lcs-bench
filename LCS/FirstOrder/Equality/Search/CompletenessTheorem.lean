import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Equality
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Equality.Search.Procedure
import Attach
import LCS.FirstOrder.Equality.Search.CompletenessTheorem.ProofsStamp

section
namespace LCS.FirstOrder.Equality.Search
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Completeness.Search

/-- Definition 5.6.3: Fixed input and admissible enumerations of one equality
search run in a first-order language. No path or completeness properties are
assumed in this data. -/
@[blueprint "chap5__definition_5_6_3"]
structure Run (L : FirstOrderLanguage) (hL : L.hasEquality = true) where
  input : InfSequentN L.toLanguage
  inputBuiltFromX : input.builtFromX
  inputFreeBound : crossNoFreeBoundInf input
  enumeration : SearchEnumeration input
  equalityEnumeration : EqEnumeration hL input

/-- Definition 5.6.3: The actual kth state produced by the fixed run. -/
@[blueprint "chap5__definition_5_6_3"]
noncomputable def Run.state {L : FirstOrderLanguage} {hL : L.hasEquality = true}
    (run : Run L hL) (k : Nat) :=
  searchEq hL run.input run.inputBuiltFromX run.inputFreeBound
    run.enumeration run.equalityEnumeration k

/-- Theorem 5.6.1: The run term domain is t(TERM₀), the union of the term
entries appearing in its finite-round TERM₀ lists. -/
@[blueprint "chap5__theorem_5_6_1"]
def Run.termDomain {L : FirstOrderLanguage} {hL : L.hasEquality = true}
    (run : Run L hL) : Set (Term L.toLanguage) := fun t =>
  ∃ k, t ∈ (run.state k).TERM0

/-- Theorem 5.6.1: Every finite prefix of an infinite path occurs in the
limit tree of the fixed equality-search run. -/
@[blueprint "chap5__theorem_5_6_1"]
def Run.IsInfinitePath {L : FirstOrderLanguage} {hL : L.hasEquality = true}
    (run : Run L hL) (path : Nat → Nat) : Prop :=
  ∀ n, ∃ k label,
    (run.state k).tree.forget.labelAt ((List.range n).map path) = some label

/-- Theorem 5.6.1: The signed set contains exactly the formulas in labels
at finite prefixes of the path through the procedure's finite approximants. -/
@[blueprint "chap5__theorem_5_6_1"]
def Run.pathSignedSet {L : FirstOrderLanguage} {hL : L.hasEquality = true}
    (run : Run L hL) (path : Nat → Nat) : Set (SignedFormula L.toLanguage) := fun sf =>
  ∃ n k label,
    (run.state k).tree.forget.labelAt ((List.range n).map path) = some label ∧
    sf ∈ inputSignedSet (InfSequentN.ofSequent label)

/-- Theorem 5.6.1: For every infinite path in the limit tree of the equality
search procedure, the signed set collected along that path is a Hintikka set
with equality over t(TERM₀), the term domain of the same run. -/
@[attach_debt, blueprint "chap5__theorem_5_6_1"]
theorem infinitePath_yields_hintikkaSetEq {L : FirstOrderLanguage}
    {hL : L.hasEquality = true} (run : Run L hL)
    (path : Nat → Nat) (hPath : run.IsInfinitePath path) :
    IsHintikkaSetEq L.toLanguage hL run.termDomain (run.pathSignedSet path) 

/-- Theorem 5.6.1(i): A finite initial subsequent takes the first m
antecedent entries and first n succedent entries, stopping at exhaustion
on either side and preserving their order and multiplicity. -/
@[blueprint "chap5__theorem_5_5_1"]
def initialSubsequent {L : Language} (q : InfSequentN L) (m n : Nat) : Sequent L :=
  .mk ((List.range m).filterMap q.antecedent) ((List.range n).filterMap q.succedent)

/-- Theorem 5.6.1(i): Extract a G_= proof from the specified closed search
round by propagating input formulae to the root, contracting input-introduction
edges, and interpreting equality packets by the printed equality rules.
The equality witness identifies the supplied tree with that run's approximant. -/
@[blueprint "chap5__theorem_5_6_1"]
noncomputable def closedSearchTreeToProofEq {L : Language} (hL : L.hasEquality = true)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (eqEnum : EqEnumeration hL q) (k : Nat)
    (tree : InfGDeductionTreeExt
      (Sequent.mk (q.antecedent 0).toList (q.succedent 0).toList))
    (hTree : tree = (searchEq hL q hq hFB enum eqEnum k).tree.forget)
    (hClosed : ∀ leaf ∈ tree.leaves, isAxiom leaf) :
    Σ s : Sequent L, GEqProofTree hL s := by
  -- REPAIR(T118): proof pending
  sorry

/-- Theorem 5.6.1(i): For every admissible equality-search run on a possibly
infinite input containing equality and satisfying the sequent-wide free/bound
convention, validity implies a closed, finished finite round. The G_= proof
extracted from that same tree concludes a finite initial subsequent of the input. -/
@[attach_debt, blueprint "chap5__theorem_5_6_1" (main := true)]
theorem searchCompletenessEqValid {L : FirstOrderLanguage} (hL : L.hasEquality = true)
    (q : InfSequentN L.toLanguage) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (eqEnum : EqEnumeration hL q)
    (hEq : ∃ A, (q.memAntecedent A ∨ q.memSuccedent A) ∧
      ¬ LCS.FirstOrder.SemanticsN.formulaNoEq A)
    (hValid : infSequentValid q) :
    ∃ k, ∃ hClosed : ∀ leaf ∈ (searchEq hL q hq hFB enum eqEnum k).tree.forget.leaves,
      isAxiom leaf,
      allFinished hL (searchEq hL q hq hFB enum eqEnum k) ∧
      ∃ m n, (closedSearchTreeToProofEq hL q hq hFB enum eqEnum k
        (searchEq hL q hq hFB enum eqEnum k).tree.forget rfl hClosed).1 =
          initialSubsequent q m n 

/-- Theorem 5.6.1(ii): Every admissible equality-search run on a falsifiable
possibly infinite input containing equality has an infinite nonclosed path.
The input is falsified by the canonical assignment in the equality quotient
of that run's t(TERM₀), using precisely the signed set on the selected path.
The quotient domain is countable, allowing both finite and countably infinite models. -/
@[attach_debt, blueprint "chap5__theorem_5_6_1" (main := true)]
theorem searchCompletenessEqFalsifiable {L : FirstOrderLanguage}
    (hL : L.hasEquality = true)
    (q : InfSequentN L.toLanguage) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (eqEnum : EqEnumeration hL q)
    (hEq : ∃ A, (q.memAntecedent A ∨ q.memSuccedent A) ∧
      ¬ LCS.FirstOrder.SemanticsN.formulaNoEq A)
    (hFals : infSequentFalsifiable q) :
    let run : Run L hL := ⟨q, hq, hFB, enum, eqEnum⟩
    ¬ haltsEq hL q hq hFB enum eqEnum ∧
    ∃ path, ∃ hPath : run.IsInfinitePath path,
      (∀ n k label,
        (run.state k).tree.forget.labelAt ((List.range n).map path) = some label →
        ¬ isAxiom label) ∧
      let hHS := infinitePath_yields_hintikkaSetEq run path hPath
      let M := quotientStructureEq hL run.termDomain (run.pathSignedSet path) hHS
      let s := quotAssignment hL run.termDomain (run.pathSignedSet path) hHS
      LCS.FirstOrder.SemanticsN.isCountableDomain M ∧
        (∀ A, q.memAntecedent A → LCS.FirstOrder.SemanticsN.formulaEvalN M A s) ∧
        (∀ B, q.memSuccedent B → ¬ LCS.FirstOrder.SemanticsN.formulaEvalN M B s) 

/-- Definition 5.6.3, descendant remark: Reflexive closure of repeated signed
component descent. Quantified components use terms free for the bound variable. -/
inductive SignedDescendant {L : Language} : SignedFormula L → SignedFormula L → Prop where
  | refl (A : SignedFormula L) : SignedDescendant A A
  | a1 (a : TypeA L) {X} : SignedDescendant X a.comp1 → SignedDescendant X a.toSigned
  | a2 (a : TypeA L) {X} : SignedDescendant X a.comp2 → SignedDescendant X a.toSigned
  | b1 (b : TypeB L) {X} : SignedDescendant X b.comp1 → SignedDescendant X b.toSigned
  | b2 (b : TypeB L) {X} : SignedDescendant X b.comp2 → SignedDescendant X b.toSigned
  | c (c : TypeC L) (t : Term L) (ht : isFreeForN t c.var c.body) {X} :
      SignedDescendant X (c.comp t ht) → SignedDescendant X c.toSigned
  | d (d : TypeD L) (t : Term L) (ht : isFreeForN t d.var d.body) {X} :
      SignedDescendant X (d.comp t ht) → SignedDescendant X d.toSigned

end LCS.FirstOrder.Equality.Search
end
