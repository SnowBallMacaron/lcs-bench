import LCS.Item
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Gentzen.Search.NoFunction.Initialization
import LCS.FirstOrder.Gentzen.Search.NoFunction.Growth
import LCS.FirstOrder.Gentzen.Search.NoFunction.LeafInvariant
import LCS.FirstOrder.Gentzen.Search.NoFunction.Search
import Attach
import LCS.FirstOrder.Gentzen.Search.NoFunction.Contracts.ProofsStamp

section
namespace LCS.FirstOrder.Gentzen.Search.NoFunction
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.Hintikka

/-- Definition 5.4.9 (companion): Every sequent admits a formula-wise
    bound-variable renaming apart. Lemma 5.3.4's rectification traversal
    uses a common fresh counter on both sides, retains formula order,
    and preserves each formula's interpretation under every assignment. -/
@[blueprint "chap5__definition_5_4_9"]
theorem exists_renamingApart {L : Language} (hNoEq : L.hasEquality = false)
    (seq : Sequent L) :
    ∃ (n : Nat) (variant : Sequent L),
      variant.antecedent = seq.antecedent.map (fun A => (rectifyAux A id n).1) ∧
      variant.succedent = seq.succedent.map (fun A => (rectifyAux A id n).1) ∧
      (∀ A ∈ seq.antecedent ++ seq.succedent, ∀ (M : Structure L) (s : Assignment M),
        formulaEvalN M (rectifyAux A id n).1 s ↔ formulaEvalN M A s) ∧
      crossNoFreeBound variant 

end LCS.FirstOrder.Gentzen.Search.NoFunction
end

section
namespace LCS.FirstOrder.Gentzen.Search.NoFunction
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.Hintikka

/-- Definition 5.4.9 (companion): A particular leaf occurrence, addressed
    from the root. Unary children and left children use `false`; right
    children use `true`. The empty address denotes the root leaf. -/
@[blueprint "chap5__definition_5_4_9"]
inductive SearchTree.LeafAt {L : Language} (leaf : Sequent L) (records : BranchRecords L) :
    {s : Sequent L} → SearchTree s → List Bool → Prop where
  | here : LeafAt leaf records (.leaf leaf records) []
  | one {prem conc : Sequent L} (rule : GentzenStep1Ext prem conc)
      {t : SearchTree prem} {p : List Bool} (h : LeafAt leaf records t p) :
      LeafAt leaf records (.onePremise rule t) (false :: p)
  | left {p1 p2 conc : Sequent L} (rule : GentzenStep2Ext p1 p2 conc)
      {t1 : SearchTree p1} (t2 : SearchTree p2) {p : List Bool}
      (h : LeafAt leaf records t1 p) :
      LeafAt leaf records (.twoPremise rule t1 t2) (false :: p)
  | right {p1 p2 conc : Sequent L} (rule : GentzenStep2Ext p1 p2 conc)
      (t1 : SearchTree p1) {t2 : SearchTree p2} {p : List Bool}
      (h : LeafAt leaf records t2 p) :
      LeafAt leaf records (.twoPremise rule t1 t2) (true :: p)

/-- Definition 5.4.9 (companion): An exhausted non-axiom leaf at a round
    boundary has a non-axiom descendant at every later round. The address
    prefix keeps the conclusion local to that particular branch. -/
theorem search_exhausted_leaf_stays_open {L : Language}
    (hNoEq : L.hasEquality = false) (hNoFunc : L.funSymbols → False)
    (seq : Sequent L) (hCNFB : crossNoFreeBound seq) (initial : Init seq)
    (k : Nat) (p : List Bool) (leaf : Sequent L) (records : BranchRecords L)
    (hLeaf : SearchTree.LeafAt leaf records (search hNoEq hNoFunc seq hCNFB initial k).1 p)
    (hFinished : SearchState.isFinishedLeaf hNoEq
      (search hNoEq hNoFunc seq hCNFB initial k).2 records leaf)
    (hOpen : ¬ isAxiom leaf) :
    ∀ m, k ≤ m → ∃ (suffix : List Bool) (leaf' : Sequent L) (records' : BranchRecords L),
      SearchTree.LeafAt leaf' records'
        (search hNoEq hNoFunc seq hCNFB initial m).1 (p ++ suffix) ∧ ¬ isAxiom leaf' := by
  intro m hkm
  by_cases hEq : k = m
  · subst m
    exact ⟨[], leaf, records, by simpa using hLeaf, hOpen⟩
  · -- REPAIR(T90): proof pending
    sorry

/-- Definition 5.4.9 (companion): The terms selected for an instance step
    from the fixed TERM₀ and this branch's FORM₀ snapshot. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def SearchState.instanceTerms {L : Language} {supply : TermStream L}
    (st : SearchState L supply) (records : BranchRecords L) (A : FormulaN L) : List (Term L) := by
  classical
  exact ((st.tTERM0.mapIdx (fun k t => (t, k))).filter
    (fun p => ¬ SearchState.isUsed records p.2 A)).map Prod.fst

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.4.9 (companion): The actual term list of a root instance
    inference; a leaf or any other inference has no such list. -/
def SearchTree.rootInstanceTerms {L : Language} : {s : Sequent L} → SearchTree s → Option (List (Term L))
  | _, .onePremise (.allLeft ts _ _ _ _ _ _ _) _ => some ts
  | _, .onePremise (.exRight ts _ _ _ _ _ _ _) _ => some ts
  | _, _ => none

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem SearchTree.rootInstanceTerms_cast {L : Language} {s s' : Sequent L}
    (h : s = s') (t : SearchTree s) : (h ▸ t).rootInstanceTerms = t.rootInstanceTerms := by
  cases h
  rfl





-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.4.9 (companion): Equal TERM₀ and FORM₀ snapshots select
    the same substitutions, independently of in-round TERM₁/FORM₁ changes. -/
theorem SearchState.instanceTerms_eq {L : Language} {supply : TermStream L}
    (st st' : SearchState L supply) (records records' : BranchRecords L) (A : FormulaN L)
    (hTerms : st.TERM0 = st'.TERM0) (hRecords : records.form0 = records'.form0) :
    st.instanceTerms records A = st'.instanceTerms records' A := by
  cases records with
  | mk f0 f1 =>
    cases records' with
    | mk g0 g1 =>
      dsimp only at hRecords
      cases hRecords
      simp only [instanceTerms, tTERM0, isUsed, hTerms]
      rfl







end LCS.FirstOrder.Gentzen.Search.NoFunction
end

