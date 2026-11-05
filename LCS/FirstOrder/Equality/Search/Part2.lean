import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Equality
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Equality.Search.Part1
import Attach
import LCS.FirstOrder.Equality.Search.Part2.ProofsStamp

section
namespace LCS.FirstOrder.Equality.Search
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Completeness.Search

/-- Definition 5.6.3: The round-k equality-search approximant for fixed
admissible TERMS, AVAIL and EQ enumerations of the input reduct. -/
@[blueprint "chap5__definition_5_6_3" (main := true)]
noncomputable def searchEq {L : Language} (hL : L.hasEquality = true)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (eqEnum : EqEnumeration hL q) (k : Nat) :
    SearchState L (Sequent.mk (q.antecedent 0).toList (q.succedent 0).toList) :=
  match k with
  | 0 => SearchState.init hL q hq hFB enum.terms enum.avail eqEnum
  | k + 1 => searchRound hL (searchEq hL q hq hFB enum eqEnum k)

/-- Definition 5.6.3: Equality search halts exactly when all leaves of some
finite-round approximant are finished, that is, axioms. -/
@[blueprint "chap5__definition_5_6_3"]
def haltsEq {L : Language} (hL : L.hasEquality = true)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (eqEnum : EqEnumeration hL q) : Prop :=
  ∃ k, allFinished hL (searchEq hL q hq hFB enum eqEnum k)

/-- Definition 5.6.3: The terminal messages, "T is a proof of Γ₀ → Δ₀"
and "Γ₀ → Δ₀ is falsifiable". A deduction tree all of whose leaves are
axioms is a proof (Definition 5.4.2). -/
@[blueprint "chap5__definition_5_6_3"]
inductive SearchOutput {L : Language} (root : Sequent L) : Type where
  | proof (T : InfGDeductionTreeExt root)
      (hClosed : ∀ leaf ∈ T.leaves, isAxiom leaf)
  | falsifiable

/-- Definition 5.6.3: While not all leaves are finished, there is no output.
After the loop, if all leaves are closed, write "T is a proof of Γ₀ → Δ₀";
otherwise, write "Γ₀ → Δ₀ is falsifiable". -/
@[blueprint "chap5__definition_5_6_3"]
noncomputable def outputEq {L : Language} (hL : L.hasEquality = true)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (eqEnum : EqEnumeration hL q) (k : Nat) :
    Option (SearchOutput (Sequent.mk (q.antecedent 0).toList (q.succedent 0).toList)) := by
  classical
  let st := searchEq hL q hq hFB enum eqEnum k
  exact if allFinished hL st then
    if hClosed : ∀ leaf ∈ st.tree.forget.leaves, isAxiom leaf then
      some (.proof st.tree.forget hClosed)
    else some .falsifiable
  else none



-- ATTACH-BLOCKER: unsupported untagged inductive
/-- Definition 5.6.3: Tree extension preserves every existing label and
edge and adds nodes only below leaves. -/
inductive InfGDeductionTreeExt.Extension {L : Language} :
    {s t : Sequent L} → InfGDeductionTreeExt s → InfGDeductionTreeExt t → Prop where
  | leaf {s} (t : InfGDeductionTreeExt s) : Extension (.leaf s) t
  | one {s p} (rule : GentzenStep1Ext p s) {a b : InfGDeductionTreeExt p} :
      Extension a b → Extension (.onePremise rule a) (.onePremise rule b)
  | two {s p q} (rule : GentzenStep2Ext p q s)
      {a b : InfGDeductionTreeExt p} {c d : InfGDeductionTreeExt q} :
      Extension a b → Extension c d → Extension (.twoPremise rule a c) (.twoPremise rule b d)
  | intro {s} (a b) {t u : InfGDeductionTreeExt (extendSeq s a b)} :
      Extension t u → Extension (.extend a b t) (.extend a b u)
  | eqIntro {s} (a b) (heads : List (EqEntry L)) (hne : heads ≠ [])
      {t u : InfGDeductionTreeExt (appendHeads (extendSeq s a b) heads)} :
      Extension t u → Extension (.extendEq a b heads hne t) (.extendEq a b heads hne u)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.6.3: Every search-stage tree extends itself. -/
theorem InfGDeductionTreeExt.Extension.refl {L : Language} {s : Sequent L}
    (t : InfGDeductionTreeExt s) : Extension t t := by
  induction t with
  | leaf => exact .leaf _
  | onePremise r _ ih => exact .one r ih
  | twoPremise r _ _ ih₁ ih₂ => exact .two r ih₁ ih₂
  | extend a b _ ih => exact .intro a b ih
  | extendEq a b hs hn _ ih => exact .eqIntro a b hs hn ih

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.6.3: Successive leaf extensions compose. -/
theorem InfGDeductionTreeExt.Extension.trans {L : Language} {s t u : Sequent L}
    {a : InfGDeductionTreeExt s} {b : InfGDeductionTreeExt t} {c : InfGDeductionTreeExt u}
    (h₁ : Extension a b) (h₂ : Extension b c) : Extension a c := by
  induction h₁ generalizing u with
  | leaf => cases h₂ <;> exact .leaf _
  | one r h ih => cases h₂ with | one _ h₂ => exact .one r (ih h₂)
  | two r h₁ h₂ ih₁ ih₂ =>
    cases h₂ with | two _ ha hb => exact .two r (ih₁ ha) (ih₂ hb)
  | intro a b h ih => cases h₂ with | intro _ _ h₂ => exact .intro a b (ih h₂)
  | eqIntro a b hs hn h ih => cases h₂ with | eqIntro _ _ _ _ h₂ => exact .eqIntro a b hs hn (ih h₂)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.6.3: Starting a round only changes formula records. -/
theorem SearchTree.forget_startRound {L : Language} {s : Sequent L} (t : SearchTree s) :
    t.startRound.forget = t.forget := by
  induction t with
  | leaf => rfl
  | onePremise r t ih => simp [SearchTree.startRound, SearchTree.forget, ih]
  | twoPremise r l t ihl iht => simp [SearchTree.startRound, SearchTree.forget, ihl, iht]
  | extend a b t ih => simp [SearchTree.startRound, SearchTree.forget, ih]
  | extendEq a b hs hn t ih => simp [SearchTree.startRound, SearchTree.forget, ih]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.6.3: Committing a round only changes formula records. -/
theorem SearchTree.forget_commitRound {L : Language} {s : Sequent L}
    (t : SearchTree s) (n : Nat) : (t.commitRound n).forget = t.forget := by
  induction t with
  | leaf => rfl
  | onePremise r t ih => simp [SearchTree.commitRound, SearchTree.forget, ih]
  | twoPremise r l t ihl iht => simp [SearchTree.commitRound, SearchTree.forget, ihl, iht]
  | extend a b t ih => simp [SearchTree.commitRound, SearchTree.forget, ih]
  | extendEq a b hs hn t ih => simp [SearchTree.commitRound, SearchTree.forget, ih]









/-- Definition 5.6.3: Read a node label by its tree address, with child 0
for unary and intake edges and children 0 and 1 for binary edges. -/
@[blueprint "chap5__definition_5_6_3"]
def InfGDeductionTreeExt.labelAt {L : Language} :
    {s : Sequent L} → InfGDeductionTreeExt s → List Nat → Option (Sequent L)
  | s, _, [] => some s
  | _, .leaf _, _ :: _ => none
  | _, .onePremise _ t, 0 :: p => t.labelAt p
  | _, .onePremise _ _, (_ + 1) :: _ => none
  | _, .twoPremise _ l _, 0 :: p => l.labelAt p
  | _, .twoPremise _ _ r, 1 :: p => r.labelAt p
  | _, .twoPremise _ _ _, (_ + 2) :: _ => none
  | _, .extend _ _ t, 0 :: p => t.labelAt p
  | _, .extend _ _ _, (_ + 1) :: _ => none
  | _, .extendEq _ _ _ _ t, 0 :: p => t.labelAt p
  | _, .extendEq _ _ _ _ _, (_ + 1) :: _ => none

/-- Definition 5.6.3: The limit tree consists exactly of the labeled nodes
appearing in a finite round approximant of the fixed run. -/
@[blueprint "chap5__definition_5_6_3"]
def searchLimitEq {L : Language} (hL : L.hasEquality = true)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (eqEnum : EqEnumeration hL q) (address : List Nat) (label : Sequent L) : Prop :=
  ∃ k, (searchEq hL q hq hFB enum eqEnum k).tree.forget.labelAt address = some label

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.6.3: Extension preserves the label at every old address. -/
theorem InfGDeductionTreeExt.Extension.labelAt_preserves {L : Language}
    {s t : Sequent L} {a : InfGDeductionTreeExt s} {b : InfGDeductionTreeExt t}
    (h : Extension a b) (p : List Nat) (label : Sequent L)
    (hp : a.labelAt p = some label) : b.labelAt p = some label := by
  induction h generalizing p with
  | leaf t =>
    cases p with
    | nil => cases t <;> exact hp
    | cons => simp [InfGDeductionTreeExt.labelAt] at hp
  | one rule h ih =>
    cases p with
    | nil => exact hp
    | cons i p =>
      cases i with
      | zero => exact ih p hp
      | succ => simp [InfGDeductionTreeExt.labelAt] at hp
  | two rule h₁ h₂ ih₁ ih₂ =>
    cases p with
    | nil => exact hp
    | cons i p =>
      cases i with
      | zero => exact ih₁ p hp
      | succ i =>
        cases i with
        | zero => exact ih₂ p hp
        | succ => simp [InfGDeductionTreeExt.labelAt] at hp
  | intro a b h ih =>
    cases p with
    | nil => exact hp
    | cons i p =>
      cases i with
      | zero => exact ih p hp
      | succ => simp [InfGDeductionTreeExt.labelAt] at hp
  | eqIntro a b hs hn h ih =>
    cases p with
    | nil => exact hp
    | cons i p =>
      cases i with
      | zero => exact ih p hp
      | succ => simp [InfGDeductionTreeExt.labelAt] at hp






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

/-- Corollary of Theorem 5.6.1 (Gödel extended completeness): In a first-order
language with equality, a possibly infinite sequent satisfying sequent-wide
free/bound separation is valid exactly when some finite subsequent has a
G_= proof with the printed extended G and equality rules. -/
@[attach_debt, blueprint "chap5__theorem_5_6_1"]
theorem goedelExtendedCompletenessGEq {L : FirstOrderLanguage}
    (hL : L.hasEquality = true) (q : InfSequentN L.toLanguage)
    (hFB : crossNoFreeBoundInf q) :
    infSequentValid q ↔ ∃ seq : Sequent L.toLanguage,
      LCS.FirstOrder.Completeness.IsFiniteSubsequentInf seq q ∧
        Nonempty (GEqProofTree hL seq) 



/-- Theorem 5.6.1, nontermination remark: Some finite quantifier-free
sequent containing equality has an admissible equality-search run that
never reaches a finished round. -/
@[attach_debt, blueprint "chap5__theorem_5_6_1"]
theorem quantifierFree_searchEq_mayDiverge :
    ∃ (L : FirstOrderLanguage) (hL : L.hasEquality = true)
      (seq : Sequent L.toLanguage)
      (hq : (InfSequentN.ofSequent seq).builtFromX)
      (hFB : crossNoFreeBoundInf (InfSequentN.ofSequent seq))
      (enum : SearchEnumeration (InfSequentN.ofSequent seq))
      (eqEnum : EqEnumeration hL (InfSequentN.ofSequent seq)),
      LCS.FirstOrder.Completeness.sequentQuantifierFree seq ∧
      (∃ A, (A ∈ seq.antecedent ∨ A ∈ seq.succedent) ∧
        ¬ LCS.FirstOrder.SemanticsN.formulaNoEq A) ∧
      ¬ haltsEq hL (InfSequentN.ofSequent seq) hq hFB enum eqEnum 







-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.6.3, subformula remark: Forget the sign of a signed formula. -/
def signedFormulaBody {L : Language} : SignedFormula L → FormulaN L
  | .trueF A | .falseF A => A

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.6.3, subformula remark: Antecedent occurrences have sign T
and succedent occurrences have sign F, retaining order and multiplicity. -/
def sequentSignedFormulae {L : Language} (s : Sequent L) : List (SignedFormula L) :=
  s.antecedent.map SignedFormula.trueF ++ s.succedent.map SignedFormula.falseF

-- ATTACH-BLOCKER: unsupported untagged inductive
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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.6.3, subformula remark: Signed descent implies the
Definition 5.3.9 subformula relation after forgetting signs. -/
theorem SignedDescendant.isSubformula {L : Language} {A B : SignedFormula L}
    (h : SignedDescendant A B) :
    LCS.FirstOrder.Semantics.Subformulae.IsSubformula
      (signedFormulaBody A) (signedFormulaBody B) := by
  induction h with
  | refl A => exact .refl _
  | a1 a h ih =>
    cases a <;> first | exact .conjLeft ih | exact .disjLeft ih |
      exact .implLeft ih | exact .negSub ih
  | a2 a h ih =>
    cases a <;> first | exact .conjRight ih | exact .disjRight ih |
      exact .implRight ih | exact .negSub ih
  | b1 b h ih =>
    cases b <;> first | exact .conjLeft ih | exact .disjLeft ih | exact .implLeft ih
  | b2 b h ih =>
    cases b <;> first | exact .conjRight ih | exact .disjRight ih | exact .implRight ih
  | c c t ht h ih =>
    cases c <;> first | exact .allSub t ht ih | exact .exSub t ht ih
  | d d t ht h ih =>
    cases d <;> first | exact .allSub t ht ih | exact .exSub t ht ih

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.6.3: A node formula is a root subformula when it is a
Definition 5.3.9 subformula of a formula on either side of the root. -/
def RootSubformula {L : Language} (root : Sequent L) (A : FormulaN L) : Prop :=
  ∃ B, B ∈ root.antecedent ++ root.succedent ∧
    LCS.FirstOrder.Semantics.Subformulae.IsSubformula A B

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.6.3: A signed node formula descends from the root when
it descends from one of the root's signed formula occurrences. -/
def RootDescendant {L : Language} (root : Sequent L) (A : SignedFormula L) : Prop :=
  ∃ B, B ∈ sequentSignedFormulae root ∧ SignedDescendant A B

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.6.3: All node sequents of an extended G deduction tree,
including its root, internal nodes, and leaves. -/
def gDeductionSequents {L : Language} : {s : Sequent L} → GDeductionTreeExt s → List (Sequent L)
  | _, .leaf s => [s]
  | s, .onePremise _ sub => s :: gDeductionSequents sub
  | s, .twoPremise _ left right => s :: (gDeductionSequents left ++ gDeductionSequents right)



/-- Definition 5.6.3, G subformula property: Every signed occurrence at
every node of a G deduction tree descends from a root occurrence; its
underlying formula is a Definition 5.3.9 subformula of a root formula. -/
theorem gDeduction_subformulaProperty {L : Language} (hL : L.withoutEquality)
    {root : Sequent L} (tree : GDeductionTreeExt root) :
    ∀ node ∈ gDeductionSequents tree, ∀ A ∈ sequentSignedFormulae node,
      RootDescendant root A ∧ RootSubformula root (signedFormulaBody A) := by
  -- REPAIR(T122): proof pending
  sorry

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.6.3 (search counterexample): The language with equality
and no function, constant, or predicate symbols. -/
def subformulaCounterLanguage : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := Empty
  predSymbols := Empty
  predArity := Empty.elim
  hasEquality := true

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.6.3 (search counterexample): The input is the empty sequent →.
Its initial term supply uses the fallback y₀ = x₁. -/
def subformulaCounterInput : InfSequentN subformulaCounterLanguage :=
  InfSequentN.ofSequent (.mk [] [])

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The empty input meets the variable-supply and free/bound conditions. -/
theorem subformulaCounterInput_admissible :
    subformulaCounterInput.builtFromX ∧ crossNoFreeBoundInf subformulaCounterInput := by
  simp [InfSequentN.builtFromX, crossNoFreeBoundInf, subformulaCounterInput,
    InfSequentN.memAntecedent, InfSequentN.memSuccedent, InfSequentN.ofSequent]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The singleton stream yᵢ, followed by empty markers. -/
def subformulaCounterTermStream (i : Nat) : TermStream subformulaCounterLanguage where
  entries := fun n => if n = 0 then some (yVar i) else none
  noHoles := by intro n h; simp
  some_injective := by
    intro n m t hn hm
    by_cases hn0 : n = 0 <;> by_cases hm0 : m = 0 <;> simp_all

/-- For the empty input, TERMS is {y₀} and each positive AVAILᵢ is {yᵢ}. -/
theorem subformulaCounterTermStream_spec :
    (∀ t, (∃ n, (subformulaCounterTermStream 0).entries n = some t) ↔
      termsTerm subformulaCounterInput t) ∧
    (∀ i, 0 < i → ∀ t, (∃ n, (subformulaCounterTermStream i).entries n = some t) ↔
      availTerm subformulaCounterInput i t) := by
  -- REPAIR(T147): proof pending
  sorry

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Concrete TERMS and AVAIL streams for the empty input. -/
def subformulaCounterEnumeration : SearchEnumeration subformulaCounterInput where
  terms := { subformulaCounterTermStream 0 with
    enumerates := subformulaCounterTermStream_spec.1
    fallback_head := by intro _; rfl }
  avail := fun i hi => { subformulaCounterTermStream i with
    index_pos := hi
    enumerates := subformulaCounterTermStream_spec.2 i hi
    starts_with := rfl }

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Concrete EQ lists for the empty input. EQ₁,ᵢ is the singleton yᵢ ≐ yᵢ;
EQ₂ is empty. EQ₃,ᵢ lists equality-congruence quadruples over y₀,…,yᵢ
in lexicographic index order, requiring an occurrence of yᵢ at positive levels.
All other family indices have empty lists. -/
def subformulaCounterEqEntries (j i : Nat) : List (EqEntry subformulaCounterLanguage) :=
  if j = 1 then
    [⟨.eq_ rfl (yVar i) (yVar i), fun hL => Or.inl ⟨yVar i, rfl⟩⟩]
  else if j = 3 then
    (List.range (i + 1)).flatMap fun a =>
      (List.range (i + 1)).flatMap fun b =>
        (List.range (i + 1)).flatMap fun c =>
          ((List.range (i + 1)).filter fun d =>
            i == 0 || a == i || b == i || c == i || d == i).map fun d =>
              ⟨eqCongruenceImplEq rfl (yVar a) (yVar b) (yVar c) (yVar d),
                fun hL => Or.inr (Or.inr (Or.inr ⟨yVar a, yVar b, yVar c, yVar d, rfl⟩))⟩
  else []

/-- The concrete EQ lists have unique positions and enumerate exactly
Definition 5.6.3's level families, including the mixed positive levels. -/
theorem subformulaCounterEqEntries_spec :
    (∀ (j i n m : Nat) (e : EqEntry subformulaCounterLanguage),
      (subformulaCounterEqEntries j i)[n]? = some e →
      (subformulaCounterEqEntries j i)[m]? = some e → n = m) ∧
    (∀ j i A, (∃ (n : Nat) (e : EqEntry subformulaCounterLanguage),
      (subformulaCounterEqEntries j i)[n]? = some e ∧ e.val = A) ↔
      EqLevelInstance rfl subformulaCounterInput j i A) := by
  -- REPAIR(T147): proof pending
  sorry

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Concrete admissible EQ streams, obtained by indexing the finite EQ lists. -/
def subformulaCounterEqEnumeration : EqEnumeration rfl subformulaCounterInput where
  streams := fun j i => {
    entries := fun n => (subformulaCounterEqEntries j i)[n]?
    noHoles := by
      intro n hn
      have h := List.getElem?_eq_none_iff.mp hn
      exact List.getElem?_eq_none (by omega)
    some_injective := subformulaCounterEqEntries_spec.1 j i }
  enumerates := subformulaCounterEqEntries_spec.2

/-- Definition 5.6.3: At stage 1 of the actual search on →, the child at
address [0] has label y₀ ≐ y₀ →. The round selects EQ₁,₀, whose sole entry
uses the initial fallback y₀ = x₁. That formula is not a subformula of any
root formula because both sides of the input are empty. -/
theorem searchEq_subformula_counterexample :
    let q := InfSequentN.ofSequent (Sequent.mk
      ([] : List (FormulaN subformulaCounterLanguage)) [])
    ∃ label : Sequent subformulaCounterLanguage,
      (searchEq rfl q subformulaCounterInput_admissible.1
        subformulaCounterInput_admissible.2 subformulaCounterEnumeration
        subformulaCounterEqEnumeration 1).tree.forget.labelAt [0] = some label ∧
      label = Sequent.mk [.eq_ rfl (.var 1) (.var 1)] [] ∧
      FormulaN.eq_ rfl (.var 1) (.var 1) ∈ label.antecedent ∧
      ¬ RootSubformula (Sequent.mk ([] : List (FormulaN subformulaCounterLanguage)) [])
        (FormulaN.eq_ rfl (.var 1) (.var 1)) := by
  dsimp only
  refine ⟨Sequent.mk [.eq_ rfl (.var 1) (.var 1)] [], ?_, rfl, ?_, ?_⟩
  · -- REPAIR(T147): proof pending
    sorry
  · simp
  · simp [RootSubformula]





/-- Theorem 5.6.4, consistent-search remark: A nonclosed equality-search
path is an infinite path of the actual run whose every node label is nonaxiomatic. -/
@[blueprint "chap5__theorem_5_6_1"]
def Run.IsNonclosedPath {L : FirstOrderLanguage} {hL : L.hasEquality = true}
    (run : Run L hL) (path : Nat → Nat) : Prop :=
  run.IsInfinitePath path ∧ ∀ n k label,
    (run.state k).tree.forget.labelAt ((List.range n).map path) = some label →
      ¬ isAxiom label

/-- Theorem 5.6.4, consistent-search remark: If Γ is G_=-consistent,
the possibly infinite sequent enumerating exactly Γ with empty succedent
is falsifiable. -/
@[attach_debt, blueprint "chap5__theorem_5_6_4"]
theorem consistent_emptySucc_falsifiable {L : FirstOrderLanguage}
    (hL : L.hasEquality = true) [Countable (FormulaN L.toLanguage)]
    (Gamma : Set (FormulaN L.toLanguage))
    (hCon : LCS.FirstOrder.Equality.MetaTheorems.isConsistentSetEq hL Gamma)
    (q : InfSequentN L.toLanguage)
    (hGamma : ∀ A, q.memAntecedent A ↔ A ∈ Gamma)
    (hEmpty : ∀ n, q.succedent n = none) : infSequentFalsifiable q 

/-- Theorem 5.6.4, consistent-search remark: Every admissible equality
search on Γ → for a consistent Γ has a nonclosed path in its actual limit tree. -/
theorem consistent_search_has_nonclosed_path {L : FirstOrderLanguage}
    (hL : L.hasEquality = true) [Countable (FormulaN L.toLanguage)]
    (Gamma : Set (FormulaN L.toLanguage))
    (hCon : LCS.FirstOrder.Equality.MetaTheorems.isConsistentSetEq hL Gamma)
    (q : InfSequentN L.toLanguage)
    (hGamma : ∀ A, q.memAntecedent A ↔ A ∈ Gamma)
    (hEmpty : ∀ n, q.succedent n = none)
    (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (eqEnum : EqEnumeration hL q) :
    let run : Run L hL := ⟨q, hq, hFB, enum, eqEnum⟩
    ∃ path, run.IsNonclosedPath path := by
  -- REPAIR(T123): proof pending
  sorry

/-- Theorem 5.6.4, conditional search-model remark: For every nonclosed
path and every signed set S arising on it that is Hintikka over the run's
t(TERM₀), the Lemma 5.6.1 quotient structure and canonical assignment
satisfy S and Γ. The carrier is explicitly the equality quotient of t(TERM₀). -/
@[attach_debt, blueprint "chap5__theorem_5_6_4"]
theorem nonclosed_search_path_hintikka_model {L : FirstOrderLanguage}
    {hL : L.hasEquality = true} (run : Run L hL)
    (Gamma : Set (FormulaN L.toLanguage))
    (hGamma : ∀ A, run.input.memAntecedent A ↔ A ∈ Gamma)
    (hEmpty : ∀ n, run.input.succedent n = none)
    (path : Nat → Nat) (hPath : run.IsNonclosedPath path)
    (S : Set (SignedFormula L.toLanguage)) (hS : S = run.pathSignedSet path)
    (hHS : IsHintikkaSetEq L.toLanguage hL run.termDomain S) :
    let M := quotientStructureEq hL run.termDomain S hHS
    let s := quotAssignment hL run.termDomain S hHS
    M.carrier = QType hL run.termDomain S hHS ∧
      (∀ sf ∈ S, SignedFormula.satisfiedBy M s sf) ∧
      (∀ A ∈ Gamma, LCS.FirstOrder.SemanticsN.formulaEvalN M A s) 



end LCS.FirstOrder.Equality.Search
end

