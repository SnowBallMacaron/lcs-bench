import LCS.Item
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import Attach
import LCS.FirstOrder.Gentzen.Search.NoFunction.SearchState.ProofsStamp

/-! # The search state of Definition 5.4.9 (Section 5.4.7)

The lists TERM₀, TERM₁ and AVAIL₀, the records FORM₀(i) and FORM₁(i), the search tree
carrying them at its leaves, the operations used by grow-left and grow-right, the
instance terms of a for-all:left or exists:right step, and finished leaves and trees.
Source: Logic for Computer Science, Gallier 2015
-/

section
namespace LCS.FirstOrder.Gentzen.Search.NoFunction
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka

/-- Definition 5.4.9 (companion): A finite or infinite enumeration with
    no holes and no repeated present term. -/
@[blueprint "chap5__definition_5_5_1"]
structure TermStream (L : Language) where
  entries : Nat → Option (Term L)
  noHoles : ∀ n, entries n = none → entries (n + 1) = none
  some_injective : ∀ n m t, entries n = some t → entries m = some t → n = m

/-- Definition 5.4.9 (companion): Extract the variable at a position
    known to contain a variable. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def TermStream.varAt {L : Language} (supply : TermStream L) (n : Nat)
    (h : ∃ i, supply.entries n = some (.var i)) : Nat := h.choose

theorem TermStream.varAt_spec {L : Language} (supply : TermStream L) (n : Nat)
    (h : ∃ i, supply.entries n = some (.var i)) :
    supply.entries n = some (.var (supply.varAt n h)) := h.choose_spec

/-- Definition 5.4.9 (companion): An index is unavailable in the stream
    at and after the cursor. -/
@[blueprint "chap5__definition_5_4_9"]
def BeforeCursor {L : Language} (supply : TermStream L) (cursor i : Nat) : Prop :=
  ∀ n, cursor ≤ n → supply.entries n ≠ some (.var i)

theorem BeforeCursor.mono {L : Language} {supply : TermStream L} {a b i : Nat}
    (h : BeforeCursor supply a i) (hab : a ≤ b) : BeforeCursor supply b i :=
  fun n hn => h n (Nat.le_trans hab hn)

/-- The selected variable cannot occur later in an injective stream. -/
theorem TermStream.varAt_beforeSucc {L : Language} (supply : TermStream L) (n : Nat)
    (h : ∃ i, supply.entries n = some (.var i)) :
    BeforeCursor supply (n + 1) (supply.varAt n h) := by
  intro m hm heq
  have hnm := supply.some_injective n m _ (supply.varAt_spec n h) heq
  omega

/-- Definition 5.4.9 (companion): Formula-use records for one branch.
    The entries of `form0` correspond to the global TERM₀ list at the
    start of a round; `form1` records applications during that round,
    with entries corresponding to TERM₁. -/
@[blueprint "chap5__definition_5_4_9"]
structure BranchRecords (L : Language) where
  form0 : List (List (FormulaN L))
  form1 : List (List (FormulaN L))

/-- Definition 5.4.9 (companion): A search tree indexed by its conclusion,
    with a separate formula-use record at each leaf. Inference nodes carry
    the extended G rules of Definition 5.4.8. -/
@[blueprint "chap5__definition_5_4_9"]
inductive SearchTree {L : Language} : Sequent L → Type where
  | leaf (s : Sequent L) (records : BranchRecords L) : SearchTree s
  | onePremise {prem conc : Sequent L}
      (rule : GentzenStep1Ext prem conc) (t : SearchTree prem) : SearchTree conc
  | twoPremise {p1 p2 conc : Sequent L}
      (rule : GentzenStep2Ext p1 p2 conc)
      (t1 : SearchTree p1) (t2 : SearchTree p2) : SearchTree conc

namespace SearchTree

/-- Definition 5.4.9 (companion): Extension by replacing leaves with
    subtrees rooted at the same sequent. Existing inference nodes, their
    rules, and their ordered premises are preserved. Formula-use records
    at replaced leaves may change. -/
@[blueprint "chap5__definition_5_4_9"]
inductive Extends {L : Language} : {s : Sequent L} → SearchTree s → SearchTree s → Prop where
  | leaf {s : Sequent L} (records : BranchRecords L) (t : SearchTree s) :
      Extends (.leaf s records) t
  | onePremise {prem conc : Sequent L} (rule : GentzenStep1Ext prem conc)
      {t t' : SearchTree prem} (h : Extends t t') :
      Extends (.onePremise rule t) (.onePremise rule t')
  | twoPremise {p1 p2 conc : Sequent L} (rule : GentzenStep2Ext p1 p2 conc)
      {t1 t1' : SearchTree p1} {t2 t2' : SearchTree p2}
      (h1 : Extends t1 t1') (h2 : Extends t2 t2') :
      Extends (.twoPremise rule t1 t2) (.twoPremise rule t1' t2')

/-- Definition 5.4.9 (companion): Forget the leaf records, preserving every
    sequent and inference. The resulting deduction tree supplies the
    `isProof` and `isClosed` predicates. -/
@[blueprint "chap5__definition_5_4_9"]
def toDeductionTree {L : Language} :
    {s : Sequent L} → SearchTree s → GDeductionTreeExt s
  | _, .leaf s _ => .leaf s
  | _, .onePremise rule t => .onePremise rule t.toDeductionTree
  | _, .twoPremise rule t1 t2 =>
      .twoPremise rule t1.toDeductionTree t2.toDeductionTree

/-- Definition 5.4.9 (companion): The leaf sequents and their branch records
    in left-to-right order. Equal sequents on different branches retain
    their separate records. -/
@[blueprint "chap5__definition_5_4_9"]
def leaves {L : Language} :
    {s : Sequent L} → SearchTree s → List (Sequent L × BranchRecords L)
  | _, .leaf s records => [(s, records)]
  | _, .onePremise _ t => t.leaves
  | _, .twoPremise _ t1 t2 => t1.leaves ++ t2.leaves

/-- Definition 5.4.9 (companion): Commit FORM₁ to FORM₀ at every leaf.
    New global terms have empty usage lists on branches where they have
    not yet been used. Both snapshots are aligned with the committed
    global term count. -/
@[blueprint "chap5__definition_5_4_9"]
def commitRound {L : Language} (termCount : Nat) :
    {s : Sequent L} → SearchTree s → SearchTree s
  | _, .leaf s records =>
      let forms := records.form1 ++ List.replicate (termCount - records.form1.length) []
      .leaf s { form0 := forms, form1 := forms }
  | _, .onePremise rule t => .onePremise rule (t.commitRound termCount)
  | _, .twoPremise rule t1 t2 =>
      .twoPremise rule (t1.commitRound termCount) (t2.commitRound termCount)

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Committing branch records preserves every sequent and inference. -/
theorem toDeductionTree_commitRound {L : Language} {s : Sequent L}
    (t : SearchTree s) (termCount : Nat) :
    (t.commitRound termCount).toDeductionTree = t.toDeductionTree := by
  induction t with
  | leaf s records => rfl
  | onePremise rule t ih => simp only [commitRound, toDeductionTree, ih]
  | twoPremise rule t1 t2 ih1 ih2 =>
      simp only [commitRound, toDeductionTree, ih1, ih2]

/-- Committing the new leaf records preserves an extension. -/
theorem Extends.commitRound {L : Language} {s : Sequent L}
    {t t' : SearchTree s} (h : t.Extends t') (termCount : Nat) :
    t.Extends (t'.commitRound termCount) := by
  induction h with
  | leaf records t => exact .leaf records _
  | onePremise rule h ih => exact .onePremise rule ih
  | twoPremise rule h1 h2 ih1 ih2 => exact .twoPremise rule ih1 ih2

end SearchTree

/-- Definition 5.4.9 (companion): Global term lists and a cursor in a
    fixed availability enumeration. The stream parameter remains the same
    throughout a run; `availNext` counts consumed positions, independently
    of the indices of variables stored at those positions. -/
@[blueprint "chap5__definition_5_4_9"]
structure SearchState (L : Language) (supply : TermStream L) : Type 1 where
  /-- The ordered global term list at the start of the round. -/
  TERM0 : List (Term L)
  /-- The in-round global term list. -/
  TERM1 : List (Term L)
  /-- The first unconsumed position in the availability stream. -/
  availNext : Nat

namespace SearchState

/-- Definition 5.4.9 (companion): The ordered global term list t(TERM₀). -/
@[blueprint "chap5__definition_5_4_9"]
def tTERM0 {L : Language} {supply : TermStream L} (st : SearchState L supply) : List (Term L) :=
  st.TERM0

/-- Definition 5.4.9 (companion): `AVAIL₀ := tail(AVAIL₀)` — advance
    the bookkeeping `availNext` index by one, equivalently popping the
    head of the implicit infinite stream. Always well-defined. -/
@[blueprint "chap5__definition_5_4_9"]
def tailAVAIL0 {L : Language} {supply : TermStream L} (st : SearchState L supply) : SearchState L supply :=
  { st with availNext := st.availNext + 1 }

/-- Definition 5.4.9 (companion): `TERM₁ := append(TERM₁, ⟨y, nil⟩)` —
    append a new fresh eigenvariable `y` to the global in-round TERM₁
    buffer. Branch records receive empty entries at the round boundary. Used by `grow-left` (∃:left case) and
    `grow-right` (∀:right case) per §5.4.9 lines 161-162 and 195-196. -/
@[blueprint "chap5__definition_5_4_9"]
def appendTERM1 {L : Language} {supply : TermStream L} (st : SearchState L supply) (y : Term L) :
    SearchState L supply :=
  { st with TERM1 := st.TERM1 ++ [y] }

/-- Definition 5.4.9 (companion): Append the principal formula `A` to
    FORM₁(k) on one branch. FORM₀ remains the start-of-round snapshot.
    The index `k` corresponds to the global TERM₁ list; an out-of-range
    index leaves the branch records unchanged. -/
@[blueprint "chap5__definition_5_4_9"]
def appendFORM1 {L : Language} (records : BranchRecords L)
    (k : Nat) (A : FormulaN L) : BranchRecords L :=
  { records with form1 :=
      records.form1.mapIdx (fun i forms => if i = k then forms ++ [A] else forms) }

/-- Definition 5.4.9 (companion): Whether the principal formula `A` has
    already been used with term index `k` on this branch. The query reads
    the branch's start-of-round FORM₀; a missing entry records no use. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def isUsed {L : Language} (records : BranchRecords L)
    (k : Nat) (A : FormulaN L) : Prop :=
  match records.form0[k]? with
  | none => False
  | some forms => A ∈ forms

/-- Definition 5.4.9 (companion): Commit the round's global TERM₁ to
    TERM₀ and every leaf's FORM₁ to FORM₀. AVAIL₀ is unchanged. -/
@[blueprint "chap5__definition_5_4_9"]
def commitRound {L : Language} {supply : TermStream L} (st : SearchState L supply) {s : Sequent L}
    (t : SearchTree s) : SearchTree s × SearchState L supply :=
  (t.commitRound st.TERM1.length, { st with TERM0 := st.TERM1 })

-- ===================================================================
-- Definition 5.4.9: finished leaf / finished tree (§5.4.7 lines 65-67)
-- ===================================================================

/-- Definition 5.4.9 (companion, `finished` — §5.4.7 lines 65-67):
    A leaf of the tree constructed by procedure `search` is finished
    iff either:
    (1) The sequent labeling it is an axiom, or
    (2) The sequent contains only atoms or formulae `∀x A` (resp.
        `∃x A` on the right) belonging to all of the lists `FORM₀(i)`
        for all records `⟨u_i, FORM₀(i)⟩` in TERM₀.

    Textbook §5.4.7 lines 65-67 verbatim:
    "A leaf of the tree constructed by procedure search is finished
     iff either:
     (1) The sequent labeling it is an axiom, or
     (2) The sequent contains only atoms or formulae ∀x A (or ∃x A)
         belonging to all of the lists FORM₀(i) for all
         ⟨u_i, FORM₀(i)⟩ in TERM₀."

    Implementation: every antecedent formula is atomic OR `∀x A` with
    `∀x A` used at every record of TERM₀; symmetrically every succedent
    formula is atomic OR `∃x A` used at every record of TERM₀. The
    "used-at-every-record" clause reads the leaf's own FORM₀ through
    `isUsed records k A` for every index `k` of the global TERM₀ list.

    The `isAtomic` predicate returns `true` for `.predN` / `.eq_` and
    `false` for all other constructors — matching the textbook "atoms"
    wording (atomic = predicate application or equality).

    `noncomputable` because it dispatches on `isUsed` which uses
    `DecidableEq FormulaN` (classical-propositional). -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def isFinishedLeaf {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false)
    (st : SearchState L supply) (records : BranchRecords L) (leaf : Sequent L) : Prop :=
  isAxiom leaf ∨
    ((∀ A ∈ leaf.antecedent,
        A.isAtomic = true ∨
        (∃ x B, A = FormulaN.all x B ∧
          ∀ k, k < st.TERM0.length → isUsed records k A)) ∧
     (∀ B ∈ leaf.succedent,
        B.isAtomic = true ∨
        (∃ x C, B = FormulaN.ex x C ∧
          ∀ k, k < st.TERM0.length → isUsed records k B)))

end SearchState

/-- Definition 5.4.9 (companion, `finished` tree — §5.4.7 line 65):
    A search tree is finished iff every leaf is finished using its own
    branch records (in the sense of `SearchState.isFinishedLeaf`). This is
    the termination predicate for the outer `while not all leaves of
    T are finished do` loop of §5.4.9 line 87. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def isFinishedTree {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false) {s : Sequent L}
    (t : SearchTree s) (st : SearchState L supply) : Prop :=
  ∀ l ∈ t.leaves, SearchState.isFinishedLeaf hNoEq st l.2 l.1

end LCS.FirstOrder.Gentzen.Search.NoFunction

end
