import LCS.Item
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import Attach
import LCS.FirstOrder.Gentzen.Search.NoFunction.Initialization.ProofsStamp

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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem TermStream.varAt_spec {L : Language} (supply : TermStream L) (n : Nat)
    (h : ∃ i, supply.entries n = some (.var i)) :
    supply.entries n = some (.var (supply.varAt n h)) := h.choose_spec

/-- Definition 5.4.9 (companion): An index is unavailable in the stream
    at and after the cursor. -/
@[blueprint "chap5__definition_5_4_9"]
def BeforeCursor {L : Language} (supply : TermStream L) (cursor i : Nat) : Prop :=
  ∀ n, cursor ≤ n → supply.entries n ≠ some (.var i)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem BeforeCursor.mono {L : Language} {supply : TermStream L} {a b i : Nat}
    (h : BeforeCursor supply a i) (hab : a ≤ b) : BeforeCursor supply b i :=
  fun n hn => h n (Nat.le_trans hab hn)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
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

end LCS.FirstOrder.Gentzen.Search.NoFunction
end

section
namespace LCS.FirstOrder.Gentzen.Search.NoFunction
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Committing the new leaf records preserves an extension. -/
theorem Extends.commitRound {L : Language} {s : Sequent L}
    {t t' : SearchTree s} (h : t.Extends t') (termCount : Nat) :
    t.Extends (t'.commitRound termCount) := by
  induction h with
  | leaf records t => exact .leaf records _
  | onePremise rule h ih => exact .onePremise rule ih
  | twoPremise rule h1 h2 ih1 ih2 => exact .twoPremise rule ih1 ih2

end SearchTree
end LCS.FirstOrder.Gentzen.Search.NoFunction
end

section
namespace LCS.FirstOrder.Gentzen.Search.NoFunction
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka

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

end LCS.FirstOrder.Gentzen.Search.NoFunction
end

section
namespace LCS.FirstOrder.Gentzen.Search.NoFunction
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
namespace SearchState

/-- Definition 5.4.9 (companion): The ordered global term list t(TERM₀). -/
@[blueprint "chap5__definition_5_4_9"]
def tTERM0 {L : Language} {supply : TermStream L} (st : SearchState L supply) : List (Term L) :=
  st.TERM0

end SearchState
end LCS.FirstOrder.Gentzen.Search.NoFunction
end

section
namespace LCS.FirstOrder.Gentzen.Search.NoFunction
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka

/-- Definition 5.4.9 (companion): All free and bound variable indices
    occurring in the input sequent. -/
@[blueprint "chap5__definition_5_4_9"]
def sequentVarIndices {L : Language} (seq : Sequent L) : List Nat :=
  (seq.antecedent ++ seq.succedent).flatMap
    (fun A => formulaFreeVarIndices A ++ formulaBoundVarIndices A)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (companion): A strict bound on the input variable indices. -/
def sequentVarBound {L : Language} (seq : Sequent L) : Nat :=
  (sequentVarIndices seq).foldl Nat.max 0 + 1

/-- Definition 5.4.9 (companion): The least index absent from the input.
    The increasing bounded search includes an index beyond every input variable. -/
@[blueprint "chap5__definition_5_4_9"]
def leastAbsentVar {L : Language} (seq : Sequent L) : Nat :=
  let vars := sequentVarIndices seq
  ((List.range (sequentVarBound seq + 1)).find? (fun i => !(vars.contains i))).getD
    (sequentVarBound seq)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem le_foldl_max (xs : List Nat) (b : Nat) : b ≤ xs.foldl Nat.max b := by
  induction xs generalizing b with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.le_trans (Nat.le_max_left b x) (ih (max b x))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem mem_le_foldl_max {xs : List Nat} {i : Nat} (hi : i ∈ xs) (b : Nat) :
    i ≤ xs.foldl Nat.max b := by
  induction xs generalizing b with
  | nil => cases hi
  | cons x xs ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · exact Nat.le_trans (Nat.le_max_right b i) (le_foldl_max xs (max b i))
    · exact ih hi (max b x)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem sequentVarIndices_lt_bound {L : Language} (seq : Sequent L) {i : Nat}
    (hi : i ∈ sequentVarIndices seq) : i < sequentVarBound seq :=
  Nat.lt_succ_of_le (mem_le_foldl_max hi 0)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The bounded search returns the least absent variable. -/
theorem leastAbsentVar_spec {L : Language} (seq : Sequent L) :
    leastAbsentVar seq ∉ sequentVarIndices seq ∧
    leastAbsentVar seq ≤ sequentVarBound seq ∧
    (∀ i, i < leastAbsentVar seq → i ∈ sequentVarIndices seq) := by
  let vars := sequentVarIndices seq
  let bound := sequentVarBound seq
  have hAbsent : bound ∉ vars := by
    intro h; exact Nat.lt_irrefl _ (sequentVarIndices_lt_bound seq h)
  have hSome : ∃ i, (List.range (bound + 1)).find? (fun i => !(vars.contains i)) = some i := by
    cases h : (List.range (bound + 1)).find? (fun i => !(vars.contains i)) with
    | some i => exact ⟨i, rfl⟩
    | none =>
      have hNone := List.find?_eq_none.mp h bound (List.mem_range.mpr (Nat.lt_succ_self _))
      simp [hAbsent] at hNone
  obtain ⟨i, hi⟩ := hSome
  have hLeast : leastAbsentVar seq = i := by
    unfold leastAbsentVar
    change ((List.range (bound + 1)).find? (fun i => !(vars.contains i))).getD bound = i
    rw [hi]; rfl
  rw [hLeast]
  have hNot : i ∉ vars := by simpa using List.find?_some hi
  have hiRange := List.mem_of_find?_eq_some hi
  have hiLe : i ≤ bound := by have := List.mem_range.mp hiRange; omega
  refine ⟨hNot, hiLe, ?_⟩
  intro j hj
  obtain ⟨_, as, bs, hSplit, hBefore⟩ := List.find?_eq_some_iff_append.mp hi
  have hjRange : j ∈ List.range (bound + 1) := List.mem_range.mpr (by omega)
  rw [hSplit, List.mem_append, List.mem_cons] at hjRange
  have hIn : j ∈ as := by
    rcases hjRange with hIn | hEq | hTail
    · exact hIn
    · omega
    · have hPair : (as ++ i :: bs).Pairwise (· < ·) := hSplit ▸ List.pairwise_lt_range
      have hlt := List.rel_of_pairwise_cons (List.pairwise_append.mp hPair).2.1 hTail
      omega
  simpa using hBefore j hIn

/-- Definition 5.4.9 (companion): The repetition-free initial term list.
    A sequent with no free variables or constants receives the least absent variable. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def initialTerms {L : Language} (seq : Sequent L) : List (Term L) := by
  classical
  let forms := seq.antecedent ++ seq.succedent
  let freeVars := forms.flatMap formulaFreeVarIndices
  let consts := forms.flatMap formulaConstsList
  let terms := (freeVars.map (Term.var (L := L)) ++ consts).eraseDups
  exact if terms.isEmpty then [.var (leastAbsentVar seq)] else terms

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (companion): Canonical TERM₀ for the equality-free input. -/
noncomputable def initialTERM0 {L : Language} (hNoEq : L.hasEquality = false)
    (seq : Sequent L) : List (Term L) := initialTerms seq

/-- Definition 5.4.9 (companion): An initial term list containing exactly the
    input's free variables and constants, allowing repeated generators. With no
    generators, it is the singleton containing the least absent variable.
    The infinite injective variable supply is fresh for the input and disjoint
    from those terms. -/
@[blueprint "chap5__definition_5_4_9"]
def admissibleInitialization {L : Language} (seq : Sequent L)
    (terms : List (Term L)) (avail : TermStream L) : Prop :=
  (∀ t, t ∈ terms ↔ t ∈ initialTerms seq) ∧
  (∀ n, ∃ i, avail.entries n = some (.var i) ∧ i ∉ sequentVarIndices seq) ∧
  (∀ n t, avail.entries n = some t → t ∉ terms) ∧
  ((seq.antecedent ++ seq.succedent).flatMap formulaFreeVarIndices = [] →
    (seq.antecedent ++ seq.succedent).flatMap formulaConstsList = [] →
    terms = [.var (leastAbsentVar seq)])

/-- Definition 5.4.9 (companion): An admissible initialization of a run. -/
@[blueprint "chap5__definition_5_4_9"]
structure Init {L : Language} (seq : Sequent L) where
  term0 : List (Term L)
  avail0 : TermStream L
  admissible : admissibleInitialization seq term0 avail0


/-- Definition 5.4.9 (companion): An increasing variable supply starting
    at the given index. -/
@[blueprint "chap5__definition_5_4_9"]
def TermStream.variablesFrom (L : Language) (start : Nat) : TermStream L where
  entries n := some (.var (start + n))
  noHoles := by intro n h; cases h
  some_injective := by
    intro n m t hn hm
    have h := Term.var.inj (Option.some.inj (hn.trans hm.symm))
    omega

end LCS.FirstOrder.Gentzen.Search.NoFunction
end

section
namespace LCS.FirstOrder.Gentzen.Search.NoFunction
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
namespace SearchState

/-- Definition 5.4.9 (companion): Start at the first position of the
    supplied availability stream with matching TERM₀ and TERM₁. -/
@[blueprint "chap5__definition_5_4_9"]
def init {L : Language} {seq : Sequent L} (initial : Init seq) :
    SearchState L initial.avail0 :=
  { TERM0 := initial.term0, TERM1 := initial.term0, availNext := 0 }

/-- Definition 5.4.9 (companion): The first unconsumed entry of AVAIL₀.
    An exhausted stream returns `none`; the search invariant ensures that
    admissible §5.4.9 runs have a variable at every position. -/
@[blueprint "chap5__definition_5_4_9"]
def headAVAIL0 {L : Language} {supply : TermStream L} (st : SearchState L supply) : Option (Term L) :=
  supply.entries st.availNext

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
end LCS.FirstOrder.Gentzen.Search.NoFunction
end

section
namespace LCS.FirstOrder.Gentzen.Search.NoFunction
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka

/-- Definition 5.4.9 (companion, `finished` tree — §5.4.7 line 65):
    A search tree is finished iff every leaf is finished using its own
    branch records (in the sense of `SearchState.isFinishedLeaf`). This is
    the termination predicate for the outer `while not all leaves of
    T are finished do` loop of §5.4.9 line 87. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def isFinishedTree {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false) {s : Sequent L}
    (t : SearchTree s) (st : SearchState L supply) : Prop :=
  ∀ l ∈ t.leaves, SearchState.isFinishedLeaf hNoEq st l.2 l.1

-- ===================================================================
-- SearchState invariant (textbook §5.4.7 variable bookkeeping)
-- ===================================================================

/-- Definition 5.4.9 (companion, invariant): A Nat `bound` is above all
    variable indices in `seq` if every formula of `seq` has all free
    and bound variable indices strictly less than `bound`. Used to
    state the `SearchState.Inv` invariant below. -/
@[blueprint "chap5__definition_5_4_9"]
def NoVarAbove {L : Language} (seq : Sequent L) (bound : Nat) : Prop :=
  ∀ F ∈ seq.antecedent ++ seq.succedent,
    (∀ j ∈ formulaFVN F, j < bound) ∧ (∀ j ∈ formulaBVN F, j < bound)

end LCS.FirstOrder.Gentzen.Search.NoFunction
end

section
namespace LCS.FirstOrder.Gentzen.Search.NoFunction
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
namespace SearchState

/-- Definition 5.4.9 (companion): The input's bound variables stay below
    `bound`. Available entries are variables fresh for those binders.
    Activated variables are either input free variables or fresh for its
    binders, and no variable in TERM₀ or TERM₁ occurs in the unconsumed
    availability stream. These conditions permit any injective enumeration,
    including enumerations whose variable indices do not increase. -/
@[blueprint "chap5__definition_5_4_9"]
structure Inv {L : Language} {supply : TermStream L} (seq : Sequent L) (bound : Nat)
    (st : SearchState L supply) : Prop where
  bound_above_seq : NoVarAbove seq bound
  available_vars : ∀ n, ∃ i, supply.entries n = some (.var i)
  avail_fresh : ∀ n, st.availNext ≤ n → ∀ i, supply.entries n = some (.var i) →
    ∀ F ∈ seq.antecedent ++ seq.succedent, i ∉ formulaBVN F
  terms_allowed : ∀ rec ∈ st.TERM0,
    ∀ i, rec = Term.var i →
      (∃ F ∈ seq.antecedent ++ seq.succedent, i ∈ formulaFVN F) ∨
      ∀ F ∈ seq.antecedent ++ seq.succedent, i ∉ formulaBVN F
  terms1_allowed : ∀ rec ∈ st.TERM1,
    ∀ i, rec = Term.var i →
      (∃ F ∈ seq.antecedent ++ seq.succedent, i ∈ formulaFVN F) ∨
      ∀ F ∈ seq.antecedent ++ seq.succedent, i ∉ formulaBVN F
  terms_below_avail : ∀ rec ∈ st.TERM0,
    ∀ i, rec = Term.var i → BeforeCursor supply st.availNext i
  terms1_below_avail : ∀ rec ∈ st.TERM1,
    ∀ i, rec = Term.var i → BeforeCursor supply st.availNext i




-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Growth
/-- Definition 5.4.9 (companion, invariant): `tailAVAIL0` preserves the
    state invariant. Increments `availNext`; `bound`, TERM₀, and TERM₁
    unchanged. -/
theorem tailAVAIL0_preserves_Inv {L : Language} {supply : TermStream L} {seq : Sequent L} {bound : Nat}
    {st : SearchState L supply} (h : Inv seq bound st) : Inv seq bound st.tailAVAIL0 := by
  refine ⟨h.bound_above_seq, h.available_vars, ?_, h.terms_allowed, h.terms1_allowed, ?_, ?_⟩
  · intro n hn i hi
    exact h.avail_fresh n (Nat.le_trans (Nat.le_succ _) hn) i hi
  · intro t ht i hi
    exact (h.terms_below_avail t ht i hi).mono (Nat.le_succ _)
  · intro t ht i hi
    exact (h.terms1_below_avail t ht i hi).mono (Nat.le_succ _)

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Growth
/-- Definition 5.4.9 (companion, invariant): `appendTERM1` preserves
    the state invariant. Only `TERM1` changes; TERM₀, availNext, bound
    are untouched. The caller must witness that the appended `y` (if
    a variable) is either free-in-seq or ≥ bound — typically discharged
    via `avail_above_bound` when `y = Term.var (supply.varAt st.availNext (hInv.available_vars st.availNext))`. -/
theorem appendTERM1_preserves_Inv {L : Language} {supply : TermStream L} {seq : Sequent L}
    {bound : Nat} {st : SearchState L supply} {y : Term L}
    (h : Inv seq bound st)
    (hy : ∀ i, y = Term.var i →
      (∃ F ∈ seq.antecedent ++ seq.succedent, i ∈ formulaFVN F) ∨
      (∀ F ∈ seq.antecedent ++ seq.succedent, i ∉ formulaBVN F))
    (hy_strict : ∀ i, y = Term.var i → BeforeCursor supply st.availNext i) :
    Inv seq bound (st.appendTERM1 y) := by
-- BEGIN PROOF
  refine ⟨h.bound_above_seq, h.available_vars, h.avail_fresh, h.terms_allowed, ?_, h.terms_below_avail, ?_⟩
  · -- terms1_allowed preservation
    intro rec hRec i hi
    unfold appendTERM1 at hRec
    simp only at hRec
    rw [List.mem_append] at hRec
    rcases hRec with h1 | h2
    · exact h.terms1_allowed rec h1 i hi
    · rw [List.mem_singleton] at h2
      rw [h2] at hi
      apply hy i
      exact hi
  · -- terms1_below_avail preservation
    intro rec hRec i hi
    unfold appendTERM1 at hRec
    simp only at hRec
    rw [List.mem_append] at hRec
    rcases hRec with h1 | h2
    · exact h.terms1_below_avail rec h1 i hi
    · rw [List.mem_singleton] at h2
      rw [h2] at hi
      exact hy_strict i hi

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Definition 5.4.9 (companion, invariant): `commitRound` preserves
    the state invariant. Since `Inv`'s `terms1_allowed` field tracks
    the TERM₁ allowed-variable property, committing TERM₀ := TERM₁
    straightforwardly moves that property to `terms_allowed`. -/
theorem commitRound_preserves_Inv {L : Language} {supply : TermStream L} {seq : Sequent L}
    {bound : Nat} {st : SearchState L supply} (h : Inv seq bound st)
    {s : Sequent L} (t : SearchTree s) :
    Inv seq bound (st.commitRound t).2 :=
  ⟨h.bound_above_seq, h.available_vars, h.avail_fresh, h.terms1_allowed,
    h.terms1_allowed, h.terms1_below_avail, h.terms1_below_avail⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (required helper): `formulaConstsList F` contains
    only `Term.const` values (never `Term.var`). Structural induction
    on `F` using the same fact for `termConstsList` on `Term L`. -/
theorem not_var_mem_formulaConstsList {L : Language}
    (F : FormulaN L) (i : Nat) :
    Term.var i ∉ formulaConstsList F := by
-- BEGIN PROOF
  -- First establish the term-level version.
  have termHelper : ∀ (t : Term L), Term.var i ∉ termConstsList t := by
    intro t
    induction t with
    | var _ => simp [termConstsList]
    | const _ => simp [termConstsList]
    | func f ts ih =>
      -- Term.var i ∈ foldl (fun acc j => acc ++ termConstsList (ts j)) []
      -- ⇒ Term.var i ∈ some termConstsList (ts j), contradicting ih.
      simp only [termConstsList]
      intro h
      have : ∀ (acc : List (Term L)) (l : List (Fin (L.funArity f))),
        Term.var i ∉ acc →
        Term.var i ∉ l.foldl (fun a j => a ++ termConstsList (ts j)) acc := by
        intro acc l hAcc
        induction l generalizing acc with
        | nil => exact hAcc
        | cons hd tl ih' =>
          apply ih'
          intro hMem
          rw [List.mem_append] at hMem
          rcases hMem with h1 | h2
          · exact hAcc h1
          · exact ih hd h2
      exact this [] _ (by simp) h
  -- Now induct on F.
  induction F with
  | predN P ts =>
    simp only [formulaConstsList]
    intro h
    -- Same foldl argument at the predicate level.
    have : ∀ (acc : List (Term L)) (l : List (Fin (L.predArity P))),
      Term.var i ∉ acc →
      Term.var i ∉ l.foldl (fun a j => a ++ termConstsList (ts j)) acc := by
      intro acc l hAcc
      induction l generalizing acc with
      | nil => exact hAcc
      | cons hd tl ih' =>
        apply ih'
        intro hMem
        rw [List.mem_append] at hMem
        rcases hMem with h1 | h2
        · exact hAcc h1
        · exact termHelper (ts hd) h2
    exact this [] _ (by simp) h
  | eq_ _ t1 t2 =>
    simp only [formulaConstsList]
    intro h
    rw [List.mem_append] at h
    rcases h with h | h
    · exact termHelper t1 h
    · exact termHelper t2 h
  | neg A ih => simp only [formulaConstsList]; exact ih
  | conj A B ihA ihB =>
    simp only [formulaConstsList]
    intro h
    rw [List.mem_append] at h
    rcases h with h | h
    · exact ihA h
    · exact ihB h
  | disj A B ihA ihB =>
    simp only [formulaConstsList]
    intro h
    rw [List.mem_append] at h
    rcases h with h | h
    · exact ihA h
    · exact ihB h
  | impl A B ihA ihB =>
    simp only [formulaConstsList]
    intro h
    rw [List.mem_append] at h
    rcases h with h | h
    · exact ihA h
    · exact ihB h
  | all _ A ih => simp only [formulaConstsList]; exact ih
  | ex _ A ih => simp only [formulaConstsList]; exact ih

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (required helper): `i ∈ foldl-append` iff `i` is in
    the initial accumulator or in one of the pushed lists. Used by
    `formulaFreeVarIndices_iff_formulaFVN` to peel the `List.ofFn`
    enumerations in the predN / func cases. -/
theorem mem_foldl_append_termVar {L : Language} (i : Nat)
    {β : Type} (f : β → Term L) :
    ∀ (l : List β) (acc : List Nat),
      i ∈ l.foldl (fun a j => a ++ termVarIndicesList (f j)) acc ↔
      i ∈ acc ∨ ∃ j ∈ l, i ∈ termVarIndicesList (f j) := by
-- BEGIN PROOF
  intro l
  induction l with
  | nil =>
    intro acc
    constructor
    · intro h; exact Or.inl h
    · intro h
      rcases h with h | ⟨_, hm, _⟩
      · exact h
      · cases hm
  | cons hd tl ih =>
    intro acc
    constructor
    · intro h
      rcases (ih _).mp h with hAcc | ⟨j, hJin, hJ⟩
      · rw [List.mem_append] at hAcc
        rcases hAcc with h1 | h1
        · exact Or.inl h1
        · exact Or.inr ⟨hd, List.mem_cons.mpr (Or.inl rfl), h1⟩
      · exact Or.inr ⟨j, List.mem_cons.mpr (Or.inr hJin), hJ⟩
    · intro h
      apply (ih _).mpr
      rcases h with hAcc | ⟨j, hJin, hJ⟩
      · left; exact List.mem_append_left _ hAcc
      · rcases List.mem_cons.mp hJin with hEq | hTl
        · left; rw [hEq] at hJ; exact List.mem_append_right _ hJ
        · right; exact ⟨j, hTl, hJ⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (required helper): `i ∈ formulaFreeVarIndices F`
    iff `i ∈ formulaFVN F`. Structural correspondence between the
    computable (List) and declarative (Set) FV enumerations. -/
theorem formulaFreeVarIndices_iff_formulaFVN {L : Language}
    (F : FormulaN L) (i : Nat) :
    i ∈ formulaFreeVarIndices F ↔ i ∈ formulaFVN F := by
  have termHelper : ∀ (t : Term L), i ∈ termVarIndicesList t ↔ i ∈ termFV t := by
-- BEGIN PROOF
    intro t
    induction t with
    | var j =>
      constructor <;> intro h
      · simp [termVarIndicesList] at h; exact h ▸ rfl
      · simp [termFV] at h; subst h; simp [termVarIndicesList]
    | const c =>
      constructor <;> intro h
      · simp [termVarIndicesList] at h
      · exact h.elim
    | func f ts ih =>
      simp only [termVarIndicesList]
      constructor
      · intro h
        rcases (mem_foldl_append_termVar i ts _ []).mp h with hAcc | ⟨j, _, hJ⟩
        · exact absurd hAcc (by simp)
        · exact ⟨j, (ih j).mp hJ⟩
      · intro h
        obtain ⟨j, hj⟩ := h
        apply (mem_foldl_append_termVar i ts _ []).mpr
        exact Or.inr ⟨j, List.mem_ofFn.mpr ⟨j, rfl⟩, (ih j).mpr hj⟩
  induction F with
  | predN P ts =>
    simp only [formulaFreeVarIndices]
    constructor
    · intro h
      rcases (mem_foldl_append_termVar i ts _ []).mp h with hAcc | ⟨j, _, hJ⟩
      · exact absurd hAcc (by simp)
      · exact ⟨j, (termHelper (ts j)).mp hJ⟩
    · intro h
      obtain ⟨j, hj⟩ := h
      apply (mem_foldl_append_termVar i ts _ []).mpr
      exact Or.inr ⟨j, List.mem_ofFn.mpr ⟨j, rfl⟩, (termHelper (ts j)).mpr hj⟩
  | eq_ _ t1 t2 =>
    simp only [formulaFreeVarIndices, formulaFVN, List.mem_append]
    exact or_congr (termHelper t1) (termHelper t2)
  | neg _ ih => simp only [formulaFreeVarIndices, formulaFVN]; exact ih
  | conj _ _ ihA ihB =>
    simp only [formulaFreeVarIndices, formulaFVN, List.mem_append]
    exact or_congr ihA ihB
  | disj _ _ ihA ihB =>
    simp only [formulaFreeVarIndices, formulaFVN, List.mem_append]
    exact or_congr ihA ihB
  | impl _ _ ihA ihB =>
    simp only [formulaFreeVarIndices, formulaFVN, List.mem_append]
    exact or_congr ihA ihB
  | all x A ih =>
    simp only [formulaFreeVarIndices, formulaFVN, List.mem_filter]
    constructor
    · intro ⟨hA, hNe⟩
      refine ⟨ih.mp hA, ?_⟩
      intro heq
      simp at hNe
      have : i = x := heq
      rw [this] at hNe
      simp at hNe
    · intro ⟨hA, hNotInSingleton⟩
      refine ⟨ih.mpr hA, ?_⟩
      simp
      intro hIsX
      apply hNotInSingleton
      rw [hIsX]; rfl
  | ex x A ih =>
    simp only [formulaFreeVarIndices, formulaFVN, List.mem_filter]
    constructor
    · intro ⟨hA, hNe⟩
      refine ⟨ih.mp hA, ?_⟩
      intro heq
      simp at hNe
      have : i = x := heq
      rw [this] at hNe
      simp at hNe
    · intro ⟨hA, hNotInSingleton⟩
      refine ⟨ih.mpr hA, ?_⟩
      simp
      intro hIsX
      apply hNotInSingleton
      rw [hIsX]; rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.4.9 (required helper): Every variable term
    produced by `initialTERM0 hNoEq seq` has its index either
    as a free variable of some formula of `seq`, or equal to
    `leastAbsentVar seq` (the fallback y₀ case). -/
theorem initialTerms_var_index {L : Language}
    (seq : Sequent L)
    (rec : Term L)
    (hRec : rec ∈ initialTerms seq)
    (i : Nat) (hi : rec = Term.var i) :
    (∃ F ∈ seq.antecedent ++ seq.succedent, i ∈ formulaFVN F) ∨
    i = leastAbsentVar seq := by
-- BEGIN PROOF
  classical
  unfold initialTerms at hRec
  simp only at hRec
  have hU := hRec
  split at hU
  · -- The fallback contains the computed least absent variable.
    right
    rw [List.mem_singleton] at hU
    rw [hU] at hi
    exact (Term.var.inj hi).symm
  · -- Non-fallback: u ∈ us = freeVarTerms ++ consts.
    left
    rw [List.mem_eraseDups, List.mem_append] at hU
    rcases hU with hFV | hConst
    · rw [List.mem_map] at hFV
      obtain ⟨j, hJmem, hJEq⟩ := hFV
      have hji : j = i := by
        rw [← hJEq] at hi
        exact Term.var.inj hi
      rw [List.mem_flatMap] at hJmem
      obtain ⟨F, hFmem, hFVj⟩ := hJmem
      refine ⟨F, hFmem, ?_⟩
      rw [← hji]
      exact (formulaFreeVarIndices_iff_formulaFVN F j).mp hFVj
    · exfalso
      rw [List.mem_flatMap] at hConst
      obtain ⟨F, _, hC⟩ := hConst
      exact not_var_mem_formulaConstsList F i (hi ▸ hC)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem formulaBoundVarIndices_iff_formulaBVN {L : Language} (F : FormulaN L) (i : Nat) :
    i ∈ formulaBoundVarIndices F ↔ i ∈ formulaBVN F := by
  induction F with
  | predN P ts | eq_ _ _ _ =>
      constructor
      · intro h; cases h
      · intro h; exact False.elim h
  | neg A ih => exact ih
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
      change i ∈ formulaBoundVarIndices A ++ formulaBoundVarIndices B ↔
        (i ∈ formulaBVN A ∨ i ∈ formulaBVN B)
      rw [List.mem_append]
      exact or_congr ihA ihB
  | all x A ih | ex x A ih =>
      simp only [formulaBoundVarIndices, List.mem_cons]
      change (i = x ∨ i ∈ formulaBoundVarIndices A) ↔ (i ∈ formulaBVN A ∨ i = x)
      rw [ih]
      exact or_comm

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem sequentVarIndices_mem {L : Language} {seq : Sequent L} {F : FormulaN L}
    (hF : F ∈ seq.antecedent ++ seq.succedent) {i : Nat}
    (hi : i ∈ formulaFVN F ∨ i ∈ formulaBVN F) : i ∈ sequentVarIndices seq := by
  apply List.mem_flatMap.mpr
  refine ⟨F, hF, List.mem_append.mpr ?_⟩
  rcases hi with hi | hi
  · exact Or.inl ((formulaFreeVarIndices_iff_formulaFVN F i).mpr hi)
  · exact Or.inr ((formulaBoundVarIndices_iff_formulaBVN F i).mpr hi)

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Definition 5.4.9 (companion): Every admissible initialization
    satisfies the global search invariant. -/
theorem init_preserves_Inv {L : Language} {seq : Sequent L} (initial : Init seq) :
    Inv seq (sequentVarBound seq) (init initial) := by
  rcases initial.admissible with ⟨hTerms, hVars, hDisj, _⟩
  have hAllowed : ∀ t ∈ initial.term0, ∀ i, t = Term.var i →
      (∃ F ∈ seq.antecedent ++ seq.succedent, i ∈ formulaFVN F) ∨
      (∀ F ∈ seq.antecedent ++ seq.succedent, i ∉ formulaBVN F) := by
    intro t ht i hi
    rcases initialTerms_var_index seq t ((hTerms t).mp ht) i hi with hFV | hEq
    · exact Or.inl hFV
    · right; subst i
      intro F hF hBV
      exact (leastAbsentVar_spec seq).1 (sequentVarIndices_mem hF (Or.inr hBV))
  have hBefore : ∀ t ∈ initial.term0, ∀ i, t = Term.var i →
      BeforeCursor initial.avail0 0 i := by
    intro t ht i hi n _ heq
    exact hDisj n t (hi ▸ heq) ht
  refine ⟨?_, ?_, ?_, hAllowed, hAllowed, hBefore, hBefore⟩
  · intro F hF
    exact ⟨fun i hi => sequentVarIndices_lt_bound seq (sequentVarIndices_mem hF (Or.inl hi)),
      fun i hi => sequentVarIndices_lt_bound seq (sequentVarIndices_mem hF (Or.inr hi))⟩
  · intro n; obtain ⟨i, hi, _⟩ := hVars n; exact ⟨i, hi⟩
  · intro n _ i hi F hF hBV
    obtain ⟨j, hj, hjFresh⟩ := hVars n
    have hji : j = i := Term.var.inj (Option.some.inj (hj.symm.trans hi))
    subst j
    exact hjFresh (sequentVarIndices_mem hF (Or.inr hBV))

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- The availability stream of an admissible initialization is fresh
    for the input sequent's free variables. -/
theorem init_available_fresh {L : Language} {seq : Sequent L} (initial : Init seq)
    (F : FormulaN L) (hF : F ∈ seq.antecedent ++ seq.succedent)
    (i : Nat) (hi : i ∈ formulaFVN F) (n : Nat) :
    initial.avail0.entries n ≠ some (.var i) := by
  obtain ⟨j, hj, hjFresh⟩ := initial.admissible.2.1 n
  intro heq
  have hji : j = i := Term.var.inj (Option.some.inj (hj.symm.trans heq))
  subst j
  apply hjFresh
  exact List.mem_flatMap.mpr ⟨F, hF, List.mem_append.mpr
    (Or.inl ((formulaFreeVarIndices_iff_formulaFVN F i).mpr hi))⟩

end SearchState
end LCS.FirstOrder.Gentzen.Search.NoFunction
end

section
namespace LCS.FirstOrder.Gentzen.Search.NoFunction
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka



-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The canonical initial list and a supply above the input are admissible. -/
theorem defaultInit_admissible {L : Language} (seq : Sequent L) :
    admissibleInitialization seq (initialTerms seq)
      (TermStream.variablesFrom L (sequentVarBound seq + 1)) := by
  classical
  have hBound : ∀ i, Term.var (L := L) i ∈ initialTerms seq → i ≤ sequentVarBound seq := by
    intro i hi
    rcases SearchState.initialTerms_var_index seq (.var i) hi i rfl with hFV | hEq
    · obtain ⟨F, hF, hiF⟩ := hFV
      exact Nat.le_of_lt (sequentVarIndices_lt_bound seq
        (SearchState.sequentVarIndices_mem hF (Or.inl hiF)))
    · exact hEq ▸ (leastAbsentVar_spec seq).2.1
  refine ⟨fun _ => Iff.rfl, ?_, ?_, ?_⟩
  · intro n
    refine ⟨sequentVarBound seq + 1 + n, rfl, ?_⟩
    intro hMem
    have := sequentVarIndices_lt_bound seq hMem
    omega
  · intro n t ht hMem
    have ht' : Term.var (L := L) (sequentVarBound seq + 1 + n) = t := Option.some.inj ht
    have := hBound _ (ht' ▸ hMem)
    omega
  · intro hFree hConsts
    simp [initialTerms, hFree, hConsts]

/-- Definition 5.4.9 (companion): Computed initialization with canonical
    term order and an availability stream disjoint from the input and y₀. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def Init.default {L : Language} (seq : Sequent L) : Init seq :=
  let freshStart := sequentVarBound seq + 1
  { term0 := initialTerms seq
    avail0 := TermStream.variablesFrom L freshStart
    admissible := defaultInit_admissible seq }



-- ===================================================================
-- Side-condition discharge lemmas (isFreeForN, freshness)
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (companion, discharge): `isFreeForN (Term.var i) x B`
    holds whenever `i ∉ formulaBVN B`, i.e. `i` is not a bound variable
    anywhere in B. Structural induction on B unfolds both `isFreeForN`
    and `formulaBVN` in parallel: at binders, either `x` matches the
    binder (trivial case of isFreeForN) or we must show `i ≠ y` and
    recurse. Since `i ∉ BV(∀y A) = BV(A) ∪ {y}` gives both `i ∉ BV(A)`
    (IH) and `i ≠ y` (the `{y}` clause), the proof goes through. -/
theorem isFreeForN_var_of_notBV {L : Language} (i x : Nat) (B : FormulaN L)
    (h : i ∉ formulaBVN B) : isFreeForN (Term.var i) x B := by
-- BEGIN PROOF
  induction B with
  | predN _ _ => exact trivial
  | eq_ _ _ _ => exact trivial
  | neg A ihA =>
    have h' : i ∉ formulaBVN A := h
    exact ihA h'
  | conj A B ihA ihB =>
    have hA : i ∉ formulaBVN A := fun hx => h (Or.inl hx)
    have hB : i ∉ formulaBVN B := fun hx => h (Or.inr hx)
    exact ⟨ihA hA, ihB hB⟩
  | disj A B ihA ihB =>
    have hA : i ∉ formulaBVN A := fun hx => h (Or.inl hx)
    have hB : i ∉ formulaBVN B := fun hx => h (Or.inr hx)
    exact ⟨ihA hA, ihB hB⟩
  | impl A B ihA ihB =>
    have hA : i ∉ formulaBVN A := fun hx => h (Or.inl hx)
    have hB : i ∉ formulaBVN B := fun hx => h (Or.inr hx)
    exact ⟨ihA hA, ihB hB⟩
  | all y A ihA =>
    -- formulaBVN (all y A) = formulaBVN A ∪ {y}
    -- h : i ∉ formulaBVN A ∪ {y}
    -- Goal: x = y ∨ (¬ (y ∈ termFV (Term.var i)) ∧ isFreeForN (Term.var i) x A)
    by_cases hxy : x = y
    · exact Or.inl hxy
    · refine Or.inr ⟨?_, ihA (fun hBVA => h (Or.inl hBVA))⟩
      -- termFV (Term.var i) = {i}, so ¬ (y ∈ {i}) ↔ y ≠ i, which is i ≠ y
      show y ∉ termFV (Term.var i)
      intro hy
      -- termFV (Term.var i) = Set.singleton i; hy : y ∈ Set.singleton i
      have hyi : y = i := hy
      have hiyIn : i ∈ formulaBVN (FormulaN.all y A) := by
        show i ∈ formulaBVN A ∪ Set.singleton y
        exact Or.inr (by show i ∈ Set.singleton y; rw [hyi]; rfl)
      exact h hiyIn
  | ex y A ihA =>
    by_cases hxy : x = y
    · exact Or.inl hxy
    · refine Or.inr ⟨?_, ihA (fun hBVA => h (Or.inl hBVA))⟩
      show y ∉ termFV (Term.var i)
      intro hy
      have hyi : y = i := hy
      have hiyIn : i ∈ formulaBVN (FormulaN.ex y A) := by
        show i ∈ formulaBVN A ∪ Set.singleton y
        exact Or.inr (by show i ∈ Set.singleton y; rw [hyi]; rfl)
      exact h hiyIn

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (companion, discharge): `isFreeForN (Term.const c) x B`
    holds unconditionally, because `termFV (Term.const c) = ∅` means
    no variable of B can be captured by substituting `c`. -/
theorem isFreeForN_const {L : Language} (c : L.constSymbols) (x : Nat)
    (B : FormulaN L) : isFreeForN (Term.const c) x B := by
-- BEGIN PROOF
  induction B with
  | predN _ _ => exact trivial
  | eq_ _ _ _ => exact trivial
  | neg _ ih => exact ih
  | conj _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | disj _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | impl _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | all y _ ih =>
    by_cases hxy : x = y
    · exact Or.inl hxy
    · refine Or.inr ⟨?_, ih⟩
      show y ∉ termFV (Term.const (L := L) c)
      intro hy
      exact hy
  | ex y _ ih =>
    by_cases hxy : x = y
    · exact Or.inl hxy
    · refine Or.inr ⟨?_, ih⟩
      show y ∉ termFV (Term.const (L := L) c)
      intro hy
      exact hy

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (companion, discharge): An index `i ∈ FV(seq)`
    (i.e. appears free in some formula of `seq`), under the §5.4.7
    standing assumption `crossNoFreeBound seq` ("the set of all
    variables occurring free in some formula in the sequent is
    disjoint from the set of all variables occurring bound in some
    formula in the sequent"), does NOT occur bound in any formula of
    `seq`.

    Bridge between "FV-class TERM₀ entries" and "isFreeForN discharge":
    when a TERM₀ entry `Term.var i` has `i ∈ FV(seq)`,
    `crossNoFreeBound` gives `i ∉ BV(G)` for every `G ∈ seq`, so via
    the subformula-bound invariant `BV(B) ⊆ BV(G)` for any subformula
    `B` of `G`, `isFreeForN_var_of_notBV` yields
    `isFreeForN (Term.var i) x B`. -/
theorem notBV_of_FV_of_crossNFB {L : Language} {seq : Sequent L}
    (hCNFB : crossNoFreeBound seq) {i : Nat}
    (hFV : ∃ F ∈ seq.antecedent ++ seq.succedent, i ∈ formulaFVN F)
    (G : FormulaN L) (hG : G ∈ seq.antecedent ++ seq.succedent) :
    i ∉ formulaBVN G :=
-- BEGIN PROOF
  hCNFB i hFV G hG



-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (companion, discharge): Combined "allowed index"
    discharge — if `i` is `VarAllowed` (free in seq OR ≥ bound), then
    `i` is not bound in any formula of `seq` under the §5.4.7 standing
    assumption `crossNoFreeBound seq` and the invariant
    `NoVarAbove seq bound`. -/
theorem notBV_of_allowed {L : Language} {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq) (hNVA : NoVarAbove seq bound) {i : Nat}
    (hAllowed :
      (∃ F ∈ seq.antecedent ++ seq.succedent, i ∈ formulaFVN F) ∨
      (∀ F ∈ seq.antecedent ++ seq.succedent, i ∉ formulaBVN F))
    (G : FormulaN L) (hG : G ∈ seq.antecedent ++ seq.succedent) :
    i ∉ formulaBVN G := by
-- BEGIN PROOF
  cases hAllowed with
  | inl hFV => exact notBV_of_FV_of_crossNFB hCNFB hFV G hG
  | inr hFresh => exact hFresh G hG

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.4.9 (companion, discharge): Every term `u ∈ tTERM0 st`
    is free for substitution for any variable `x` in any formula `G`
    occurring in the original sequent `seq`, provided:
    - `Inv seq bound st` (the state invariant),
    - `crossNoFreeBound seq` (the §5.4.7 standing assumption),
    - `hNoFunc : L.funSymbols → False` (the §5.4.7 no-function-symbols
      standing assumption), and
    - `G ∈ seq`.

    This is the main discharge lemma consumed by the quantifier-aware
    `growLeft` / `growRight`: it produces the `hfree : isFreeForN u x G`
    witness required by `GentzenStep1Ext.allLeft` / `.exRight` when
    `G = ∀x B` (or `∃x B`) is the principal formula of the rule.

    The `hNoFunc` hypothesis eliminates the `.func` case of `Term L` —
    §5.4.7 languages have no function symbols, so `TERM₀` never
    contains `Term.func` values. -/
theorem SearchState.term_isFreeForN_of_Inv {L : Language} {supply : TermStream L}
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat} {st : SearchState L supply}
    (h : SearchState.Inv seq bound st)
    (hCNFB : crossNoFreeBound seq)
    {u : Term L} (hu : u ∈ st.tTERM0)
    (x : Nat) (G : FormulaN L)
    (hG : G ∈ seq.antecedent ++ seq.succedent) :
    isFreeForN u x G := by
-- BEGIN PROOF
  unfold tTERM0 at hu
  match u with
  | .var i =>
    have hAllowed := h.terms_allowed _ hu i rfl
    have hNotBV : i ∉ formulaBVN G :=
      notBV_of_allowed hCNFB h.bound_above_seq hAllowed G hG
    exact isFreeForN_var_of_notBV i x G hNotBV
  | .const c => exact isFreeForN_const c x G
  | .func f _ => exact (hNoFunc f).elim

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (required helper): If `i ∉ formulaBVN (∀x A)`,
    then `i ∉ formulaBVN A`. This is the "descend into binder body"
    direction of the subformula-bound invariant: binding `x` can only
    ADD `x` to BV, so the inside's BV is a subset of the outside's BV.
    Used by `growLeftAll` (and mirror cases) to lift discharge from
    `∀x A ∈ seq` to `A` (the body, where substitution actually
    happens). -/
theorem notBV_body_of_all {L : Language} {i x : Nat} {A : FormulaN L}
    (h : i ∉ formulaBVN (FormulaN.all x A)) : i ∉ formulaBVN A := by
-- BEGIN PROOF
  intro hBV
  exact h (Or.inl hBV)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (required helper): Mirror of `notBV_body_of_all`
    for the existential binder. -/
theorem notBV_body_of_ex {L : Language} {i x : Nat} {A : FormulaN L}
    (h : i ∉ formulaBVN (FormulaN.ex x A)) : i ∉ formulaBVN A := by
-- BEGIN PROOF
  intro hBV
  exact h (Or.inl hBV)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.4.9 (companion, discharge): Specialization of
    `SearchState.term_isFreeForN_of_Inv` to the body of a universal
    formula: if `∀x A ∈ seq`, then every `u ∈ tTERM0 st` satisfies
    `isFreeForN u y A` for any `y`. The discharge proceeds in two
    steps: (1) get `u` free-for-substitution in the WHOLE formula
    `∀x A` from `term_isFreeForN_of_Inv`; (2) since that trivially
    holds by the binder-match clause, we need a different path —
    directly lift `i ∉ BV(∀x A)` to `i ∉ BV(A)` via `notBV_body_of_all`.

    This is what `growLeftAll` consumes to produce the `hfree` witness
    for `GentzenStep1Ext.allLeft`. -/
theorem SearchState.term_isFreeForN_body_all_of_Inv {L : Language} {supply : TermStream L}
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat} {st : SearchState L supply}
    (h : SearchState.Inv seq bound st)
    (hCNFB : crossNoFreeBound seq)
    {u : Term L} (hu : u ∈ st.tTERM0)
    (x : Nat) (A : FormulaN L)
    (hInSeq : FormulaN.all x A ∈ seq.antecedent ++ seq.succedent) :
    ∀ y, isFreeForN u y A := by
-- BEGIN PROOF
  intro y
  unfold tTERM0 at hu
  match u with
  | .var i =>
    have hAllowed := h.terms_allowed _ hu i rfl
    have hNotBV_all : i ∉ formulaBVN (FormulaN.all x A) :=
      notBV_of_allowed hCNFB h.bound_above_seq hAllowed _ hInSeq
    have hNotBV_A : i ∉ formulaBVN A := notBV_body_of_all hNotBV_all
    exact isFreeForN_var_of_notBV i y A hNotBV_A
  | .const c => exact isFreeForN_const c y A
  | .func f _ => exact (hNoFunc f).elim

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.4.9 (companion, discharge): Mirror of
    `term_isFreeForN_body_all_of_Inv` for the existential body. -/
theorem SearchState.term_isFreeForN_body_ex_of_Inv {L : Language} {supply : TermStream L}
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat} {st : SearchState L supply}
    (h : SearchState.Inv seq bound st)
    (hCNFB : crossNoFreeBound seq)
    {u : Term L} (hu : u ∈ st.tTERM0)
    (x : Nat) (A : FormulaN L)
    (hInSeq : FormulaN.ex x A ∈ seq.antecedent ++ seq.succedent) :
    ∀ y, isFreeForN u y A := by
-- BEGIN PROOF
  intro y
  unfold tTERM0 at hu
  match u with
  | .var i =>
    have hAllowed := h.terms_allowed _ hu i rfl
    have hNotBV_ex : i ∉ formulaBVN (FormulaN.ex x A) :=
      notBV_of_allowed hCNFB h.bound_above_seq hAllowed _ hInSeq
    have hNotBV_A : i ∉ formulaBVN A := notBV_body_of_ex hNotBV_ex
    exact isFreeForN_var_of_notBV i y A hNotBV_A
  | .const c => exact isFreeForN_const c y A
  | .func f _ => exact (hNoFunc f).elim

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Growth
/-- Definition 5.4.9 (required helper): If a formula `A` occurs in a
    list of antecedent/succedent formulae, we can split the list as
    `Γ ++ [A] ++ Δ`. Canonical choice of splitting: the leftmost
    occurrence. Used to construct `GentzenStep1Ext` / `GentzenStep2Ext`
    rule witnesses (whose constructors expect explicit `Γ Δ Λ` lists). -/
theorem list_split_mem {α : Type} (l : List α) (a : α) (h : a ∈ l) :
    ∃ pre post : List α, l = pre ++ [a] ++ post := by
-- BEGIN PROOF
  induction l with
  | nil => cases h
  | cons x xs ih =>
    by_cases hxa : x = a
    · exact ⟨[], xs, by simp [hxa]⟩
    · cases h with
      | head _ => exact absurd rfl hxa
      | tail _ h' =>
        obtain ⟨pre, post, heq⟩ := ih h'
        exact ⟨x :: pre, post, by simp [heq]⟩

end LCS.FirstOrder.Gentzen.Search.NoFunction
end

