import LCS.FirstOrder.Completeness.InfiniteSearch
import LCS.FirstOrder.Gentzen.Search.NoFunction
import LCS.FirstOrder.Completeness.Search.Part1
import Attach
import LCS.FirstOrder.Completeness.Search.Part2.ProofsStamp

section
namespace LCS.FirstOrder.Completeness.Search
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen

/-- Definition 5.5.1: Start a round by copying TERM₀ and its branch records
to the working TERM₁ and FORM₁ lists. -/
@[blueprint "chap5__definition_5_5_1"]
def startRound {L : Language} {root : Sequent L} (st : SearchState L root) :
    SearchState L root :=
  { st with TERM1 := st.TERM0, tree := st.tree.startRound }

/-- Definition 5.5.1: One round expands the original leaves in lexicographic
address order, then commits TERM₁, advances L/R once, and transfers active
AVAIL heads. A state whose leaves are all finished is left unchanged. -/
@[blueprint "chap5__definition_5_5_1"]
noncomputable def searchRound {L : Language} (hL : L.withoutEquality)
    {root : Sequent L} (st : SearchState L root) : SearchState L root := by
  classical
  exact if allFinished hL st then st else
    let expanded := st.tree.leafAddresses.foldl (fun acc path => expand hL path acc) (startRound st)
    roundEndUpdate (advanceInput expanded)

/-- Definition 5.5.1: The round-k approximant of the search procedure for
an input built from the x-variables and satisfying the free/bound convention,
with fixed admissible TERMS and AVAIL enumerations. The returned state contains
the tree with all rule and intake edges and its branch-local records. -/
@[blueprint "chap5__definition_5_5_1" (main := true)]
noncomputable def search51 {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (k : Nat) :
    SearchState L (Sequent.mk (q.antecedent 0).toList (q.succedent 0).toList) :=
  match k with
  | 0 => SearchState.init hL q hq hFB enum.terms enum.avail
  | k + 1 => searchRound hL (search51 hL q hq hFB enum k)

/-- Definition 5.5.1: Search halts for its fixed admissible enumerations
when some finite-round approximant has every leaf finished. -/
@[blueprint "chap5__definition_5_5_1"]
def halts51 {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) : Prop :=
  ∃ k, allFinished hL (search51 hL q hq hFB enum k)

/-- Definition 5.5.1: The terminal messages, "T is a proof of Γ₀ → Δ₀"
and "Γ₀ → Δ₀ is falsifiable". A deduction tree all of whose leaves are
axioms is a proof (Definition 5.4.2). -/
@[blueprint "chap5__definition_5_5_1"]
inductive SearchOutput {L : Language} (root : Sequent L) : Type where
  | proof (T : InfGDeductionTreeExt root)
      (hClosed : ∀ leaf ∈ T.leaves, isAxiom leaf)
  | falsifiable

/-- Definition 5.5.1: While not all leaves are finished, there is no output.
After the loop, if all leaves are closed, write "T is a proof of Γ₀ → Δ₀";
otherwise, write "Γ₀ → Δ₀ is falsifiable". -/
@[blueprint "chap5__definition_5_5_1"]
noncomputable def output51 {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (k : Nat) :
    Option (SearchOutput (Sequent.mk (q.antecedent 0).toList (q.succedent 0).toList)) := by
  classical
  let st := search51 hL q hq hFB enum k
  exact if allFinished hL st then
    if hClosed : ∀ leaf ∈ st.tree.forget.leaves, isAxiom leaf then
      some (.proof st.tree.forget hClosed)
    else some .falsifiable
  else none

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- Definition 5.5.1: Tree extension preserves every existing label and
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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.5.1: Every search-stage tree extends itself. -/
theorem InfGDeductionTreeExt.Extension.refl {L : Language} {s : Sequent L}
    (t : InfGDeductionTreeExt s) : Extension t t := by
  induction t with
  | leaf => exact .leaf _
  | onePremise r _ ih => exact .one r ih
  | twoPremise r _ _ ih₁ ih₂ => exact .two r ih₁ ih₂
  | extend a b _ ih => exact .intro a b ih

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.5.1: Successive leaf extensions compose. -/
theorem InfGDeductionTreeExt.Extension.trans {L : Language} {s t u : Sequent L}
    {a : InfGDeductionTreeExt s} {b : InfGDeductionTreeExt t} {c : InfGDeductionTreeExt u}
    (h₁ : Extension a b) (h₂ : Extension b c) : Extension a c := by
  induction h₁ generalizing u with
  | leaf => cases h₂ <;> exact .leaf _
  | one r h ih => cases h₂ with | one _ h₂ => exact .one r (ih h₂)
  | two r h₁ h₂ ih₁ ih₂ =>
    cases h₂ with | two _ ha hb => exact .two r (ih₁ ha) (ih₂ hb)
  | intro a b h ih => cases h₂ with | intro _ _ h₂ => exact .intro a b (ih h₂)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.5.1: Starting a round only changes formula records. -/
theorem SearchTree.forget_startRound {L : Language} {s : Sequent L} (t : SearchTree s) :
    t.startRound.forget = t.forget := by
  induction t with
  | leaf => rfl
  | onePremise r t ih => simp [SearchTree.startRound, SearchTree.forget, ih]
  | twoPremise r l t ihl iht => simp [SearchTree.startRound, SearchTree.forget, ihl, iht]
  | extend a b t ih => simp [SearchTree.startRound, SearchTree.forget, ih]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.5.1: Committing a round only changes formula records. -/
theorem SearchTree.forget_commitRound {L : Language} {s : Sequent L}
    (t : SearchTree s) (n : Nat) : (t.commitRound n).forget = t.forget := by
  induction t with
  | leaf => rfl
  | onePremise r t ih => simp [SearchTree.commitRound, SearchTree.forget, ih]
  | twoPremise r l t ihl iht => simp [SearchTree.commitRound, SearchTree.forget, ihl, iht]
  | extend a b t ih => simp [SearchTree.commitRound, SearchTree.forget, ih]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.5.1: Expanding a designated leaf preserves all existing
edges, including input-introduction edges. -/
theorem expand_extends {L : Language} (hL : L.withoutEquality) {root : Sequent L}
    (path : List Nat) (st : SearchState L root) :
    InfGDeductionTreeExt.Extension st.tree.forget (expand hL path st).tree.forget := by
  induction path generalizing root with
  | nil =>
    cases ht : st.tree with
    | leaf s records =>
      simp only [expand, ht, SearchTree.forget]
      exact .leaf _
    | onePremise => simpa only [Nat.zero_add, expand, ht] using InfGDeductionTreeExt.Extension.refl st.tree.forget
    | twoPremise => simpa only [Nat.zero_add, expand, ht] using InfGDeductionTreeExt.Extension.refl st.tree.forget
    | extend => simpa only [Nat.zero_add, expand, ht] using InfGDeductionTreeExt.Extension.refl st.tree.forget
  | cons i path ih =>
    cases i with
    | zero =>
      cases ht : st.tree with
      | leaf => simpa only [Nat.zero_add, expand, ht] using InfGDeductionTreeExt.Extension.refl st.tree.forget
      | onePremise rule sub =>
        simpa only [Nat.zero_add, expand, ht, SearchState.withTree, SearchTree.forget] using
          InfGDeductionTreeExt.Extension.one rule (ih (st.withTree sub))
      | twoPremise rule left right =>
        simpa only [Nat.zero_add, expand, ht, SearchState.withTree, SearchTree.forget] using
          InfGDeductionTreeExt.Extension.two rule (ih (st.withTree left))
            (InfGDeductionTreeExt.Extension.refl right.forget)
      | extend a b sub =>
        simpa only [Nat.zero_add, expand, ht, SearchState.withTree, SearchTree.forget] using
          InfGDeductionTreeExt.Extension.intro a b (ih (st.withTree sub))
    | succ i =>
      cases i with
      | zero =>
        cases ht : st.tree with
        | twoPremise rule left right =>
          simpa only [Nat.zero_add, expand, ht, SearchState.withTree, SearchTree.forget] using
            InfGDeductionTreeExt.Extension.two rule (InfGDeductionTreeExt.Extension.refl left.forget)
              (ih (st.withTree right))
        | leaf => simpa only [Nat.zero_add, expand, ht] using InfGDeductionTreeExt.Extension.refl st.tree.forget
        | onePremise => simpa only [Nat.zero_add, expand, ht] using InfGDeductionTreeExt.Extension.refl st.tree.forget
        | extend => simpa only [Nat.zero_add, expand, ht] using InfGDeductionTreeExt.Extension.refl st.tree.forget
      | succ i => simpa only [expand] using InfGDeductionTreeExt.Extension.refl st.tree.forget

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.5.1: A sequence of designated-leaf expansions extends the
initial tree, with each expansion using the updated global state. -/
theorem expandFold_extends {L : Language} (hL : L.withoutEquality) {root : Sequent L}
    (paths : List (List Nat)) (st : SearchState L root) :
    InfGDeductionTreeExt.Extension st.tree.forget
      (paths.foldl (fun acc path => expand hL path acc) st).tree.forget := by
  induction paths generalizing st with
  | nil => exact .refl _
  | cons path paths ih => exact (expand_extends hL path st).trans (ih (expand hL path st))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.5.1: Each round preserves every previous tree node and edge. -/
theorem searchRound_extends {L : Language} (hL : L.withoutEquality) {root : Sequent L}
    (st : SearchState L root) :
    InfGDeductionTreeExt.Extension st.tree.forget (searchRound hL st).tree.forget := by
  classical
  by_cases h : allFinished hL st
  · simp only [searchRound, ite_eq_left h]
    exact .refl _
  · simpa only [searchRound, ite_eq_right h, roundEndUpdate, advanceInput,
      SearchTree.forget_commitRound, startRound, SearchTree.forget_startRound] using
      expandFold_extends hL st.tree.leafAddresses (startRound st)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.5.1: The finite round approximants are monotone: round k+1
extends round k, retaining all G-rule and input-introduction edges. -/
theorem search51_monotone {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (k : Nat) :
    InfGDeductionTreeExt.Extension (search51 hL q hq hFB enum k).tree.forget
      (search51 hL q hq hFB enum (k + 1)).tree.forget :=
  searchRound_extends hL _

/-- Definition 5.5.1: Read a node label by its tree address, with child 0
for unary and intake edges and children 0 and 1 for binary edges. -/
@[blueprint "chap5__definition_5_5_1"]
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

/-- Definition 5.5.1: The limit tree consists exactly of the labeled nodes
appearing in a finite round approximant of the fixed run. -/
@[blueprint "chap5__definition_5_5_1"]
def searchLimit51 {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (address : List Nat) (label : Sequent L) : Prop :=
  ∃ k, (search51 hL q hq hFB enum k).tree.forget.labelAt address = some label

/-- Definition 5.5.1: An infinite path is a sequence of child choices
whose every finite prefix is an address in the actual limit tree. -/
@[blueprint "chap5__definition_5_5_1", blueprint "chap5__theorem_5_5_1"]
def InfinitePath51 {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (path : Nat → Nat) : Prop :=
  ∀ n, ∃ label, searchLimit51 hL q hq hFB enum ((List.range n).map path) label

/-- Definition 5.5.1: A term is eventually activated when it belongs to
TERM₀ in some finite round of the fixed run. TERM₀ is global; branch records
determine which principal formulae have used its terms on each branch. -/
@[blueprint "chap5__definition_5_5_1", blueprint "chap5__theorem_5_5_1"]
def eventuallyActivated51 {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (t : Term L) : Prop :=
  ∃ k, t ∈ (search51 hL q hq hFB enum k).TERM0

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.5.1: Extension preserves the label at every old address. -/
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

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.5.1: A node remains at the same address in every later round. -/
theorem search51_labelAt_mono {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (k n : Nat) (p : List Nat) (label : Sequent L)
    (hp : (search51 hL q hq hFB enum k).tree.forget.labelAt p = some label) :
    (search51 hL q hq hFB enum (k + n)).tree.forget.labelAt p = some label := by
  induction n with
  | zero => exact hp
  | succ n ih => exact (search51_monotone hL q hq hFB enum (k + n)).labelAt_preserves p label ih



-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.5.1: Once search finishes, every later round has the
same state, so a finite open stopping path need not drain its AVAIL lists. -/
theorem search51_stable_of_finished {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (k : Nat)
    (h : allFinished hL (search51 hL q hq hFB enum k)) (n : Nat) :
    search51 hL q hq hFB enum (k + n) = search51 hL q hq hFB enum k := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    change searchRound hL (search51 hL q hq hFB enum (k + n)) = _
    rw [ih]
    simp [searchRound, h]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.5.1: Maximum edge depth of a finite search approximant. -/
def InfGDeductionTreeExt.height {L : Language} :
    {s : Sequent L} → InfGDeductionTreeExt s → Nat
  | _, .leaf _ => 0
  | _, .onePremise _ t => t.height + 1
  | _, .twoPremise _ l r => max l.height r.height + 1
  | _, .extend _ _ t => t.height + 1

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.5.1: Every address in a finite tree is bounded by its height. -/
theorem InfGDeductionTreeExt.labelAt_length_le_height {L : Language} {s label : Sequent L}
    (t : InfGDeductionTreeExt s) (p : List Nat) (h : t.labelAt p = some label) :
    p.length ≤ t.height := by
  induction t generalizing p with
  | leaf => cases p <;> simp_all [labelAt, height]
  | onePremise rule t ih =>
    cases p with
    | nil => simp
    | cons i p =>
      cases i with
      | zero => exact Nat.succ_le_succ (ih p h)
      | succ => simp [labelAt] at h
  | twoPremise rule l r ih₁ ih₂ =>
    cases p with
    | nil => simp
    | cons i p =>
      cases i with
      | zero =>
        have := ih₁ p h
        simp only [List.length_cons, height]
        omega
      | succ i =>
        cases i with
        | zero =>
          have := ih₂ p h
          simp only [List.length_cons, height]
          omega
        | succ => simp [labelAt] at h
  | extend a b t ih =>
    cases p with
    | nil => simp
    | cons i p =>
      cases i with
      | zero => exact Nat.succ_le_succ (ih p h)
      | succ => simp [labelAt] at h

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.5.1: An infinite path in the actual limit tree prevents
search from reaching a state in which all leaves are finished. -/
theorem infinitePath51_not_halts {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (path : Nat → Nat)
    (hp : InfinitePath51 hL q hq hFB enum path) : ¬ halts51 hL q hq hFB enum := by
  rintro ⟨k, hk⟩
  have hlimit (p : List Nat) (label : Sequent L)
      (hl : searchLimit51 hL q hq hFB enum p label) :
      (search51 hL q hq hFB enum k).tree.forget.labelAt p = some label := by
    obtain ⟨j, hj⟩ := hl
    rcases Nat.le_total j k with hjk | hkj
    · have h := search51_labelAt_mono hL q hq hFB enum j (k - j) p label hj
      simpa only [Nat.add_sub_of_le hjk] using h
    · have h := search51_stable_of_finished hL q hq hFB enum k hk (j - k)
      rw [Nat.add_sub_of_le hkj] at h
      simpa only [h] using hj
  obtain ⟨label, hl⟩ := hp ((search51 hL q hq hFB enum k).tree.forget.height + 1)
  have hbound := InfGDeductionTreeExt.labelAt_length_le_height _ _ (hlimit _ label hl)
  simp only [List.length_map, List.length_range] at hbound
  omega



/-- Definition 5.5.1: Along every infinite path of the limit search tree,
once any entry of an initially fixed AVAILᵢ stream is activated, every entry
of that stream is eventually activated. AVAIL₀ is initially tail(TERMS).
The path scope is infinite paths: the alternative encompassing every finite
non-closing path does not ensure continued transfer, since a finite open
search can halt with availability entries still unconsumed. -/
theorem eventualActivation51 {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (path : Nat → Nat)
    (hp : InfinitePath51 hL q hq hFB enum path) (i : Nat)
    (hactivated : ∃ n t,
      ((search51 hL q hq hFB enum 0).avail i).entries n = some t ∧
      eventuallyActivated51 hL q hq hFB enum t) :
    ∀ n t, ((search51 hL q hq hFB enum 0).avail i).entries n = some t →
      eventuallyActivated51 hL q hq hFB enum t := by
  have hrun : ¬ halts51 hL q hq hFB enum :=
    infinitePath51_not_halts hL q hq hFB enum path hp
  -- REPAIR(T105): proof pending
  sorry

end LCS.FirstOrder.Completeness.Search
end

section
namespace LCS.FirstOrder.Completeness.Search
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae

/-- Definition 5.5.1: The allowed initial variables determined by the
constant symbols and free variables, with y₀ when both sets are empty. -/
@[blueprint "chap5__definition_5_5_1"]
def initialVarOfSymbols {L : Language} (cs : Set L.constSymbols) (fv : Set Nat)
    (x : Nat) : Prop :=
  fv x ∨ (¬ ((∃ x, fv x) ∨ ∃ c, cs c) ∧ x = 1)

/-- Definition 5.5.1: TERMS membership depends only on the function and
constant symbols of L′ and the set of initial free variables. -/
@[blueprint "chap5__definition_5_5_1"]
def termsTermOfSymbols {L : Language} (fs : Set L.funSymbols)
    (cs : Set L.constSymbols) (fv : Set Nat) (t : Term L) : Prop :=
  (termFunSyms t ⊆ fs ∧ termConstSyms t ⊆ cs) ∧
    ∀ x, x ∈ termFV t → initialVarOfSymbols cs fv x

/-- Definition 5.5.1: AVAILᵢ membership depends only on the symbols of L′,
the initial free variables, and y₁ through yᵢ, and requires occurrence of yᵢ. -/
@[blueprint "chap5__definition_5_5_1"]
def availTermOfSymbols {L : Language} (fs : Set L.funSymbols)
    (cs : Set L.constSymbols) (fv : Set Nat) (i : Nat) (t : Term L) : Prop :=
  (termFunSyms t ⊆ fs ∧ termConstSyms t ⊆ cs) ∧
    (∀ x, x ∈ termFV t →
      initialVarOfSymbols cs fv x ∨ ∃ j, 1 ≤ j ∧ j ≤ i ∧ x = 2 * j + 1) ∧
    2 * i + 1 ∈ termFV t

/-- Definition 5.5.1: Admissibility of a TERMS stream over fixed symbol
and variable sets. The stream supplies no holes and injectivity; this predicate
specifies its exact range and its first entry in the y₀ fallback case. -/
@[blueprint "chap5__definition_5_5_1"]
def TermsAdmissibleOfSymbols {L : Language} (fs : Set L.funSymbols)
    (cs : Set L.constSymbols) (fv : Set Nat) (stream : TermStream L) : Prop :=
  (∀ t, (∃ n, stream.entries n = some t) ↔ termsTermOfSymbols fs cs fv t) ∧
    (¬ ((∃ x, fv x) ∨ ∃ c, cs c) → stream.entries 0 = some (yVar 0))

/-- Definition 5.5.1: Admissibility of AVAILᵢ over fixed symbol and variable
sets: exact range, positive index, and first entry yᵢ. -/
@[blueprint "chap5__definition_5_5_1"]
def AvailAdmissibleOfSymbols {L : Language} (fs : Set L.funSymbols)
    (cs : Set L.constSymbols) (fv : Set Nat) (i : Nat) (stream : TermStream L) : Prop :=
  0 < i ∧ (∀ t, (∃ n, stream.entries n = some t) ↔ availTermOfSymbols fs cs fv i t) ∧
    stream.entries 0 = some (yVar i)





/-- Definition 5.5.1: A finite displayed list agrees entry by entry with
the beginning of an admissible stream. -/
@[blueprint "chap5__example_5_5_1"]
def TermStream.HasPrefix {L : Language} (stream : TermStream L) (xs : List (Term L)) : Prop :=
  ∀ i : Fin xs.length, stream.entries i.val = some xs[i]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Removing the first displayed entry corresponds to taking the stream's tail. -/
theorem TermStream.HasPrefix.tail {L : Language} {stream : TermStream L}
    {t : Term L} {ts : List (Term L)} (h : stream.HasPrefix (t :: ts)) :
    stream.tail.HasPrefix ts := by
  intro i
  exact h ⟨i.val + 1, by simpa using Nat.succ_lt_succ i.isLt⟩

/-- §5.5.1 (standing assumption, using Lemma 5.3.4): the bound variables of a possibly
infinite input sequent built from the x-variables can be renamed so that no variable
free in the sequent occurs bound in it; each formula keeps its position, its free
variables and its meaning in every structure. The book's "infinite supply of new
variables" is the hypothesis `hfresh`: infinitely many x-variables occur free nowhere
in the input (when every x-variable occurs free and a quantifier occurs, no bound-only
renaming exists). -/
@[attach_debt, blueprint "chap5__definition_5_5_1"]
theorem exists_renaming_crossNoFreeBoundInf {L : Language} (q : InfSequentN L)
    (hq : q.builtFromX)
    (hfresh : ∀ n : Nat, ∃ x : Nat, n ≤ x ∧ isXIndex x ∧
      (∀ i A, q.antecedent i = some A → x ∉ SyntaxN.Variables.formulaFVN A) ∧
      (∀ i B, q.succedent i = some B → x ∉ SyntaxN.Variables.formulaFVN B)) :
    ∃ q' : InfSequentN L, q'.builtFromX ∧ crossNoFreeBoundInf q' ∧
      (∀ i, (q'.antecedent i).isSome ↔ (q.antecedent i).isSome) ∧
      (∀ i, (q'.succedent i).isSome ↔ (q.succedent i).isSome) ∧
      (∀ i A A', q.antecedent i = some A → q'.antecedent i = some A' →
        SyntaxN.Variables.formulaFVN A' = SyntaxN.Variables.formulaFVN A ∧
        ∀ (M : Structure L) (s : Assignment M),
          SemanticsN.formulaEvalN M A' s ↔ SemanticsN.formulaEvalN M A s) ∧
      (∀ i B B', q.succedent i = some B → q'.succedent i = some B' →
        SyntaxN.Variables.formulaFVN B' = SyntaxN.Variables.formulaFVN B ∧
        ∀ (M : Structure L) (s : Assignment M),
          SemanticsN.formulaEvalN M B' s ↔ SemanticsN.formulaEvalN M B s)

end LCS.FirstOrder.Completeness.Search
end

section
namespace LCS.FirstOrder.Completeness
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.Completeness.Search

/-- Example 5.5.1: The eight displayed TERMS entries and the nine displayed
AVAIL₁ entries extend to admissible enumerations for the constant a, binary f,
and unary g, with no initial free variables. Their AVAIL₀ stream is tail(TERMS)
and has the seven displayed entries. The first AVAIL₁ entry is y₁. -/
@[attach_debt, blueprint "chap5__example_5_5_1" (main := true)]
theorem exAFG_admissible_prefixes :
    ∃ terms avail1 : TermStream exLangAFG,
      TermsAdmissibleOfSymbols (fun _ => True) (fun _ => True) (fun _ => False) terms ∧
      AvailAdmissibleOfSymbols (fun _ => True) (fun _ => True) (fun _ => False) 1 avail1 ∧
      terms.HasPrefix exTermsEnumFuncSyms ∧
      terms.tail.HasPrefix exAvail0AFG ∧
      avail1.HasPrefix exAvail1AFG 

end LCS.FirstOrder.Completeness
end

section
namespace LCS.FirstOrder.Completeness
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Completeness.Search LCS.FirstOrder.Completeness.InfiniteSearch

/-- Example 5.5.2: The input → A, with x, y, z, v represented by the
x-supply indices 0, 2, 4, 6. -/
@[blueprint "chap5__example_5_5_2"]
def exProofInput : InfSequentN exLangPQf2 :=
  InfSequentN.ofSequent (Sequent.mk [] [evenFormula exFormulaPQf2])

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 5.5.2: The input uses only the x-variable supply. -/
theorem exProofInput_builtFromX : exProofInput.builtFromX := by
  intro A h
  simp only [exProofInput, InfSequentN.memAntecedent_ofSequent,
    InfSequentN.memSuccedent_ofSequent, List.not_mem_nil, List.mem_cons,
    or_false, false_or] at h
  subst A
  exact FormulaN.builtFromX_evenFormula _

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 5.5.2: The input's only free variable v is distinct from
its bound variables x, y, and z. -/
theorem exProofInput_crossNoFreeBound : crossNoFreeBoundInf exProofInput := by
  rw [exProofInput, crossNoFreeBoundInf_ofSequent_iff]
  intro x hx B hB
  simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hB
  subst B
  simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨_, rfl, hx⟩ := hx
  simp [exFormulaPQf2, evenFormula, evenTerm, formulaFVN, formulaBVN,
    termFV, Set.union, Set.diff, Set.singleton, Set.iUnion, Set.empty,
    Membership.mem] at hx ⊢
  omega

/-- Example 5.5.2: The unary iterate fⁿ(t). -/
@[blueprint "chap5__example_5_5_2"]
def exPQfIter (n : Nat) (t : Term exLangPQf2) : Term exLangPQf2 :=
  Nat.rec t (fun _ u => Term.func ExFuncF2.f (fun _ => u)) n

/-- Example 5.5.2: The printed admissible schedules are TERMS = fⁿ(v)
and AVAILᵢ = fⁿ(yᵢ), with yᵢ from the odd-index supply. -/
@[blueprint "chap5__example_5_5_2"]
def exPQfEnumerationSchedule (enum : SearchEnumeration exProofInput) : Prop :=
  (∀ n, enum.terms.entries n = some (exPQfIter n (.var 6))) ∧
    ∀ i hi n, (enum.avail i hi).entries n = some (exPQfIter n (yVar i))

/-- Example 5.5.2: The actual round-k search state, including the tree,
TERM₀, AVAIL streams, activation counter, and branch-local formula records. -/
@[blueprint "chap5__example_5_5_2"]
noncomputable def exSearchProofFuncSyms (enum : SearchEnumeration exProofInput) (k : Nat) :=
  search51 (L := exLangPQf2) rfl exProofInput exProofInput_builtFromX
    exProofInput_crossNoFreeBound enum k

/-- Example 5.5.2: TERM₀ after rounds 0 through 4, in loop order.
The round-3 activation appends y₁ before the AVAIL₀ and AVAIL₁ transfers. -/
@[blueprint "chap5__example_5_5_2"]
def exPQfExpectedTerms (k : Nat) : List (Term exLangPQf2) :=
  let v : Term exLangPQf2 := .var 6
  let y := yVar (L := exLangPQf2) 1
  match k with
  | 0 => [v]
  | 1 => [v, exPQfIter 1 v]
  | 2 => [v, exPQfIter 1 v, exPQfIter 2 v]
  | 3 => [v, exPQfIter 1 v, exPQfIter 2 v, y, exPQfIter 3 v, exPQfIter 1 y]
  | _ => [v, exPQfIter 1 v, exPQfIter 2 v, y, exPQfIter 3 v, exPQfIter 1 y,
      exPQfIter 4 v, exPQfIter 2 y]

/-- Example 5.5.2: The round frontiers. T₁ contains the ∀:left instances;
the final Γ′ consists of P-atoms, and the right branch closes with ∃:right. -/
@[blueprint "chap5__example_5_5_2"]
def exPQfExpectedLeaves (k : Nat) : List (Sequent exLangPQf2) :=
  let p := fun t => FormulaN.predN ExPredPQf2.P (fun _ => t)
  let q := fun t => FormulaN.predN ExPredPQf2.Q (fun _ => t)
  let v : Term exLangPQf2 := .var 6
  let y := yVar (L := exLangPQf2) 1
  let allP := FormulaN.all 0 (p (.var 0))
  let exQ := FormulaN.ex 2 (q (.var 2))
  let exZQ := FormulaN.ex 4 (q (.var 4))
  let vs := [v, exPQfIter 1 v, exPQfIter 2 v]
  let us := [y, exPQfIter 3 v, exPQfIter 1 y]
  let t1 := Sequent.mk (vs.map p ++ [allP, exQ]) [p (exPQfIter 1 v)]
  match k with
  | 0 => [Sequent.mk [] [evenFormula exFormulaPQf2]]
  | 1 => [Sequent.mk [.conj allP exQ] [.conj (p (exPQfIter 1 v)) exZQ]]
  | 2 => [Sequent.mk [allP, exQ] [p (exPQfIter 1 v)], Sequent.mk [allP, exQ] [exZQ]]
  | 3 => [t1, Sequent.mk (vs.map p ++ [allP, q y]) (vs.map q ++ [exZQ])]
  | _ => [t1, Sequent.mk (vs.map p ++ us.map p ++ [allP, q y])
      (vs.map q ++ us.map q ++ [exZQ])]

/-- Example 5.5.2 (companion): An ordered display tree storing each G
inference with its original premise and conclusion sequents. These endpoints
are stored independently of edges contracted by the display projection. -/
@[blueprint "chap5__example_5_5_2"]
inductive SearchDiagram (L : Language) where
  | leaf (s : Sequent L) : SearchDiagram L
  | onePremise {prem conc : Sequent L} (rule : GentzenStep1Ext prem conc)
      (sub : SearchDiagram L) : SearchDiagram L
  | twoPremise {leftPrem rightPrem conc : Sequent L}
      (rule : GentzenStep2Ext leftPrem rightPrem conc)
      (left right : SearchDiagram L) : SearchDiagram L

/-- Example 5.5.2 (companion): The general diagram projection contracts only
administrative input-introduction (`extend`) edges, replacing each such node
by its projected child. It preserves every G inference, its original premise
and conclusion sequents, every leaf, and the left-to-right premise order.
It neither merges repeated inference nodes nor compresses consecutive rules.
The input is the deduction tree obtained by separately forgetting leaf records;
this same projection applies to the diagrams of Example 5.5.3. -/
@[blueprint "chap5__example_5_5_2"]
def exPQfDiagramProjection {L : Language} :
    {s : Sequent L} → InfGDeductionTreeExt s → SearchDiagram L
  | _, .leaf s => .leaf s
  | _, .onePremise rule sub => .onePremise rule (exPQfDiagramProjection sub)
  | _, .twoPremise rule left right =>
      .twoPremise rule (exPQfDiagramProjection left) (exPQfDiagramProjection right)
  | _, .extend _ _ sub => exPQfDiagramProjection sub

/-- Example 5.5.2: The first three displayed trees with all their internal
inferences. In the third tree T₁ is the left ∀:left proof subtree; T₂ is the
right chain ∀:left, ∃:left, ∃:right. The extended instance rules each use
[v, f(v), f²(v)], and the fresh variable y₁ has index 3. -/
@[blueprint "chap5__example_5_5_2"]
def exPQfExpectedTrees123 :
    let root := Sequent.mk [] [evenFormula exFormulaPQf2]
    InfGDeductionTreeExt root × InfGDeductionTreeExt root × InfGDeductionTreeExt root :=
  let p := fun t => FormulaN.predN ExPredPQf2.P (fun _ => t)
  let q := fun t => FormulaN.predN ExPredPQf2.Q (fun _ => t)
  let v : Term exLangPQf2 := .var 6
  let y : Term exLangPQf2 := .var 3
  let allP := FormulaN.all 0 (p (.var 0))
  let exQ := FormulaN.ex 2 (q (.var 2))
  let exZQ := FormulaN.ex 4 (q (.var 4))
  let pfv := p (exPQfIter 1 v)
  let ant := FormulaN.conj allP exQ
  let suc := FormulaN.conj pfv exZQ
  let root := Sequent.mk [] [FormulaN.impl ant suc]
  let vs := [v, exPQfIter 1 v, exPQfIter 2 v]
  let gamma := vs.map p
  let tree1 : InfGDeductionTreeExt root :=
    .onePremise (.implRight [] [] [] ant suc) (.leaf ⟨[ant], [suc]⟩)
  let tree2 : InfGDeductionTreeExt root :=
    .onePremise (.implRight [] [] [] ant suc)
      (.onePremise (.conjLeft [] [] [suc] allP exQ)
        (.twoPremise (.conjRight [allP, exQ] [] [] pfv exZQ)
          (.leaf ⟨[allP, exQ], [pfv]⟩) (.leaf ⟨[allP, exQ], [exZQ]⟩)))
  let t1 : InfGDeductionTreeExt (Sequent.mk [allP, exQ] [pfv]) :=
    .onePremise (.allLeft vs [] [exQ] [pfv] 0 (p (.var 0))
      (by simp [vs]) (by intro t ht; exact True.intro))
      (.leaf ⟨gamma ++ [allP, exQ], [pfv]⟩)
  let t2 : InfGDeductionTreeExt (Sequent.mk [allP, exQ] [exZQ]) :=
    .onePremise (.allLeft vs [] [exQ] [exZQ] 0 (p (.var 0))
      (by simp [vs]) (by intro t ht; exact True.intro))
      (.onePremise (.exLeft 3 (gamma ++ [allP]) [] [exZQ] 2 (q (.var 2))
        (by
          intro F hF
          simp [gamma, vs, p, q, v, allP, exQ, exZQ, exPQfIter,
            List.mem_cons, List.mem_append] at hF
          rcases hF with rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [formulaFVN, termFV, Set.iUnion, Set.union, Set.diff,
              Set.singleton, Set.empty, Membership.mem])
        (by exact True.intro))
        (.onePremise (.exRight vs (gamma ++ [allP, q y]) [] [] 4 (q (.var 4))
          (by simp [vs]) (by intro t ht; exact True.intro))
          (.leaf ⟨gamma ++ [allP, q y], vs.map q ++ [exZQ]⟩)))
  let tree3 : InfGDeductionTreeExt root :=
    .onePremise (.implRight [] [] [] ant suc)
      (.onePremise (.conjLeft [] [] [suc] allP exQ)
        (.twoPremise (.conjRight [allP, exQ] [] [] pfv exZQ) t1 t2))
  (tree1, tree2, tree3)

/-- Example 5.5.2: The first three actual scheduled search stages have
exactly the displayed ordered trees after administrative intake is contracted. -/
theorem exPQfDiagrams123 (enum : SearchEnumeration exProofInput)
    (hSchedule : exPQfEnumerationSchedule enum) :
    exPQfDiagramProjection (exSearchProofFuncSyms enum 1).tree.forget =
      exPQfDiagramProjection exPQfExpectedTrees123.1 ∧
    exPQfDiagramProjection (exSearchProofFuncSyms enum 2).tree.forget =
      exPQfDiagramProjection exPQfExpectedTrees123.2.1 ∧
    exPQfDiagramProjection (exSearchProofFuncSyms enum 3).tree.forget =
      exPQfDiagramProjection exPQfExpectedTrees123.2.2 := by
  -- REPAIR(T139): proof pending
  sorry

/-- Example 5.5.2 (companion): Select a subtree by its address in the
projected diagram. Unary and left edges are `false`, right edges are `true`.
An invalid address returns `none`; the empty address selects the whole tree. -/
@[blueprint "chap5__example_5_5_2"]
def SearchDiagram.subtreeAt {L : Language} : SearchDiagram L → List Bool → Option (SearchDiagram L)
  | t, [] => some t
  | .leaf _, _ :: _ => none
  | .onePremise _ t, false :: path => t.subtreeAt path
  | .onePremise _ _, true :: _ => none
  | .twoPremise _ left _, false :: path => left.subtreeAt path
  | .twoPremise _ _ right, true :: path => right.subtreeAt path

/-- Example 5.5.2: The three remaining displayed subtrees: T₁ after round
three, T₂ after round three, and T₂ after round four. The final compressed
line is represented by consecutive extended ∀:left and ∃:right inferences
with the newly available terms [y₁, f³(v), f(y₁)]. Γ′ contains the P-instances
of those terms as well as P(v), P(f(v)), P(f²(v)) and ∀x P(x). -/
@[blueprint "chap5__example_5_5_2"]
def exPQfExpectedTrees456 :
    let p := fun t => FormulaN.predN ExPredPQf2.P (fun _ => t)
    let q := fun t => FormulaN.predN ExPredPQf2.Q (fun _ => t)
    let ant := [FormulaN.all 0 (p (.var 0)), FormulaN.ex 2 (q (.var 2))]
    let leftRoot := Sequent.mk ant [p (exPQfIter 1 (.var 6))]
    let rightRoot := Sequent.mk ant [FormulaN.ex 4 (q (.var 4))]
    InfGDeductionTreeExt leftRoot × InfGDeductionTreeExt rightRoot × InfGDeductionTreeExt rightRoot :=
  let p := fun t => FormulaN.predN ExPredPQf2.P (fun _ => t)
  let q := fun t => FormulaN.predN ExPredPQf2.Q (fun _ => t)
  let v : Term exLangPQf2 := .var 6
  let y : Term exLangPQf2 := .var 3
  let allP := FormulaN.all 0 (p (.var 0))
  let exQ := FormulaN.ex 2 (q (.var 2))
  let exZQ := FormulaN.ex 4 (q (.var 4))
  let pfv := p (exPQfIter 1 v)
  let vs := [v, exPQfIter 1 v, exPQfIter 2 v]
  let us := [y, exPQfIter 3 v, exPQfIter 1 y]
  let gamma := vs.map p
  let t1 : InfGDeductionTreeExt (Sequent.mk [allP, exQ] [pfv]) :=
    .onePremise (.allLeft vs [] [exQ] [pfv] 0 (p (.var 0))
      (by simp [vs]) (by intro t ht; exact True.intro))
      (.leaf ⟨gamma ++ [allP, exQ], [pfv]⟩)
  let finish : InfGDeductionTreeExt
      (Sequent.mk (gamma ++ [allP, q y]) (vs.map q ++ [exZQ])) :=
    .onePremise (.allLeft us gamma [q y] (vs.map q ++ [exZQ]) 0 (p (.var 0))
      (by simp [us]) (by intro t ht; exact True.intro))
      (.onePremise (.exRight us (gamma ++ us.map p ++ [allP, q y]) (vs.map q) []
        4 (q (.var 4)) (by simp [us]) (by intro t ht; exact True.intro))
        (.leaf ⟨gamma ++ us.map p ++ [allP, q y], vs.map q ++ us.map q ++ [exZQ]⟩))
  let t2 (top : InfGDeductionTreeExt
      (Sequent.mk (gamma ++ [allP, q y]) (vs.map q ++ [exZQ]))) :
      InfGDeductionTreeExt (Sequent.mk [allP, exQ] [exZQ]) :=
    .onePremise (.allLeft vs [] [exQ] [exZQ] 0 (p (.var 0))
      (by simp [vs]) (by intro t ht; exact True.intro))
      (.onePremise (.exLeft 3 (gamma ++ [allP]) [] [exZQ] 2 (q (.var 2))
        (by
          intro F hF
          simp [gamma, vs, p, q, v, allP, exQ, exZQ, exPQfIter,
            List.mem_cons, List.mem_append] at hF
          rcases hF with rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [formulaFVN, termFV, Set.iUnion, Set.union, Set.diff,
              Set.singleton, Set.empty, Membership.mem])
        (by exact True.intro))
        (.onePremise (.exRight vs (gamma ++ [allP, q y]) [] [] 4 (q (.var 4))
          (by simp [vs]) (by intro t ht; exact True.intro)) top))
  (t1, t2 (.leaf _), t2 finish)

/-- Example 5.5.2: T₁ and T₂ occupy the left and right branches of the
round-three diagram. In round four the same right occurrence contains the
complete expanded T₂. Addresses are measured after contracting intake edges. -/
theorem exPQfDiagrams456 (enum : SearchEnumeration exProofInput)
    (hSchedule : exPQfEnumerationSchedule enum) :
    (exPQfDiagramProjection (exSearchProofFuncSyms enum 3).tree.forget).subtreeAt
        [false, false, false] = some (exPQfDiagramProjection exPQfExpectedTrees456.1) ∧
    (exPQfDiagramProjection (exSearchProofFuncSyms enum 3).tree.forget).subtreeAt
        [false, false, true] = some (exPQfDiagramProjection exPQfExpectedTrees456.2.1) ∧
    (exPQfDiagramProjection (exSearchProofFuncSyms enum 4).tree.forget).subtreeAt
        [false, false, true] = some (exPQfDiagramProjection exPQfExpectedTrees456.2.2) := by
  -- REPAIR(T140): proof pending
  sorry

/-- Example 5.5.2 (companion): Read the sequent and records of a leaf
at its diagram address. Intake edges consume no address component, matching
`exPQfDiagramProjection`; unary and left edges use `false`, right edges `true`.
Internal nodes and invalid addresses return `none`. -/
@[blueprint "chap5__example_5_5_2"]
def Search.SearchTree.diagramLeafAt {L : Language} :
    {s : Sequent L} → SearchTree s → List Bool → Option (Sequent L × BranchRecords L)
  | _, .extend _ _ sub, path => sub.diagramLeafAt path
  | _, .leaf s records, [] => some (s, records)
  | _, .onePremise _ sub, false :: path => sub.diagramLeafAt path
  | _, .twoPremise _ left _, false :: path => left.diagramLeafAt path
  | _, .twoPremise _ _ right, true :: path => right.diagramLeafAt path
  | _, _, _ => none

/-- Example 5.5.2: All TERM₀/FORM₀ rows at the actual leaf occurrences
through round four. The list order is the global term-position order, while
histories are read from the selected leaf's own records. Rounds one and two
have empty histories. The closed left branch records only ∀x P(x) at v, f(v),
and f²(v); the expanded right branch also records ∃z Q(z). Every newly appended
term has an empty history until it is used. Addresses match the diagrams after
intake-edge contraction, and the two branches remain separate. -/
theorem exPQfBranchHistories (enum : SearchEnumeration exProofInput)
    (hSchedule : exPQfEnumerationSchedule enum) :
    let p := fun t => FormulaN.predN ExPredPQf2.P (fun _ => t)
    let q := fun t => FormulaN.predN ExPredPQf2.Q (fun _ => t)
    let allP := FormulaN.all 0 (p (.var 0))
    let exZQ := FormulaN.ex 4 (q (.var 4))
    let v : Term exLangPQf2 := .var 6
    let y : Term exLangPQf2 := .var 3
    let fv := exPQfIter 1 v
    let ffv := exPQfIter 2 v
    let fffv := exPQfIter 3 v
    let ffffv := exPQfIter 4 v
    let fy := exPQfIter 1 y
    let ffy := exPQfIter 2 y
    let rows := fun k path =>
      ((exSearchProofFuncSyms enum k).tree.diagramLeafAt path).map fun leaf =>
        (exSearchProofFuncSyms enum k).TERM0.mapIdx fun i t => (t, leaf.2.FORM0 i)
    rows 1 [false] = some [(v, []), (fv, [])] ∧
    rows 2 [false, false, false] = some [(v, []), (fv, []), (ffv, [])] ∧
    rows 2 [false, false, true] = some [(v, []), (fv, []), (ffv, [])] ∧
    rows 3 [false, false, false, false] =
      some [(v, [allP]), (fv, [allP]), (ffv, [allP]),
        (y, []), (fffv, []), (fy, [])] ∧
    rows 3 [false, false, true, false, false, false] =
      some [(v, [allP, exZQ]), (fv, [allP, exZQ]), (ffv, [allP, exZQ]),
        (y, []), (fffv, []), (fy, [])] ∧
    rows 4 [false, false, false, false] =
      some [(v, [allP]), (fv, [allP]), (ffv, [allP]),
        (y, []), (fffv, []), (fy, []), (ffffv, []), (ffy, [])] ∧
    rows 4 [false, false, true, false, false, false, false, false] =
      some [(v, [allP, exZQ]), (fv, [allP, exZQ]), (ffv, [allP, exZQ]),
        (y, [allP, exZQ]), (fffv, [allP, exZQ]), (fy, [allP, exZQ]),
        (ffffv, []), (ffy, [])] := by
  -- REPAIR(T141): proof pending
  sorry

/-- Example 5.5.2: Admissible printed enumerations yield the displayed four
rounds of search51, with exact TERM₀ order and AVAIL tails. Round 4 is finished
and all its leaves are axioms. -/
@[attach_debt, blueprint "chap5__example_5_5_2" (main := true)]
theorem exProofTreeClosureFuncSyms :
    ∃ enum : SearchEnumeration exProofInput,
      exPQfEnumerationSchedule enum ∧
      (∀ k, k ≤ 4 →
        (exSearchProofFuncSyms enum k).TERM0 = exPQfExpectedTerms k ∧
        (exSearchProofFuncSyms enum k).tree.forget.leaves = exPQfExpectedLeaves k ∧
        (exSearchProofFuncSyms enum k).numact = (if k < 3 then 0 else 1) ∧
        (∀ n, ((exSearchProofFuncSyms enum k).avail 0).entries n =
          some (exPQfIter (n + k + 1) (.var 6))) ∧
        (∀ n, ((exSearchProofFuncSyms enum k).avail 1).entries n =
          some (exPQfIter (if k < 3 then n else n + k - 1) (yVar 1))) ∧
        (∀ i, 1 < i → ∀ n, ((exSearchProofFuncSyms enum k).avail i).entries n =
          some (exPQfIter n (yVar i)))) ∧
      allFinished (L := exLangPQf2) rfl (exSearchProofFuncSyms enum 4) ∧
      ∀ leaf ∈ (exSearchProofFuncSyms enum 4).tree.forget.leaves, isAxiom leaf 

end LCS.FirstOrder.Completeness
end

section
namespace LCS.FirstOrder.Completeness
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Completeness.Search LCS.FirstOrder.Completeness.InfiniteSearch

/-- Example 5.5.3: The input → A in the x-variable supply, with bound
variables x and y at indices 0 and 2. -/
@[blueprint "chap5__example_5_5_3"]
def exCounterInput : InfSequentN exLangPQa :=
  InfSequentN.ofSequent (Sequent.mk [] [evenFormula exFormulaPQa])

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 5.5.3: The input is built entirely from x-variables. -/
theorem exCounterInput_builtFromX : exCounterInput.builtFromX := by
  intro A h
  simp only [exCounterInput, InfSequentN.memAntecedent_ofSequent,
    InfSequentN.memSuccedent_ofSequent, List.not_mem_nil, List.mem_cons,
    or_false, false_or] at h
  subst A
  exact FormulaN.builtFromX_evenFormula _

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 5.5.3: The closed input satisfies the free/bound convention. -/
theorem exCounterInput_crossNoFreeBound : crossNoFreeBoundInf exCounterInput := by
  rw [exCounterInput, crossNoFreeBoundInf_ofSequent_iff]
  intro x hx B hB
  simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨_, rfl, hx⟩ := hx
  simp [exFormulaPQa, evenFormula, evenTerm, formulaFVN, termFV,
    Set.union, Set.diff, Set.singleton, Set.iUnion, Set.empty, Membership.mem] at hx
  rcases hx with ⟨⟨_, h⟩, hn⟩ | ⟨⟨_, _, h⟩, hn⟩ <;> exact (hn h).elim

/-- Example 5.5.3: The unary iterate fⁿ(t). -/
@[blueprint "chap5__example_5_5_3"]
def exPQaIter (n : Nat) (t : Term exLangPQa) : Term exLangPQa :=
  Nat.rec t (fun _ u => Term.func ExFuncFa.f (fun _ => u)) n

/-- Example 5.5.3: The printed schedules enumerate fⁿ(a) for TERMS
and fⁿ(yᵢ) for each positive AVAILᵢ. -/
@[blueprint "chap5__example_5_5_3"]
def exPQaEnumerationSchedule (enum : SearchEnumeration exCounterInput) : Prop :=
  (∀ n, enum.terms.entries n = some (exPQaIter n (.const ExConstA.a))) ∧
    ∀ i hi n, (enum.avail i hi).entries n = some (exPQaIter n (yVar i))

/-- Example 5.5.3: The actual round-k state of search51 on → A, including
the tree, TERM₀, AVAIL streams, NUMACT, and branch-local records. -/
@[blueprint "chap5__example_5_5_3"]
noncomputable def exSearchCounterFuncSyms (enum : SearchEnumeration exCounterInput) (k : Nat) :=
  search51 (L := exLangPQa) rfl exCounterInput exCounterInput_builtFromX
    exCounterInput_crossNoFreeBound enum k

/-- Example 5.5.3: TERM₀ in the procedure's loop order. In round 2,
y₁ precedes the AVAIL₀ transfer f²(a), followed by the AVAIL₁ transfer f(y₁). -/
@[blueprint "chap5__example_5_5_3"]
def exPQaExpectedTerms (k : Nat) : List (Term exLangPQa) :=
  let a : Term exLangPQa := .const ExConstA.a
  let y1 := yVar (L := exLangPQa) 1
  let y2 := yVar (L := exLangPQa) 2
  match k with
  | 0 => [a]
  | 1 => [a, exPQaIter 1 a]
  | 2 => [a, exPQaIter 1 a, y1, exPQaIter 2 a, exPQaIter 1 y1]
  | _ => [a, exPQaIter 1 a, y1, exPQaIter 2 a, exPQaIter 1 y1,
      y2, exPQaIter 3 a, exPQaIter 2 y1, exPQaIter 1 y2]

/-- Example 5.5.3: The successive frontiers result from ⊃:right,
then ∧:left and ∀:right(y₁), then ∃:left(y₂). -/
@[blueprint "chap5__example_5_5_3"]
def exPQaExpectedLeaves (k : Nat) : List (Sequent exLangPQa) :=
  let p := fun t => FormulaN.predN ExPredPQa.P (fun _ => t)
  let qa := FormulaN.predN ExPredPQa.Q (fun _ => Term.const ExConstA.a)
  let exP := FormulaN.ex 0 (p (.var 0))
  let allPf := FormulaN.all 2 (p (exPQaIter 1 (.var 2)))
  match k with
  | 0 => [Sequent.mk [] [evenFormula exFormulaPQa]]
  | 1 => [Sequent.mk [.conj exP qa] [allPf]]
  | 2 => [Sequent.mk [exP, qa] [p (exPQaIter 1 (yVar 1))]]
  | _ => [exFinishedNonclosedTree]

/-- Example 5.5.3: The three complete ordered round trees. The compressed
conjunction-left/universal-right line is represented by its two G inferences.
The fresh variables y₁ and y₂ have indices 3 and 5, distinct from the input
binders 0 and 2. The third tree ends at P(y₂), Q(a) → P(f(y₁)). -/
@[blueprint "chap5__example_5_5_3"]
def exPQaExpectedTrees123 :
    let root := Sequent.mk [] [evenFormula exFormulaPQa]
    InfGDeductionTreeExt root × InfGDeductionTreeExt root × InfGDeductionTreeExt root :=
  let p : Term exLangPQa → FormulaN exLangPQa :=
    fun t => .predN ExPredPQa.P (fun _ => t)
  let f : Term exLangPQa → Term exLangPQa :=
    fun t => .func ExFuncFa.f (fun _ => t)
  let qa : FormulaN exLangPQa := .predN ExPredPQa.Q (fun _ => .const ExConstA.a)
  let exP := FormulaN.ex 0 (p (.var 0))
  let allPf := FormulaN.all 2 (p (f (.var 2)))
  let ant := FormulaN.conj exP qa
  let root := Sequent.mk [] [FormulaN.impl ant allPf]
  let pfy1 := p (f (.var 3))
  let tree1 : InfGDeductionTreeExt root :=
    .onePremise (.implRight [] [] [] ant allPf) (.leaf ⟨[ant], [allPf]⟩)
  let trunk (top : InfGDeductionTreeExt (Sequent.mk [exP, qa] [pfy1])) :
      InfGDeductionTreeExt root :=
    .onePremise (.implRight [] [] [] ant allPf)
      (.onePremise (.conjLeft [] [] [allPf] exP qa)
        (.onePremise (.allRight 3 [exP, qa] [] [] 2 (p (f (.var 2)))
          (by
            intro F hF
            simp [exP, qa, allPf, p, f, List.mem_cons] at hF
            rcases hF with rfl | rfl | rfl <;>
              simp [formulaFVN, termFV, Set.iUnion, Set.union, Set.diff,
                Set.singleton, Set.empty, Membership.mem])
          (by exact True.intro)) top))
  let tree2 := trunk (.leaf ⟨[exP, qa], [pfy1]⟩)
  let tree3 := trunk
    (.onePremise (.exLeft 5 [] [qa] [pfy1] 0 (p (.var 0))
      (by
        intro F hF
        simp [exP, qa, pfy1, p, f, List.mem_cons] at hF
        rcases hF with rfl | rfl | rfl <;>
          simp [formulaFVN, termFV, Set.iUnion, Set.union, Set.diff,
            Set.singleton, Set.empty, Membership.mem])
      (by exact True.intro))
      (.leaf ⟨[p (.var 5), qa], [pfy1]⟩))
  (tree1, tree2, tree3)

/-- Example 5.5.3: The first three actual counterexample-search stages
have the displayed whole trees under the shared intake-edge projection. -/
theorem exPQaRoundDiagrams (enum : SearchEnumeration exCounterInput)
    (hSchedule : exPQaEnumerationSchedule enum) :
    exPQfDiagramProjection (exSearchCounterFuncSyms enum 1).tree.forget =
      exPQfDiagramProjection exPQaExpectedTrees123.1 ∧
    exPQfDiagramProjection (exSearchCounterFuncSyms enum 2).tree.forget =
      exPQfDiagramProjection exPQaExpectedTrees123.2.1 ∧
    exPQfDiagramProjection (exSearchCounterFuncSyms enum 3).tree.forget =
      exPQfDiagramProjection exPQaExpectedTrees123.2.2 := by
  -- REPAIR(T142): proof pending
  sorry

/-- Example 5.5.3: Every TERM₀ position has an empty FORM₀ history at
its actual leaf occurrence in rounds one, two, and three. The paired lists
follow the procedure's term order and include every newly appended slot.
Addresses contract intake edges, as in the displayed round trees. -/
theorem exPQaBranchHistories (enum : SearchEnumeration exCounterInput)
    (hSchedule : exPQaEnumerationSchedule enum) :
    let a : Term exLangPQa := .const ExConstA.a
    let y1 := yVar (L := exLangPQa) 1
    let y2 := yVar (L := exLangPQa) 2
    let rows := fun k path =>
      ((exSearchCounterFuncSyms enum k).tree.diagramLeafAt path).map fun leaf =>
        (exSearchCounterFuncSyms enum k).TERM0.mapIdx fun i t => (t, leaf.2.FORM0 i)
    rows 1 [false] = some [(a, []), (exPQaIter 1 a, [])] ∧
    rows 2 [false, false, false] =
      some [(a, []), (exPQaIter 1 a, []), (y1, []),
        (exPQaIter 2 a, []), (exPQaIter 1 y1, [])] ∧
    rows 3 [false, false, false, false] =
      some [(a, []), (exPQaIter 1 a, []), (y1, []),
        (exPQaIter 2 a, []), (exPQaIter 1 y1, []), (y2, []),
        (exPQaIter 3 a, []), (exPQaIter 2 y1, []), (exPQaIter 1 y2, [])] := by
  -- REPAIR(T143): proof pending
  sorry

/-- Example 5.5.3: Admissible printed schedules produce the three displayed
rounds with the loop-order TERM₀ and exact AVAIL tails. The round-3 tree is
finished and nonclosed. -/
@[attach_debt, blueprint "chap5__example_5_5_3" (main := true)]
theorem exSearchCounterFuncSyms_trace :
    ∃ enum : SearchEnumeration exCounterInput,
      exPQaEnumerationSchedule enum ∧
      (∀ k, k ≤ 3 →
        (exSearchCounterFuncSyms enum k).TERM0 = exPQaExpectedTerms k ∧
        (exSearchCounterFuncSyms enum k).tree.forget.leaves = exPQaExpectedLeaves k ∧
        (exSearchCounterFuncSyms enum k).numact = (if k < 2 then 0 else k - 1) ∧
        (∀ n, ((exSearchCounterFuncSyms enum k).avail 0).entries n =
          some (exPQaIter (n + k + 1) (.const ExConstA.a))) ∧
        (∀ n, ((exSearchCounterFuncSyms enum k).avail 1).entries n =
          some (exPQaIter (if k < 2 then n else n + k) (yVar 1))) ∧
        (∀ n, ((exSearchCounterFuncSyms enum k).avail 2).entries n =
          some (exPQaIter (if k < 3 then n else n + 2) (yVar 2))) ∧
        (∀ i, 2 < i → ∀ n, ((exSearchCounterFuncSyms enum k).avail i).entries n =
          some (exPQaIter n (yVar i)))) ∧
      allFinished (L := exLangPQa) rfl (exSearchCounterFuncSyms enum 3) ∧
      ∀ leaf ∈ (exSearchCounterFuncSyms enum 3).tree.forget.leaves, ¬ isAxiom leaf 

end LCS.FirstOrder.Completeness
end

