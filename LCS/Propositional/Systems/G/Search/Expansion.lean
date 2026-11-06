import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import Attach
import LCS.Propositional.Systems.G.Search.Expansion.ProofsStamp

/-! # Procedure expand (Definition 3.4.6)

Atomic and nonatomic propositions, finished leaves and trees, the function
dosubstitution, and procedure expand, which applies the rule for every
nonatomic proposition of a leaf from left to right.
-/
section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

/-- The two stopping conventions of Definition 3.4.6. Systematic search
    closes axiom leaves immediately; atomic search expands them until all
    formulas are variables. -/
@[blueprint "chap3__definition_3_4_6"]
inductive SearchMode where
  | systematic
  | atomic
  deriving DecidableEq, Repr

variable {mode : SearchMode}

/-- Definition 3.4.6 (companion): A proposition is atomic if it is a
    propositional variable (PropFormulaNormalized.var _). -/
@[blueprint "chap3__definition_3_4_6"]
def isAtomicFormula : PropFormulaNormalized → Prop
  | .var _ => True
  | _ => False

/-- Definition 3.4.6 (companion): A proposition is nonatomic if it is not
    atomic, i.e. it has a top-level connective (neg, conj, disj, impl). -/
@[blueprint "chap3__definition_3_4_6"]
def isNonatomicFormula : PropFormulaNormalized → Prop
  | .var _ => False
  | _ => True

/-- Definition 3.4.6 (companion): Decidable version of isAtomicFormula
    for computation. -/
@[blueprint "chap3__definition_3_4_6"]
def isAtomicBool : PropFormulaNormalized → Bool
  | .var _ => true
  | _ => false

/-- Definition 3.4.6 (companion): Decidable version of isNonatomicFormula
    for computation. -/
@[blueprint "chap3__definition_3_4_6"]
def isNonatomicBool : PropFormulaNormalized → Bool
  | .var _ => false
  | _ => true

-- ========= Definition 3.4.6: Finished leaves and trees =========

/-- Definition 3.4.6 (companion): A leaf is finished when all formulas
    are atomic, or, in systematic mode, when it is an axiom. -/
@[blueprint "chap3__definition_3_4_6"]
def isFinishedLeaf (mode : SearchMode) (s : Sequent) : Prop :=
  (mode = .systematic ∧ isAxiom s) ∨
  (∀ A ∈ s.antecedent ++ s.succedent, isAtomicFormula A)

/-- Definition 3.4.6 (companion): Decidable version of isFinishedLeaf. -/
@[blueprint "chap3__definition_3_4_6"]
def isFinishedLeafBool (mode : SearchMode) (s : Sequent) : Bool :=
  ((mode == .systematic) &&
    (s.antecedent.any (fun A => s.succedent.any (fun B => A == B)))) ||
  ((s.antecedent ++ s.succedent).all isAtomicBool)

/-- Definition 3.4.6 (companion): All leaves of a deduction tree are
    finished. -/
@[blueprint "chap3__definition_3_4_6"]
def isFinishedTree (mode : SearchMode) {s : Sequent} (dt : DeductionTree s) : Prop :=
  ∀ s ∈ dt.leaves, isFinishedLeaf mode s

/-- Definition 3.4.6 (companion): Decidable version of isFinishedTree. -/
@[blueprint "chap3__definition_3_4_6"]
def isFinishedTreeBool (mode : SearchMode) {s : Sequent} (dt : DeductionTree s) : Bool :=
  dt.leaves.all (isFinishedLeafBool mode)

-- ========= Transport lemmas for indexed DeductionTree =========

/-- Transport through a type-index equality does not change the list of
    leaves. -/
theorem DeductionTree.leaves_eq_rec {s s' : Sequent} (heq : s' = s)
    (dt : DeductionTree s') : (heq ▸ dt : DeductionTree s).leaves = dt.leaves := by
-- BEGIN PROOF
  subst heq; rfl

-- ========= Definition 3.4.6: doSubstitution =========

/-- An address identifies one node, including unary edges, even when
    distinct nodes carry identical sequents. -/
@[blueprint "chap3__definition_3_4_6"]
inductive NodeAddress : {s : Sequent} → DeductionTree s → Sequent → Type where
  | here {s : Sequent} (tree : DeductionTree s) : NodeAddress tree s
  | down {p c t : Sequent} {rule : GentzenStep1 p c} {child : DeductionTree p} :
      NodeAddress child t → NodeAddress (.onePremise rule child) t
  | left {p q c t : Sequent} {rule : GentzenStep2 p q c}
      {left : DeductionTree p} {right : DeductionTree q} :
      NodeAddress left t → NodeAddress (.twoPremise rule left right) t
  | right {p q c t : Sequent} {rule : GentzenStep2 p q c}
      {left : DeductionTree p} {right : DeductionTree q} :
      NodeAddress right t → NodeAddress (.twoPremise rule left right) t

/-- Definition 3.4.6: Substitute at the single addressed node. -/
@[blueprint "chap3__definition_3_4_6"]
def doSubstitution {s target : Sequent} {tree : DeductionTree s}
    (address : NodeAddress tree target) (replacement : DeductionTree target) :
    DeductionTree s :=
  match address with
  | .here _ => replacement
  | .down (rule := rule) a => .onePremise rule (doSubstitution a replacement)
  | .left (rule := rule) (right := right) a => .twoPremise rule (doSubstitution a replacement) right
  | .right (rule := rule) (left := left) a => .twoPremise rule left (doSubstitution a replacement)

/-- Replace each leaf once, traversing the input tree rather than the
    newly inserted subtrees. This preserves the identities of equal leaves. -/
@[blueprint "chap3__definition_3_4_6"]
def mapLeaves (expand : (s : Sequent) → DeductionTree s) :
    {s : Sequent} → DeductionTree s → DeductionTree s
  | _, .leaf s => expand s
  | _, .onePremise rule child => .onePremise rule (mapLeaves expand child)
  | _, .twoPremise rule left right =>
    .twoPremise rule (mapLeaves expand left) (mapLeaves expand right)

-- ========= Definition 3.4.6: expandLeaf =========

/-- Definition 3.4.6 (companion): Finds the first nonatomic formula in a
    list, returning the formula and its index. -/
@[blueprint "chap3__definition_3_4_6"]
def findFirstNonatomic (L : List PropFormulaNormalized) (k : Nat := 0) :
    Option (PropFormulaNormalized × Nat) :=
  match L with
  | [] => none
  | A :: rest => if isNonatomicBool A then some (A, k) else findFirstNonatomic rest (k + 1)

/-- Definition 3.4.6 (required helper): If `findFirstNonatomic L = some (A, i)`,
    then `L = L.take i ++ [A] ++ L.drop (i+1)`. Enables `expandLeaf` to
    construct `DeductionTree s` by rewriting `s.antecedent` (resp. `s.succedent`)
    into its rule-shaped split form. -/
@[blueprint "chap3__definition_3_4_6"]
theorem findFirstNonatomic_split
    (ante : List PropFormulaNormalized) (A : PropFormulaNormalized) (i : Nat)
    (h : findFirstNonatomic ante = some (A, i)) :
    ante = ante.take i ++ [A] ++ ante.drop (i + 1) 

/-- Apply the rule at the selected occurrence on either side. The selectors
    certify the split around that occurrence. -/
@[blueprint "chap3__definition_3_4_6"]
def expandSelected (s : Sequent)
    (pickAnte pickSucc : Option (PropFormulaNormalized × Nat))
    (splitAnte : ∀ A i, pickAnte = some (A, i) →
      s.antecedent = s.antecedent.take i ++ [A] ++ s.antecedent.drop (i + 1))
    (splitSucc : ∀ A i, pickSucc = some (A, i) →
      s.succedent = s.succedent.take i ++ [A] ++ s.succedent.drop (i + 1)) : DeductionTree s :=
  match (generalizing := false) hAnte : pickAnte with
  | some (A, i) =>
    let gamma := s.antecedent.take i
    let delta := s.antecedent.drop (i + 1)
    let hsplit : s.antecedent = gamma ++ [A] ++ delta :=
      splitAnte A i hAnte
    let hseq : Sequent.mk (gamma ++ [A] ++ delta) s.succedent = s := by
      cases s with | mk ante succ => simp at hsplit; simp [hsplit.symm]
    match A, hseq with
    | .neg C, heq =>
      let prem : Sequent := Sequent.mk (gamma ++ delta) (C :: s.succedent)
      heq ▸ DeductionTree.onePremise (GentzenStep1.negLeft gamma delta s.succedent C)
        (DeductionTree.leaf prem)
    | .conj C D, heq =>
      let prem : Sequent := Sequent.mk (gamma ++ [C, D] ++ delta) s.succedent
      heq ▸ DeductionTree.onePremise (GentzenStep1.andLeft gamma delta s.succedent C D)
        (DeductionTree.leaf prem)
    | .disj C D, heq =>
      let p1 : Sequent := Sequent.mk (gamma ++ [C] ++ delta) s.succedent
      let p2 : Sequent := Sequent.mk (gamma ++ [D] ++ delta) s.succedent
      heq ▸ DeductionTree.twoPremise (GentzenStep2.orLeft gamma delta s.succedent C D)
        (DeductionTree.leaf p1) (DeductionTree.leaf p2)
    | .impl C D, heq =>
      let p1 : Sequent := Sequent.mk (gamma ++ delta) (C :: s.succedent)
      let p2 : Sequent := Sequent.mk ([D] ++ gamma ++ delta) s.succedent
      heq ▸ DeductionTree.twoPremise (GentzenStep2.implLeft gamma delta s.succedent C D)
        (DeductionTree.leaf p1) (DeductionTree.leaf p2)
    | .var _, _ => DeductionTree.leaf s
  | none =>
    match (generalizing := false) hSucc : pickSucc with
    | some (B, j) =>
      let delta := s.succedent.take j
      let lambda := s.succedent.drop (j + 1)
      let hsplit : s.succedent = delta ++ [B] ++ lambda :=
        splitSucc B j hSucc
      let hseq : Sequent.mk s.antecedent (delta ++ [B] ++ lambda) = s := by
        cases s with | mk ante succ => simp at hsplit; simp [hsplit.symm]
      match B, hseq with
      | .neg C, heq =>
        let prem : Sequent := Sequent.mk (C :: s.antecedent) (delta ++ lambda)
        heq ▸ DeductionTree.onePremise
          (GentzenStep1.negRight s.antecedent delta lambda C)
          (DeductionTree.leaf prem)
      | .conj C D, heq =>
        let p1 : Sequent := Sequent.mk s.antecedent (delta ++ [C] ++ lambda)
        let p2 : Sequent := Sequent.mk s.antecedent (delta ++ [D] ++ lambda)
        heq ▸ DeductionTree.twoPremise
          (GentzenStep2.andRight s.antecedent delta lambda C D)
          (DeductionTree.leaf p1) (DeductionTree.leaf p2)
      | .disj C D, heq =>
        let prem : Sequent := Sequent.mk s.antecedent (delta ++ [C, D] ++ lambda)
        heq ▸ DeductionTree.onePremise
          (GentzenStep1.orRight s.antecedent delta lambda C D)
          (DeductionTree.leaf prem)
      | .impl C D, heq =>
        let prem : Sequent := Sequent.mk (C :: s.antecedent) (D :: (delta ++ lambda))
        heq ▸ DeductionTree.onePremise
          (GentzenStep1.implRight s.antecedent delta lambda C D)
          (DeductionTree.leaf prem)
      | .var _, _ => DeductionTree.leaf s
    | none => DeductionTree.leaf s

/-- The first effective step of a round; preceding atomic occurrences do
    not generate rules. -/
@[blueprint "chap3__definition_3_4_6"]
def expandFirstFormula (s : Sequent) : DeductionTree s :=
  expandSelected s (findFirstNonatomic s.antecedent) (findFirstNonatomic s.succedent)
    (findFirstNonatomic_split s.antecedent) (findFirstNonatomic_split s.succedent)

@[blueprint "chap3__definition_3_4_6"]
def selectOffset (offset : Nat) (L : List PropFormulaNormalized) :
    Option (PropFormulaNormalized × Nat) :=
  let i := L.length - (offset + 1)
  L[i]?.map (fun A => (A, i))

@[blueprint "chap3__definition_3_4_6"]
theorem selectOffset_split (offset : Nat) (L : List PropFormulaNormalized)
    (A : PropFormulaNormalized) (i : Nat)
    (h : selectOffset offset L = some (A, i)) :
    L = L.take i ++ [A] ++ L.drop (i + 1) 

/-- A frozen schedule records the side and number of original occurrences
    to the right. The untouched suffix keeps these addresses stable when
    earlier rules insert formulas, including equal formulas. -/
@[blueprint "chap3__definition_3_4_6"]
def expandScheduled (mode : SearchMode) (rightSide : Bool) (offset : Nat) (s : Sequent) :
    DeductionTree s :=
  if isFinishedLeafBool mode s then .leaf s
  else if rightSide then
    expandSelected s none (selectOffset offset s.succedent)
      (by intros; contradiction) (selectOffset_split offset s.succedent)
  else
    expandSelected s (selectOffset offset s.antecedent) none
      (selectOffset_split offset s.antecedent) (by intros; contradiction)

@[blueprint "chap3__definition_3_4_6"]
def expandSchedule (mode : SearchMode) {s : Sequent} (schedule : List (Bool × Nat))
    (tree : DeductionTree s) : DeductionTree s :=
  schedule.foldl (fun dt entry => mapLeaves (expandScheduled mode entry.1 entry.2) dt) tree

@[blueprint "chap3__definition_3_4_6"]
def suffixSchedule (rightSide : Bool) (count : Nat) : List (Bool × Nat) :=
  (List.range count).reverse.map (fun offset => (rightSide, offset))

/-- Definition 3.4.6: Expand every formula present in the original leaf,
    antecedent first and then succedent. Systematic mode stops at axioms;
    atomic mode continues through them. Newly introduced subformulas wait
    for the next round. -/
@[blueprint "chap3__definition_3_4_6"]
def expandLeaf (mode : SearchMode) (s : Sequent) : DeductionTree s :=
  if isFinishedLeafBool mode s then .leaf s
  else
    let remaining := match findFirstNonatomic s.antecedent with
      | some (_, i) => suffixSchedule false (s.antecedent.length - (i + 1)) ++
          suffixSchedule true s.succedent.length
      | none => match findFirstNonatomic s.succedent with
        | some (_, i) => suffixSchedule true (s.succedent.length - (i + 1))
        | none => []
    expandSchedule mode remaining (expandFirstFormula s)

-- ========= pathToLeaf: construct a path from root to a given leaf =========



-- ========= sequentsAlongPath' never empty =========



-- ========= pathToLeaf_reaches_leaf =========



-- ========= leaf is in sequentsAlongPath' =========



-- ========= leaf_signedSet_subset_pathSignedSet =========



-- ========= Theorem 3.4.1: search produces a finished tree =========

-- Bridge: isAtomicBool reflects isAtomicFormula
theorem isAtomicBool_iff (A : PropFormulaNormalized) :
    isAtomicBool A = true ↔ isAtomicFormula A := by
-- BEGIN PROOF
  cases A <;> simp_all [isAtomicBool, isAtomicFormula]

-- Bridge: isFinishedLeafBool reflects isFinishedLeaf
theorem isFinishedLeafBool_iff (s : Sequent) :
    isFinishedLeafBool mode s = true ↔ isFinishedLeaf mode s := by
-- BEGIN PROOF
  simp only [isFinishedLeafBool, isFinishedLeaf, Bool.or_eq_true, Bool.and_eq_true,
             List.any_eq_true, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h
    rcases h with ⟨hmode, A, hA, B, hB, rfl⟩ | hall
    · exact Or.inl ⟨hmode, A, hA, hB⟩
    · exact Or.inr (fun A hA => (isAtomicBool_iff A).mp (hall A hA))
  · intro h
    rcases h with ⟨hmode, A, hA, hB⟩ | hall
    · exact Or.inl ⟨hmode, A, hA, A, hB, rfl⟩
    · exact Or.inr (fun A hA => (isAtomicBool_iff A).mpr (hall A hA))

-- Bridge: isFinishedTreeBool reflects isFinishedTree
theorem isFinishedTreeBool_iff_isFinishedTree {c : Sequent} (dt : DeductionTree c) :
    isFinishedTreeBool mode dt = true ↔ isFinishedTree mode dt := by
-- BEGIN PROOF
  simp only [isFinishedTreeBool, isFinishedTree, List.all_eq_true]
  exact forall_congr' (fun s => forall_congr' (fun _ => isFinishedLeafBool_iff s))

theorem findFirstNonatomic_spec_aux (L : List PropFormulaNormalized) (k : Nat)
    (A : PropFormulaNormalized) (i : Nat)
    (h : findFirstNonatomic L k = some (A, i)) :
    k ≤ i ∧ L[i - k]? = some A ∧ isNonatomicBool A = true := by
-- BEGIN PROOF
  induction L generalizing k with
  | nil => simp [findFirstNonatomic] at h
  | cons x xs ih =>
    simp only [findFirstNonatomic] at h; split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; simp [Nat.sub_self, *]
    · have step := ih (k + 1) h; refine ⟨by omega, ?_, step.2.2⟩
      rw [show i - k = (i - (k + 1)) + 1 from by omega]
      simp [List.getElem?_cons_succ]; exact step.2.1

theorem findFirstNonatomic_spec (L : List PropFormulaNormalized) (A : PropFormulaNormalized) (i : Nat)
    (h : findFirstNonatomic L = some (A, i)) :
    i < L.length ∧ L[i]? = some A ∧ isNonatomicBool A = true := by
-- BEGIN PROOF
  have aux := findFirstNonatomic_spec_aux L 0 A i h
  obtain ⟨_, hget, hna⟩ := aux; simp at hget
  exact ⟨Classical.byContradiction fun hge => by
    rw [List.getElem?_eq_none (by omega)] at hget; simp at hget, hget, hna⟩

theorem findFirstNonatomic_none_all_atomic (L : List PropFormulaNormalized) (k : Nat)
    (h : findFirstNonatomic L k = none) :
    ∀ A ∈ L, isAtomicFormula A := by
-- BEGIN PROOF
  induction L generalizing k with
  | nil => intro A hA; simp at hA
  | cons x xs ih =>
    simp only [findFirstNonatomic] at h
    split at h
    · simp at h
    · case isFalse hna =>
      intro A hA
      cases List.mem_cons.mp hA with
      | inl heq =>
        subst heq
        cases A with
        | var _ => exact trivial
        | _ => simp [isNonatomicBool] at hna
      | inr hmem => exact ih (k + 1) h A hmem

/-- Finished leaves are preserved by expansion. -/
theorem expandLeaf_of_finished (s : Sequent) (h : isFinishedLeafBool mode s = true) :
    expandLeaf mode s = .leaf s := by simp [expandLeaf, h]

/-- The frozen schedule visits the leftmost remaining occurrence first. -/
theorem suffixSchedule_succ (side : Bool) (n : Nat) :
    suffixSchedule side (n + 1) = (side, n) :: suffixSchedule side n := by
  simp [suffixSchedule, List.range_succ, List.reverse_append]

/-- A suffix offset identifies its occurrence regardless of the prefix. -/
theorem selectOffset_suffix (pre tail : List PropFormulaNormalized)
    (A : PropFormulaNormalized) :
    selectOffset tail.length (pre ++ A :: tail) = some (A, pre.length) := by
  simp [selectOffset, List.length_append]

/-- A scheduled variable contributes no inference step. -/
theorem expandScheduled_var {s : Sequent} (side : Bool) (offset i n : Nat)
    (h : selectOffset offset (if side then s.succedent else s.antecedent) =
      some (.var n, i)) :
    expandScheduled mode side offset s = .leaf s := by
  cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  all_goals
    unfold expandScheduled
    split
    · rfl
    · simp only [Bool.false_eq_true, ↓reduceIte]
      unfold expandSelected
      dsimp only []
      split
      · next A j hj =>
        have he := Option.some.inj (h.symm.trans hj)
        cases he
        rfl
      · rfl

/-- A block of original variables is skipped without changing the tree.
    The already visited prefix remains in the current sequent. -/
theorem expandSchedule_skip_atomic_prefix (s : Sequent) (side : Bool)
    (done pre tail : List PropFormulaNormalized) (rest : List (Bool × Nat))
    (hs : (if side then s.succedent else s.antecedent) = done ++ pre ++ tail)
    (hat : ∀ A ∈ pre, isAtomicFormula A) :
    expandSchedule mode (suffixSchedule side (pre.length + tail.length) ++ rest) (.leaf s) =
      expandSchedule mode (suffixSchedule side tail.length ++ rest) (.leaf s) := by
  induction pre generalizing done with
  | nil => simp
  | cons A pre ih =>
    have hA := hat A (by simp)
    cases A with
    | var n =>
      have hselect : selectOffset (pre.length + tail.length)
          (if side then s.succedent else s.antecedent) = some (.var n, done.length) := by
        rw [hs]
        simpa [List.append_assoc] using selectOffset_suffix done (pre ++ tail) (.var n)
      have hstep := expandScheduled_var (mode := mode) side _ _ _ hselect
      rw [show (PropFormulaNormalized.var n :: pre).length + tail.length =
        (pre.length + tail.length) + 1 from by simp; omega, suffixSchedule_succ]
      simp only [List.cons_append, expandSchedule, List.foldl_cons, mapLeaves, hstep]
      exact ih (done ++ [.var n]) (by simpa [List.append_assoc] using hs)
        (fun B hB => hat B (by simp [hB]))
    | neg _ => simp [isAtomicFormula] at hA
    | conj _ _ => simp [isAtomicFormula] at hA
    | disj _ _ => simp [isAtomicFormula] at hA
    | impl _ _ => simp [isAtomicFormula] at hA

/-- The first nonatomic selector's preceding occurrences are variables. -/
theorem findFirstNonatomic_atomic_prefix (L : List PropFormulaNormalized) (k : Nat)
    (A : PropFormulaNormalized) (i : Nat)
    (h : findFirstNonatomic L k = some (A, i)) :
    ∀ B ∈ L.take (i - k), isAtomicFormula B := by
  induction L generalizing k with
  | nil => simp [findFirstNonatomic] at h
  | cons C cs ih =>
    simp only [findFirstNonatomic] at h
    split at h
    · obtain ⟨rfl, rfl⟩ := Option.some.inj h
      simp
    · next hc =>
      have hbound := (findFirstNonatomic_spec_aux cs (k + 1) A i h).1
      have hi : i - k = (i - (k + 1)) + 1 := by omega
      rw [hi, List.take_succ_cons]
      intro B hB
      rcases List.mem_cons.mp hB with rfl | hB
      · cases B <;> simp_all [isNonatomicBool, isAtomicFormula]
      · exact ih (k + 1) h B hB

/-- Finished leaves remain unchanged for any frozen schedule. -/
theorem expandSchedule_finished (s : Sequent) (schedule : List (Bool × Nat))
    (h : isFinishedLeafBool mode s = true) :
    expandSchedule mode schedule (.leaf s) = .leaf s := by
  induction schedule with
  | nil => rfl
  | cons entry rest ih =>
    simpa only [expandSchedule, List.foldl_cons, mapLeaves, expandScheduled, h,
      ↓reduceIte] using ih

/-- The first antecedent occurrence is the first effective scheduled rule. -/
theorem expandFirstFormula_eq_scheduled_ante (s : Sequent)
    (hunf : ¬isFinishedLeafBool mode s = true) (A : PropFormulaNormalized) (i : Nat)
    (h : findFirstNonatomic s.antecedent = some (A, i)) :
    expandFirstFormula s = expandScheduled mode false
      (s.antecedent.length - (i + 1)) s := by
  have ⟨hi, hget, _⟩ := findFirstNonatomic_spec _ _ _ h
  have hsel : selectOffset (s.antecedent.length - (i + 1)) s.antecedent = some (A, i) := by
    simp only [selectOffset]
    rw [show s.antecedent.length - (s.antecedent.length - (i + 1) + 1) = i by omega, hget]
    rfl
  unfold expandFirstFormula expandScheduled
  simp only [hunf, Bool.false_eq_true, ↓reduceIte]
  unfold expandSelected
  split
  · next B j hB =>
    obtain ⟨hAB, hij⟩ := Prod.mk.inj (Option.some.inj (h.symm.trans hB))
    subst B; subst j
    cases A <;> dsimp only [] <;> split
    all_goals first
      | next C k hC =>
        obtain ⟨hAC, hik⟩ := Prod.mk.inj (Option.some.inj (hsel.symm.trans hC))
        subst C; subst k
        rfl
      | next hnone => simp [hnone] at hsel
  · next hnone => simp [hnone] at h

/-- The first succedent occurrence is the first effective scheduled rule
    when every original antecedent occurrence is atomic. -/
theorem expandFirstFormula_eq_scheduled_succ (s : Sequent)
    (hunf : ¬isFinishedLeafBool mode s = true)
    (hant : findFirstNonatomic s.antecedent = none)
    (A : PropFormulaNormalized) (i : Nat)
    (h : findFirstNonatomic s.succedent = some (A, i)) :
    expandFirstFormula s = expandScheduled mode true
      (s.succedent.length - (i + 1)) s := by
  have ⟨hi, hget, _⟩ := findFirstNonatomic_spec _ _ _ h
  have hsel : selectOffset (s.succedent.length - (i + 1)) s.succedent = some (A, i) := by
    simp only [selectOffset]
    rw [show s.succedent.length - (s.succedent.length - (i + 1) + 1) = i by omega, hget]
    rfl
  unfold expandFirstFormula expandScheduled
  simp only [hunf, Bool.false_eq_true, ↓reduceIte]
  unfold expandSelected
  split
  · next B j hB => simp [hant] at hB
  · dsimp only []
    split
    · next B j hB =>
      obtain ⟨hAB, hij⟩ := Prod.mk.inj (Option.some.inj (h.symm.trans hB))
      subst B; subst j
      cases A <;> dsimp only [] <;> split
      all_goals first
        | next C k hC =>
          obtain ⟨hAC, hik⟩ := Prod.mk.inj (Option.some.inj (hsel.symm.trans hC))
          subst C; subst k
          rfl
        | next hnone => simp [hnone] at hsel
    · next hnone => simp [hnone] at h

/-- The implementation is exactly the two frozen occurrence loops in
    Definition 3.4.6. Skipping an initial block of variables only removes
    iterations that leave the tree unchanged. -/
theorem expandLeaf_eq_full_schedule (s : Sequent) :
    expandLeaf mode s =
      expandSchedule mode (suffixSchedule false s.antecedent.length ++
        suffixSchedule true s.succedent.length) (.leaf s) := by
  by_cases hfin : isFinishedLeafBool mode s = true
  · rw [expandLeaf_of_finished s hfin, expandSchedule_finished s _ hfin]
  · unfold expandLeaf
    simp only [hfin, Bool.false_eq_true, ↓reduceIte]
    cases hant : findFirstNonatomic s.antecedent with
    | some pair =>
      obtain ⟨A, i⟩ := pair
      have hsplit := findFirstNonatomic_split _ _ _ hant
      have hat : ∀ B ∈ s.antecedent.take i, isAtomicFormula B := by
        simpa using findFirstNonatomic_atomic_prefix s.antecedent 0 A i hant
      have hskip := expandSchedule_skip_atomic_prefix (mode := mode) s false []
        (s.antecedent.take i) (A :: s.antecedent.drop (i + 1))
        (suffixSchedule true s.succedent.length)
        (by simpa [List.append_assoc] using hsplit) hat
      have hlen : (s.antecedent.take i).length +
          (A :: s.antecedent.drop (i + 1)).length = s.antecedent.length := by
        have := congrArg List.length hsplit
        simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
        omega
      rw [hlen] at hskip
      rw [hskip]
      simp only [List.length_cons, List.length_drop, suffixSchedule_succ,
        List.cons_append, expandSchedule, List.foldl_cons, mapLeaves]
      rw [← expandFirstFormula_eq_scheduled_ante s hfin A i hant]
    | none =>
      have hat := findFirstNonatomic_none_all_atomic _ _ hant
      have hskip := expandSchedule_skip_atomic_prefix (mode := mode) s false []
        s.antecedent [] (suffixSchedule true s.succedent.length) (by simp) hat
      have hskipAnt : expandSchedule mode
          (suffixSchedule false s.antecedent.length ++ suffixSchedule true s.succedent.length)
          (.leaf s) = expandSchedule mode (suffixSchedule true s.succedent.length) (.leaf s) := by
        simpa [suffixSchedule] using hskip
      rw [hskipAnt]
      cases hsucc : findFirstNonatomic s.succedent with
      | none =>
        exfalso
        apply hfin
        apply (isFinishedLeafBool_iff s).mpr
        right
        intro A hA
        rcases List.mem_append.mp hA with hA | hA
        · exact hat A hA
        · exact findFirstNonatomic_none_all_atomic _ _ hsucc A hA
      | some pair =>
        obtain ⟨A, i⟩ := pair
        have hsplit := findFirstNonatomic_split _ _ _ hsucc
        have hpre : ∀ B ∈ s.succedent.take i, isAtomicFormula B := by
          simpa using findFirstNonatomic_atomic_prefix s.succedent 0 A i hsucc
        have hskip := expandSchedule_skip_atomic_prefix (mode := mode) s true []
          (s.succedent.take i) (A :: s.succedent.drop (i + 1)) []
          (by simpa [List.append_assoc] using hsplit) hpre
        have hlen : (s.succedent.take i).length +
            (A :: s.succedent.drop (i + 1)).length = s.succedent.length := by
          have := congrArg List.length hsplit
          simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
          omega
        rw [hlen] at hskip
        simp only [List.append_nil] at hskip
        rw [hskip]
        simp only [List.length_cons, List.length_drop, suffixSchedule_succ,
          expandSchedule, List.foldl_cons, mapLeaves]
        rw [← expandFirstFormula_eq_scheduled_succ s hfin hant A i hsucc]

end LCS.Propositional.Systems.G.Search
end
