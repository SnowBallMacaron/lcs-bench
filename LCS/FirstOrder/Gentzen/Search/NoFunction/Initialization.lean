import LCS.Item
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Gentzen.Search.NoFunction.SearchState
import Attach
import LCS.FirstOrder.Gentzen.Search.NoFunction.Initialization.ProofsStamp

/-! # Initialization of TERM₀ and AVAIL₀ (Section 5.4.7)

TERM₀ lists the free variables and constants of the input sequent, or the first
absent variable y₀; AVAIL₀ lists variables not occurring in the input.
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

namespace SearchState

/-- Definition 5.4.9 (companion): Start at the first position of the
    supplied availability stream with matching TERM₀ and TERM₁. -/
@[blueprint "chap5__definition_5_4_9"]
def init {L : Language} {seq : Sequent L} (initial : Init seq) :
    SearchState L initial.avail0 :=
  { TERM0 := initial.term0, TERM1 := initial.term0, availNext := 0 }

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

end LCS.FirstOrder.Gentzen.Search.NoFunction
end
