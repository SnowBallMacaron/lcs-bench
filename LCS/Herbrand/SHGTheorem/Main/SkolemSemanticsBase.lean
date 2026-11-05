import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.SHGTheorem.Herbrand

section
namespace LCS.Herbrand.SHGTheorem.Main
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.SHGTheorem.Herbrand
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.CutElim.Hauptsatz
open LCS.FirstOrder.SemanticsN.Substitution

/-- Substitution preserves the NNF property for FormulaN: replacing a
variable by a term in an NNF formula produces an NNF formula. -/
theorem formulaSubstN_isNNF {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) :
    A.isNNF → (formulaSubstN A t x).isNNF := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => intro h; simp [formulaSubstN]; exact h
  | eq_ _ _ => intro h; simp [formulaSubstN]; exact h
  | neg B _ =>
    intro h; simp [formulaSubstN]
    cases B with
    | predN _ _ => simp [formulaSubstN]; exact h
    | eq_ _ _ => simp [formulaSubstN]; exact h
    | _ => exact absurd h id
  | conj A B ihA ihB =>
    intro ⟨hA, hB⟩; simp [formulaSubstN]; exact ⟨ihA hA, ihB hB⟩
  | disj A B ihA ihB =>
    intro ⟨hA, hB⟩; simp [formulaSubstN]; exact ⟨ihA hA, ihB hB⟩
  | impl _ _ _ _ => intro h; exact absurd h id
  | all y B ihB =>
    intro h; simp [formulaSubstN]; split; exact h; exact ihB h
  | ex y B ihB =>
    intro h; simp [formulaSubstN]; split; exact h; exact ihB h

-- ===================================================================
-- Lemma 7.6.3 (companion def): isExpansion
-- ===================================================================

/-- Lemma 7.6.3 (companion def): Predicate asserting that a structure N in a Skolem-extended language expands a structure M in the base language L: N has the same carrier as M, and N's interpretations of the original function, constant, and predicate symbols agree with M's interpretations. -/
def isExpansion (L : Language)
    (n : Nat) (skolemRank : Fin n → Nat)
    (M : Structure L)
    (N : Structure (SkolemLanguage (L := L) n skolemRank)) :
    Prop :=
  ∃ (heq : M.carrier = N.carrier),
    (∀ (f : L.funSymbols)
      (args : Fin (L.funArity f) → N.carrier),
      N.interpFunc (Sum.inl f) args =
        heq ▸ M.interpFunc f (fun i => heq ▸ args i)) ∧
    (∀ (c : L.constSymbols),
      N.interpConst (Sum.inl c) = heq ▸ M.interpConst c) ∧
    (∀ (P : L.predSymbols)
      (args : Fin (L.predArity P) → N.carrier),
      N.interpPred P args ↔
        M.interpPred P (fun i => heq ▸ args i))

-- ===================================================================
-- Lemma 7.6.3 (companion def): skolemFormCounterMap
-- ===================================================================

/-- Stub helper kept for API shape compatibility. The Skolem-to-existential
   correspondence is carried structurally by `SkolemSpec.allocations` and
`witnessSelectingExpansion`'s `skolemMapping` parameter; this stub returns
the empty list. Untagged because it has no live callers and its body does
not compute Lem 7.6.3's companion mapping. -/
def skolemFormCounterMap {L : Language}
    (_A : FormulaN L)
    (_scopeLookup : FormulaN L → List Nat)
    (_symbolLookup : Nat → L.funSymbols)
    (_counter : Nat) : List (Nat × Nat × FormulaN L) :=
  []

-- ===================================================================
-- Lemma 7.6.3 (companion def): witnessSelectingExpansion
-- ===================================================================

/-- Lemma 7.6.3: Extend M while preserving each original symbol through
its base-language injection. At the original index i, choose a witness for
skolemMapping i under the assignment given by the ordered scopeVarMap i.
Positive ranks use functions; rank-zero indices use constants with the unique
empty argument vector. If no witness exists, use an arbitrary carrier element. -/
noncomputable def witnessSelectingExpansion {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat}
    (M : Structure L)
    (skolemMapping : (i : Fin n) → (Nat × FormulaN L))
    (scopeVarMap : (i : Fin n) → (Fin (skolemRank i) → Nat))
    : Structure (SkolemLanguage (L := L) n skolemRank) :=
  haveI : ∀ (P : Prop), Decidable P := Classical.propDecidable
  let selectWitness (i : Fin n) (args : Fin (skolemRank i) → M.carrier) :=
    let (x, D) := skolemMapping i
    let sArgs : Assignment M := fun v =>
      if h : ∃ j : Fin (skolemRank i), scopeVarMap i j = v
      then args (Classical.choose h)
      else Classical.choice M.carrierNonempty
    if h : ∃ d, formulaEvalN M D (assignUpdate sArgs x d)
    then Classical.choose h
    else Classical.choice M.carrierNonempty
  { carrier := M.carrier
    carrierNonempty := M.carrierNonempty
    interpFunc := fun fsym args =>
      match fsym with
      | Sum.inl f => M.interpFunc f args
      | Sum.inr i => selectWitness i.val args
    interpConst := fun
      | Sum.inl c => M.interpConst c
      | Sum.inr i => selectWitness i.val
          (fun j => Fin.elim0 (Fin.cast i.property j))
    interpPred := fun P args => M.interpPred P args }

/-- Lemma 7.6.3 (companion theorem): witnessSelectingExpansion is indeed an expansion of M: same carrier (rfl), same interpretation of original function symbols (Sum.inl), constants, and predicates. -/
theorem witnessSelectingExpansion_isExpansion {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat}
    (M : Structure L)
    (skolemMapping : (i : Fin n) → (Nat × FormulaN L))
    (scopeVarMap : (i : Fin n) → (Fin (skolemRank i) → Nat))
    : isExpansion L n skolemRank M
        (witnessSelectingExpansion M skolemMapping scopeVarMap) :=
-- BEGIN PROOF
  ⟨rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => Iff.rfl⟩

-- ===================================================================
-- Lemma 7.6.3 (transport helpers)
-- ===================================================================

/-- Double transport cancellation: transporting forward then backward
is the identity. Uses subst on free type variables. -/
theorem transport_back_forth {α β : Type} (h : α = β) (v : α) :
    (h ▸ (h ▸ v : β) : α) = v := by
-- BEGIN PROOF
  subst h; rfl

/-- Transport commutes with assignUpdate: updating a transported
assignment with a transported value equals transporting the updated
assignment pointwise. -/
theorem transport_assignUpdate {L L' : Language}
    {M : Structure L} {N : Structure L'}
    (h : M.carrier = N.carrier)
    (s : Assignment M) (x : Nat) (a : M.carrier) :
    assignUpdate (fun y => (h ▸ s y : N.carrier)) x (h ▸ a) =
    (fun y => (h ▸ assignUpdate s x a y : N.carrier)) := by
-- BEGIN PROOF
  funext y; simp only [assignUpdate]; split <;> rfl

/-- Universal quantifier transport across an equality of types. -/
theorem forall_transport {α β : Type} (h : α = β)
    (P : α → Prop) (Q : β → Prop)
    (hPQ : ∀ v : α, P v ↔ Q (h ▸ v)) :
    (∀ a : α, P a) ↔ (∀ a : β, Q a) := by
-- BEGIN PROOF
  subst h; exact forall_congr' hPQ

/-- Existential quantifier transport across an equality of types. -/
theorem exists_transport {α β : Type} (h : α = β)
    (P : α → Prop) (Q : β → Prop)
    (hPQ : ∀ v : α, P v ↔ Q (h ▸ v)) :
    (∃ a : α, P a) ↔ (∃ a : β, Q a) := by
-- BEGIN PROOF
  subst h; exact exists_congr hPQ

/-- Transport preserves equality between elements. -/
theorem transport_eq_iff {α β : Type} (h : α = β) (x y : α) :
    x = y ↔ (h ▸ x : β) = (h ▸ y : β) := by
-- BEGIN PROOF
  subst h; exact Iff.rfl

-- ===================================================================
-- Lemma 7.6.3 (companion helper): liftTermSkolem_eval
-- ===================================================================

/-- Helper for liftFormulaSkolem_eval_iff: evaluating a lifted term in
the expansion N equals the transported evaluation in M. -/
theorem liftTermSkolem_eval {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat}
    (M : Structure L)
    (N : Structure (SkolemLanguage (L := L) n skolemRank))
    (heq : M.carrier = N.carrier)
    (hFunc : ∀ (f : L.funSymbols)
      (args : Fin (L.funArity f) → N.carrier),
      N.interpFunc (Sum.inl f) args =
        heq ▸ M.interpFunc f (fun i => heq ▸ args i))
    (hConst : ∀ (c : L.constSymbols),
      N.interpConst (Sum.inl c) = heq ▸ M.interpConst c)
    (s : Assignment M) (t : Term L) :
    termEval N (fun x => heq ▸ s x) (liftTermSkolem t) =
      heq ▸ termEval M s t := by
-- BEGIN PROOF
  induction t with
  | var x => simp [liftTermSkolem, termEval]
  | const c =>
    simp only [liftTermSkolem, termEval]
    exact hConst c
  | func f ts ih =>
    simp only [liftTermSkolem, termEval]
    -- Goal: heq ▸ M.interpFunc f (fun i => heq ▸ termEval N sN (liftTermSkolem (ts i)))
    --     = heq ▸ M.interpFunc f (fun i => termEval M s (ts i))
    -- By IH: termEval N sN (liftTermSkolem (ts i)) = heq ▸ termEval M s (ts i)
    -- So heq ▸ that = heq ▸ (heq ▸ v) = v by transport_back_forth
    have hargs : (fun i => heq ▸ termEval N (fun x => heq ▸ s x)
        (liftTermSkolem (ts i))) =
      (fun i => termEval M s (ts i)) :=
      funext fun i => by rw [ih i]; exact transport_back_forth heq _
    exact (hFunc f _).trans
      (congrArg (heq ▸ ·) (congrArg (M.interpFunc f) hargs))

-- ===================================================================
-- Lemma 7.6.3 (companion theorem): liftFormulaSkolem_eval_iff
-- ===================================================================

/-- Lemma 7.6.3 (companion theorem): The evaluation bridge between the base language and the Skolem-extended language. When N is an expansion of M (same carrier, same interpretations on original symbols), evaluating a lifted L-formula in N gives the same truth value as evaluating the original formula in M. This bridges the gap between skolemForm_backward_genN (which works within a single language) and skolem_form_backward (which works across L and SkolemLanguage). -/
theorem liftFormulaSkolem_eval_iff {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat}
    (M : Structure L)
    (N : Structure (SkolemLanguage (L := L) n skolemRank))
    (hExp : isExpansion L n skolemRank M N)
    (s : Assignment M) (A : FormulaN L) :
    formulaEvalN M A s ↔
      formulaEvalN N
        (liftFormulaSkolem A)
        (fun x => (hExp.choose ▸ s x : N.carrier)) := by
-- BEGIN PROOF
  obtain ⟨heq, hFunc, hConst, hPred⟩ := hExp
  induction A generalizing s with
  | predN P ts =>
    simp only [liftFormulaSkolem, formulaEvalN]
    have hterm : ∀ i, termEval N (fun x => heq ▸ s x) (liftTermSkolem (ts i)) =
        heq ▸ termEval M s (ts i) :=
      fun i => liftTermSkolem_eval M N heq hFunc hConst s (ts i)
    have hargs_eq : (fun i => heq ▸ termEval N (fun x => heq ▸ s x)
        (liftTermSkolem (ts i))) = (fun i => termEval M s (ts i)) :=
      funext fun i => by rw [hterm i]; exact transport_back_forth heq _
    have hPredEval := hPred P
      (fun i => termEval N (fun x => heq ▸ s x) (liftTermSkolem (ts i)))
    rw [hargs_eq] at hPredEval
    exact hPredEval.symm
  | eq_ _h t1 t2 =>
    simp only [liftFormulaSkolem, formulaEvalN]
    have h1 := liftTermSkolem_eval M N heq hFunc hConst s t1
    have h2 := liftTermSkolem_eval M N heq hFunc hConst s t2
    rw [h1, h2]
    exact transport_eq_iff heq (termEval M s t1) (termEval M s t2)
  | neg A ih =>
    simp only [liftFormulaSkolem, formulaEvalN]
    exact not_congr (ih s)
  | conj A B ihA ihB =>
    simp only [liftFormulaSkolem, formulaEvalN]
    exact and_congr (ihA s) (ihB s)
  | disj A B ihA ihB =>
    simp only [liftFormulaSkolem, formulaEvalN]
    exact or_congr (ihA s) (ihB s)
  | impl A B ihA ihB =>
    simp only [liftFormulaSkolem, formulaEvalN]
    exact imp_congr (ihA s) (ihB s)
  | all x A ih =>
    simp only [liftFormulaSkolem, formulaEvalN]
    apply forall_transport heq
    intro a
    rw [transport_assignUpdate heq s x a]
    exact ih (assignUpdate s x a)
  | ex x A ih =>
    simp only [liftFormulaSkolem, formulaEvalN]
    apply exists_transport heq
    intro a
    rw [transport_assignUpdate heq s x a]
    exact ih (assignUpdate s x a)

-- ===================================================================
-- Lemma 7.6.3 (exact-traversal semantic invariant)
-- ===================================================================

/-- A successful, allocation-aligned exact traversal reflects truth.
The scope side condition is the capture invariant: variables used as
arguments of the next exact Skolem term are not rebound in the current
formula. -/
private theorem skolemFormExactAux_forward_semantics {L : Language}
    (S : SkolemSpec L) (N : Structure S.language) :
    ∀ (m : Nat) (A : FormulaN S.language) (scope : List Nat)
      (indices : List (Fin S.n)) (B : FormulaN S.language) (used : Nat),
      formulaQuantCount A = m →
      FormulaN.isNNF A →
      indices.length = skolemDescriptorCount A →
      indices.map S.skolemScope = existentialScopesAux A scope →
      skolemFormExactAux S A scope indices = some (B, used) →
      distinctQuantifierBindings A →
      (∀ y ∈ scope, y ∉ formulaBVN A) →
      ∀ s : Assignment N,
        formulaEvalN N B s → formulaEvalN N A s := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro A scope indices Out used hCount hNNF hLength hScopes hRun
      hDistinct hScopeFresh s hOut
    match A, hCount, hNNF, hLength, hDistinct with
    | .predN P ts, _, _, hLength, _ =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.predN P ts) scope [] =
            some (.predN P ts, 0) := by
        simp [skolemFormExactAux]
      have hFormula :=
        skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact hOut
    | .eq_ h t₁ t₂, _, _, hLength, _ =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.eq_ h t₁ t₂) scope [] =
            some (.eq_ h t₁ t₂, 0) := by
        simp [skolemFormExactAux]
      have hFormula :=
        skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact hOut
    | .neg C, _, hNNF, hLength, _ =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      have hCanonical :
          skolemFormExactAux S (.neg C) scope [] =
            some (.neg C, 0) := by
        simp [skolemFormExactAux]
      have hFormula :=
        skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact hOut
    | .conj C D, hCount, hNNF, hLength, hDistinct =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qC : formulaQuantCount C < m := by omega
      have qD : formulaQuantCount D < m := by omega
      have hCLe : skolemDescriptorCount C ≤ indices.length := by
        rw [hLength]
        exact Nat.le_add_right _ _
      have hLeftLength :
          (indices.take (skolemDescriptorCount C)).length =
            skolemDescriptorCount C :=
        List.length_take_of_le hCLe
      have hRightLength :
          (indices.drop (skolemDescriptorCount C)).length =
            skolemDescriptorCount D := by
        rw [List.length_drop, hLength]
        simp [skolemDescriptorCount]
      have hLeftScopes :
          (indices.take (skolemDescriptorCount C)).map S.skolemScope =
            existentialScopesAux C scope := by
        calc
          _ = (indices.map S.skolemScope).take
                (skolemDescriptorCount C) := List.map_take
          _ = (existentialScopesAux C scope ++
                existentialScopesAux D scope).take
                (skolemDescriptorCount C) := by
              rw [hScopes]
              rfl
          _ = existentialScopesAux C scope := by
              rw [← existentialScopesAux_length C scope]
              exact List.take_left
      have hRightScopes :
          (indices.drop (skolemDescriptorCount C)).map S.skolemScope =
            existentialScopesAux D scope := by
        calc
          _ = (indices.map S.skolemScope).drop
                (skolemDescriptorCount C) := List.map_drop
          _ = (existentialScopesAux C scope ++
                existentialScopesAux D scope).drop
                (skolemDescriptorCount C) := by
              rw [hScopes]
              rfl
          _ = existentialScopesAux D scope := by
              rw [← existentialScopesAux_length C scope]
              exact List.drop_left
      obtain ⟨C', hC'⟩ :=
        skolemFormExactAux_result S _ C scope
          (indices.take (skolemDescriptorCount C)) rfl hLeftLength
      obtain ⟨D', hD'⟩ :=
        skolemFormExactAux_result S _ D scope
          (indices.drop (skolemDescriptorCount C)) rfl hRightLength
      have hFreshC : ∀ y ∈ scope, y ∉ formulaBVN C := by
        intro y hyScope hyBound
        exact hScopeFresh y hyScope (Or.inl hyBound)
      have hFreshD : ∀ y ∈ scope, y ∉ formulaBVN D := by
        intro y hyScope hyBound
        exact hScopeFresh y hyScope (Or.inr hyBound)
      have hSemC :=
        ih _ qC C scope (indices.take (skolemDescriptorCount C))
          C' _ rfl hNNF.1 hLeftLength hLeftScopes hC'
          hDistinct.1 hFreshC
      have hSemD :=
        ih _ qD D scope (indices.drop (skolemDescriptorCount C))
          D' _ rfl hNNF.2 hRightLength hRightScopes hD'
          hDistinct.2.1 hFreshD
      have hCanonical :
          skolemFormExactAux S (.conj C D) scope indices =
            some (.conj C' D',
              skolemDescriptorCount C + skolemDescriptorCount D) := by
        simp [skolemFormExactAux, hC', hD']
      have hFormula :=
        skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      exact ⟨hSemC s hOut.1, hSemD s hOut.2⟩
    | .disj C D, hCount, hNNF, hLength, hDistinct =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qC : formulaQuantCount C < m := by omega
      have qD : formulaQuantCount D < m := by omega
      have hCLe : skolemDescriptorCount C ≤ indices.length := by
        rw [hLength]
        exact Nat.le_add_right _ _
      have hLeftLength :
          (indices.take (skolemDescriptorCount C)).length =
            skolemDescriptorCount C :=
        List.length_take_of_le hCLe
      have hRightLength :
          (indices.drop (skolemDescriptorCount C)).length =
            skolemDescriptorCount D := by
        rw [List.length_drop, hLength]
        simp [skolemDescriptorCount]
      have hLeftScopes :
          (indices.take (skolemDescriptorCount C)).map S.skolemScope =
            existentialScopesAux C scope := by
        calc
          _ = (indices.map S.skolemScope).take
                (skolemDescriptorCount C) := List.map_take
          _ = (existentialScopesAux C scope ++
                existentialScopesAux D scope).take
                (skolemDescriptorCount C) := by
              rw [hScopes]
              rfl
          _ = existentialScopesAux C scope := by
              rw [← existentialScopesAux_length C scope]
              exact List.take_left
      have hRightScopes :
          (indices.drop (skolemDescriptorCount C)).map S.skolemScope =
            existentialScopesAux D scope := by
        calc
          _ = (indices.map S.skolemScope).drop
                (skolemDescriptorCount C) := List.map_drop
          _ = (existentialScopesAux C scope ++
                existentialScopesAux D scope).drop
                (skolemDescriptorCount C) := by
              rw [hScopes]
              rfl
          _ = existentialScopesAux D scope := by
              rw [← existentialScopesAux_length C scope]
              exact List.drop_left
      obtain ⟨C', hC'⟩ :=
        skolemFormExactAux_result S _ C scope
          (indices.take (skolemDescriptorCount C)) rfl hLeftLength
      obtain ⟨D', hD'⟩ :=
        skolemFormExactAux_result S _ D scope
          (indices.drop (skolemDescriptorCount C)) rfl hRightLength
      have hFreshC : ∀ y ∈ scope, y ∉ formulaBVN C := by
        intro y hyScope hyBound
        exact hScopeFresh y hyScope (Or.inl hyBound)
      have hFreshD : ∀ y ∈ scope, y ∉ formulaBVN D := by
        intro y hyScope hyBound
        exact hScopeFresh y hyScope (Or.inr hyBound)
      have hSemC :=
        ih _ qC C scope (indices.take (skolemDescriptorCount C))
          C' _ rfl hNNF.1 hLeftLength hLeftScopes hC'
          hDistinct.1 hFreshC
      have hSemD :=
        ih _ qD D scope (indices.drop (skolemDescriptorCount C))
          D' _ rfl hNNF.2 hRightLength hRightScopes hD'
          hDistinct.2.1 hFreshD
      have hCanonical :
          skolemFormExactAux S (.disj C D) scope indices =
            some (.disj C' D',
              skolemDescriptorCount C + skolemDescriptorCount D) := by
        simp [skolemFormExactAux, hC', hD']
      have hFormula :=
        skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      rcases hOut with hOut | hOut
      · exact Or.inl (hSemC s hOut)
      · exact Or.inr (hSemD s hOut)
    | .impl _ _, _, hNNF, _, _ => exact hNNF.elim
    | .all x C, hCount, hNNF, hLength, hDistinct =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      have qC : formulaQuantCount C < m := by omega
      have hBodyLength :
          indices.length = skolemDescriptorCount C := by
        simpa [skolemDescriptorCount] using hLength
      have hBodyScopes :
          indices.map S.skolemScope =
            existentialScopesAux C (scope ++ [x]) := by
        simpa [existentialScopesAux] using hScopes
      obtain ⟨C', hC'⟩ :=
        skolemFormExactAux_result S _ C (scope ++ [x])
          indices rfl hBodyLength
      have hFreshC :
          ∀ y ∈ scope ++ [x], y ∉ formulaBVN C := by
        intro y hyScope hyBound
        rcases List.mem_append.mp hyScope with hyScope | hyLast
        · exact hScopeFresh y hyScope (Or.inl hyBound)
        · have hyx : y = x := List.mem_singleton.mp hyLast
          subst y
          exact hDistinct.2 hyBound
      have hSemC :=
        ih _ qC C (scope ++ [x]) indices C' _
          rfl hNNF hBodyLength hBodyScopes hC'
          hDistinct.1 hFreshC
      have hCanonical :
          skolemFormExactAux S (.all x C) scope indices =
            some (.all x C', skolemDescriptorCount C) := by
        simp [skolemFormExactAux, hC']
      have hFormula :=
        skolemFormExactAux_formula_unique hCanonical hRun
      subst Out
      intro a
      exact hSemC (assignUpdate s x a) (hOut a)
    | .ex x C, hCount, hNNF, hLength, hDistinct =>
      have hCountAt := hCount
      simp [formulaQuantCount] at hCountAt
      cases indices with
      | nil =>
        simp [skolemDescriptorCount] at hLength
        omega
      | cons i rest =>
        have hRestLength :
            rest.length = skolemDescriptorCount C := by
          simp [skolemDescriptorCount] at hLength
          omega
        have hScopesAt := hScopes
        simp only [List.map_cons, existentialScopesAux] at hScopesAt
        have hHeadScope : S.skolemScope i = scope :=
          (List.cons.inj hScopesAt).1
        have hRestScopes :
            rest.map S.skolemScope = existentialScopesAux C scope :=
          (List.cons.inj hScopesAt).2
        let CSub := formulaSubstN C (exactSkolemTerm S i) x
        have qCSub : formulaQuantCount CSub < m := by
          simp only [CSub]
          rw [formulaSubst_quantCount]
          omega
        have hNNFSub : FormulaN.isNNF CSub :=
          formulaSubstN_isNNF C (exactSkolemTerm S i) x hNNF
        have hSubLength :
            rest.length = skolemDescriptorCount CSub := by
          rw [formulaSubstN_descriptorCount]
          exact hRestLength
        have hSubScopes :
            rest.map S.skolemScope =
              existentialScopesAux CSub scope := by
          rw [existentialScopesAux_formulaSubstN]
          exact hRestScopes
        obtain ⟨C', hC'⟩ :=
          skolemFormExactAux_result S _ CSub scope rest rfl hSubLength
        have hDistinctSub : distinctQuantifierBindings CSub :=
          distinctQuantifierBindings_of_formulaSubstN
            C (exactSkolemTerm S i) x hDistinct.1
        have hFreshSub :
            ∀ y ∈ scope, y ∉ formulaBVN CSub := by
          intro y hyScope hyBound
          apply hScopeFresh y hyScope
          apply Or.inl
          have hyBoundC : formulaBVN C y := by
            change formulaBVN CSub y at hyBound
            simpa only [CSub,
              LCS.CutElim.Interpolation.formulaBV_formulaSubst] using hyBound
          exact hyBoundC
        have hFree : isFreeForN (exactSkolemTerm S i) x C := by
          apply LCS.FirstOrder.Gentzen.Hintikka.isFreeForN_of_bv_disjoint
          intro y hyTerm hyBound
          apply hScopeFresh y
          · rw [← hHeadScope]
            exact exactSkolemTerm_fv S i y hyTerm
          · exact Or.inl hyBound
        have hSemC :=
          ih _ qCSub CSub scope rest C' _
            rfl hNNFSub hSubLength hSubScopes hC'
            hDistinctSub hFreshSub
        have hCanonical :
            skolemFormExactAux S (.ex x C) scope (i :: rest) =
              some (C', skolemDescriptorCount CSub + 1) := by
          simp [skolemFormExactAux, skolemSubst, CSub, hC']
        have hFormula :=
          skolemFormExactAux_formula_unique hCanonical hRun
        subst Out
        have hEvalSub : formulaEvalN N CSub s := hSemC s hOut
        refine ⟨termEval N s (exactSkolemTerm S i), ?_⟩
        exact
          (formulaSubstEvalDirectN s C (exactSkolemTerm S i) x hFree).mp
            hEvalSub

-- ===================================================================
-- Lemma 7.6.3 (forward generalized): skolemForm_forward_genN
-- ===================================================================

/-- Lemma 7.6.3 forward (FormulaN version): if a Skolem-extended
structure N satisfies the Skolem form `SK spec`, then (transported back
via `liftFormulaSkolem_eval_iff`) the base structure satisfies
`spec.source`. The Skolem-form argument is fully packaged as
`spec : SkolemSpec L` (Def 7.6.2). -/
theorem skolemForm_forward_genN {L : Language}
    (spec : SkolemSpec L)
    (N : Structure spec.language) (_sN : Assignment N)
    (_h : formulaEvalN N (SK spec) _sN)
    (M : Structure L) (s : Assignment M)
    (_hExp : isExpansion L spec.n spec.skolemRank M N) :
    formulaEvalN M spec.source s := by
-- BEGIN PROOF
  unfold SkolemSpec.language at N
  let A :=
    liftFormulaSkolem (skolemRank := spec.skolemRank) spec.source
  have hNNF : FormulaN.isNNF A :=
    liftFormulaSkolem_isNNF spec.source spec.hNNF
  have hDistinct : distinctQuantifierBindings A := by
    simpa [A] using
      liftFormulaSkolem_distinctQuantifierBindings
        spec.source spec.hRect.2
  have hScopeFresh : ∀ y ∈ ([] : List Nat), y ∉ formulaBVN A := by
    intro y hy
    simp at hy
  have hRun :
      skolemFormExactAux spec A [] spec.indices =
        some (SK spec, spec.n) := by
    simpa [A] using skolemFormExactAux_top_formula_result spec
  have hLiftAtSN : formulaEvalN N A _sN :=
    skolemFormExactAux_forward_semantics spec N _ A [] spec.indices
      (SK spec) spec.n rfl hNNF
      spec.indices_length_eq_lifted_descriptorCount
      spec.indices_scopes_lifted hRun hDistinct hScopeFresh _sN _h
  have hClosedLift : formulaFVN A = (∅ : Set Nat) := by
    rw [show formulaFVN A = formulaFVN spec.source by
      simpa [A] using liftFormulaSkolem_formulaFVN spec.source]
    exact spec.hSentence
  have hLiftAtTransport :
      formulaEvalN N A
        (fun x => (_hExp.choose ▸ s x : N.carrier)) :=
    (coincidenceLemmaN N A _sN
      (fun x => (_hExp.choose ▸ s x : N.carrier))
      (fun y hy => by
        rw [hClosedLift] at hy
        exact hy.elim)).mp hLiftAtSN
  exact
    (liftFormulaSkolem_eval_iff M N _hExp s spec.source).mpr
      (by simpa [A] using hLiftAtTransport)

-- ===================================================================
-- Lemma 7.6.3 (contextual witness-selection infrastructure)
-- ===================================================================

/-- Interpretations of the exact finite family of Skolem symbols over
the carrier of a fixed base structure. -/
abbrev SkolemInterpretation {L : Language}
    (S : SkolemSpec L) (M : Structure L) :=
  (i : Fin S.n) →
    (Fin (S.skolemRank i) → M.carrier) → M.carrier

/-- Expansion determined by a complete interpretation of the exact
Skolem-symbol family. -/
noncomputable def interpretationExpansion {L : Language}
    (S : SkolemSpec L) (M : Structure L)
    (K : SkolemInterpretation S M) : Structure S.language :=
  { carrier := M.carrier
    carrierNonempty := M.carrierNonempty
    interpFunc := fun f args =>
      match f with
      | Sum.inl g => M.interpFunc g args
      | Sum.inr i => K i.val args
    interpConst := fun
      | Sum.inl c => M.interpConst c
      | Sum.inr i => K i.val (fun j => Fin.elim0 (Fin.cast i.property j))
    interpPred := M.interpPred }

theorem interpretationExpansion_isExpansion {L : Language}
    (S : SkolemSpec L) (M : Structure L)
    (K : SkolemInterpretation S M) :
    isExpansion L S.n S.skolemRank M
      (interpretationExpansion S M K) :=
  ⟨rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => Iff.rfl⟩

/-- Every Skolem constant or function head in a term belongs to `available`. -/
def skolemTermSupported {L : Language} (S : SkolemSpec L)
    (available : List (Fin S.n)) : Term S.language → Prop
  | .var _ => True
  | .const (Sum.inl _) => True
  | .const (Sum.inr i) => i.val ∈ available
  | .func (Sum.inl _) ts =>
      ∀ j, skolemTermSupported S available (ts j)
  | .func (Sum.inr i) ts =>
      i.val ∈ available ∧
      ∀ j, skolemTermSupported S available (ts j)

/-- Every Skolem head occurring in a formula belongs to `available`. -/
def skolemFormulaSupported {L : Language} (S : SkolemSpec L)
    (available : List (Fin S.n)) : FormulaN S.language → Prop
  | .predN _ ts =>
      ∀ j, skolemTermSupported S available (ts j)
  | .eq_ _ t₁ t₂ =>
      skolemTermSupported S available t₁ ∧
      skolemTermSupported S available t₂
  | .neg A => skolemFormulaSupported S available A
  | .conj A B =>
      skolemFormulaSupported S available A ∧
      skolemFormulaSupported S available B
  | .disj A B =>
      skolemFormulaSupported S available A ∧
      skolemFormulaSupported S available B
  | .impl A B =>
      skolemFormulaSupported S available A ∧
      skolemFormulaSupported S available B
  | .all _ A => skolemFormulaSupported S available A
  | .ex _ A => skolemFormulaSupported S available A

private theorem skolemTermSupported_mono {L : Language}
    (S : SkolemSpec L) {xs ys : List (Fin S.n)}
    (hSub : ∀ i, i ∈ xs → i ∈ ys) :
    ∀ t, skolemTermSupported S xs t →
      skolemTermSupported S ys t := by
  intro t
  induction t with
  | var _ => exact fun _ => trivial
  | const c =>
    cases c with
    | inl _ => exact fun _ => trivial
    | inr i => exact hSub i.val
  | func f ts ih =>
    cases f with
    | inl f =>
      intro h j
      exact ih j (h j)
    | inr i =>
      intro h
      exact ⟨hSub i.val h.1, fun j => ih j (h.2 j)⟩

theorem skolemFormulaSupported_mono {L : Language}
    (S : SkolemSpec L) {xs ys : List (Fin S.n)}
    (hSub : ∀ i, i ∈ xs → i ∈ ys) :
    ∀ A, skolemFormulaSupported S xs A →
      skolemFormulaSupported S ys A := by
  intro A
  induction A with
  | predN _ ts =>
    intro h j
    exact skolemTermSupported_mono S hSub (ts j) (h j)
  | eq_ _ t₁ t₂ =>
    intro h
    exact
      ⟨skolemTermSupported_mono S hSub t₁ h.1,
       skolemTermSupported_mono S hSub t₂ h.2⟩
  | neg A ih => exact ih
  | conj A B ihA ihB =>
    intro h
    exact ⟨ihA h.1, ihB h.2⟩
  | disj A B ihA ihB =>
    intro h
    exact ⟨ihA h.1, ihB h.2⟩
  | impl A B ihA ihB =>
    intro h
    exact ⟨ihA h.1, ihB h.2⟩
  | all _ A ih => exact ih
  | ex _ A ih => exact ih

private theorem liftTermSkolem_supported_nil {L : Language}
    (S : SkolemSpec L) :
    ∀ t : Term L,
      skolemTermSupported S [] (liftTermSkolem t) := by
  intro t
  induction t with
  | var _ => trivial
  | const _ => trivial
  | func _ ts ih =>
    exact fun j => ih j

theorem liftFormulaSkolem_supported_nil {L : Language}
    (S : SkolemSpec L) :
    ∀ A : FormulaN L,
      skolemFormulaSupported S [] (liftFormulaSkolem A) := by
  intro A
  induction A with
  | predN _ ts =>
    exact fun j => liftTermSkolem_supported_nil S (ts j)
  | eq_ _ t₁ t₂ =>
    exact
      ⟨liftTermSkolem_supported_nil S t₁,
       liftTermSkolem_supported_nil S t₂⟩
  | neg _ ih => exact ih
  | conj _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | disj _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | impl _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | all _ _ ih => exact ih
  | ex _ _ ih => exact ih

theorem exactSkolemTerm_supported {L : Language}
    (S : SkolemSpec L) (i : Fin S.n)
    (available : List (Fin S.n)) (hi : i ∈ available) :
    skolemTermSupported S available (exactSkolemTerm S i) := by
  unfold exactSkolemTerm
  split
  · exact hi
  · exact ⟨hi, fun _ => trivial⟩

private theorem termSubst_supported {L : Language}
    (S : SkolemSpec L) (available : List (Fin S.n)) :
    ∀ r t : Term S.language, skolemTermSupported S available r →
      skolemTermSupported S available t →
      ∀ x, skolemTermSupported S available (termSubst r t x) := by
  intro r
  induction r with
  | var y =>
    intro t _ ht x
    simp only [termSubst]
    split
    · exact ht
    · trivial
  | const c =>
    intro t hr _ x
    exact hr
  | func f ts ih =>
    intro t hr ht x
    cases f with
    | inl f =>
      intro j
      exact ih j t (hr j) ht x
    | inr i =>
      exact ⟨hr.1, fun j => ih j t (hr.2 j) ht x⟩

theorem formulaSubstN_supported {L : Language}
    (S : SkolemSpec L) (available : List (Fin S.n)) :
    ∀ A t x,
      skolemFormulaSupported S available A →
      skolemTermSupported S available t →
      skolemFormulaSupported S available (formulaSubstN A t x) := by
  intro A
  induction A with
  | predN P ts =>
    intro t x hA ht j
    exact termSubst_supported S available (ts j) t (hA j) ht x
  | eq_ h t₁ t₂ =>
    intro t x hA ht
    exact
      ⟨termSubst_supported S available t₁ t hA.1 ht x,
       termSubst_supported S available t₂ t hA.2 ht x⟩
  | neg A ih =>
    intro t x hA ht
    exact ih t x hA ht
  | conj A B ihA ihB =>
    intro t x hA ht
    exact ⟨ihA t x hA.1 ht, ihB t x hA.2 ht⟩
  | disj A B ihA ihB =>
    intro t x hA ht
    exact ⟨ihA t x hA.1 ht, ihB t x hA.2 ht⟩
  | impl A B ihA ihB =>
    intro t x hA ht
    exact ⟨ihA t x hA.1 ht, ihB t x hA.2 ht⟩
  | all y A ih =>
    intro t x hA ht
    simp only [formulaSubstN]
    split
    · exact ih t x hA ht
    · exact hA
  | ex y A ih =>
    intro t x hA ht
    simp only [formulaSubstN]
    split
    · exact ih t x hA ht
    · exact hA

/-- Pointwise agreement of two Skolem interpretations on a list of
allocated symbols. -/
def skolemInterpretationsAgreeOn {L : Language}
    (S : SkolemSpec L) (M : Structure L)
    (available : List (Fin S.n))
    (K K' : SkolemInterpretation S M) : Prop :=
  ∀ i, i ∈ available → ∀ args, K i args = K' i args

private theorem termEval_interpretationExpansion_eq {L : Language}
    (S : SkolemSpec L) (M : Structure L)
    (available : List (Fin S.n))
    (K K' : SkolemInterpretation S M)
    (hAgree : skolemInterpretationsAgreeOn S M available K K')
    (s : Nat → M.carrier) :
    ∀ t, skolemTermSupported S available t →
      termEval (interpretationExpansion S M K) s t =
        termEval (interpretationExpansion S M K') s t := by
  intro t
  induction t with
  | var _ => exact fun _ => rfl
  | const c =>
    cases c with
    | inl _ => exact fun _ => rfl
    | inr i => exact fun h => hAgree i.val h _
  | func f ts ih =>
    cases f with
    | inl f =>
      intro h
      simp only [termEval, interpretationExpansion]
      congr 1
      funext j
      exact ih j (h j)
    | inr i =>
      intro h
      simp only [termEval, interpretationExpansion]
      calc
        K i.val (fun j => termEval (interpretationExpansion S M K) s (ts j)) =
            K i.val (fun j => termEval (interpretationExpansion S M K') s (ts j)) := by
              congr 1
              funext j
              exact ih j (h.2 j)
        _ = K' i.val
            (fun j => termEval (interpretationExpansion S M K') s (ts j)) :=
              hAgree i.val h.1 _

theorem formulaEvalN_interpretationExpansion_iff {L : Language}
    (S : SkolemSpec L) (M : Structure L)
    (available : List (Fin S.n))
    (K K' : SkolemInterpretation S M)
    (hAgree : skolemInterpretationsAgreeOn S M available K K') :
    ∀ (A : FormulaN S.language),
      skolemFormulaSupported S available A →
      ∀ s : Nat → M.carrier,
        formulaEvalN (interpretationExpansion S M K) A s ↔
          formulaEvalN (interpretationExpansion S M K') A s := by
  intro A
  induction A with
  | predN P ts =>
    intro h s
    simp only [formulaEvalN]
    have hArgs :
        (fun j => termEval (interpretationExpansion S M K) s (ts j)) =
          (fun j => termEval (interpretationExpansion S M K') s (ts j)) := by
      funext j
      exact termEval_interpretationExpansion_eq
        S M available K K' hAgree s (ts j) (h j)
    rw [hArgs]
    rfl
  | eq_ h t₁ t₂ =>
    intro hSupport s
    simp only [formulaEvalN]
    rw [termEval_interpretationExpansion_eq
          S M available K K' hAgree s t₁ hSupport.1,
        termEval_interpretationExpansion_eq
          S M available K K' hAgree s t₂ hSupport.2]
    exact Iff.rfl
  | neg A ih =>
    intro h s
    exact not_congr (ih h s)
  | conj A B ihA ihB =>
    intro h s
    exact and_congr (ihA h.1 s) (ihB h.2 s)
  | disj A B ihA ihB =>
    intro h s
    exact or_congr (ihA h.1 s) (ihB h.2 s)
  | impl A B ihA ihB =>
    intro h s
    exact imp_congr (ihA h.1 s) (ihB h.2 s)
  | all x A ih =>
    intro h s
    exact forall_congr' fun a => ih h (assignUpdate s x a)
  | ex x A ih =>
    intro h s
    exact exists_congr fun a => ih h (assignUpdate s x a)

theorem not_mem_right_of_nodup_append {α : Type}
    {xs ys : List α} (h : (xs ++ ys).Nodup)
    {a : α} (ha : a ∈ xs) : a ∉ ys := by
  intro ha'
  exact (List.nodup_append.mp h).2.2 a ha a ha' rfl

theorem not_mem_left_of_nodup_append {α : Type}
    {xs ys : List α} (h : (xs ++ ys).Nodup)
    {a : α} (ha : a ∈ ys) : a ∉ xs := by
  intro ha'
  exact (List.nodup_append.mp h).2.2 a ha' a ha rfl

theorem skolemInterpretationsAgreeOn_of_frame {L : Language}
    (S : SkolemSpec L) (M : Structure L)
    {available changed : List (Fin S.n)}
    {K K' : SkolemInterpretation S M}
    (hFrame : ∀ i, i ∉ changed → ∀ args, K' i args = K i args)
    (hDisjoint : ∀ i, i ∈ available → i ∉ changed) :
    skolemInterpretationsAgreeOn S M available K K' := by
  intro i hi args
  exact (hFrame i (hDisjoint i hi) args).symm

/-- Values of the exact ordered universal scope under an assignment. -/
def exactScopeValues {L : Language}
    (S : SkolemSpec L) (M : Structure L) (i : Fin S.n)
    (s : Nat → M.carrier) :
    Fin (S.skolemRank i) → M.carrier :=
  fun k =>
    s ((S.skolemScope i).get
      ⟨k.val, by
        simpa [SkolemSpec.skolemRank] using k.isLt⟩)

theorem termEval_exactSkolemTerm {L : Language}
    (S : SkolemSpec L) (M : Structure L)
    (K : SkolemInterpretation S M) (i : Fin S.n)
    (s : Nat → M.carrier) :
    termEval (interpretationExpansion S M K) s
        (exactSkolemTerm S i) =
      K i (exactScopeValues S M i s) := by
  unfold exactSkolemTerm
  split
  · rename_i hRank
    simp only [termEval, interpretationExpansion]
    apply congrArg (K i)
    funext j
    exact Fin.elim0 (Fin.cast hRank j)
  · rfl

theorem skolemSpec_indices_nodup {L : Language}
    (S : SkolemSpec L) : S.indices.Nodup := by
  unfold SkolemSpec.indices
  change List.Pairwise (fun x₁ x₂ : Fin S.n => x₁ ≠ x₂)
    (List.ofFn fun i : Fin S.n => i)
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [List.getElem_ofFn, List.getElem_ofFn]
  intro hEq
  have hVal := congrArg Fin.val hEq
  simp at hVal
  omega

/-- Every computed allocation is backed by an existential descriptor;
the filter-map representation cannot allocate any other constructor. -/
private theorem skolemAllocation_isExistential {L : Language}
    (S : SkolemSpec L) (i : Fin S.n) :
    ∃ x D, (S.allocation i).1 = FormulaN.ex x D := by
  have hMem : S.allocation i ∈ S.allocations :=
    List.get_mem S.allocations i
  unfold SkolemSpec.allocations existentialDescriptors
    existentialDescriptorsAux at hMem
  obtain ⟨pair, _hPairMem, hPair⟩ := List.mem_filterMap.mp hMem
  rcases pair with ⟨F, scope⟩
  cases F with
  | predN _ _ => simp at hPair
  | eq_ _ _ _ => simp at hPair
  | neg _ => simp at hPair
  | conj _ _ => simp at hPair
  | disj _ _ => simp at hPair
  | impl _ _ => simp at hPair
  | all _ _ => simp at hPair
  | ex x D =>
    have hEq :
        (FormulaN.ex x D, scope) = S.allocation i :=
      Option.some.inj hPair
    exact ⟨x, D, by rw [← hEq]⟩

/-- Proof-backed binder/body map used to seed the public
`witnessSelectingExpansion`. -/
noncomputable def skolemAllocationBinderBody {L : Language}
    (S : SkolemSpec L) (i : Fin S.n) : Nat × FormulaN L :=
  let h := skolemAllocation_isExistential S i
  (Classical.choose h, Classical.choose (Classical.choose_spec h))

end LCS.Herbrand.SHGTheorem.Main
end

