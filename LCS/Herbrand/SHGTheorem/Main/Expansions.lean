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

end LCS.Herbrand.SHGTheorem.Main
end
