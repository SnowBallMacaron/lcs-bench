import LCS.Item
import LCS.Util
import LCS.FOResolution.Method
import LCS.FirstOrder.SemanticsN.Substitution
import Attach
import LCS.FOResolution.Method.Soundness.ClauseSemantics.ProofsStamp

section
namespace LCS.FOResolution.Method.Soundness
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
namespace FOClause

/-- Lemma 8.5.1 (companion): The set of free variables occurring in a
    first-order clause C, defined as the union of free variables of all
    literals in C. Each literal's free variables are obtained via the
    formulaFVN of its underlying atomic formula. Returns Set Nat. -/
@[blueprint "chap8__lemma_8_5_1"]
def freeVars {L : Language} (hNoEq : L.withoutEquality) (C : FOClause L hNoEq) : Set Nat :=
  fun n => ∃ lit, lit ∈ C ∧ formulaFVN lit.formula n

end FOClause

/-- Lemma 8.5.1 (companion): Syntactic conversion for consumers already
    carrying a formula in the language. This is not clause satisfaction.
    Convert a clause (list of literals) into
    a formula by taking the disjunction of the formulae corresponding
    to each literal. The empty clause maps to `FormulaN.falsum A` —
    the §5.3.8 abbreviation ⊥ ≡ (A ∧ ¬A) for a designated formula A.
    A positive literal `.pos B` contributes B; a negative literal
    `.neg B` contributes `.neg B`. -/
@[blueprint "chap8__lemma_8_5_1"]
def clauseToFormula {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) : FOClause L hNoEq → FormulaN L
  | [] => FormulaN.falsum A
  | [lit] => litToFormula lit
  | lit :: rest =>
    FormulaN.disj (litToFormula lit) ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A rest)
where
  /-- Convert a single literal to its corresponding formula. -/
  litToFormula : FOLiteral L hNoEq → FormulaN L
    | .pos B => B
    | .neg B => FormulaN.neg B

namespace FOClause

/-- Lemma 8.5.1 (companion): The universal closure of a clause C:
    wraps the disjunction of literals in C with universal quantifiers
    forall v_1 ... forall v_p for each v_i in FV(C). Since the free
    variable set is a Set Nat (not a list), we take a witness list fvs
    enumerating the free variables and fold universal quantifiers over
    them. Produces a closed FormulaN L. `A` is the §5.3.8 falsum
    abbreviation witness, passed to `clauseToFormula`. -/
@[blueprint "chap8__lemma_8_5_1"]
def universalClosure {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (C : FOClause L hNoEq) (fvs : List Nat) : FormulaN L :=
  fvs.foldr (fun v acc => FormulaN.all v acc) ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C)

end FOClause

namespace FOClause

/-- Lemma 8.5.2 (companion): A clause holds under an assignment exactly
    when one of its literal members holds. The empty clause is false. -/
@[blueprint "chap8__lemma_8_5_2"]
def satisfiedAt {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (C : FOClause L hNoEq) (s : Assignment M) : Prop :=
  ∃ lit, lit ∈ C ∧ formulaEvalN M (clauseToFormula.litToFormula hNoEq lit) s

/-- Lemma 8.5.2 (companion): Universal assignment closure of a clause's
    direct literal semantics, without constructing an auxiliary formula. -/
@[blueprint "chap8__lemma_8_5_2"]
def validIn {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (C : FOClause L hNoEq) : Prop :=
  ∀ s : Assignment M, satisfiedAt hNoEq M C s

end FOClause

namespace FOClauseSet

/-- Lemma 8.5.2 (companion): No structure satisfies every clause of S
    under every assignment. In particular, the empty clause is false
    independently of whether the language has any atomic formula. -/
@[blueprint "chap8__lemma_8_5_2"]
def isUnsatisfiable {L : Language} (hNoEq : L.withoutEquality)
    (S : FOClause L hNoEq → Prop) : Prop :=
  ¬ ∃ (M : Structure L), ∀ C, S C → FOClause.validIn hNoEq M C

end FOClauseSet

-- ===================================================================
-- Helper: computable variable collection for terms and formulae
-- ===================================================================

-- retained: used by LCS.SLD.FirstOrder.HashLanguage, LCS.SLD.FirstOrder.HornEncoding
/-- Collect all variable indices from a term into a list. -/
def termVarsList {L : Language} : Term L → List Nat
  | .var n => [n]
  | .const _ => []
  | .func _ args => (List.ofFn (fun i => termVarsList (args i))).flatten

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.FOResolution.Method.Soundness.ResolventValidity, LCS.SLD.FirstOrder.HashLanguage, LCS.SLD.FirstOrder.HornEncoding
/-- Collect all variable indices from a formula into a list. -/
def formulaVarsList {L : Language} : FormulaN L → List Nat
  | .predN _ args => (List.ofFn (fun i => termVarsList (args i))).flatten
  | .eq_ hL t1 t2 => termVarsList t1 ++ termVarsList t2
  | .neg A => formulaVarsList A
  | .conj A B => formulaVarsList A ++ formulaVarsList B
  | .disj A B => formulaVarsList A ++ formulaVarsList B
  | .impl A B => formulaVarsList A ++ formulaVarsList B
  | .all _ A => formulaVarsList A
  | .ex _ A => formulaVarsList A

-- retained: used by LCS.SLD.FirstOrder.HornEncoding
/-- termVarsList covers all free variables of a term. -/
theorem termVarsList_cover {L : Language} :
    ∀ (t : Term L) (n : Nat), termFV t n → n ∈ termVarsList t := by
-- BEGIN PROOF
  intro t
  induction t with
  | var x =>
    intro n hn
    change n = x at hn
    simp [termVarsList, hn]
  | const _ =>
    intro n hn; exact absurd hn id
  | func f args ih =>
    intro n hn
    change ∃ j, termFV (args j) n at hn
    obtain ⟨j, hj⟩ := hn
    rw [termVarsList, List.mem_flatten]
    exact ⟨termVarsList (args j), ⟨List.mem_ofFn.mpr ⟨j, rfl⟩, ih j n hj⟩⟩

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.FOResolution.Method.Soundness.ResolventValidity, LCS.SLD.FirstOrder.HashLanguage
theorem formulaVarsList_cover {L : Language} :
    ∀ (A : FormulaN L) (n : Nat), formulaFVN A n → n ∈ formulaVarsList A := by
-- BEGIN PROOF
  intro A
  induction A with
  | predN P args =>
    intro n hn
    -- formulaFVN (.predN P args) = Set.iUnion (fun j => termFV (args j))
    change ∃ j, termFV (args j) n at hn
    obtain ⟨j, hj⟩ := hn
    rw [formulaVarsList, List.mem_flatten]
    exact ⟨termVarsList (args j),
      ⟨List.mem_ofFn.mpr ⟨j, rfl⟩, termVarsList_cover (args j) n hj⟩⟩
  | eq_ hL t1 t2 =>
    intro n hn
    -- formulaFVN (.eq_ hL t1 t2) = Set.union (termFV t1) (termFV t2)
    change termFV t1 n ∨ termFV t2 n at hn
    rw [formulaVarsList, List.mem_append]
    cases hn with
    | inl h => left; exact termVarsList_cover t1 n h
    | inr h => right; exact termVarsList_cover t2 n h
  | neg A ih =>
    intro n hn; exact ih n hn
  | conj A B ihA ihB =>
    intro n hn
    change formulaFVN A n ∨ formulaFVN B n at hn
    rw [formulaVarsList, List.mem_append]
    cases hn with
    | inl h => left; exact ihA n h
    | inr h => right; exact ihB n h
  | disj A B ihA ihB =>
    intro n hn
    change formulaFVN A n ∨ formulaFVN B n at hn
    rw [formulaVarsList, List.mem_append]
    cases hn with
    | inl h => left; exact ihA n h
    | inr h => right; exact ihB n h
  | impl A B ihA ihB =>
    intro n hn
    change formulaFVN A n ∨ formulaFVN B n at hn
    rw [formulaVarsList, List.mem_append]
    cases hn with
    | inl h => left; exact ihA n h
    | inr h => right; exact ihB n h
  | all _ A ih =>
    intro n hn
    -- formulaFVN (.all i A) = Set.diff (formulaFVN A) (Set.singleton i)
    change formulaFVN A n ∧ ¬ (n = _) at hn
    exact ih n hn.1
  | ex _ A ih =>
    intro n hn
    change formulaFVN A n ∧ ¬ (n = _) at hn
    exact ih n hn.1

-- ===================================================================
-- Helper: stripping universal closure to get pointwise evaluation
-- ===================================================================

-- retained: used by LCS.FOResolution.Method.Soundness.ResolventValidity, LCS.SLD.FirstOrder.HashLanguage
/-- If validIn M (universalClosure C fvs) and fvs covers all free
    variables of C, then formulaEvalN M (clauseToFormula C) s holds
    for every assignment s.
    The proof works by induction on fvs: at each step we instantiate
    the outermost forall with s(v), and use the fact that the result
    only depends on variables in FV(C). -/
theorem universalClosure_strip {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (A : FormulaN L) (C : FOClause L hNoEq) (fvs : List Nat)
    (hValid : ∀ s : Assignment M, formulaEvalN M ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) A C fvs) s) :
    ∀ s : Assignment M, formulaEvalN M ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C) s := by
-- BEGIN PROOF
  intro s
  induction fvs generalizing s with
  | nil =>
    exact hValid s
  | cons v rest ih =>
    apply ih
    intro s'
    have h := hValid s'
    simp only [FOClause.universalClosure, List.foldr, formulaEvalN] at h
    specialize h (s' v)
    have hsv : assignUpdate s' v (s' v) = s' := by
      funext x; unfold assignUpdate; split <;> simp_all
    rw [hsv] at h
    exact h

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.FOResolution.Method.Soundness.ResolventValidity, LCS.SLD.FirstOrder.HashLanguage, LCS.SLD.FirstOrder.PropositionalEncoding, LCS.SLD.LogicProgramming.Correctness.Correctness
theorem universalClosure_lift {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (A : FormulaN L) (C : FOClause L hNoEq) (fvs : List Nat)
    (h : ∀ s : Assignment M, formulaEvalN M ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C) s) :
    ∀ s : Assignment M, formulaEvalN M ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) A C fvs) s := by
-- BEGIN PROOF
  intro s
  induction fvs generalizing s with
  | nil => exact h s
  | cons v rest ih =>
    simp only [FOClause.universalClosure, List.foldr, formulaEvalN]
    intro a; exact ih (assignUpdate s v a)

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness, LCS.FOResolution.Method.HerbrandBridge, LCS.FOResolution.Method.Soundness.ResolventValidity, LCS.SLD.FirstOrder.Soundness, LCS.SLD.LogicProgramming.Correctness.Correctness
theorem clauseToFormula_true_of_mem {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M) (A : FormulaN L) (C : FOClause L hNoEq)
    (lit : FOLiteral L hNoEq) (hmem : lit ∈ C)
    (hlit : formulaEvalN M ((clauseToFormula.litToFormula (hNoEq := hNoEq)) lit) s) :
    formulaEvalN M ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C) s := by
-- BEGIN PROOF
  induction C with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp only [List.mem_cons] at hmem
    cases tl with
    | nil =>
      simp only [clauseToFormula]
      obtain rfl | h := hmem
      · exact hlit
      · simp at h
    | cons hd' tl' =>
      simp only [clauseToFormula, formulaEvalN]
      obtain rfl | h := hmem
      · left; exact hlit
      · right; exact ih h

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness, LCS.FOResolution.Method.Soundness.ResolventValidity, LCS.SLD.FirstOrder.Soundness, LCS.SLD.LogicProgramming.Completeness, LCS.SLD.LogicProgramming.Correctness.Correctness
/-- Evaluating clauseToFormula: if the formula is true and the clause is
    non-empty, then some literal in the clause evaluates to true.
    (For the empty clause, `clauseToFormula A []` = `FormulaN.falsum A`
    is unsatisfiable, so the hypothesis h is contradictory and the
    conclusion is vacuous.) -/
theorem clauseToFormula_exists_of_true {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M) (A : FormulaN L) (C : FOClause L hNoEq)
    (h : formulaEvalN M ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C) s) :
    ∃ lit, lit ∈ C ∧ formulaEvalN M ((clauseToFormula.litToFormula (hNoEq := hNoEq)) lit) s := by
-- BEGIN PROOF
  induction C with
  | nil =>
    -- clauseToFormula A [] = FormulaN.falsum A = A ∧ ¬A, which is False
    simp only [clauseToFormula, FormulaN.falsum, formulaEvalN] at h
    exact absurd h.1 h.2
  | cons hd tl ih =>
    cases tl with
    | nil =>
      exact ⟨hd, List.mem_cons_self, h⟩
    | cons hd' tl' =>
      simp only [clauseToFormula, formulaEvalN] at h
      cases h with
      | inl hleft =>
        exact ⟨hd, List.mem_cons_self, hleft⟩
      | inr hright =>
        obtain ⟨lit, hmem, heval⟩ := ih hright
        exact ⟨lit, .tail _ hmem, heval⟩

/-- Direct clause validity validates every universal closure encoding. -/
theorem FOClause.universalClosure_of_validIn {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (C : FOClause L hNoEq) (h : FOClause.validIn hNoEq M C) :
    ∀ A fvs s, formulaEvalN M (FOClause.universalClosure hNoEq A C fvs) s := by
  intro A fvs
  apply universalClosure_lift hNoEq M A C fvs
  intro s
  obtain ⟨lit, hmem, hlit⟩ := h s
  exact clauseToFormula_true_of_mem hNoEq M s A C lit hmem hlit

end LCS.FOResolution.Method.Soundness
end
