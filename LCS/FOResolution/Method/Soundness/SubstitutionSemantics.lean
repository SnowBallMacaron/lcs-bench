import LCS.Item
import LCS.Util
import LCS.FOResolution.Method
import LCS.FirstOrder.SemanticsN.Substitution
import Attach
import LCS.FOResolution.Method.Soundness.SubstitutionSemantics.ProofsStamp

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
end LCS.FOResolution.Method.Soundness
end

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

end LCS.FOResolution.Method.Soundness
end

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
end LCS.FOResolution.Method.Soundness
end

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

/-- Lemma 8.5.1 (companion): Build a substitution from a renaming list:
    each pair (v, w) maps variable v to variable w; all other variables
    are left unchanged. Used to construct the renaming component of
    composedSubst. -/
@[blueprint "chap8__lemma_8_5_1"]
def renamingSubst {L : Language} :
    List (Nat × Nat) → Nat → Term L
  | [], x => Term.var x
  | (v, w) :: rest, x =>
    if x = v then Term.var w else renamingSubst rest x

/-- Lemma 8.5.1 (companion): The composed substitution
    sigma' = SubstitutionCore.substCompose sigma (w_1/v_1, ..., w_p/v_p), where sigma
    is the mgu and the second component renames the free variables of C
    to fresh variables w_1,...,w_p. The renaming is given as a list of
    pairs (v_i, w_i). The resulting substitution first renames each v_i
    to w_i, then applies sigma. -/
@[blueprint "chap8__lemma_8_5_1"]
def composedSubst {L : Language}
    (sigma : Nat → Term L) (pairs : List (Nat × Nat)) : Nat → Term L :=
  SubstitutionCore.substCompose sigma (renamingSubst pairs)

end LCS.FOResolution.Method.Soundness
end

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
end LCS.FOResolution.Method.Soundness
end

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

-- retained: used by LCS.FOResolution.Method.Soundness.ResolventValidity, LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
/-- The universal closure of the empty clause wraps
    `FormulaN.falsum A` (the §5.3.8 abbreviation ⊥ ≡ A ∧ ¬A) in
    universal quantifiers. Since `A ∧ ¬A` is unsatisfiable in every
    structure (no assignment can make it true), no structure can
    validate the closure of the empty clause. -/
theorem universalClosure_nil_validIn_false {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (A : FormulaN L)
    (fvs : List Nat)
    (h : ∀ s : Assignment M,
      formulaEvalN M ((FOClause.universalClosure (L := L) (hNoEq := by all_goals exact hNoEq)) A [] fvs) s) :
    False := by
-- BEGIN PROOF
  induction fvs with
  | nil =>
    -- universalClosure A [] [] = clauseToFormula A [] = falsum A = A ∧ ¬A
    have h' := h (fun _ => Classical.choice M.carrierNonempty)
    simp only [FOClause.universalClosure, List.foldr, clauseToFormula,
      FormulaN.falsum, formulaEvalN] at h'
    exact h'.2 h'.1
  | cons v rest ih =>
    apply ih
    intro s
    have h' := h s
    simp only [FOClause.universalClosure, List.foldr, formulaEvalN] at h'
    specialize h' (s v)
    have hsv : assignUpdate s v (s v) = s := by
      funext x; unfold assignUpdate; split <;> simp_all
    rw [hsv] at h'
    exact h'

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
-- Helper: substitution-evaluation lemma for termSubstAll
-- ===================================================================

-- retained: used by LCS.FOResolution.Method.Soundness.ResolventValidity, LCS.SLD.LogicProgramming.Correctness.Correctness
/-- Evaluating a term after applying substitution sigma is the same as
    evaluating the term under a modified assignment that first evaluates
    sigma's images. This is the key semantic lemma connecting syntactic
    substitution to semantic evaluation. -/
theorem termSubstAll_eval {L : Language}
    (M : Structure L) (s : Assignment M) (sigma : Nat → Term L) :
    ∀ (t : Term L),
      termEval M s (termSubstAll t sigma) =
      termEval M (fun x => termEval M s (sigma x)) t := by
-- BEGIN PROOF
  intro t
  induction t with
  | var x => simp [termSubstAll, termEval]
  | const c => simp [termSubstAll, termEval]
  | func f ts ih =>
    simp [termSubstAll, termEval]
    congr 1; funext i; exact ih i

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.SLD.FirstOrder.Soundness
/-- For a predicate formula, evaluating after substitution equals
    evaluating under the substituted assignment. -/
theorem substFormula_predN_eval {L : Language}
    (M : Structure L) (s : Assignment M) (sigma : Nat → Term L)
    (P : L.predSymbols) (args : Fin (L.predArity P) → Term L) :
    formulaEvalN M (substLit.substFormula sigma (.predN P args)) s ↔
    formulaEvalN M (.predN P args) (fun x => termEval M s (sigma x)) := by
-- BEGIN PROOF
  simp only [substLit.substFormula, formulaEvalN]
  have heq : (fun i => termEval M s (termSubstAll (args i) sigma)) =
             (fun i => termEval M (fun x => termEval M s (sigma x)) (args i)) :=
    funext fun i => termSubstAll_eval M s sigma (args i)
  rw [heq]

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.SLD.FirstOrder.Soundness
/-- For an equality formula, evaluating after substitution equals
    evaluating under the substituted assignment. -/
theorem substFormula_eq_eval {L : Language}
    (M : Structure L) (s : Assignment M) (hL : L.hasEquality = true)
    (sigma : Nat → Term L) (t1 t2 : Term L) :
    formulaEvalN M (substLit.substFormula sigma (.eq_ hL t1 t2)) s ↔
    formulaEvalN M (.eq_ hL t1 t2) (fun x => termEval M s (sigma x)) := by
-- BEGIN PROOF
  simp only [substLit.substFormula, formulaEvalN]
  rw [termSubstAll_eval, termSubstAll_eval]

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.SLD.FirstOrder.Soundness
/-- A substitution sigma is fresh for a formula A when for every variable
    i that is bound in A, sigma maps i to var i and no sigma(y) mentions i.
    This ensures substFormula sigma A does not capture bound variables.
    For quantifier-free formulae (including all clause-form formulae used
    in resolution), this predicate is trivially True. -/
def SubstFreshFor {L : Language} (sigma : Nat → Term L) : FormulaN L → Prop
  | .predN _ _ => True
  | .eq_ _ _ _ => True
  | .neg A => SubstFreshFor sigma A
  | .conj A B => SubstFreshFor sigma A ∧ SubstFreshFor sigma B
  | .disj A B => SubstFreshFor sigma A ∧ SubstFreshFor sigma B
  | .impl A B => SubstFreshFor sigma A ∧ SubstFreshFor sigma B
  | .all i A => sigma i = .var i ∧ (∀ y, ¬ termFV (sigma y) i) ∧ SubstFreshFor sigma A
  | .ex i A => sigma i = .var i ∧ (∀ y, ¬ termFV (sigma y) i) ∧ SubstFreshFor sigma A

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.SLD.FirstOrder.Soundness
/-- A quantifier-free formula satisfies SubstFreshFor for any
    substitution, since there are no bound variables to capture. -/
theorem isQF_implies_substFreshFor {L : Language} (sigma : Nat → Term L)
    (A : FormulaN L) (h : isQuantifierFree A) :
    SubstFreshFor sigma A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => trivial
  | eq_ _ _ _ => trivial
  | neg A ih => exact ih h
  | conj A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | disj A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | impl A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | all _ _ => exact absurd h id
  | ex _ _ => exact absurd h id



/-- Lemma 8.5.1 (companion): A clause is quantifier-free when every
    literal's formula is. -/
@[blueprint "chap8__lemma_8_5_1"]
def ClauseQF {L : Language} (hNoEq : L.withoutEquality) (C : FOClause L hNoEq) : Prop :=
  ∀ lit, lit ∈ C → isQuantifierFree lit.formula

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.FOResolution.Method.Soundness.ResolventValidity
/-- Every first-order clause is quantifier-free by construction. -/
theorem clauseQF {L : Language} (hNoEq : L.withoutEquality) (C : FOClause L hNoEq) : (ClauseQF (hNoEq := by all_goals exact hNoEq)) C := by
  intro lit hlit
  cases lit <;> rename_i atom <;> cases atom <;>
    simp [FOLiteral.formula, FOLiteralCore.formula, FOAtomCore.toFormula, isQuantifierFree]









-- retained: used by LCS.FOResolution.Method.Soundness.ResolventValidity
/-- substLit preserves the quantifier-free property of a literal's formula. -/
theorem isQF_substLit_formula {L : Language} (hNoEq : L.withoutEquality) (sigma : Nat → Term L)
    (lit : FOLiteral L hNoEq) (h : isQuantifierFree lit.formula) :
    isQuantifierFree ((substLit (hNoEq := by all_goals exact hNoEq)) sigma lit).formula := by
-- BEGIN PROOF
  exact (clauseQF (hNoEq := by all_goals exact hNoEq)) [(substLit (hNoEq := by all_goals exact hNoEq)) sigma lit] _ (by simp)

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.SLD.FirstOrder.Soundness
/-- If variable i is not free in term t, then termEval is unchanged
    when assignment s is updated at i. -/
theorem termEval_assignUpdate_irrelevant {L : Language}
    (M : Structure L) (s : Assignment M) (i : Nat) (a : M.carrier)
    (t : Term L) (h : ¬ termFV t i) :
    termEval M (assignUpdate s i a) t = termEval M s t := by
-- BEGIN PROOF
  induction t with
  | var x =>
    simp [termFV, Set.singleton] at h
    simp [termEval, assignUpdate]
    intro heq; exact absurd heq.symm h
  | const c => simp [termEval]
  | func f ts ih =>
    simp [termEval]; congr 1; funext j
    apply ih j; intro hc; exact h ⟨j, hc⟩

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.SLD.FirstOrder.Soundness
/-- When sigma is fresh for bound variable i (sigma i = var i and no
    sigma(y) mentions i), the substitution-induced assignment commutes
    with assignUpdate at i. -/
theorem substFresh_assignment_eq {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M) (sigma : Nat → Term L)
    (i : Nat) (a : M.carrier)
    (hSigmaI : sigma i = .var i) (hFresh : ∀ y, ¬ termFV (sigma y) i) :
    (fun x => termEval M (assignUpdate s i a) (sigma x)) =
    assignUpdate (fun x => termEval M s (sigma x)) i a := by
-- BEGIN PROOF
  funext x; simp [assignUpdate]
  by_cases hxi : x = i
  · subst hxi; simp [hSigmaI, termEval, assignUpdate]
  · rw [termEval_assignUpdate_irrelevant M s i a (sigma x) (hFresh x)]; simp [hxi]

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.SLD.FirstOrder.Soundness
/-- General substitution-evaluation lemma for all formulae: evaluating
    substFormula sigma A under assignment s is equivalent to evaluating
    A under the substitution-induced assignment. The hypothesis
    SubstFreshFor sigma A ensures that sigma does not capture any
    bound variable of A. For quantifier-free formulae (including all
    clause-form formulae used in resolution), this hypothesis is
    trivially True. -/
theorem substFormula_eval {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M) (sigma : Nat → Term L)
    (A : FormulaN L) (hFresh : SubstFreshFor sigma A) :
      formulaEvalN M (substLit.substFormula sigma A) s ↔
      formulaEvalN M A (fun x => termEval M s (sigma x)) := by
-- BEGIN PROOF
  induction A generalizing s with
  | predN P args => exact substFormula_predN_eval M s sigma P args
  | eq_ hL t1 t2 => exact substFormula_eq_eval M s hL sigma t1 t2
  | neg A ih =>
    simp only [substLit.substFormula, formulaEvalN]
    exact not_congr (ih s hFresh)
  | conj A B ihA ihB =>
    simp only [substLit.substFormula, formulaEvalN]
    exact and_congr (ihA s hFresh.1) (ihB s hFresh.2)
  | disj A B ihA ihB =>
    simp only [substLit.substFormula, formulaEvalN]
    exact or_congr (ihA s hFresh.1) (ihB s hFresh.2)
  | impl A B ihA ihB =>
    simp only [substLit.substFormula, formulaEvalN]
    exact imp_congr (ihA s hFresh.1) (ihB s hFresh.2)
  | all i A ih =>
    obtain ⟨hSigmaI, hNoCapture, hFreshA⟩ := hFresh
    simp only [substLit.substFormula, formulaEvalN]
    constructor
    · intro h a
      rw [← (substFresh_assignment_eq (hNoEq := by all_goals exact hNoEq)) M s sigma i a hSigmaI hNoCapture]
      exact (ih (assignUpdate s i a) hFreshA).mp (h a)
    · intro h a
      apply (ih (assignUpdate s i a) hFreshA).mpr
      rw [(substFresh_assignment_eq (hNoEq := by all_goals exact hNoEq)) M s sigma i a hSigmaI hNoCapture]
      exact h a
  | ex i A ih =>
    obtain ⟨hSigmaI, hNoCapture, hFreshA⟩ := hFresh
    simp only [substLit.substFormula, formulaEvalN]
    constructor
    · intro ⟨a, ha⟩
      exact ⟨a, by
        rw [← (substFresh_assignment_eq (hNoEq := by all_goals exact hNoEq)) M s sigma i a hSigmaI hNoCapture]
        exact (ih (assignUpdate s i a) hFreshA).mp ha⟩
    · intro ⟨a, ha⟩
      exact ⟨a, by
        apply (ih (assignUpdate s i a) hFreshA).mpr
        rw [(substFresh_assignment_eq (hNoEq := by all_goals exact hNoEq)) M s sigma i a hSigmaI hNoCapture]
        exact ha⟩

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.FOResolution.Method.Soundness.ResolventValidity
/-- For a literal (positive or negative), evaluating the substituted
    literal under assignment s is equivalent to evaluating the original
    literal under the substitution-induced assignment. Requires that
    the literal's formula is quantifier-free (which ensures that
    substFormula does not capture bound variables). -/
theorem substLit_eval {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M) (sigma : Nat → Term L)
    (lit : FOLiteral L hNoEq)
    (hQF : isQuantifierFree lit.formula) :
    formulaEvalN M ((clauseToFormula.litToFormula (hNoEq := hNoEq)) ((substLit (hNoEq := by all_goals exact hNoEq)) sigma lit)) s ↔
    formulaEvalN M ((clauseToFormula.litToFormula (hNoEq := hNoEq)) lit)
      (fun x => termEval M s (sigma x)) := by
-- BEGIN PROOF
  cases lit with
  | pos B =>
    simp only [substLit, clauseToFormula.litToFormula]
    rw [(atomSubst_toFormula (hNoEq := by all_goals exact hNoEq))]
    exact (substFormula_eval (hNoEq := by all_goals exact hNoEq)) M s sigma B.toFormula
      (isQF_implies_substFreshFor sigma B.toFormula hQF)
  | neg B =>
    simp only [substLit, clauseToFormula.litToFormula, formulaEvalN]
    rw [(atomSubst_toFormula (hNoEq := by all_goals exact hNoEq))]
    exact not_congr ((substFormula_eval (hNoEq := by all_goals exact hNoEq)) M s sigma B.toFormula
      (isQF_implies_substFreshFor sigma B.toFormula hQF))

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

-- retained: used by LCS.FOResolution.Method.HerbrandBridge, LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions, LCS.SLD.LogicProgramming.Correctness.Correctness
theorem substLits_clauseToFormula_eval {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (s : Assignment M) (A : FormulaN L)
    (sigma : Nat → Term L)
    (C : FOClause L hNoEq)
    (hQF : (ClauseQF (hNoEq := by all_goals exact hNoEq)) C) :
    formulaEvalN M ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A ((substLits (hNoEq := by all_goals exact hNoEq)) sigma C)) s ↔
    formulaEvalN M ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C) (fun x => termEval M s (sigma x)) := by
-- BEGIN PROOF
  constructor
  · intro h
    obtain ⟨lit', hmem', heval'⟩ := (clauseToFormula_exists_of_true (hNoEq := by all_goals exact hNoEq)) M s A _ h
    simp only [substLits, List.mem_map] at hmem'
    obtain ⟨lit, hmem, rfl⟩ := hmem'
    apply (clauseToFormula_true_of_mem (hNoEq := by all_goals exact hNoEq)) M _ A C lit hmem
    exact ((substLit_eval (hNoEq := by all_goals exact hNoEq)) M s sigma lit (hQF lit hmem)).mp heval'
  · intro h
    obtain ⟨lit, hmem, heval⟩ := (clauseToFormula_exists_of_true (hNoEq := by all_goals exact hNoEq)) M _ A _ h
    have hmem' : (substLit (hNoEq := by all_goals exact hNoEq)) sigma lit ∈ (substLits (hNoEq := by all_goals exact hNoEq)) sigma C := by
      simp only [substLits]; exact List.mem_map_of_mem hmem
    apply (clauseToFormula_true_of_mem (hNoEq := by all_goals exact hNoEq)) M s A _ ((substLit (hNoEq := by all_goals exact hNoEq)) sigma lit) hmem'
    exact ((substLit_eval (hNoEq := by all_goals exact hNoEq)) M s sigma lit (hQF lit hmem)).mpr heval

-- ===================================================================
-- Helper: litSetUnifTerms membership lemmas
-- ===================================================================

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting, LCS.FOResolution.Method.Soundness.ResolventValidity
/-- Helper: define the step function used in litSetUnifTerms foldl. -/
def litSetUnifTermsStep {L : Language} (hNoEq : L.withoutEquality) :
    List (Term L) → FOLiteral L hNoEq → List (Term L) :=
  fun acc lit =>
    match lit with
    | .pos (.predN _ args) => acc ++ List.ofFn args
    | .neg (.predN _ args) => acc ++ List.ofFn args
    | _ => acc

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting, LCS.FOResolution.Method.Soundness.ResolventValidity
/-- The accumulator is preserved through litSetUnifTerms foldl. -/
theorem litSetUnifTerms_foldl_mono {L : Language} (hNoEq : L.withoutEquality)
    (acc : List (Term L)) (lits : List (FOLiteral L hNoEq))
    (t : Term L) (ht : t ∈ acc) :
    t ∈ lits.foldl (litSetUnifTermsStep (hNoEq := by all_goals exact hNoEq)) acc := by
-- BEGIN PROOF
  induction lits generalizing acc with
  | nil => exact ht
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    unfold litSetUnifTermsStep
    split <;> first | exact List.mem_append_left _ ht | exact ht

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting, LCS.FOResolution.Method.Soundness.ResolventValidity
/-- The step function used in litSetUnifTerms agrees with litSetUnifTermsStep. -/
theorem litSetUnifTermsStep_eq {L : Language} (hNoEq : L.withoutEquality)
    (acc : List (Term L)) (lit : FOLiteral L hNoEq) :
    (match lit with
     | .pos (.predN _ args) => acc ++ List.ofFn args
     | .neg (.predN _ args) => acc ++ List.ofFn args
     | _ => acc) = (litSetUnifTermsStep (hNoEq := by all_goals exact hNoEq)) acc lit := by
-- BEGIN PROOF
  unfold litSetUnifTermsStep; cases lit with
  | pos f => cases f <;> rfl
  | neg f => cases f <;> rfl

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting, LCS.FOResolution.Method.Soundness.ResolventValidity
/-- litSetUnifTerms computes the same as foldl with litSetUnifTermsStep. -/
theorem litSetUnifTerms_eq_foldl' {L : Language} (hNoEq : L.withoutEquality)
    (lits : List (FOLiteral L hNoEq)) :
    ∀ acc, lits.foldl (fun acc lit =>
      match lit with
      | .pos (.predN _ args) => acc ++ List.ofFn args
      | .neg (.predN _ args) => acc ++ List.ofFn args
      | _ => acc) acc = lits.foldl (litSetUnifTermsStep (hNoEq := by all_goals exact hNoEq)) acc := by
-- BEGIN PROOF
  induction lits with
  | nil => intro _; rfl
  | cons hd tl ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [(litSetUnifTermsStep_eq (hNoEq := by all_goals exact hNoEq))]
    exact ih _

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting, LCS.FOResolution.Method.Soundness.ResolventValidity
theorem litSetUnifTerms_eq_foldl {L : Language} (hNoEq : L.withoutEquality)
    (lits : List (FOLiteral L hNoEq)) :
    (litSetUnifTerms (hNoEq := by all_goals exact hNoEq)) lits = lits.foldl (litSetUnifTermsStep (hNoEq := by all_goals exact hNoEq)) [] := by
-- BEGIN PROOF
  unfold litSetUnifTerms; exact (litSetUnifTerms_eq_foldl' (hNoEq := by all_goals exact hNoEq)) lits []

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting, LCS.FOResolution.Method.Soundness.ResolventValidity
/-- Monotonicity: if acc1 ⊆ acc2, then foldl step acc1 ⊆ foldl step acc2. -/
theorem litSetUnifTerms_foldl_subset {L : Language} (hNoEq : L.withoutEquality)
    (acc1 acc2 : List (Term L)) (lits : List (FOLiteral L hNoEq))
    (hsub : ∀ t, t ∈ acc1 → t ∈ acc2) :
    ∀ t, t ∈ lits.foldl (litSetUnifTermsStep (hNoEq := by all_goals exact hNoEq)) acc1 →
         t ∈ lits.foldl (litSetUnifTermsStep (hNoEq := by all_goals exact hNoEq)) acc2 := by
-- BEGIN PROOF
  induction lits generalizing acc1 acc2 with
  | nil => exact hsub
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    intro t ht
    unfold litSetUnifTermsStep at ht ⊢
    cases hd with
    | pos f =>
      cases f with
      | predN P args =>
        rw [List.mem_append] at ht ⊢
        rcases ht with h | h
        · exact Or.inl (hsub t h)
        · exact Or.inr h
      | _ => exact hsub t ht
    | neg f =>
      cases f with
      | predN P args =>
        rw [List.mem_append] at ht ⊢
        rcases ht with h | h
        · exact Or.inl (hsub t h)
        · exact Or.inr h
      | _ => exact hsub t ht

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting, LCS.FOResolution.Method.Soundness.ResolventValidity
/-- Helper for litSetUnifTerms_mem_of_predN: works with foldl directly. -/
theorem litSetUnifTerms_mem_of_predN_aux {L : Language} (hNoEq : L.withoutEquality)
    {P : L.predSymbols} {args : Fin (L.predArity P) → Term L}
    {lits : List (FOLiteral L hNoEq)}
    (hmem : FOLiteralCore.pos (.predN P args) ∈ lits ∨
            FOLiteralCore.neg (.predN P args) ∈ lits)
    (i : Fin (L.predArity P)) :
    args i ∈ lits.foldl (litSetUnifTermsStep (hNoEq := by all_goals exact hNoEq)) [] := by
-- BEGIN PROOF
  rcases hmem with hmem | hmem <;> {
    induction lits with
    | nil => exact (List.not_mem_nil hmem).elim
    | cons hd tl ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hmem with rfl | htl
      · apply (litSetUnifTerms_foldl_mono (hNoEq := by all_goals exact hNoEq))
        unfold litSetUnifTermsStep
        exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
      · have h := ih htl
        exact (litSetUnifTerms_foldl_subset (hNoEq := by all_goals exact hNoEq)) [] ((litSetUnifTermsStep (hNoEq := by all_goals exact hNoEq)) [] hd) tl
          (fun _ h => (List.not_mem_nil h).elim) _ h
  }

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting, LCS.FOResolution.Method.Soundness.ResolventValidity
/-- If a predN literal appears in lits, its args are in litSetUnifTerms. -/
theorem litSetUnifTerms_mem_of_predN {L : Language} (hNoEq : L.withoutEquality)
    {P : L.predSymbols} {args : Fin (L.predArity P) → Term L}
    {lits : List (FOLiteral L hNoEq)}
    (hmem : FOLiteralCore.pos (.predN P args) ∈ lits ∨
            FOLiteralCore.neg (.predN P args) ∈ lits)
    (i : Fin (L.predArity P)) :
    args i ∈ (litSetUnifTerms (hNoEq := by all_goals exact hNoEq)) lits := by
-- BEGIN PROOF
  rw [(litSetUnifTerms_eq_foldl (hNoEq := by all_goals exact hNoEq))]
  exact (litSetUnifTerms_mem_of_predN_aux (hNoEq := by all_goals exact hNoEq)) hmem i

/-- Universal validity of a clause closure gives direct clause validity. -/
theorem FOClause.validIn_of_universalClosure {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (A : FormulaN L) (C : FOClause L hNoEq) (fvs : List Nat)
    (_hCover : ∀ n, FOClause.freeVars hNoEq C n → n ∈ fvs)
    (h : ∀ s, formulaEvalN M (FOClause.universalClosure hNoEq A C fvs) s) :
    FOClause.validIn hNoEq M C := by
  intro s
  exact clauseToFormula_exists_of_true hNoEq M s A C
    (universalClosure_strip hNoEq M A C fvs h s)

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

