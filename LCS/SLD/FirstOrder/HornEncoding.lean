import LCS.Item
import LCS.Util
import LCS.SLD.Propositional
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import LCS.FOResolution.Method
import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.Method.Completeness
import LCS.Herbrand.SHGTheorem.Main
import LCS.SLD.FirstOrder.HornClauses
import LCS.SLD.FirstOrder.HashLanguage
import Attach
import LCS.SLD.FirstOrder.HornEncoding.ProofsStamp

noncomputable section
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.Completeness

-- ATTACH-BLOCKER: private declaration
private def hashReliftTermAt {L : Language} (k : Nat) :
    Term L → Term (HashLanguage L)
  | .var x => if x = k then hashTerm else .var x
  | .const c => .const (Sum.inl c)
  | .func f args =>
      .func (Sum.inl f) (fun i => hashReliftTermAt k (args i))

-- ATTACH-BLOCKER: private declaration
private def hashReliftFormulaAt {L : Language} (k : Nat) :
    FormulaN L → FormulaN (HashLanguage L)
  | .predN P args => .predN P (fun i => hashReliftTermAt k (args i))
  | .eq_ hL t₁ t₂ =>
      .eq_ hL (hashReliftTermAt k t₁) (hashReliftTermAt k t₂)
  | .neg A => .neg (hashReliftFormulaAt k A)
  | .conj A B => .conj (hashReliftFormulaAt k A) (hashReliftFormulaAt k B)
  | .disj A B => .disj (hashReliftFormulaAt k A) (hashReliftFormulaAt k B)
  | .impl A B => .impl (hashReliftFormulaAt k A) (hashReliftFormulaAt k B)
  | .all x A => .all x (hashReliftFormulaAt k A)
  | .ex x A => .ex x (hashReliftFormulaAt k A)

-- ATTACH-BLOCKER: private declaration
private theorem hashReliftTermAt_hashLowerTerm_of_ground {L : Language}
    (k : Nat) (t : Term (HashLanguage L))
    (hGround : ∀ x, ¬ termVars t x) :
    hashReliftTermAt k (hashLowerTerm k t) = t := by
  induction t with
  | var x =>
    exact (hGround x rfl).elim
  | const c =>
    cases c with
    | inl c => rfl
    | inr c =>
      have hc : c = ⟨(0 : Fin 1), rfl⟩ := Subtype.ext (Subsingleton.elim _ _)
      subst c
      simp [hashLowerTerm, hashReliftTermAt, hashTerm]
  | func fs args ih =>
    cases fs with
    | inl f =>
      simp only [hashLowerTerm, hashReliftTermAt]
      congr 1
      funext i
      exact ih i (fun x hx => hGround x ⟨i, hx⟩)
    | inr s => exact (Nat.not_lt_zero _ s.property).elim

-- ATTACH-BLOCKER: private declaration
private theorem hashReliftFormulaAt_hashLowerFormula_of_ground
    {L : Language} (k : Nat) (A : FormulaN (HashLanguage L))
    (hGround : ∀ x, ¬ formulaVars A x) :
    hashReliftFormulaAt k (hashLowerFormula k A) = A := by
  induction A with
  | predN P args =>
    simp only [hashLowerFormula, hashReliftFormulaAt]
    congr 1
    funext i
    exact hashReliftTermAt_hashLowerTerm_of_ground k (args i)
      (fun x hx => hGround x ⟨i, hx⟩)
  | eq_ hL t₁ t₂ =>
    simp only [hashLowerFormula, hashReliftFormulaAt]
    rw [hashReliftTermAt_hashLowerTerm_of_ground k t₁
          (fun x hx => hGround x (Or.inl hx)),
        hashReliftTermAt_hashLowerTerm_of_ground k t₂
          (fun x hx => hGround x (Or.inr hx))]
  | neg A ih =>
    simp only [hashLowerFormula, hashReliftFormulaAt]
    rw [ih hGround]
  | conj A B ihA ihB =>
    simp only [hashLowerFormula, hashReliftFormulaAt]
    rw [ihA (fun x hx => hGround x (Or.inl hx)),
        ihB (fun x hx => hGround x (Or.inr hx))]
  | disj A B ihA ihB =>
    simp only [hashLowerFormula, hashReliftFormulaAt]
    rw [ihA (fun x hx => hGround x (Or.inl hx)),
        ihB (fun x hx => hGround x (Or.inr hx))]
  | impl A B ihA ihB =>
    simp only [hashLowerFormula, hashReliftFormulaAt]
    rw [ihA (fun x hx => hGround x (Or.inl hx)),
        ihB (fun x hx => hGround x (Or.inr hx))]
  | all x A ih =>
    simp only [hashLowerFormula, hashReliftFormulaAt]
    rw [ih hGround]
  | ex x A ih =>
    simp only [hashLowerFormula, hashReliftFormulaAt]
    rw [ih hGround]

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Lowering is injective on ground hash-language terms.  Groundness is
    essential: it rules out a source `.var k` colliding with the hash
    head, which also lowers to `.var k`. -/
theorem hashLowerTerm_injective_of_ground {L : Language} (k : Nat)
    {t u : Term (HashLanguage L)}
    (ht : ∀ x, ¬ termVars t x)
    (hu : ∀ x, ¬ termVars u x)
    (h : hashLowerTerm k t = hashLowerTerm k u) :
    t = u := by
  calc
    t = hashReliftTermAt k (hashLowerTerm k t) :=
      (hashReliftTermAt_hashLowerTerm_of_ground k t ht).symm
    _ = hashReliftTermAt k (hashLowerTerm k u) := congrArg _ h
    _ = u := hashReliftTermAt_hashLowerTerm_of_ground k u hu

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Lowering is injective on ground hash-language formulae. -/
theorem hashLowerFormula_injective_of_ground {L : Language} (k : Nat)
    {A B : FormulaN (HashLanguage L)}
    (hA : ∀ x, ¬ formulaVars A x)
    (hB : ∀ x, ¬ formulaVars B x)
    (h : hashLowerFormula k A = hashLowerFormula k B) :
    A = B := by
  calc
    A = hashReliftFormulaAt k (hashLowerFormula k A) :=
      (hashReliftFormulaAt_hashLowerFormula_of_ground k A hA).symm
    _ = hashReliftFormulaAt k (hashLowerFormula k B) := congrArg _ h
    _ = B := hashReliftFormulaAt_hashLowerFormula_of_ground k B hB

-- retained: used by LCS.SLD.FirstOrder.Soundness
/-- Pointwise lowering of a list of hash-language formulae. -/
def hashLowerFormulaList {L : Language} (k : Nat)
    (xs : List (FormulaN (HashLanguage L))) : List (FormulaN L) :=
  xs.map (hashLowerFormula k)





-- retained: used by LCS.SLD.FirstOrder.Soundness
/-- List lowering commutes with cons. -/
theorem hashLowerFormulaList_cons {L : Language} (k : Nat)
    (A : FormulaN (HashLanguage L))
    (xs : List (FormulaN (HashLanguage L))) :
    hashLowerFormulaList k (A :: xs) =
      hashLowerFormula k A :: hashLowerFormulaList k xs :=
  rfl





























-- retained: used by LCS.SLD.FirstOrder.Soundness
/-- Raw syntactic variables of a formula are covered by the existing
    computable `formulaVarsList` traversal, including occurrences below
    binders. -/
theorem formulaVars_mem_formulaVarsList {L : Language} (A : FormulaN L)
    (x : Nat) (hx : formulaVars A x) :
    x ∈ formulaVarsList A := by
  induction A with
  | predN P args =>
    obtain ⟨i, hi⟩ := hx
    rw [formulaVarsList, List.mem_flatten]
    refine ⟨termVarsList (args i), List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
    exact termVarsList_cover (args i) x
      ((termVars_iff_termFV _ _).mp hi)
  | eq_ hL t₁ t₂ =>
    rw [formulaVarsList, List.mem_append]
    exact hx.elim
      (fun h => Or.inl
        (termVarsList_cover t₁ x ((termVars_iff_termFV _ _).mp h)))
      (fun h => Or.inr
        (termVarsList_cover t₂ x ((termVars_iff_termFV _ _).mp h)))
  | neg A ih => exact ih hx
  | conj A B ihA ihB =>
    rw [formulaVarsList, List.mem_append]
    exact hx.elim (fun h => Or.inl (ihA h)) (fun h => Or.inr (ihB h))
  | disj A B ihA ihB =>
    rw [formulaVarsList, List.mem_append]
    exact hx.elim (fun h => Or.inl (ihA h)) (fun h => Or.inr (ihB h))
  | impl A B ihA ihB =>
    rw [formulaVarsList, List.mem_append]
    exact hx.elim (fun h => Or.inl (ihA h)) (fun h => Or.inr (ihB h))
  | all y A ih => exact ih hx
  | ex y A ih => exact ih hx

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Finite raw-variable enumeration for one source Horn clause. -/
def hashSourceClauseVarsList {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) : List Nat :=
  (c.toFOClause.map (fun lit => formulaVarsList (FOLiteralCore.formula lit))).flatten

-- retained: used by LCS.SLD.FirstOrder.Soundness
/-- `hashSourceClauseVarsList` covers the clause-form FV predicate. -/
theorem hashSourceClauseVarsList_covers {L : Language} (hNoEq : L.withoutEquality)
    (c : FOHornClause L hNoEq) (x : Nat)
    (hx : (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) x) :
    x ∈ (hashSourceClauseVarsList (hNoEq := by all_goals exact hNoEq)) c := by
  obtain ⟨lit, hLit, hVar⟩ := hx
  unfold hashSourceClauseVarsList
  rw [List.mem_flatten]
  refine ⟨formulaVarsList (FOLiteralCore.formula lit),
    List.mem_map.mpr ⟨lit, hLit, rfl⟩, ?_⟩
  apply formulaVars_mem_formulaVarsList (FOLiteralCore.formula lit) x
  rw [← FOLiteralCore.vars_eq_formulaVars lit]
  exact hVar

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The finite variable list of a source Horn problem.  It is computed
    solely from the concrete syntax of `D ++ goals`; no infinite set or
    ambient-language enumeration is involved. -/
def hashSourceProblemVarsList {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq)) : List Nat :=
  ((D ++ goals).map (hashSourceClauseVarsList (hNoEq := by all_goals exact hNoEq))).flatten.eraseDups

-- retained: used by LCS.SLD.FirstOrder.Soundness
/-- Every source-clause variable in `D ++ goals` occurs in the finite
    problem-variable list. -/
theorem hashSourceProblemVarsList_covers {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq))
    (c : FOHornClause L hNoEq) (hc : c ∈ D ++ goals)
    (x : Nat) (hx : (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) x) :
    x ∈ (hashSourceProblemVarsList (hNoEq := by all_goals exact hNoEq)) D goals := by
  unfold hashSourceProblemVarsList
  rw [List.mem_eraseDups, List.mem_flatten]
  exact ⟨(hashSourceClauseVarsList (hNoEq := by all_goals exact hNoEq)) c,
    List.mem_map.mpr ⟨c, hc, rfl⟩,
    (hashSourceClauseVarsList_covers (hNoEq := by all_goals exact hNoEq)) c x hx⟩

-- ATTACH-BLOCKER: private declaration
private theorem hashFoldlMaxInitLe (init : Nat) (xs : List Nat) :
    init ≤ xs.foldl Nat.max init := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl _
  | cons x rest ih =>
    exact Nat.le_trans (Nat.le_max_left init x) (ih _)

-- ATTACH-BLOCKER: private declaration
private theorem hashFoldlMaxMemLe (xs : List Nat) (init x : Nat)
    (hx : x ∈ xs) :
    x ≤ xs.foldl Nat.max init := by
  induction xs generalizing init with
  | nil => exact (List.not_mem_nil hx).elim
  | cons y rest ih =>
    cases List.mem_cons.mp hx with
    | inl h =>
      subst y
      exact Nat.le_trans (Nat.le_max_right init x)
        (hashFoldlMaxInitLe _ _)
    | inr h =>
      exact ih (Nat.max init y) h

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A globally fresh even variable for the finite source Horn problem.
    It is twice one more than the maximum enumerated source variable. -/
def hashFreshEvenVar {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq)) : Nat :=
  2 * (((hashSourceProblemVarsList (hNoEq := by all_goals exact hNoEq)) D goals).foldl Nat.max 0 + 1)

-- retained: used by LCS.SLD.FirstOrder.GroundLifting
/-- The chosen hash variable is explicitly even. -/
theorem hashFreshEvenVar_even {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq)) :
    ∃ q, (hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals = 2 * q :=
  ⟨((hashSourceProblemVarsList (hNoEq := by all_goals exact hNoEq)) D goals).foldl Nat.max 0 + 1, rfl⟩

-- ATTACH-BLOCKER: private name in relocated declaration
/-- The chosen hash variable lies strictly above every member of the
    finite source-problem variable list. -/
theorem hashFreshEvenVar_gt_of_mem {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq)) (x : Nat)
    (hx : x ∈ (hashSourceProblemVarsList (hNoEq := by all_goals exact hNoEq)) D goals) :
    x < (hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals := by
  have hle := hashFoldlMaxMemLe
    ((hashSourceProblemVarsList (hNoEq := by all_goals exact hNoEq)) D goals) 0 x hx
  unfold hashFreshEvenVar
  omega

-- retained: used by LCS.SLD.FirstOrder.Soundness
/-- Global freshness: the selected even variable is absent from every
    source clause in `D ++ goals`. -/
theorem hashFreshEvenVar_not_clauseFV {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq))
    (c : FOHornClause L hNoEq) (hc : c ∈ D ++ goals) :
    ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) := by
  intro hx
  have hMem := (hashSourceProblemVarsList_covers (hNoEq := by all_goals exact hNoEq)) D goals c hc
    ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) hx
  have hLt := (hashFreshEvenVar_gt_of_mem (hNoEq := by all_goals exact hNoEq)) D goals
    ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) hMem
  exact (Nat.lt_irrefl _ hLt)

-- retained: used by LCS.SLD.FirstOrder.GroundLifting
/-- Program-side specialization of global freshness. -/
theorem hashFreshEvenVar_not_program_clauseFV {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq))
    (c : FOHornClause L hNoEq) (hc : c ∈ D) :
    ¬ (clauseFV (hNoEq := by all_goals exact hNoEq)) (c.toFOClause (hNoEq := by all_goals exact hNoEq)) ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) :=
  (hashFreshEvenVar_not_clauseFV (hNoEq := by all_goals exact hNoEq)) D goals c
    (List.mem_append.mpr (Or.inl hc))



-- retained: used by LCS.SLD.FirstOrder.Soundness
/-- Parity separates the fresh hash variable from every odd variable
    used by the existing source-clause renaming. -/
theorem hashFreshEvenVar_ne_odd {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq)) (x : Nat) :
    (hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals ≠ 2 * x + 1 := by
  obtain ⟨q, hq⟩ := (hashFreshEvenVar_even (hNoEq := by all_goals exact hNoEq)) D goals
  rw [hq]
  omega

-- retained: used by LCS.SLD.FirstOrder.Soundness
/-- The term representing the fresh even variable cannot equal a term
    in the odd renaming range. -/
theorem hashFreshEvenVar_var_ne_odd {L : Language} (hNoEq : L.withoutEquality)
    (D goals : List (FOHornClause L hNoEq)) (x : Nat) :
    (Term.var ((hashFreshEvenVar (hNoEq := by all_goals exact hNoEq)) D goals) : Term L) ≠
      Term.var (2 * x + 1) := by
  intro h
  exact (hashFreshEvenVar_ne_odd (hNoEq := by all_goals exact hNoEq)) D goals x (Term.var.inj h)

end LCS.SLD.FirstOrder
end

section
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.Completeness
namespace HashLanguageRegression























end HashLanguageRegression
end LCS.SLD.FirstOrder
end

section
namespace LCS.SLD.FirstOrder
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.FOResolution.Method.Completeness

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- `FormulaN.neg` of an atomic formula is in NNF. -/
theorem isNNF_neg_of_atomic {L : Language}
    (A : FormulaN L) (hA : FormulaN.isAtomic A = true) :
    (FormulaN.neg A).isNNF := by
-- BEGIN PROOF
  cases A with
  | predN _ _ => simp [FormulaN.isNNF]
  | eq_ _ _ _ => simp [FormulaN.isNNF]
  | _ => simp [FormulaN.isAtomic] at hA

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- An atomic formula is in NNF. -/
theorem isNNF_of_atomic {L : Language}
    (A : FormulaN L) (hA : FormulaN.isAtomic A = true) : A.isNNF := by
-- BEGIN PROOF
  cases A with
  | predN _ _ => simp [FormulaN.isNNF]
  | eq_ _ _ _ => simp [FormulaN.isNNF]
  | _ => simp [FormulaN.isAtomic] at hA

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- BVN of an atomic formula is empty. -/
theorem formulaBVN_of_atomic {L : Language}
    (A : FormulaN L) (hA : FormulaN.isAtomic A = true) :
    LCS.FirstOrder.SyntaxN.Variables.formulaBVN A = ∅ := by
-- BEGIN PROOF
  cases A with
  | predN _ _ => simp [LCS.FirstOrder.SyntaxN.Variables.formulaBVN]
  | eq_ _ _ _ => simp [LCS.FirstOrder.SyntaxN.Variables.formulaBVN]
  | _ => simp [FormulaN.isAtomic] at hA

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- BVN of a `litToFormula` is empty because literals carry atoms
    structurally. -/
theorem formulaBVN_of_litToFormula_atomic {L : Language} (hNoEq : L.withoutEquality)
    (lit : FOLiteral L hNoEq) :
    LCS.FirstOrder.SyntaxN.Variables.formulaBVN ((clauseToFormula.litToFormula (hNoEq := by all_goals exact hNoEq)) lit) = ∅ := by
-- BEGIN PROOF
  cases lit with
  | pos B =>
    exact formulaBVN_of_atomic B.toFormula B.toFormula_isAtomic
  | neg B =>
    simp only [clauseToFormula.litToFormula,
      LCS.FirstOrder.SyntaxN.Variables.formulaBVN]
    exact formulaBVN_of_atomic B.toFormula B.toFormula_isAtomic

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- `clauseToFormula` with atomic Afalsum and atomic-literal clause has
    empty BVN. -/
theorem formulaBVN_clauseToFormula_empty {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (hA : FormulaN.isAtomic A = true)
    (C : FOClause L hNoEq) :
    LCS.FirstOrder.SyntaxN.Variables.formulaBVN ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C) = ∅ := by
-- BEGIN PROOF
  induction C with
  | nil =>
    simp only [clauseToFormula, FormulaN.falsum, LCS.FirstOrder.SyntaxN.Variables.formulaBVN]
    rw [formulaBVN_of_atomic A hA]
    ext x; constructor
    · rintro (h | h) <;> exact h
    · intro h; exact h.elim
  | cons hd tl ih =>
    cases tl with
    | nil =>
      simp only [clauseToFormula]
      exact (formulaBVN_of_litToFormula_atomic (hNoEq := by all_goals exact hNoEq)) hd
    | cons hd2 tl2 =>
      simp only [clauseToFormula, LCS.FirstOrder.SyntaxN.Variables.formulaBVN]
      rw [(formulaBVN_of_litToFormula_atomic (hNoEq := by all_goals exact hNoEq)) hd]
      rw [ih]
      ext x; constructor
      · rintro (h | h) <;> exact h
      · intro h; exact h.elim

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- `clauseToFormula` with atomic Afalsum and atomic-literal clause is in NNF. -/
theorem clauseToFormula_isNNF {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (hA : FormulaN.isAtomic A = true)
    (C : FOClause L hNoEq) :
    ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C).isNNF := by
-- BEGIN PROOF
  induction C with
  | nil =>
    simp only [clauseToFormula, FormulaN.falsum]
    simp only [FormulaN.isNNF]
    refine ⟨isNNF_of_atomic A hA, ?_⟩
    exact isNNF_neg_of_atomic A hA
  | cons hd tl ih =>
    cases tl with
    | nil =>
      simp only [clauseToFormula]
      cases hd with
      | pos B =>
        simp only [clauseToFormula.litToFormula]
        exact isNNF_of_atomic B.toFormula B.toFormula_isAtomic
      | neg B =>
        simp only [clauseToFormula.litToFormula]
        exact isNNF_neg_of_atomic B.toFormula B.toFormula_isAtomic
    | cons hd2 tl2 =>
      simp only [clauseToFormula]
      refine ⟨?_, ?_⟩
      · cases hd with
        | pos B =>
          simp only [clauseToFormula.litToFormula]
          exact isNNF_of_atomic B.toFormula B.toFormula_isAtomic
        | neg B =>
          simp only [clauseToFormula.litToFormula]
          exact isNNF_neg_of_atomic B.toFormula B.toFormula_isAtomic
      · exact ih

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- `FOClause.universalClosure` preserves NNF. -/
theorem universalClosure_isNNF {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (hA : FormulaN.isAtomic A = true)
    (C : FOClause L hNoEq) (fvs : List Nat) :
    ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) A C fvs).isNNF := by
-- BEGIN PROOF
  unfold FOClause.universalClosure
  have hBase : ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C).isNNF :=
    (clauseToFormula_isNNF (hNoEq := by all_goals exact hNoEq)) A hA C
  induction fvs with
  | nil => exact hBase
  | cons v rest ih =>
    simp only [List.foldr, FormulaN.isNNF]
    exact ih

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- Membership-level characterization of BVN of `foldr (all v) ... base`.
    Avoids set-builder notation for broader Lean compatibility. -/
theorem formulaBVN_foldr_all_mem {L : Language}
    (fvs : List Nat) (base : FormulaN L) (x : Nat) :
    x ∈ LCS.FirstOrder.SyntaxN.Variables.formulaBVN
      (fvs.foldr (fun v acc => FormulaN.all v acc) base) ↔
    x ∈ LCS.FirstOrder.SyntaxN.Variables.formulaBVN base ∨ x ∈ fvs := by
-- BEGIN PROOF
  induction fvs with
  | nil =>
    simp only [List.foldr, List.not_mem_nil, or_false]
  | cons v rest ih =>
    simp only [List.foldr, LCS.FirstOrder.SyntaxN.Variables.formulaBVN]
    constructor
    · intro hmem
      -- hmem : x ∈ formulaBVN (foldr (all v) rest base) ∪ Set.singleton v
      rcases hmem with hInner | hSing
      · -- hInner : x ∈ formulaBVN (foldr (all v) rest base)
        rcases ih.mp hInner with hb | hr
        · left; exact hb
        · right; exact List.mem_cons_of_mem _ hr
      · -- hSing : x ∈ Set.singleton v, so x = v
        right
        have : x = v := hSing
        exact this ▸ List.mem_cons_self
    · intro hmem
      rcases hmem with hb | hC
      · left; exact ih.mpr (Or.inl hb)
      · rw [List.mem_cons] at hC
        cases hC with
        | inl h =>
          right
          show x ∈ Set.singleton v
          exact h
        | inr h => left; exact ih.mpr (Or.inr h)

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- `distinctQuantifierBindings` of `foldr (all v) ... base` holds when
    `base` has `distinctQuantifierBindings`, `base`'s BVN is disjoint
    from `fvs`, and `fvs` is Nodup. -/
theorem distinctQuantifierBindings_foldr_all {L : Language}
    (fvs : List Nat) (base : FormulaN L)
    (hBase : LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings base)
    (hBaseBVN : LCS.FirstOrder.SyntaxN.Variables.formulaBVN base = ∅)
    (hNodup : fvs.Nodup) :
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings
      (fvs.foldr (fun v acc => FormulaN.all v acc) base) := by
-- BEGIN PROOF
  induction fvs with
  | nil => exact hBase
  | cons v rest ih =>
    have hRestNodup : rest.Nodup := (List.nodup_cons.mp hNodup).2
    have hvNotIn : v ∉ rest := (List.nodup_cons.mp hNodup).1
    simp only [List.foldr, LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings]
    refine ⟨ih hRestNodup, ?_⟩
    intro hmem
    rcases (formulaBVN_foldr_all_mem rest base v).mp hmem with hb | hs
    · rw [hBaseBVN] at hb; exact hb.elim
    · exact hvNotIn hs

-- retained: used by LCS.SLD.FirstOrder.GroundInstances, LCS.SLD.FirstOrder.GroundSemantics
/-- Each literal formula in `h.toFOClause` is atomic by construction. -/
theorem toFOClause_literal_atomic {L : Language} (hNoEq : L.withoutEquality)
    (h : FOHornClause L hNoEq) :
    ∀ lit ∈ (h.toFOClause (hNoEq := by all_goals exact hNoEq)), FormulaN.isAtomic (FOLiteralCore.formula lit) = true := by
-- BEGIN PROOF
  intro lit _
  cases lit <;> apply FOAtomCore.toFormula_isAtomic

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- Universal closure of a Horn-clause's FOClause (with atomic atoms) is in NNF. -/
theorem hornClauseClosure_isNNF {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) (hAf : FormulaN.isAtomic Afalsum = true)
    (h : FOHornClause L hNoEq) :
    ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) Afalsum (h.toFOClause (hNoEq := by all_goals exact hNoEq)) ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum h)).isNNF := by
-- BEGIN PROOF
  exact (universalClosure_isNNF (hNoEq := by all_goals exact hNoEq)) Afalsum hAf (h.toFOClause (hNoEq := by all_goals exact hNoEq)) _



-- ATTACH-BLOCKER: scoped helper requires manual relocation
open LCS.FirstOrder.SyntaxN.Variables in
/-- Universal closure of Horn clause (with covered FVs) is a sentence. -/
theorem hornClauseClosure_isClosed {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (h : FOHornClause L hNoEq) :
    FormulaN.isClosed
      ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) A (h.toFOClause (hNoEq := by all_goals exact hNoEq)) ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) A h)) := by
-- BEGIN PROOF
  unfold FormulaN.isClosed
  ext n
  constructor
  · intro hmem
    exact ((hornClauses_univClosure_sentence (hNoEq := by all_goals exact hNoEq)) A h n hmem).elim
  · intro hmem; exact hmem.elim

-- retained: used by LCS.SLD.FirstOrder.GroundInstances, LCS.SLD.FirstOrder.GroundSemantics
/-- For any `List Nat`, `eraseDups` returns a Nodup list. -/
theorem list_eraseDups_nodup (l : List Nat) : l.eraseDups.Nodup := by
-- BEGIN PROOF
  suffices h : ∀ (n : Nat) (l : List Nat), l.length ≤ n → l.eraseDups.Nodup by
    exact h l.length l (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro l hLen
    cases l with
    | nil => exact List.nodup_nil
    | cons _ _ => simp at hLen
  | succ k ih =>
    intro l hLen
    cases l with
    | nil => exact List.nodup_nil
    | cons hd tl =>
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      refine ⟨?_, ?_⟩
      · rw [List.mem_eraseDups, List.mem_filter]
        intro ⟨_, hne⟩
        simp at hne
      · apply ih
        have hsucc : tl.length ≤ k := by
          have : tl.length + 1 ≤ k + 1 := by simpa using hLen
          omega
        calc ((List.filter _ tl).length) ≤ tl.length := List.length_filter_le _ _
          _ ≤ k := hsucc

-- retained: used by LCS.SLD.FirstOrder.GroundInstances, LCS.SLD.FirstOrder.GroundSemantics
/-- `hornClauseVarsList` is Nodup. -/
theorem hornClauseVarsList_nodup {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (h : FOHornClause L hNoEq) :
    ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) A h).Nodup := by
-- BEGIN PROOF
  unfold hornClauseVarsList
  exact list_eraseDups_nodup _

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- `distinctQuantifierBindings` of atomic formula A. -/
theorem distinctQuantifierBindings_of_atomic {L : Language}
    (A : FormulaN L) (hA : FormulaN.isAtomic A = true) :
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings A := by
-- BEGIN PROOF
  cases A with
  | predN _ _ => simp [LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings]
  | eq_ _ _ _ => simp [LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings]
  | _ => simp [FormulaN.isAtomic] at hA

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- `distinctQuantifierBindings` of `litToFormula lit`, derived from
    the literal's structural atom carrier. -/
theorem distinctQuantifierBindings_litToFormula {L : Language} (hNoEq : L.withoutEquality)
    (lit : FOLiteral L hNoEq) :
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings
      ((clauseToFormula.litToFormula (hNoEq := by all_goals exact hNoEq)) lit) := by
-- BEGIN PROOF
  cases lit with
  | pos B =>
    exact distinctQuantifierBindings_of_atomic
      B.toFormula B.toFormula_isAtomic
  | neg B =>
    simp only [clauseToFormula.litToFormula,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings]
    exact distinctQuantifierBindings_of_atomic
      B.toFormula B.toFormula_isAtomic

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- `clauseToFormula` with atomic Afalsum and atomic-literal clause has
    `distinctQuantifierBindings`. -/
theorem distinctQuantifierBindings_clauseToFormula {L : Language} (hNoEq : L.withoutEquality)
    (A : FormulaN L) (hA : FormulaN.isAtomic A = true)
    (C : FOClause L hNoEq) :
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings
      ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C) := by
-- BEGIN PROOF
  induction C with
  | nil =>
    simp only [clauseToFormula, FormulaN.falsum,
      LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings]
    refine ⟨distinctQuantifierBindings_of_atomic A hA, ?_, ?_⟩
    · -- dqb A (neg simplifies to A)
      exact distinctQuantifierBindings_of_atomic A hA
    · -- BVN disjoint
      intro x hmem
      have hA' := formulaBVN_of_atomic A hA
      rw [hA'] at hmem
      exact hmem.1.elim
  | cons hd tl ih =>
    cases tl with
    | nil =>
      simp only [clauseToFormula]
      exact (distinctQuantifierBindings_litToFormula (hNoEq := by all_goals exact hNoEq)) hd
    | cons hd2 tl2 =>
      simp only [clauseToFormula,
        LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings]
      refine ⟨(distinctQuantifierBindings_litToFormula (hNoEq := by all_goals exact hNoEq)) hd, ih, ?_⟩
      intro x hmem
      have hhd_bvn := (formulaBVN_of_litToFormula_atomic (hNoEq := by all_goals exact hNoEq)) hd
      rw [hhd_bvn] at hmem
      exact hmem.1.elim

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- Universal closure of a Horn-clause's FOClause is rectified: its
    quantifier-free core has empty BVN, FVs are covered by the
    dedup'd `hornClauseVarsList`, so bound-and-free are disjoint and
    the quantifiers bind distinct variables. -/
theorem hornClauseClosure_isRectified {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) (hAf : FormulaN.isAtomic Afalsum = true)
    (h : FOHornClause L hNoEq) :
    LCS.FirstOrder.Semantics.Subformulae.isRectified
      ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) Afalsum (h.toFOClause (hNoEq := by all_goals exact hNoEq)) ((hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum h)) := by
-- BEGIN PROOF
  constructor
  · -- boundVarsFresh: FV ∩ BV = ∅. Since the formula is closed, FV = ∅.
    intro x hmem
    exact ((hornClauses_univClosure_sentence (hNoEq := by all_goals exact hNoEq)) Afalsum h x hmem.1).elim
  · -- distinctQuantifierBindings
    unfold FOClause.universalClosure
    apply distinctQuantifierBindings_foldr_all
    · exact (distinctQuantifierBindings_clauseToFormula (hNoEq := by all_goals exact hNoEq)) Afalsum hAf (h.toFOClause (hNoEq := by all_goals exact hNoEq))
    · exact (formulaBVN_clauseToFormula_empty (hNoEq := by all_goals exact hNoEq)) Afalsum hAf (h.toFOClause (hNoEq := by all_goals exact hNoEq))
    · exact (hornClauseVarsList_nodup (hNoEq := by all_goals exact hNoEq)) Afalsum h

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- `hornClauses_to_formulaN` with atomic Afalsum is in NNF when the
    list is non-empty; Horn-atom atomicity is structural. -/
theorem hornClauses_to_formulaN_isNNF {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) (hAf : FormulaN.isAtomic Afalsum = true)
    (S : List (FOHornClause L hNoEq)) (hNe : S ≠ []) :
    ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum S).isNNF := by
-- BEGIN PROOF
  induction S with
  | nil => exact (hNe rfl).elim
  | cons hd tl ih =>
    cases tl with
    | nil =>
      simp only [hornClauses_to_formulaN]
      exact (hornClauseClosure_isNNF (hNoEq := by all_goals exact hNoEq)) Afalsum hAf hd
    | cons hd2 tl2 =>
      simp only [hornClauses_to_formulaN, FormulaN.isNNF]
      have hIhNe : (hd2 :: tl2 : List (FOHornClause L hNoEq)) ≠ [] := List.cons_ne_nil _ _
      refine ⟨?_, ih hIhNe⟩
      exact (hornClauseClosure_isNNF (hNoEq := by all_goals exact hNoEq)) Afalsum hAf hd

-- ATTACH-BLOCKER: scoped helper requires manual relocation
open LCS.FirstOrder.SyntaxN.Variables in
/-- `hornClauses_to_formulaN` is a sentence (closed formula) when the
    list is non-empty: each clause contributes a closed universal
    closure. -/
theorem hornClauses_to_formulaN_isClosed {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) (S : List (FOHornClause L hNoEq)) (hNe : S ≠ []) :
    FormulaN.isClosed ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum S) := by
-- BEGIN PROOF
  induction S with
  | nil => exact (hNe rfl).elim
  | cons hd tl ih =>
    cases tl with
    | nil =>
      simp only [hornClauses_to_formulaN]
      exact (hornClauseClosure_isClosed (hNoEq := by all_goals exact hNoEq)) Afalsum hd
    | cons hd2 tl2 =>
      simp only [hornClauses_to_formulaN]
      unfold FormulaN.isClosed
      ext n
      constructor
      · intro hmem
        simp only [LCS.FirstOrder.SyntaxN.Variables.formulaFVN] at hmem
        cases hmem with
        | inl hL =>
          have := (hornClauseClosure_isClosed (hNoEq := by all_goals exact hNoEq)) Afalsum hd
          unfold FormulaN.isClosed at this
          rw [this] at hL
          exact hL.elim
        | inr hR =>
          have hIhNe : (hd2 :: tl2 : List (FOHornClause L hNoEq)) ≠ [] := List.cons_ne_nil _ _
          have := ih hIhNe
          unfold FormulaN.isClosed at this
          rw [this] at hR
          exact hR.elim
      · intro hmem; exact hmem.elim

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- BVN of `hornClauses_to_formulaN` with atomic atoms is the union of
    per-clause `hornClauseVarsList`s. Key for proving rectification of
    the multi-clause conjunction. -/
theorem formulaBVN_hornClauses_to_formulaN {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) (hAf : FormulaN.isAtomic Afalsum = true)
    (S : List (FOHornClause L hNoEq)) (hNe : S ≠ []) (x : Nat) :
    x ∈ LCS.FirstOrder.SyntaxN.Variables.formulaBVN
      ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum S) ↔
    ∃ h ∈ S, x ∈ (hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum h := by
-- BEGIN PROOF
  induction S with
  | nil => exact (hNe rfl).elim
  | cons hd tl ih =>
    cases tl with
    | nil =>
      simp only [hornClauses_to_formulaN]
      constructor
      · intro hmem
        unfold FOClause.universalClosure at hmem
        rcases (formulaBVN_foldr_all_mem _ _ x).mp hmem with hb | hl
        · rw [(formulaBVN_clauseToFormula_empty (hNoEq := by all_goals exact hNoEq)) Afalsum hAf (hd.toFOClause (hNoEq := by all_goals exact hNoEq))] at hb
          exact hb.elim
        · exact ⟨hd, List.mem_cons_self, hl⟩
      · rintro ⟨h, hmem, hx⟩
        rw [List.mem_cons] at hmem
        cases hmem with
        | inl heq =>
          subst heq
          unfold FOClause.universalClosure
          exact (formulaBVN_foldr_all_mem _ _ x).mpr (Or.inr hx)
        | inr hF => exact (List.not_mem_nil hF).elim
    | cons hd2 tl2 =>
      simp only [hornClauses_to_formulaN, LCS.FirstOrder.SyntaxN.Variables.formulaBVN]
      have hIhNe : (hd2 :: tl2 : List (FOHornClause L hNoEq)) ≠ [] := List.cons_ne_nil _ _
      constructor
      · intro hmem
        cases hmem with
        | inl hL =>
          unfold FOClause.universalClosure at hL
          rcases (formulaBVN_foldr_all_mem _ _ x).mp hL with hb | hl
          · rw [(formulaBVN_clauseToFormula_empty (hNoEq := by all_goals exact hNoEq)) Afalsum hAf (hd.toFOClause (hNoEq := by all_goals exact hNoEq))] at hb
            exact hb.elim
          · exact ⟨hd, List.mem_cons_self, hl⟩
        | inr hR =>
          obtain ⟨h, hmem, hx⟩ := (ih hIhNe).mp hR
          exact ⟨h, List.mem_cons_of_mem _ hmem, hx⟩
      · rintro ⟨h, hmem, hx⟩
        rw [List.mem_cons] at hmem
        cases hmem with
        | inl heq =>
          subst heq
          left
          unfold FOClause.universalClosure
          exact (formulaBVN_foldr_all_mem _ _ x).mpr (Or.inr hx)
        | inr htl =>
          right
          exact (ih hIhNe).mpr ⟨h, htl, hx⟩

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- `hornClauses_to_formulaN` is rectified when:
    - Each clause's atoms are atomic (inherited from `hAtomic`).
    - Pairwise clause lists (`hornClauseVarsList`) are disjoint.
    - The overall list `S` is `Nodup` (no syntactically equal duplicates).

    The Nodup requirement eliminates the degenerate case where the same
    clause appears twice, which would trivially violate pairwise
    disjointness against itself. In the Horn-clause completeness
    pipeline (Thm 9.4.1), the input `S = D ++ goals` satisfies both
    conditions under the "standardization apart" convention referenced
    in Def 9.4.2: every clause in the program is α-renamed to fresh
    variables before any SLD-resolution step. -/
theorem hornClauses_to_formulaN_isRectified {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L) (hAf : FormulaN.isAtomic Afalsum = true)
    (S : List (FOHornClause L hNoEq))
    (hNe : S ≠ []) (hNodup : S.Nodup)
    (hVarsDisjoint : ∀ h1 ∈ S, ∀ h2 ∈ S, h1 ≠ h2 →
      ∀ x, ¬ (x ∈ (hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum h1 ∧
              x ∈ (hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum h2)) :
    LCS.FirstOrder.Semantics.Subformulae.isRectified
      ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum S) := by
-- BEGIN PROOF
  induction S with
  | nil => exact (hNe rfl).elim
  | cons hd tl ih =>
    cases tl with
    | nil =>
      simp only [hornClauses_to_formulaN]
      exact (hornClauseClosure_isRectified (hNoEq := by all_goals exact hNoEq)) Afalsum hAf hd
    | cons hd2 tl2 =>
      simp only [hornClauses_to_formulaN,
        LCS.FirstOrder.Semantics.Subformulae.isRectified,
        LCS.FirstOrder.Semantics.Subformulae.boundVarsFresh,
        LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings]
      have hIhNe : (hd2 :: tl2 : List (FOHornClause L hNoEq)) ≠ [] := List.cons_ne_nil _ _
      have hIhNodup : (hd2 :: tl2 : List (FOHornClause L hNoEq)).Nodup :=
        (List.nodup_cons.mp hNodup).2
      have hIhVarsDisjoint : ∀ h1 : FOHornClause L hNoEq, h1 ∈ (hd2 :: tl2 : List (FOHornClause L hNoEq)) →
          ∀ h2 : FOHornClause L hNoEq, h2 ∈ (hd2 :: tl2 : List (FOHornClause L hNoEq)) → h1 ≠ h2 →
          ∀ x, ¬ (x ∈ (hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum h1 ∧
                  x ∈ (hornClauseVarsList (hNoEq := by all_goals exact hNoEq)) Afalsum h2) := by
        intro h1 h1mem h2 h2mem hne
        exact hVarsDisjoint h1 (List.mem_cons_of_mem _ h1mem) h2
          (List.mem_cons_of_mem _ h2mem) hne
      have ihRes := ih hIhNe hIhNodup hIhVarsDisjoint
      have hHdRect := (hornClauseClosure_isRectified (hNoEq := by all_goals exact hNoEq)) Afalsum hAf hd
      obtain ⟨hHdBVF, hHdDQB⟩ := hHdRect
      obtain ⟨hTlBVF, hTlDQB⟩ := ihRes
      refine ⟨?_, ?_⟩
      · -- boundVarsFresh of conj
        intro x hmem
        simp only [LCS.FirstOrder.SyntaxN.Variables.formulaFVN,
          LCS.FirstOrder.SyntaxN.Variables.formulaBVN] at hmem
        obtain ⟨hFV, _⟩ := hmem
        -- FV(conj L R) = FV(L) ∪ FV(R); both are closed, so FV = ∅.
        cases hFV with
        | inl hL =>
          have := (hornClauseClosure_isClosed (hNoEq := by all_goals exact hNoEq)) Afalsum hd
          unfold LCS.FirstOrder.SyntaxN.Variables.FormulaN.isClosed at this
          rw [this] at hL
          exact hL.elim
        | inr hR =>
          have := (hornClauses_to_formulaN_isClosed (hNoEq := by all_goals exact hNoEq)) Afalsum (hd2 :: tl2) hIhNe
          unfold LCS.FirstOrder.SyntaxN.Variables.FormulaN.isClosed at this
          rw [this] at hR
          exact hR.elim
      · -- distinctQuantifierBindings of conj
        refine ⟨hHdDQB, hTlDQB, ?_⟩
        -- BVN(hd-closure) ∩ BVN(tl-encoding) = ∅ via hVarsDisjoint
        intro x ⟨hHd, hTl⟩
        unfold FOClause.universalClosure at hHd
        rcases (formulaBVN_foldr_all_mem _ _ x).mp hHd with hb | hl
        · rw [(formulaBVN_clauseToFormula_empty (hNoEq := by all_goals exact hNoEq)) Afalsum hAf (hd.toFOClause (hNoEq := by all_goals exact hNoEq))] at hb
          exact hb.elim
        · -- hl : x ∈ hornClauseVarsList Afalsum hd
          obtain ⟨h', h'mem, h'x⟩ :=
            ((formulaBVN_hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum hAf (hd2 :: tl2)
              hIhNe x).mp hTl
          have h'mem_full : h' ∈ (hd :: hd2 :: tl2 : List (FOHornClause L hNoEq)) :=
            List.mem_cons_of_mem _ h'mem
          -- Since S = hd :: hd2 :: tl2 is Nodup and h' ∈ hd2 :: tl2,
          -- h' ≠ hd (Nodup ensures hd ∉ tl).
          have hd_not_in_tl := (List.nodup_cons.mp hNodup).1
          have hne : h' ≠ hd := by
            intro heq
            subst heq
            exact hd_not_in_tl h'mem
          exact hVarsDisjoint hd List.mem_cons_self h' h'mem_full hne.symm x ⟨hl, h'x⟩

-- ===================================================================
-- Theorem 9.4.1 (required helper): SHG bridge for Horn clauses
-- ===================================================================

-- retained: used by LCS.SLD.FirstOrder.Completeness
/-- Theorem 9.4.1 (required helper): SHG bridge for Horn clauses.
    Given an unsatisfiable Horn clause set `D ++ goals` and a
    `SkolemSpec` packaging `hornClauses_to_formulaN Afalsum (D ++ goals)`
    as a rectified NNF sentence, produce an unsatisfiable compound
    instance of the Skolem form. This is the Chapter 9 specialization
    of Theorem 7.6.1 (Skolem-Herbrand-Godel) part (a) applied to the
    Horn-clause encoding. The caller (Theorem 9.4.1 completeness proof)
    must provide the `SkolemSpec` witness, which amounts to proving
    the Horn-clause universal closure is in rectified NNF — a direct
    consequence of `toFOClause`'s atomic-literal structure under the
    `hD`/`hGoals` definite/goal hypotheses carried by Theorem 9.4.1's
    signature. -/
theorem horn_shg_bridge_with_const {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (D goals : List (FOHornClause L hNoEq))
    (hNe : D ++ goals ≠ [])
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (hSpec : spec.source = (hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals))
    (hConst : Nonempty L.constSymbols)
    (hUnsat : (FOHornClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals)) :
    ∃ (C : FormulaN spec.language)
      (ci : LCS.Herbrand.SHGTheorem.CInstance spec.language),
      ci.source = LCS.Herbrand.SHGTheorem.SK spec ∧
      ci.toFormula = C ∧
      LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci ∧
      ¬ satisfiableN C :=
-- BEGIN PROOF
by
  -- Step (a): By `satisfiableN_hornClauseSet_iff`, the encoded formula
  -- is unsatisfiable iff the Horn clause set is unsatisfiable.
  have hNotSat : ¬ satisfiableN ((hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals)) := by
    rw [(satisfiableN_hornClauseSet_iff (hNoEq := by all_goals exact hNoEq)) _ _ hNe]
    exact hUnsat
  -- Step (b): Transport unsatisfiability to `spec.source` via `hSpec`.
  have hNotSatSource : ¬ satisfiableN spec.source := hSpec ▸ hNotSat
  -- Step (c): Apply Theorem 7.6.1 (shgTheorem_unsat) to extract the
  -- unsatisfiable compound instance.
  exact
    (LCS.Herbrand.SHGTheorem.Main.shgTheorem_unsat
      spec spec.source rfl hConst).mp hNotSatSource

/-- Theorem 9.4.1 (required helper): SHG bridge for Horn clauses without a
    base-language constant premise. The source problem is lifted into the
    one-symbol hash language, whose distinguished nullary term supplies the
    closed seed required by the internal SHG construction. -/
@[blueprint "chap9__theorem_9_4_1"]
theorem horn_shg_bridge {L : Language} (hNoEq : L.withoutEquality)
    (Afalsum : FormulaN L)
    (D goals : List (FOHornClause L hNoEq))
    (hNe : D ++ goals ≠ [])
    (spec : LCS.Herbrand.SHGTheorem.SkolemSpec L)
    (hSpec : spec.source = (hornClauses_to_formulaN (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals))
    (hUnsat : (FOHornClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) Afalsum (D ++ goals)) :
    ∃ (C : FormulaN (hashLiftSkolemSpec spec).language)
      (ci : LCS.Herbrand.SHGTheorem.CInstance
        (hashLiftSkolemSpec spec).language),
      ci.source = LCS.Herbrand.SHGTheorem.SK (hashLiftSkolemSpec spec) ∧
      ci.toFormula = C ∧
      LCS.Herbrand.SHGTheorem.CInstance.WellFormed ci ∧
      ¬ satisfiableN C 

-- ===================================================================
-- Lemma 9.4.1 (helpers): Empty clause unsatisfiability
-- ===================================================================





end LCS.SLD.FirstOrder
end

