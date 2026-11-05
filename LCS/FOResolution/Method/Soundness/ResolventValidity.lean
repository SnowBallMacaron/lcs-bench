import LCS.Item
import LCS.Util
import LCS.FOResolution.Method
import LCS.FirstOrder.SemanticsN.Substitution
import LCS.FOResolution.Method.Soundness.SubstitutionSemantics
import Attach
import LCS.FOResolution.Method.Soundness.ResolventValidity.ProofsStamp

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
-- ATTACH-BLOCKER: size baseline: retain helper in front
theorem substLit_pos_predN {L : Language} (hNoEq : L.withoutEquality)
    (sigma : Nat → Term L) (P : L.predSymbols)
    (args : Fin (L.predArity P) → Term L) :
    (substLit (hNoEq := by all_goals exact hNoEq)) sigma (FOLiteralCore.pos (.predN P args)) =
    FOLiteralCore.pos (.predN P (fun i => termSubstAll (args i) sigma)) := by
-- BEGIN PROOF
  rfl
-- ATTACH-BLOCKER: size baseline: retain helper in front
theorem substLit_neg_predN {L : Language} (hNoEq : L.withoutEquality)
    (sigma : Nat → Term L) (P : L.predSymbols)
    (args : Fin (L.predArity P) → Term L) :
    (substLit (hNoEq := by all_goals exact hNoEq)) sigma (FOLiteralCore.neg (.predN P args)) =
    FOLiteralCore.neg (.predN P (fun i => termSubstAll (args i) sigma)) := by
-- BEGIN PROOF
  rfl

-- ===================================================================
-- Helper: LitSetAbs preserves membership when head is known
-- ===================================================================
-- ATTACH-BLOCKER: size baseline: retain helper in front
/-- If the first element of a non-empty list is positive,
    LitSetAbs returns the list unchanged. -/
theorem LitSetAbs_of_pos_head {L : Language} (hNoEq : L.withoutEquality)
    {B : FOAtom L hNoEq} {tl : List (FOLiteral L hNoEq)} :
    (LitSetAbs (hNoEq := by all_goals exact hNoEq)) (FOLiteralCore.pos B :: tl) = FOLiteralCore.pos B :: tl := by
-- BEGIN PROOF
  simp [LitSetAbs]
-- ATTACH-BLOCKER: size baseline: retain helper in front
/-- If the first element of a non-empty list is negative,
    LitSetAbs returns LitSetConjugate of the list. -/
theorem LitSetAbs_of_neg_head {L : Language} (hNoEq : L.withoutEquality)
    {B : FOAtom L hNoEq} {tl : List (FOLiteral L hNoEq)} :
    (LitSetAbs (hNoEq := by all_goals exact hNoEq)) (FOLiteralCore.neg B :: tl) = (LitSetConjugate (hNoEq := by all_goals exact hNoEq)) (FOLiteralCore.neg B :: tl) := by
-- BEGIN PROOF
  simp [LitSetAbs]

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting
/-- Conjugation changes only a literal's sign, not its atomic payload. -/
theorem literalAtom_conjugate {L : Language} (hNoEq : L.withoutEquality) (lit : FOLiteral L hNoEq) :
    (literalAtom (hNoEq := by all_goals exact hNoEq)) ((FOLiteral.conjugate (by all_goals exact hNoEq)) lit) = (literalAtom (hNoEq := by all_goals exact hNoEq)) lit := by
  cases lit <;> rfl

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting
/-- Embedding the extracted atom recovers the literal's unsigned formula. -/
theorem literalAtom_toFormula {L : Language} (hNoEq : L.withoutEquality) (lit : FOLiteral L hNoEq) :
    ((literalAtom (hNoEq := by all_goals exact hNoEq)) lit).toFormula = lit.formula := by
  cases lit <;> rfl

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting
/-- Structural substitution commutes with extraction of the atomic payload. -/
theorem literalAtom_substLit {L : Language} (hNoEq : L.withoutEquality)
    (sigma : Nat → Term L) (lit : FOLiteral L hNoEq) :
    (literalAtom (hNoEq := by all_goals exact hNoEq)) ((substLit (hNoEq := by all_goals exact hNoEq)) sigma lit) = ((literalAtom (hNoEq := by all_goals exact hNoEq)) lit).subst (hNoEq := hNoEq) sigma := by
  cases lit <;> rfl

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting
/-- Every literal entering `LitSetAbs` has a same-atom representative in its
    output; only the sign may have been conjugated. -/
theorem LitSetAbs_mem_same_atom {L : Language} (hNoEq : L.withoutEquality)
    {lit : FOLiteral L hNoEq} {lits : List (FOLiteral L hNoEq)}
    (hMem : lit ∈ lits) :
    ∃ absLit ∈ (LitSetAbs (hNoEq := by all_goals exact hNoEq)) lits, (literalAtom (hNoEq := by all_goals exact hNoEq)) absLit = (literalAtom (hNoEq := by all_goals exact hNoEq)) lit := by
  cases lits with
  | nil =>
      exact (List.not_mem_nil hMem).elim
  | cons head tail =>
      cases head with
      | pos atom =>
          exact ⟨lit, by simpa [LitSetAbs] using hMem, rfl⟩
      | neg atom =>
          refine ⟨(FOLiteral.conjugate (by all_goals exact hNoEq)) lit, ?_, (literalAtom_conjugate (hNoEq := by all_goals exact hNoEq)) lit⟩
          simp only [LitSetAbs, LitSetConjugate, List.mem_map]
          exact ⟨lit, hMem, rfl⟩

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting
/-- Conversely, every literal in `LitSetAbs` comes from a source literal with
    the same atomic payload. -/
theorem LitSetAbs_source_same_atom {L : Language} (hNoEq : L.withoutEquality)
    {absLit : FOLiteral L hNoEq} {lits : List (FOLiteral L hNoEq)}
    (hMem : absLit ∈ (LitSetAbs (hNoEq := by all_goals exact hNoEq)) lits) :
    ∃ lit ∈ lits, (literalAtom (hNoEq := by all_goals exact hNoEq)) absLit = (literalAtom (hNoEq := by all_goals exact hNoEq)) lit := by
  cases lits with
  | nil =>
      simp [LitSetAbs] at hMem
  | cons head tail =>
      cases head with
      | pos atom =>
          exact ⟨absLit, by simpa [LitSetAbs] using hMem, rfl⟩
      | neg atom =>
          simp only [LitSetAbs, LitSetConjugate, List.mem_map] at hMem
          obtain ⟨lit, hLitMem, rfl⟩ := hMem
          exact ⟨lit, hLitMem, (literalAtom_conjugate (hNoEq := by all_goals exact hNoEq)) lit⟩

-- ===================================================================
-- Helper: opposite-sign contradiction under substitution
-- ===================================================================
-- ATTACH-BLOCKER: size baseline: retain helper in front
/-- If litA ∈ A' (same-sign set) and litB ∈ B' (opposite-sign set),
    then after applying separating substitutions rho/rho' and unifier
    sigma, the substituted literals cannot both be satisfied under the
    same assignment. This is because:
    (1) A' and B' have opposite sign (one positive, one negative),
    (2) all literals share the same predicate symbol P,
    (3) the unifier makes all predicate arguments equal,
    so one literal gives P(v) true and the other gives ¬P(v) true. -/
theorem opposite_sign_contradiction {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    (M : Structure L) (s : Assignment M)
    (A' B' : List (FOLiteral L hNoEq))
    (rho rho' sigma : Nat → Term L)
    (litA litB : FOLiteral L hNoEq)
    (hlitA_mem : litA ∈ A')
    (hlitB_mem : litB ∈ B')
    (hSameSign : (LitSetSameSign (hNoEq := by all_goals exact hNoEq)) A')
    (hOppSign : (LitSetOppositeSign (hNoEq := by all_goals exact hNoEq)) A' B')
    (hSamePred : (LitSetSamePred (hNoEq := by all_goals exact hNoEq)) (A' ++ (LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B'))
    (hUnif : IsUnifierCore sigma
      ((litSetUnifTerms (hNoEq := by all_goals exact hNoEq))
        ((LitSetAbs (hNoEq := by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) rho A' ++ (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B')))))
    (hlitA_eval : formulaEvalN M
      ((clauseToFormula.litToFormula (hNoEq := hNoEq)) litA)
      (fun x => termEval M (fun y => termEval M s (sigma y)) (rho x)))
    (hlitB_eval : formulaEvalN M
      ((clauseToFormula.litToFormula (hNoEq := hNoEq)) litB)
      (fun x => termEval M (fun y => termEval M s (sigma y)) (rho' x))) :
    False := by
-- BEGIN PROOF
  -- Abbreviations for the composed assignments
  let s_sigma : Assignment M := fun y => termEval M s (sigma y)
  let sA : Assignment M := fun x => termEval M s_sigma (rho x)
  let sB : Assignment M := fun x => termEval M s_sigma (rho' x)
  -- Extract the common predicate symbol from hSamePred
  obtain ⟨P, hPred⟩ := hSamePred
  -- litA ∈ A' ++ LitSetConjugate B'
  have hlitA_comb : litA ∈ A' ++ (LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B' :=
    List.mem_append_left _ hlitA_mem
  -- conjugate(litB) ∈ A' ++ LitSetConjugate B'
  have hconjB_mem : (FOLiteral.conjugate (by all_goals exact hNoEq)) litB ∈ (LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B' := by
    simp only [LitSetConjugate, List.mem_map]
    exact ⟨litB, hlitB_mem, rfl⟩
  have hconjB_comb : (FOLiteral.conjugate (by all_goals exact hNoEq)) litB ∈ A' ++ (LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B' :=
    List.mem_append_right _ hconjB_mem
  -- Both have predicate P
  obtain ⟨argsA, hfA⟩ := hPred litA hlitA_comb
  obtain ⟨argsB, hfB⟩ := hPred ((FOLiteral.conjugate (by all_goals exact hNoEq)) litB) hconjB_comb
  -- Case split on signs
  rcases hOppSign with ⟨hApos, hBneg⟩ | ⟨hAneg, hBpos⟩
  · -- Case 1: A' positive, B' negative
    obtain ⟨fA, rfl⟩ := hApos litA hlitA_mem
    obtain ⟨fB, rfl⟩ := hBneg litB hlitB_mem
    -- Extract predicate structure from formula field
    simp only [FOLiteral.formula, FOLiteralCore.formula] at hfA
    simp only [FOLiteral.conjugate, FOLiteralCore.conjugate, FOLiteral.formula, FOLiteralCore.formula] at hfB
    have hfA' : fA = FOAtomCore.predN P argsA := by
      apply FOAtomCore.toFormula_injective
      simpa [FOAtomCore.toFormula] using hfA
    have hfB' : fB = FOAtomCore.predN P argsB := by
      apply FOAtomCore.toFormula_injective
      simpa [FOAtomCore.toFormula] using hfB
    subst fA
    subst fB
    -- Now litA = pos (predN P argsA), litB = neg (predN P argsB)
    simp only [clauseToFormula.litToFormula, FOAtomCore.toFormula, formulaEvalN] at hlitA_eval hlitB_eval
    change M.interpPred P (fun i => termEval M sA (argsA i)) at hlitA_eval
    change ¬ M.interpPred P (fun i => termEval M sB (argsB i)) at hlitB_eval
    -- hlitA_eval : M.interpPred P (fun i => termEval M sA (argsA i))
    -- hlitB_eval : ¬ M.interpPred P (fun i => termEval M sB (argsB i))
    -- Show the predicate arguments evaluate to the same function
    suffices heq : (fun i => termEval M sA (argsA i)) =
                   (fun i => termEval M sB (argsB i)) by
      rw [heq] at hlitA_eval
      exact hlitB_eval hlitA_eval
    -- Prove argument equality using the unifier
    funext i
    -- termEval M sA (argsA i) = termEval M s (termSubstAll (termSubstAll (argsA i) rho) sigma)
    have hevA : termEval M sA (argsA i) =
        termEval M s (termSubstAll (termSubstAll (argsA i) rho) sigma) := by
      change termEval M (fun x => termEval M s_sigma (rho x)) (argsA i) = _
      rw [← termSubstAll_eval M s_sigma rho (argsA i)]
      rw [← termSubstAll_eval M s sigma (termSubstAll (argsA i) rho)]
    have hevB : termEval M sB (argsB i) =
        termEval M s (termSubstAll (termSubstAll (argsB i) rho') sigma) := by
      change termEval M (fun x => termEval M s_sigma (rho' x)) (argsB i) = _
      rw [← termSubstAll_eval M s_sigma rho' (argsB i)]
      rw [← termSubstAll_eval M s sigma (termSubstAll (argsB i) rho')]
    rw [hevA, hevB]
    -- Now show: termSubstAll (termSubstAll (argsA i) rho) sigma
    --         = termSubstAll (termSubstAll (argsB i) rho') sigma
    -- Both are terms in litSetUnifTerms(...), so the unifier makes them equal.
    -- The unifier gives syntactic equality, which implies evaluation equality.
    congr 1
    -- Need: termSubstAll (termSubstAll (argsA i) rho) sigma
    --     = termSubstAll (termSubstAll (argsB i) rho') sigma
    -- These terms are both in litSetUnifTerms(LitSetAbs(...)), and IsUnifierCore
    -- says all pairs in that list have equal images under sigma.
    apply hUnif
    · -- termSubstAll (argsA i) rho ∈ litSetUnifTerms(LitSetAbs(combined))
      -- Step 1: substLit rho (pos (predN P argsA)) is in substLits rho A'
      have hmemA_subst : FOLiteralCore.pos (.predN P (fun j => termSubstAll (argsA j) rho)) ∈
          (substLits (hNoEq := by all_goals exact hNoEq)) rho A' := by
        rw [← (substLit_pos_predN (hNoEq := by all_goals exact hNoEq)) rho P argsA]
        exact List.mem_map_of_mem (f := (substLit (hNoEq := by all_goals exact hNoEq)) rho) hlitA_mem
      -- Step 2: this is in the combined list
      have hmemA_combined := List.mem_append_left
        ((substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B')) hmemA_subst
      -- Step 3: LitSetAbs of combined = combined (first elem is pos)
      -- Since A' is nonempty (litA ∈ A') and positive, substLits rho A' is nonempty with pos head
      -- Show LitSetAbs of combined = combined (first element is positive)
      -- substLits rho A' is nonempty since A' is nonempty
      have hA'_ne : A' ≠ [] := List.ne_nil_of_mem hlitA_mem
      -- First literal in A' is positive
      obtain ⟨hdA', tlA', rfl⟩ := List.exists_cons_of_ne_nil hA'_ne
      obtain ⟨BhdA, rfl⟩ := hApos hdA' (List.mem_cons_self)
      -- substLits rho (pos BhdA :: tlA') starts with pos (substFormula rho BhdA)
      have hcombined_head : (substLits (hNoEq := by all_goals exact hNoEq)) rho (FOLiteralCore.pos BhdA :: tlA') ++
          (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B') =
          FOLiteralCore.pos ((BhdA.subst (hNoEq := by all_goals exact hNoEq)) rho) ::
          ((substLits (hNoEq := by all_goals exact hNoEq)) rho tlA' ++ (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B')) := by
        simp [substLits, substLit, List.map]
      have habs_eq : (LitSetAbs (hNoEq := by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) rho (FOLiteralCore.pos BhdA :: tlA') ++
          (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B')) =
          (substLits (hNoEq := by all_goals exact hNoEq)) rho (FOLiteralCore.pos BhdA :: tlA') ++
          (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B') := by
        rw [hcombined_head]; exact (LitSetAbs_of_pos_head (hNoEq := by all_goals exact hNoEq))
      rw [habs_eq]
      exact (litSetUnifTerms_mem_of_predN (hNoEq := by all_goals exact hNoEq)) (Or.inl hmemA_combined) i
    · -- termSubstAll (argsB i) rho' ∈ litSetUnifTerms(LitSetAbs(combined))
      -- conjugate(neg (predN P argsB)) = pos (predN P argsB) ∈ LitSetConjugate B'
      have hconjB_in : FOLiteralCore.pos (.predN P argsB) ∈ (LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B' := by
        simp only [LitSetConjugate, List.mem_map]
        exact ⟨FOLiteralCore.neg (.predN P argsB), hlitB_mem, by simp [FOLiteral.conjugate, FOLiteralCore.conjugate]⟩
      -- substLit rho' (pos (predN P argsB)) is in substLits rho' (LitSetConjugate B')
      have hmemB_subst : FOLiteralCore.pos (.predN P (fun j => termSubstAll (argsB j) rho')) ∈
          (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B') := by
        rw [← (substLit_pos_predN (hNoEq := by all_goals exact hNoEq)) rho' P argsB]
        exact List.mem_map_of_mem (f := (substLit (hNoEq := by all_goals exact hNoEq)) rho') hconjB_in
      -- This is in the combined list
      have hmemB_combined := List.mem_append_right
        ((substLits (hNoEq := by all_goals exact hNoEq)) rho A') hmemB_subst
      -- LitSetAbs = identity (same reasoning as above)
      have hA'_ne : A' ≠ [] := List.ne_nil_of_mem hlitA_mem
      obtain ⟨hdA', tlA', rfl⟩ := List.exists_cons_of_ne_nil hA'_ne
      obtain ⟨BhdA, rfl⟩ := hApos hdA' (List.mem_cons_self)
      have habs_eq : (LitSetAbs (hNoEq := by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) rho (FOLiteralCore.pos BhdA :: tlA') ++
          (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B')) =
          (substLits (hNoEq := by all_goals exact hNoEq)) rho (FOLiteralCore.pos BhdA :: tlA') ++
          (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B') := by
        simp [substLits, substLit, List.map, (LitSetAbs_of_pos_head (hNoEq := by all_goals exact hNoEq))]
      rw [habs_eq]
      exact (litSetUnifTerms_mem_of_predN (hNoEq := by all_goals exact hNoEq)) (Or.inl hmemB_combined) i
  · -- Case 2: A' negative, B' positive (symmetric)
    obtain ⟨fA, rfl⟩ := hAneg litA hlitA_mem
    obtain ⟨fB, rfl⟩ := hBpos litB hlitB_mem
    simp only [FOLiteral.formula, FOLiteralCore.formula] at hfA
    simp only [FOLiteral.conjugate, FOLiteralCore.conjugate, FOLiteral.formula, FOLiteralCore.formula] at hfB
    have hfA' : fA = FOAtomCore.predN P argsA := by
      apply FOAtomCore.toFormula_injective
      simpa [FOAtomCore.toFormula] using hfA
    have hfB' : fB = FOAtomCore.predN P argsB := by
      apply FOAtomCore.toFormula_injective
      simpa [FOAtomCore.toFormula] using hfB
    subst fA
    subst fB
    simp only [clauseToFormula.litToFormula, FOAtomCore.toFormula, formulaEvalN] at hlitA_eval hlitB_eval
    change ¬ M.interpPred P (fun i => termEval M sA (argsA i)) at hlitA_eval
    change M.interpPred P (fun i => termEval M sB (argsB i)) at hlitB_eval
    suffices heq : (fun i => termEval M sA (argsA i)) =
                   (fun i => termEval M sB (argsB i)) by
      rw [heq] at hlitA_eval
      exact hlitA_eval hlitB_eval
    funext i
    have hevA : termEval M sA (argsA i) =
        termEval M s (termSubstAll (termSubstAll (argsA i) rho) sigma) := by
      change termEval M (fun x => termEval M s_sigma (rho x)) (argsA i) = _
      rw [← termSubstAll_eval M s_sigma rho (argsA i)]
      rw [← termSubstAll_eval M s sigma (termSubstAll (argsA i) rho)]
    have hevB : termEval M sB (argsB i) =
        termEval M s (termSubstAll (termSubstAll (argsB i) rho') sigma) := by
      change termEval M (fun x => termEval M s_sigma (rho' x)) (argsB i) = _
      rw [← termSubstAll_eval M s_sigma rho' (argsB i)]
      rw [← termSubstAll_eval M s sigma (termSubstAll (argsB i) rho')]
    rw [hevA, hevB]
    congr 1
    apply hUnif
    · -- In Case 2: A' neg, B' pos. After subst, litA = neg (predN P argsA).
      -- substLit rho (neg (predN P argsA)) = neg (predN P (fun j => termSubstAll (argsA j) rho))
      have hmemA_subst : FOLiteralCore.neg (.predN P (fun j => termSubstAll (argsA j) rho)) ∈
          (substLits (hNoEq := by all_goals exact hNoEq)) rho A' := by
        rw [← (substLit_neg_predN (hNoEq := by all_goals exact hNoEq)) rho P argsA]
        exact List.mem_map_of_mem (f := (substLit (hNoEq := by all_goals exact hNoEq)) rho) hlitA_mem
      have hmemA_combined := List.mem_append_left
        ((substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B')) hmemA_subst
      -- A' starts with neg, so combined starts with neg, so LitSetAbs = LitSetConjugate
      have hA'_ne : A' ≠ [] := List.ne_nil_of_mem hlitA_mem
      obtain ⟨hdA', tlA', rfl⟩ := List.exists_cons_of_ne_nil hA'_ne
      obtain ⟨BhdA, rfl⟩ := hAneg hdA' (List.mem_cons_self)
      -- After LitSetConjugate, neg becomes pos
      -- LitSetAbs applies LitSetConjugate since head is neg
      -- conjugate(neg (predN P args_rho)) = pos (predN P args_rho)
      -- So our term is in litSetUnifTerms of the conjugated list
      have hcombined_head : (substLits (hNoEq := by all_goals exact hNoEq)) rho (FOLiteralCore.neg BhdA :: tlA') ++
          (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B') =
          FOLiteralCore.neg ((BhdA.subst (hNoEq := by all_goals exact hNoEq)) rho) ::
          ((substLits (hNoEq := by all_goals exact hNoEq)) rho tlA' ++ (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B')) := by
        simp [substLits, substLit, List.map]
      have habs_eq : (LitSetAbs (hNoEq := by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) rho (FOLiteralCore.neg BhdA :: tlA') ++
          (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B')) =
          (LitSetConjugate (hNoEq := by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) rho (FOLiteralCore.neg BhdA :: tlA') ++
          (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B')) := by
        rw [hcombined_head]; exact (LitSetAbs_of_neg_head (hNoEq := by all_goals exact hNoEq))
      rw [habs_eq]
      -- conjugate maps neg (predN P args) to pos (predN P args)
      -- So our term's membership carries through
      have hconj_mem : FOLiteralCore.pos (.predN P (fun j => termSubstAll (argsA j) rho)) ∈
          (LitSetConjugate (hNoEq := by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) rho (FOLiteralCore.neg BhdA :: tlA') ++
          (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B')) := by
        simp only [LitSetConjugate, List.mem_map]
        exact ⟨FOLiteralCore.neg (.predN P (fun j => termSubstAll (argsA j) rho)),
          hmemA_combined, by simp [FOLiteral.conjugate, FOLiteralCore.conjugate]⟩
      exact (litSetUnifTerms_mem_of_predN (hNoEq := by all_goals exact hNoEq)) (Or.inl hconj_mem) i
    · -- B side in Case 2: litB = pos (predN P argsB), conjugate = neg (predN P argsB)
      -- substLit rho' (neg (predN P argsB)) is in substLits rho' (LitSetConjugate B')
      have hconjB_in : FOLiteralCore.neg (.predN P argsB) ∈ (LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B' := by
        simp only [LitSetConjugate, List.mem_map]
        exact ⟨FOLiteralCore.pos (.predN P argsB), hlitB_mem, by simp [FOLiteral.conjugate, FOLiteralCore.conjugate]⟩
      have hmemB_subst : FOLiteralCore.neg (.predN P (fun j => termSubstAll (argsB j) rho')) ∈
          (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B') := by
        rw [← (substLit_neg_predN (hNoEq := by all_goals exact hNoEq)) rho' P argsB]
        exact List.mem_map_of_mem (f := (substLit (hNoEq := by all_goals exact hNoEq)) rho') hconjB_in
      have hmemB_combined := List.mem_append_right
        ((substLits (hNoEq := by all_goals exact hNoEq)) rho A') hmemB_subst
      -- Same LitSetAbs reasoning
      have hA'_ne : A' ≠ [] := List.ne_nil_of_mem hlitA_mem
      obtain ⟨hdA', tlA', rfl⟩ := List.exists_cons_of_ne_nil hA'_ne
      obtain ⟨BhdA, rfl⟩ := hAneg hdA' (List.mem_cons_self)
      have habs_eq : (LitSetAbs (hNoEq := by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) rho (FOLiteralCore.neg BhdA :: tlA') ++
          (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B')) =
          (LitSetConjugate (hNoEq := by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) rho (FOLiteralCore.neg BhdA :: tlA') ++
          (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B')) := by
        simp [substLits, substLit, List.map, (LitSetAbs_of_neg_head (hNoEq := by all_goals exact hNoEq))]
      rw [habs_eq]
      have hconj_mem : FOLiteralCore.pos (.predN P (fun j => termSubstAll (argsB j) rho')) ∈
          (LitSetConjugate (hNoEq := by all_goals exact hNoEq)) ((substLits (hNoEq := by all_goals exact hNoEq)) rho (FOLiteralCore.neg BhdA :: tlA') ++
          (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B')) := by
        simp only [LitSetConjugate, List.mem_map]
        exact ⟨FOLiteralCore.neg (.predN P (fun j => termSubstAll (argsB j) rho')),
          hmemB_combined, by simp [FOLiteral.conjugate, FOLiteralCore.conjugate]⟩
      exact (litSetUnifTerms_mem_of_predN (hNoEq := by all_goals exact hNoEq)) (Or.inl hconj_mem) i
-- ATTACH-BLOCKER: size baseline: retain helper in front
/-- Pairwise-equation version of `opposite_sign_contradiction`. The generated
    equations compare corresponding arguments with one common reference atom,
    so unrelated argument positions are never equated. -/
theorem opposite_sign_contradiction_pairwise {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    (M : Structure L) (s : Assignment M)
    (A' B' : List (FOLiteral L hNoEq))
    (rho rho' sigma : Nat → Term L)
    (litA litB : FOLiteral L hNoEq)
    (hlitA_mem : litA ∈ A')
    (hlitB_mem : litB ∈ B')
    (_hSameSign : (LitSetSameSign (hNoEq := by all_goals exact hNoEq)) A')
    (hOppSign : (LitSetOppositeSign (hNoEq := by all_goals exact hNoEq)) A' B')
    (hSamePred : (LitSetSamePred (hNoEq := by all_goals exact hNoEq)) (A' ++ (LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B'))
    (hPairwise :
      ∃ pairs : List (Term L × Term L),
        (litSetUnifPairs (hNoEq := by all_goals exact hNoEq))
          ((LitSetAbs (hNoEq := by all_goals exact hNoEq))
            ((substLits (hNoEq := by all_goals exact hNoEq)) rho A' ++
              (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B'))) = some pairs ∧
        IsPairwiseUnifier sigma pairs ∧
        IsPairwiseMGU sigma pairs)
    (hlitA_eval : formulaEvalN M
      ((clauseToFormula.litToFormula (hNoEq := hNoEq)) litA)
      (fun x => termEval M (fun y => termEval M s (sigma y)) (rho x)))
    (hlitB_eval : formulaEvalN M
      ((clauseToFormula.litToFormula (hNoEq := hNoEq)) litB)
      (fun x => termEval M (fun y => termEval M s (sigma y)) (rho' x))) :
    False := by
  let combined :=
    (substLits (hNoEq := by all_goals exact hNoEq)) rho A' ++ (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B')
  obtain ⟨pairs, hPairs, hUnif, _hMGU⟩ := hPairwise
  obtain ⟨P, hPred⟩ := hSamePred
  have hlitA_comb : litA ∈ A' ++ (LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B' :=
    List.mem_append_left _ hlitA_mem
  have hconjB_mem : (FOLiteral.conjugate (by all_goals exact hNoEq)) litB ∈ (LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B' := by
    simp only [LitSetConjugate, List.mem_map]
    exact ⟨litB, hlitB_mem, rfl⟩
  have hconjB_comb :
      (FOLiteral.conjugate (by all_goals exact hNoEq)) litB ∈ A' ++ (LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B' :=
    List.mem_append_right _ hconjB_mem
  obtain ⟨argsA, hFormulaA⟩ := hPred litA hlitA_comb
  obtain ⟨argsB, hFormulaB⟩ :=
    hPred ((FOLiteral.conjugate (by all_goals exact hNoEq)) litB) hconjB_comb
  have hAtomA : (literalAtom (hNoEq := by all_goals exact hNoEq)) litA = FOAtomCore.predN P argsA := by
    apply FOAtomCore.toFormula_injective
    rw [(literalAtom_toFormula (hNoEq := by all_goals exact hNoEq))]
    simpa [FOAtomCore.toFormula] using hFormulaA
  have hConjAtomB :
      (literalAtom (hNoEq := by all_goals exact hNoEq)) ((FOLiteral.conjugate (by all_goals exact hNoEq)) litB) = FOAtomCore.predN P argsB := by
    apply FOAtomCore.toFormula_injective
    rw [(literalAtom_toFormula (hNoEq := by all_goals exact hNoEq))]
    simpa [FOAtomCore.toFormula] using hFormulaB
  have hAtomB : (literalAtom (hNoEq := by all_goals exact hNoEq)) litB = FOAtomCore.predN P argsB := by
    rw [← (literalAtom_conjugate (hNoEq := by all_goals exact hNoEq)) litB]
    exact hConjAtomB
  have hCombinedPred :
      ∀ lit, lit ∈ combined →
        ∃ args : Fin (L.predArity P) → Term L,
          (literalAtom (hNoEq := by all_goals exact hNoEq)) lit = FOAtomCore.predN P args := by
    intro lit hMem
    rcases List.mem_append.mp hMem with hMemA | hMemB
    · simp only [substLits, List.mem_map] at hMemA
      obtain ⟨source, hSourceMem, rfl⟩ := hMemA
      obtain ⟨args, hFormula⟩ :=
        hPred source (List.mem_append_left _ hSourceMem)
      have hSourceAtom : (literalAtom (hNoEq := by all_goals exact hNoEq)) source = FOAtomCore.predN P args := by
        apply FOAtomCore.toFormula_injective
        rw [(literalAtom_toFormula (hNoEq := by all_goals exact hNoEq))]
        simpa [FOAtomCore.toFormula] using hFormula
      refine ⟨fun i => termSubstAll (args i) rho, ?_⟩
      rw [(literalAtom_substLit (hNoEq := by all_goals exact hNoEq)), hSourceAtom]
      rfl
    · simp only [substLits, List.mem_map] at hMemB
      obtain ⟨source, hSourceMem, rfl⟩ := hMemB
      obtain ⟨args, hFormula⟩ :=
        hPred source (List.mem_append_right _ hSourceMem)
      have hSourceAtom : (literalAtom (hNoEq := by all_goals exact hNoEq)) source = FOAtomCore.predN P args := by
        apply FOAtomCore.toFormula_injective
        rw [(literalAtom_toFormula (hNoEq := by all_goals exact hNoEq))]
        simpa [FOAtomCore.toFormula] using hFormula
      refine ⟨fun i => termSubstAll (args i) rho', ?_⟩
      rw [(literalAtom_substLit (hNoEq := by all_goals exact hNoEq)), hSourceAtom]
      rfl
  have hAbsPred :
      ∀ lit, lit ∈ (LitSetAbs (hNoEq := by all_goals exact hNoEq)) combined →
        ∃ args : Fin (L.predArity P) → Term L,
          (literalAtom (hNoEq := by all_goals exact hNoEq)) lit = FOAtomCore.predN P args := by
    intro lit hMem
    obtain ⟨source, hSourceMem, hSameAtom⟩ :=
      (LitSetAbs_source_same_atom (hNoEq := by all_goals exact hNoEq)) hMem
    obtain ⟨args, hSourceShape⟩ := hCombinedPred source hSourceMem
    exact ⟨args, hSameAtom.trans hSourceShape⟩
  have hSubA_mem : (substLit (hNoEq := by all_goals exact hNoEq)) rho litA ∈ (substLits (hNoEq := by all_goals exact hNoEq)) rho A' := by
    simp only [substLits]
    exact List.mem_map_of_mem hlitA_mem
  have hSubA_comb : (substLit (hNoEq := by all_goals exact hNoEq)) rho litA ∈ combined :=
    List.mem_append_left _ hSubA_mem
  have hSubB_mem :
      (substLit (hNoEq := by all_goals exact hNoEq)) rho' ((FOLiteral.conjugate (by all_goals exact hNoEq)) litB) ∈
        (substLits (hNoEq := by all_goals exact hNoEq)) rho' ((LitSetConjugate (hNoEq := by all_goals exact hNoEq)) B') := by
    simp only [substLits]
    exact List.mem_map_of_mem hconjB_mem
  have hSubB_comb :
      (substLit (hNoEq := by all_goals exact hNoEq)) rho' ((FOLiteral.conjugate (by all_goals exact hNoEq)) litB) ∈ combined :=
    List.mem_append_right _ hSubB_mem
  obtain ⟨absA, hAbsA_mem, hAbsA_atom⟩ :=
    (LitSetAbs_mem_same_atom (hNoEq := by all_goals exact hNoEq)) hSubA_comb
  obtain ⟨absB, hAbsB_mem, hAbsB_atom⟩ :=
    (LitSetAbs_mem_same_atom (hNoEq := by all_goals exact hNoEq)) hSubB_comb
  have hAbsA_shape :
      (literalAtom (hNoEq := by all_goals exact hNoEq)) absA =
        FOAtomCore.predN P (fun i => termSubstAll (argsA i) rho) := by
    calc
      (literalAtom (hNoEq := by all_goals exact hNoEq)) absA = (literalAtom (hNoEq := by all_goals exact hNoEq)) ((substLit (hNoEq := by all_goals exact hNoEq)) rho litA) := hAbsA_atom
      _ = ((literalAtom (hNoEq := by all_goals exact hNoEq)) litA).subst (hNoEq := hNoEq) rho := (literalAtom_substLit (hNoEq := by all_goals exact hNoEq)) rho litA
      _ = _ := by rw [hAtomA]; rfl
  have hAbsB_shape :
      (literalAtom (hNoEq := by all_goals exact hNoEq)) absB =
        FOAtomCore.predN P (fun i => termSubstAll (argsB i) rho') := by
    calc
      (literalAtom (hNoEq := by all_goals exact hNoEq)) absB =
          (literalAtom (hNoEq := by all_goals exact hNoEq)) ((substLit (hNoEq := by all_goals exact hNoEq)) rho' ((FOLiteral.conjugate (by all_goals exact hNoEq)) litB)) :=
        hAbsB_atom
      _ = ((literalAtom (hNoEq := by all_goals exact hNoEq)) ((FOLiteral.conjugate (by all_goals exact hNoEq)) litB)).subst (hNoEq := hNoEq) rho' :=
        (literalAtom_substLit (hNoEq := by all_goals exact hNoEq)) rho' ((FOLiteral.conjugate (by all_goals exact hNoEq)) litB)
      _ = _ := by rw [hConjAtomB]; rfl
  have hArgsUnified :
      ∀ i,
        termSubstAll (termSubstAll (argsA i) rho) sigma =
          termSubstAll (termSubstAll (argsB i) rho') sigma :=
    (litSetUnifPairs_unifies_position (hNoEq := by all_goals exact hNoEq)) sigma hPairs hUnif hAbsPred
      hAbsA_mem hAbsB_mem hAbsA_shape hAbsB_shape
  let sSigma : Assignment M := fun y => termEval M s (sigma y)
  let sA : Assignment M := fun x => termEval M sSigma (rho x)
  let sB : Assignment M := fun x => termEval M sSigma (rho' x)
  have hEvalArgs :
      (fun i => termEval M sA (argsA i)) =
        (fun i => termEval M sB (argsB i)) := by
    funext i
    change termEval M (fun x => termEval M sSigma (rho x)) (argsA i) =
      termEval M (fun x => termEval M sSigma (rho' x)) (argsB i)
    rw [← termSubstAll_eval M sSigma rho (argsA i),
        ← termSubstAll_eval M s sigma (termSubstAll (argsA i) rho),
        ← termSubstAll_eval M sSigma rho' (argsB i),
        ← termSubstAll_eval M s sigma (termSubstAll (argsB i) rho'),
        hArgsUnified i]
  rcases hOppSign with ⟨hApos, hBneg⟩ | ⟨hAneg, hBpos⟩
  · obtain ⟨atomA, hLitA⟩ := hApos litA hlitA_mem
    obtain ⟨atomB, hLitB⟩ := hBneg litB hlitB_mem
    subst litA
    subst litB
    simp only [literalAtom] at hAtomA hAtomB
    have hAtomAEq : atomA = FOAtomCore.predN P argsA := hAtomA
    have hAtomBEq : atomB = FOAtomCore.predN P argsB := hAtomB
    subst atomA
    subst atomB
    simp only [clauseToFormula.litToFormula, FOAtomCore.toFormula, formulaEvalN] at hlitA_eval hlitB_eval
    change M.interpPred P (fun i => termEval M sA (argsA i)) at hlitA_eval
    change ¬ M.interpPred P (fun i => termEval M sB (argsB i)) at hlitB_eval
    rw [hEvalArgs] at hlitA_eval
    exact hlitB_eval hlitA_eval
  · obtain ⟨atomA, hLitA⟩ := hAneg litA hlitA_mem
    obtain ⟨atomB, hLitB⟩ := hBpos litB hlitB_mem
    subst litA
    subst litB
    simp only [literalAtom] at hAtomA hAtomB
    have hAtomAEq : atomA = FOAtomCore.predN P argsA := hAtomA
    have hAtomBEq : atomB = FOAtomCore.predN P argsB := hAtomB
    subst atomA
    subst atomB
    simp only [clauseToFormula.litToFormula, FOAtomCore.toFormula, formulaEvalN] at hlitA_eval hlitB_eval
    change ¬ M.interpPred P (fun i => termEval M sA (argsA i)) at hlitA_eval
    change M.interpPred P (fun i => termEval M sB (argsB i)) at hlitB_eval
    rw [hEvalArgs] at hlitA_eval
    exact hlitA_eval hlitB_eval

-- ===================================================================
-- Lemma 8.5.1: Resolvent validity
-- ===================================================================

/-- Lemma 8.5.1: In a language without equality, the universal closures
    of clauses A and B entail the universal closure of any resolvent C.
    Clause truth quantifies over every assignment in every structure.
    The resolvent relation compares literal membership, so C may use any
    finite list representative of its literal set. -/
@[blueprint "chap8__lemma_8_5_1" (main := true)]
theorem resolvent_validity {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    (A B C : FOClause L hNoEq)
    (hRes : IsResolvent hNoEq C A B) :
    ∀ (M : Structure L),
      FOClause.validIn hNoEq M A →
      FOClause.validIn hNoEq M B →
      FOClause.validIn hNoEq M C

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness, LCS.SLD.FirstOrder.Soundness, LCS.SLD.LogicProgramming.Completeness, LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
theorem resolvent_subtree_pw {L : Language} (hNoEq : L.withoutEquality)
    (M : Structure L) (A : FormulaN L) (C : FOClause L hNoEq)
    (h : ∀ (fvs : List Nat),
      (∀ n, (FOClause.freeVars (hNoEq := by all_goals exact hNoEq)) C n → n ∈ fvs) →
        (∀ s : Assignment M, formulaEvalN M ((FOClause.universalClosure (hNoEq := by all_goals exact hNoEq)) A C fvs) s)) :
    ∀ s : Assignment M, formulaEvalN M ((clauseToFormula (hNoEq := by all_goals exact hNoEq)) A C) s := by
-- BEGIN PROOF
  -- Construct a covering list from the clause structure.
  have ⟨fvs, hfvs⟩ : ∃ fvs : List Nat,
      ∀ n, (FOClause.freeVars (hNoEq := by all_goals exact hNoEq)) C n → n ∈ fvs := by
    let clauseVarsList : FOClause L hNoEq → List Nat :=
      fun cl => (cl.map (fun lit => formulaVarsList lit.formula)).flatten
    exact ⟨clauseVarsList C, fun n hfv => by
      obtain ⟨lit, hlit_mem, hlit_fv⟩ := hfv
      rw [List.mem_flatten]
      refine ⟨formulaVarsList ((FOLiteral.formula (by all_goals exact hNoEq)) lit), ?_, formulaVarsList_cover _ n hlit_fv⟩
      exact List.mem_map_of_mem (f := fun lit => formulaVarsList ((FOLiteral.formula (by all_goals exact hNoEq)) lit)) hlit_mem⟩
  exact (universalClosure_strip (hNoEq := by all_goals exact hNoEq)) M A C fvs (h fvs hfvs)
-- ATTACH-BLOCKER: size baseline: retain helper in front
theorem resolvent_validity_pw {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    (A B C : FOClause L hNoEq) (hRes : IsResolvent hNoEq C A B)
    (M : Structure L)
    (hA : FOClause.validIn hNoEq M A)
    (hB : FOClause.validIn hNoEq M B) :
    FOClause.validIn hNoEq M C := by
-- BEGIN PROOF
  have hQFA := (clauseQF (hNoEq := by all_goals exact hNoEq)) A
  have hQFB := (clauseQF (hNoEq := by all_goals exact hNoEq)) B
  obtain ⟨A', B', rho, rho', sigma,
    hSubA, hSubB, _hA'ne, _hB'ne, _hSameSign, _hOppSign,
    _hSamePred, _hSep, _hPairwise, hCeq⟩ := hRes
  intro s
  have sA_eq : (fun x => termEval M s (termSubstAll (rho x) sigma)) =
      (fun x => termEval M (fun y => termEval M s (sigma y)) (rho x)) :=
    funext fun x => termSubstAll_eval M s sigma (rho x)
  have sB_eq : (fun x => termEval M s (termSubstAll (rho' x) sigma)) =
      (fun x => termEval M (fun y => termEval M s (sigma y)) (rho' x)) :=
    funext fun x => termSubstAll_eval M s sigma (rho' x)
  let sA : Assignment M := fun x => termEval M s (termSubstAll (rho x) sigma)
  let sB : Assignment M := fun x => termEval M s (termSubstAll (rho' x) sigma)
  obtain ⟨litA, hlitA_mem, hlitA_eval⟩ := hA sA
  obtain ⟨litB, hlitB_mem, hlitB_eval⟩ := hB sB
  have listDiff_mem : ∀ {α : Type} [DecidableEq α] {a : α} {full sub : List α},
      a ∈ full → a ∉ sub → a ∈ listDiff full sub := by
    intro α _ a full sub hmem hnotin
    simp only [listDiff, List.mem_filter]
    refine ⟨hmem, ?_⟩
    rw [Bool.not_eq_true']; rw [Bool.eq_false_iff]
    intro hc; rw [List.contains_iff_exists_mem_beq] at hc
    obtain ⟨b, hb, heq⟩ := hc; exact hnotin (eq_of_beq heq ▸ hb)
  by_cases hlitA_in : litA ∈ A'
  · by_cases hlitB_in : litB ∈ B'
    · -- contradiction case: opposite sign + unifier
      exact absurd ((opposite_sign_contradiction_pairwise (hNoEq := by all_goals exact hNoEq)) M s A' B' rho rho' sigma
        litA litB hlitA_in hlitB_in _hSameSign _hOppSign _hSamePred _hPairwise
        (sA_eq ▸ hlitA_eval) (sB_eq ▸ hlitB_eval)) id
    · have hmem_diff := listDiff_mem hlitB_mem hlitB_in
      have hmem_sigma : (substLit (hNoEq := by all_goals exact hNoEq)) sigma ((substLit (hNoEq := by all_goals exact hNoEq)) rho' litB) ∈
          (substLits (hNoEq := by all_goals exact hNoEq)) sigma ((substLits (hNoEq := by all_goals exact hNoEq)) rho (listDiff A A') ++
                           (substLits (hNoEq := by all_goals exact hNoEq)) rho' (listDiff B B')) := by
        simp only [substLits, List.map_append]
        exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_map_of_mem hmem_diff))
      refine ⟨_, (hCeq _).mpr hmem_sigma, ?_⟩
      apply ((substLit_eval (hNoEq := by all_goals exact hNoEq)) M s sigma ((substLit (hNoEq := by all_goals exact hNoEq)) rho' litB)
        ((isQF_substLit_formula (hNoEq := by all_goals exact hNoEq)) rho' litB (hQFB litB hlitB_mem))).mpr
      apply ((substLit_eval (hNoEq := by all_goals exact hNoEq)) M (fun x => termEval M s (sigma x)) rho' litB
        (hQFB litB hlitB_mem)).mpr
      rw [← sB_eq]; exact hlitB_eval
  · have hmem_diff := listDiff_mem hlitA_mem hlitA_in
    have hmem_sigma : (substLit (hNoEq := by all_goals exact hNoEq)) sigma ((substLit (hNoEq := by all_goals exact hNoEq)) rho litA) ∈
        (substLits (hNoEq := by all_goals exact hNoEq)) sigma ((substLits (hNoEq := by all_goals exact hNoEq)) rho (listDiff A A') ++
                         (substLits (hNoEq := by all_goals exact hNoEq)) rho' (listDiff B B')) := by
      simp only [substLits, List.map_append]
      exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_map_of_mem hmem_diff))
    refine ⟨_, (hCeq _).mpr hmem_sigma, ?_⟩
    apply ((substLit_eval (hNoEq := by all_goals exact hNoEq)) M s sigma ((substLit (hNoEq := by all_goals exact hNoEq)) rho litA)
      ((isQF_substLit_formula (hNoEq := by all_goals exact hNoEq)) rho litA (hQFA litA hlitA_mem))).mpr
    apply ((substLit_eval (hNoEq := by all_goals exact hNoEq)) M (fun x => termEval M s (sigma x)) rho litA
      (hQFA litA hlitA_mem)).mpr
    rw [← sA_eq]; exact hlitA_eval

-- ===================================================================
-- Helper: well-formed tree label validity (induction on tree)
-- ===================================================================
-- ATTACH-BLOCKER: size baseline: retain helper in front
/-- Every resolution-tree label is quantifier-free by construction. -/
theorem tree_label_qf {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FOLiteral L hNoEq)]
    (T : FOResolutionTree L hNoEq) : (ClauseQF (hNoEq := by all_goals exact hNoEq)) (T.label (hNoEq := by all_goals exact hNoEq)) := by
-- BEGIN PROOF
  exact (clauseQF (hNoEq := by all_goals exact hNoEq)) (T.label (hNoEq := by all_goals exact hNoEq))
-- ATTACH-BLOCKER: size baseline: retain helper in front
/-- Every label of a well-formed resolution tree is satisfied whenever
    all source clauses are satisfied, using direct clause semantics. -/
theorem tree_label_valid {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    (S : FOClause L hNoEq → Prop) (M : Structure L)
    (hSat : ∀ C, S C → FOClause.validIn hNoEq M C)
    (T : FOResolutionTree L hNoEq)
    (hLeaves : T.leavesFrom hNoEq S) (hWF : T.isWellFormed hNoEq) :
    FOClause.validIn hNoEq M (T.label hNoEq) := by
  induction T with
  | axiom_ C => exact hSat C hLeaves
  | resolve T1 T2 A' B' rho rho' sigma ih1 ih2 =>
    obtain ⟨hWF1, hWF2, hVia⟩ := hWF
    exact resolvent_validity_pw hNoEq _ _ _
      ⟨A', B', rho, rho', sigma, hVia⟩ M
      (ih1 hLeaves.1 hWF1) (ih2 hLeaves.2 hWF2)

-- ===================================================================
-- Lemma 8.5.2: Soundness of first-order resolution
-- ===================================================================

/-- Lemma 8.5.2: A finite resolution refutation of S in a language
    without equality makes S unsatisfiable under direct clause semantics.
    The singleton refutation consisting of an empty source clause is
    included, even when the language has no atomic formula. -/
@[blueprint "chap8__lemma_8_5_2" (main := true)]
theorem resolution_soundness_fo {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FOLiteral L hNoEq)]
    (S : FOClause L hNoEq → Prop)
    (D : FOResolutionDAG L hNoEq)
    (hRef : (FOResolutionDAG.isResolutionRefutation (hNoEq := by all_goals exact hNoEq)) D S) :
    (FOClauseSet.isUnsatisfiable (hNoEq := by all_goals exact hNoEq)) S

/-- Lemma 8.5.2 (companion): The singleton set containing the empty
    clause is unsatisfiable. Its one-leaf refutation has zero resolution
    steps and is available in every equality-free language. -/
@[blueprint "chap8__lemma_8_5_2"]
theorem resolution_soundness_empty_clause {L : Language} (hNoEq : L.withoutEquality) :
    FOClauseSet.isUnsatisfiable hNoEq (fun C => C = [])

end LCS.FOResolution.Method.Soundness
end

