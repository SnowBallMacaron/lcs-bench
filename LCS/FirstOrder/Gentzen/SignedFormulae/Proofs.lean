import LCS.FirstOrder.Gentzen.SignedFormulae

namespace LCS.FirstOrder.Gentzen.SignedFormulae

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Gentzen

helper /-- For any structure M, term t', a ground term t (whose evaluation is
assignment-independent), variable x, element m, and assignment s:
evaluating t'[t/x] under s equals evaluating t' under s[x := m],
provided t evaluates to m under all assignments. -/
theorem termSubstEvalConst {L : Language} (M : Structure L)
    (t' : Term L) (t : Term L) (x : Nat) (m : M.carrier)
    (ht : ∀ s' : Assignment M, termEval M s' t = m)
    (s : Assignment M) :
    termEval M s (termSubst t' t x) =
    termEval M (assignUpdate s x m) t' := by
-- BEGIN PROOF
  induction t' with
  | var y =>
    simp [termSubst, termEval, assignUpdate]
    split
    · subst_vars; simp [ht]
    · rfl
  | const c =>
    simp [termSubst, termEval]
  | func f ts ih =>
    simp [termSubst, termEval]
    congr 1; funext j; exact ih j

helper /-- For any structure M, FormulaN A, a ground term t, variable x,
element m, and assignment s: evaluating A[t/x] under s is equivalent
to evaluating A under s[x := m], provided t evaluates to m under all
assignments. -/
theorem formulaSubstEvalConstN {L : Language} (M : Structure L)
    (A : FormulaN L) (t : Term L) (x : Nat) (m : M.carrier)
    (ht : ∀ s' : Assignment M, termEval M s' t = m)
    (s : Assignment M) :
    formulaEvalN M (formulaSubstN A t x) s ↔
    formulaEvalN M A (assignUpdate s x m) := by
-- BEGIN PROOF
  induction A generalizing s with
  | predN P ts =>
    simp only [formulaSubstN, formulaEvalN]
    have heq : (fun i => termEval M s (termSubst (ts i) t x)) =
               (fun i => termEval M (assignUpdate s x m) (ts i)) := by
      funext j; exact termSubstEvalConst M (ts j) t x m ht s
    rw [heq]
  | eq_ _ t1 t2 =>
    simp only [formulaSubstN, formulaEvalN]
    rw [termSubstEvalConst M t1 t x m ht s, termSubstEvalConst M t2 t x m ht s]
  | conj A B ihA ihB =>
    simp only [formulaSubstN, formulaEvalN, Basic.andM]; exact and_congr (ihA s) (ihB s)
  | disj A B ihA ihB =>
    simp only [formulaSubstN, formulaEvalN, Basic.orM]; exact or_congr (ihA s) (ihB s)
  | impl A B ihA ihB =>
    simp only [formulaSubstN, formulaEvalN, Basic.implM]; exact imp_congr (ihA s) (ihB s)
  | neg A ih =>
    simp only [formulaSubstN, formulaEvalN, Basic.negM]; exact not_congr (ih s)
  | all j A ih =>
    simp only [formulaSubstN]
    by_cases hxj : x = j
    · subst hxj
      simp only [bne_self_eq_false, formulaEvalN]
      have key : ∀ (a : M.carrier),
          assignUpdate (assignUpdate s x m) x a = assignUpdate s x a :=
        fun a => funext fun k => by unfold assignUpdate; split <;> simp_all
      apply forall_congr'; intro a; rw [key]
    · simp only [show (x != j) = true from by
        rw [bne_iff_ne]; exact hxj, ite_true, formulaEvalN]
      have swap : ∀ (a : M.carrier),
          assignUpdate (assignUpdate s x m) j a =
            assignUpdate (assignUpdate s j a) x m :=
        fun a => funext fun k => by
          unfold assignUpdate; split <;> split <;> simp_all
      apply forall_congr'; intro a; rw [swap]; exact ih (assignUpdate s j a)
  | ex j A ih =>
    simp only [formulaSubstN]
    by_cases hxj : x = j
    · subst hxj
      simp only [bne_self_eq_false, formulaEvalN]
      have key : ∀ (a : M.carrier),
          assignUpdate (assignUpdate s x m) x a = assignUpdate s x a :=
        fun a => funext fun k => by unfold assignUpdate; split <;> simp_all
      apply exists_congr; intro a; rw [key]
    · simp only [show (x != j) = true from by
        rw [bne_iff_ne]; exact hxj, ite_true, formulaEvalN]
      have swap : ∀ (a : M.carrier),
          assignUpdate (assignUpdate s x m) j a =
            assignUpdate (assignUpdate s j a) x m :=
        fun a => funext fun k => by
          unfold assignUpdate; split <;> split <;> simp_all
      apply exists_congr; intro a; rw [swap]; exact ih (assignUpdate s j a)

proof_of namingConst_freeForN := by
  induction A <;> simp_all [isFreeForN, namingConst, termFV]
  all_goals exact Or.inr (fun h => h)


helper /-- Lemma 5.4.4: For any structure M, assignment s, and type-c formula C
(in the extended language), M |= C[s] iff for every element a in M.carrier, M |= C(namingConst a)[s]. (Lemma 5.4.4 bundles type-c universal and type-d existential; this is the type-c primary.) -/
theorem typeC_satisfaction_iff {L : Language} (S : Structure L)
    (s : Assignment (extendedInterp S))
    (C : TypeC (extendedLanguage L S.carrier)) :
    SignedFormula.satisfiedBy (extendedInterp S) s (TypeC.toSigned C) ↔
    ∀ a : S.carrier,
      SignedFormula.satisfiedBy (extendedInterp S) s
        (TypeC.comp C (namingConst a) (namingConst_freeForN a C.var C.body)) :=
-- BEGIN PROOF
by
  have ncEval : ∀ (a : S.carrier) (s' : Assignment (extendedInterp S)),
      termEval (extendedInterp S) s' (namingConst a) = a :=
    fun a s' => namingConstEval S s' a
  cases C with
  | tAll x Y =>
    simp only [TypeC.toSigned, TypeC.comp, SignedFormula.satisfiedBy]
    constructor
    · intro h a
      exact (formulaSubstEvalConstN _ Y _ x a (ncEval a) s).mpr (h a)
    · intro h a
      exact (formulaSubstEvalConstN _ Y _ x a (ncEval a) s).mp (h a)
  | fEx x Y =>
    simp only [TypeC.toSigned, TypeC.comp, SignedFormula.satisfiedBy]
    constructor
    · intro h a habs
      exact h ⟨a, (formulaSubstEvalConstN _ Y _ x a (ncEval a) s).mp habs⟩
    · intro h ⟨a, ha⟩
      exact h a ((formulaSubstEvalConstN _ Y _ x a (ncEval a) s).mpr ha)

helper /-- Lemma 5.4.4 (companion, Part ii): For any structure M, assignment
s, and type-d formula D (in the extended language), M |= D[s] iff for
at least one element a in M.carrier, M |= D(namingConst a)[s]. -/
theorem typeD_satisfaction_iff {L : Language} (S : Structure L)
    (s : Assignment (extendedInterp S))
    (D : TypeD (extendedLanguage L S.carrier)) :
    SignedFormula.satisfiedBy (extendedInterp S) s (TypeD.toSigned D) ↔
    ∃ a : S.carrier,
      SignedFormula.satisfiedBy (extendedInterp S) s
        (TypeD.comp D (namingConst a) (namingConst_freeForN a D.var D.body)) :=
-- BEGIN PROOF
by
  have ncEval : ∀ (a : S.carrier) (s' : Assignment (extendedInterp S)),
      termEval (extendedInterp S) s' (namingConst a) = a :=
    fun a s' => namingConstEval S s' a
  cases D with
  | tEx x Y =>
    simp only [TypeD.toSigned, TypeD.comp, SignedFormula.satisfiedBy]
    constructor
    · intro ⟨a, ha⟩
      exact ⟨a, (formulaSubstEvalConstN _ Y _ x a (ncEval a) s).mpr ha⟩
    · intro ⟨a, ha⟩
      exact ⟨a, (formulaSubstEvalConstN _ Y _ x a (ncEval a) s).mp ha⟩
  | fAll x Y =>
    simp only [TypeD.toSigned, TypeD.comp, SignedFormula.satisfiedBy]
    have key : ∀ a : S.carrier,
        formulaEvalN (extendedInterp S) Y (assignUpdate s x a) ↔
        formulaEvalN (extendedInterp S) (formulaSubstN Y (namingConst a) x) s :=
      fun a => (formulaSubstEvalConstN _ Y _ x a (ncEval a) s).symm
    constructor
    · intro h
      have h' : ¬ ∀ a, formulaEvalN (extendedInterp S)
          (formulaSubstN Y (namingConst a) x) s :=
        fun hall => h (fun a => (key a).mpr (hall a))
      rw [Classical.not_forall] at h'
      obtain ⟨a, ha⟩ := h'
      exact ⟨a, ha⟩
    · intro ⟨a, ha⟩ hall
      exact ha ((key a).mp (hall a))

proof_of typeC_satisfaction_iffNoEq := typeC_satisfaction_iff S s C


proof_of typeD_satisfaction_iffNoEq := typeD_satisfaction_iff S s D


end LCS.FirstOrder.Gentzen.SignedFormulae
