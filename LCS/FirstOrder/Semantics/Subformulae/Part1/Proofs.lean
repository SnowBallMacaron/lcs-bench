import LCS.FirstOrder.Semantics.Subformulae.Part1

section

namespace LCS.FirstOrder.Semantics.Subformulae

open LCS.FirstOrder.Basic

open LCS.FirstOrder.Syntax

open LCS.FirstOrder.Syntax.Substitution

open LCS.FirstOrder.Syntax.Variables

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics

open LCS.FirstOrder.Semantics.Substitution (coincidenceLemma)

helper /-- A vacuous universal quantifier binds its own variable position. -/
theorem quantifierBindsAt_vacuous_binder :
    let L : Language := {
      funSymbols := Empty, funArity := Empty.elim, constSymbols := Empty,
      predSymbols := Bool, predArity := fun p => if p then 1 else 0 }
    let A : Formula L := Formula.all 0 (Formula.pred0 false rfl)
    quantifierBindsAt A [] (.binder []) := by
  exact ⟨rfl, ⟨[], rfl⟩⟩

helper /-- In ∀x₀(P ∧ ∀x₀ Q(x₀)), the outer quantifier binds both the inner
atom's occurrence of x₀ and the inner quantifier's binder position. -/
theorem quantifierBindsAt_nested_occurrences :
    let L : Language := {
      funSymbols := Empty, funArity := Empty.elim, constSymbols := Empty,
      predSymbols := Bool, predArity := fun p => if p then 1 else 0 }
    let A : Formula L := Formula.all 0
      (Formula.conj (Formula.pred0 false rfl)
        (Formula.all 0 (Formula.predN true (by decide) (fun _ => Term.var 0))))
    quantifierBindsAt A [] (.atom [0, 1, 0] 0 []) ∧
      quantifierBindsAt A [] (.binder [0, 1]) := by
  exact ⟨⟨rfl, ⟨[0, 1, 0], rfl⟩⟩, ⟨rfl, ⟨[0, 1], rfl⟩⟩⟩

helper /-- A normalized formula contains a quantifier: quantifierBinds q x A holds iff A
contains a subformula of the form FormulaN.all x B (if q = 0) or
FormulaN.ex x B (if q = 1). Uses IsSubformula to witness that A has
a subformula that is a quantifier binding variable x. -/
def quantifierBinds {L : Language} (q : Nat) (x : Nat)
    (A : FormulaN L) : Prop :=
  match q with
  | 0 => ∃ B : FormulaN L, IsSubformula (FormulaN.all x B) A
  | 1 => ∃ B : FormulaN L, IsSubformula (FormulaN.ex x B) A
  | _ => False

helper /-- Example 5.3.3: The displayed formula B is rectified: its free and
bound variables are disjoint, and its quantifier variables are distinct. -/
theorem exampleRectified_5_3_3_isRectified :
    isRectified exampleRectified_5_3_3 := by
  constructor
  · intro x
    dsimp [boundVarsFresh, exampleRectified_5_3_3, formulaFVN, formulaBVN,
      termFV, exampleLang_5_3_3, Set.iUnion, Set.union, Set.diff,
      Set.singleton, Set.empty, Membership.mem]
    simp only [Fin.exists_fin_two, Fin.exists_fin_one, vec2, termFV, Set.singleton]
    rintro ⟨hFV, hBV⟩
    simp only [false_or] at hBV
    rcases hBV with rfl | rfl | rfl <;> simp at hFV
  · simp [distinctQuantifierBindings, exampleRectified_5_3_3, formulaBVN,
      Membership.mem, Set.union, Set.singleton, Set.empty]

proof_of exampleRectified_5_3_3_equiv := by
  intro M s
  have evalPair (t : Assignment M) (x y : Nat) :
      (fun i : Fin (exampleLang_5_3_3.predArity ExPred_5_3_3.R) => termEval M t (vec2 (Term.var x) (Term.var y) i)) =
        vec2 (t x) (t y) := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  simp [exampleNonRectified_5_3_3, exampleRectified_5_3_3, formulaEvalN,
    evalPair, termEval, assignUpdate]


helper /-- Example 5.3.3 (companion): Demonstrates that renaming x to u in the
first conjunct preserves semantic equivalence, via alphaEquivUniv.
That is, forall x(Rxy => Px) is semantically equivalent to
forall u(Ruy => Pu) where u=2. -/
theorem exampleRenaming_x_to_u :
    universallyValidN (L := exampleLang_5_3_3)
      (FormulaN.conj
        (FormulaN.impl
          (FormulaN.all 0
            (FormulaN.impl
              (FormulaN.predN ExPred_5_3_3.R
                (vec2 (Term.var 0) (Term.var 1)))
              (FormulaN.predN ExPred_5_3_3.P
                (fun _ => Term.var 0))))
          (FormulaN.all 2
            (formulaSubstN
              (FormulaN.impl
                (FormulaN.predN ExPred_5_3_3.R
                  (vec2 (Term.var 0) (Term.var 1)))
                (FormulaN.predN ExPred_5_3_3.P
                  (fun _ => Term.var 0)))
              (Term.var 2) 0)))
        (FormulaN.impl
          (FormulaN.all 2
            (formulaSubstN
              (FormulaN.impl
                (FormulaN.predN ExPred_5_3_3.R
                  (vec2 (Term.var 0) (Term.var 1)))
                (FormulaN.predN ExPred_5_3_3.P
                  (fun _ => Term.var 0)))
              (Term.var 2) 0))
          (FormulaN.all 0
            (FormulaN.impl
              (FormulaN.predN ExPred_5_3_3.R
                (vec2 (Term.var 0) (Term.var 1)))
              (FormulaN.predN ExPred_5_3_3.P
                (fun _ => Term.var 0)))))) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  -- Both sides quantify over all domain elements a.
  -- LHS body under s[0:=a]: R(a, s 1) => P(a)
  -- RHS body is A[var 2/0] under s[2:=a]: R(a, s 1) => P(a)
  -- They agree because the substitution maps var 0 to var 2 and
  -- s[0:=a](0) = a = s[2:=a](2).
  suffices ∀ a : M.carrier,
    formulaEvalN M
      (FormulaN.impl
        (FormulaN.predN ExPred_5_3_3.R (vec2 (Term.var 0) (Term.var 1)))
        (FormulaN.predN ExPred_5_3_3.P (fun _ => Term.var 0)))
      (assignUpdate s 0 a) ↔
    formulaEvalN M
      (formulaSubstN
        (FormulaN.impl
          (FormulaN.predN ExPred_5_3_3.R (vec2 (Term.var 0) (Term.var 1)))
          (FormulaN.predN ExPred_5_3_3.P (fun _ => Term.var 0)))
        (Term.var 2) 0)
      (assignUpdate s 2 a) by
    exact ⟨fun h a => (this a).mp (h a), fun h a => (this a).mpr (h a)⟩
  intro a
  -- Both sides reduce to: R(a, s 1) → P(a)
  have hR_args : (fun i => termEval M (assignUpdate s 0 a) (vec2 (Term.var 0) (Term.var 1) i)) =
      (fun i => termEval M (assignUpdate s 2 a) (termSubst (vec2 (Term.var 0) (Term.var 1) i) (Term.var 2) 0)) := by
    funext ⟨k, hk⟩
    match k, hk with
    | 0, _ => simp [vec2, termSubst, termEval, assignUpdate]
    | 1, _ => simp [vec2, termSubst, termEval, assignUpdate]
  have hP_args : (fun (_ : Fin (exampleLang_5_3_3.predArity ExPred_5_3_3.P)) =>
      termEval M (assignUpdate s 0 a) (Term.var 0)) =
      (fun _ => termEval M (assignUpdate s 2 a) (termSubst (Term.var 0) (Term.var 2) 0)) := by
    funext _; simp [termSubst, termEval, assignUpdate]
  show formulaEvalN M
    (FormulaN.impl (FormulaN.predN ExPred_5_3_3.R (vec2 (Term.var 0) (Term.var 1)))
      (FormulaN.predN ExPred_5_3_3.P (fun _ => Term.var 0)))
    (assignUpdate s 0 a) ↔
    formulaEvalN M
    (formulaSubstN (FormulaN.impl (FormulaN.predN ExPred_5_3_3.R (vec2 (Term.var 0) (Term.var 1)))
      (FormulaN.predN ExPred_5_3_3.P (fun _ => Term.var 0))) (Term.var 2) 0)
    (assignUpdate s 2 a)
  have body_eq : formulaEvalN M
      (FormulaN.impl (FormulaN.predN ExPred_5_3_3.R (vec2 (Term.var 0) (Term.var 1)))
        (FormulaN.predN ExPred_5_3_3.P (fun _ => Term.var 0)))
      (assignUpdate s 0 a) =
    formulaEvalN M
      (formulaSubstN (FormulaN.impl (FormulaN.predN ExPred_5_3_3.R (vec2 (Term.var 0) (Term.var 1)))
        (FormulaN.predN ExPred_5_3_3.P (fun _ => Term.var 0))) (Term.var 2) 0)
      (assignUpdate s 2 a) := by
    simp only [formulaEvalN, formulaSubstN, Basic.implM]
    apply propext; apply imp_congr
    · exact hR_args ▸ Iff.rfl
    · exact hP_args ▸ Iff.rfl
  exact body_eq ▸ Iff.rfl

end LCS.FirstOrder.Semantics.Subformulae

end

section

namespace LCS.FirstOrder.Semantics.Subformulae

open LCS.FirstOrder.Basic

open LCS.FirstOrder.Syntax

open LCS.FirstOrder.Syntax.Substitution

open LCS.FirstOrder.Syntax.Variables

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics

open LCS.FirstOrder.Semantics.Substitution (coincidenceLemma)

open LCS.Propositional.Syntax

open LCS.Propositional.Semantics

helper /-- Example 5.3.4: The displayed proposition B is a tautology. -/
theorem examplePropFormula_5_3_4_tautology {α : Type} (P Q : α) :
    tautology (examplePropFormula_5_3_4 P Q) := by
  intro v
  exact ⟨fun h => ⟨h.mp, h.mpr⟩, fun h => ⟨h.1, h.2⟩⟩

helper /-- Example 5.3.4: The specified substitution sends B to the displayed A. -/
theorem exampleInstance_5_3_4_subst {L : Language} (P Q : PS0 L)
    (C D : Formula L) (x y : Nat) (sigma : PS0 L → Formula L)
    (hP : sigma P = Formula.all x C)
    (hQ : sigma Q = Formula.ex y (Formula.conj C D)) :
    propSubst sigma (examplePropFormula_5_3_4 P Q) = exampleInstance_5_3_4 C D x y := by
  simp [examplePropFormula_5_3_4, propSubst, exampleInstance_5_3_4, hP, hQ]

proof_of exampleInstance_5_3_4_inPROPL := ⟨examplePropFormula_5_3_4 P Q, sigma, examplePropFormula_5_3_4_tautology P Q,
    exampleInstance_5_3_4_subst P Q C D x y sigma hP hQ⟩








proof_of forall_not_inPROPL := by
  intro h
  exact inPROPL_propositionalSkeletonEval h


proof_of exists_conj_not_inPROPL := by
  intro h
  exact inPROPL_propositionalSkeletonEval h












helper /-- Lemma 5.3.4 (companion): Substitution of a variable free for i
agrees with updating the assignment at i to the value of that variable. -/
theorem formulaVarSubstEvalF {L : Language} (M : Structure L)
    (s : Assignment M) (A : Formula L) (i j : Nat)
    (hFree : isFreeFor (Term.var j) i A) :
    formulaEval M (formulaSubst A (Term.var j) i) s ↔
    formulaEval M A (assignUpdate s i (s j)) := by
-- BEGIN PROOF
  induction A generalizing s with
  | falsum => simp [formulaSubst, formulaEval]
  | pred0 _ _ => simp [formulaSubst, formulaEval]
  | predN P _ ts =>
    simp only [formulaSubst, formulaEval]
    have : (fun k => termEval M s (termSubst (ts k) (Term.var j) i)) =
           (fun k => termEval M (assignUpdate s i (s j)) (ts k)) :=
      funext fun k => termVarSubstEval M s (ts k) i j
    rw [this]
  | eq_ _ t1 t2 =>
    simp only [formulaSubst, formulaEval]
    rw [termVarSubstEval M s t1 i j, termVarSubstEval M s t2 i j]
  | conj A B ihA ihB =>
    simp only [isFreeFor] at hFree
    simp only [formulaSubst, formulaEval]
    exact and_congr (ihA s hFree.1) (ihB s hFree.2)
  | disj A B ihA ihB =>
    simp only [isFreeFor] at hFree
    simp only [formulaSubst, formulaEval]
    exact or_congr (ihA s hFree.1) (ihB s hFree.2)
  | impl A B ihA ihB =>
    simp only [isFreeFor] at hFree
    simp only [formulaSubst, formulaEval]
    exact imp_congr (ihA s hFree.1) (ihB s hFree.2)
  | equiv_ A B ihA ihB =>
    simp only [isFreeFor] at hFree
    simp only [formulaSubst, formulaEval]
    exact iff_congr (ihA s hFree.1) (ihB s hFree.2)
  | neg A ih =>
    simp only [isFreeFor] at hFree
    simp only [formulaSubst, formulaEval]
    exact not_congr (ih s hFree)
  | all k A ih =>
    simp only [isFreeFor] at hFree
    simp only [formulaSubst, formulaEval]
    by_cases hik : i = k
    · subst hik; simp; constructor <;> intro h a
      · have heq : assignUpdate (assignUpdate s i (s j)) i a = assignUpdate s i a :=
          funext fun x => by unfold assignUpdate; split <;> simp_all
        rw [heq]; exact h a
      · have heq : assignUpdate (assignUpdate s i (s j)) i a = assignUpdate s i a :=
          funext fun x => by unfold assignUpdate; split <;> simp_all
        rw [← heq]; exact h a
    · have hFreeA : isFreeFor (Term.var j) i A := by
        rcases hFree with rfl | ⟨_, h⟩
        · exact absurd rfl hik
        · exact h
      have hjk : k ≠ j := by
        intro heq
        rcases hFree with rfl | ⟨hne, _⟩
        · exact hik rfl
        · subst heq
          exact hne rfl
      simp [hik]; constructor <;> intro h a
      · have swap : assignUpdate (assignUpdate s i (s j)) k a =
            assignUpdate (assignUpdate s k a) i (s j) := by
          funext x; unfold assignUpdate
          by_cases hxk : x = k
          · subst hxk; simp [Ne.symm hik]
          · by_cases hxi : x = i
            · subst hxi; simp [hxk]
            · simp [hxk, hxi]
        rw [swap]
        have hjks : (assignUpdate s k a) j = s j := by
          unfold assignUpdate; simp [Ne.symm hjk]
        rw [← hjks]
        exact (ih (assignUpdate s k a) hFreeA).mp (h a)
      · have swap : assignUpdate (assignUpdate s i (s j)) k a =
            assignUpdate (assignUpdate s k a) i (s j) := by
          funext x; unfold assignUpdate
          by_cases hxk : x = k
          · subst hxk; simp [Ne.symm hik]
          · by_cases hxi : x = i
            · subst hxi; simp [hxk]
            · simp [hxk, hxi]
        have hjks : (assignUpdate s k a) j = s j := by
          unfold assignUpdate; simp [Ne.symm hjk]
        have ha := h a
        have combined : assignUpdate (assignUpdate s i (s j)) k a =
            assignUpdate (assignUpdate s k a) i ((assignUpdate s k a) j) := by
          rw [swap]; congr 1; exact hjks.symm
        rw [combined] at ha
        exact (ih (assignUpdate s k a) hFreeA).mpr ha
  | ex k A ih =>
    simp only [isFreeFor] at hFree
    simp only [formulaSubst, formulaEval]
    by_cases hik : i = k
    · subst hik; simp; constructor <;> intro ⟨a, ha⟩ <;> refine ⟨a, ?_⟩
      · have heq : assignUpdate (assignUpdate s i (s j)) i a = assignUpdate s i a :=
          funext fun x => by unfold assignUpdate; split <;> simp_all
        rw [heq]; exact ha
      · have heq : assignUpdate (assignUpdate s i (s j)) i a = assignUpdate s i a :=
          funext fun x => by unfold assignUpdate; split <;> simp_all
        rw [← heq]; exact ha
    · have hFreeA : isFreeFor (Term.var j) i A := by
        rcases hFree with rfl | ⟨_, h⟩
        · exact absurd rfl hik
        · exact h
      have hjk : k ≠ j := by
        intro heq
        rcases hFree with rfl | ⟨hne, _⟩
        · exact hik rfl
        · subst heq
          exact hne rfl
      simp [hik]; constructor <;> intro ⟨a, ha⟩ <;> refine ⟨a, ?_⟩
      · have swap : assignUpdate (assignUpdate s i (s j)) k a =
            assignUpdate (assignUpdate s k a) i (s j) := by
          funext x; unfold assignUpdate
          by_cases hxk : x = k
          · subst hxk; simp [Ne.symm hik]
          · by_cases hxi : x = i
            · subst hxi; simp [hxk]
            · simp [hxk, hxi]
        have hjks : (assignUpdate s k a) j = s j := by
          unfold assignUpdate; simp [Ne.symm hjk]
        rw [swap, ← hjks]
        exact (ih (assignUpdate s k a) hFreeA).mp ha
      · have swap : assignUpdate (assignUpdate s i (s j)) k a =
            assignUpdate (assignUpdate s k a) i (s j) := by
          funext x; unfold assignUpdate
          by_cases hxk : x = k
          · subst hxk; simp [Ne.symm hik]
          · by_cases hxi : x = i
            · subst hxi; simp [hxk]
            · simp [hxk, hxi]
        have hjks : (assignUpdate s k a) j = s j := by
          unfold assignUpdate; simp [Ne.symm hjk]
        have combined : assignUpdate (assignUpdate s i (s j)) k a =
            assignUpdate (assignUpdate s k a) i ((assignUpdate s k a) j) := by
          rw [swap]; congr 1; exact hjks.symm
        rw [combined] at ha
        exact (ih (assignUpdate s k a) hFreeA).mpr ha



proof_of alphaEquivUnivF := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    by_cases hij : i = j
    · subst hij
      constructor
      · intro h a
        have key := (formulaVarSubstEvalF M (assignUpdate s i a) A i i hFree).symm
        have : (assignUpdate s i a) i = a := by unfold assignUpdate; simp
        rw [this] at key
        have idem : assignUpdate (assignUpdate s i a) i a = assignUpdate s i a :=
          funext fun x => by unfold assignUpdate; split <;> simp_all
        rw [idem] at key; exact key.mp (h a)
      · intro h a
        have key := (formulaVarSubstEvalF M (assignUpdate s i a) A i i hFree).symm
        have : (assignUpdate s i a) i = a := by unfold assignUpdate; simp
        rw [this] at key
        have idem : assignUpdate (assignUpdate s i a) i a = assignUpdate s i a :=
          funext fun x => by unfold assignUpdate; split <;> simp_all
        rw [idem] at key; exact key.mpr (h a)
    · have hjNotFree : j ∉ formulaFV A := by
        intro hmem
        exact hFresh ⟨hmem, hij ∘ Eq.symm⟩
      constructor
      · intro h a
        have step1 := formulaVarSubstEvalF M (assignUpdate s j a) A i j hFree
        have step2 : (assignUpdate s j a) j = a := by
          unfold assignUpdate; simp
        rw [step2] at step1
        apply step1.mpr
        exact (coincidenceLemma M A
          (assignUpdate s i a) (assignUpdate (assignUpdate s j a) i a)
          (fun y hy => by
            unfold assignUpdate
            by_cases hyi : y = i
            · subst hyi; simp
            · simp [hyi]
              by_cases hyj : y = j
              · subst hyj; exact absurd hy hjNotFree
              · simp [hyj])).mp (h a)
      · intro h a
        have step1 := formulaVarSubstEvalF M (assignUpdate s j a) A i j hFree
        have step2 : (assignUpdate s j a) j = a := by
          unfold assignUpdate; simp
        rw [step2] at step1
        have from_subst := step1.mp (h a)
        exact (coincidenceLemma M A
          (assignUpdate (assignUpdate s j a) i a) (assignUpdate s i a)
          (fun y hy => by
            unfold assignUpdate
            by_cases hyi : y = i
            · subst hyi; simp
            · simp [hyi]
              by_cases hyj : y = j
              · subst hyj; exact absurd hy hjNotFree
              · simp [hyj])).mp from_subst


proof_of alphaEquivExF := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    by_cases hij : i = j
    · subst hij
      constructor
      · intro ⟨a, ha⟩; refine ⟨a, ?_⟩
        have key := (formulaVarSubstEvalF M (assignUpdate s i a) A i i hFree).symm
        have : (assignUpdate s i a) i = a := by unfold assignUpdate; simp
        rw [this] at key
        have idem : assignUpdate (assignUpdate s i a) i a = assignUpdate s i a :=
          funext fun x => by unfold assignUpdate; split <;> simp_all
        rw [idem] at key; exact key.mp ha
      · intro ⟨a, ha⟩; refine ⟨a, ?_⟩
        have key := (formulaVarSubstEvalF M (assignUpdate s i a) A i i hFree).symm
        have : (assignUpdate s i a) i = a := by unfold assignUpdate; simp
        rw [this] at key
        have idem : assignUpdate (assignUpdate s i a) i a = assignUpdate s i a :=
          funext fun x => by unfold assignUpdate; split <;> simp_all
        rw [idem] at key; exact key.mpr ha
    · have hjNotFree : j ∉ formulaFV A := by
        intro hmem; exact hFresh ⟨hmem, hij ∘ Eq.symm⟩
      constructor
      · intro ⟨a, ha⟩; refine ⟨a, ?_⟩
        have step1 := formulaVarSubstEvalF M (assignUpdate s j a) A i j hFree
        have step2 : (assignUpdate s j a) j = a := by unfold assignUpdate; simp
        rw [step2] at step1
        apply step1.mpr
        exact (coincidenceLemma M A
          (assignUpdate s i a) (assignUpdate (assignUpdate s j a) i a)
          (fun y hy => by
            unfold assignUpdate
            by_cases hyi : y = i
            · subst hyi; simp
            · simp [hyi]
              by_cases hyj : y = j
              · subst hyj; exact absurd hy hjNotFree
              · simp [hyj])).mp ha
      · intro ⟨a, ha⟩; refine ⟨a, ?_⟩
        have step1 := formulaVarSubstEvalF M (assignUpdate s j a) A i j hFree
        have step2 : (assignUpdate s j a) j = a := by unfold assignUpdate; simp
        rw [step2] at step1
        have from_subst := step1.mp ha
        exact (coincidenceLemma M A
          (assignUpdate (assignUpdate s j a) i a) (assignUpdate s i a)
          (fun y hy => by
            unfold assignUpdate
            by_cases hyi : y = i
            · subst hyi; simp
            · simp [hyi]
              by_cases hyj : y = j
              · subst hyj; exact absurd hy hjNotFree
              · simp [hyj])).mp from_subst


end LCS.FirstOrder.Semantics.Subformulae

end
