import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.ValidityReduction

section

namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Decision

open LCS.FirstOrder.ManySorted

open LCS.FirstOrder.ManySorted.Semantics

open LCS.FirstOrder.ManySorted.Equality

open LCS.FirstOrder.ManySorted.CongruenceClosure

open LCS.Propositional.Semantics

proof_of msIsGeneratedTermAlgebra_univ := {
  nonempty := fun s => ⟨MSTerm.var s 0, trivial⟩
  closedFunc := fun _ _ _ => trivial
  closedConst := fun _ _ => trivial
  closedSubterm := fun _ _ _ _ => trivial }

proof_of sat_of_no_complementary_pair := by
  classical
  -- The Herbrand structure on the all-terms term algebra, with the
  -- positive-conjunct predicate valuation.
  let H : (s : L.SortType) → Set (MSTerm L s) := fun _ => (fun _ => True)
  have hTA : Gentzen.MSIsGeneratedTermAlgebra L H := msIsGeneratedTermAlgebra_univ L
  let S : Set (Gentzen.MSSignedFormula L) := trueConjunctsSet C
  let M : MSStructure L := Gentzen.msHintikkaStructure H S hTA
  let v : MSAssignment M := Gentzen.msIdentityAssignment H S hTA
  -- The atom-evaluation fact: a `pred P ts` atom evaluates to `T` iff it is
  -- a conjunct of `C` (via `msTermEvalIdentity` + the `interpPred` clause).
  have hAtomEval : ∀ (P : L.predSymbols)
      (ts : (i : Fin (L.predArity P).length) → MSTerm L ((L.predArity P).get i)),
      msFormulaEval M (MSFormula.pred P ts) v = BoolVal.T ↔
        msConjunctContains C (MSFormula.pred P ts) := by
    intro P ts
    have hargs : (fun i => msTermEval M v (ts i))
        = (fun i => (⟨ts i, trivial⟩ : { t // t ∈ H _ })) :=
      funext (fun i => Gentzen.msTermEvalIdentity (ts i) trivial)
    simp only [msFormulaEval, predM]
    rw [hargs]
    simp only [M, Gentzen.msHintikkaStructure]
    -- `interpPred … = if trueF (pred P ts) ∈ S then T else F`.
    constructor
    · intro h
      by_cases hmem : Gentzen.MSSignedFormula.trueF (MSFormula.pred P ts) ∈ S
      · obtain ⟨A, hAeq, hAcon⟩ := hmem
        have : A = MSFormula.pred P ts := by
          injection hAeq with hAeq; exact hAeq.symm
        rwa [this] at hAcon
      · rw [if_neg hmem] at h; exact absurd h (by decide)
    · intro hcon
      have hmem : Gentzen.MSSignedFormula.trueF (MSFormula.pred P ts) ∈ S :=
        ⟨MSFormula.pred P ts, rfl, hcon⟩
      rw [if_pos hmem]
  -- Every literal conjunct of `C` evaluates to `T`, by induction on the
  -- conjunction tree. We strengthen the statement: every conjunct `X` of `C`
  -- (with `C` a conj-of-literals, no-⊥, no-complementary-pair) evaluates `T`.
  have hLeaf : ∀ X, msConjunctContains C X → MSFormula.isLiteral X →
      msFormulaEval M X v = BoolVal.T := by
    intro X hXin hXlit
    rcases hXlit with hat | ⟨B, rfl, hBat⟩
    · -- `X` atomic: with no equality it is `falsum` or `pred …`; `hNoBot`
      -- excludes `falsum`, so it is a positive atom — a conjunct of `C`.
      cases X with
      | falsum => exact absurd rfl (hNoBot _ hXin (Or.inl trivial)).1
      | pred P ts => exact (hAtomEval P ts).mpr hXin
      | eq_ hL _ _ _ => exact absurd hL (by rw [hEq]; decide)
      | _ => exact absurd hat (by simp [MSFormula.isAtomic])
    · -- `X = ¬B`, `B` atomic: `B` is `falsum` (excluded by `hNoBot`) or a
      -- `pred …` atom; the latter would be a positive conjunct, giving a
      -- complementary pair (contradiction with `hno`), so its valuation is `F`.
      cases B with
      | falsum => exact absurd rfl (hNoBot _ hXin (Or.inr ⟨_, rfl, trivial⟩)).2
      | pred P ts =>
        rw [msFormulaEval_neg]
        by_cases hPcon : msConjunctContains C (MSFormula.pred P ts)
        · exact absurd ⟨MSFormula.pred P ts, hPcon, hXin, trivial⟩ hno
        · rw [show msFormulaEval M (MSFormula.pred P ts) v = BoolVal.F from by
              cases hev : msFormulaEval M (MSFormula.pred P ts) v with
              | T => exact absurd ((hAtomEval P ts).mp hev) hPcon
              | F => rfl]
          rfl
      | eq_ hL _ _ _ => exact absurd hL (by rw [hEq]; decide)
      | _ => exact absurd hBat (by simp [MSFormula.isAtomic])
  -- Now evaluate `C` itself by induction on its conjunction tree.
  have hConj : ∀ D, msIsConjunctionOfLiterals D →
      (∀ X, msConjunctContains D X → msConjunctContains C X) →
      msFormulaEval M D v = BoolVal.T := by
    intro D
    induction D with
    | conj A B _ ihB =>
      intro hDcl hsub
      rcases hDcl with hself | ⟨hAlit, hBcl⟩
      · -- a conjunction is never a literal.
        exact absurd hself (by
          simp [MSFormula.isLiteral, MSFormula.isAtomic])
      · rw [msFormulaEval_conj, hAnd_eq_T_iff]
        refine ⟨?_, ?_⟩
        · -- left conjunct `A` is a literal of `C`.
          have hAself : msConjunctContains A A := by
            cases A <;> first | rfl | exact Or.inl rfl
          have hAin : msConjunctContains (MSFormula.conj A B) A :=
            Or.inr (Or.inl hAself)
          exact hLeaf A (hsub A hAin) hAlit
        · -- right subtree `B` recurses.
          exact ihB hBcl (fun X hXin =>
            hsub X (Or.inr (Or.inr hXin)))
    | falsum =>
      intro hDcl hsub
      exact hLeaf _ (hsub _ (by rfl)) hDcl
    | pred P ts =>
      intro hDcl hsub
      exact hLeaf _ (hsub _ (by rfl)) hDcl
    | eq_ hL s t u =>
      intro hDcl hsub
      exact hLeaf _ (hsub _ (by rfl)) hDcl
    | disj A B _ _ =>
      intro hDcl hsub
      exact hLeaf _ (hsub _ (by rfl)) hDcl
    | impl A B _ _ =>
      intro hDcl hsub
      exact hLeaf _ (hsub _ (by rfl)) hDcl
    | equiv_ A B _ _ =>
      intro hDcl hsub
      exact hLeaf _ (hsub _ (by rfl)) hDcl
    | neg A _ =>
      intro hDcl hsub
      exact hLeaf _ (hsub _ (by rfl)) hDcl
    | all s i A _ =>
      intro hDcl hsub
      exact hLeaf _ (hsub _ (by rfl)) hDcl
    | ex s i A _ =>
      intro hDcl hsub
      exact hLeaf _ (hsub _ (by rfl)) hDcl
  exact ⟨M, v, hConj C hClit (fun _ h => h)⟩

proof_of msValid_reduces_to_conjunction_unsat := by
  -- BEGIN PROOF
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- (1) DNF existence: `B := toDNF A` is a DNF (`msIsDNF_toDNF`) and
      -- `A ≡ B` is valid because `toDNF A` evaluates exactly like `A` on
      -- every structure/assignment (`eval_toDNF`).
      intro A hA
      refine ⟨toDNF A, msIsDNF_toDNF A hA, ?_⟩
      intro M v
      rw [msFormulaEval_equiv, eval_toDNF M v A hA]
      -- `hEquiv x x = T`.
      cases msFormulaEval M A v <;> rfl
    · -- (2) validity via unsatisfiability of the negation's DNF.
      -- From `(¬A) ≡ B` valid: `eval B v = hNeg (eval A v)` for all `M, v`.
      intro A B _ _ hequiv
      have hBval : ∀ (M : MSStructure L) (v : MSAssignment M),
          msFormulaEval M B v = hNeg (msFormulaEval M A v) := by
        intro M v
        have h := hequiv M v
        rw [msFormulaEval_equiv, msFormulaEval_neg] at h
        -- `hEquiv (hNeg (eval A)) (eval B) = T` forces equality.
        revert h
        cases msFormulaEval M A v <;> cases msFormulaEval M B v <;>
          simp [hEquiv, hNeg]
      constructor
      · -- `msValid A → msUnsatisfiable B`.
        intro hvalid
        rintro ⟨M, v, hBv⟩
        rw [hBval M v, hvalid M v] at hBv
        exact absurd hBv (by decide)
      · -- `msUnsatisfiable B → msValid A`.
        intro hunsat M v
        -- if `eval A v = F`, then `eval B v = hNeg F = T`, a model of `B` —
        -- contradicting unsatisfiability; so `eval A v = T`.
        cases hA' : msFormulaEval M A v with
        | T => rfl
        | F =>
          have hBT : msFormulaEval M B v = BoolVal.T := by
            rw [hBval M v, hA']; rfl
          exact (hunsat ⟨M, v, hBT⟩).elim
    · -- (3) DNF unsatisfiability criterion.
      intro B _
      constructor
      · -- unsat ⇒ every disjunct unsat (a satisfiable disjunct would make
        -- `B` satisfiable via `disjunctOf_eval`).
        intro hunsat Ci hdis
        rintro ⟨M, v, hCi⟩
        exact hunsat ⟨M, v, disjunctOf_eval M v B Ci hdis hCi⟩
      · -- REPAIR(T10-30): proof pending — a satisfied DNF has a satisfied conjunction leaf.
        sorry
    · -- (4) no-equality trivial case.
      -- The BACKWARD direction (a complementary pair forces unsatisfiability)
      -- is sound: a model satisfying the conjunction would have to satisfy both
      -- `P` and `¬P`, impossible. The FORWARD direction (unsatisfiable ⇒
      -- complementary pair) uses the contrapositive: with the `hNoBot`
      -- precondition (no bare `⊥`/`¬⊥` literal — issue c3de0858), a
      -- conjunction of literals with NO complementary pair is satisfied by the
      -- Herbrand model (`sat_of_no_complementary_pair`), contradicting
      -- unsatisfiability.
      intro C hEq hClit hNoBot
      constructor
      · -- forward: unsatisfiable ⇒ complementary pair, by contraposition via
        -- the Herbrand satisfaction lemma.
        intro hunsat
        refine Classical.byContradiction fun hno => ?_
        exact hunsat (sat_of_no_complementary_pair hEq C hClit hNoBot hno)
      · -- backward: a complementary atomic pair `P, ¬P` in `C` makes `C`
        -- unsatisfiable, since any model would satisfy both `P` and `¬P`.
        rintro ⟨P, hPin, hnPin, _⟩
        rintro ⟨M, v, hCeval⟩
        have hPeval : msFormulaEval M P v = BoolVal.T :=
          conjunctContains_eval M v C P hPin hCeval
        have hnPeval : msFormulaEval M (MSFormula.neg P) v = BoolVal.T :=
          conjunctContains_eval M v C (MSFormula.neg P) hnPin hCeval
        rw [msFormulaEval_neg, hPeval] at hnPeval
        exact absurd hnPeval (by decide)

end LCS.FirstOrder.ManySorted.CongruenceClosure.Decision

end
