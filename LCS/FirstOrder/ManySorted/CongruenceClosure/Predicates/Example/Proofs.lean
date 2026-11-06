import LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.Example

section

namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates

open LCS.FirstOrder.ManySorted

open LCS.FirstOrder.ManySorted.Semantics

open LCS.FirstOrder.ManySorted.Equality

open LCS.FirstOrder.ManySorted.CongruenceClosure

open LCS.FirstOrder.ManySorted.CongruenceClosure.Decision

open LCS.Propositional.Semantics

proof_of exampleSeedPred_sortSupported := by
  -- REPAIR(T10-74): proof pending — Verify the sorts of the three printed seed pairs.
  sorry


proof_of exampleClosurePred_eq_equationClosure := by
  -- REPAIR(T10-74): proof pending — Prove closure equality by symmetry of the two data pairs.
  sorry


proof_of example_lift_applyF := by
  show msLiftTerm examplePredLanguage
      (MSTerm.func ExamplePredFunc.f (examplePredFArg t)) = _
  rw [msLiftTerm.eq_def, exampleLiftTf]
  dsimp only
  congr 1
  funext i
  obtain ⟨iv, hiv⟩ := i
  match iv, hiv with
  | 0, _ => rfl


proof_of example_lift_a := rfl


proof_of example_lift_fa := by
  show msLiftTerm examplePredLanguage (examplePredApplyF examplePredTerm_a) = _
  rw [example_lift_applyF]; rfl


proof_of example_lift_f3a := by
  show msLiftTerm examplePredLanguage
      (examplePredApplyF (examplePredApplyF examplePredTerm_fa)) = _
  rw [example_lift_applyF, example_lift_applyF]
  show exampleLiftTf (exampleLiftTf (msLiftTerm examplePredLanguage examplePredTerm_fa))
    = exampleLiftT3
  rw [example_lift_fa]; rfl


proof_of example_lift_f5a := by
  show msLiftTerm examplePredLanguage
      (examplePredApplyF (examplePredApplyF examplePredTerm_f3a)) = _
  rw [example_lift_applyF, example_lift_applyF, example_lift_f3a]; rfl

proof_of example_contains_f5a_eq_a := by
  have h : Decision.msConjunctContains examplePredConjunctionEncoded
      (MSFormula.eq_ (L := boolExtendedLanguage examplePredLanguage) rfl
        (some ExamplePredSort.iota)
        (msLiftTerm examplePredLanguage examplePredTerm_f5a)
        (msLiftTerm examplePredLanguage examplePredTerm_a)) := by
    unfold examplePredConjunctionEncoded examplePredConjunction
    simp only [msEncodeConjunction]
    exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  rwa [example_lift_f5a, example_lift_a] at h


proof_of example_sub_step := Decision.msTermSubterms_subterm_closed T (Sum.inl ExamplePredFunc.f)
    (exampleLiftFArg t) ⟨0, by decide⟩ h


proof_of example_subT5_T5 := Decision.msTermSubterms_self _


proof_of example_subT5_T4 := example_sub_step exampleLiftT4 example_subT5_T5


proof_of example_subT5_T3 := example_sub_step exampleLiftT3 example_subT5_T4


proof_of example_subT5_T2 := example_sub_step exampleLiftT2 example_subT5_T3


proof_of example_subT5_T1 := example_sub_step exampleLiftT1 example_subT5_T2


proof_of example_subT5_T0 := example_sub_step exampleLiftT0 example_subT5_T1


proof_of example_memTk := ⟨rfl, some ExamplePredSort.iota, exampleLiftT5, exampleLiftT0,
    Or.inl example_contains_f5a_eq_a, Or.inl h⟩

proof_of example_fa_eq_a := by
  -- REPAIR(T10-17): proof pending — Use sort-fiber symmetry and transitivity for the six data nodes.
  sorry


proof_of example_contains_Pa_eq_top := by
  unfold examplePredConjunctionEncoded examplePredConjunction
  simp only [msEncodeConjunction, msEncodeAtom]
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
  unfold examplePredTermP msPredAsFuncTerm
  congr 1
  apply congrArg (MSTerm.func (L := boolExtendedLanguage examplePredLanguage)
    (Sum.inr ⟨ExamplePredPred.P, by decide⟩))
  funext i
  obtain ⟨iv, hiv⟩ := i
  match iv, hiv with
  | 0, _ => rfl


proof_of example_contains_neg_Pfa_eq_top := by
  unfold examplePredConjunctionEncoded examplePredConjunction
  simp only [msEncodeConjunction, msEncodeNegAtom, msEncodeAtom]
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
  apply congrArg MSFormula.neg
  unfold examplePredTermP msPredAsFuncTerm
  congr 1
  apply congrArg (MSTerm.func (L := boolExtendedLanguage examplePredLanguage)
    (Sum.inr ⟨ExamplePredPred.P, by decide⟩))
  funext i
  obtain ⟨iv, hiv⟩ := i
  match iv, hiv with
  | 0, _ => rfl

proof_of example_memTop := ⟨rfl, MSBoolSort examplePredLanguage,
    examplePredTermP (msLiftTerm examplePredLanguage examplePredTerm_a),
    msTopConst examplePredLanguage, Or.inl example_contains_Pa_eq_top,
    Or.inr (Decision.msTermSubterms_self _)⟩


proof_of example_memPfa := ⟨rfl, MSBoolSort examplePredLanguage,
    examplePredTermP (msLiftTerm examplePredLanguage examplePredTerm_fa),
    msTopConst examplePredLanguage, Or.inr example_contains_neg_Pfa_eq_top,
    Or.inl (Decision.msTermSubterms_self _)⟩


proof_of example_fa_eq_a_lifted := by
  have e1 : exampleNodeFa = exampleNodeT1 :=
    node_eq_of_val_eq (congrArg
      (fun t => (⟨some ExamplePredSort.iota, t⟩ :
        Decision.MSTermSig (boolExtendedLanguage examplePredLanguage))) example_lift_fa)
  have e2 : exampleNodeA = exampleNodeT0 :=
    node_eq_of_val_eq (congrArg
      (fun t => (⟨some ExamplePredSort.iota, t⟩ :
        Decision.MSTermSig (boolExtendedLanguage examplePredLanguage))) example_lift_a)
  rw [e1, e2]; exact example_fa_eq_a

proof_of example_Pfa_top := by
  -- REPAIR(T10-17): proof pending — Compose the Boolean-sort closure facts using fiber transitivity.
  sorry


proof_of exampleCollisionPfa := by
  -- BEGIN PROOF
    -- The collision `P(f(a)) ↔* ⊤` is `example_Pfa_top`: build the f-tower
    -- congruence to `f(a) ~ a`, the predicate-congruence step to
    -- `P(f(a)) ~ P(a)`, then transitivity through the seed `P(a) ~ ⊤`. The two
    -- nodes are the `TERM(C')` bool nodes for `P(f(a))` and `⊤`.
    refine ⟨⟨⟨MSBoolSort examplePredLanguage,
        examplePredTermP (msLiftTerm examplePredLanguage examplePredTerm_fa)⟩,
        example_memPfa⟩,
      ⟨⟨MSBoolSort examplePredLanguage, msTopConst examplePredLanguage⟩, example_memTop⟩,
      ?_, rfl, ?_⟩
    · -- The node's term `examplePredTermP (msLiftTerm (f a))` IS the statement's
      -- `msPredAsFuncTerm P (fun i => hsort ▸ msLiftTerm (f a))` (the single
      -- argument index resolves the proof-irrelevant cast).
      show (⟨MSBoolSort examplePredLanguage,
          examplePredTermP (msLiftTerm examplePredLanguage examplePredTerm_fa)⟩ :
          Decision.MSTermSig (boolExtendedLanguage examplePredLanguage)) = _
      congr 1
      unfold examplePredTermP msPredAsFuncTerm
      apply congrArg (MSTerm.func (L := boolExtendedLanguage examplePredLanguage)
        (Sum.inr ⟨ExamplePredPred.P, by decide⟩))
      funext i
      obtain ⟨iv, hiv⟩ := i
      match iv, hiv with
      | 0, _ => rfl
    · exact example_Pfa_top


proof_of examplePredConjunction_isConjOfLiterals := by
  -- C = conj (eq_) (conj (eq_) (conj (pred P) (neg (pred P)))), all literals.
  unfold examplePredConjunction
  simp only [Decision.msIsConjunctionOfLiterals]
  refine Or.inr ⟨?_, Or.inr ⟨?_, Or.inr ⟨?_, ?_⟩⟩⟩
  · -- `f³(a) ≐ a` is atomic, hence a literal.
    exact Or.inl (by simp [MSFormula.isAtomic])
  · -- `f⁵(a) ≐ a` is atomic, hence a literal.
    exact Or.inl (by simp [MSFormula.isAtomic])
  · -- `P(a)` is an atomic predicate application, hence a literal.
    exact Or.inl (by simp [MSFormula.isAtomic])
  · -- `¬P(f(a))` is the negation of the atomic `P(f(a))`, hence a literal.
    exact Or.inr ⟨_, rfl, by simp [MSFormula.isAtomic]⟩


proof_of examplePredConjunction_noBot := by
  intro X hX _
  -- Walk the conjunction tree; each leaf is an `eq_`/`pred`/`neg pred`,
  -- none of which is `falsum` or `neg falsum`.
  unfold examplePredConjunction at hX
  simp only [Decision.msConjunctContains] at hX
  -- After unfolding, `hX` is a big disjunction of equalities `X = <leaf>`;
  -- in every case `X` is a concrete non-falsum formula.
  rcases hX with h | h | h | h | h | h | h <;>
    (subst h <;>
      constructor <;>
      simp [examplePredTerm_f3a, examplePredTerm_f5a,
        examplePredApplyF, examplePredTerm_a, examplePredTerm_fa,
        MSFormula.neg.injEq])


proof_of examplePredicateDecision := by
  -- BEGIN PROOF
    -- Apply Lemma 10.6.4 to the bool-sort collision `P(f(a)) ↔* ⊤`.
    apply (msUnsatisfiable_iff_collision_withPredicates examplePredLanguage
      examplePredConjunction examplePredConjunction_isConjOfLiterals
      examplePredConjunction_noBot).mpr
    obtain ⟨p, q, hp, hq, hcol⟩ := exampleCollisionPfa
    rw [exampleClosurePred_eq_equationClosure] at hcol
    refine ⟨MSBoolSort examplePredLanguage,
      msPredAsFuncTerm examplePredLanguage ExamplePredPred.P
        (fun i => by
          have hi : i.val < (examplePredLanguage.predArity ExamplePredPred.P).length := by
            have := i.isLt
            simpa [boolExtendedLanguage, boolExtendedFunRank, List.length_map]
              using this
          have hsort :
              (((boolExtendedLanguage examplePredLanguage).funRank
                (Sum.inr ⟨ExamplePredPred.P, by decide⟩)).1.get i) =
                some ((examplePredLanguage.predArity ExamplePredPred.P).get
                  ⟨i.val, hi⟩) := by
            simp [boolExtendedLanguage, boolExtendedFunRank,
              List.get_eq_getElem, List.getElem_map]
            all_goals exact List.getElem_map some
          exact hsort ▸ msLiftTerm examplePredLanguage examplePredTerm_fa),
      msTopConst examplePredLanguage, p, q, ?_, hp, hq, hcol⟩
    -- `¬(P(f(a)) ≐_bool ⊤)` is the last conjunct of the encoded conjunction.
    -- It is `msEncodeNegAtom`, i.e. `neg (msEncodeAtom …)` =
    -- `neg (eq_ rfl bool (msPredAsFuncTerm …) (msTopConst …))`, produced by the
    -- `neg (pred P ts)` clause of `msEncodeConjunction`.
    -- `¬(P(f(a)) ≐_bool ⊤)` is the rightmost conjunct of the encoded
    -- conjunction (the `neg (pred P (fa))` literal, encoded by the
    -- `neg (pred …)` clause of `msEncodeConjunction`). Membership is the
    -- rightmost branch of the nested `msConjunctContains` disjunction; the
    -- two occurrences of the predicate-application term differ only by a
    -- proof-irrelevant sort-cast, identified by `Subsingleton.elim`.
    show Decision.msConjunctContains
      (msEncodeConjunction examplePredLanguage examplePredConjunction) _
    unfold examplePredConjunction
    simp only [msEncodeConjunction, msEncodeNegAtom, msEncodeAtom,
      Decision.msConjunctContains]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
    -- Goal: `neg (P(f(a)) ≐ ⊤) = neg (P(f(a)) ≐ ⊤)`, the two predicate-arg
    -- families differing only by `examplePredPArg fa ⟨0,_⟩ = fa` (definitional
    -- once the single argument index is resolved) and a proof-irrelevant cast.
    apply congrArg MSFormula.neg
    unfold msPredAsFuncTerm
    congr 1
    apply congrArg (MSTerm.func (L := boolExtendedLanguage examplePredLanguage)
      (Sum.inr ⟨ExamplePredPred.P, by decide⟩))
    funext i
    obtain ⟨iv, hiv⟩ := i
    match iv, hiv with
    | 0, _ => rfl


end LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates

end
