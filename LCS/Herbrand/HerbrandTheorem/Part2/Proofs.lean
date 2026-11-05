import LCS.Herbrand.HerbrandTheorem.Part2

section

namespace LCS.Herbrand.HerbrandTheorem

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.Semantics.Subformulae

open LCS.Herbrand.PrenexForm

open LCS.Herbrand.SharpenedHauptsatz.Theorem

open LCS.CutElim.LK

open LCS.CutElim.LKe.Equivalence

open LCS.FirstOrder.Gentzen

open LCS.CutElim.Interpolation.Equality

proof_of groundSequentExample_eq_substitution := by
  simp only [functionalFormExample_7_5_2, groundSequentExample_7_5_2,
    skolemExampleGroundSubstitution, prenexPrefix, prenexMatrix,
    Substitution.applyFormula, vec2, List.map_cons, List.map_nil,
    List.cons.injEq, and_true, LCS.FirstOrder.SyntaxN.FormulaN.neg.injEq,
    LCS.FirstOrder.SyntaxN.FormulaN.conj.injEq]
  refine ⟨True.intro, True.intro, ?_, ?_, ?_, ?_⟩
  all_goals
    apply congrArg (LCS.FirstOrder.SyntaxN.FormulaN.predN _)
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl


helper /-- Definition 7.5.3 (counterexamples): the concrete atom P(s,t). -/
def substitutionExampleAtom (s t : Term substitutionExampleLang) : FormulaN substitutionExampleLang :=
  .predN () (vec2 s t)

helper /-- Definition 7.5.3: the formula P(x,y), with x=0 and y=1. -/
def sequentialDifferenceFormula : FormulaN substitutionExampleLang :=
  substitutionExampleAtom (.var 0) (.var 1)

helper /-- Definition 7.5.3: x↦y and y↦a, fixing every other variable. -/
def sequentialDifferenceSubstitution : Substitution substitutionExampleLang
  | 0 => .var 1
  | 1 => .const false
  | x => .var x

helper /-- Definition 7.5.3: both changed variables occur in the formula; the exact
finite support is enumerated once each in the displayed order x,y. -/
theorem sequentialDifferenceSupport :
    Substitution.ExactSupportEnumeration sequentialDifferenceSubstitution [0, 1] := by
  constructor
  · decide
  · intro x
    cases x with
    | zero => simp [Substitution.support, sequentialDifferenceSubstitution]
    | succ x => cases x with
      | zero => simp [Substitution.support, sequentialDifferenceSubstitution]
      | succ x => simp [Substitution.support, sequentialDifferenceSubstitution]

helper /-- Definition 7.5.3: the sequential/simultaneous witness satisfies every
finite-support, actual-free-support, bound-exclusion and free-for condition. -/
theorem sequentialDifferenceAdmissible :
    Substitution.Admissible sequentialDifferenceSubstitution sequentialDifferenceFormula := by
  refine ⟨⟨[0, 1], fun x => (sequentialDifferenceSupport.2 x).symm⟩, ?_, ?_, ?_⟩
  · intro x hx
    have h := (sequentialDifferenceSupport.2 x).mpr hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact ⟨(0 : Fin 2), rfl⟩
    · exact ⟨(1 : Fin 2), rfl⟩
  · intro x _
    simp [sequentialDifferenceFormula, substitutionExampleAtom, formulaBVN,
      Membership.mem, Set.empty]
  · intro x _
    trivial

helper /-- Definition 7.5.3: the sequential witness is P(a,a), whereas the admissible
simultaneous instance is P(y,a). The newly inserted y is changed by the second
sequential step, but simultaneous substitution does not revisit its images. -/
theorem sequentialDifferenceValues :
    Substitution.applySequential sequentialDifferenceSubstitution sequentialDifferenceFormula [0, 1] =
      substitutionExampleAtom (.const false) (.const false) ∧
    Substitution.applyInstance sequentialDifferenceSubstitution sequentialDifferenceFormula
      sequentialDifferenceAdmissible = substitutionExampleAtom (.var 1) (.const false) := by
  constructor
  all_goals
    apply congrArg (FormulaN.predN (L := substitutionExampleLang) ())
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl

proof_of sequentialSubstitution_canDiffer := by
  refine ⟨sequentialDifferenceSubstitution, sequentialDifferenceFormula,
    sequentialDifferenceAdmissible, [0, 1], sequentialDifferenceSupport, ?_⟩
  rw [sequentialDifferenceValues.1, sequentialDifferenceValues.2]
  intro h
  have h0 := congrArg (fun A : FormulaN substitutionExampleLang => match A with
    | .predN _ ts => ts ⟨0, by change 0 < 2; decide⟩
    | _ => .var 0) h
  cases h0


helper /-- Definition 7.5.3: the two source-associated substitutions xᵢ↦a, for
indices i=0,1. Every other variable remains fixed. -/
def substitutionCollisionMap (i : Fin 2) : Substitution substitutionExampleLang :=
  fun x => if x = i.val then .const false else .var x

helper /-- Definition 7.5.3: the exact singleton support of each collision witness. -/
theorem substitutionCollisionSupport (i : Fin 2) (x : Nat) :
    Substitution.support (substitutionCollisionMap i) x ↔ x = i.val := by
  by_cases h : x = i.val
  · simp [Substitution.support, substitutionCollisionMap, h]
  · simp [Substitution.support, substitutionCollisionMap, h]

helper /-- Definition 7.5.3: each singleton substitution is admissible on P(xᵢ,xᵢ). -/
theorem substitutionCollisionAdmissible (i : Fin 2) :
    Substitution.Admissible (substitutionCollisionMap i)
      (substitutionExampleAtom (.var i.val) (.var i.val)) := by
  refine ⟨⟨[i.val], ?_⟩, ?_, ?_, ?_⟩
  · intro x
    simpa using substitutionCollisionSupport i x
  · intro x hx
    have h := (substitutionCollisionSupport i x).mp hx
    subst x
    exact ⟨(0 : Fin 2), rfl⟩
  · intro x _
    simp [substitutionExampleAtom, formulaBVN, Membership.mem, Set.empty]
  · intro x _
    trivial

helper /-- Definition 7.5.3: the two concrete admissible pairs, indexed by their
source occurrence, rather than recovered from their coincident instance. -/
def substitutionCollisionPair (i : Fin 2) : SubstitutionPair substitutionExampleLang :=
  ⟨substitutionExampleAtom (.var i.val) (.var i.val),
    substitutionCollisionMap i, substitutionCollisionAdmissible i⟩

helper /-- Definition 7.5.3: explicit source association for the two pairs:
∃x P(x,x) and ∃y P(y,y), with distinct source indices/binders 0 and 1. -/
def substitutionCollisionSource (i : Fin 2) : FormulaN substitutionExampleLang :=
  .ex i.val (substitutionExampleAtom (.var i.val) (.var i.val))

helper /-- Definition 7.5.3: each pair is the matrix/assignment of its retained
existential source, and that source is a closed sentence. This asserts the
association, not unique recovery of the source from an instance. -/
theorem substitutionCollisionSourceAssociation (i : Fin 2) :
    (substitutionCollisionPair i).formula = prenexMatrix (substitutionCollisionSource i) ∧
    prenexPrefix (substitutionCollisionSource i) = [(.existential, i.val)] ∧
    Substitution.IsExistentialPrefixAssignment (substitutionCollisionPair i).subst
      (substitutionCollisionSource i) ∧
    formulaFVN (substitutionCollisionSource i) = ∅ := by
  refine ⟨rfl, rfl, ⟨?_, (substitutionCollisionAdmissible i).finiteSupport, ?_⟩, ?_⟩
  · trivial
  · intro x hx
    have h := (substitutionCollisionSupport i x).mp hx
    simp [substitutionCollisionSource, prenexPrefix, substitutionExampleAtom, h]
  · have hv : vec2 (Term.var (L := substitutionExampleLang) i.val) (.var i.val) =
        fun _ : Fin 2 => .var i.val := by
      funext ⟨j, hj⟩
      match j, hj with
      | 0, _ => rfl
      | 1, _ => rfl
    funext x
    apply propext
    simp [substitutionCollisionSource, substitutionExampleAtom, formulaFVN,
      hv, termFV, Membership.mem, Set.iUnion, Set.diff, Set.singleton, Set.empty]

helper /-- Definition 7.5.3: both concrete admissible pairs yield exactly P(a,a). -/
theorem substitutionCollisionInstance (i : Fin 2) :
    (substitutionCollisionPair i).substitutionInstance =
      substitutionExampleAtom (.const false) (.const false) := by
  apply congrArg (FormulaN.predN (L := substitutionExampleLang) ())
  funext ⟨j, hj⟩
  match j, hj with
  | 0, _ => simp [SubstitutionPair.substitutionInstance, substitutionCollisionPair,
      substitutionExampleAtom, Substitution.applyInstance, Substitution.applyTerm,
      substitutionCollisionMap, vec2]
  | 1, _ => simp [SubstitutionPair.substitutionInstance, substitutionCollisionPair,
      substitutionExampleAtom, Substitution.applyInstance, Substitution.applyTerm,
      substitutionCollisionMap, vec2]

helper /-- Definition 7.5.3: the source-indexed witnesses are unequal as pairs and
have unequal source sentences, despite their equal substitution instances. -/
theorem substitutionCollisionWitnesses :
    substitutionCollisionPair 0 ≠ substitutionCollisionPair 1 ∧
    (substitutionCollisionPair 0).substitutionInstance =
      (substitutionCollisionPair 1).substitutionInstance ∧
    substitutionCollisionSource 0 ≠ substitutionCollisionSource 1 := by
  refine ⟨?_, (substitutionCollisionInstance 0).trans (substitutionCollisionInstance 1).symm, ?_⟩
  · intro h
    have h0 := congrArg (fun p : SubstitutionPair substitutionExampleLang => match p.formula with
      | .predN _ ts => ts ⟨0, by change 0 < 2; decide⟩
      | _ => .var 0) h
    cases h0
  · intro h
    cases h

helper /-- Definition 7.5.3: distinct admissible substitution pairs can have the same
instance. Their source association is separately retained by the witness family. -/
theorem substitutionPairs_canShareInstance :
    ∃ p q : SubstitutionPair substitutionExampleLang,
      p ≠ q ∧ p.substitutionInstance = q.substitutionInstance :=
  ⟨substitutionCollisionPair 0, substitutionCollisionPair 1,
    substitutionCollisionWitnesses.1, substitutionCollisionWitnesses.2.1⟩

helper /-- Construct finite names by first-occurrence indices above all source
variables. Equality is supplied for the local term lookup; no hashes are used. -/
def mkFreshTermNames {L : Language} (Γ : List (FormulaN L))
    [DecidableEq (Term (validitySkolemLanguage Γ))]
    (terms : List (Term (validitySkolemLanguage Γ))) : FreshTermNames Γ terms where
  name := fun t _ => (sourceVariableIndices Γ).foldl Nat.max 0 + 1 + terms.idxOf t
  injective := by
    intro t u ht hu he
    have hi : terms.idxOf t = terms.idxOf u := by omega
    have ht' := List.getElem_idxOf (List.idxOf_lt_length_of_mem ht)
    have hu' := List.getElem_idxOf (List.idxOf_lt_length_of_mem hu)
    have hf : (⟨terms.idxOf t, List.idxOf_lt_length_of_mem ht⟩ : Fin terms.length) =
        ⟨terms.idxOf u, List.idxOf_lt_length_of_mem hu⟩ := Fin.ext hi
    exact ht'.symm.trans ((congrArg terms.get hf).trans hu')
  fresh := by
    intro t ht x hx
    have bound (xs : List Nat) : ∀ n, x ≤ n ∨ x ∈ xs → x ≤ xs.foldl Nat.max n := by
      induction xs with
      | nil => intro n h; simpa using h
      | cons a xs ih =>
        intro n h
        apply ih (max n a)
        rcases h with hn | hm
        · exact Or.inl (Nat.le_trans hn (Nat.le_max_left n a))
        · rcases List.mem_cons.mp hm with he | hm
          · subst a
            exact Or.inl (Nat.le_max_right n x)
          · exact Or.inr hm
    have hxBound := bound (sourceVariableIndices Γ) 0 (Or.inr hx)
    omega

helper /-- Finite fresh naming is available for every finite proof-local term list.
This concerns no injection of the entire term universe into Nat. -/
def newVariable_injective_assumption (L : Language) : Prop :=
  ∀ (Γ : List (FormulaN L)) (terms : List (Term (validitySkolemLanguage Γ))),
    Nonempty (FreshTermNames Γ terms)

helper /-- Finite fresh-name availability imposes no restriction on the source
language or sequent. Classical decidability is used only in this existence proof. -/
theorem newVariable_injective_available (L : Language) :
    newVariable_injective_assumption L := by
  classical
  intro Γ terms
  exact ⟨mkFreshTermNames Γ terms⟩

proof_of sigmaMatrixTerm_mem := by
  unfold sigmaMatrixRequiredTerms
  apply List.mem_flatMap.mpr
  refine ⟨p, List.mem_ofFn.mpr ⟨p, rfl⟩, ?_⟩
  split <;> rename_i hp
  · exact List.mem_singleton.mpr rfl
  · cases h.symm.trans hp


helper /-- Explicit completion of the proof's HT list by the terms requested by the
selected σ-matrix. HT alone need not contain a term for a vacuous universal.
The original proof terms precede the added terms, so their first indices stay
fixed. This completes a proof-local naming domain, not the whole term universe. -/
def mkSigmaMatrixNames {L : Language} {Γ : List (FormulaN L)}
    [DecidableEq (Term (validitySkolemLanguage Γ))]
    (sd : SkolemData L Γ) (j : Fin Γ.length)
    (sigma : Substitution (validitySkolemLanguage Γ))
    (proofTerms : List (Term (validitySkolemLanguage Γ))) :
    FreshTermNames Γ (proofTerms ++ sigmaMatrixRequiredTerms sd j sigma) :=
  mkFreshTermNames Γ _

helper /-- The explicit finite completion covers all requests, including missing HT terms. -/
theorem mkSigmaMatrixNames_covers {L : Language} {Γ : List (FormulaN L)}
    [DecidableEq (Term (validitySkolemLanguage Γ))]
    (sd : SkolemData L Γ) (j : Fin Γ.length)
    (sigma : Substitution (validitySkolemLanguage Γ))
    (proofTerms : List (Term (validitySkolemLanguage Γ))) :
    SigmaMatrixNamesCover sd j sigma (mkSigmaMatrixNames sd j sigma proofTerms) :=
  fun _ ht => List.mem_append.mpr (Or.inr ht)

helper /-- Appending missing requirements preserves the canonical names already
assigned to the original proof terms. -/
theorem mkFreshTermNames_append {L : Language} (Γ : List (FormulaN L))
    [DecidableEq (Term (validitySkolemLanguage Γ))]
    (terms extra : List (Term (validitySkolemLanguage Γ)))
    (t : Term (validitySkolemLanguage Γ)) (ht : t ∈ terms) :
    newVariable (mkFreshTermNames Γ (terms ++ extra)) t
      (List.mem_append.mpr (Or.inl ht)) =
      newVariable (mkFreshTermNames Γ terms) t ht := by
  simp [newVariable, mkFreshTermNames, List.idxOf_append, ht]

proof_of sigmaMatrix_succ := by
  simp only [sigmaMatrix, sigmaMatrix.stage, dite_eq_left hi]


helper /-- Lemma 7.5.1 (helper): If -> B is LK-provable, then
    -> forall y B is LK-provable. Applies the allRight rule with
    eigenvariable y. The eigenvariable condition is satisfied because
    y is not free in all y B. -/
theorem folkProvable_allRight {L : Language}
    (y : Nat) (B : FormulaN L)
    (hprov : folkProvable (Sequent.mk [] [B])) :
    folkProvable (Sequent.mk [] [FormulaN.all y B]) := by
-- BEGIN PROOF
  obtain ⟨t⟩ := hprov
  have hfresh :
      ∀ F ∈ (Sequent.mk [] ([] ++ [FormulaN.all y B])).antecedent ++
          (Sequent.mk [] ([] ++ [FormulaN.all y B])).succedent,
        y ∉ formulaFVN F := by
    intro F hF
    simp only [List.nil_append, List.mem_singleton] at hF
    subst F
    rintro ⟨_, hy⟩
    exact hy rfl
  have t' :
      FOLKProofTree
        (Sequent.mk [] [formulaSubstN B (Term.var y) y]) := by
    simpa only [formulaSubstN_var_self] using t
  exact ⟨.onePremise
    (.allRight y y B [] [] hfresh
      (LCS.CutElim.Interpolation.isFreeForN_var_self B y))
    t'⟩

helper /-- Lemma 7.5.1 (helper): If -> forall y B is LK-provable, then
    -> B is LK-provable. Uses cut with the derivation
    [forall y B] -> [B] obtained from allLeft + axiom. -/
theorem folkProvable_allLeft_cut {L : Language}
    (y : Nat) (B : FormulaN L)
    (hprov : folkProvable (Sequent.mk [] [FormulaN.all y B])) :
    folkProvable (Sequent.mk [] [B]) := by
-- BEGIN PROOF
  obtain ⟨t⟩ := hprov
  have tAx : FOLKProofTree (Sequent.mk [B] [B]) :=
    .axiom_ _ ⟨B, rfl, rfl⟩
  have tSub :
      FOLKProofTree
        (Sequent.mk [formulaSubstN B (Term.var y) y] [B]) := by
    simpa only [formulaSubstN_var_self] using tAx
  have tAllLeft :
      FOLKProofTree (Sequent.mk [FormulaN.all y B] [B]) :=
    .onePremise
      (.allLeft (Term.var y) y B [] [B]
        (LCS.CutElim.Interpolation.isFreeForN_var_self B y))
      tSub
  exact ⟨by
    simpa using
      FOLKProofTree.twoPremise
        (.cut (FormulaN.all y B) [] [] [] [B]) t tAllLeft⟩

helper /-- Lemma 7.5.1 (helper): For any formula A and variable list fvs,
    -> A is LK-provable iff -> universalClosure A fvs is LK-provable.
    Proved by induction on fvs using folkProvable_allRight (forward)
    and folkProvable_allLeft_cut (backward). -/
theorem universalClosure_iff_folkProvable {L : Language}
    (A : FormulaN L) (fvs : List Nat) :
    folkProvable (Sequent.mk [] [A]) ↔
    folkProvable (Sequent.mk [] [universalClosure A fvs]) := by
-- BEGIN PROOF
  induction fvs with
  | nil =>
      simp only [universalClosure, List.foldr_nil]
  | cons y ys ih =>
      constructor
      · intro hprov
        simpa only [universalClosure, List.foldr_cons] using
          folkProvable_allRight y (universalClosure A ys) (ih.mp hprov)
      · intro hprov
        apply ih.mpr
        apply folkProvable_allLeft_cut y (universalClosure A ys)
        simpa only [universalClosure, List.foldr_cons] using hprov

helper /-- Lemma 7.5.1 (LK variant): Let A be a rectified formula with
    FV(A) = {y_1, ..., y_n}. The sequent -> A is LK-provable if and
    only if the sequent -> forall y_1 ... forall y_n A is LK-provable.

    Stated as a biconditional between provability of the sequent with
    A as sole succedent and provability of the sequent with the
    universal closure of A.

    STANDING ASSUMPTION #2 (§5.3.6+): formulae are rectified; encoded
    by `hRect`.
    STANDING ASSUMPTION #11 (§5.4-5.5): LK is for languages without
    equality; encoded by `hNoEq : L.withoutEquality`.

    Proof: By induction on the list of free variables fvs. Each
    forward step applies allRight (the eigenvariable y is not free in
    all y B). Each backward step uses cut with allLeft + axiom to
    strip one universal quantifier. -/
theorem universal_closure_provability_iff_LK {L : Language}
    (A : FormulaN L)
    (hRect : isRectified A)
    (fvs : List Nat)
    (hFVs : ∀ x, x ∈ fvs ↔ Membership.mem (formulaFVN A) x)
    (hNoEq : L.withoutEquality) :
    folkProvable (Sequent.mk [] [A]) ↔
    folkProvable
      (Sequent.mk [] [universalClosure A fvs]) := by
-- BEGIN PROOF
  clear hRect hFVs hNoEq
  exact universalClosure_iff_folkProvable A fvs

helper /-- Lemma 7.5.1 (LKe variant): The same biconditional holds for
    LKe-provability: the sequent -> A is LKe-provable if and only if
    the sequent -> forall y_1 ... forall y_n A is LKe-provable,
    provided A is rectified. LKe is the sequent calculus for languages
    with equality (§6.3), so no no-equality hypothesis is required.

    STANDING ASSUMPTION #2 (§5.3.6+): formulae are rectified; encoded
    by `hRect`. -/
theorem universal_closure_provability_iff_LKe {L : Language}
    (A : FormulaN L)
    (hRect : isRectified A)
    (fvs : List Nat)
    (hFVs : ∀ x, x ∈ fvs ↔ Membership.mem (formulaFVN A) x) :
    lkeProvable (Sequent.mk [] [A]) ↔
    lkeProvable
      (Sequent.mk [] [universalClosure A fvs]) := by
-- BEGIN PROOF
  clear hRect hFVs
  have lkeProvable_all_iff (y : Nat) (B : FormulaN L) :
      lkeProvable (Sequent.mk [] [B]) ↔
      lkeProvable (Sequent.mk [] [FormulaN.all y B]) := by
    constructor
    · intro hprov
      apply lkeProvable_of_universally_valid
      intro M s
      simp only [LCS.FirstOrder.SemanticsN.formulaEvalN]
      intro a
      have hvalid := lkeProvable_valid (Sequent.mk [] [B]) hprov
      simpa using hvalid M (assignUpdate s y a) (by simp)
    · intro hprov
      apply lkeProvable_of_universally_valid
      intro M s
      have hvalid :=
        lkeProvable_valid (Sequent.mk [] [FormulaN.all y B]) hprov
      have hall :
          LCS.FirstOrder.SemanticsN.formulaEvalN M (FormulaN.all y B) s := by
        simpa using hvalid M s (by simp)
      simp only [LCS.FirstOrder.SemanticsN.formulaEvalN] at hall
      have hself : assignUpdate s y (s y) = s := by
        funext x
        simp only [assignUpdate]
        split
        · rename_i hxy
          subst x
          rfl
        · rfl
      simpa only [hself] using hall (s y)
  induction fvs with
  | nil =>
      simp only [universalClosure, List.foldr_nil]
  | cons y ys ih =>
      constructor
      · intro hprov
        simpa only [universalClosure, List.foldr_cons] using
          (lkeProvable_all_iff y (universalClosure A ys)).mp (ih.mp hprov)
      · intro hprov
        apply ih.mpr
        apply (lkeProvable_all_iff y (universalClosure A ys)).mpr
        simpa only [universalClosure, List.foldr_cons] using hprov

proof_of lemma_7_5_1 := by
  -- BEGIN PROOF
  refine ⟨fun hNoEq => ?_, ?_⟩
  · exact universal_closure_provability_iff_LK A hRect fvs hFVs hNoEq
  · exact universal_closure_provability_iff_LKe A hRect fvs hFVs


proof_of sequent_disjunction_provability_iff_LK := by
  -- REPAIR(T7-91): proof pending
  sorry


proof_of sequent_disjunction_provability_iff_LKe := by
  -- REPAIR(T7-91): proof pending
  sorry


proof_of sequent_sentence_reduction_LK := by
  let D := sequentDisjunction s hNonempty
  let A := rectify D
  let fvs := (formulaFreeVarIndices A).eraseDups
  have hPreparation :
      (∀ x, x ∈ fvs ↔ Membership.mem (formulaFVN A) x) ∧
      FormulaN.isSentence (universalClosure A fvs) ∧
      (folkProvable (Sequent.mk [] [D]) ↔ folkProvable (Sequent.mk [] [A])) := by
    -- REPAIR(T7-92): proof pending
    sorry
  refine ⟨hPreparation.2.1, ?_⟩
  exact (sequent_disjunction_provability_iff_LK hL s hNonempty).trans
    (hPreparation.2.2.trans ((lemma_7_5_1 A (rectify_isRectified D) fvs hPreparation.1).1 hL))


proof_of sequent_sentence_reduction_LKe := by
  let D := sequentDisjunction s hNonempty
  let A := rectify D
  let fvs := (formulaFreeVarIndices A).eraseDups
  have hPreparation :
      (∀ x, x ∈ fvs ↔ Membership.mem (formulaFVN A) x) ∧
      FormulaN.isSentence (universalClosure A fvs) ∧
      (lkeProvable (Sequent.mk [] [D]) ↔ lkeProvable (Sequent.mk [] [A])) := by
    -- REPAIR(T7-92): proof pending
    sorry
  refine ⟨hPreparation.2.1, ?_⟩
  exact (sequent_disjunction_provability_iff_LKe hL s hNonempty).trans
    (hPreparation.2.2.trans (lemma_7_5_1 A (rectify_isRectified D) fvs hPreparation.1).2)


proof_of herbrand_sequent_convention_LK := by
  have nonemptyCase (q : Sequent L) (hn : q.antecedent ++ q.succedent ≠ []) :
      let B := rectify (associatedSentence q hn).toNNF
      HerbrandInputConvention [B] ∧ (∀ A ∈ [B], isRectified A) ∧
        (folkProvable q ↔ folkProvable (Sequent.mk [] [B])) := by
    have hSentence := sequent_sentence_reduction_LK hL q hn
    let A := associatedSentence q hn
    let B := rectify A.toNNF
    have hPreparation : HerbrandInputConvention [B] ∧
        (folkProvable (Sequent.mk [] [A]) ↔ folkProvable (Sequent.mk [] [B])) := by
      -- REPAIR(T7-93): proof pending
      sorry
    refine ⟨hPreparation.1, ?_, hSentence.2.trans hPreparation.2⟩
    intro C hC
    have hCB : C = B := List.mem_singleton.mp hC
    subst C
    exact rectify_isRectified _
  rcases s with ⟨Gamma, Delta⟩
  cases Gamma with
  | nil =>
    cases Delta with
    | nil =>
      refine ⟨[], rfl, ?_, ?_, Iff.rfl⟩
      · simp [HerbrandInputConvention]
      · simp
    | cons B rest => exact ⟨_, rfl, nonemptyCase (Sequent.mk [] (B :: rest)) (by simp)⟩
  | cons A rest => exact ⟨_, rfl, nonemptyCase (Sequent.mk (A :: rest) Delta) (by simp)⟩


proof_of herbrand_sequent_convention_LKe := by
  have nonemptyCase (q : Sequent L) (hn : q.antecedent ++ q.succedent ≠ []) :
      let B := rectify (associatedSentence q hn).toNNF
      HerbrandInputConvention [B] ∧ (∀ A ∈ [B], isRectified A) ∧
        (lkeProvable q ↔ lkeProvable (Sequent.mk [] [B])) := by
    have hSentence := sequent_sentence_reduction_LKe hL q hn
    let A := associatedSentence q hn
    let B := rectify A.toNNF
    have hPreparation : HerbrandInputConvention [B] ∧
        (lkeProvable (Sequent.mk [] [A]) ↔ lkeProvable (Sequent.mk [] [B])) := by
      -- REPAIR(T7-93): proof pending
      sorry
    refine ⟨hPreparation.1, ?_, hSentence.2.trans hPreparation.2⟩
    intro C hC
    have hCB : C = B := List.mem_singleton.mp hC
    subst C
    exact rectify_isRectified _
  rcases s with ⟨Gamma, Delta⟩
  cases Gamma with
  | nil =>
    cases Delta with
    | nil =>
      refine ⟨[], rfl, ?_, ?_, Iff.rfl⟩
      · simp [HerbrandInputConvention]
      · simp
    | cons B rest => exact ⟨_, rfl, nonemptyCase (Sequent.mk [] (B :: rest)) (by simp)⟩
  | cons A rest => exact ⟨_, rfl, nonemptyCase (Sequent.mk (A :: rest) Delta) (by simp)⟩


end LCS.Herbrand.HerbrandTheorem

end

section

namespace LCS.Herbrand.HerbrandTheorem

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.Semantics.Subformulae

open LCS.Herbrand.PrenexForm

open LCS.Herbrand.SharpenedHauptsatz.Theorem

open LCS.CutElim.LK

open LCS.CutElim.LKe.Equivalence

open LCS.FirstOrder.Gentzen

open LCS.CutElim.Interpolation.Equality

section ValidityDuality

open LCS.FirstOrder.SemanticsN

helper /-- The identification ¬B with A for B = ¬A in §7.5.2 is semantic:
the two formulae agree in every nonempty structure and under every assignment.
No equality between their raw syntax trees is asserted. -/
theorem negated_complement_semantics {L : Language} (A B : FormulaN L)
    (hB : B = .neg A) (M : Structure L) (v : Assignment M) :
    formulaEvalN M (.neg B) v ↔ formulaEvalN M A v := by
  subst B
  classical
  simp [formulaEvalN, negM]

proof_of skolem_validity_duality := by
  subst B
  classical
  simp [universallyValidN, validInN, satisfiableN, satisfiableInN,
    sequentValid, formulaEvalN, negM]


end ValidityDuality

end LCS.Herbrand.HerbrandTheorem

end

section

namespace LCS.Herbrand.HerbrandTheorem

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.Semantics.Subformulae

open LCS.Herbrand.PrenexForm

open LCS.Herbrand.SharpenedHauptsatz.Theorem

open LCS.CutElim.LK

open LCS.CutElim.LKe.Equivalence

open LCS.FirstOrder.Gentzen

open LCS.CutElim.Interpolation.Equality

proof_of sigmaMatrix_base := by
  simpa [toPrenexHelper] using
    sigmaMatrix_stage_spec sd j sigma hSigma names hCover 0 (Nat.zero_le _)


proof_of sigmaMatrix_eq_original := by
  exact sigmaMatrix_go_full sd j sigma hSigma names hCover


end LCS.Herbrand.HerbrandTheorem

end
