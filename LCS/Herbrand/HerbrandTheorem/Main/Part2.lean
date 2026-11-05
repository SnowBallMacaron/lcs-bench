import LCS.Item
import LCS.Util
import LCS.Herbrand.HerbrandTheorem
import LCS.Herbrand.HerbrandTheorem.Main.Part1
import Attach
import LCS.Herbrand.HerbrandTheorem.Main.Part2.ProofsStamp

section
namespace LCS.Herbrand.HerbrandTheorem.Main
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.HerbrandTheorem
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.CutElim.LK
open LCS.CutElim.LKe.Equivalence

/-- Example 7.5.3: a is the only requested universal term for this sentence. -/
theorem herbrandExSigmaNamesCover :
    SigmaMatrixNamesCover skolemExampleAllocation ⟨2, by decide⟩
      herbrandExSigmaAssignment herbrandExSigmaNames := by
  intro t ht
  change t ∈ [herbrandExCanonicalA] at ht
  exact ht /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

/-- Example 7.5.3: the concrete σ-matrix stage, with its remaining existential
variables instantiated and the occurrence-indexed signature given the printed
f/g/a names. Stage 0 leaves v,u free; stage 1 binds z₁ and leaves v free. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExSigmaStage (i : Nat) : FormulaN herbrandExLang :=
  herbrandExFromSkolemFormula (skolemExampleNameFormula
    (Substitution.applyFormula herbrandExSigmaAssignment
      (sigmaMatrix skolemExampleAllocation ⟨2, by decide⟩ herbrandExSigmaAssignment
        herbrandExSigmaNames herbrandExSigmaNamesCover i)))

/-- Example 7.5.3: the two printed σ-matrix observations, tied to Definition
7.5.4 and to the actual H′/first-prefix boundaries. The naming is the a↦w
entry of the full finite bijection; the residual assignment has the source
existential-prefix domain. -/
@[attach_debt, blueprint "chap7__example_7_5_3"]
theorem herbrandExSigmaObservations :
    Substitution.IsExistentialPrefixAssignment herbrandExSigmaAssignment
      (liftValidityFormula skolemExampleSequent_7_3_4
        (skolemExampleSequent_7_3_4.get ⟨2, by decide⟩)) ∧
    herbrandExFreshName (.const .a) =
      some (herbrandExSigmaNames.name herbrandExCanonicalA (by simp)) ∧
    herbrandExSigmaStage 0 =
      .conj (herbrandExP (.var 9) (.var 8)) (herbrandExQ (.var 8) (.var 7)) ∧
    herbrandExSigmaStage 1 =
      .ex 6 (.conj (herbrandExP (.var 9) (.var 8)) (herbrandExQ (.var 8) (.var 6))) ∧
    herbrandExHPrime.succedent.getLast? = some (herbrandExSigmaStage 0) ∧
    herbrandExReconstruction1.succedent.getLast? = some (herbrandExSigmaStage 1) 



/-- Example 7.5.3: the fourth boundary introduces ∃y₁ outside ∀z. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExReconstruction4 : Sequent herbrandExLang :=
  ⟨[], [.neg (herbrandExP (.var 9) (.var 8)),
    .ex 2 (.all 3 (.neg (herbrandExQ (.var 2) (.var 3)))),
    .ex 5 (.ex 6 (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))]⟩

/-- Example 7.5.3: the fifth boundary restores ∀y, with v=8 as eigenvariable. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExReconstruction5 : Sequent herbrandExLang :=
  ⟨[], [.all 1 (.neg (herbrandExP (.var 9) (.var 1))),
    .ex 2 (.all 3 (.neg (herbrandExQ (.var 2) (.var 3)))),
    .ex 5 (.ex 6 (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))]⟩

/-- Example 7.5.3: the sixth boundary introduces ∃x outside ∀y. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExReconstruction6 : Sequent herbrandExLang :=
  ⟨[], [.ex 0 (.all 1 (.neg (herbrandExP (.var 0) (.var 1)))),
    .ex 2 (.all 3 (.neg (herbrandExQ (.var 2) (.var 3)))),
    .ex 5 (.ex 6 (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))]⟩

/-- Example 7.5.3: lawful cumulative prefix 4, retaining every earlier
boundary. Quantifier side conditions are checked in the entire conclusion. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExPrefix4 : FOLKProofTree herbrandExReconstruction4 := by
  have substAtom (p : HerbrandExPred) (a b t : Term herbrandExLang) (x : Nat) :
      formulaSubstN (.predN p (vec2 a b)) t x =
        .predN p (vec2 (termSubst a t x) (termSubst b t x)) := by
    apply congrArg (FormulaN.predN (L := herbrandExLang) p)
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
  let np := FormulaN.neg (herbrandExP (.var 9) (.var 8))
  let c2 := FormulaN.ex 5 (.ex 6 (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))
  let aq := FormulaN.all 3 (.neg (herbrandExQ (.var 8) (.var 3)))
  let eq := FormulaN.ex 2 (.all 3 (.neg (herbrandExQ (.var 2) (.var 3))))
  have r : FOLKStep1 ⟨[], [np, c2, aq]⟩ ⟨[], [np, c2, eq]⟩ := by
    simpa [aq, eq, formulaSubstN, herbrandExQ, substAtom, termSubst] using
      (FOLKStep1.exRight (L := herbrandExLang) (.var 8) 2
        (.all 3 (.neg (herbrandExQ (.var 2) (.var 3)))) [] [np, c2]
        (by simp [isFreeForN, herbrandExQ, termFV, Membership.mem, Set.singleton]))
  exact .onePremise (.exchangeRight [] [np] c2 eq [])
    (.onePremise r (.onePremise (.exchangeRight [] [np] aq c2 []) herbrandExPrefix3))

/-- Example 7.5.3: lawful cumulative prefix 5, retaining every earlier
boundary. Quantifier side conditions are checked in the entire conclusion. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExPrefix5 : FOLKProofTree herbrandExReconstruction5 := by
  have substAtom (p : HerbrandExPred) (a b t : Term herbrandExLang) (x : Nat) :
      formulaSubstN (.predN p (vec2 a b)) t x =
        .predN p (vec2 (termSubst a t x) (termSubst b t x)) := by
    apply congrArg (FormulaN.predN (L := herbrandExLang) p)
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
  let np := FormulaN.neg (herbrandExP (.var 9) (.var 8))
  let c2 := FormulaN.ex 5 (.ex 6 (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))
  let eq := FormulaN.ex 2 (.all 3 (.neg (herbrandExQ (.var 2) (.var 3))))
  let ap := FormulaN.all 1 (.neg (herbrandExP (.var 9) (.var 1)))
  have finTwo (R : Fin 2 → Prop) : (∃ i, R i) ↔ R 0 ∨ R 1 := by
    constructor
    · rintro ⟨⟨i, hi⟩, h⟩
      match i, hi with
      | 0, _ => exact Or.inl h
      | 1, _ => exact Or.inr h
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  have finTwoAll (R : Fin 2 → Prop) : (∀ i, R i) ↔ R 0 ∧ R 1 := by
    constructor
    · intro h; exact ⟨h 0, h 1⟩
    · rintro ⟨h0, h1⟩ ⟨i, hi⟩
      match i, hi with
      | 0, _ => exact h0
      | 1, _ => exact h1
  have fresh : ∀ F ∈ ([] : List (FormulaN herbrandExLang)) ++ ([eq, c2] ++ [ap]),
      8 ∉ formulaFVN F := by
    intro F hF
    simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl
    all_goals simp [np, c2, eq, ap, formulaFVN, herbrandExP, herbrandExQ,
      Membership.mem, Set.iUnion, Set.union, Set.diff, Set.singleton,
      termFV, vec2, herbrandExLang, finTwo, finTwoAll]
  have r : FOLKStep1 ⟨[], [eq, c2, np]⟩ ⟨[], [eq, c2, ap]⟩ := by
    simpa [np, ap, formulaSubstN, herbrandExP, substAtom, termSubst] using
      (FOLKStep1.allRight (L := herbrandExLang) 8 1
        (.neg (herbrandExP (.var 9) (.var 1))) [] [eq, c2] fresh
        (by simp [isFreeForN, herbrandExP]))
  exact .onePremise (.exchangeRight [] [] eq ap [c2])
    (.onePremise (.exchangeRight [] [eq] c2 ap [])
      (.onePremise r (.onePremise (.exchangeRight [] [eq] np c2 [])
        (.onePremise (.exchangeRight [] [] np eq [c2]) herbrandExPrefix4))))

/-- Example 7.5.3: lawful cumulative prefix 6, retaining every earlier
boundary. Quantifier side conditions are checked in the entire conclusion. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExPrefix6 : FOLKProofTree herbrandExReconstruction6 := by
  have substAtom (p : HerbrandExPred) (a b t : Term herbrandExLang) (x : Nat) :
      formulaSubstN (.predN p (vec2 a b)) t x =
        .predN p (vec2 (termSubst a t x) (termSubst b t x)) := by
    apply congrArg (FormulaN.predN (L := herbrandExLang) p)
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
  let c2 := FormulaN.ex 5 (.ex 6 (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))
  let eq := FormulaN.ex 2 (.all 3 (.neg (herbrandExQ (.var 2) (.var 3))))
  let ap := FormulaN.all 1 (.neg (herbrandExP (.var 9) (.var 1)))
  let ep := FormulaN.ex 0 (.all 1 (.neg (herbrandExP (.var 0) (.var 1))))
  have r : FOLKStep1 ⟨[], [eq, c2, ap]⟩ ⟨[], [eq, c2, ep]⟩ := by
    simpa [ap, ep, formulaSubstN, herbrandExP, substAtom, termSubst] using
      (FOLKStep1.exRight (L := herbrandExLang) (.var 9) 0
        (.all 1 (.neg (herbrandExP (.var 0) (.var 1)))) [] [eq, c2]
        (by simp [isFreeForN, herbrandExP, termFV, Membership.mem, Set.singleton]))
  exact .onePremise (.exchangeRight [] [] eq ep [c2])
    (.onePremise (.exchangeRight [] [eq] c2 ep [])
      (.onePremise r (.onePremise (.exchangeRight [] [eq] ap c2 [])
        (.onePremise (.exchangeRight [] [] ap eq [c2]) herbrandExPrefix5))))

/-- Example 7.5.3: lawful cumulative prefix 7, retaining every earlier
boundary. Quantifier side conditions are checked in the entire conclusion. -/
@[blueprint "chap7__example_7_5_3" (main := true)]
def herbrandExPrefix7 : FOLKProofTree herbrandExampleSequent := by
  have substAtom (p : HerbrandExPred) (a b t : Term herbrandExLang) (x : Nat) :
      formulaSubstN (.predN p (vec2 a b)) t x =
        .predN p (vec2 (termSubst a t x) (termSubst b t x)) := by
    apply congrArg (FormulaN.predN (L := herbrandExLang) p)
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
  let c2 := FormulaN.ex 5 (.ex 6 (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))
  let cf := FormulaN.ex 5 (.ex 6 (.conj (herbrandExP (.var 4) (.var 5)) (herbrandExQ (.var 5) (.var 6))))
  let ep := FormulaN.ex 0 (.all 1 (.neg (herbrandExP (.var 0) (.var 1))))
  let eq := FormulaN.ex 2 (.all 3 (.neg (herbrandExQ (.var 2) (.var 3))))
  have finTwo (R : Fin 2 → Prop) : (∃ i, R i) ↔ R 0 ∨ R 1 := by
    constructor
    · rintro ⟨⟨i, hi⟩, h⟩
      match i, hi with
      | 0, _ => exact Or.inl h
      | 1, _ => exact Or.inr h
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  have finTwoAll (R : Fin 2 → Prop) : (∀ i, R i) ↔ R 0 ∧ R 1 := by
    constructor
    · intro h; exact ⟨h 0, h 1⟩
    · rintro ⟨h0, h1⟩ ⟨i, hi⟩
      match i, hi with
      | 0, _ => exact h0
      | 1, _ => exact h1
  have fresh : ∀ F ∈ ([] : List (FormulaN herbrandExLang)) ++ ([ep, eq] ++ [.all 4 cf]),
      9 ∉ formulaFVN F := by
    intro F hF
    simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl
    all_goals simp [c2, cf, ep, eq, formulaFVN, herbrandExP, herbrandExQ,
      Membership.mem, Set.iUnion, Set.union, Set.diff, Set.singleton,
      termFV, vec2, herbrandExLang, finTwo, finTwoAll]
  have r : FOLKStep1 ⟨[], [ep, eq, c2]⟩ ⟨[], [ep, eq, .all 4 cf]⟩ := by
    simpa [c2, cf, formulaSubstN, herbrandExP, herbrandExQ, substAtom, termSubst] using
      (FOLKStep1.allRight (L := herbrandExLang) 9 4 cf [] [ep, eq] fresh
        (by simp [cf, isFreeForN, herbrandExP, herbrandExQ, termFV, Membership.mem, Set.singleton]))
  exact .onePremise r herbrandExPrefix6



/-- Example 7.5.3: the displayed comparison renaming w↦x₁, v↦y, u↦z.
Original binder names 0–6 and all other variables are fixed. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExRestoreVariables : Substitution herbrandExLang
  | 9 => .var 4
  | 8 => .var 1
  | 7 => .var 3
  | x => .var x

/-- Example 7.5.3: the complete seven-quantifier suffix, including its twelve
exchanges and every boundary through the midsequent, agrees with Example 7.3.4
under the displayed renaming. Quantifier binders agree exactly; eigenvariables
and instantiating terms agree after renaming. This compares two fixed proofs. -/
@[attach_debt, blueprint "chap7__example_7_5_3"]
theorem herbrandExSuffixRenamed :
    (∀ d ≤ 19,
      ((LCS.Herbrand.SharpenedHauptsatz.Permutability.lkSubtreeAt
        herbrandExPrefix7 (List.replicate d 0)).map (fun node =>
          (Sequent.mk
            (node.1.antecedent.map (Substitution.applyFormula herbrandExRestoreVariables))
            (node.1.succedent.map (Substitution.applyFormula herbrandExRestoreVariables))))) =
      ((LCS.Herbrand.SharpenedHauptsatz.Permutability.lkSubtreeAt
        midsequentExampleTree (List.replicate d 0)).map (fun node =>
          (Sequent.mk
            (node.1.antecedent.map (fun A => herbrandExFromSkolemFormula (skolemExampleLiftFormula A)))
            (node.1.succedent.map (fun A => herbrandExFromSkolemFormula (skolemExampleLiftFormula A))))))) ∧
    (∀ d < 19,
      match LCS.Herbrand.SharpenedHauptsatz.Permutability.lkInferenceAt herbrandExPrefix7 (List.replicate d 0),
        LCS.Herbrand.SharpenedHauptsatz.Permutability.lkInferenceAt midsequentExampleTree (List.replicate d 0) with
      | some (.one r), some (.one q) => r.ctorIdx = q.ctorIdx ∧
        match r, q with
        | .allRight y x _ _ _ _ _, .allRight z w _ _ _ _ _ =>
          herbrandExRestoreVariables y = .var z ∧ x = w
        | .exRight t x _ _ _ _, .exRight u w _ _ _ _ =>
          Substitution.applyTerm herbrandExRestoreVariables t =
            herbrandExFromSkolemTerm (skolemExampleLiftTerm u) ∧ x = w
        | _, _ => True
      | _, _ => False) 

-- ===================================================================
-- Theorem 7.5.1: the printed constant-free counterexample (CN26)
-- ===================================================================

































-- ===================================================================
-- Theorem 7.5.1 (forward direction, required companion):
--   herbrand_substitution_pairs_LK
-- ===================================================================











/-- The normalized sequent is obtained by NNF conversion and fresh binder
renaming of each source occurrence, followed by deletion of duplicate sentences.
The intermediate list preserves source order and occurrences; the sublist and
coverage clauses permit only duplicate deletion. Global binder distinction is
certified on the output by its Skolem allocation. -/
@[blueprint "chap7__theorem_7_5_1"]
def IsHerbrandNormalization {L : Language}
    (Gamma Delta : List (FormulaN L)) : Prop :=
  ∃ starts : Fin Gamma.length → Nat,
    let renamed := List.ofFn fun i =>
      (rectifyAux (Gamma.get i).toNNF id (starts i)).1
    Delta.Sublist renamed ∧ (∀ B ∈ renamed, B ∈ Delta)

/-- Theorem 7.5.1 (forward direction): An LK-provable prenex sentence
sequent over an equality-free language has a normalized representative with
sequent-wide distinct binders and a provable Herbrand disjunction. Each witness
occurrence retains its normalized source and the complete ground tuple, including
vacuous existential binders, in the common constant-completed Skolem signature. -/
theorem herbrandTheorem_forward_LK {L : Language}
    (hL : L.withoutEquality)
    (Gamma : List (FormulaN L))
    (hAllPrenex : allSequentFormulaeArePrenex (Sequent.mk [] Gamma))
    (hAllSentences : ∀ A ∈ Gamma, FormulaN.isSentence A)
    (hAllRectified : ∀ A ∈ Gamma, isRectified A)
    (hDistinct : Gamma.Nodup)
    (hProv : folkProvable (Sequent.mk [] Gamma)) :
    ∃ (Delta : List (FormulaN L)) (sps : SubstitutionPairSeq Delta)
      (sd : SkolemData L Delta),
      IsHerbrandNormalization Gamma Delta ∧
      IsConstructibleFromFunctionalForm Delta sps sd ∧
      folkProvable (HerbrandDisjunction sd sps) := by
  -- REPAIR(T7-58): proof pending
  sorry

/-- Theorem 7.5.1 (converse direction): A provable Herbrand disjunction
built from a normalized representative of the source yields LK provability of
the original sequent. The allocation certifies the output binder convention;
finite fresh names for reconstruction are chosen within the proof. -/
theorem herbrandTheorem_converse_LK {L : Language}
    (hL : L.withoutEquality)
    (Gamma : List (FormulaN L))
    (hAllPrenex : allSequentFormulaeArePrenex (Sequent.mk [] Gamma))
    (hAllSentences : ∀ A ∈ Gamma, FormulaN.isSentence A)
    (hAllRectified : ∀ A ∈ Gamma, isRectified A)
    (hDistinct : Gamma.Nodup)
    (hHerbrand : ∃ (Delta : List (FormulaN L)) (sps : SubstitutionPairSeq Delta)
      (sd : SkolemData L Delta),
      IsHerbrandNormalization Gamma Delta ∧
      IsConstructibleFromFunctionalForm Delta sps sd ∧
      folkProvable (HerbrandDisjunction sd sps)) :
    folkProvable (Sequent.mk [] Gamma) := by
  -- REPAIR(T7-58): proof pending
  sorry

/-- Theorem 7.5.1: A prenex sentence sequent over an equality-free language
is LK-provable iff a normalized representative admits a finite source-associated
sequence of ground substitution pairs with provable Herbrand disjunction.
Normalization uses NNF conversion, binder renaming and duplicate deletion;
its Skolem allocation certifies sequent-wide binder distinction. The witness
signature, occurring-symbol restriction, grounding constant and full-prefix
assignments are those of IsConstructibleFromFunctionalForm. -/
@[blueprint "chap7__theorem_7_5_1" (main := true)]
theorem herbrandTheorem_LK {L : Language}
    (hL : L.withoutEquality)
    (Gamma : List (FormulaN L))
    (hAllPrenex : allSequentFormulaeArePrenex (Sequent.mk [] Gamma))
    (hAllSentences : ∀ A ∈ Gamma, FormulaN.isSentence A)
    (hAllRectified : ∀ A ∈ Gamma, isRectified A)
    (hDistinct : Gamma.Nodup) :
    folkProvable (Sequent.mk [] Gamma) ↔
    (∃ (Delta : List (FormulaN L)) (sps : SubstitutionPairSeq Delta)
      (sd : SkolemData L Delta),
      IsHerbrandNormalization Gamma Delta ∧
      IsConstructibleFromFunctionalForm Delta sps sd ∧
      folkProvable (HerbrandDisjunction sd sps)) 

-- ===================================================================
-- Theorem 7.5.1 (LKe variant, required companion):
--   herbrand_substitution_pairs_LKe
-- ===================================================================











-- ===================================================================
-- Theorem 7.5.1: herbrandTheorem_LKe (LKe variant)
-- ===================================================================

/-- Theorem 7.5.1 (LKₑ): A prenex sentence sequent over a language with
equality is LKₑ-provable iff a normalized representative admits a finite
source-associated sequence of ground substitution pairs with LKₑ-provable
Herbrand disjunction. Equality retains its identity interpretation. Normalization
uses NNF conversion, binder renaming and duplicate deletion; the output's Skolem
allocation certifies sequent-wide binder distinction. Full-prefix ground tuples,
occurring-symbol restrictions and the ambient/adjoined grounding constant are
those of IsConstructibleFromFunctionalForm. Fresh names for reconstruction are
chosen within the proof. -/
@[attach_debt, blueprint "chap7__theorem_7_5_1" (main := true)]
theorem herbrandTheorem_LKe {L : Language}
    (hL : L.hasEquality = true)
    (Gamma : List (FormulaN L))
    (hAllPrenex : allSequentFormulaeArePrenex (Sequent.mk [] Gamma))
    (hAllSentences : ∀ A ∈ Gamma, FormulaN.isSentence A)
    (hAllRectified : ∀ A ∈ Gamma, isRectified A)
    (hDistinct : Gamma.Nodup) :
    lkeProvable (Sequent.mk [] Gamma) ↔
    (∃ (Delta : List (FormulaN L)) (sps : SubstitutionPairSeq Delta)
      (sd : SkolemData L Delta),
      IsHerbrandNormalization Gamma Delta ∧
      IsConstructibleFromFunctionalForm Delta sps sd ∧
      lkeProvable (HerbrandDisjunction sd sps)) 

-- ===================================================================
-- Example 7.5.3 (helper defs): Proof tree components
-- ===================================================================













-- ===================================================================
-- Example 7.5.3 (companion theorem): herbrandExDisjunctionProvable
-- ===================================================================

/-- Example 7.5.3 (companion theorem): The Herbrand disjunction -> not P(a, f(a)), not Q(f(a), g(f(a))), P(a, f(a)) and Q(f(a), g(f(a))) is LK-provable. The first succedent not P(a, f(a)) is the negation of a conjunct P(a, f(a)) of the third succedent, and the second succedent not Q(f(a), g(f(a))) is the negation of the other conjunct Q(f(a), g(f(a))). Proof: Construct an LK proof tree using axioms P(a,f(a)) -> P(a,f(a)) and Q(f(a),g(f(a))) -> Q(f(a),g(f(a))), applying negRight, weakenRight, exchangeRight to build both branches, then andRight to combine them. -/
@[blueprint "chap7__example_7_5_3" (main := true)]
theorem herbrandExDisjunctionProvable :
    folkProvable herbrandExDisjunction 

end LCS.Herbrand.HerbrandTheorem.Main
end

