import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.CutRank
import Attach
import LCS.CutElim.Hauptsatz.CutElimination.FormulaSubstitution.ProofsStamp

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem LCS.Finset.image_insert [DecidableEq α] [DecidableEq β]
    (f : α → β) (a : α) (s : LCS.Finset α) :
    LCS.Finset.image f (LCS.Finset.insert a s) =
      LCS.Finset.insert (f a) (LCS.Finset.image f s) := by
-- BEGIN PROOF
  apply LCS.Finset.ext; intro b
  rw [LCS.Finset.mem_image, LCS.Finset.mem_insert]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [LCS.Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (LCS.Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  · rintro (rfl | hb)
    · exact ⟨a, LCS.Finset.mem_insert.mpr (Or.inl rfl), rfl⟩
    · obtain ⟨x, hx, rfl⟩ := LCS.Finset.mem_image.mp hb
      exact ⟨x, LCS.Finset.mem_insert.mpr (Or.inr hx), rfl⟩

namespace LCS.CutElim.Hauptsatz

-- ===================================================================
-- Helper: isAtomic preserved under formulaSubstN
-- ===================================================================
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 6.4.5 (required helper): term substitution `[t/y]` preserves
atomicity of a formula. Used when `substRule` transports the atomic-axiom
hypothesis across rule substitution. -/
theorem isAtomic_formulaSubstN {L : Language} (A : FormulaN L)
    (t : Term L) (x : Nat) (hAtom : A.isAtomic = true) :
    (formulaSubstN A t x).isAtomic = true := by
-- BEGIN PROOF
  cases A with
  | predN _ _ => simp [formulaSubstN, FormulaN.isAtomic]
  | eq_ _ _ => simp [formulaSubstN, FormulaN.isAtomic]
  | neg _ => simp [FormulaN.isAtomic] at hAtom
  | conj _ _ => simp [FormulaN.isAtomic] at hAtom
  | disj _ _ => simp [FormulaN.isAtomic] at hAtom
  | impl _ _ => simp [FormulaN.isAtomic] at hAtom
  | all _ _ => simp [FormulaN.isAtomic] at hAtom
  | ex _ _ => simp [FormulaN.isAtomic] at hAtom

-- ===================================================================
-- Definition 6.4.5: substFormulaFinset — Finset substitution
-- ===================================================================
/-- Definition 6.4.5 (required helper): Apply term substitution [t/y]
to every formula in a Finset. -/
@[blueprint "chap6__definition_6_4_5"]
noncomputable def substFormulaFinset {L : Language}
    (S : LCS.Finset (FormulaN L)) (t : Term L) (y : Nat) :
    LCS.Finset (FormulaN L) :=
  LCS.Finset.image (fun A => formulaSubstN A t y) S

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.EigenWeakening
theorem substFormulaFinset_union {L : Language}
    (S₁ S₂ : LCS.Finset (FormulaN L)) (t : Term L) (v : Nat) :
    substFormulaFinset (LCS.Finset.union S₁ S₂) t v =
      LCS.Finset.union
        (substFormulaFinset S₁ t v)
        (substFormulaFinset S₂ t v) := by
  apply LCS.Finset.ext
  intro A
  simp only [substFormulaFinset, LCS.Finset.mem_image,
    LCS.Finset.mem_union]
  constructor
  · rintro ⟨B, hB | hB, rfl⟩
    · exact Or.inl ⟨B, hB, rfl⟩
    · exact Or.inr ⟨B, hB, rfl⟩
  · rintro (⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩)
    · exact ⟨B, Or.inl hB, rfl⟩
    · exact ⟨B, Or.inr hB, rfl⟩

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.EigenWeakening, LCS.CutElim.Hauptsatz.CutElimination.Substitution, LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression
theorem substFormulaFinset_insert {L : Language}
    (A : FormulaN L) (S : LCS.Finset (FormulaN L)) (t : Term L) (y : Nat) :
    substFormulaFinset (LCS.Finset.insert A S) t y =
      LCS.Finset.insert (formulaSubstN A t y) (substFormulaFinset S t y) := by
-- BEGIN PROOF
  exact LCS.Finset.image_insert _ A S

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Substitution, LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression
/-- Term substitution preserves the pointwise NNF invariant of a formula
Finset. -/
theorem substFormulaFinset_isNNF {L : Language}
    (S : LCS.Finset (FormulaN L)) (t : Term L) (y : Nat)
    (hNNF : ∀ A ∈ S, FormulaN.isNNF A) :
    ∀ A ∈ substFormulaFinset S t y, FormulaN.isNNF A := by
-- BEGIN PROOF
  intro A hA
  rw [substFormulaFinset, LCS.Finset.mem_image] at hA
  rcases hA with ⟨B, hB, rfl⟩
  exact isNNF_formulaSubstN B t y (hNNF B hB)

-- END PROOF
-- ===================================================================
-- Freshness and free-for transport through substitution
-- ===================================================================
-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Substitution
/-- A variable absent from both a term and the substituting term remains
absent after term substitution. -/
theorem termFV_termSubst_not_mem {L : Language}
    (u t : Term L) (y v : Nat)
    (hu : v ∉ termFV u) (ht : v ∉ termFV t) :
    v ∉ termFV (termSubst u t y) := by
-- BEGIN PROOF
  intro hv
  rcases
      LCS.FirstOrder.Gentzen.Hintikka.termFV_termSubst u t y v hv with
    ⟨hvU, _⟩ | ⟨_, hvT⟩
  · exact hu hvU
  · exact ht hvT

-- END PROOF
-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Substitution
/-- A variable absent from both a formula and the substituting term remains
absent from the formula after substitution. -/
theorem formulaFVN_formulaSubstN_not_mem {L : Language}
    (A : FormulaN L) (t : Term L) (y v : Nat)
    (hA : v ∉ formulaFVN A) (ht : v ∉ termFV t) :
    v ∉ formulaFVN (formulaSubstN A t y) := by
-- BEGIN PROOF
  intro hv
  rcases
      LCS.FirstOrder.Gentzen.Hintikka.formulaFVN_formulaSubstN
        A t y v hv with
    ⟨hvA, _⟩ | hvT
  · exact hA hvA
  · exact ht hvT

-- END PROOF
-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Substitution
/-- Pointwise freshness of a formula Finset is preserved by substitution
when the tracked variable is also absent from the substituting term. -/
theorem substFormulaFinset_fresh {L : Language}
    (S : LCS.Finset (FormulaN L)) (t : Term L) (y v : Nat)
    (hS : ∀ A ∈ S, v ∉ formulaFVN A)
    (ht : v ∉ termFV t) :
    ∀ A ∈ substFormulaFinset S t y, v ∉ formulaFVN A := by
-- BEGIN PROOF
  intro A hA
  obtain ⟨B, hBS, rfl⟩ := LCS.Finset.mem_image.mp hA
  exact formulaFVN_formulaSubstN_not_mem B t y v (hS B hBS) ht

-- END PROOF
-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Substitution
/-- Simultaneously substituting `t` for `y` in a formula and in a term
that is free for `x` preserves the free-for relation. The bound-variable
condition ensures substitution descends through every binder of `A`. -/
theorem isFreeForN_termSubst_formulaSubstN {L : Language}
    (A : FormulaN L) (u t : Term L) (x y : Nat)
    (hu : isFreeForN u x A)
    (ht : isFreeForN t y A)
    (hyBV : y ∉ formulaBVN A) :
    isFreeForN (termSubst u t y) x (formulaSubstN A t y) := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => trivial
  | eq_ _ _ _ => trivial
  | neg A ih =>
    exact ih hu ht hyBV
  | conj A B ihA ihB =>
    exact
      ⟨ihA hu.1 ht.1 (fun h => hyBV (Or.inl h)),
       ihB hu.2 ht.2 (fun h => hyBV (Or.inr h))⟩
  | disj A B ihA ihB =>
    exact
      ⟨ihA hu.1 ht.1 (fun h => hyBV (Or.inl h)),
       ihB hu.2 ht.2 (fun h => hyBV (Or.inr h))⟩
  | impl A B ihA ihB =>
    exact
      ⟨ihA hu.1 ht.1 (fun h => hyBV (Or.inl h)),
       ihB hu.2 ht.2 (fun h => hyBV (Or.inr h))⟩
  | all z A ih =>
    have hyz : y ≠ z := by
      intro hyz
      exact hyBV (Or.inr (hyz ▸ rfl))
    have hyzB : (y != z) = true := bne_iff_ne.mpr hyz
    have hyB : y ∉ formulaBVN A := fun h => hyBV (Or.inl h)
    simp only [formulaSubstN, hyzB, ↓reduceIte, isFreeForN]
    simp only [isFreeForN] at hu ht
    rcases ht with hyz' | ⟨hzT, ht⟩
    · exact absurd hyz' hyz
    · rcases hu with hxz | ⟨hzU, hu⟩
      · exact Or.inl hxz
      · exact Or.inr
          ⟨termFV_termSubst_not_mem u t y z hzU hzT,
           ih hu ht hyB⟩
  | ex z A ih =>
    have hyz : y ≠ z := by
      intro hyz
      exact hyBV (Or.inr (hyz ▸ rfl))
    have hyzB : (y != z) = true := bne_iff_ne.mpr hyz
    have hyB : y ∉ formulaBVN A := fun h => hyBV (Or.inl h)
    simp only [formulaSubstN, hyzB, ↓reduceIte, isFreeForN]
    simp only [isFreeForN] at hu ht
    rcases ht with hyz' | ⟨hzT, ht⟩
    · exact absurd hyz' hyz
    · rcases hu with hxz | ⟨hzU, hu⟩
      · exact Or.inl hxz
      · exact Or.inr
          ⟨termFV_termSubst_not_mem u t y z hzU hzT,
           ih hu ht hyB⟩

-- END PROOF
-- formulaSubstN distributivity lemmas
-- ===================================================================
-- substRule — substitution on G1nnfRule (Finset)
-- ===================================================================
/-- Definition 6.4.5 (required helper): Applies the substitution
[t/y] to all formulae and term parameters in a G1nnf rule, including
Finset-substitution of stored axiom and cut contexts. Used in the body of
`G1nnfProofTree.substTerm` to transport each rule of a proof tree T
to the substituted tree T[t/y], implementing the textbook clause
"T[t/y] is the result of replacing every sequent Γ → Δ in T by
(Γ → Δ)[t/y]" at the rule level. -/
@[blueprint "chap6__definition_6_4_5"]
noncomputable def substRule {L : Language} (t : Term L) (y : Nat) :
    G1nnfRule L → G1nnfRule L
  | .axiomPosAtomic A hAtom rG rD =>
    .axiomPosAtomic (formulaSubstN A t y)
      (isAtomic_formulaSubstN A t y hAtom)
      (substFormulaFinset rG t y) (substFormulaFinset rD t y)
  | .axiomNegAtomic A hAtom rG rD =>
    .axiomNegAtomic (formulaSubstN A t y)
      (isAtomic_formulaSubstN A t y hAtom)
      (substFormulaFinset rG t y) (substFormulaFinset rD t y)
  | .axiomCompLeft A hAtom rG rD =>
    .axiomCompLeft (formulaSubstN A t y)
      (isAtomic_formulaSubstN A t y hAtom)
      (substFormulaFinset rG t y) (substFormulaFinset rD t y)
  | .axiomCompRight A hAtom rG rD =>
    .axiomCompRight (formulaSubstN A t y)
      (isAtomic_formulaSubstN A t y hAtom)
      (substFormulaFinset rG t y) (substFormulaFinset rD t y)
  | .cut A Lam Theta =>
    .cut (formulaSubstN A t y)
      (substFormulaFinset Lam t y) (substFormulaFinset Theta t y)
  | .conjLeft1 A B => .conjLeft1 (formulaSubstN A t y) (formulaSubstN B t y)
  | .conjLeft2 A B => .conjLeft2 (formulaSubstN A t y) (formulaSubstN B t y)
  | .conjRight A B => .conjRight (formulaSubstN A t y) (formulaSubstN B t y)
  | .disjLeft A B => .disjLeft (formulaSubstN A t y) (formulaSubstN B t y)
  | .disjRight1 A B => .disjRight1 (formulaSubstN A t y) (formulaSubstN B t y)
  | .disjRight2 A B => .disjRight2 (formulaSubstN A t y) (formulaSubstN B t y)
  | .allLeft x A u =>
    if y != x then .allLeft x (formulaSubstN A t y) (termSubst u t y)
    else .allLeft x A (termSubst u t y)
  | .allRight x A ev =>
    if y != x then .allRight x (formulaSubstN A t y) ev
    else .allRight x A ev
  | .exLeft x A ev =>
    if y != x then .exLeft x (formulaSubstN A t y) ev
    else .exLeft x A ev
  | .exRight x A u =>
    if y != x then .exRight x (formulaSubstN A t y) (termSubst u t y)
    else .exRight x A (termSubst u t y)

-- ===================================================================
-- substRule_conclusion_eq: conclusion commutes with substFormulaFinset
-- ===================================================================
-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.EigenWeakening, LCS.CutElim.Hauptsatz.CutElimination.Substitution, LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression
/-- Definition 6.4.5 (required helper): The conclusion of
`substRule t y rule` applied to substituted context Finsets equals the
substitution of the original conclusion. Used in the body of
`G1nnfProofTree.substTerm` to reconcile the expected conclusion index
of each proof tree constructor with the substituted Γ, Δ. -/
theorem substRule_conclusion_eq {L : Language}
    (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
    (t : Term L) (y : Nat) :
    (substRule t y rule).conclusion
      (substFormulaFinset Gamma t y) (substFormulaFinset Delta t y) =
    (substFormulaFinset (rule.conclusion Gamma Delta).1 t y,
     substFormulaFinset (rule.conclusion Gamma Delta).2 t y) := by
-- BEGIN PROOF
  cases rule with
  | axiomPosAtomic A hAtom rG rD =>
    show (LCS.Finset.insert (formulaSubstN A t y) (substFormulaFinset rG t y),
          LCS.Finset.insert (formulaSubstN A t y) (substFormulaFinset rD t y)) =
         (substFormulaFinset (LCS.Finset.insert A rG) t y,
          substFormulaFinset (LCS.Finset.insert A rD) t y)
    rw [substFormulaFinset_insert, substFormulaFinset_insert]
  | axiomNegAtomic A hAtom rG rD =>
    show (LCS.Finset.insert (formulaSubstN (.neg A) t y) (substFormulaFinset rG t y),
          LCS.Finset.insert (formulaSubstN (.neg A) t y) (substFormulaFinset rD t y)) =
         (substFormulaFinset (LCS.Finset.insert (.neg A) rG) t y,
          substFormulaFinset (LCS.Finset.insert (.neg A) rD) t y)
    rw [substFormulaFinset_insert, substFormulaFinset_insert]
  | axiomCompLeft A hAtom rG rD =>
    show (LCS.Finset.insert (formulaSubstN A t y)
            (LCS.Finset.insert (formulaSubstN (.neg A) t y)
              (substFormulaFinset rG t y)),
          substFormulaFinset rD t y) =
         (substFormulaFinset (LCS.Finset.insert A (LCS.Finset.insert (.neg A) rG)) t y,
          substFormulaFinset rD t y)
    rw [substFormulaFinset_insert, substFormulaFinset_insert]
  | axiomCompRight A hAtom rG rD =>
    show (substFormulaFinset rG t y,
          LCS.Finset.insert (formulaSubstN A t y)
            (LCS.Finset.insert (formulaSubstN (.neg A) t y)
              (substFormulaFinset rD t y))) =
         (substFormulaFinset rG t y,
          substFormulaFinset (LCS.Finset.insert A (LCS.Finset.insert (.neg A) rD)) t y)
    rw [substFormulaFinset_insert, substFormulaFinset_insert]
  | cut A Lam Theta =>
    simp only [substRule, G1nnfRule.conclusion, substFormulaFinset_union]
  | conjLeft1 A B =>
    show (LCS.Finset.insert (.conj (formulaSubstN A t y) (formulaSubstN B t y))
            (substFormulaFinset Gamma t y),
          substFormulaFinset Delta t y) =
         (substFormulaFinset (LCS.Finset.insert (.conj A B) Gamma) t y,
          substFormulaFinset Delta t y)
    rw [substFormulaFinset_insert]; simp [formulaSubstN]
  | conjLeft2 A B =>
    show (LCS.Finset.insert (.conj (formulaSubstN A t y) (formulaSubstN B t y))
            (substFormulaFinset Gamma t y),
          substFormulaFinset Delta t y) =
         (substFormulaFinset (LCS.Finset.insert (.conj A B) Gamma) t y,
          substFormulaFinset Delta t y)
    rw [substFormulaFinset_insert]; simp [formulaSubstN]
  | conjRight A B =>
    show (substFormulaFinset Gamma t y,
          LCS.Finset.insert (.conj (formulaSubstN A t y) (formulaSubstN B t y))
            (substFormulaFinset Delta t y)) =
         (substFormulaFinset Gamma t y,
          substFormulaFinset (LCS.Finset.insert (.conj A B) Delta) t y)
    rw [substFormulaFinset_insert]; simp [formulaSubstN]
  | disjLeft A B =>
    show (LCS.Finset.insert (.disj (formulaSubstN A t y) (formulaSubstN B t y))
            (substFormulaFinset Gamma t y),
          substFormulaFinset Delta t y) =
         (substFormulaFinset (LCS.Finset.insert (.disj A B) Gamma) t y,
          substFormulaFinset Delta t y)
    rw [substFormulaFinset_insert]; simp [formulaSubstN]
  | disjRight1 A B =>
    show (substFormulaFinset Gamma t y,
          LCS.Finset.insert (.disj (formulaSubstN A t y) (formulaSubstN B t y))
            (substFormulaFinset Delta t y)) =
         (substFormulaFinset Gamma t y,
          substFormulaFinset (LCS.Finset.insert (.disj A B) Delta) t y)
    rw [substFormulaFinset_insert]; simp [formulaSubstN]
  | disjRight2 A B =>
    show (substFormulaFinset Gamma t y,
          LCS.Finset.insert (.disj (formulaSubstN A t y) (formulaSubstN B t y))
            (substFormulaFinset Delta t y)) =
         (substFormulaFinset Gamma t y,
          substFormulaFinset (LCS.Finset.insert (.disj A B) Delta) t y)
    rw [substFormulaFinset_insert]; simp [formulaSubstN]
  | allLeft x A u =>
    simp only [substRule]; split <;> {
      simp only [G1nnfRule.conclusion]
      show (LCS.Finset.insert _ (substFormulaFinset Gamma t y), substFormulaFinset Delta t y) =
           (substFormulaFinset (LCS.Finset.insert (.all x A) Gamma) t y, substFormulaFinset Delta t y)
      congr 1
      rw [substFormulaFinset_insert]
      congr 1; simp [formulaSubstN, *] }
  | allRight x A ev =>
    simp only [substRule]; split <;> {
      simp only [G1nnfRule.conclusion]
      show (substFormulaFinset Gamma t y, LCS.Finset.insert _ (substFormulaFinset Delta t y)) =
           (substFormulaFinset Gamma t y, substFormulaFinset (LCS.Finset.insert (.all x A) Delta) t y)
      congr 1
      rw [substFormulaFinset_insert]
      congr 1; simp [formulaSubstN, *] }
  | exLeft x A ev =>
    simp only [substRule]; split <;> {
      simp only [G1nnfRule.conclusion]
      show (LCS.Finset.insert _ (substFormulaFinset Gamma t y), substFormulaFinset Delta t y) =
           (substFormulaFinset (LCS.Finset.insert (.ex x A) Gamma) t y, substFormulaFinset Delta t y)
      congr 1
      rw [substFormulaFinset_insert]
      congr 1; simp [formulaSubstN, *] }
  | exRight x A u =>
    simp only [substRule]; split <;> {
      simp only [G1nnfRule.conclusion]
      show (substFormulaFinset Gamma t y, LCS.Finset.insert _ (substFormulaFinset Delta t y)) =
           (substFormulaFinset Gamma t y, substFormulaFinset (LCS.Finset.insert (.ex x A) Delta) t y)
      congr 1
      rw [substFormulaFinset_insert]
      congr 1; simp [formulaSubstN, *] }

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Substitution, LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression
/-- Definition 6.4.5 (required helper): The premises list length is
invariant under `substRule`. Used in the body of
`G1nnfProofTree.substTerm` to ensure that axiom/onePremise/twoPremise
constructors' premise-count side conditions continue to hold after
substituting a rule. -/
theorem substRule_premises_length {L : Language}
    (rule : G1nnfRule L) (Gamma Delta : LCS.Finset (FormulaN L))
    (t : Term L) (y : Nat) :
    ((substRule t y rule).premises
        (substFormulaFinset Gamma t y) (substFormulaFinset Delta t y)).length =
      (rule.premises Gamma Delta).length := by
-- BEGIN PROOF
  cases rule with
  | axiomPosAtomic _ _ _ _ => rfl
  | axiomNegAtomic _ _ _ _ => rfl
  | axiomCompLeft _ _ _ _ => rfl
  | axiomCompRight _ _ _ _ => rfl
  | cut _ _ _ => rfl
  | conjLeft1 _ _ => rfl
  | conjLeft2 _ _ => rfl
  | conjRight _ _ => rfl
  | disjLeft _ _ => rfl
  | disjRight1 _ _ => rfl
  | disjRight2 _ _ => rfl
  | allLeft _ _ _ => simp only [substRule]; split <;> rfl
  | allRight _ _ _ => simp only [substRule]; split <;> rfl
  | exLeft _ _ _ => simp only [substRule]; split <;> rfl
  | exRight _ _ _ => simp only [substRule]; split <;> rfl

-- ===================================================================
-- substRule_cutFormula: cut formula commutes with substRule
-- ===================================================================
-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.EigenWeakening
theorem substRule_cutFormula {L : Language}
    (rule : G1nnfRule L) (t : Term L) (y : Nat) :
    (substRule t y rule).cutFormula =
      rule.cutFormula.map (fun A => formulaSubstN A t y) := by
-- BEGIN PROOF
  cases rule with
  | cut A Lam Theta => simp [substRule, G1nnfRule.cutFormula, Option.map]
  | axiomPosAtomic _ _ _ _ => simp [substRule, G1nnfRule.cutFormula, Option.map]
  | axiomNegAtomic _ _ _ _ => simp [substRule, G1nnfRule.cutFormula, Option.map]
  | axiomCompLeft _ _ _ _ => simp [substRule, G1nnfRule.cutFormula, Option.map]
  | axiomCompRight _ _ _ _ => simp [substRule, G1nnfRule.cutFormula, Option.map]
  | conjLeft1 _ _ => simp [substRule, G1nnfRule.cutFormula, Option.map]
  | conjLeft2 _ _ => simp [substRule, G1nnfRule.cutFormula, Option.map]
  | conjRight _ _ => simp [substRule, G1nnfRule.cutFormula, Option.map]
  | disjLeft _ _ => simp [substRule, G1nnfRule.cutFormula, Option.map]
  | disjRight1 _ _ => simp [substRule, G1nnfRule.cutFormula, Option.map]
  | disjRight2 _ _ => simp [substRule, G1nnfRule.cutFormula, Option.map]
  | allLeft x A u =>
    simp only [substRule]; split <;> simp [G1nnfRule.cutFormula, Option.map]
  | allRight x A ev =>
    simp only [substRule]; split <;> simp [G1nnfRule.cutFormula, Option.map]
  | exLeft x A ev =>
    simp only [substRule]; split <;> simp [G1nnfRule.cutFormula, Option.map]
  | exRight x A u =>
    simp only [substRule]; split <;> simp [G1nnfRule.cutFormula, Option.map]

-- ===================================================================
-- Degree preservation: degree is invariant under formulaSubstN
-- ===================================================================
-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.EigenWeakening
theorem degree_formulaSubstN {L : Language} (A : FormulaN L)
    (t : Term L) (x : Nat) :
    (formulaSubstN A t x).degree = A.degree := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => rfl
  | eq_ _ _ => rfl
  | neg A ih =>
    cases A with
    | predN _ _ => simp [formulaSubstN, FormulaN.degree]
    | eq_ _ _ => simp [formulaSubstN, FormulaN.degree]
    | conj A' B' => simp [formulaSubstN, FormulaN.degree]
    | disj A' B' => simp [formulaSubstN, FormulaN.degree]
    | impl A' B' => simp [formulaSubstN, FormulaN.degree]
    | neg A' => simp [formulaSubstN, FormulaN.degree]
    | all y A' =>
      simp only [formulaSubstN]
      split <;> simp [FormulaN.degree]
    | ex y A' =>
      simp only [formulaSubstN]
      split <;> simp [FormulaN.degree]
  | conj A B ihA ihB =>
    simp only [formulaSubstN, FormulaN.degree, ihA, ihB]
  | disj A B ihA ihB =>
    simp only [formulaSubstN, FormulaN.degree, ihA, ihB]
  | impl A B ihA ihB =>
    simp only [formulaSubstN, FormulaN.degree]
  | all y A ih =>
    simp only [formulaSubstN]
    by_cases hxy : (x != y) = true
    · simp [hxy, FormulaN.degree, ih]
    · simp [hxy, FormulaN.degree]
  | ex y A ih =>
    simp only [formulaSubstN]
    by_cases hxy : (x != y) = true
    · simp [hxy, FormulaN.degree, ih]
    · simp [hxy, FormulaN.degree]

-- ===================================================================
-- substRule_eigenvariable_eq: eigenvariable is preserved by substRule
-- ===================================================================
-- ===================================================================
-- Substitution composition lemmas (formula-level)
-- ===================================================================
-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming, LCS.Herbrand.SHGTheorem.Herbrand.ClosedSubstitution
theorem termSubst_not_free {L : Language} (r t : Term L) (x : Nat)
    (h : ¬ termFV r x) : termSubst r t x = r := by
-- BEGIN PROOF
  induction r with
  | var n =>
    simp only [termSubst]
    by_cases hnx : n = x
    · subst hnx; exfalso; apply h; simp [termFV, Set.singleton]
    · simp only [if_neg hnx]
  | const c => simp only [termSubst]
  | func f ts ih =>
    simp only [termSubst, Term.func.injEq, heq_eq_eq, true_and]
    funext i; apply ih i; intro hi; apply h; simp only [termFV]; exact ⟨i, hi⟩

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
theorem termSubst_composition {L : Language}
    (r t u : Term L) (x y : Nat)
    (hyx : y ≠ x) (hxt : ¬ termFV t x) :
    termSubst (termSubst r u x) t y
      = termSubst (termSubst r t y) (termSubst u t y) x := by
-- BEGIN PROOF
  induction r with
  | var n =>
    simp only [termSubst]
    by_cases hnx : n = x
    · subst hnx
      simp only [if_true]
      have hneqxy : ¬ (n = y) := fun h => by subst h; exact hyx rfl
      simp only [termSubst, if_neg hneqxy, if_true]
    · simp only [if_neg hnx]
      by_cases hny : n = y
      · subst hny
        simp only [if_true, termSubst, if_true]
        exact (termSubst_not_free t (termSubst u t n) x hxt).symm
      · simp only [if_neg hny, termSubst, if_neg hnx]
  | const c => simp only [termSubst]
  | func f ts ih =>
    simp only [termSubst, Term.func.injEq, heq_eq_eq, true_and]
    funext i; exact ih i

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Substitution, LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression
theorem formulaSubstN_composition {L : Language}
    (A : FormulaN L) (t u : Term L) (x y : Nat)
    (hyx : y ≠ x) (hxt : ¬ termFV t x)
    (hyA : ¬ formulaBVN A y)
    (hff : isFreeForN t y A) :
    formulaSubstN (formulaSubstN A u x) t y
      = formulaSubstN (formulaSubstN A t y) (termSubst u t y) x := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    simp only [formulaSubstN, FormulaN.predN.injEq, heq_eq_eq, true_and]
    funext i; exact termSubst_composition (ts i) t u x y hyx hxt
  | eq_ hL t1 t2 =>
    simp only [formulaSubstN, FormulaN.eq_.injEq, heq_eq_eq, true_and]
    exact ⟨termSubst_composition t1 t u x y hyx hxt,
           termSubst_composition t2 t u x y hyx hxt⟩
  | neg A ih =>
    simp only [formulaSubstN, FormulaN.neg.injEq]
    exact ih hyA hff
  | conj A B ihA ihB =>
    simp only [formulaSubstN, FormulaN.conj.injEq]
    refine ⟨ihA ?_ hff.1, ihB ?_ hff.2⟩
    · intro h; apply hyA; exact Or.inl h
    · intro h; apply hyA; exact Or.inr h
  | disj A B ihA ihB =>
    simp only [formulaSubstN, FormulaN.disj.injEq]
    refine ⟨ihA ?_ hff.1, ihB ?_ hff.2⟩
    · intro h; apply hyA; exact Or.inl h
    · intro h; apply hyA; exact Or.inr h
  | impl A B ihA ihB =>
    simp only [formulaSubstN, FormulaN.impl.injEq]
    refine ⟨ihA ?_ hff.1, ihB ?_ hff.2⟩
    · intro h; apply hyA; exact Or.inl h
    · intro h; apply hyA; exact Or.inr h
  | all z A ih =>
    have hzy : y ≠ z := by
      intro hzy; apply hyA; subst hzy
      show (formulaBVN A ∪ Set.singleton y) y; right; rfl
    have hff_ : isFreeForN t y A := by
      unfold isFreeForN at hff
      rcases hff with rfl | hff
      · exact absurd rfl hzy
      · exact hff.2
    have hyA_ : ¬ formulaBVN A y := by
      intro h; apply hyA
      show (formulaBVN A ∪ Set.singleton z) y; left; exact h
    by_cases hxz : x = z
    · subst hxz
      have hxx : (x != x) = false := by simp
      have hyx_ : (y != x) = true := by simp; exact fun h => hyx h
      rw [show formulaSubstN (.all x A) u x = .all x A from by
        simp only [formulaSubstN, hxx]; rfl]
      rw [show formulaSubstN (.all x A) t y = .all x (formulaSubstN A t y) from by
        simp only [formulaSubstN, hyx_]; rfl]
      rw [show formulaSubstN (.all x (formulaSubstN A t y)) (termSubst u t y) x
            = .all x (formulaSubstN A t y) from by
        simp only [formulaSubstN, hxx]; rfl]
    · have hxz_ : (x != z) = true := by simp; exact hxz
      have hyz_ : (y != z) = true := by simp; exact hzy
      rw [show formulaSubstN (.all z A) u x = .all z (formulaSubstN A u x) from by
        simp only [formulaSubstN, hxz_]; rfl]
      rw [show formulaSubstN (.all z A) t y = .all z (formulaSubstN A t y) from by
        simp only [formulaSubstN, hyz_]; rfl]
      rw [show formulaSubstN (.all z (formulaSubstN A u x)) t y
            = .all z (formulaSubstN (formulaSubstN A u x) t y) from by
        simp only [formulaSubstN, hyz_]; rfl]
      rw [show formulaSubstN (.all z (formulaSubstN A t y)) (termSubst u t y) x
            = .all z (formulaSubstN (formulaSubstN A t y) (termSubst u t y) x) from by
        simp only [formulaSubstN, hxz_]; rfl]
      exact congrArg (FormulaN.all z) (ih hyA_ hff_)
  | ex z A ih =>
    have hzy : y ≠ z := by
      intro hzy; apply hyA; subst hzy
      show (formulaBVN A ∪ Set.singleton y) y; right; rfl
    have hff_ : isFreeForN t y A := by
      unfold isFreeForN at hff
      rcases hff with rfl | hff
      · exact absurd rfl hzy
      · exact hff.2
    have hyA_ : ¬ formulaBVN A y := by
      intro h; apply hyA
      show (formulaBVN A ∪ Set.singleton z) y; left; exact h
    by_cases hxz : x = z
    · subst hxz
      have hxx : (x != x) = false := by simp
      have hyx_ : (y != x) = true := by simp; exact fun h => hyx h
      rw [show formulaSubstN (.ex x A) u x = .ex x A from by
        simp only [formulaSubstN, hxx]; rfl]
      rw [show formulaSubstN (.ex x A) t y = .ex x (formulaSubstN A t y) from by
        simp only [formulaSubstN, hyx_]; rfl]
      rw [show formulaSubstN (.ex x (formulaSubstN A t y)) (termSubst u t y) x
            = .ex x (formulaSubstN A t y) from by
        simp only [formulaSubstN, hxx]; rfl]
    · have hxz_ : (x != z) = true := by simp; exact hxz
      have hyz_ : (y != z) = true := by simp; exact hzy
      rw [show formulaSubstN (.ex z A) u x = .ex z (formulaSubstN A u x) from by
        simp only [formulaSubstN, hxz_]; rfl]
      rw [show formulaSubstN (.ex z A) t y = .ex z (formulaSubstN A t y) from by
        simp only [formulaSubstN, hyz_]; rfl]
      rw [show formulaSubstN (.ex z (formulaSubstN A u x)) t y
            = .ex z (formulaSubstN (formulaSubstN A u x) t y) from by
        simp only [formulaSubstN, hyz_]; rfl]
      rw [show formulaSubstN (.ex z (formulaSubstN A t y)) (termSubst u t y) x
            = .ex z (formulaSubstN (formulaSubstN A t y) (termSubst u t y) x) from by
        simp only [formulaSubstN, hxz_]; rfl]
      exact congrArg (FormulaN.ex z) (ih hyA_ hff_)

-- ===================================================================
-- Private substitution preparation: alpha/substitution interaction
-- ===================================================================
-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Freshening, LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression
theorem formulaSubstN_eq_self_of_not_free {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat)
    (h : x ∉ formulaFVN A) :
    formulaSubstN A t x = A := by
  induction A with
  | predN P ts =>
      simp only [formulaSubstN, FormulaN.predN.injEq, heq_eq_eq, true_and]
      funext i
      exact termSubst_not_free (ts i) t x (fun hm => h ⟨i, hm⟩)
  | eq_ _ t₁ t₂ =>
      simp only [formulaSubstN, FormulaN.eq_.injEq]
      exact
        ⟨termSubst_not_free t₁ t x (fun hm => h (Or.inl hm)),
         termSubst_not_free t₂ t x (fun hm => h (Or.inr hm))⟩
  | conj A B ihA ihB =>
      simp only [formulaSubstN, FormulaN.conj.injEq]
      exact
        ⟨ihA (fun hm => h (Or.inl hm)),
         ihB (fun hm => h (Or.inr hm))⟩
  | disj A B ihA ihB =>
      simp only [formulaSubstN, FormulaN.disj.injEq]
      exact
        ⟨ihA (fun hm => h (Or.inl hm)),
         ihB (fun hm => h (Or.inr hm))⟩
  | impl A B ihA ihB =>
      simp only [formulaSubstN, FormulaN.impl.injEq]
      exact
        ⟨ihA (fun hm => h (Or.inl hm)),
         ihB (fun hm => h (Or.inr hm))⟩
  | neg A ih =>
      simp only [formulaSubstN, FormulaN.neg.injEq]
      exact ih h
  | all w A ih =>
      simp only [formulaSubstN]
      split
      · simp only [FormulaN.all.injEq, true_and]
        exact
          ih (fun hm =>
            h ⟨hm, by
              rename_i hne
              exact bne_iff_ne.mp hne⟩)
      · rfl
  | ex w A ih =>
      simp only [formulaSubstN]
      split
      · simp only [FormulaN.ex.injEq, true_and]
        exact
          ih (fun hm =>
            h ⟨hm, by
              rename_i hne
              exact bne_iff_ne.mp hne⟩)
      · rfl

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.EigenWeakening, LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression
theorem substFormulaFinset_eq_self_of_not_free {L : Language}
    (S : LCS.Finset (FormulaN L)) (t : Term L) (v : Nat)
    (hS : ∀ A ∈ S, v ∉ formulaFVN A) :
    substFormulaFinset S t v = S := by
  apply LCS.Finset.ext
  intro A
  rw [substFormulaFinset, LCS.Finset.mem_image]
  constructor
  · rintro ⟨B, hB, rfl⟩
    simpa only [formulaSubstN_eq_self_of_not_free B t v (hS B hB)]
      using hB
  · intro hA
    exact
      ⟨A, hA,
       formulaSubstN_eq_self_of_not_free A t v (hS A hA)⟩

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
theorem termSubst_via_fresh {L : Language}
    (r t : Term L) (v z : Nat)
    (hzv : z ≠ v) (hzr : z ∉ termFV r) :
    termSubst (termSubst r (.var z) v) t z =
      termSubst r t v := by
  induction r with
  | var n =>
      by_cases hnv : n = v
      · subst n
        simp [termSubst, hzv]
      · have hnz : n ≠ z := by
          intro hnz
          subst n
          exact hzr rfl
        simp [termSubst, hnv, hnz]
  | const c =>
      rfl
  | func f ts ih =>
      simp only [termSubst, Term.func.injEq, heq_eq_eq, true_and]
      funext i
      exact ih i (fun h => hzr ⟨i, h⟩)

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.EigenWeakening
theorem formulaSubstN_eigenInstance {L : Language}
    (A : FormulaN L) (x v z : Nat)
    (hxv : x ≠ v) (hvFree : v ∉ formulaFVN A)
    (hvBound : v ∉ formulaBVN A) :
    formulaSubstN (formulaSubstN A (.var v) x) (.var z) v =
      formulaSubstN A (.var z) x := by
  induction A with
  | predN P ts =>
      simp only [formulaSubstN, FormulaN.predN.injEq, heq_eq_eq, true_and]
      funext i
      exact
        termSubst_via_fresh (ts i) (.var z) x v
          (Ne.symm hxv) (fun h => hvFree ⟨i, h⟩)
  | eq_ hL t₁ t₂ =>
      simp only [formulaSubstN, FormulaN.eq_.injEq, heq_eq_eq, true_and]
      exact
        ⟨termSubst_via_fresh t₁ (.var z) x v (Ne.symm hxv)
            (fun h => hvFree (Or.inl h)),
         termSubst_via_fresh t₂ (.var z) x v (Ne.symm hxv)
            (fun h => hvFree (Or.inr h))⟩
  | neg A ih =>
      simp only [formulaSubstN, FormulaN.neg.injEq]
      exact ih hvFree hvBound
  | conj A B ihA ihB =>
      simp only [formulaSubstN, FormulaN.conj.injEq]
      exact
        ⟨ihA (fun h => hvFree (Or.inl h))
            (fun h => hvBound (Or.inl h)),
         ihB (fun h => hvFree (Or.inr h))
            (fun h => hvBound (Or.inr h))⟩
  | disj A B ihA ihB =>
      simp only [formulaSubstN, FormulaN.disj.injEq]
      exact
        ⟨ihA (fun h => hvFree (Or.inl h))
            (fun h => hvBound (Or.inl h)),
         ihB (fun h => hvFree (Or.inr h))
            (fun h => hvBound (Or.inr h))⟩
  | impl A B ihA ihB =>
      simp only [formulaSubstN, FormulaN.impl.injEq]
      exact
        ⟨ihA (fun h => hvFree (Or.inl h))
            (fun h => hvBound (Or.inl h)),
         ihB (fun h => hvFree (Or.inr h))
            (fun h => hvBound (Or.inr h))⟩
  | all w A ih =>
      have hvw : v ≠ w := fun h => hvBound (Or.inr h)
      have hvFreeA : v ∉ formulaFVN A :=
        fun h => hvFree ⟨h, hvw⟩
      have hvBoundA : v ∉ formulaBVN A :=
        fun h => hvBound (Or.inl h)
      by_cases hxw : x = w
      · subst x
        simpa [formulaSubstN, hvw] using
          congrArg (FormulaN.all w)
            (formulaSubstN_eq_self_of_not_free
              A (.var z) v hvFreeA)
      · simpa [formulaSubstN, hxw, hvw] using
          congrArg (FormulaN.all w) (ih hvFreeA hvBoundA)
  | ex w A ih =>
      have hvw : v ≠ w := fun h => hvBound (Or.inr h)
      have hvFreeA : v ∉ formulaFVN A :=
        fun h => hvFree ⟨h, hvw⟩
      have hvBoundA : v ∉ formulaBVN A :=
        fun h => hvBound (Or.inl h)
      by_cases hxw : x = w
      · subst x
        simpa [formulaSubstN, hvw] using
          congrArg (FormulaN.ex w)
            (formulaSubstN_eq_self_of_not_free
              A (.var z) v hvFreeA)
      · simpa [formulaSubstN, hxw, hvw] using
          congrArg (FormulaN.ex w) (ih hvFreeA hvBoundA)

end LCS.CutElim.Hauptsatz
end
