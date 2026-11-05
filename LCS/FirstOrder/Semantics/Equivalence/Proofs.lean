import LCS.FirstOrder.Semantics.Equivalence

namespace LCS.FirstOrder.Semantics.Equivalence

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.Syntax

open LCS.FirstOrder.SemanticsN

open Classical

helper /-- Definition 5.3.12 (companion): The truth constant is true in every
structure under every assignment. -/
theorem formulaEvalT_top {L : Language} (M : Structure L) (s : Assignment M) :
    formulaEvalT M FormulaT.top s = True := rfl

helper /-- Definition 5.3.12 (companion): Embedding a normalized formula
preserves its truth value under every interpretation and assignment. -/
theorem formulaEvalT_ofFormulaN {L : Language} (M : Structure L)
    (A : FormulaN L) (s : Assignment M) :
    formulaEvalT M (FormulaT.ofFormulaN A) s ↔ formulaEvalN M A s := by
  induction A generalizing s with
  | predN P ts => exact Iff.rfl
  | eq_ hL t u => exact Iff.rfl
  | neg A ih => exact not_congr (ih s)
  | conj A B ihA ihB => exact and_congr (ihA s) (ihB s)
  | disj A B ihA ihB => exact or_congr (ihA s) (ihB s)
  | impl A B ihA ihB => exact imp_congr (ihA s) (ihB s)
  | all x A ih =>
    exact ⟨fun h a => (ih (assignUpdate s x a)).mp (h a),
      fun h a => (ih (assignUpdate s x a)).mpr (h a)⟩
  | ex x A ih => exact exists_congr (fun a => ih (assignUpdate s x a))

proof_of foLogEquivT_refl := by
  -- BEGIN PROOF
    intro M s
    simp [formulaEvalT]


proof_of foLogEquivT_symm := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivT, universallyValidT, formulaEvalT] at *
    obtain ⟨hab, hba⟩ := h M s
    exact ⟨hba, hab⟩


proof_of foLogEquivT_trans := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivT, universallyValidT, formulaEvalT] at *
    obtain ⟨hab, hba⟩ := h1 M s
    obtain ⟨hbc, hcb⟩ := h2 M s
    exact ⟨fun ha => hbc (hab ha), fun hc => hba (hcb hc)⟩


proof_of foLogEquivT_conj := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivT, universallyValidT, formulaEvalT] at *
    obtain ⟨hAf, hAb⟩ := hA M s
    obtain ⟨hBf, hBb⟩ := hB M s
    exact ⟨fun ⟨ha, hb⟩ => ⟨hAf ha, hBf hb⟩, fun ⟨ha', hb'⟩ => ⟨hAb ha', hBb hb'⟩⟩


proof_of foLogEquivT_disj := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivT, universallyValidT, formulaEvalT] at *
    obtain ⟨hAf, hAb⟩ := hA M s
    obtain ⟨hBf, hBb⟩ := hB M s
    exact ⟨fun h => h.elim (Or.inl ∘ hAf) (Or.inr ∘ hBf),
           fun h => h.elim (Or.inl ∘ hAb) (Or.inr ∘ hBb)⟩


proof_of foLogEquivT_impl := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivT, universallyValidT, formulaEvalT] at *
    obtain ⟨hAf, hAb⟩ := hA M s
    obtain ⟨hBf, hBb⟩ := hB M s
    exact ⟨fun h ha' => hBf (h (hAb ha')), fun h ha => hBb (h (hAf ha))⟩


proof_of foLogEquivT_equiv := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivT, universallyValidT, formulaEvalT] at *
    obtain ⟨hAf, hAb⟩ := hA M s
    obtain ⟨hBf, hBb⟩ := hB M s
    exact ⟨fun ⟨hab, hba⟩ => ⟨fun ha' => hBf (hab (hAb ha')), fun hb' => hAf (hba (hBb hb'))⟩,
           fun ⟨hab', hba'⟩ => ⟨fun ha => hBb (hab' (hAf ha)), fun hb => hAb (hba' (hBf hb))⟩⟩


proof_of foLogEquivT_neg := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivT, universallyValidT, formulaEvalT] at *
    obtain ⟨hf, hb⟩ := h M s
    exact ⟨fun hna ha' => hna (hb ha'), fun hna' ha => hna' (hf ha)⟩


proof_of foLogEquivT_all := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivT, universallyValidT, formulaEvalT] at *
    exact ⟨fun hall a => (h M (assignUpdate s x a)).1 (hall a),
           fun hall a => (h M (assignUpdate s x a)).2 (hall a)⟩


proof_of foLogEquivT_ex := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivT, universallyValidT, formulaEvalT] at *
    exact ⟨fun ⟨a, ha⟩ => ⟨a, (h M (assignUpdate s x a)).1 ha⟩,
           fun ⟨a, ha'⟩ => ⟨a, (h M (assignUpdate s x a)).2 ha'⟩⟩


proof_of validF_equiv_elimination := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    exact ⟨fun h => ⟨h.mp, h.mpr⟩, fun h => ⟨h.1, h.2⟩⟩


proof_of validF_impl_as_disj := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    exact ⟨fun h => (em _).elim (fun ha => Or.inr (h ha)) Or.inl,
           fun h ha => h.elim (fun hna => absurd ha hna) id⟩


proof_of validF_disj_as_impl := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    exact ⟨fun h hna => h.elim (fun ha => absurd ha hna) id,
           fun h => (em _).elim Or.inl (fun hna => Or.inr (h hna))⟩


proof_of validF_disj_as_neg_conj := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    exact ⟨fun h ⟨hna, hnb⟩ => h.elim (fun ha => hna ha) (fun hb => hnb hb),
           fun h => (em _).elim Or.inl (fun hna =>
             Or.inr ((em _).elim id (fun hnb => absurd ⟨hna, hnb⟩ h)))⟩


proof_of validF_conj_as_neg_disj := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    exact ⟨fun ⟨ha, hb⟩ h => h.elim (fun hna => hna ha) (fun hnb => hnb hb),
           fun h => ⟨byContradiction (fun hna => h (Or.inl hna)),
                      byContradiction (fun hnb => h (Or.inr hnb))⟩⟩


proof_of validF_neg_as_impl_falsum := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    exact Iff.rfl


proof_of validF_falsum_as_contradiction := by
  intro M s
  exact ⟨False.elim, fun h => h.2 h.1⟩


proof_of validF_neg_all_as_ex_neg := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    exact ⟨Classical.not_forall.mp, fun ⟨a, hna⟩ h => hna (h a)⟩


proof_of quantifierDuality_valid_not_inPROPL := ⟨validF_neg_all_as_ex_neg x A, Subformulae.quantifierDuality_not_inPROPL A x⟩


proof_of validF_neg_ex_as_all_neg := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    exact ⟨fun h a ha => h ⟨a, ha⟩, fun h ⟨a, ha⟩ => h a ha⟩


proof_of validF_all_as_neg_ex_neg := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    exact ⟨fun h ⟨a, hna⟩ => hna (h a), fun h a => byContradiction (fun hna => h ⟨a, hna⟩)⟩


proof_of validF_ex_as_neg_all_neg := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEval]
    exact ⟨fun ⟨a, ha⟩ h => h a ha, fun h => byContradiction (fun hne => h (fun a ha => hne ⟨a, ha⟩))⟩


helper /-- Substitute arbitrary first-order formulae for the letters of a propositional formula. -/
def instantiateProp {L : Language} {α : Type} (σ : α → Formula L) :
    Subformulae.PropFormulaOver α → Formula L
  | .fls => .falsum
  | .var a => σ a
  | .neg A => .neg (instantiateProp σ A)
  | .conj A B => .conj (instantiateProp σ A) (instantiateProp σ B)
  | .disj A B => .disj (instantiateProp σ A) (instantiateProp σ B)
  | .impl A B => .impl (instantiateProp σ A) (instantiateProp σ B)
  | .equiv_ A B => .equiv_ (instantiateProp σ A) (instantiateProp σ B)

helper /-- Substitution of formulae evaluates by their truth values. -/
theorem instantiateProp_eval {L : Language} {α : Type} (σ : α → Formula L)
    (B : Subformulae.PropFormulaOver α) (M : Structure L) (s : Assignment M) :
    formulaEval M (instantiateProp σ B) s ↔
      Subformulae.evalProp (fun a => formulaEval M (σ a) s) B := by
  induction B <;> simp_all [instantiateProp, formulaEval, Subformulae.evalProp,
    Basic.andM, Basic.orM, implM, equivM, negM]

helper /-- Propositional substitution preserves the permitted connective set. -/
theorem instantiateProp_usesConnectives {L : Language} {α : Type}
    (K : FormulaConnective → Prop) (σ : α → Formula L)
    (hσ : ∀ a, usesConnectives K (σ a)) (B : Subformulae.PropFormulaOver α)
    (hB : ∀ c ∈ propConnectives B, K c) : usesConnectives K (instantiateProp σ B) := by
  induction B <;> simp_all [instantiateProp, usesConnectives, formulaConnectives,
    propConnectives, List.mem_cons, List.mem_append, or_imp, forall_and]
  exact hσ _

helper /-- A complete propositional basis realizes truth functions of first-order formulae. -/
theorem realizeTruthFunction {L : Language} {K : FormulaConnective → Prop}
    (hK : functionallyComplete K) (n : Nat) (hn : 0 < n)
    (f : (Fin n → Prop) → Prop) (σ : Fin n → Formula L)
    (hσ : ∀ i, usesConnectives K (σ i)) :
    ∃ B : Formula L, usesConnectives K B ∧
      ∀ (M : Structure L) (s : Assignment M),
        formulaEval M B s ↔ f (fun i => formulaEval M (σ i) s) := by
  obtain ⟨B, hB, he⟩ := hK n hn f
  exact ⟨instantiateProp σ B, instantiateProp_usesConnectives K σ hσ B hB,
    fun M s => (instantiateProp_eval σ B M s).trans (he _)⟩

proof_of formula_connectiveReduction := by
  induction A with
  | falsum =>
    rcases hbase with hb | ⟨a, ha⟩
    · exact ⟨.falsum, by simpa [usesConnectives, formulaConnectives] using hb,
        fun _ _ => Iff.rfl⟩
    · obtain ⟨B, hB, he⟩ := realizeTruthFunction hK 1 (by decide) (fun _ => False)
        (fun _ => a) (fun _ => by simp [usesConnectives, ha])
      exact ⟨B, hB, fun M s => (he M s).symm⟩
  | pred0 P h => exact ⟨.pred0 P h, by simp [usesConnectives, formulaConnectives], fun _ _ => Iff.rfl⟩
  | predN P h ts => exact ⟨.predN P h ts, by simp [usesConnectives, formulaConnectives], fun _ _ => Iff.rfl⟩
  | eq_ h t u => exact ⟨.eq_ h t u, by simp [usesConnectives, formulaConnectives], fun _ _ => Iff.rfl⟩
  | neg A ih =>
    obtain ⟨B, hB, he⟩ := ih
    obtain ⟨C, hC, hc⟩ := realizeTruthFunction hK 1 (by decide) (fun v => ¬ v 0)
      (fun _ => B) (fun _ => hB)
    refine ⟨C, hC, fun M s => ?_⟩
    exact (not_congr (he M s)).trans (hc M s).symm
  | conj A D ihA ihD =>
    obtain ⟨B, hB, hb⟩ := ihA
    obtain ⟨C, hC, hc⟩ := ihD
    obtain ⟨E, hE, he⟩ := realizeTruthFunction hK 2 (by decide)
      (fun v => v 0 ∧ v 1) (fun i => if i.val = 0 then B else C)
      (fun i => by split <;> assumption)
    refine ⟨E, hE, fun M s => ?_⟩
    have h := (he M s).symm
    simpa [formulaEval, Basic.andM, Basic.orM, implM, equivM, ← propext (hb M s), ← propext (hc M s)] using h
  | disj A D ihA ihD =>
    obtain ⟨B, hB, hb⟩ := ihA
    obtain ⟨C, hC, hc⟩ := ihD
    obtain ⟨E, hE, he⟩ := realizeTruthFunction hK 2 (by decide)
      (fun v => v 0 ∨ v 1) (fun i => if i.val = 0 then B else C)
      (fun i => by split <;> assumption)
    refine ⟨E, hE, fun M s => ?_⟩
    have h := (he M s).symm
    simpa [formulaEval, Basic.andM, Basic.orM, implM, equivM, ← propext (hb M s), ← propext (hc M s)] using h
  | impl A D ihA ihD =>
    obtain ⟨B, hB, hb⟩ := ihA
    obtain ⟨C, hC, hc⟩ := ihD
    obtain ⟨E, hE, he⟩ := realizeTruthFunction hK 2 (by decide)
      (fun v => v 0 → v 1) (fun i => if i.val = 0 then B else C)
      (fun i => by split <;> assumption)
    refine ⟨E, hE, fun M s => ?_⟩
    have h := (he M s).symm
    simpa [formulaEval, Basic.andM, Basic.orM, implM, equivM, ← propext (hb M s), ← propext (hc M s)] using h
  | equiv_ A D ihA ihD =>
    obtain ⟨B, hB, hb⟩ := ihA
    obtain ⟨C, hC, hc⟩ := ihD
    obtain ⟨E, hE, he⟩ := realizeTruthFunction hK 2 (by decide)
      (fun v => v 0 ↔ v 1) (fun i => if i.val = 0 then B else C)
      (fun i => by split <;> assumption)
    refine ⟨E, hE, fun M s => ?_⟩
    have h := (he M s).symm
    simpa [formulaEval, Basic.andM, Basic.orM, implM, equivM, ← propext (hb M s), ← propext (hc M s)] using h
  | all x A ih =>
    obtain ⟨B, hB, hb⟩ := ih
    refine ⟨.all x B, ?_, fun M s => ?_⟩
    · simpa [usesConnectives, formulaConnectives] using hB
    · simp only [formulaEval]
      simp only [show ∀ s, formulaEval M A s = formulaEval M B s from
        fun s => propext (hb M s), equivM, iff_self]
  | ex x A ih =>
    obtain ⟨B, hB, hb⟩ := ih
    refine ⟨.ex x B, ?_, fun M s => ?_⟩
    · simpa [usesConnectives, formulaConnectives] using hB
    · simp only [formulaEval]
      simp only [show ∀ s, formulaEval M A s = formulaEval M B s from
        fun s => propext (hb M s), equivM, iff_self]


helper /-- Eliminate ∃ when `useAll` is true, or ∀ when it is false, recursively
using ¬∀x¬A and ¬∃x¬A respectively. -/
def eliminateQuantifier {L : Language} (useAll : Bool) : Formula L → Formula L
  | .falsum => .falsum
  | .pred0 P h => .pred0 P h
  | .predN P h ts => .predN P h ts
  | .eq_ h t u => .eq_ h t u
  | .neg A => .neg (eliminateQuantifier useAll A)
  | .conj A B => .conj (eliminateQuantifier useAll A) (eliminateQuantifier useAll B)
  | .disj A B => .disj (eliminateQuantifier useAll A) (eliminateQuantifier useAll B)
  | .impl A B => .impl (eliminateQuantifier useAll A) (eliminateQuantifier useAll B)
  | .equiv_ A B => .equiv_ (eliminateQuantifier useAll A) (eliminateQuantifier useAll B)
  | .all x A => if useAll then .all x (eliminateQuantifier useAll A)
      else .neg (.ex x (.neg (eliminateQuantifier useAll A)))
  | .ex x A => if useAll then .neg (.all x (.neg (eliminateQuantifier useAll A)))
      else .ex x (eliminateQuantifier useAll A)

helper /-- The selected quantifier is absent throughout the translated formula. -/
theorem eliminateQuantifier_free {L : Language} (useAll : Bool) (A : Formula L) :
    (if useAll then FormulaConnective.ex else .all) ∉
      formulaConnectives (eliminateQuantifier useAll A) := by
  induction A <;> cases useAll <;>
    simp_all [eliminateQuantifier, formulaConnectives]

helper /-- Quantifier elimination by duality preserves truth under every assignment. -/
theorem eliminateQuantifier_equiv {L : Language} (useAll : Bool) (A : Formula L) :
    universallyValid (.equiv_ A (eliminateQuantifier useAll A)) := by
  intro M s
  induction A generalizing s <;> cases useAll <;>
    simp_all [eliminateQuantifier, formulaEval, Basic.andM, Basic.orM, implM, equivM, negM,
      Classical.not_forall]

proof_of formula_existsFree_equivalent := ⟨eliminateQuantifier true A, eliminateQuantifier_free true A,
    eliminateQuantifier_equiv true A⟩


proof_of formula_forallFree_equivalent := ⟨eliminateQuantifier false A, eliminateQuantifier_free false A,
    eliminateQuantifier_equiv false A⟩


helper /-- For normalized formulae, (A equiv B) equiv ((A supset B) wedge (B supset A)) is
universally valid. The biconditional can be eliminated in terms of conjunction and implication. -/
theorem valid_equiv_elimination {L : Language} (A B : FormulaN L) :
    universallyValidN (FormulaN.equiv
      (FormulaN.equiv A B)
      (FormulaN.conj (FormulaN.impl A B) (FormulaN.impl B A))) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  exact ⟨fun h => h, fun h => h⟩



helper /-- For normalized formulae, (A vee B) equiv (neg A supset B) is universally
valid. Disjunction can be expressed as implication with negation. -/
theorem valid_disj_as_impl {L : Language} (A B : FormulaN L) :
    universallyValidN (FormulaN.equiv
      (FormulaN.disj A B)
      (FormulaN.impl (FormulaN.neg A) B)) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  exact ⟨fun h hna => h.elim (fun ha => absurd ha hna) id,
         fun h => (em _).elim Or.inl (fun hna => Or.inr (h hna))⟩

helper /-- For normalized formulae, (A vee B) equiv neg(neg A wedge neg B) is
universally valid. Disjunction expressed as negated conjunction. -/
theorem valid_disj_as_neg_conj {L : Language} (A B : FormulaN L) :
    universallyValidN (FormulaN.equiv
      (FormulaN.disj A B)
      (FormulaN.neg (FormulaN.conj (FormulaN.neg A) (FormulaN.neg B)))) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  exact ⟨fun h ⟨hna, hnb⟩ => h.elim (fun ha => hna ha) (fun hb => hnb hb),
         fun h => (em _).elim Or.inl (fun hna =>
           Or.inr ((em _).elim id (fun hnb => absurd ⟨hna, hnb⟩ h)))⟩

helper /-- For normalized formulae, (A wedge B) equiv neg(neg A vee neg B) is
universally valid. Conjunction expressed as negated disjunction. -/
theorem valid_conj_as_neg_disj {L : Language} (A B : FormulaN L) :
    universallyValidN (FormulaN.equiv
      (FormulaN.conj A B)
      (FormulaN.neg (FormulaN.disj (FormulaN.neg A) (FormulaN.neg B)))) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  exact ⟨fun ⟨ha, hb⟩ h => h.elim (fun hna => hna ha) (fun hnb => hnb hb),
         fun h => ⟨byContradiction (fun hna => h (Or.inl hna)),
                    byContradiction (fun hnb => h (Or.inr hnb))⟩⟩

helper /-- For normalized formulae, ¬A is logically equivalent to
A ⊃ (A ∧ ¬A): negation is expressed as implication to a contradiction. -/
theorem valid_neg_as_impl_contradiction {L : Language} (A : FormulaN L) :
    universallyValidN (FormulaN.equiv
      (FormulaN.neg A)
      (FormulaN.impl A (FormulaN.falsum A))) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  exact ⟨fun hna ha => ⟨ha, hna⟩, fun h ha => (h ha).2 ha⟩

helper /-- For normalized formulae, neg forall x A equiv exists x neg A is universally
valid. Negated universal as existential negation. -/
theorem valid_neg_all_as_ex_neg {L : Language} (x : Nat)
    (A : FormulaN L) :
    universallyValidN (FormulaN.equiv
      (FormulaN.neg (FormulaN.all x A))
      (FormulaN.ex x (FormulaN.neg A))) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  exact ⟨Classical.not_forall.mp, fun ⟨a, hna⟩ h => hna (h a)⟩

helper /-- For normalized formulae, neg exists x A equiv forall x neg A is universally
valid. Negated existential as universal negation. -/
theorem valid_neg_ex_as_all_neg {L : Language} (x : Nat)
    (A : FormulaN L) :
    universallyValidN (FormulaN.equiv
      (FormulaN.neg (FormulaN.ex x A))
      (FormulaN.all x (FormulaN.neg A))) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  exact ⟨fun h a ha => h ⟨a, ha⟩, fun h ⟨a, ha⟩ => h a ha⟩

helper /-- For normalized formulae, forall x A equiv neg exists x neg A is universally
valid. Universal as negated existential negation. -/
theorem valid_all_as_neg_ex_neg {L : Language} (x : Nat)
    (A : FormulaN L) :
    universallyValidN (FormulaN.equiv
      (FormulaN.all x A)
      (FormulaN.neg (FormulaN.ex x (FormulaN.neg A)))) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  exact ⟨fun h ⟨a, hna⟩ => hna (h a), fun h a => byContradiction (fun hna => h ⟨a, hna⟩)⟩

helper /-- For normalized formulae, exists x A equiv neg forall x neg A is universally
valid. Existential as negated universal negation. -/
theorem valid_ex_as_neg_all_neg {L : Language} (x : Nat)
    (A : FormulaN L) :
    universallyValidN (FormulaN.equiv
      (FormulaN.ex x A)
      (FormulaN.neg (FormulaN.all x (FormulaN.neg A)))) :=
-- BEGIN PROOF
by
  intro M s
  simp only [formulaEvalN]
  exact ⟨fun ⟨a, ha⟩ h => h a ha, fun h => byContradiction (fun hne => h (fun a ha => hne ⟨a, ha⟩))⟩







proof_of foLogEquivN_conj := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivN, universallyValidN, validInN, formulaEvalN] at *
    obtain ⟨hAf, hAb⟩ := hA M s
    obtain ⟨hBf, hBb⟩ := hB M s
    exact ⟨fun ⟨ha, hb⟩ => ⟨hAf ha, hBf hb⟩, fun ⟨ha', hb'⟩ => ⟨hAb ha', hBb hb'⟩⟩


proof_of foLogEquivN_disj := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivN, universallyValidN, validInN, formulaEvalN] at *
    obtain ⟨hAf, hAb⟩ := hA M s
    obtain ⟨hBf, hBb⟩ := hB M s
    exact ⟨fun h => h.elim (Or.inl ∘ hAf) (Or.inr ∘ hBf),
           fun h => h.elim (Or.inl ∘ hAb) (Or.inr ∘ hBb)⟩


proof_of foLogEquivN_impl := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivN, universallyValidN, validInN, formulaEvalN] at *
    obtain ⟨hAf, hAb⟩ := hA M s
    obtain ⟨hBf, hBb⟩ := hB M s
    exact ⟨fun h ha' => hBf (h (hAb ha')), fun h ha => hBb (h (hAf ha))⟩


proof_of foLogEquivN_equiv := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivN, universallyValidN, validInN, formulaEvalN] at *
    obtain ⟨hAf, hAb⟩ := hA M s
    obtain ⟨hBf, hBb⟩ := hB M s
    exact ⟨fun ⟨hab, hba⟩ => ⟨fun ha' => hBf (hab (hAb ha')), fun hb' => hAf (hba (hBb hb'))⟩,
           fun ⟨hab', hba'⟩ => ⟨fun ha => hBb (hab' (hAf ha)), fun hb => hAb (hba' (hBf hb))⟩⟩


proof_of foLogEquivN_neg := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivN, universallyValidN, validInN, formulaEvalN] at *
    obtain ⟨hf, hb⟩ := h M s
    exact ⟨fun hna ha' => hna (hb ha'), fun hna' ha => hna' (hf ha)⟩


proof_of foLogEquivN_all := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivN, universallyValidN, validInN, formulaEvalN] at *
    exact ⟨fun hall a => (h M (assignUpdate s x a)).1 (hall a),
           fun hall a => (h M (assignUpdate s x a)).2 (hall a)⟩


proof_of foLogEquivN_ex := by
  -- BEGIN PROOF
    intro M s
    simp only [foLogEquivN, universallyValidN, validInN, formulaEvalN] at *
    exact ⟨fun ⟨a, ha⟩ => ⟨a, (h M (assignUpdate s x a)).1 ha⟩,
           fun ⟨a, ha'⟩ => ⟨a, (h M (assignUpdate s x a)).2 ha'⟩⟩


helper /-- Lemma 5.3.6 (companion): A formula uses only ∨, ¬, and ∀ as
connectives; predicate and equality atoms are unrestricted. -/
def usesDisjNegAll {L : Language} : FormulaN L → Prop
  | .predN _ _ => True
  | .eq_ _ _ _ => True
  | .neg A => usesDisjNegAll A
  | .disj A B => usesDisjNegAll A ∧ usesDisjNegAll B
  | .all _ A => usesDisjNegAll A
  | .conj _ _ | .impl _ _ | .ex _ _ => False

helper /-- Lemma 5.3.6 (consequence): Every normalized formula is logically
equivalent to a formula whose only connectives are ∨, ¬, and ∀.
Thus the six-connective set used in §5.3.8 is not minimal. -/
theorem connectivesNonminimal {L : Language} (A : FormulaN L) :
    ∃ B : FormulaN L, usesDisjNegAll B ∧ foLogEquivN A B := by
  induction A with
  | predN P ts => exact ⟨.predN P ts, trivial, foLogEquivN_refl (.predN P ts)⟩
  | eq_ hL t u => exact ⟨.eq_ hL t u, trivial, foLogEquivN_refl (.eq_ hL t u)⟩
  | neg A ih =>
    obtain ⟨B, hB, hEq⟩ := ih
    exact ⟨.neg B, hB, foLogEquivN_neg hEq⟩
  | disj A C ihA ihC =>
    obtain ⟨B, hB, hAB⟩ := ihA
    obtain ⟨D, hD, hCD⟩ := ihC
    exact ⟨.disj B D, ⟨hB, hD⟩, foLogEquivN_disj hAB hCD⟩
  | conj A C ihA ihC =>
    obtain ⟨B, hB, hAB⟩ := ihA
    obtain ⟨D, hD, hCD⟩ := ihC
    exact ⟨.neg (.disj (.neg B) (.neg D)), ⟨hB, hD⟩,
      foLogEquivN_trans (valid_conj_as_neg_disj A C)
        (foLogEquivN_neg (foLogEquivN_disj
          (foLogEquivN_neg hAB) (foLogEquivN_neg hCD)))⟩
  | impl A C ihA ihC =>
    obtain ⟨B, hB, hAB⟩ := ihA
    obtain ⟨D, hD, hCD⟩ := ihC
    exact ⟨.disj (.neg B) D, ⟨hB, hD⟩,
      foLogEquivN_trans (valid_impl_as_disj A C)
        (foLogEquivN_disj (foLogEquivN_neg hAB) hCD)⟩
  | all x A ih =>
    obtain ⟨B, hB, hEq⟩ := ih
    exact ⟨.all x B, hB, foLogEquivN_all x hEq⟩
  | ex x A ih =>
    obtain ⟨B, hB, hEq⟩ := ih
    exact ⟨.neg (.all x (.neg B)), hB,
      foLogEquivN_trans (valid_ex_as_neg_all_neg x A)
        (foLogEquivN_neg (foLogEquivN_all x (foLogEquivN_neg hEq)))⟩

proof_of foLogEquivT_disj_assoc := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]; exact ⟨or_assoc.mp, or_assoc.mpr⟩


proof_of foLogEquivT_conj_assoc := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]; exact ⟨and_assoc.mp, and_assoc.mpr⟩


proof_of foLogEquivT_disj_comm := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]; exact ⟨Or.comm.mp, Or.comm.mpr⟩


proof_of foLogEquivT_conj_comm := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]; exact ⟨And.comm.mp, And.comm.mpr⟩


proof_of foLogEquivT_disj_distrib := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]; exact ⟨or_and_left.mp, or_and_left.mpr⟩


proof_of foLogEquivT_conj_distrib := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]; exact ⟨and_or_left.mp, and_or_left.mpr⟩


proof_of foLogEquivT_deMorgan_disj := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]; exact ⟨not_or.mp, not_or.mpr⟩


proof_of foLogEquivT_deMorgan_conj := by
  -- BEGIN PROOF
    intro M s
    simp only [formulaEvalT]
    exact ⟨fun h => (em _).elim (fun ha => Or.inr (fun hb => h ⟨ha, hb⟩)) Or.inl,
           fun h ⟨ha, hb⟩ => h.elim (· ha) (· hb)⟩


proof_of foLogEquivT_disj_idem := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]; exact ⟨or_self_iff.mp, or_self_iff.mpr⟩


proof_of foLogEquivT_conj_idem := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]; exact ⟨and_self_iff.mp, and_self_iff.mpr⟩


proof_of foLogEquivT_double_neg := by
  -- BEGIN PROOF
    intro M s; simp [formulaEvalT]


proof_of foLogEquivT_absorb_disj := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]
    exact ⟨fun h => h.elim id (fun ⟨ha, _⟩ => ha), Or.inl⟩


proof_of foLogEquivT_absorb_conj := by
  -- BEGIN PROOF
    intro M s; simp only [formulaEvalT]
    exact ⟨fun ⟨ha, _⟩ => ha, fun ha => ⟨ha, Or.inl ha⟩⟩


proof_of foLogEquivT_excluded_middle := by
  intro M s
  exact ⟨fun _ => trivial, fun _ => em _⟩


proof_of foLogEquivT_disj_identity := by
  intro M s
  exact ⟨fun h => h.elim id (fun hbot => False.elim (hbot.2 hbot.1)), Or.inl⟩


proof_of foLogEquivT_conj_annihilation := by
  intro M s
  exact ⟨And.right, fun hbot => False.elim (hbot.2 hbot.1)⟩


proof_of foLogEquivT_disj_top := by
  intro M s
  exact ⟨fun _ => trivial, fun _ => Or.inr trivial⟩


proof_of foLogEquivT_conj_identity_top := by
  intro M s
  exact ⟨And.left, fun h => ⟨h, trivial⟩⟩


proof_of foLogEquivT_contradiction := by
  intro M s
  exact ⟨fun h => False.elim (h.2 h.1), fun hbot => False.elim (hbot.2 hbot.1)⟩


helper /-- Associativity of disjunction for normalized formulae:
((A vee B) vee C) simeq (A vee (B vee C)). -/
theorem foLogEquivN_disj_assoc {L : Language} (A B C : FormulaN L) :
    foLogEquivN (FormulaN.disj (FormulaN.disj A B) C)
      (FormulaN.disj A (FormulaN.disj B C)) :=
-- BEGIN PROOF
by
  intro M s; simp only [formulaEvalN]; exact ⟨or_assoc.mp, or_assoc.mpr⟩

helper /-- Associativity of conjunction for normalized formulae:
((A wedge B) wedge C) simeq (A wedge (B wedge C)). -/
theorem foLogEquivN_conj_assoc {L : Language} (A B C : FormulaN L) :
    foLogEquivN (FormulaN.conj (FormulaN.conj A B) C)
      (FormulaN.conj A (FormulaN.conj B C)) :=
-- BEGIN PROOF
by
  intro M s; simp only [formulaEvalN]; exact ⟨and_assoc.mp, and_assoc.mpr⟩





helper /-- Distributivity of disjunction over conjunction for normalized formulae:
(A vee (B wedge C)) simeq ((A vee B) wedge (A vee C)). -/
theorem foLogEquivN_disj_distrib {L : Language}
    (A B C : FormulaN L) :
    foLogEquivN (FormulaN.disj A (FormulaN.conj B C))
      (FormulaN.conj (FormulaN.disj A B) (FormulaN.disj A C)) :=
-- BEGIN PROOF
by
  intro M s; simp only [formulaEvalN]; exact ⟨or_and_left.mp, or_and_left.mpr⟩

helper /-- Distributivity of conjunction over disjunction for normalized formulae:
(A wedge (B vee C)) simeq ((A wedge B) vee (A wedge C)). -/
theorem foLogEquivN_conj_distrib {L : Language}
    (A B C : FormulaN L) :
    foLogEquivN (FormulaN.conj A (FormulaN.disj B C))
      (FormulaN.disj (FormulaN.conj A B) (FormulaN.conj A C)) :=
-- BEGIN PROOF
by
  intro M s; simp only [formulaEvalN]; exact ⟨and_or_left.mp, and_or_left.mpr⟩





helper /-- Idempotency of disjunction for normalized formulae:
(A vee A) simeq A. -/
theorem foLogEquivN_disj_idem {L : Language} (A : FormulaN L) :
    foLogEquivN (FormulaN.disj A A) A :=
-- BEGIN PROOF
by
  intro M s; simp only [formulaEvalN]; exact ⟨or_self_iff.mp, or_self_iff.mpr⟩

helper /-- Idempotency of conjunction for normalized formulae:
(A wedge A) simeq A. -/
theorem foLogEquivN_conj_idem {L : Language} (A : FormulaN L) :
    foLogEquivN (FormulaN.conj A A) A :=
-- BEGIN PROOF
by
  intro M s; simp only [formulaEvalN]; exact ⟨and_self_iff.mp, and_self_iff.mpr⟩



helper /-- Absorption of disjunction for normalized formulae:
(A vee (A wedge B)) simeq A. -/
theorem foLogEquivN_absorb_disj {L : Language}
    (A B : FormulaN L) :
    foLogEquivN (FormulaN.disj A (FormulaN.conj A B)) A :=
-- BEGIN PROOF
by
  intro M s; simp only [formulaEvalN]
  exact ⟨fun h => h.elim id (fun ⟨ha, _⟩ => ha), Or.inl⟩

helper /-- Absorption of conjunction for normalized formulae:
(A wedge (A vee B)) simeq A. -/
theorem foLogEquivN_absorb_conj {L : Language}
    (A B : FormulaN L) :
    foLogEquivN (FormulaN.conj A (FormulaN.disj A B)) A :=
-- BEGIN PROOF
by
  intro M s; simp only [formulaEvalN]
  exact ⟨fun ⟨ha, _⟩ => ha, fun ha => ⟨ha, Or.inl ha⟩⟩

helper /-- Excluded middle for normalized formulae:
A ∨ ¬A is logically equivalent to ¬(A ∧ ¬A). -/
theorem foLogEquivN_excluded_middle {L : Language}
    (A : FormulaN L) :
    foLogEquivN (FormulaN.disj A (FormulaN.neg A))
      (FormulaN.neg (FormulaN.conj A (FormulaN.neg A))) :=
-- BEGIN PROOF
by
  intro M s; simp only [formulaEvalN, FormulaN.falsum]
  exact ⟨fun _ ⟨ha, hna⟩ => hna ha, fun _ => em _⟩

namespace BL

helper /-- Lemma 5.3.8 (companion): Classes are equal exactly when their
representatives are logically equivalent. -/
theorem BL.ofFormulaEqIff {L : Language} (A B : FormulaT L) :
    ofFormula A = ofFormula B ↔ foLogEquivT A B :=
  ⟨Quotient.exact, fun h => @Quotient.sound _ (foLogEquivSetoid L) A B h⟩

helper /-- Lemma 5.3.8 (companion): Addition on classes is induced by disjunction. -/
theorem BL.addOfFormula {L : Language} (A B : FormulaT L) :
    add (ofFormula A) (ofFormula B) = ofFormula (.disj A B) := rfl

helper /-- Lemma 5.3.8 (companion): Multiplication on classes is induced by conjunction. -/
theorem BL.mulOfFormula {L : Language} (A B : FormulaT L) :
    mul (ofFormula A) (ofFormula B) = ofFormula (.conj A B) := rfl

helper /-- Lemma 5.3.8 (companion): Negation on classes is induced by formula negation. -/
theorem BL.negOfFormula {L : Language} (A : FormulaT L) :
    neg (ofFormula A) = ofFormula (.neg A) := rfl

end BL

proof_of BL.isBooleanAlgebra := {
  addAssoc := BL.addAssoc
  mulAssoc := BL.mulAssoc
  addComm := BL.addComm
  mulComm := BL.mulComm
  addMulDistrib := BL.addMulDistrib
  mulAddDistrib := BL.mulAddDistrib
  negAdd := BL.negAdd
  negMul := BL.negMul
  addIdempotent := BL.addIdempotent
  mulIdempotent := BL.mulIdempotent
  negNeg := BL.negNeg
  addAbsorption := BL.addAbsorption
  mulAbsorption := BL.mulAbsorption
  addZero := fun a => BL.addZero a P hP
  mulZero := fun a => BL.mulZero a P hP
  addOne := BL.addOne
  mulOne := BL.mulOne
  addNeg := BL.addNeg
  mulNeg := fun a => BL.mulNeg a P hP }

end LCS.FirstOrder.Semantics.Equivalence
