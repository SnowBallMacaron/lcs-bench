import LCS.Item
import LCS.Util
import LCS.Propositional.Infinite
import LCS.Propositional.Systems.G.Search.Fairness
import Attach
import LCS.Propositional.Infinite.SignedFormulae.ProofsStamp

/-! # Propositional.Infinite.SignedFormulae
    Formalization of Chapter 3, Sections 3.5.4-3.5.6.
    Defines signed formulae, type-a/b classification,
    satisfaction, conjugates, Hintikka sets,
    and extended completeness of G'.
    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Propositional.Infinite.SignedFormulae

open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search
open LCS.Propositional.Infinite
open Classical

-- ========= Definition 3.5.3: Signed Formulae =========

/-- Definition 3.5.3: A signed formula is any expression of the form T A
    or F A, where A is an arbitrary proposition. -/
@[blueprint "chap3__definition_3_5_3" (main := true)]
inductive SignedFormula where
  | trueF : PropFormulaNormalized → SignedFormula
  | falseF : PropFormulaNormalized → SignedFormula
  deriving DecidableEq, Repr

-- ========= Definition 3.5.4: Type-A and Type-B Signed Formulae =========

/-- Definition 3.5.4: Type-a (conjunctive) signed formulae with components
    A₁, A₂: T(X∧Y), F(X∨Y), F(X⊃Y), T(¬X), F(¬X). -/
@[blueprint "chap3__definition_3_5_4" (main := true)]
inductive TypeA where
  | tConj : PropFormulaNormalized → PropFormulaNormalized → TypeA
  | fDisj : PropFormulaNormalized → PropFormulaNormalized → TypeA
  | fImpl : PropFormulaNormalized → PropFormulaNormalized → TypeA
  | tNeg : PropFormulaNormalized → TypeA
  | fNeg : PropFormulaNormalized → TypeA
  deriving DecidableEq, Repr

/-- Definition 3.5.4: Type-b (disjunctive) signed formulae with components
    B₁, B₂: F(X∧Y), T(X∨Y), T(X⊃Y). -/
@[blueprint "chap3__definition_3_5_4" (main := true)]
inductive TypeB where
  | fConj : PropFormulaNormalized → PropFormulaNormalized → TypeB
  | tDisj : PropFormulaNormalized → PropFormulaNormalized → TypeB
  | tImpl : PropFormulaNormalized → PropFormulaNormalized → TypeB
  deriving DecidableEq, Repr

-- ========= Definition 3.5.4 (companion defs): Type-A Components =========

namespace TypeA

/-- Definition 3.5.4 (companion): Recovers the original signed formula from a
    type-a entry. -/
@[blueprint "chap3__definition_3_5_4"]
def toSigned : TypeA → SignedFormula
  | tConj X Y => .trueF (.conj X Y)
  | fDisj X Y => .falseF (.disj X Y)
  | fImpl X Y => .falseF (.impl X Y)
  | tNeg X => .trueF (.neg X)
  | fNeg X => .falseF (.neg X)

/-- Definition 3.5.4 (companion): First component A1 of a type-a formula. -/
@[blueprint "chap3__definition_3_5_4"]
def comp1 : TypeA → SignedFormula
  | tConj X _ => .trueF X
  | fDisj X _ => .falseF X
  | fImpl X _ => .trueF X
  | tNeg X => .falseF X
  | fNeg X => .trueF X

/-- Definition 3.5.4 (companion): Second component A2 of a type-a formula. -/
@[blueprint "chap3__definition_3_5_4"]
def comp2 : TypeA → SignedFormula
  | tConj _ Y => .trueF Y
  | fDisj _ Y => .falseF Y
  | fImpl _ Y => .falseF Y
  | tNeg X => .falseF X
  | fNeg X => .trueF X

end TypeA

-- ========= Definition 3.5.4 (companion defs): Type-B Components =========

namespace TypeB

/-- Definition 3.5.4 (companion): Recovers the original signed formula from a
    type-b entry. -/
@[blueprint "chap3__definition_3_5_4"]
def toSigned : TypeB → SignedFormula
  | fConj X Y => .falseF (.conj X Y)
  | tDisj X Y => .trueF (.disj X Y)
  | tImpl X Y => .trueF (.impl X Y)

/-- Definition 3.5.4 (companion): First component B1 of a type-b formula. -/
@[blueprint "chap3__definition_3_5_4"]
def comp1 : TypeB → SignedFormula
  | fConj X _ => .falseF X
  | tDisj X _ => .trueF X
  | tImpl X _ => .falseF X

/-- Definition 3.5.4 (companion): Second component B2 of a type-b formula. -/
@[blueprint "chap3__definition_3_5_4"]
def comp2 : TypeB → SignedFormula
  | fConj _ Y => .falseF Y
  | tDisj _ Y => .trueF Y
  | tImpl _ Y => .trueF Y

end TypeB

-- ========= Definition 3.5.4 (companion): SignedFormula.classify =========

namespace SignedFormula

/-- Definition 3.5.4 (companion): Classifies a signed formula as type-a
    (Sum.inl), type-b (Sum.inr), or neither (none, for signed propositional
    letters and signed falsum). -/
@[blueprint "chap3__definition_3_5_4"]
def classify : SignedFormula → Option (TypeA ⊕ TypeB)
  | .trueF (.conj X Y) => some (.inl (.tConj X Y))
  | .trueF (.disj X Y) => some (.inr (.tDisj X Y))
  | .trueF (.impl X Y) => some (.inr (.tImpl X Y))
  | .trueF (.neg X) => some (.inl (.tNeg X))
  | .falseF (.conj X Y) => some (.inr (.fConj X Y))
  | .falseF (.disj X Y) => some (.inl (.fDisj X Y))
  | .falseF (.impl X Y) => some (.inl (.fImpl X Y))
  | .falseF (.neg X) => some (.inl (.fNeg X))
  | .trueF (.var _) => none
  | .falseF (.var _) => none

end SignedFormula

-- ========= Definition 3.5.7: Hintikka Sets =========

/-- Definition 3.5.7: A set S of signed formulae is a Hintikka set iff:
    (H1) No signed propositional letter and its conjugate are both in S.
    (H2) If a type-a formula A is in S, then both A1 and A2 are in S.
    (H3) If a type-b formula B is in S, then B1 is in S or B2 is in S. -/
@[blueprint "chap3__definition_3_5_7" (main := true)]
structure IsHintikkaSet (S : Set SignedFormula) : Prop where
  h1 : ∀ (n : Nat), ¬(SignedFormula.trueF (.var n) ∈ S ∧
    SignedFormula.falseF (.var n) ∈ S)
  h2 : ∀ (a : TypeA), a.toSigned ∈ S → a.comp1 ∈ S ∧ a.comp2 ∈ S
  h3 : ∀ (b : TypeB), b.toSigned ∈ S → b.comp1 ∈ S ∨ b.comp2 ∈ S

-- ========= Definition 3.5.3 (companion def): Signed Set of a Sequent =========

/-- Definition 3.5.3: Given an infinite sequent Γ → Δ, the signed set of
    formulae {T A | A ∈ Γ} ∪ {F B | B ∈ Δ}. -/
@[blueprint "chap3__definition_3_5_3" (main := true)]
def signedSetOfSequent (seq : InfSequent) : Set SignedFormula :=
  fun sf => match sf with
    | .trueF A => ∃ n, seq.antecedent n = some A
    | .falseF B => ∃ n, seq.succedent n = some B

-- ========= Definition 3.5.5: Satisfaction of Signed Formulae =========

namespace SignedFormula

/-- Definition 3.5.5: A valuation v makes T A true iff v makes A true, and
    makes F A true iff v makes A false. -/
@[blueprint "chap3__definition_3_5_5" (main := true)]
def satisfiedBy : SignedFormula → Valuation → Prop
  | .trueF A, v => evalExtN v A = BoolVal.T
  | .falseF A, v => evalExtN v A = BoolVal.F

end SignedFormula

namespace SignedSet

/-- Definition 3.5.5: A valuation v satisfies a signed set S iff v makes
    every signed formula in S true. -/
@[blueprint "chap3__definition_3_5_5" (main := true)]
def satisfiedBy (S : Set SignedFormula) (v : Valuation) : Prop :=
  ∀ sf, sf ∈ S → SignedFormula.satisfiedBy sf v

end SignedSet

-- ========= Definition 3.5.6: Conjugate of a Signed Formula =========

namespace SignedFormula

/-- Definition 3.5.6: The conjugate of a signed formula is defined as follows:
    The conjugate of T A is F A, and the conjugate of F A is T A. -/
@[blueprint "chap3__definition_3_5_6" (main := true)]
def conjugate : SignedFormula → SignedFormula
  | .trueF A => .falseF A
  | .falseF A => .trueF A

end SignedFormula

-- ========= Lemma 3.5.2 (required defs): Path Operations on Search Trees =========

/-- Lemma 3.5.2 (required): A path in a deduction tree is a list of
    directional choices (left or right at each two-premise split). -/
@[blueprint "chap3__lemma_3_5_2"]
inductive PathDir where
  | left : PathDir
  | right : PathDir
  deriving DecidableEq, Repr

-- ========= Lemma 3.5.3 (required def): Canonical Valuation =========

/-- Lemma 3.5.3 (required): The canonical valuation for a Hintikka set S. -/
@[blueprint "chap3__lemma_3_5_3"]
noncomputable def hintikkaCanonicalValuation (S : Set SignedFormula) : Valuation :=
  fun n =>
    if SignedFormula.falseF (.var n) ∈ S then BoolVal.F
    else BoolVal.T

-- ========= Lemma 3.5.3: Hintikka Set Satisfiability =========

/-- Core induction step for the proof of Lemma 3.5.3: the canonical
    valuation makes every signed formula in S true. This is the
    internal inductive argument; the lemma statement itself is
    `hintikka_set_satisfiable`. -/
theorem canonical_satisfies_combined (S : Set SignedFormula)
    (hS : IsHintikkaSet S) :
    let v := hintikkaCanonicalValuation S
    ∀ A : PropFormulaNormalized,
      (SignedFormula.trueF A ∈ S → evalExtN v A = BoolVal.T) ∧
      (SignedFormula.falseF A ∈ S → evalExtN v A = BoolVal.F) := by
-- BEGIN PROOF
  intro v A
  induction A with
  | var n =>
    exact ⟨
      fun hT => by
        simp only [hintikkaCanonicalValuation, evalExtN, v]
        split
        · exact absurd ⟨hT, ‹_›⟩ (hS.h1 n)
        · rfl,
      fun hF => by
        simp only [hintikkaCanonicalValuation, evalExtN, v]
        split
        · rfl
        · exact absurd hF ‹_›⟩
  | neg A ihA =>
    obtain ⟨ihAT, ihAF⟩ := ihA
    exact ⟨
      fun hT => by
        have ha := hS.h2 (TypeA.tNeg A) (show (TypeA.tNeg A).toSigned ∈ S from hT)
        have : evalExtN v A = BoolVal.F := ihAF ha.1
        simp only [evalExtN, this, hNeg],
      fun hF => by
        have ha := hS.h2 (TypeA.fNeg A) (show (TypeA.fNeg A).toSigned ∈ S from hF)
        have : evalExtN v A = BoolVal.T := ihAT ha.1
        simp only [evalExtN, this, hNeg]⟩
  | conj A B ihA ihB =>
    obtain ⟨ihAT, ihAF⟩ := ihA
    obtain ⟨ihBT, ihBF⟩ := ihB
    exact ⟨
      fun hT => by
        have ha := hS.h2 (TypeA.tConj A B) (show (TypeA.tConj A B).toSigned ∈ S from hT)
        rw [evalExtN, ihAT ha.1, ihBT ha.2, hAnd],
      fun hF => by
        have hb := hS.h3 (TypeB.fConj A B) (show (TypeB.fConj A B).toSigned ∈ S from hF)
        rcases hb with hFA | hFB
        · simp only [evalExtN, ihAF hFA, hAnd]
        · simp only [evalExtN, ihBF hFB, hAnd]; cases evalExtN v A <;> rfl⟩
  | disj A B ihA ihB =>
    obtain ⟨ihAT, ihAF⟩ := ihA
    obtain ⟨ihBT, ihBF⟩ := ihB
    exact ⟨
      fun hT => by
        have hb := hS.h3 (TypeB.tDisj A B) (show (TypeB.tDisj A B).toSigned ∈ S from hT)
        rcases hb with hTA | hTB
        · simp only [evalExtN, ihAT hTA, hOr]
        · simp only [evalExtN, ihBT hTB, hOr]; cases evalExtN v A <;> rfl,
      fun hF => by
        have ha := hS.h2 (TypeA.fDisj A B) (show (TypeA.fDisj A B).toSigned ∈ S from hF)
        rw [evalExtN, ihAF ha.1, ihBF ha.2, hOr]⟩
  | impl A B ihA ihB =>
    obtain ⟨ihAT, ihAF⟩ := ihA
    obtain ⟨ihBT, ihBF⟩ := ihB
    exact ⟨
      fun hT => by
        have hb := hS.h3 (TypeB.tImpl A B) (show (TypeB.tImpl A B).toSigned ∈ S from hT)
        rcases hb with hFA | hTB
        · simp only [evalExtN, ihAF hFA, hImplies]
        · simp only [evalExtN, ihBT hTB, hImplies]; cases evalExtN v A <;> rfl,
      fun hF => by
        have ha := hS.h2 (TypeA.fImpl A B) (show (TypeA.fImpl A B).toSigned ∈ S from hF)
        simp only [evalExtN, ihAT ha.1, ihBF ha.2, hImplies]⟩

/-- Lemma 3.5.3: Every Hintikka set S is satisfiable. -/
@[blueprint "chap3__lemma_3_5_3" (main := true)]
theorem hintikka_set_satisfiable (S : Set SignedFormula)
    (hS : IsHintikkaSet S)
    : ∃ v : Valuation, SignedSet.satisfiedBy S v 







/-- Signed occurrence in a finite sequent. -/
@[blueprint "chap3__definition_3_5_3"]
def occurs (s : Sequent) : SignedFormula → Prop
  | .trueF A => A ∈ s.antecedent
  | .falseF A => A ∈ s.succedent

/-- The components required when a non-atomic signed formula is expanded.
    Atomic formulae cannot be expanded. -/
def expanded (S : Set SignedFormula) : SignedFormula → Prop
  | .trueF (.var _) | .falseF (.var _) => False
  | .trueF (.conj A B) => S (.trueF A) ∧ S (.trueF B)
  | .falseF (.disj A B) => S (.falseF A) ∧ S (.falseF B)
  | .falseF (.impl A B) => S (.trueF A) ∧ S (.falseF B)
  | .trueF (.neg A) => S (.falseF A)
  | .falseF (.neg A) => S (.trueF A)
  | .falseF (.conj A B) => S (.falseF A) ∨ S (.falseF B)
  | .trueF (.disj A B) => S (.trueF A) ∨ S (.trueF B)
  | .trueF (.impl A B) => S (.falseF A) ∨ S (.trueF B)

theorem expanded_mono {S T : Set SignedFormula}
    (h : ∀ sf, S sf → T sf) (sf : SignedFormula) :
    expanded S sf → expanded T sf := by
  cases sf with
  | trueF A => cases A <;> simp only [expanded] <;> grind
  | falseF A => cases A <;> simp only [expanded] <;> grind

theorem step1_support {prem conc : Sequent} (r : GentzenStep1 prem conc)
    (sf : SignedFormula) (h : occurs conc sf) :
    occurs prem sf ∨ expanded (occurs prem) sf := by
  cases r <;> cases sf with
  | trueF A => cases A <;> simp_all [occurs, expanded] <;> grind
  | falseF A => cases A <;> simp_all [occurs, expanded] <;> grind

theorem step2_support_left {p q conc : Sequent} (r : GentzenStep2 p q conc)
    (sf : SignedFormula) (h : occurs conc sf) :
    occurs p sf ∨ expanded (occurs p) sf := by
  cases r <;> cases sf with
  | trueF A => cases A <;> simp_all [occurs, expanded] <;> grind
  | falseF A => cases A <;> simp_all [occurs, expanded] <;> grind

theorem step2_support_right {p q conc : Sequent} (r : GentzenStep2 p q conc)
    (sf : SignedFormula) (h : occurs conc sf) :
    occurs q sf ∨ expanded (occurs q) sf := by
  cases r <;> cases sf with
  | trueF A => cases A <;> simp_all [occurs, expanded] <;> grind
  | falseF A => cases A <;> simp_all [occurs, expanded] <;> grind

theorem support_lift {S T : Set SignedFormula} {s : Sequent}
    (hsub : ∀ sf, S sf → T sf) {sf : SignedFormula}
    (h : occurs s sf ∨ expanded S sf) : occurs s sf ∨ expanded T sf :=
  h.imp id (expanded_mono hsub sf)

/-- The formula actually selected by a one-premise rule. -/
def principal1 {p s : Sequent} : GentzenStep1 p s → SignedFormula
  | .andLeft _ _ _ A B => .trueF (.conj A B)
  | .orRight _ _ _ A B => .falseF (.disj A B)
  | .implRight _ _ _ A B => .falseF (.impl A B)
  | .negLeft _ _ _ A => .trueF (.neg A)
  | .negRight _ _ _ A => .falseF (.neg A)

/-- The formula actually selected by a two-premise rule. -/
def principal2 {p q s : Sequent} : GentzenStep2 p q s → SignedFormula
  | .andRight _ _ _ A B => .falseF (.conj A B)
  | .orLeft _ _ _ A B => .trueF (.disj A B)
  | .implLeft _ _ _ A B => .trueF (.impl A B)

/-- Context introduction and a stationary endpoint do not select a connective. -/
def branchPrincipal {s t : Sequent} : InfBranchStep s t → Option SignedFormula
  | .onePremise r => some (principal1 r)
  | .leftPremise r => some (principal2 r)
  | .rightPremise r => some (principal2 r)
  | .extend _ _ _ | .idle _ => none

theorem branchStep_support {s t : Sequent} (step : InfBranchStep s t)
    (sf : SignedFormula) (h : occurs s sf) :
    occurs t sf ∨ expanded (occurs t) sf := by
  cases step with
  | onePremise r => exact step1_support r sf h
  | leftPremise r => exact step2_support_left r sf h
  | rightPremise r => exact step2_support_right r sf h
  | extend a b =>
    apply Or.inl
    cases sf <;> simp_all [occurs, extendSeq]
  | idle => exact Or.inl h

















/-- A root-to-leaf path in a finite stage of the actual infinite search.
    Introduction edges retain both the old root and the extended label. -/
@[blueprint "chap3__lemma_3_5_2"]
inductive SearchTreePath : {s : Sequent} → InfDeductionTree s →
    Sequent → List Sequent → Prop where
  | leaf (s) : SearchTreePath (.leaf s) s [s]
  | onePremise {s p leaf labels} {t : InfDeductionTree p}
      (r : GentzenStep1 p s) : SearchTreePath t leaf labels →
      SearchTreePath (.onePremise r t) leaf (s :: labels)
  | leftPremise {s p q leaf labels} {l : InfDeductionTree p} {r : InfDeductionTree q}
      (rule : GentzenStep2 p q s) : SearchTreePath l leaf labels →
      SearchTreePath (.twoPremise rule l r) leaf (s :: labels)
  | rightPremise {s p q leaf labels} {l : InfDeductionTree p} {r : InfDeductionTree q}
      (rule : GentzenStep2 p q s) : SearchTreePath r leaf labels →
      SearchTreePath (.twoPremise rule l r) leaf (s :: labels)
  | extend {s leaf labels} {a b : Option PropFormulaNormalized}
      {t : InfDeductionTree (extendSeq s a b)} : SearchTreePath t leaf labels →
      SearchTreePath (.extend a b t) leaf (s :: labels)

@[blueprint "chap3__lemma_3_5_2"]
def sequentListSignedSet (labels : List Sequent) : Set SignedFormula :=
  fun sf => ∃ s ∈ labels, occurs s sf

theorem SearchTreePath.root_mem {s leaf labels} {t : InfDeductionTree s}
    (hp : SearchTreePath t leaf labels) : s ∈ labels := by
  cases hp <;> exact List.Mem.head _

theorem SearchTreePath.terminal_mem {s terminal labels} {t : InfDeductionTree s}
    (hp : SearchTreePath t terminal labels) : terminal ∈ labels := by
  induction hp with
  | leaf => exact List.Mem.head _
  | onePremise _ _ ih => exact List.Mem.tail _ ih
  | leftPremise _ _ ih => exact List.Mem.tail _ ih
  | rightPremise _ _ ih => exact List.Mem.tail _ ih
  | extend _ ih => exact List.Mem.tail _ ih

theorem SearchTreePath.leaf_mem {s terminal labels} {t : InfDeductionTree s}
    (hp : SearchTreePath t terminal labels) : terminal ∈ t.leaves := by
  induction hp with
  | leaf => exact List.Mem.head _
  | onePremise _ _ ih => exact ih
  | leftPremise _ _ ih => exact List.mem_append_left _ ih
  | rightPremise _ _ ih => exact List.mem_append_right _ ih
  | extend _ ih => exact ih

theorem SearchTreePath.canonical_falsifies_terminal {s terminal labels}
    {t : InfDeductionTree s} (hp : SearchTreePath t terminal labels)
    (hS : IsHintikkaSet (sequentListSignedSet labels)) :
    sequentFalsifiedBy terminal (hintikkaCanonicalValuation (sequentListSignedSet labels)) := by
  constructor
  · intro A hA
    exact (canonical_satisfies_combined _ hS A).1 ⟨terminal, hp.terminal_mem, hA⟩
  · intro A hA
    exact (canonical_satisfies_combined _ hS A).2 ⟨terminal, hp.terminal_mem, hA⟩

theorem SearchTreePath.exists_of_leaf {s : Sequent} (t : InfDeductionTree s)
    (leaf : Sequent) (h : leaf ∈ t.leaves) :
    ∃ labels, SearchTreePath t leaf labels := by
  induction t with
  | leaf s =>
    simp only [InfDeductionTree.leaves, List.mem_singleton] at h
    subst leaf
    exact ⟨[s], .leaf s⟩
  | onePremise r t ih =>
    obtain ⟨labels, hp⟩ := ih h
    exact ⟨_, .onePremise r hp⟩
  | twoPremise r l t ih₁ ih₂ =>
    rcases List.mem_append.mp h with h | h
    · obtain ⟨labels, hp⟩ := ih₁ h
      exact ⟨_, .leftPremise r hp⟩
    · obtain ⟨labels, hp⟩ := ih₂ h
      exact ⟨_, .rightPremise r hp⟩
  | extend a b t ih =>
    obtain ⟨labels, hp⟩ := ih h
    exact ⟨_, .extend hp⟩

theorem sequentListSignedSet_tail (s : Sequent) (labels : List Sequent) :
    ∀ sf, sequentListSignedSet labels sf → sequentListSignedSet (s :: labels) sf := by
  intro sf ⟨t, ht, hm⟩
  exact ⟨t, List.Mem.tail s ht, hm⟩

theorem support_prepend {s p terminal : Sequent} {labels : List Sequent}
    (step : InfBranchStep s p) (hp : p ∈ labels) (sf : SignedFormula)
    (ih : occurs p sf → occurs terminal sf ∨ expanded (sequentListSignedSet labels) sf)
    (h : occurs s sf) :
    occurs terminal sf ∨ expanded (sequentListSignedSet (s :: labels)) sf := by
  rcases branchStep_support step sf h with h | h
  · exact support_lift (sequentListSignedSet_tail s labels) (ih h)
  · exact Or.inr (expanded_mono (fun sf hm => ⟨p, List.Mem.tail s hp, hm⟩) sf h)

theorem SearchTreePath.support_from_root {s terminal labels} {t : InfDeductionTree s}
    (hp : SearchTreePath t terminal labels) (sf : SignedFormula) (h : occurs s sf) :
    occurs terminal sf ∨ expanded (sequentListSignedSet labels) sf := by
  induction hp with
  | leaf => exact Or.inl h
  | onePremise r hp ih => exact support_prepend (.onePremise r) hp.root_mem sf ih h
  | leftPremise r hp ih => exact support_prepend (.leftPremise r) hp.root_mem sf ih h
  | rightPremise r hp ih => exact support_prepend (.rightPremise r) hp.root_mem sf ih h
  | extend hp ih => exact support_prepend (.extend _ _ _) hp.root_mem sf ih h

theorem support_any_prepend {s terminal : Sequent} {labels : List Sequent}
    (sf : SignedFormula)
    (root : occurs s sf → occurs terminal sf ∨ expanded (sequentListSignedSet (s :: labels)) sf)
    (tail : sequentListSignedSet labels sf → occurs terminal sf ∨
      expanded (sequentListSignedSet labels) sf)
    (h : sequentListSignedSet (s :: labels) sf) :
    occurs terminal sf ∨ expanded (sequentListSignedSet (s :: labels)) sf := by
  obtain ⟨t, ht, hm⟩ := h
  rcases List.mem_cons.mp ht with rfl | ht
  · exact root hm
  · exact support_lift (sequentListSignedSet_tail s labels) (tail ⟨t, ht, hm⟩)

theorem SearchTreePath.support {s terminal labels} {t : InfDeductionTree s}
    (hp : SearchTreePath t terminal labels) (sf : SignedFormula)
    (h : sequentListSignedSet labels sf) :
    occurs terminal sf ∨ expanded (sequentListSignedSet labels) sf := by
  induction hp with
  | leaf s => exact Or.inl (by simpa [sequentListSignedSet] using h)
  | onePremise r hp ih =>
    exact support_any_prepend sf (SearchTreePath.support_from_root (.onePremise r hp) sf) ih h
  | @leftPremise s p q leaf labels l r rule hp ih =>
    exact support_any_prepend sf
      (SearchTreePath.support_from_root (.leftPremise (r := r) rule hp) sf) ih h
  | @rightPremise s p q leaf labels l r rule hp ih =>
    exact support_any_prepend sf
      (SearchTreePath.support_from_root (.rightPremise (l := l) rule hp) sf) ih h
  | extend hp ih =>
    exact support_any_prepend sf (SearchTreePath.support_from_root (.extend hp) sf) ih h

/-- Proof of Lemma 3.5.2, terminated nonclosed search case. A branch of the
    actual completed search stage, including every introduction edge, yields S. -/
@[blueprint "chap3__lemma_3_5_2"]
theorem finished_search_hintikka_set_extraction (seq : InfSequent) (k : Nat)
    (hfinished : infIsFinishedTree (infSearchSteps seq k))
    (hopen : ¬ ∀ leaf ∈ (infSearchSteps seq k).tree.leaves, isAxiom leaf) :
    ∃ leaf labels, SearchTreePath (infSearchSteps seq k).tree leaf labels ∧
      IsHintikkaSet (sequentListSignedSet labels) 



















/-- A possibly infinite branch, or a finite branch continued at its endpoint.
    Fairness requires each compound occurrence to be selected as an actual
    inference-rule principal at a later step. All edges are Gentzen inferences,
    context introductions, or stationary endpoints. -/
structure FairOpenBranch where
  label : Nat → Sequent
  step : ∀ n, InfBranchStep (label n) (label (n + 1))
  isOpen : ∀ n, ¬isAxiom (label n)
  fair : ∀ n sf, occurs (label n) sf → sf.classify ≠ none →
    ∃ m, n ≤ m ∧ ∃ selected : InfBranchStep (label m) (label (m + 1)),
      branchPrincipal selected = some sf













/-- Proof of Lemma 3.5.2 and its valuation consequence, infinite-path case.
    The path is in the actual search limit; openness, fairness, and input
    coverage are all proved from the procedure rather than supplied. -/
@[blueprint "chap3__lemma_3_5_2"]
theorem infinite_search_path_canonical_countermodel (seq : InfSequent)
    (address : Nat → List Nat) (hp : (infSearchTreeDomain seq).InfinitePath address) :
    ∃ label : Nat → Sequent,
      (∀ n, infSearchLimit seq (address n) (label n)) ∧
      IsHintikkaSet (fun sf => ∃ n, occurs (label n) sf) ∧
      infSeqFalsifies (hintikkaCanonicalValuation (fun sf => ∃ n, occurs (label n) sf)) seq 

/-- Proof of Lemma 3.5.2: if the actual search never produces a closed
    finite stage, a Hintikka set is extracted either from a path to an open
    leaf of a finished stage or from an infinite path of the search limit. -/
@[blueprint "chap3__lemma_3_5_2" (main := true)]
theorem hintikka_set_extraction (seq : InfSequent)
    (hnotclosed : ¬ ∃ k, ∀ leaf ∈ (infSearchSteps seq k).tree.leaves, isAxiom leaf) :
    (∃ k terminal labels, infIsFinishedTree (infSearchSteps seq k) ∧
      SearchTreePath (infSearchSteps seq k).tree terminal labels ∧
      IsHintikkaSet (sequentListSignedSet labels)) ∨
    (∃ address : Nat → List Nat, ∃ label : Nat → Sequent,
      (infSearchTreeDomain seq).InfinitePath address ∧
      (∀ n, infSearchLimit seq (address n) (label n)) ∧
      IsHintikkaSet (fun sf => ∃ n, occurs (label n) sf)) 

end LCS.Propositional.Infinite.SignedFormulae
