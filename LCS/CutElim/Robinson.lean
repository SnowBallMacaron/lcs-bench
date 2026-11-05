import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.CutElim.LKe
import LCS.FirstOrder.Completeness.MetaTheorems
import LCS.FirstOrder.Equality.MetaTheorems
import Attach
import LCS.CutElim.Robinson.ProofsStamp

/-! # CutElim.Robinson
    Formalization of Chapter 6, Section 7.
    Robinson's joint consistency theorem.
    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.CutElim.Robinson

open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax (peanoLanguage)
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.FirstOrder.Completeness.MetaTheorems
open LCS.FirstOrder.Equality.MetaTheorems
open LCS.FirstOrder.Equality
open Classical

-- ===================================================================
-- Theorem 6.7.1 (companion def): LanguageExpansion
-- ===================================================================

/-- Theorem 6.7.1 (companion): L' is an expansion of L if every
predicate, function, and constant symbol of L is also a symbol of L'
with the same arity. -/
@[blueprint "chap6__theorem_6_7_1"]
structure LanguageExpansion (L L' : Language) where
  /-- Injective embedding of predicate symbols -/
  predEmbed : L.predSymbols → L'.predSymbols
  /-- Predicate embedding preserves arities -/
  predArityPreserve :
    ∀ P, L'.predArity (predEmbed P) = L.predArity P
  /-- Predicate embedding is injective -/
  predInj : Function.Injective predEmbed
  /-- Injective embedding of function symbols -/
  funEmbed : L.funSymbols → L'.funSymbols
  /-- Function embedding preserves arities -/
  funArityPreserve :
    ∀ f, L'.funArity (funEmbed f) = L.funArity f
  /-- Function embedding is injective -/
  funInj : Function.Injective funEmbed
  /-- Injective embedding of constant symbols -/
  constEmbed : L.constSymbols → L'.constSymbols
  /-- Constant embedding is injective -/
  constInj : Function.Injective constEmbed
  /-- Equality preservation: if L has equality then L' has equality -/
  eqPreserve : L.hasEquality = true → L'.hasEquality = true

-- ===================================================================
-- Theorem 6.7.1 (companion def): LanguageIntersection
-- ===================================================================

/-- Theorem 6.7.1 (companion): The condition that L = L1 cap L2. -/
@[blueprint "chap6__theorem_6_7_1"]
structure LanguageIntersection
    (L L1 L2 : Language) where
  /-- L is a sublanguage of L1 -/
  expand1 : LanguageExpansion L L1
  /-- L is a sublanguage of L2 -/
  expand2 : LanguageExpansion L L2
  /-- Equality belongs to the common language exactly when it belongs to L1. -/
  eqExact1 : L.hasEquality = L1.hasEquality
  /-- Equality belongs to the common language exactly when it belongs to L2. -/
  eqExact2 : L.hasEquality = L2.hasEquality
  /-- Predicate intersection (L1 side) -/
  predDecL1 :
    ∀ (P1 : L1.predSymbols),
    Decidable (∃ (Q : L.predSymbols), expand1.predEmbed Q = P1)
  /-- Predicate intersection (L2 side) -/
  predDecL2 :
    ∀ (P2 : L2.predSymbols),
    Decidable (∃ (Q : L.predSymbols), expand2.predEmbed Q = P2)
  /-- Function intersection (L1 side) -/
  funDecL1 :
    ∀ (f1 : L1.funSymbols),
    Decidable (∃ (g : L.funSymbols), expand1.funEmbed g = f1)
  /-- Function intersection (L2 side) -/
  funDecL2 :
    ∀ (f2 : L2.funSymbols),
    Decidable (∃ (g : L.funSymbols), expand2.funEmbed g = f2)
  /-- Constant intersection (L1 side) -/
  constDecL1 :
    ∀ (c1 : L1.constSymbols),
    Decidable (∃ (d : L.constSymbols), expand1.constEmbed d = c1)
  /-- Constant intersection (L2 side) -/
  constDecL2 :
    ∀ (c2 : L2.constSymbols),
    Decidable (∃ (d : L.constSymbols), expand2.constEmbed d = c2)

-- Regression probes for the equality component of language intersection.

-- ATTACH-BLOCKER: private declaration
private def equalityFlagLanguage (hasEquality : Bool) : Language where
  funSymbols := Unit
  funArity := fun _ => 0
  constSymbols := Unit
  predSymbols := Unit
  predArity := fun _ => 0
  hasEquality := hasEquality

-- ATTACH-BLOCKER: private declaration
private def equalityFlagExpansion
    (sourceEquality targetEquality : Bool)
    (hEq : sourceEquality = true → targetEquality = true) :
    LanguageExpansion
      (equalityFlagLanguage sourceEquality)
      (equalityFlagLanguage targetEquality) where
  predEmbed := id
  predArityPreserve := by intro; rfl
  predInj := fun _ _ h => h
  funEmbed := id
  funArityPreserve := by intro; rfl
  funInj := fun _ _ h => h
  constEmbed := id
  constInj := fun _ _ h => h
  eqPreserve := hEq

-- ATTACH-BLOCKER: private declaration
private def equalityFlagIntersection
    (baseEquality leftEquality rightEquality : Bool)
    (hExact1 : baseEquality = leftEquality)
    (hExact2 : baseEquality = rightEquality) :
    LanguageIntersection
      (equalityFlagLanguage baseEquality)
      (equalityFlagLanguage leftEquality)
      (equalityFlagLanguage rightEquality) where
  expand1 := equalityFlagExpansion baseEquality leftEquality (by
    intro h
    exact hExact1.symm.trans h)
  expand2 := equalityFlagExpansion baseEquality rightEquality (by
    intro h
    exact hExact2.symm.trans h)
  eqExact1 := hExact1
  eqExact2 := hExact2
  predDecL1 := fun P => isTrue ⟨P, rfl⟩
  predDecL2 := fun P => isTrue ⟨P, rfl⟩
  funDecL1 := fun f => isTrue ⟨f, rfl⟩
  funDecL2 := fun f => isTrue ⟨f, rfl⟩
  constDecL1 := fun c => isTrue ⟨c, rfl⟩
  constDecL2 := fun c => isTrue ⟨c, rfl⟩

-- ATTACH-BLOCKER: private declaration
private def equalityIntersection_allowsEquality :
    LanguageIntersection
      (equalityFlagLanguage true)
      (equalityFlagLanguage true)
      (equalityFlagLanguage true) :=
  equalityFlagIntersection true true true (by simp) (by simp)

-- ATTACH-BLOCKER: private declaration
private def equalityIntersection_allowsNoEquality :
    LanguageIntersection
      (equalityFlagLanguage false)
      (equalityFlagLanguage false)
      (equalityFlagLanguage false) :=
  equalityFlagIntersection false false false (by simp) (by simp)

-- ATTACH-BLOCKER: private declaration
private theorem equalityIntersection_rejectsOneSidedEquality :
    LanguageIntersection
      (equalityFlagLanguage false)
      (equalityFlagLanguage true)
      (equalityFlagLanguage false) → False := by
  intro hIntersect
  simpa [equalityFlagLanguage] using hIntersect.eqExact1

-- ATTACH-BLOCKER: private declaration
private theorem equalityIntersection_rejectsHiddenCommonEquality :
    LanguageIntersection
      (equalityFlagLanguage false)
      (equalityFlagLanguage true)
      (equalityFlagLanguage true) → False := by
  intro hIntersect
  simpa [equalityFlagLanguage] using hIntersect.eqExact1

-- ===================================================================
-- Theorem 6.7.1 (companion def): isSentenceSet
-- ===================================================================

/-- Theorem 6.7.1 (companion): Every formula in the set is a sentence
(closed formula). -/
@[blueprint "chap6__theorem_6_7_1"]
def isSentenceSet {L : Language} (S : Set (FormulaN L)) : Prop :=
  ∀ A, A ∈ S → formulaFVN A = ∅

-- ===================================================================
-- Theorem 6.7.1 (companion def): formulaLiftN
-- ===================================================================

/-- Theorem 6.7.1 (companion): Lifts a FormulaN L into a
FormulaN L' via an expansion embedding. -/
@[blueprint "chap6__theorem_6_7_1"]
def formulaLiftN {L L' : Language}
    (e : LanguageExpansion L L') : FormulaN L → FormulaN L' :=
  let rec liftTerm : Term L → Term L'
    | .var x => .var x
    | .const c => .const (e.constEmbed c)
    | .func f ts => .func (e.funEmbed f)
        (fun i => liftTerm (ts (Fin.cast (e.funArityPreserve f) i)))
  let rec go : FormulaN L → FormulaN L'
    | .predN P ts => .predN (e.predEmbed P)
        (fun i => liftTerm (ts (Fin.cast (e.predArityPreserve P) i)))
    | .eq_ hL t1 t2 => .eq_ (e.eqPreserve hL) (liftTerm t1) (liftTerm t2)
    | .conj A B => .conj (go A) (go B)
    | .disj A B => .disj (go A) (go B)
    | .impl A B => .impl (go A) (go B)
    | .neg A => .neg (go A)
    | .all x A => .all x (go A)
    | .ex x A => .ex x (go A)
  go

-- ===================================================================
-- Theorem 6.7.1 (companion def): commonSentenceSet
-- ===================================================================

/-- Theorem 6.7.1 (companion): The set S = S1 cap S2 of
L-sentences that belong to both S1 and S2. -/
@[blueprint "chap6__theorem_6_7_1"]
def commonSentenceSet {L L1 L2 : Language}
    (e1 : LanguageExpansion L L1)
    (e2 : LanguageExpansion L L2)
    (S1 : Set (FormulaN L1)) (S2 : Set (FormulaN L2)) :
    Set (FormulaN L) :=
  fun A => formulaFVN A = ∅ ∧
    formulaLiftN e1 A ∈ S1 ∧ formulaLiftN e2 A ∈ S2

-- ===================================================================
-- Theorem 6.7.1 (companion def): isConsistentSetUnified
-- ===================================================================

/-- Theorem 6.7.1 (companion): A set of formulae is consistent when some
formula B is unprovable from every finite list of members of the set.
Languages with equality use G_=-provability; languages without equality
use G-provability. -/
@[blueprint "chap6__theorem_6_7_1"]
def isConsistentSetUnified {L : Language}
    (Gamma : Set (FormulaN L)) : Prop :=
  if hEq : L.hasEquality = true then
    isConsistentSetEq hEq Gamma
  else
    LCS.FirstOrder.Completeness.InfiniteSearch.isConsistentSet Gamma

-- ===================================================================
-- Theorem 6.7.1 (companion def): isCompleteSet
-- ===================================================================

/-- Theorem 6.7.1 (companion): A set S of L-sentences is complete:
for every closed L-formula C, either S proves C or S proves neg C. -/
@[blueprint "chap6__theorem_6_7_1"]
def isCompleteSet {L : Language}
    (S : Set (FormulaN L)) : Prop :=
  ∀ C : FormulaN L, formulaFVN C = ∅ →
    (∃ (cs : List (FormulaN L)),
      (∀ c, c ∈ cs → c ∈ S) ∧
      if hEq : L.hasEquality = true then
        sequentProvableEq hEq (Sequent.mk cs [C])
      else
        sequentProvableExt (Sequent.mk cs [C])) ∨
    (∃ (cs : List (FormulaN L)),
      (∀ c, c ∈ cs → c ∈ S) ∧
      if hEq : L.hasEquality = true then
        sequentProvableEq hEq (Sequent.mk cs [FormulaN.neg C])
      else
        sequentProvableExt (Sequent.mk cs [FormulaN.neg C]))

-- ===================================================================
-- Theorem 6.7.1 (companion def): languageCaseCondition
-- ===================================================================

/-- Theorem 6.7.1 (companion): The base language L satisfies one of
two conditions: (1) no function symbols and no equality, or
(2) has equality. -/
@[blueprint "chap6__theorem_6_7_1"]
def languageCaseCondition (L : Language) : Prop :=
  (L.hasEquality = false ∧ (L.funSymbols → False)) ∨
  (L.hasEquality = true)

-- ===================================================================
-- Theorem 6.7.1 (helpers): symbol equivalence relations
-- ===================================================================

/-- Theorem 6.7.1 (companion): The relation on `L1.funSymbols ⊕ L2.funSymbols`
that identifies `Sum.inl (expand1.funEmbed s)` with `Sum.inr (expand2.funEmbed s)`
for every L-symbol `s`. Forces the amalgamated language to treat
symbols of the common sublanguage L as shared between L1 and L2. -/
@[blueprint "chap6__theorem_6_7_1"]
def funSymbolRel {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    L1.funSymbols ⊕ L2.funSymbols → L1.funSymbols ⊕ L2.funSymbols → Prop
  | .inl f1, .inl f1' => f1 = f1'
  | .inr f2, .inr f2' => f2 = f2'
  | .inl f1, .inr f2 =>
      ∃ s : L.funSymbols,
        hI.expand1.funEmbed s = f1 ∧ hI.expand2.funEmbed s = f2
  | .inr f2, .inl f1 =>
      ∃ s : L.funSymbols,
        hI.expand1.funEmbed s = f1 ∧ hI.expand2.funEmbed s = f2

/-- Theorem 6.7.1 (companion): The analogous relation on predicate symbols. -/
@[blueprint "chap6__theorem_6_7_1"]
def predSymbolRel {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    L1.predSymbols ⊕ L2.predSymbols → L1.predSymbols ⊕ L2.predSymbols → Prop
  | .inl P1, .inl P1' => P1 = P1'
  | .inr P2, .inr P2' => P2 = P2'
  | .inl P1, .inr P2 =>
      ∃ Q : L.predSymbols,
        hI.expand1.predEmbed Q = P1 ∧ hI.expand2.predEmbed Q = P2
  | .inr P2, .inl P1 =>
      ∃ Q : L.predSymbols,
        hI.expand1.predEmbed Q = P1 ∧ hI.expand2.predEmbed Q = P2

/-- Theorem 6.7.1 (companion): The analogous relation on constant symbols. -/
@[blueprint "chap6__theorem_6_7_1"]
def constSymbolRel {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    L1.constSymbols ⊕ L2.constSymbols → L1.constSymbols ⊕ L2.constSymbols → Prop
  | .inl c1, .inl c1' => c1 = c1'
  | .inr c2, .inr c2' => c2 = c2'
  | .inl c1, .inr c2 =>
      ∃ d : L.constSymbols,
        hI.expand1.constEmbed d = c1 ∧ hI.expand2.constEmbed d = c2
  | .inr c2, .inl c1 =>
      ∃ d : L.constSymbols,
        hI.expand1.constEmbed d = c1 ∧ hI.expand2.constEmbed d = c2

-- ===================================================================
-- Theorem 6.7.1 (companion def): languageAmalgam
-- ===================================================================

/-- Theorem 6.7.1 (companion): The amalgamated language `L1 ⊔_L L2`:
symbols are the quotient of `L1.* ⊕ L2.*` by the equivalence that
identifies `expand1 s` with `expand2 s` for every symbol `s` of the
common sublanguage L. This is the semantic pushout that realises the
textbook's "L = L_1 ∩ L_2" assumption syntactically. -/
@[blueprint "chap6__theorem_6_7_1"]
def languageAmalgam {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) : Language where
  funSymbols := Quot (funSymbolRel hI)
  funArity :=
    Quot.lift
      (fun a => match a with
        | .inl f => L1.funArity f
        | .inr f => L2.funArity f)
      (by
        intro a b h
        cases a <;> cases b <;> simp_all [funSymbolRel]
        all_goals first
          | (obtain ⟨s, hs1, hs2⟩ := h;
             rw [← hs1, ← hs2, hI.expand1.funArityPreserve,
                 hI.expand2.funArityPreserve])
          | exact congrArg L1.funArity h
          | exact congrArg L2.funArity h)
  constSymbols := Quot (constSymbolRel hI)
  predSymbols := Quot (predSymbolRel hI)
  predArity :=
    Quot.lift
      (fun a => match a with
        | .inl P => L1.predArity P
        | .inr P => L2.predArity P)
      (by
        intro a b h
        cases a <;> cases b <;> simp_all [predSymbolRel]
        all_goals first
          | (obtain ⟨Q, hQ1, hQ2⟩ := h;
             rw [← hQ1, ← hQ2, hI.expand1.predArityPreserve,
                 hI.expand2.predArityPreserve])
          | exact congrArg L1.predArity h
          | exact congrArg L2.predArity h)
  hasEquality := L1.hasEquality || L2.hasEquality

-- ===================================================================
-- Theorem 6.7.1 (helpers): injectivity projections for amalgam
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Canonicalisation for the amalgamated function symbols: maps an
`Sum.inr f2` back to its L1 representative `Sum.inl (expand1 s)`
whenever `f2 = expand2 s`; otherwise leaves it on the right. Used to
prove that `Sum.inl` injects into the quotient. -/
noncomputable def canonFun {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    L1.funSymbols ⊕ L2.funSymbols → L1.funSymbols ⊕ L2.funSymbols
  | .inl f1 => .inl f1
  | .inr f2 =>
      if h : ∃ s : L.funSymbols, hI.expand2.funEmbed s = f2 then
        .inl (hI.expand1.funEmbed (Classical.choose h))
      else
        .inr f2

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Canonicalisation for amalgamated predicate symbols. -/
noncomputable def canonPred {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    L1.predSymbols ⊕ L2.predSymbols → L1.predSymbols ⊕ L2.predSymbols
  | .inl P1 => .inl P1
  | .inr P2 =>
      if h : ∃ Q : L.predSymbols, hI.expand2.predEmbed Q = P2 then
        .inl (hI.expand1.predEmbed (Classical.choose h))
      else
        .inr P2

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Canonicalisation for amalgamated constant symbols. -/
noncomputable def canonConst {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    L1.constSymbols ⊕ L2.constSymbols → L1.constSymbols ⊕ L2.constSymbols
  | .inl c1 => .inl c1
  | .inr c2 =>
      if h : ∃ d : L.constSymbols, hI.expand2.constEmbed d = c2 then
        .inl (hI.expand1.constEmbed (Classical.choose h))
      else
        .inr c2

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Canonicalisation respects the function-symbol relation. -/
theorem canonFun_respects {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2)
    (a b : L1.funSymbols ⊕ L2.funSymbols)
    (h : funSymbolRel hI a b) :
    canonFun hI a = canonFun hI b := by
-- BEGIN PROOF
  cases a <;> cases b <;> simp [funSymbolRel] at h
  · subst h; rfl
  · rename_i f1 f2
    obtain ⟨s, hs1, hs2⟩ := h
    simp [canonFun]
    have hex : ∃ s' : L.funSymbols, hI.expand2.funEmbed s' = f2 := ⟨s, hs2⟩
    rw [dif_pos hex]
    have hchoose : Classical.choose hex = s := by
      have := Classical.choose_spec hex
      exact hI.expand2.funInj (this.trans hs2.symm)
    rw [hchoose, hs1]
  · rename_i f2 f1
    obtain ⟨s, hs1, hs2⟩ := h
    simp [canonFun]
    have hex : ∃ s' : L.funSymbols, hI.expand2.funEmbed s' = f2 := ⟨s, hs2⟩
    rw [dif_pos hex]
    have hchoose : Classical.choose hex = s := by
      have := Classical.choose_spec hex
      exact hI.expand2.funInj (this.trans hs2.symm)
    rw [hchoose, hs1]
  · subst h; rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Canonicalisation respects the predicate-symbol relation. -/
theorem canonPred_respects {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2)
    (a b : L1.predSymbols ⊕ L2.predSymbols)
    (h : predSymbolRel hI a b) :
    canonPred hI a = canonPred hI b := by
-- BEGIN PROOF
  cases a <;> cases b <;> simp [predSymbolRel] at h
  · subst h; rfl
  · rename_i P1 P2
    obtain ⟨Q, hQ1, hQ2⟩ := h
    simp [canonPred]
    have hex : ∃ Q' : L.predSymbols, hI.expand2.predEmbed Q' = P2 := ⟨Q, hQ2⟩
    rw [dif_pos hex]
    have hchoose : Classical.choose hex = Q := by
      have := Classical.choose_spec hex
      exact hI.expand2.predInj (this.trans hQ2.symm)
    rw [hchoose, hQ1]
  · rename_i P2 P1
    obtain ⟨Q, hQ1, hQ2⟩ := h
    simp [canonPred]
    have hex : ∃ Q' : L.predSymbols, hI.expand2.predEmbed Q' = P2 := ⟨Q, hQ2⟩
    rw [dif_pos hex]
    have hchoose : Classical.choose hex = Q := by
      have := Classical.choose_spec hex
      exact hI.expand2.predInj (this.trans hQ2.symm)
    rw [hchoose, hQ1]
  · subst h; rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Canonicalisation respects the constant-symbol relation. -/
theorem canonConst_respects {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2)
    (a b : L1.constSymbols ⊕ L2.constSymbols)
    (h : constSymbolRel hI a b) :
    canonConst hI a = canonConst hI b := by
-- BEGIN PROOF
  cases a <;> cases b <;> simp [constSymbolRel] at h
  · subst h; rfl
  · rename_i c1 c2
    obtain ⟨d, hd1, hd2⟩ := h
    simp [canonConst]
    have hex : ∃ d' : L.constSymbols, hI.expand2.constEmbed d' = c2 := ⟨d, hd2⟩
    rw [dif_pos hex]
    have hchoose : Classical.choose hex = d := by
      have := Classical.choose_spec hex
      exact hI.expand2.constInj (this.trans hd2.symm)
    rw [hchoose, hd1]
  · rename_i c2 c1
    obtain ⟨d, hd1, hd2⟩ := h
    simp [canonConst]
    have hex : ∃ d' : L.constSymbols, hI.expand2.constEmbed d' = c2 := ⟨d, hd2⟩
    rw [dif_pos hex]
    have hchoose : Classical.choose hex = d := by
      have := Classical.choose_spec hex
      exact hI.expand2.constInj (this.trans hd2.symm)
    rw [hchoose, hd1]
  · subst h; rfl

-- ===================================================================
-- Theorem 6.7.1 (companion def): amalgamExpansionLeft
-- ===================================================================

/-- Theorem 6.7.1 (companion): The left predicate-symbol embedding into
the amalgamated language — simply lifts an L1 predicate into the
quotient via the left disjoint-sum injection. -/
@[blueprint "chap6__theorem_6_7_1"]
def amalgamExpansionLeft_predEmbed {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2)
    (P1 : L1.predSymbols) : (languageAmalgam hI).predSymbols :=
  Quot.mk _ (.inl P1)

/-- Theorem 6.7.1 (companion): The left function-symbol embedding. -/
@[blueprint "chap6__theorem_6_7_1"]
def amalgamExpansionLeft_funEmbed {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2)
    (f1 : L1.funSymbols) : (languageAmalgam hI).funSymbols :=
  Quot.mk _ (.inl f1)

/-- Theorem 6.7.1 (companion): The left constant-symbol embedding. -/
@[blueprint "chap6__theorem_6_7_1"]
def amalgamExpansionLeft_constEmbed {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2)
    (c1 : L1.constSymbols) : (languageAmalgam hI).constSymbols :=
  Quot.mk _ (.inl c1)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 6.7.1 (companion): The left predicate embedding preserves
arities by construction of `languageAmalgam.predArity`. -/
theorem amalgamExpansionLeft_predArityPreserve {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    ∀ P, (languageAmalgam hI).predArity (amalgamExpansionLeft_predEmbed hI P) =
      L1.predArity P :=
-- BEGIN PROOF
  fun _ => rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 6.7.1 (companion): The left function embedding preserves
arities by construction of `languageAmalgam.funArity`. -/
theorem amalgamExpansionLeft_funArityPreserve {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    ∀ f, (languageAmalgam hI).funArity (amalgamExpansionLeft_funEmbed hI f) =
      L1.funArity f :=
-- BEGIN PROOF
  fun _ => rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 6.7.1 (companion): `Quot.mk _ ∘ .inl` is injective as a map
from `L1.predSymbols` into the amalgamated predicate-symbol quotient. -/
theorem amalgamExpansionLeft_predInj {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    Function.Injective (amalgamExpansionLeft_predEmbed hI) := by
-- BEGIN PROOF
  intro P1 P1' h
  have hlift : Quot.lift (canonPred hI) (canonPred_respects hI)
      (Quot.mk _ (.inl P1)) =
      Quot.lift (canonPred hI) (canonPred_respects hI)
      (Quot.mk _ (.inl P1')) := congrArg _ h
  simpa [canonPred, amalgamExpansionLeft_predEmbed] using hlift

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 6.7.1 (companion): `Quot.mk _ ∘ .inl` is injective as a map
from `L1.funSymbols` into the amalgamated function-symbol quotient. -/
theorem amalgamExpansionLeft_funInj {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    Function.Injective (amalgamExpansionLeft_funEmbed hI) := by
-- BEGIN PROOF
  intro f1 f1' h
  have hlift : Quot.lift (canonFun hI) (canonFun_respects hI)
      (Quot.mk _ (.inl f1)) =
      Quot.lift (canonFun hI) (canonFun_respects hI)
      (Quot.mk _ (.inl f1')) := congrArg _ h
  simpa [canonFun, amalgamExpansionLeft_funEmbed] using hlift

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 6.7.1 (companion): `Quot.mk _ ∘ .inl` is injective as a map
from `L1.constSymbols` into the amalgamated constant-symbol quotient. -/
theorem amalgamExpansionLeft_constInj {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    Function.Injective (amalgamExpansionLeft_constEmbed hI) := by
-- BEGIN PROOF
  intro c1 c1' h
  have hlift : Quot.lift (canonConst hI) (canonConst_respects hI)
      (Quot.mk _ (.inl c1)) =
      Quot.lift (canonConst hI) (canonConst_respects hI)
      (Quot.mk _ (.inl c1')) := congrArg _ h
  simpa [canonConst, amalgamExpansionLeft_constEmbed] using hlift

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 6.7.1 (companion): The amalgamated language has equality if
the L1 side does (inherited through the left disjunct of
`L1.hasEquality || L2.hasEquality`). -/
theorem amalgamExpansionLeft_eqPreserve {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    L1.hasEquality = true → (languageAmalgam hI).hasEquality = true := by
-- BEGIN PROOF
  intro h
  simp only [languageAmalgam, h, Bool.true_or]

/-- Theorem 6.7.1 (companion): The canonical expansion embedding
of L1 into the amalgamated language via the left injection followed
by the quotient map. -/
@[blueprint "chap6__theorem_6_7_1"]
def amalgamExpansionLeft {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    LanguageExpansion L1 (languageAmalgam hI) where
  predEmbed := amalgamExpansionLeft_predEmbed hI
  predArityPreserve := amalgamExpansionLeft_predArityPreserve hI
  predInj := amalgamExpansionLeft_predInj hI
  funEmbed := amalgamExpansionLeft_funEmbed hI
  funArityPreserve := amalgamExpansionLeft_funArityPreserve hI
  funInj := amalgamExpansionLeft_funInj hI
  constEmbed := amalgamExpansionLeft_constEmbed hI
  constInj := amalgamExpansionLeft_constInj hI
  eqPreserve := amalgamExpansionLeft_eqPreserve hI

-- ===================================================================
-- Theorem 6.7.1 (companion def): amalgamExpansionRight
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Symmetric canonicalisation for the amalgamated function symbols,
mapping everything to the L2-side representative when possible. Used
to prove that `Sum.inr` injects into the quotient. -/
noncomputable def canonFunR {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    L1.funSymbols ⊕ L2.funSymbols → L1.funSymbols ⊕ L2.funSymbols
  | .inr f2 => .inr f2
  | .inl f1 =>
      if h : ∃ s : L.funSymbols, hI.expand1.funEmbed s = f1 then
        .inr (hI.expand2.funEmbed (Classical.choose h))
      else
        .inl f1

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Symmetric canonicalisation for amalgamated predicate symbols. -/
noncomputable def canonPredR {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    L1.predSymbols ⊕ L2.predSymbols → L1.predSymbols ⊕ L2.predSymbols
  | .inr P2 => .inr P2
  | .inl P1 =>
      if h : ∃ Q : L.predSymbols, hI.expand1.predEmbed Q = P1 then
        .inr (hI.expand2.predEmbed (Classical.choose h))
      else
        .inl P1

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Symmetric canonicalisation for amalgamated constant symbols. -/
noncomputable def canonConstR {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    L1.constSymbols ⊕ L2.constSymbols → L1.constSymbols ⊕ L2.constSymbols
  | .inr c2 => .inr c2
  | .inl c1 =>
      if h : ∃ d : L.constSymbols, hI.expand1.constEmbed d = c1 then
        .inr (hI.expand2.constEmbed (Classical.choose h))
      else
        .inl c1

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Symmetric canonicalisation respects the function-symbol relation. -/
theorem canonFunR_respects {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2)
    (a b : L1.funSymbols ⊕ L2.funSymbols)
    (h : funSymbolRel hI a b) :
    canonFunR hI a = canonFunR hI b := by
-- BEGIN PROOF
  cases a <;> cases b <;> simp [funSymbolRel] at h
  · subst h; rfl
  · rename_i f1 f2
    obtain ⟨s, hs1, hs2⟩ := h
    simp [canonFunR]
    have hex : ∃ s' : L.funSymbols, hI.expand1.funEmbed s' = f1 := ⟨s, hs1⟩
    rw [dif_pos hex]
    have hchoose : Classical.choose hex = s := by
      have := Classical.choose_spec hex
      exact hI.expand1.funInj (this.trans hs1.symm)
    rw [hchoose, hs2]
  · rename_i f2 f1
    obtain ⟨s, hs1, hs2⟩ := h
    simp [canonFunR]
    have hex : ∃ s' : L.funSymbols, hI.expand1.funEmbed s' = f1 := ⟨s, hs1⟩
    rw [dif_pos hex]
    have hchoose : Classical.choose hex = s := by
      have := Classical.choose_spec hex
      exact hI.expand1.funInj (this.trans hs1.symm)
    rw [hchoose, hs2]
  · subst h; rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Symmetric canonicalisation respects the predicate-symbol relation. -/
theorem canonPredR_respects {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2)
    (a b : L1.predSymbols ⊕ L2.predSymbols)
    (h : predSymbolRel hI a b) :
    canonPredR hI a = canonPredR hI b := by
-- BEGIN PROOF
  cases a <;> cases b <;> simp [predSymbolRel] at h
  · subst h; rfl
  · rename_i P1 P2
    obtain ⟨Q, hQ1, hQ2⟩ := h
    simp [canonPredR]
    have hex : ∃ Q' : L.predSymbols, hI.expand1.predEmbed Q' = P1 := ⟨Q, hQ1⟩
    rw [dif_pos hex]
    have hchoose : Classical.choose hex = Q := by
      have := Classical.choose_spec hex
      exact hI.expand1.predInj (this.trans hQ1.symm)
    rw [hchoose, hQ2]
  · rename_i P2 P1
    obtain ⟨Q, hQ1, hQ2⟩ := h
    simp [canonPredR]
    have hex : ∃ Q' : L.predSymbols, hI.expand1.predEmbed Q' = P1 := ⟨Q, hQ1⟩
    rw [dif_pos hex]
    have hchoose : Classical.choose hex = Q := by
      have := Classical.choose_spec hex
      exact hI.expand1.predInj (this.trans hQ1.symm)
    rw [hchoose, hQ2]
  · subst h; rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Symmetric canonicalisation respects the constant-symbol relation. -/
theorem canonConstR_respects {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2)
    (a b : L1.constSymbols ⊕ L2.constSymbols)
    (h : constSymbolRel hI a b) :
    canonConstR hI a = canonConstR hI b := by
-- BEGIN PROOF
  cases a <;> cases b <;> simp [constSymbolRel] at h
  · subst h; rfl
  · rename_i c1 c2
    obtain ⟨d, hd1, hd2⟩ := h
    simp [canonConstR]
    have hex : ∃ d' : L.constSymbols, hI.expand1.constEmbed d' = c1 := ⟨d, hd1⟩
    rw [dif_pos hex]
    have hchoose : Classical.choose hex = d := by
      have := Classical.choose_spec hex
      exact hI.expand1.constInj (this.trans hd1.symm)
    rw [hchoose, hd2]
  · rename_i c2 c1
    obtain ⟨d, hd1, hd2⟩ := h
    simp [canonConstR]
    have hex : ∃ d' : L.constSymbols, hI.expand1.constEmbed d' = c1 := ⟨d, hd1⟩
    rw [dif_pos hex]
    have hchoose : Classical.choose hex = d := by
      have := Classical.choose_spec hex
      exact hI.expand1.constInj (this.trans hd1.symm)
    rw [hchoose, hd2]
  · subst h; rfl

/-- Theorem 6.7.1 (companion): The right predicate-symbol embedding. -/
@[blueprint "chap6__theorem_6_7_1"]
def amalgamExpansionRight_predEmbed {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2)
    (P2 : L2.predSymbols) : (languageAmalgam hI).predSymbols :=
  Quot.mk _ (.inr P2)

/-- Theorem 6.7.1 (companion): The right function-symbol embedding. -/
@[blueprint "chap6__theorem_6_7_1"]
def amalgamExpansionRight_funEmbed {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2)
    (f2 : L2.funSymbols) : (languageAmalgam hI).funSymbols :=
  Quot.mk _ (.inr f2)

/-- Theorem 6.7.1 (companion): The right constant-symbol embedding. -/
@[blueprint "chap6__theorem_6_7_1"]
def amalgamExpansionRight_constEmbed {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2)
    (c2 : L2.constSymbols) : (languageAmalgam hI).constSymbols :=
  Quot.mk _ (.inr c2)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 6.7.1 (companion): The right predicate embedding preserves
arities by construction of `languageAmalgam.predArity`. -/
theorem amalgamExpansionRight_predArityPreserve {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    ∀ P, (languageAmalgam hI).predArity (amalgamExpansionRight_predEmbed hI P) =
      L2.predArity P :=
-- BEGIN PROOF
  fun _ => rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 6.7.1 (companion): The right function embedding preserves
arities by construction of `languageAmalgam.funArity`. -/
theorem amalgamExpansionRight_funArityPreserve {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    ∀ f, (languageAmalgam hI).funArity (amalgamExpansionRight_funEmbed hI f) =
      L2.funArity f :=
-- BEGIN PROOF
  fun _ => rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 6.7.1 (companion): `Quot.mk _ ∘ .inr` is injective as a map
from `L2.predSymbols` into the amalgamated predicate-symbol quotient. -/
theorem amalgamExpansionRight_predInj {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    Function.Injective (amalgamExpansionRight_predEmbed hI) := by
-- BEGIN PROOF
  intro P2 P2' h
  have hlift : Quot.lift (canonPredR hI) (canonPredR_respects hI)
      (Quot.mk _ (.inr P2)) =
      Quot.lift (canonPredR hI) (canonPredR_respects hI)
      (Quot.mk _ (.inr P2')) := congrArg _ h
  simpa [canonPredR, amalgamExpansionRight_predEmbed] using hlift

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 6.7.1 (companion): `Quot.mk _ ∘ .inr` is injective as a map
from `L2.funSymbols` into the amalgamated function-symbol quotient. -/
theorem amalgamExpansionRight_funInj {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    Function.Injective (amalgamExpansionRight_funEmbed hI) := by
-- BEGIN PROOF
  intro f2 f2' h
  have hlift : Quot.lift (canonFunR hI) (canonFunR_respects hI)
      (Quot.mk _ (.inr f2)) =
      Quot.lift (canonFunR hI) (canonFunR_respects hI)
      (Quot.mk _ (.inr f2')) := congrArg _ h
  simpa [canonFunR, amalgamExpansionRight_funEmbed] using hlift

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 6.7.1 (companion): `Quot.mk _ ∘ .inr` is injective as a map
from `L2.constSymbols` into the amalgamated constant-symbol quotient. -/
theorem amalgamExpansionRight_constInj {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    Function.Injective (amalgamExpansionRight_constEmbed hI) := by
-- BEGIN PROOF
  intro c2 c2' h
  have hlift : Quot.lift (canonConstR hI) (canonConstR_respects hI)
      (Quot.mk _ (.inr c2)) =
      Quot.lift (canonConstR hI) (canonConstR_respects hI)
      (Quot.mk _ (.inr c2')) := congrArg _ h
  simpa [canonConstR, amalgamExpansionRight_constEmbed] using hlift

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 6.7.1 (companion): The amalgamated language has equality if
the L2 side does (inherited through the right disjunct of
`L1.hasEquality || L2.hasEquality`). -/
theorem amalgamExpansionRight_eqPreserve {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    L2.hasEquality = true → (languageAmalgam hI).hasEquality = true := by
-- BEGIN PROOF
  intro h
  simp only [languageAmalgam, h, Bool.or_true]

/-- Theorem 6.7.1 (companion): The canonical expansion embedding
of L2 into the amalgamated language via the right injection followed
by the quotient map. -/
@[blueprint "chap6__theorem_6_7_1"]
def amalgamExpansionRight {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2) :
    LanguageExpansion L2 (languageAmalgam hI) where
  predEmbed := amalgamExpansionRight_predEmbed hI
  predArityPreserve := amalgamExpansionRight_predArityPreserve hI
  predInj := amalgamExpansionRight_predInj hI
  funEmbed := amalgamExpansionRight_funEmbed hI
  funArityPreserve := amalgamExpansionRight_funArityPreserve hI
  funInj := amalgamExpansionRight_funInj hI
  constEmbed := amalgamExpansionRight_constEmbed hI
  constInj := amalgamExpansionRight_constInj hI
  eqPreserve := amalgamExpansionRight_eqPreserve hI

-- ===================================================================
-- Theorem 6.7.1 (companion def): setUnion
-- ===================================================================

/-- Theorem 6.7.1 (companion): The union of S1 and S2 as a set of
formulae over the amalgamated language. -/
@[blueprint "chap6__theorem_6_7_1"]
def setUnion {L L1 L2 : Language}
    (hI : LanguageIntersection L L1 L2)
    (S1 : Set (FormulaN L1)) (S2 : Set (FormulaN L2)) :
    Set (FormulaN (languageAmalgam hI)) :=
  fun A =>
    (∃ A1, A1 ∈ S1 ∧
      formulaLiftN (amalgamExpansionLeft hI) A1 = A) ∨
    (∃ A2, A2 ∈ S2 ∧
      formulaLiftN (amalgamExpansionRight hI) A2 = A)

open LCS.FirstOrder.SemanticsN

-- ===================================================================
-- Theorem 6.7.1 (helper): restrictLeft
-- ===================================================================





-- ===================================================================
-- Theorem 6.7.1 (helper): inconsistency extraction
-- ===================================================================



/-- Model amalgamation: the core content of Robinson's theorem. -/
theorem setUnion_satisfiable
    {L L1 L2 : Language}
    (hIntersect : LanguageIntersection L L1 L2)
    [Countable (FormulaN (languageAmalgam hIntersect))]
    (_ : languageCaseCondition L)
    (S1 : Set (FormulaN L1)) (S2 : Set (FormulaN L2))
    (_ : isSentenceSet S1) (_ : isSentenceSet S2)
    (hCons1 : isConsistentSetUnified S1) (hCons2 : isConsistentSetUnified S2)
    (_ : isCompleteSet
      (commonSentenceSet hIntersect.expand1 hIntersect.expand2 S1 S2)) :
    satisfiableSetN (setUnion hIntersect S1 S2) := by
-- BEGIN PROOF
  -- The textbook argument uses compactness via Craig interpolation.
  -- (a) conjunction introduction in G/G_=/LK
  -- (b) transfer between G/G_= and LK/LKe proof systems
  -- (c) splitting the finite list provability into the partition form
  -- Craig interpolation (Theorems 6.5.1/6.5.2) is sorry-free.
  -- DEBT(Theorem 6.7.1: model amalgamation through Craig interpolation; proof pending)
  sorry

-- ===================================================================
-- Theorem 6.7.1: robinson_joint_consistency
-- ===================================================================

/-- Theorem 6.7.1: (Robinson's joint consistency theorem) If
L = L1 cap L2, S1 is a consistent set of L1-sentences, S2 is a
consistent set of L2-sentences, and S = S1 cap S2 is complete, then
S1 union S2 is consistent. -/
@[blueprint "chap6__theorem_6_7_1" (main := true)]
theorem robinson_joint_consistency
    {L L1 L2 : Language}
    (hIntersect : LanguageIntersection L L1 L2)
    [Countable (FormulaN (languageAmalgam hIntersect))]
    (hCase : languageCaseCondition L)
    (S1 : Set (FormulaN L1)) (S2 : Set (FormulaN L2))
    (hSent1 : isSentenceSet S1) (hSent2 : isSentenceSet S2)
    (hCons1 : isConsistentSetUnified S1)
    (hCons2 : isConsistentSetUnified S2)
    (hComplete : isCompleteSet
      (commonSentenceSet hIntersect.expand1 hIntersect.expand2
        S1 S2)) :
    isConsistentSetUnified (setUnion hIntersect S1 S2) 

/-- Theorem 6.7.1 (companion): Consistency of two sentence sets does not
imply consistency of their union, even when all three languages coincide. -/
@[blueprint "chap6__theorem_6_7_1"]
theorem union_consistency_not_necessary :
    ¬ ∀ (L L1 L2 : Language) (hI : LanguageIntersection L L1 L2)
      (S1 : Set (FormulaN L1)) (S2 : Set (FormulaN L2)),
      isSentenceSet S1 → isSentenceSet S2 →
      isConsistentSetUnified S1 → isConsistentSetUnified S2 →
      isConsistentSetUnified (setUnion hI S1 S2) 

/-- Theorem 6.7.1 (companion): A sentence set is incomplete when it is
not complete. -/
@[blueprint "chap6__theorem_6_7_1"]
def isIncompleteSet {L : Language} (S : Set (FormulaN L)) : Prop :=
  ¬ isCompleteSet S

/-- Theorem 6.7.1 (companion, R-UNION-WIT): For an incomplete sentence set S
and a closed sentence C undecidable from S, adjoining C or its negation gives
two consistent extensions whose intersection is S and whose union is inconsistent. -/
@[attach_debt, blueprint "chap6__theorem_6_7_1"]
theorem incomplete_consistent_extensions {L : Language}
    (S : Set (FormulaN L)) (C : FormulaN L)
    (hSent : isSentenceSet S) (hIncomplete : isIncompleteSet S)
    (hClosed : formulaFVN C = ∅)
    (hWitness : ∀ cs : List (FormulaN L), (∀ c ∈ cs, c ∈ S) →
      if hEq : L.hasEquality = true then
        ¬ sequentProvableEq hEq (Sequent.mk cs [C]) ∧
        ¬ sequentProvableEq hEq (Sequent.mk cs [FormulaN.neg C])
      else
        ¬ sequentProvableExt (Sequent.mk cs [C]) ∧
        ¬ sequentProvableExt (Sequent.mk cs [FormulaN.neg C])) :
    isConsistentSetUnified (S ∪ Set.singleton C) ∧
    isConsistentSetUnified (S ∪ Set.singleton (FormulaN.neg C)) ∧
    (S ∪ Set.singleton C) ∩ (S ∪ Set.singleton (FormulaN.neg C)) = S ∧
    ¬ isConsistentSetUnified
      ((S ∪ Set.singleton C) ∪ (S ∪ Set.singleton (FormulaN.neg C))) 

/-- The incompleteness assertion cited in §6.7 for Peano arithmetic:
there is a closed arithmetic sentence C such that neither C nor ¬C
has a G= proof from any finite list of Peano axioms. This proposition
is supplied as a hypothesis in the illustration (OD-10). -/
@[blueprint "chap6__theorem_6_7_1"]
def PeanoIncompleteness : Prop :=
  ∃ C : FormulaN peanoLanguage, formulaFVN C = ∅ ∧
    ∀ cs : List (FormulaN peanoLanguage),
      (∀ A ∈ cs, A ∈ peanoArithAxioms) →
      ¬ sequentProvableEq (show peanoLanguage.hasEquality = true from rfl)
        (Sequent.mk cs [C]) ∧
      ¬ sequentProvableEq (show peanoLanguage.hasEquality = true from rfl)
        (Sequent.mk cs [FormulaN.neg C])

/-- The §6.7 arithmetic illustration for every closed sentence C
undecidable from the Peano axioms. Adjoining C and adjoining ¬C give
consistent sentence sets in the same arithmetic language, while their
ordinary set union is inconsistent. -/
theorem peano_undecidable_consistent_extensions
    (C : FormulaN peanoLanguage) (hClosed : formulaFVN C = ∅)
    (hUndecidable : ∀ cs : List (FormulaN peanoLanguage),
      (∀ A ∈ cs, A ∈ peanoArithAxioms) →
      ¬ sequentProvableEq (show peanoLanguage.hasEquality = true from rfl)
        (Sequent.mk cs [C]) ∧
      ¬ sequentProvableEq (show peanoLanguage.hasEquality = true from rfl)
        (Sequent.mk cs [FormulaN.neg C])) :
    isSentenceSet (peanoArithAxioms ∪ Set.singleton C) ∧
    isSentenceSet (peanoArithAxioms ∪ Set.singleton (FormulaN.neg C)) ∧
    isConsistentSetUnified (peanoArithAxioms ∪ Set.singleton C) ∧
    isConsistentSetUnified (peanoArithAxioms ∪ Set.singleton (FormulaN.neg C)) ∧
    ¬ isConsistentSetUnified
      ((peanoArithAxioms ∪ Set.singleton C) ∪
        (peanoArithAxioms ∪ Set.singleton (FormulaN.neg C))) := by
  have hSent : isSentenceSet peanoArithAxioms := by
    -- REPAIR(T6-V2-05): proof pending
    sorry
  have hIncomplete : isIncompleteSet peanoArithAxioms := by
    intro hComplete
    rcases hComplete C hClosed with ⟨cs, hcs, hProv⟩ | ⟨cs, hcs, hProv⟩
    · exact (hUndecidable cs hcs).1 hProv
    · exact (hUndecidable cs hcs).2 hProv
  have hExtensions := incomplete_consistent_extensions peanoArithAxioms C
    hSent hIncomplete hClosed (fun cs hcs => hUndecidable cs hcs)
  refine ⟨?_, ?_, hExtensions.1, hExtensions.2.1, hExtensions.2.2.2⟩
  · intro A hA
    rcases hA with hA | hA
    · exact hSent A hA
    · change A = C at hA
      subst A
      exact hClosed
  · intro A hA
    rcases hA with hA | hA
    · exact hSent A hA
    · change A = FormulaN.neg C at hA
      subst A
      exact hClosed

/-- Gödel's incompleteness assertion supplies the §6.7 example of two
consistent sentence sets with inconsistent union. Both extensions and
their union are sets of formulae of `peanoLanguage`. -/
@[blueprint "chap6__theorem_6_7_1"]
theorem goedel_union_failure (h : PeanoIncompleteness) :
    ∃ C : FormulaN peanoLanguage, formulaFVN C = ∅ ∧
      (∀ cs : List (FormulaN peanoLanguage),
        (∀ A ∈ cs, A ∈ peanoArithAxioms) →
        ¬ sequentProvableEq (show peanoLanguage.hasEquality = true from rfl)
          (Sequent.mk cs [C]) ∧
        ¬ sequentProvableEq (show peanoLanguage.hasEquality = true from rfl)
          (Sequent.mk cs [FormulaN.neg C])) ∧
      isSentenceSet (peanoArithAxioms ∪ Set.singleton C) ∧
      isSentenceSet (peanoArithAxioms ∪ Set.singleton (FormulaN.neg C)) ∧
      isConsistentSetUnified (peanoArithAxioms ∪ Set.singleton C) ∧
      isConsistentSetUnified (peanoArithAxioms ∪ Set.singleton (FormulaN.neg C)) ∧
      ¬ isConsistentSetUnified
        ((peanoArithAxioms ∪ Set.singleton C) ∪
          (peanoArithAxioms ∪ Set.singleton (FormulaN.neg C))) 

end LCS.CutElim.Robinson
