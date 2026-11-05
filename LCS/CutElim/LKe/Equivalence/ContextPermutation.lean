import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.CutElim.CompletenessBridge
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.LKe.Equivalence.AtomicLeaves
import Attach
import LCS.CutElim.LKe.Equivalence.ContextPermutation.ProofsStamp

section
namespace LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality.Completeness
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.CompletenessBridge

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Independent permutations of the two contexts of a G=-proof are
admissible without adding an inference level.  The construction recursively
rebuilds every G and equality inference.  It also transports the
atomic-or-quantified leaf invariant used by the permutation lemmas below. -/
theorem geqPermuteContexts {L : Language}
    {hL : L.hasEquality = true} {s : Sequent L}
    (T : GEqProofTree hL s)
    (Γ' Δ' : List (FormulaN L))
    (hΓ : s.antecedent.Perm Γ')
    (hΔ : s.succedent.Perm Δ')
    (hleaf : ∀ s' ∈ geqLeafSequents T,
      seqAllAtomicOrQuantified s') :
    ∃ T' : GEqProofTree hL (Sequent.mk Γ' Δ'),
      geqDepth T' = geqDepth T ∧
      ∀ s' ∈ geqLeafSequents T',
        seqAllAtomicOrQuantified s' := by
  have permFresh :
      ∀ (y : Nat) {Γ Δ Γ' Δ' : List (FormulaN L)},
        Γ.Perm Γ' →
        Δ.Perm Δ' →
        (∀ F ∈ Γ ++ Δ, y ∉ Variables.formulaFVN F) →
        ∀ F ∈ Γ' ++ Δ', y ∉ Variables.formulaFVN F := by
    intro y Γ Δ Γ' Δ' hΓ hΔ hfresh F hF
    rcases List.mem_append.mp hF with hF | hF
    · exact hfresh F
        (List.mem_append.mpr (Or.inl (hΓ.mem_iff.mpr hF)))
    · exact hfresh F
        (List.mem_append.mpr (Or.inr (hΔ.mem_iff.mpr hF)))
  have permAxiom :
      ∀ (s₀ : Sequent L) (hAx : isAxiom s₀)
        (Γ₀ Δ₀ : List (FormulaN L)),
        s₀.antecedent.Perm Γ₀ →
        s₀.succedent.Perm Δ₀ →
        seqAllAtomicOrQuantified s₀ →
        ∃ p : GEqProofTree hL (Sequent.mk Γ₀ Δ₀),
          geqDepth p = 0 ∧
          ∀ s' ∈ geqLeafSequents p,
            seqAllAtomicOrQuantified s' := by
    intro s₀ hAx Γ₀ Δ₀ hΓ₀ hΔ₀ hs₀
    rcases hAx with ⟨F, hFant, hFsuc⟩
    let p : GEqProofTree hL (Sequent.mk Γ₀ Δ₀) :=
      .axiom_ _ ⟨F, hΓ₀.mem_iff.mp hFant, hΔ₀.mem_iff.mp hFsuc⟩
    refine ⟨p, rfl, ?_⟩
    intro s' hs'
    simp only [p, geqLeafSequents, List.mem_cons,
      List.not_mem_nil, or_false] at hs'
    subst s'
    exact seqAllAtomicOrQuantified_perm hΓ₀ hΔ₀ hs₀
  suffices h :
      ∀ n : Nat, ∀ {s : Sequent L} (T : GEqProofTree hL s),
        geqDepth T = n →
        ∀ (Γ' Δ' : List (FormulaN L)),
          s.antecedent.Perm Γ' →
          s.succedent.Perm Δ' →
          (∀ s' ∈ geqLeafSequents T,
            seqAllAtomicOrQuantified s') →
          ∃ T' : GEqProofTree hL (Sequent.mk Γ' Δ'),
            geqDepth T' = geqDepth T ∧
            ∀ s' ∈ geqLeafSequents T',
              seqAllAtomicOrQuantified s' by
    exact h (geqDepth T) T rfl Γ' Δ' hΓ hΔ hleaf
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro s T hdepth Γ' Δ' hΓ hΔ hleaf
    have permOne :
        ∀ {prem conc : Sequent L}
          (rule : GentzenStep1Ext prem conc)
          (sub : GEqProofTree hL prem),
          geqDepth sub < n →
          conc.antecedent.Perm Γ' →
          conc.succedent.Perm Δ' →
          (∀ s' ∈ geqLeafSequents sub,
            seqAllAtomicOrQuantified s') →
          ∃ p : GEqProofTree hL (Sequent.mk Γ' Δ'),
            geqDepth p = 1 + geqDepth sub ∧
            ∀ s' ∈ geqLeafSequents p,
              seqAllAtomicOrQuantified s' := by
      exact geqPermuteContexts_permOne L hL n ih permFresh Γ' Δ'
    have permTwo :
        ∀ {prem1 prem2 conc : Sequent L}
          (rule : GentzenStep2Ext prem1 prem2 conc)
          (sub1 : GEqProofTree hL prem1)
          (sub2 : GEqProofTree hL prem2),
          geqDepth sub1 < n →
          geqDepth sub2 < n →
          conc.antecedent.Perm Γ' →
          conc.succedent.Perm Δ' →
          (∀ s' ∈ geqLeafSequents sub1,
            seqAllAtomicOrQuantified s') →
          (∀ s' ∈ geqLeafSequents sub2,
            seqAllAtomicOrQuantified s') →
          ∃ p : GEqProofTree hL (Sequent.mk Γ' Δ'),
            geqDepth p =
                1 + max (geqDepth sub1) (geqDepth sub2) ∧
            ∀ s' ∈ geqLeafSequents p,
              seqAllAtomicOrQuantified s' := by
      exact geqPermuteContexts_permTwo L hL n ih Γ' Δ'
    cases T with
    | base g =>
      exact geqPermuteContexts_base L hL permAxiom n s Γ' Δ' hΓ hΔ permOne permTwo g hdepth hleaf
    | axiom_ _ hAx =>
      obtain ⟨p, hpd, hpl⟩ :=
        permAxiom s hAx Γ' Δ' hΓ hΔ
          (hleaf s (by simp [geqLeafSequents]))
      exact ⟨p, by simpa [geqDepth] using hpd, hpl⟩
    | onePremise rule sub =>
      obtain ⟨p, hpd, hpl⟩ :=
        permOne rule sub (by
          simp only [geqDepth] at hdepth
          omega) hΓ hΔ (by
            simpa [geqLeafSequents] using hleaf)
      exact ⟨p, by simpa [geqDepth] using hpd, hpl⟩
    | twoPremise rule sub1 sub2 =>
      obtain ⟨p, hpd, hpl⟩ :=
        permTwo rule sub1 sub2 (by
          simp only [geqDepth] at hdepth
          omega) (by
          simp only [geqDepth] at hdepth
          omega) hΓ hΔ (by
            intro s' hs'
            exact hleaf s' (by
              simp only [geqLeafSequents, List.mem_append]
              exact Or.inl hs')) (by
            intro s' hs'
            exact hleaf s' (by
              simp only [geqLeafSequents, List.mem_append]
              exact Or.inr hs'))
      exact ⟨p, by simpa [geqDepth] using hpd, hpl⟩
    | eqRefl t Γr Δr sub =>
      exact geqPermuteContexts_eqRefl L hL n ih Γ' Δ' t _ _ sub hΓ hΔ hdepth hleaf
    | eqFuncCong f ss ts Γr Δr sub =>
      exact geqPermuteContexts_eqFuncCong L hL n ih Γ' Δ' f ss ts _ _ sub hΓ hΔ hdepth hleaf
    | eqPredCong P ss ts Γr Δr sub =>
      exact geqPermuteContexts_eqPredCong L hL n ih Γ' Δ' P ss ts _ _ sub hΓ hΔ hdepth hleaf
    | eqGeneral axioms hne haxioms Γr Δr sub =>
      exact geqPermuteContexts_eqGeneral L hL n ih Γ' Δ' axioms hne haxioms _ _ sub hΓ hΔ hdepth hleaf
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Depth-preserving adjacent exchange in the antecedent of a G=-proof.
Unlike adding an explicit exchange inference, this transform recursively
commutes the positional swap through the complete proof tree. -/
theorem geqExchangeLeft_adjacent {L : Language}
    {hL : L.hasEquality = true}
    (Γ Δ Λ : List (FormulaN L)) (A B : FormulaN L)
    (T : GEqProofTree hL
      (Sequent.mk (Γ ++ [A, B] ++ Δ) Λ))
    (hleaf : ∀ s' ∈ geqLeafSequents T,
      seqAllAtomicOrQuantified s') :
    ∃ T' : GEqProofTree hL
        (Sequent.mk (Γ ++ [B, A] ++ Δ) Λ),
      geqDepth T' = geqDepth T ∧
      ∀ s' ∈ geqLeafSequents T',
        seqAllAtomicOrQuantified s' := by
  have hswap :
      (Γ ++ [A, B] ++ Δ).Perm
        (Γ ++ [B, A] ++ Δ) := by
    have hab :
        ([A, B] ++ Δ).Perm ([B, A] ++ Δ) :=
      List.Perm.append_right Δ (List.Perm.swap B A [])
    simpa [List.append_assoc] using List.Perm.append_left Γ hab
  exact geqPermuteContexts T
    (Γ ++ [B, A] ++ Δ) Λ hswap (List.Perm.refl Λ) hleaf

-- Axiom probe: the swap is performed at depth zero, without an inference.
-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} {hL : L.hasEquality = true}
    (A B : FormulaN L)
    (hA : isAtomicOrQuantified A)
    (hB : isAtomicOrQuantified B) :
    ∃ T' : GEqProofTree hL (Sequent.mk [B, A] [A]),
      geqDepth T' = 0 := by
  let T : GEqProofTree hL (Sequent.mk [A, B] [A]) :=
    .axiom_ _ ⟨A, by simp, by simp⟩
  have hseq :
      seqAllAtomicOrQuantified (Sequent.mk [A, B] [A]) := by
    simp [seqAllAtomicOrQuantified, hA, hB]
  have hleaf :
      ∀ s' ∈ geqLeafSequents T,
        seqAllAtomicOrQuantified s' := by
    intro s' hs'
    simp only [T, geqLeafSequents, List.mem_cons,
      List.not_mem_nil, or_false] at hs'
    subst s'
    exact hseq
  obtain ⟨T', hdepth, _⟩ :=
    geqExchangeLeft_adjacent [] [] [A] A B T hleaf
  exact ⟨T', by simpa [T, geqDepth] using hdepth⟩

-- Logical probe: the selected pair contains the conjunction introduced at
-- the root, so the transform must commute through that logical inference.
-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} {hL : L.hasEquality = true}
    (A B C : FormulaN L)
    (hA : isAtomicOrQuantified A)
    (hB : isAtomicOrQuantified B)
    (hC : isAtomicOrQuantified C) :
    ∃ T' : GEqProofTree hL
        (Sequent.mk [C, FormulaN.conj A B] [A]),
      geqDepth T' = 1 := by
  let T : GEqProofTree hL
      (Sequent.mk [FormulaN.conj A B, C] [A]) :=
    .onePremise
      (.conjLeft [] [C] [A] A B)
      (.axiom_ (Sequent.mk [A, B, C] [A])
        ⟨A, by simp, by simp⟩)
  have hseq :
      seqAllAtomicOrQuantified (Sequent.mk [A, B, C] [A]) := by
    simp [seqAllAtomicOrQuantified, hA, hB, hC]
  have hleaf :
      ∀ s' ∈ geqLeafSequents T,
        seqAllAtomicOrQuantified s' := by
    intro s' hs'
    simp only [T, geqLeafSequents, List.mem_cons,
      List.not_mem_nil, or_false] at hs'
    subst s'
    exact hseq
  obtain ⟨T', hdepth, _⟩ :=
    geqExchangeLeft_adjacent [] [] [A]
      (FormulaN.conj A B) C T hleaf
  exact ⟨T', by simpa [T, geqDepth] using hdepth⟩

-- Equality probe: reflexivity is reconstructed after recursively exchanging
-- the premise, rather than dropping the G= inference into a pure-G route.
-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} (hL : L.hasEquality = true)
    (t : Term L) (A B : FormulaN L)
    (hA : isAtomicOrQuantified A)
    (hB : isAtomicOrQuantified B) :
    ∃ T' : GEqProofTree hL (Sequent.mk [B, A] [A]),
      geqDepth T' = 1 := by
  let E := FormulaN.eq_ hL t t
  let T : GEqProofTree hL (Sequent.mk [A, B] [A]) :=
    .eqRefl t [A, B] [A]
      (.axiom_ (Sequent.mk [A, B, E] [A])
        ⟨A, by simp [E], by simp⟩)
  have hE : isAtomicOrQuantified E := by
    simp [E, isAtomicOrQuantified, FormulaN.isAtomic]
  have hseq :
      seqAllAtomicOrQuantified (Sequent.mk [A, B, E] [A]) := by
    simp [seqAllAtomicOrQuantified, hE, hA, hB]
  have hleaf :
      ∀ s' ∈ geqLeafSequents T,
        seqAllAtomicOrQuantified s' := by
    intro s' hs'
    change s' ∈ [Sequent.mk [A, B, E] [A]] at hs'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs'
    subst s'
    exact hseq
  obtain ⟨T', hdepth, _⟩ :=
    geqExchangeLeft_adjacent [] [] [A] A B T hleaf
  have hTdepth : geqDepth T = 1 := rfl
  exact ⟨T', hdepth.trans hTdepth⟩

-- Duplicate probe: the marked occurrence is positional.  Swapping the
-- second `A` with `B` does not collapse it into the equal first occurrence.
-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} {hL : L.hasEquality = true}
    (A B : FormulaN L)
    (hA : isAtomicOrQuantified A)
    (hB : isAtomicOrQuantified B) :
    ∃ T' : GEqProofTree hL (Sequent.mk [A, B, A] [A]),
      geqDepth T' = 0 := by
  let T : GEqProofTree hL (Sequent.mk [A, A, B] [A]) :=
    .axiom_ _ ⟨A, by simp, by simp⟩
  have hseq :
      seqAllAtomicOrQuantified (Sequent.mk [A, A, B] [A]) := by
    simp [seqAllAtomicOrQuantified, hA, hB]
  have hleaf :
      ∀ s' ∈ geqLeafSequents T,
        seqAllAtomicOrQuantified s' := by
    intro s' hs'
    simp only [T, geqLeafSequents, List.mem_cons,
      List.not_mem_nil, or_false] at hs'
    subst s'
    exact hseq
  obtain ⟨T', hdepth, _⟩ :=
    geqExchangeLeft_adjacent [A] [] [A] A B T hleaf
  exact ⟨T', by simpa [T, geqDepth] using hdepth⟩

-- ===================================================================
-- Lemma 6.3.2 (required def): rootIsConjRight
-- ===================================================================

/-- Lemma 6.3.2 (required def): Predicate asserting that the root
rule of the proof tree is conjunction-right applied to the formula
A /\ B in the succedent, with A and B as the given arguments. The
requested contexts are compared with the rule constructor's indexed
prefix and suffix around that principal occurrence. -/
@[blueprint "chap6__lemma_6_3_2"]
def rootIsConjRight {L : Language} {hL : L.hasEquality = true} {s : Sequent L}
    (T : GEqProofTree hL s) (A B : FormulaN L)
    (Γ Δ Λ : List (FormulaN L)) : Prop :=
  match T with
  | .base (.twoPremise (.conjRight Γ' Δ' Λ' A' B') _ _) =>
    Γ' = Γ ∧ Δ' = Δ ∧ Λ' = Λ ∧ A' = A ∧ B' = B
  | .twoPremise (.conjRight Γ' Δ' Λ' A' B') _ _ =>
    Γ' = Γ ∧ Δ' = Δ ∧ Λ' = Λ ∧ A' = A ∧ B' = B
  | _ => False

-- ===================================================================
-- Lemma 6.3.2 (required def): rootIsImplLeft
-- ===================================================================

/-- Lemma 6.3.2 (required def): Predicate asserting that the root
rule of the proof tree is implication-left applied to the formula
A implies B in the antecedent, with A and B as the given arguments.
The requested contexts are compared with the rule constructor's indexed
prefix and suffix around that principal occurrence. -/
@[blueprint "chap6__lemma_6_3_2"]
def rootIsImplLeft {L : Language} {hL : L.hasEquality = true} {s : Sequent L}
    (T : GEqProofTree hL s) (A B : FormulaN L)
    (Γ Δ Λ : List (FormulaN L)) : Prop :=
  match T with
  | .base (.twoPremise (.implLeft Γ' Δ' Λ' A' B') _ _) =>
    Γ' = Γ ∧ Δ' = Δ ∧ Λ' = Λ ∧ A' = A ∧ B' = B
  | .twoPremise (.implLeft Γ' Δ' Λ' A' B') _ _ =>
    Γ' = Γ ∧ Δ' = Δ ∧ Λ' = Λ ∧ A' = A ∧ B' = B
  | _ => False

-- Regression probes for the exact-principal and arbitrary-context behavior.
-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} {hL : L.hasEquality = true}
    (X Y U V : FormulaN L) (hXU : X ≠ U) :
    let T : GEqProofTree hL
        (Sequent.mk [X, Y]
          [FormulaN.conj X Y, FormulaN.conj U V]) :=
      .twoPremise
        (.conjRight [X, Y] [] [FormulaN.conj U V] X Y)
        (.axiom_ (Sequent.mk [X, Y] [X, FormulaN.conj U V])
          ⟨X, by simp, by simp⟩)
        (.axiom_ (Sequent.mk [X, Y] [Y, FormulaN.conj U V])
          ⟨Y, by simp, by simp⟩)
    ¬ rootIsConjRight T U V [X, Y] [] [FormulaN.conj U V] := by
  change ¬
    ([X, Y] = [X, Y] ∧
      ([] : List (FormulaN L)) = [] ∧
      [FormulaN.conj U V] = [FormulaN.conj U V] ∧
      X = U ∧ Y = V)
  exact fun h => hXU h.2.2.2.1

-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} {hL : L.hasEquality = true}
    (A B P Q : FormulaN L) :
    let T : GEqProofTree hL
        (Sequent.mk [A, B] [P, FormulaN.conj A B, Q]) :=
      .twoPremise
        (.conjRight [A, B] [P] [Q] A B)
        (.axiom_ (Sequent.mk [A, B] [P, A, Q])
          ⟨A, by simp, by simp⟩)
        (.axiom_ (Sequent.mk [A, B] [P, B, Q])
          ⟨B, by simp, by simp⟩)
    rootIsConjRight T A B [A, B] [P] [Q] := by
  change
    [A, B] = [A, B] ∧ [P] = [P] ∧ [Q] = [Q] ∧
      A = A ∧ B = B
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} {hL : L.hasEquality = true}
    (A B : FormulaN L) :
    let T : GEqProofTree hL
        (Sequent.mk [A, FormulaN.impl A B, B] [B]) :=
      .twoPremise
        (.implLeft [A] [B] [B] A B)
        (.axiom_ (Sequent.mk [A, B] [A, B])
          ⟨A, by simp, by simp⟩)
        (.axiom_ (Sequent.mk [B, A, B] [B])
          ⟨B, by simp, by simp⟩)
    rootIsImplLeft T A B [A] [B] [B] := by
  change
    [A] = [A] ∧ [B] = [B] ∧ [B] = [B] ∧
      A = A ∧ B = B
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- Duplicate conjunctions do not make a root action at the first occurrence
-- certify the same-valued second occurrence, for either G= root shape.
-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} {hL : L.hasEquality = true}
    (A B : FormulaN L) :
    let C := FormulaN.conj A B
    let direct : GEqProofTree hL (Sequent.mk [A, B] [C, C]) :=
      .twoPremise
        (.conjRight [A, B] [] [C] A B)
        (.axiom_ (Sequent.mk [A, B] [A, C])
          ⟨A, by simp, by simp⟩)
        (.axiom_ (Sequent.mk [A, B] [B, C])
          ⟨B, by simp, by simp⟩)
    let embedded : GEqProofTree hL (Sequent.mk [A, B] [C, C]) :=
      .base (.twoPremise
        (.conjRight [A, B] [] [C] A B)
        (.axiom_ (Sequent.mk [A, B] [A, C])
          ⟨A, by simp, by simp⟩)
        (.axiom_ (Sequent.mk [A, B] [B, C])
          ⟨B, by simp, by simp⟩))
    ¬ rootIsConjRight direct A B [A, B] [C] [] ∧
      ¬ rootIsConjRight embedded A B [A, B] [C] [] := by
  constructor
  · change ¬
      ([A, B] = [A, B] ∧
        ([] : List (FormulaN L)) = [FormulaN.conj A B] ∧
        [FormulaN.conj A B] = [] ∧ A = A ∧ B = B)
    simp
  · change ¬
      ([A, B] = [A, B] ∧
        ([] : List (FormulaN L)) = [FormulaN.conj A B] ∧
        [FormulaN.conj A B] = [] ∧ A = A ∧ B = B)
    simp

-- Duplicate implications likewise retain the selected antecedent split for
-- both direct and embedded G roots.
-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} {hL : L.hasEquality = true}
    (A B : FormulaN L) :
    let C := FormulaN.impl A B
    let direct : GEqProofTree hL (Sequent.mk [C, C, B] [B]) :=
      .twoPremise
        (.implLeft [] [C, B] [B] A B)
        (.axiom_ (Sequent.mk [C, B] [A, B])
          ⟨B, by simp, by simp⟩)
        (.axiom_ (Sequent.mk [B, C, B] [B])
          ⟨B, by simp, by simp⟩)
    let embedded : GEqProofTree hL (Sequent.mk [C, C, B] [B]) :=
      .base (.twoPremise
        (.implLeft [] [C, B] [B] A B)
        (.axiom_ (Sequent.mk [C, B] [A, B])
          ⟨B, by simp, by simp⟩)
        (.axiom_ (Sequent.mk [B, C, B] [B])
          ⟨B, by simp, by simp⟩))
    ¬ rootIsImplLeft direct A B [C] [B] [B] ∧
      ¬ rootIsImplLeft embedded A B [C] [B] [B] := by
  constructor
  · change ¬
      (([] : List (FormulaN L)) = [FormulaN.impl A B] ∧
        [FormulaN.impl A B, B] = [B] ∧ [B] = [B] ∧
        A = A ∧ B = B)
    simp
  · change ¬
      (([] : List (FormulaN L)) = [FormulaN.impl A B] ∧
        [FormulaN.impl A B, B] = [B] ∧ [B] = [B] ∧
        A = A ∧ B = B)
    simp

-- ===================================================================
-- Lemma 6.3.2 (helper): direct G= conjRight permutation
-- ===================================================================

-- retained: used by LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
theorem geqConjRight_markedSplit
    (L : Language)
    : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → X ≠ Y → (∃ (K : List
      (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ ∃ (K : List (FormulaN L)), P = R ++ [Y] ++ K ∧ S
      = K ++ [X] ++ Q := by
  intro P Q R S X Y heq hne
  have h' : P ++ (X :: Q) = R ++ (Y :: S) := by
    simpa [List.append_assoc] using heq
  rcases List.append_eq_append_iff.mp h' with
    ⟨K, hR, htail⟩ | ⟨K, hP, htail⟩
  · cases K with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at htail
      exact (hne htail.1).elim
    | cons Z K =>
      simp only [List.cons_append, List.cons.injEq] at htail
      rcases htail with ⟨hXZ, hQ⟩
      subst Z
      exact Or.inl ⟨K, by simpa [List.append_assoc] using hR, by simpa [List.append_assoc] using hQ⟩
  · cases K with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at htail
      exact (hne htail.1.symm).elim
    | cons Z K =>
      simp only [List.cons_append, List.cons.injEq] at htail
      rcases htail with ⟨hYZ, hS⟩
      subst Z
      exact Or.inr ⟨K, by simpa [List.append_assoc] using hP, by simpa [List.append_assoc] using hS⟩

-- retained: used by LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
theorem geqConjRight_markedSplit3
    (L : Language)
    : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → (∃ (K : List
      (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ P = R ∧ X = Y ∧ Q = S ∨ ∃ (K : List (FormulaN
      L)), P = R ++ [Y] ++ K ∧ S = K ++ [X] ++ Q := by
  intro P Q R S X Y heq
  have h' : P ++ (X :: Q) = R ++ (Y :: S) := by
    simpa [List.append_assoc] using heq
  rcases List.append_eq_append_iff.mp h' with
    ⟨K, hR, htail⟩ | ⟨K, hP, htail⟩
  · cases K with
    | nil =>
      simp only [List.append_nil, List.nil_append, List.cons.injEq] at hR htail
      exact Or.inr (Or.inl ⟨hR.symm, htail.1, htail.2⟩)
    | cons Z K =>
      simp only [List.cons_append, List.cons.injEq] at htail
      rcases htail with ⟨hXZ, hQ⟩
      subst Z
      exact Or.inl ⟨K, by simpa [List.append_assoc] using hR, by simpa [List.append_assoc] using hQ⟩
  · cases K with
    | nil =>
      simp only [List.append_nil, List.nil_append, List.cons.injEq] at hP htail
      exact Or.inr (Or.inl ⟨hP, htail.1.symm, htail.2.symm⟩)
    | cons Z K =>
      simp only [List.cons_append, List.cons.injEq] at htail
      rcases htail with ⟨hYZ, hS⟩
      subst Z
      exact Or.inr (Or.inr ⟨K, by simpa [List.append_assoc] using hP, by simpa [List.append_assoc] using hS⟩)

-- retained: used by LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
theorem geqConjRight_replaceConjFresh
    (L : Language)
    : ∀ (y : Nat) (ant D S : List (FormulaN L)) (C X : FormulaN L), formulaFVN X ⊆ formulaFVN C → (∀ (F :
      FormulaN L), F ∈ ant ++ (D ++ [C] ++ S) → ¬y ∈ formulaFVN F) → ∀ (F : FormulaN L), F ∈ ant ++ (D ++ [X]
      ++ S) → ¬y ∈ formulaFVN F := by
  intro y ant D S C X hsubset hfresh F hmem
  have hmem' : F ∈ ant ∨ (F ∈ D ∨ F = X) ∨ F ∈ S := by
    simpa only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] using hmem
  rcases hmem' with hF | (hF | hF) | hF
  · exact hfresh F (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inl hF)
  · exact hfresh F (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr (Or.inl (Or.inl hF)))
  · subst F
    intro hy
    exact hfresh C (by simp) (hsubset y hy)
  · exact hfresh F (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr (Or.inr hF))

-- retained: used by LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
theorem geqConjRight_geqDepth_transport
    (L : Language) (hL : L.hasEquality = true)
    : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p := by
  intro s₁ s₂ heq p
  cases heq
  rfl

-- retained: used by LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
theorem geqConjRight_geqLeaf_transport
    (L : Language) (hL : L.hasEquality = true)
    : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), geqLeafSequents (heq ▸ p) =
      geqLeafSequents p := by
  intro s₁ s₂ heq p
  cases heq
  rfl

-- retained: used by LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
theorem geqConjRight_geqLeafProperty_transport
    (L : Language) (hL : L.hasEquality = true) (geqLeaf_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p :
      GEqProofTree hL s₁), geqLeafSequents (heq ▸ p) = geqLeafSequents p)
    : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s') → ∀ (s' : Sequent L), s' ∈ geqLeafSequents (heq ▸ p) →
      seqAllAtomicOrQuantified s' := by
  intro s₁ s₂ heq p hp
  rw [geqLeaf_transport heq p]
  exact hp

-- retained: used by LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
theorem geqConjRight_base
    (L : Language) (hL : L.hasEquality = true) (n : Nat) (s : Sequent L) (A B : FormulaN L) (Γ Δ Λ : List
      (FormulaN L)) (hseq : s = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ))) (permOne : ∀ {prem conc : Sequent L}
      (rule : GentzenStep1Ext prem conc) (sub : GEqProofTree hL prem), geqDepth sub < n → conc = (Sequent.mk
      (Γ) (Δ ++ [A.conj B] ++ Λ)) → (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified
      s') → ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ)
      (Δ ++ [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s') (permTwo : ∀ {prem1 prem2 conc : Sequent L} (rule : GentzenStep2Ext prem1
      prem2 conc) (sub1 : GEqProofTree hL prem1) (sub2 : GEqProofTree hL prem2), geqDepth sub1 < n → geqDepth
      sub2 < n → conc = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ)) → (∀ (s' : Sequent L), s' ∈ geqLeafSequents
      sub1 → seqAllAtomicOrQuantified s') → (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub2 →
      seqAllAtomicOrQuantified s') → ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 :
      GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + max
      (geqDepth sub1) (geqDepth sub2) ∧ (∀ (s' : Sequent L), s' ∈ geqLeafSequents p1 →
      seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 → seqAllAtomicOrQuantified
      s') (g : GProofTreeExt s) (hdepth : geqDepth (GEqProofTree.base (hL := hL) g) = n) (hleaf : ∀ (s' :
      Sequent L), s' ∈ geqLeafSequents (GEqProofTree.base (hL := hL) g) → seqAllAtomicOrQuantified s')
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth (GEqProofTree.base (hL := hL) g) ∧ (∀ (s' :
      Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  cases g with
  | axiom_ s hAx =>
    have hall := hleaf s (by
      simp [geqLeafSequents, gProofTreeLeafSequents])
    have hbad : isAtomicOrQuantified (FormulaN.conj A B) := by
      exact hall.2 (FormulaN.conj A B) (by
        rw [hseq]
        simp)
    simpa [isAtomicOrQuantified, FormulaN.isAtomic, isQuantified] using hbad
  | onePremise rule sub =>
    exact permOne rule (.base sub) (by
      simp only [geqDepth, gProofTreeDepth] at hdepth ⊢
      omega) hseq (by
        intro s' hs'
        exact hleaf s' (by
          simpa [geqLeafSequents, gProofTreeLeafSequents] using hs'))
  | twoPremise rule sub1 sub2 =>
    exact permTwo rule (.base sub1) (.base sub2) (by
      simp only [geqDepth, gProofTreeDepth] at hdepth ⊢
      omega) (by
        simp only [geqDepth, gProofTreeDepth] at hdepth ⊢
        omega) hseq (by
          intro s' hs'
          exact hleaf s' (by
            simp only [geqLeafSequents, gProofTreeLeafSequents, List.mem_append]
            exact Or.inl hs')) (by
          intro s' hs'
          exact hleaf s' (by
            simp only [geqLeafSequents, gProofTreeLeafSequents, List.mem_append]
            exact Or.inr hs'))

-- retained: used by LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
theorem geqConjRight_axiom_
    (L : Language) (hL : L.hasEquality = true) (s : Sequent L) (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L))
      (hseq : s = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ))) (hAx : isAxiom s) (hleaf : ∀ (s' : Sequent L), s' ∈
      geqLeafSequents (GEqProofTree.axiom_ (hL := hL) s hAx) → seqAllAtomicOrQuantified s')
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth (GEqProofTree.axiom_ (hL := hL) s hAx) ∧ (∀
      (s' : Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  have hall := hleaf s (by simp [geqLeafSequents])
  have hbad : isAtomicOrQuantified (FormulaN.conj A B) := by
    exact hall.2 (FormulaN.conj A B) (by
      rw [hseq]
      simp)
  simpa [isAtomicOrQuantified, FormulaN.isAtomic, isQuantified] using hbad

-- retained: used by LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
theorem geqConjRight_onePremise
    (L : Language) (hL : L.hasEquality = true) (n : Nat) (s : Sequent L) (A B : FormulaN L) (Γ Δ Λ : List
      (FormulaN L)) (hseq : s = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ))) (permOne : ∀ {prem conc : Sequent L}
      (rule : GentzenStep1Ext prem conc) (sub : GEqProofTree hL prem), geqDepth sub < n → conc = (Sequent.mk
      (Γ) (Δ ++ [A.conj B] ++ Λ)) → (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified
      s') → ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ)
      (Δ ++ [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s') (prem : Sequent L) (sub : GEqProofTree hL prem) (rule : GentzenStep1Ext
      prem s) (hdepth : geqDepth (GEqProofTree.onePremise rule sub) = n) (hleaf : ∀ (s' : Sequent L), s' ∈
      geqLeafSequents (GEqProofTree.onePremise rule sub) → seqAllAtomicOrQuantified s')
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth (GEqProofTree.onePremise rule sub) ∧ (∀ (s'
      : Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  exact permOne rule sub (by
    simp only [geqDepth] at hdepth
    omega) hseq (by
      simpa [geqLeafSequents] using hleaf)

-- retained: used by LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
theorem geqConjRight_twoPremise
    (L : Language) (hL : L.hasEquality = true) (n : Nat) (s : Sequent L) (A B : FormulaN L) (Γ Δ Λ : List
      (FormulaN L)) (hseq : s = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ))) (permTwo : ∀ {prem1 prem2 conc :
      Sequent L} (rule : GentzenStep2Ext prem1 prem2 conc) (sub1 : GEqProofTree hL prem1) (sub2 : GEqProofTree
      hL prem2), geqDepth sub1 < n → geqDepth sub2 < n → conc = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ)) → (∀
      (s' : Sequent L), s' ∈ geqLeafSequents sub1 → seqAllAtomicOrQuantified s') → (∀ (s' : Sequent L), s' ∈
      geqLeafSequents sub2 → seqAllAtomicOrQuantified s') → ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A]
      ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2)
      = 1 + max (geqDepth sub1) (geqDepth sub2) ∧ (∀ (s' : Sequent L), s' ∈ geqLeafSequents p1 →
      seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 → seqAllAtomicOrQuantified
      s') (prem1 prem2 : Sequent L) (sub1 : GEqProofTree hL prem1) (sub2 : GEqProofTree hL prem2) (rule :
      GentzenStep2Ext prem1 prem2 s) (hdepth : geqDepth (GEqProofTree.twoPremise rule sub1 sub2) = n) (hleaf :
      ∀ (s' : Sequent L), s' ∈ geqLeafSequents (GEqProofTree.twoPremise rule sub1 sub2) →
      seqAllAtomicOrQuantified s')
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth (GEqProofTree.twoPremise rule sub1 sub2) ∧
      (∀ (s' : Sequent L), s' ∈ geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p2 → seqAllAtomicOrQuantified s' := by
  exact permTwo rule sub1 sub2 (by
    simp only [geqDepth] at hdepth
    omega) (by
      simp only [geqDepth] at hdepth
      omega) hseq (by
        intro s' hs'
        exact hleaf s' (by
          simp only [geqLeafSequents, List.mem_append]
          exact Or.inl hs')) (by
        intro s' hs'
        exact hleaf s' (by
          simp only [geqLeafSequents, List.mem_append]
          exact Or.inr hs'))

end LCS.CutElim.LKe.Equivalence
end

section
namespace LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality.Completeness
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.CompletenessBridge
section
-- ATTACH-BLOCKER: variable
variable
    (L : Language) (hL : L.hasEquality = true) (n : Nat) (ih : ∀ (m : Nat), m < n → ∀ {s : Sequent L} (T :
      GEqProofTree hL s), geqDepth T = m → ∀ (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)), s = (Sequent.mk
      (Γ) (Δ ++ [A.conj B] ++ Λ)) → (∀ (s' : Sequent L), s' ∈ geqLeafSequents T → seqAllAtomicOrQuantified s')
      → ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ
      ++ [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = geqDepth T ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s')
-- ATTACH-BLOCKER: unknown command Lean.Parser.Command.include
include ih

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqConjRight_conjLeft
    (A B : FormulaN L) (Γ Δ Λ Γr Δr succ : List (FormulaN L)) (X Y : FormulaN L) (sub : GEqProofTree hL
      (Sequent.mk (Γr ++ [X, Y] ++ Δr) (succ))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L),
      s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified s') (hconc : (Sequent.mk (Γr ++ [X.conj Y] ++ Δr)
      (succ)) = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γ
  subst succ
  obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B
      (Γr ++ [X, Y] ++ Δr) Δ Λ rfl hsubleaf
  refine ⟨.onePremise (.conjLeft Γr Δr (Δ ++ [A] ++ Λ) X Y) q1, .onePremise
      (.conjLeft Γr Δr (Δ ++ [B] ++ Λ) X Y) q2, by
    simp only [geqDepth]
    omega, ?_, ?_⟩
  · simpa [geqLeafSequents] using hq1leaf
  · simpa [geqLeafSequents] using hq2leaf

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqConjRight_disjRight
    (markedSplit : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → X ≠ Y →
      (∃ (K : List (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ ∃ (K : List (FormulaN L)), P = R ++
      [Y] ++ K ∧ S = K ++ [X] ++ Q) (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p :
      GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p) (geqLeafProperty_transport : ∀ {s₁ s₂ : Sequent L}
      (heq : s₁ = s₂) (p : GEqProofTree hL s₁), (∀ (s' : Sequent L), s' ∈ geqLeafSequents p →
      seqAllAtomicOrQuantified s') → ∀ (s' : Sequent L), s' ∈ geqLeafSequents (heq ▸ p) →
      seqAllAtomicOrQuantified s') (A B : FormulaN L) (Γ Δ Λ Γr Δr Λr : List (FormulaN L)) (X Y : FormulaN L)
      (sub : GEqProofTree hL (Sequent.mk (Γr) (Δr ++ [X, Y] ++ Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf
      : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified s') (hconc : (Sequent.mk (Γr)
      (Δr ++ [X.disj Y] ++ Λr)) = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γ
  rcases markedSplit hsuc (by simp) with
    ⟨K, hΔ, hΛr⟩ | ⟨K, hΔr, hΛ⟩
  · subst Δ
    subst Λr
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B Γr (Δr ++ [X, Y] ++ K) Λ
        (by simp [List.append_assoc]) hsubleaf
    have hin1 : Sequent.mk Γr ((Δr ++ [X, Y] ++ K) ++ [A] ++ Λ) = Sequent.mk Γr
            (Δr ++ [X, Y] ++ (K ++ [A] ++ Λ)) := by
      simp [List.append_assoc]
    have hin2 : Sequent.mk Γr ((Δr ++ [X, Y] ++ K) ++ [B] ++ Λ) = Sequent.mk Γr
            (Δr ++ [X, Y] ++ (K ++ [B] ++ Λ)) := by
      simp [List.append_assoc]
    let q1' := hin1 ▸ q1
    let q2' := hin2 ▸ q2
    have hdq1 : geqDepth q1' = geqDepth q1 := geqDepth_transport hin1 q1
    have hdq2 : geqDepth q2' = geqDepth q2 := geqDepth_transport hin2 q2
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.disjRight Γr Δr (K ++ [A] ++ Λ) X Y) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.disjRight Γr Δr (K ++ [B] ++ Λ) X Y) q2'
    have hout1 : Sequent.mk Γr (Δr ++ [FormulaN.disj X Y] ++ (K ++ [A] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.disj X Y] ++ K) ++ [A] ++ Λ) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr (Δr ++ [FormulaN.disj X Y] ++ (K ++ [B] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.disj X Y] ++ K) ++ [B] ++ Λ) := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hdp1 : geqDepth p1 = 1 + geqDepth q1 := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hdp2 : geqDepth p2 = 1 + geqDepth q2 := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · exact geqLeafProperty_transport hout1 r1 (by
        simpa [r1, q1', geqLeafSequents] using (geqLeafProperty_transport hin1 q1 hq1leaf))
    · exact geqLeafProperty_transport hout2 r2 (by
        simpa [r2, q2', geqLeafSequents] using (geqLeafProperty_transport hin2 q2 hq2leaf))
  · subst Δr
    subst Λ
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B Γr Δ (K ++ [X, Y] ++ Λr)
        (by simp [List.append_assoc]) hsubleaf
    have hin1 : Sequent.mk Γr (Δ ++ [A] ++ (K ++ [X, Y] ++ Λr)) = Sequent.mk Γr
            ((Δ ++ [A] ++ K) ++ [X, Y] ++ Λr) := by
      simp [List.append_assoc]
    have hin2 : Sequent.mk Γr (Δ ++ [B] ++ (K ++ [X, Y] ++ Λr)) = Sequent.mk Γr
            ((Δ ++ [B] ++ K) ++ [X, Y] ++ Λr) := by
      simp [List.append_assoc]
    let q1' := hin1 ▸ q1
    let q2' := hin2 ▸ q2
    have hdq1 : geqDepth q1' = geqDepth q1 := geqDepth_transport hin1 q1
    have hdq2 : geqDepth q2' = geqDepth q2 := geqDepth_transport hin2 q2
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.disjRight Γr (Δ ++ [A] ++ K) Λr X Y) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.disjRight Γr (Δ ++ [B] ++ K) Λr X Y) q2'
    have hout1 : Sequent.mk Γr ((Δ ++ [A] ++ K) ++ [FormulaN.disj X Y] ++ Λr) = Sequent.mk Γr (Δ ++ [A] ++
              (K ++ [FormulaN.disj X Y] ++ Λr)) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr ((Δ ++ [B] ++ K) ++ [FormulaN.disj X Y] ++ Λr) = Sequent.mk Γr (Δ ++ [B] ++
              (K ++ [FormulaN.disj X Y] ++ Λr)) := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hdp1 : geqDepth p1 = 1 + geqDepth q1 := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hdp2 : geqDepth p2 = 1 + geqDepth q2 := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · exact geqLeafProperty_transport hout1 r1 (by
        simpa [r1, q1', geqLeafSequents] using (geqLeafProperty_transport hin1 q1 hq1leaf))
    · exact geqLeafProperty_transport hout2 r2 (by
        simpa [r2, q2', geqLeafSequents] using (geqLeafProperty_transport hin2 q2 hq2leaf))

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqConjRight_implRight
    (markedSplit : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → X ≠ Y →
      (∃ (K : List (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ ∃ (K : List (FormulaN L)), P = R ++
      [Y] ++ K ∧ S = K ++ [X] ++ Q) (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p :
      GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p) (geqLeafProperty_transport : ∀ {s₁ s₂ : Sequent L}
      (heq : s₁ = s₂) (p : GEqProofTree hL s₁), (∀ (s' : Sequent L), s' ∈ geqLeafSequents p →
      seqAllAtomicOrQuantified s') → ∀ (s' : Sequent L), s' ∈ geqLeafSequents (heq ▸ p) →
      seqAllAtomicOrQuantified s') (A B : FormulaN L) (Γ Δ Λ Γr Δr Λr : List (FormulaN L)) (X Y : FormulaN L)
      (sub : GEqProofTree hL (Sequent.mk ([X] ++ Γr) ([Y] ++ Δr ++ Λr))) (hsubdepth : geqDepth sub < n)
      (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified s') (hconc :
      (Sequent.mk (Γr) (Δr ++ [X.impl Y] ++ Λr)) = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γ
  rcases markedSplit hsuc (by simp) with
    ⟨K, hΔ, hΛr⟩ | ⟨K, hΔr, hΛ⟩
  · subst Δ
    subst Λr
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B
        ([X] ++ Γr) ([Y] ++ Δr ++ K) Λ
        (by simp [List.append_assoc]) hsubleaf
    have hin1 : Sequent.mk ([X] ++ Γr) (([Y] ++ Δr ++ K) ++ [A] ++ Λ) = Sequent.mk ([X] ++ Γr)
            ([Y] ++ Δr ++ (K ++ [A] ++ Λ)) := by
      simp [List.append_assoc]
    have hin2 : Sequent.mk ([X] ++ Γr) (([Y] ++ Δr ++ K) ++ [B] ++ Λ) = Sequent.mk ([X] ++ Γr)
            ([Y] ++ Δr ++ (K ++ [B] ++ Λ)) := by
      simp [List.append_assoc]
    let q1' := hin1 ▸ q1
    let q2' := hin2 ▸ q2
    have hdq1 : geqDepth q1' = geqDepth q1 := geqDepth_transport hin1 q1
    have hdq2 : geqDepth q2' = geqDepth q2 := geqDepth_transport hin2 q2
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.implRight Γr Δr (K ++ [A] ++ Λ) X Y) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.implRight Γr Δr (K ++ [B] ++ Λ) X Y) q2'
    have hout1 : Sequent.mk Γr (Δr ++ [FormulaN.impl X Y] ++ (K ++ [A] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.impl X Y] ++ K) ++ [A] ++ Λ) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr (Δr ++ [FormulaN.impl X Y] ++ (K ++ [B] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.impl X Y] ++ K) ++ [B] ++ Λ) := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hdp1 : geqDepth p1 = 1 + geqDepth q1 := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hdp2 : geqDepth p2 = 1 + geqDepth q2 := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · exact geqLeafProperty_transport hout1 r1 (by
        simpa [r1, q1', geqLeafSequents] using (geqLeafProperty_transport hin1 q1 hq1leaf))
    · exact geqLeafProperty_transport hout2 r2 (by
        simpa [r2, q2', geqLeafSequents] using (geqLeafProperty_transport hin2 q2 hq2leaf))
  · subst Δr
    subst Λ
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B
        ([X] ++ Γr) ([Y] ++ Δ) (K ++ Λr)
        (by simp [List.append_assoc]) hsubleaf
    have hin1 : Sequent.mk ([X] ++ Γr) (([Y] ++ Δ) ++ [A] ++ (K ++ Λr)) = Sequent.mk ([X] ++ Γr)
            ([Y] ++ (Δ ++ [A] ++ K) ++ Λr) := by
      simp [List.append_assoc]
    have hin2 : Sequent.mk ([X] ++ Γr) (([Y] ++ Δ) ++ [B] ++ (K ++ Λr)) = Sequent.mk ([X] ++ Γr)
            ([Y] ++ (Δ ++ [B] ++ K) ++ Λr) := by
      simp [List.append_assoc]
    let q1' := hin1 ▸ q1
    let q2' := hin2 ▸ q2
    have hdq1 : geqDepth q1' = geqDepth q1 := geqDepth_transport hin1 q1
    have hdq2 : geqDepth q2' = geqDepth q2 := geqDepth_transport hin2 q2
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.implRight Γr (Δ ++ [A] ++ K) Λr X Y) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.implRight Γr (Δ ++ [B] ++ K) Λr X Y) q2'
    have hout1 : Sequent.mk Γr ((Δ ++ [A] ++ K) ++ [FormulaN.impl X Y] ++ Λr) = Sequent.mk Γr (Δ ++ [A] ++
              (K ++ [FormulaN.impl X Y] ++ Λr)) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr ((Δ ++ [B] ++ K) ++ [FormulaN.impl X Y] ++ Λr) = Sequent.mk Γr (Δ ++ [B] ++
              (K ++ [FormulaN.impl X Y] ++ Λr)) := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hdp1 : geqDepth p1 = 1 + geqDepth q1 := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hdp2 : geqDepth p2 = 1 + geqDepth q2 := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · exact geqLeafProperty_transport hout1 r1 (by
        simpa [r1, q1', geqLeafSequents] using (geqLeafProperty_transport hin1 q1 hq1leaf))
    · exact geqLeafProperty_transport hout2 r2 (by
        simpa [r2, q2', geqLeafSequents] using (geqLeafProperty_transport hin2 q2 hq2leaf))

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqConjRight_negLeft
    (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), geqDepth (heq ▸ p) =
      geqDepth p) (geqLeafProperty_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁),
      (∀ (s' : Sequent L), s' ∈ geqLeafSequents p → seqAllAtomicOrQuantified s') → ∀ (s' : Sequent L), s' ∈
      geqLeafSequents (heq ▸ p) → seqAllAtomicOrQuantified s') (A B : FormulaN L) (Γ Δ Λ Γr Δr succ : List
      (FormulaN L)) (X : FormulaN L) (sub : GEqProofTree hL (Sequent.mk (Γr ++ Δr) ([X] ++ succ))) (hsubdepth
      : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified
      s') (hconc : (Sequent.mk (Γr ++ [X.neg] ++ Δr) (succ)) = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γ
  subst succ
  obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B (Γr ++ Δr) ([X] ++ Δ) Λ
      (by simp [List.append_assoc]) hsubleaf
  have heq1 : Sequent.mk (Γr ++ Δr) (([X] ++ Δ) ++ [A] ++ Λ) =
        Sequent.mk (Γr ++ Δr) ([X] ++ (Δ ++ [A] ++ Λ)) := by
    simp [List.append_assoc]
  have heq2 : Sequent.mk (Γr ++ Δr) (([X] ++ Δ) ++ [B] ++ Λ) =
        Sequent.mk (Γr ++ Δr) ([X] ++ (Δ ++ [B] ++ Λ)) := by
    simp [List.append_assoc]
  let q1' := heq1 ▸ q1
  let q2' := heq2 ▸ q2
  have hdq1 : geqDepth q1' = geqDepth q1 := by
    exact geqDepth_transport heq1 q1
  have hdq2 : geqDepth q2' = geqDepth q2 := by
    exact geqDepth_transport heq2 q2
  refine ⟨.onePremise (.negLeft Γr Δr (Δ ++ [A] ++ Λ) X) q1', .onePremise
      (.negLeft Γr Δr (Δ ++ [B] ++ Λ) X) q2', by
    simp only [geqDepth]
    omega, ?_, ?_⟩
  · simpa [geqLeafSequents] using (geqLeafProperty_transport heq1 q1 hq1leaf)
  · simpa [geqLeafSequents] using (geqLeafProperty_transport heq2 q2 hq2leaf)

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqConjRight_negRight
    (markedSplit : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → X ≠ Y →
      (∃ (K : List (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ ∃ (K : List (FormulaN L)), P = R ++
      [Y] ++ K ∧ S = K ++ [X] ++ Q) (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p :
      GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p) (geqLeafProperty_transport : ∀ {s₁ s₂ : Sequent L}
      (heq : s₁ = s₂) (p : GEqProofTree hL s₁), (∀ (s' : Sequent L), s' ∈ geqLeafSequents p →
      seqAllAtomicOrQuantified s') → ∀ (s' : Sequent L), s' ∈ geqLeafSequents (heq ▸ p) →
      seqAllAtomicOrQuantified s') (A B : FormulaN L) (Γ Δ Λ Γr Δr Λr : List (FormulaN L)) (X : FormulaN L)
      (sub : GEqProofTree hL (Sequent.mk ([X] ++ Γr) (Δr ++ Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀
      (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified s') (hconc : (Sequent.mk (Γr) (Δr
      ++ [X.neg] ++ Λr)) = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γ
  rcases markedSplit hsuc (by simp) with
    ⟨K, hΔ, hΛr⟩ | ⟨K, hΔr, hΛ⟩
  · subst Δ
    subst Λr
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B ([X] ++ Γr) (Δr ++ K) Λ
        (by simp [List.append_assoc]) hsubleaf
    have hin1 : Sequent.mk ([X] ++ Γr) ((Δr ++ K) ++ [A] ++ Λ) = Sequent.mk ([X] ++ Γr)
            (Δr ++ (K ++ [A] ++ Λ)) := by
      simp [List.append_assoc]
    have hin2 : Sequent.mk ([X] ++ Γr) ((Δr ++ K) ++ [B] ++ Λ) = Sequent.mk ([X] ++ Γr)
            (Δr ++ (K ++ [B] ++ Λ)) := by
      simp [List.append_assoc]
    let q1' := hin1 ▸ q1
    let q2' := hin2 ▸ q2
    have hdq1 : geqDepth q1' = geqDepth q1 := geqDepth_transport hin1 q1
    have hdq2 : geqDepth q2' = geqDepth q2 := geqDepth_transport hin2 q2
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.negRight Γr Δr (K ++ [A] ++ Λ) X) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.negRight Γr Δr (K ++ [B] ++ Λ) X) q2'
    have hout1 : Sequent.mk Γr (Δr ++ [FormulaN.neg X] ++ (K ++ [A] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.neg X] ++ K) ++ [A] ++ Λ) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr (Δr ++ [FormulaN.neg X] ++ (K ++ [B] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.neg X] ++ K) ++ [B] ++ Λ) := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hdp1 : geqDepth p1 = 1 + geqDepth q1 := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hdp2 : geqDepth p2 = 1 + geqDepth q2 := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · exact geqLeafProperty_transport hout1 r1 (by
        simpa [r1, q1', geqLeafSequents] using (geqLeafProperty_transport hin1 q1 hq1leaf))
    · exact geqLeafProperty_transport hout2 r2 (by
        simpa [r2, q2', geqLeafSequents] using (geqLeafProperty_transport hin2 q2 hq2leaf))
  · subst Δr
    subst Λ
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B ([X] ++ Γr) Δ (K ++ Λr)
        (by simp [List.append_assoc]) hsubleaf
    have hin1 : Sequent.mk ([X] ++ Γr) (Δ ++ [A] ++ (K ++ Λr)) = Sequent.mk ([X] ++ Γr)
            ((Δ ++ [A] ++ K) ++ Λr) := by
      simp [List.append_assoc]
    have hin2 : Sequent.mk ([X] ++ Γr) (Δ ++ [B] ++ (K ++ Λr)) = Sequent.mk ([X] ++ Γr)
            ((Δ ++ [B] ++ K) ++ Λr) := by
      simp [List.append_assoc]
    let q1' := hin1 ▸ q1
    let q2' := hin2 ▸ q2
    have hdq1 : geqDepth q1' = geqDepth q1 := geqDepth_transport hin1 q1
    have hdq2 : geqDepth q2' = geqDepth q2 := geqDepth_transport hin2 q2
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.negRight Γr (Δ ++ [A] ++ K) Λr X) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.negRight Γr (Δ ++ [B] ++ K) Λr X) q2'
    have hout1 : Sequent.mk Γr ((Δ ++ [A] ++ K) ++ [FormulaN.neg X] ++ Λr) = Sequent.mk Γr
            (Δ ++ [A] ++ (K ++ [FormulaN.neg X] ++ Λr)) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr ((Δ ++ [B] ++ K) ++ [FormulaN.neg X] ++ Λr) = Sequent.mk Γr
            (Δ ++ [B] ++ (K ++ [FormulaN.neg X] ++ Λr)) := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hdp1 : geqDepth p1 = 1 + geqDepth q1 := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hdp2 : geqDepth p2 = 1 + geqDepth q2 := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · exact geqLeafProperty_transport hout1 r1 (by
        simpa [r1, q1', geqLeafSequents] using (geqLeafProperty_transport hin1 q1 hq1leaf))
    · exact geqLeafProperty_transport hout2 r2 (by
        simpa [r2, q2', geqLeafSequents] using (geqLeafProperty_transport hin2 q2 hq2leaf))

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqConjRight_allLeft
    (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)) (ts : List (Term L)) (Γr Δr succ : List (FormulaN L)) (x :
      Nat) (X : FormulaN L) (hne : ts ≠ []) (hfree : ∀ (t : Term L), t ∈ ts → isFreeForN t x X) (sub :
      GEqProofTree hL (Sequent.mk (Γr ++ List.map (fun (t : Term L) => formulaSubstN X t x) ts ++
      [FormulaN.all x X] ++ Δr) (succ))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈
      geqLeafSequents sub → seqAllAtomicOrQuantified s') (hconc : (Sequent.mk (Γr ++ [FormulaN.all x X] ++ Δr)
      (succ)) = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γ
  subst succ
  obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B
      (Γr ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++ [FormulaN.all x X] ++ Δr) Δ Λ rfl hsubleaf
  refine ⟨.onePremise (.allLeft ts Γr Δr (Δ ++ [A] ++ Λ) x X hne hfree) q1, .onePremise
      (.allLeft ts Γr Δr (Δ ++ [B] ++ Λ) x X hne hfree) q2, by
    simp only [geqDepth]
    omega, ?_, ?_⟩
  · simpa [geqLeafSequents] using hq1leaf
  · simpa [geqLeafSequents] using hq2leaf

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqConjRight_allRight
    (markedSplit : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → X ≠ Y →
      (∃ (K : List (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ ∃ (K : List (FormulaN L)), P = R ++
      [Y] ++ K ∧ S = K ++ [X] ++ Q) (replaceConjFresh : ∀ (y : Nat) (ant D S : List (FormulaN L)) (C X :
      FormulaN L), formulaFVN X ⊆ formulaFVN C → (∀ (F : FormulaN L), F ∈ ant ++ (D ++ [C] ++ S) → ¬y ∈
      formulaFVN F) → ∀ (F : FormulaN L), F ∈ ant ++ (D ++ [X] ++ S) → ¬y ∈ formulaFVN F) (geqDepth_transport
      : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p)
      (geqLeafProperty_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p : GEqProofTree hL s₁), (∀ (s' :
      Sequent L), s' ∈ geqLeafSequents p → seqAllAtomicOrQuantified s') → ∀ (s' : Sequent L), s' ∈
      geqLeafSequents (heq ▸ p) → seqAllAtomicOrQuantified s') (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L))
      (y : Nat) (Γr Δr Λr : List (FormulaN L)) (x : Nat) (X : FormulaN L) (hfresh : ∀ (F : FormulaN L), F ∈
      (Γr) ++ (Δr ++ [FormulaN.all x X] ++ Λr) → ¬y ∈ formulaFVN F) (hfreeFor : isFreeForN (Term.var y) x X)
      (sub : GEqProofTree hL (Sequent.mk (Γr) (Δr ++ [formulaSubstN X (Term.var y) x] ++ Λr))) (hsubdepth :
      geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified
      s') (hconc : (Sequent.mk (Γr) (Δr ++ [FormulaN.all x X] ++ Λr)) = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++
      Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γ
  have hfreshTarget : ∀ F ∈ Γr ++ (Δ ++ [FormulaN.conj A B] ++ Λ), y ∉ Variables.formulaFVN F := by
    intro F hF
    apply hfresh F
    simpa [hsuc] using hF
  have hfreshTarget1 : ∀ F ∈ Γr ++ (Δ ++ [A] ++ Λ), y ∉ Variables.formulaFVN F :=
    replaceConjFresh y Γr Δ Λ (FormulaN.conj A B) A (fun v hv => Or.inl hv) hfreshTarget
  have hfreshTarget2 : ∀ F ∈ Γr ++ (Δ ++ [B] ++ Λ), y ∉ Variables.formulaFVN F :=
    replaceConjFresh y Γr Δ Λ (FormulaN.conj A B) B (fun v hv => Or.inr hv) hfreshTarget
  rcases markedSplit hsuc (by simp) with
    ⟨K, hΔ, hΛr⟩ | ⟨K, hΔr, hΛ⟩
  · subst Δ
    subst Λr
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B Γr (Δr ++
          [Substitution.formulaSubstN X (Term.var y) x] ++ K)
        Λ (by simp [List.append_assoc]) hsubleaf
    have hin1 : Sequent.mk Γr ((Δr ++ [Substitution.formulaSubstN X (Term.var y) x] ++ K) ++ [A] ++ Λ) =
          Sequent.mk Γr (Δr ++ [Substitution.formulaSubstN X (Term.var y) x] ++ (K ++ [A] ++ Λ)) := by
      simp [List.append_assoc]
    have hin2 : Sequent.mk Γr ((Δr ++ [Substitution.formulaSubstN X (Term.var y) x] ++ K) ++ [B] ++ Λ) =
          Sequent.mk Γr (Δr ++ [Substitution.formulaSubstN X (Term.var y) x] ++ (K ++ [B] ++ Λ)) := by
      simp [List.append_assoc]
    let q1' := hin1 ▸ q1
    let q2' := hin2 ▸ q2
    have hdq1 : geqDepth q1' = geqDepth q1 := geqDepth_transport hin1 q1
    have hdq2 : geqDepth q2' = geqDepth q2 := geqDepth_transport hin2 q2
    have hfresh1 : ∀ F ∈ (Sequent.mk Γr (Δr ++ [FormulaN.all x X] ++ (K ++ [A] ++ Λ))).antecedent ++
            (Sequent.mk Γr (Δr ++ [FormulaN.all x X] ++ (K ++ [A] ++ Λ))).succedent,
          y ∉ Variables.formulaFVN F := by
      simpa [List.append_assoc] using hfreshTarget1
    have hfresh2 : ∀ F ∈ (Sequent.mk Γr (Δr ++ [FormulaN.all x X] ++ (K ++ [B] ++ Λ))).antecedent ++
            (Sequent.mk Γr (Δr ++ [FormulaN.all x X] ++ (K ++ [B] ++ Λ))).succedent,
          y ∉ Variables.formulaFVN F := by
      simpa [List.append_assoc] using hfreshTarget2
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.allRight y Γr Δr
        (K ++ [A] ++ Λ) x X hfresh1 hfreeFor) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.allRight y Γr Δr
        (K ++ [B] ++ Λ) x X hfresh2 hfreeFor) q2'
    have hout1 : Sequent.mk Γr (Δr ++ [FormulaN.all x X] ++ (K ++ [A] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.all x X] ++ K) ++ [A] ++ Λ) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr (Δr ++ [FormulaN.all x X] ++ (K ++ [B] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.all x X] ++ K) ++ [B] ++ Λ) := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hdp1 : geqDepth p1 = 1 + geqDepth q1 := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hdp2 : geqDepth p2 = 1 + geqDepth q2 := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · exact geqLeafProperty_transport hout1 r1 (by
        simpa [r1, geqLeafSequents] using (geqLeafProperty_transport hin1 q1 hq1leaf))
    · exact geqLeafProperty_transport hout2 r2 (by
        simpa [r2, geqLeafSequents] using (geqLeafProperty_transport hin2 q2 hq2leaf))
  · subst Δr
    subst Λ
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B Γr Δ (K ++
          [Substitution.formulaSubstN X (Term.var y) x] ++ Λr)
        (by simp [List.append_assoc]) hsubleaf
    have hin1 : Sequent.mk Γr (Δ ++ [A] ++ (K ++ [Substitution.formulaSubstN X (Term.var y) x] ++ Λr)) =
          Sequent.mk Γr ((Δ ++ [A] ++ K) ++ [Substitution.formulaSubstN X (Term.var y) x] ++ Λr) := by
      simp [List.append_assoc]
    have hin2 : Sequent.mk Γr (Δ ++ [B] ++ (K ++ [Substitution.formulaSubstN X (Term.var y) x] ++ Λr)) =
          Sequent.mk Γr ((Δ ++ [B] ++ K) ++ [Substitution.formulaSubstN X (Term.var y) x] ++ Λr) := by
      simp [List.append_assoc]
    let q1' := hin1 ▸ q1
    let q2' := hin2 ▸ q2
    have hdq1 : geqDepth q1' = geqDepth q1 := geqDepth_transport hin1 q1
    have hdq2 : geqDepth q2' = geqDepth q2 := geqDepth_transport hin2 q2
    have hfresh1 : ∀ F ∈ (Sequent.mk Γr ((Δ ++ [A] ++ K) ++ [FormulaN.all x X] ++ Λr)).antecedent ++
            (Sequent.mk Γr ((Δ ++ [A] ++ K) ++ [FormulaN.all x X] ++ Λr)).succedent,
          y ∉ Variables.formulaFVN F := by
      simpa [List.append_assoc] using hfreshTarget1
    have hfresh2 : ∀ F ∈ (Sequent.mk Γr ((Δ ++ [B] ++ K) ++ [FormulaN.all x X] ++ Λr)).antecedent ++
            (Sequent.mk Γr ((Δ ++ [B] ++ K) ++ [FormulaN.all x X] ++ Λr)).succedent,
          y ∉ Variables.formulaFVN F := by
      simpa [List.append_assoc] using hfreshTarget2
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.allRight y Γr
        (Δ ++ [A] ++ K) Λr x X hfresh1 hfreeFor) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.allRight y Γr
        (Δ ++ [B] ++ K) Λr x X hfresh2 hfreeFor) q2'
    have hout1 : Sequent.mk Γr ((Δ ++ [A] ++ K) ++ [FormulaN.all x X] ++ Λr) = Sequent.mk Γr (Δ ++ [A] ++
              (K ++ [FormulaN.all x X] ++ Λr)) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr ((Δ ++ [B] ++ K) ++ [FormulaN.all x X] ++ Λr) = Sequent.mk Γr (Δ ++ [B] ++
              (K ++ [FormulaN.all x X] ++ Λr)) := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hdp1 : geqDepth p1 = 1 + geqDepth q1 := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hdp2 : geqDepth p2 = 1 + geqDepth q2 := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · exact geqLeafProperty_transport hout1 r1 (by
        simpa [r1, geqLeafSequents] using (geqLeafProperty_transport hin1 q1 hq1leaf))
    · exact geqLeafProperty_transport hout2 r2 (by
        simpa [r2, geqLeafSequents] using (geqLeafProperty_transport hin2 q2 hq2leaf))

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqConjRight_exLeft
    (replaceConjFresh : ∀ (y : Nat) (ant D S : List (FormulaN L)) (C X : FormulaN L), formulaFVN X ⊆
      formulaFVN C → (∀ (F : FormulaN L), F ∈ ant ++ (D ++ [C] ++ S) → ¬y ∈ formulaFVN F) → ∀ (F : FormulaN
      L), F ∈ ant ++ (D ++ [X] ++ S) → ¬y ∈ formulaFVN F) (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)) (y :
      Nat) (Γr Δr succ : List (FormulaN L)) (x : Nat) (X : FormulaN L) (hfresh : ∀ (F : FormulaN L), F ∈ (Γr
      ++ [FormulaN.ex x X] ++ Δr) ++ (succ) → ¬y ∈ formulaFVN F) (hfreeFor : isFreeForN (Term.var y) x X) (sub
      : GEqProofTree hL (Sequent.mk (Γr ++ [formulaSubstN X (Term.var y) x] ++ Δr) (succ))) (hsubdepth :
      geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified
      s') (hconc : (Sequent.mk (Γr ++ [FormulaN.ex x X] ++ Δr) (succ)) = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++
      Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γ
  subst succ
  obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B (Γr ++
        [Substitution.formulaSubstN X (Term.var y) x] ++ Δr)
      Δ Λ rfl hsubleaf
  have hfresh1 : ∀ F ∈ (Sequent.mk (Γr ++ [FormulaN.ex x X] ++ Δr) (Δ ++ [A] ++ Λ)).antecedent ++ (Sequent.mk
            (Γr ++ [FormulaN.ex x X] ++ Δr)
            (Δ ++ [A] ++ Λ)).succedent,
        y ∉ Variables.formulaFVN F := by
    exact replaceConjFresh y (Γr ++ [FormulaN.ex x X] ++ Δr) Δ Λ (FormulaN.conj A B) A
      (fun v hv => Or.inl hv) hfresh
  have hfresh2 : ∀ F ∈ (Sequent.mk (Γr ++ [FormulaN.ex x X] ++ Δr) (Δ ++ [B] ++ Λ)).antecedent ++ (Sequent.mk
            (Γr ++ [FormulaN.ex x X] ++ Δr)
            (Δ ++ [B] ++ Λ)).succedent,
        y ∉ Variables.formulaFVN F := by
    exact replaceConjFresh y (Γr ++ [FormulaN.ex x X] ++ Δr) Δ Λ (FormulaN.conj A B) B
      (fun v hv => Or.inr hv) hfresh
  refine ⟨.onePremise (.exLeft y Γr Δr (Δ ++ [A] ++ Λ) x X hfresh1 hfreeFor) q1, .onePremise
      (.exLeft y Γr Δr (Δ ++ [B] ++ Λ) x X hfresh2 hfreeFor) q2, by
    simp only [geqDepth]
    omega, ?_, ?_⟩
  · simpa [geqLeafSequents] using hq1leaf
  · simpa [geqLeafSequents] using hq2leaf

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqConjRight_exRight
    (markedSplit : ∀ {P Q R S : List (FormulaN L)} {X Y : FormulaN L}, P ++ [X] ++ Q = R ++ [Y] ++ S → X ≠ Y →
      (∃ (K : List (FormulaN L)), R = P ++ [X] ++ K ∧ Q = K ++ [Y] ++ S) ∨ ∃ (K : List (FormulaN L)), P = R ++
      [Y] ++ K ∧ S = K ++ [X] ++ Q) (geqDepth_transport : ∀ {s₁ s₂ : Sequent L} (heq : s₁ = s₂) (p :
      GEqProofTree hL s₁), geqDepth (heq ▸ p) = geqDepth p) (geqLeafProperty_transport : ∀ {s₁ s₂ : Sequent L}
      (heq : s₁ = s₂) (p : GEqProofTree hL s₁), (∀ (s' : Sequent L), s' ∈ geqLeafSequents p →
      seqAllAtomicOrQuantified s') → ∀ (s' : Sequent L), s' ∈ geqLeafSequents (heq ▸ p) →
      seqAllAtomicOrQuantified s') (A B : FormulaN L) (Γ Δ Λ : List (FormulaN L)) (ts : List (Term L)) (Γr Δr
      Λr : List (FormulaN L)) (x : Nat) (X : FormulaN L) (hne : ts ≠ []) (hfree : ∀ (t : Term L), t ∈ ts →
      isFreeForN t x X) (sub : GEqProofTree hL (Sequent.mk (Γr) (Δr ++ List.map (fun (t : Term L) =>
      formulaSubstN X t x) ts ++ [FormulaN.ex x X] ++ Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' :
      Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified s') (hconc : (Sequent.mk (Γr) (Δr ++
      [FormulaN.ex x X] ++ Λr)) = (Sequent.mk (Γ) (Δ ++ [A.conj B] ++ Λ)))
    : ∃ (p1 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++ [A] ++ Λ))), ∃ (p2 : GEqProofTree hL (Sequent.mk (Γ) (Δ ++
      [B] ++ Λ))), 1 + max (geqDepth p1) (geqDepth p2) = 1 + geqDepth sub ∧ (∀ (s' : Sequent L), s' ∈
      geqLeafSequents p1 → seqAllAtomicOrQuantified s') ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p2 →
      seqAllAtomicOrQuantified s' := by
  injection hconc with hant hsuc
  subst Γ
  rcases markedSplit hsuc (by simp) with
    ⟨K, hΔ, hΛr⟩ | ⟨K, hΔr, hΛ⟩
  · subst Δ
    subst Λr
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B Γr (Δr ++
          ts.map (fun t => Substitution.formulaSubstN X t x) ++
          [FormulaN.ex x X] ++ K)
        Λ (by simp [List.append_assoc]) hsubleaf
    have hin1 : Sequent.mk Γr ((Δr ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++
              [FormulaN.ex x X] ++ K) ++ [A] ++ Λ) =
          Sequent.mk Γr (Δr ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++
              [FormulaN.ex x X] ++ (K ++ [A] ++ Λ)) := by
      simp [List.append_assoc]
    have hin2 : Sequent.mk Γr ((Δr ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++
              [FormulaN.ex x X] ++ K) ++ [B] ++ Λ) =
          Sequent.mk Γr (Δr ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++
              [FormulaN.ex x X] ++ (K ++ [B] ++ Λ)) := by
      simp [List.append_assoc]
    let q1' := hin1 ▸ q1
    let q2' := hin2 ▸ q2
    have hdq1 : geqDepth q1' = geqDepth q1 := geqDepth_transport hin1 q1
    have hdq2 : geqDepth q2' = geqDepth q2 := geqDepth_transport hin2 q2
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.exRight ts Γr Δr (K ++ [A] ++ Λ) x X hne hfree) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.exRight ts Γr Δr (K ++ [B] ++ Λ) x X hne hfree) q2'
    have hout1 : Sequent.mk Γr (Δr ++ [FormulaN.ex x X] ++ (K ++ [A] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.ex x X] ++ K) ++ [A] ++ Λ) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr (Δr ++ [FormulaN.ex x X] ++ (K ++ [B] ++ Λ)) = Sequent.mk Γr
            ((Δr ++ [FormulaN.ex x X] ++ K) ++ [B] ++ Λ) := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hdp1 : geqDepth p1 = 1 + geqDepth q1 := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hdp2 : geqDepth p2 = 1 + geqDepth q2 := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · exact geqLeafProperty_transport hout1 r1 (by
        simpa [r1, geqLeafSequents] using (geqLeafProperty_transport hin1 q1 hq1leaf))
    · exact geqLeafProperty_transport hout2 r2 (by
        simpa [r2, geqLeafSequents] using (geqLeafProperty_transport hin2 q2 hq2leaf))
  · subst Δr
    subst Λ
    obtain ⟨q1, q2, hq, hq1leaf, hq2leaf⟩ := ih (geqDepth sub) hsubdepth sub rfl A B Γr Δ (K ++
          ts.map (fun t => Substitution.formulaSubstN X t x) ++
          [FormulaN.ex x X] ++ Λr)
        (by simp [List.append_assoc]) hsubleaf
    have hin1 : Sequent.mk Γr (Δ ++ [A] ++ (K ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++
                [FormulaN.ex x X] ++ Λr)) =
          Sequent.mk Γr ((Δ ++ [A] ++ K) ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++
              [FormulaN.ex x X] ++ Λr) := by
      simp [List.append_assoc]
    have hin2 : Sequent.mk Γr (Δ ++ [B] ++ (K ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++
                [FormulaN.ex x X] ++ Λr)) =
          Sequent.mk Γr ((Δ ++ [B] ++ K) ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++
              [FormulaN.ex x X] ++ Λr) := by
      simp [List.append_assoc]
    let q1' := hin1 ▸ q1
    let q2' := hin2 ▸ q2
    have hdq1 : geqDepth q1' = geqDepth q1 := geqDepth_transport hin1 q1
    have hdq2 : geqDepth q2' = geqDepth q2 := geqDepth_transport hin2 q2
    let r1 := GEqProofTree.onePremise (GentzenStep1Ext.exRight ts Γr (Δ ++ [A] ++ K) Λr x X hne hfree) q1'
    let r2 := GEqProofTree.onePremise (GentzenStep1Ext.exRight ts Γr (Δ ++ [B] ++ K) Λr x X hne hfree) q2'
    have hout1 : Sequent.mk Γr ((Δ ++ [A] ++ K) ++ [FormulaN.ex x X] ++ Λr) = Sequent.mk Γr
            (Δ ++ [A] ++ (K ++ [FormulaN.ex x X] ++ Λr)) := by
      simp [List.append_assoc]
    have hout2 : Sequent.mk Γr ((Δ ++ [B] ++ K) ++ [FormulaN.ex x X] ++ Λr) = Sequent.mk Γr
            (Δ ++ [B] ++ (K ++ [FormulaN.ex x X] ++ Λr)) := by
      simp [List.append_assoc]
    let p1 := hout1 ▸ r1
    let p2 := hout2 ▸ r2
    have hdp1 : geqDepth p1 = 1 + geqDepth q1 := by
      rw [geqDepth_transport hout1 r1]
      simp only [r1, geqDepth]
      omega
    have hdp2 : geqDepth p2 = 1 + geqDepth q2 := by
      rw [geqDepth_transport hout2 r2]
      simp only [r2, geqDepth]
      omega
    refine ⟨p1, p2, by omega, ?_, ?_⟩
    · exact geqLeafProperty_transport hout1 r1 (by
        simpa [r1, geqLeafSequents] using (geqLeafProperty_transport hin1 q1 hq1leaf))
    · exact geqLeafProperty_transport hout2 r2 (by
        simpa [r2, geqLeafSequents] using (geqLeafProperty_transport hin2 q2 hq2leaf))

end
end LCS.CutElim.LKe.Equivalence
end

