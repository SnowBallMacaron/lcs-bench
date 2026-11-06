import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.CutElim.CompletenessBridge
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.LKe.Equivalence.AtomicLeaves
import LCS.CutElim.LKe.Equivalence.ContextPermutation
import LCS.CutElim.LKe.Equivalence.ConjunctionPermutation
import LCS.CutElim.LKe.Equivalence.ImplicationPermutation
import Attach
import LCS.CutElim.LKe.Equivalence.Normalization.ProofsStamp

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

-- ===================================================================
-- Lemma 6.3.3 (required def): sequentHasConjImplTarget
-- ===================================================================
/-- Lemma 6.3.3 (required def): A sequent has a pending normalization
target when its succedent contains a conjunction or its antecedent
contains an implication. -/
@[blueprint "chap6__lemma_6_3_3"]
def sequentHasConjImplTarget {L : Language} (s : Sequent L) : Prop :=
  (∃ (A B : FormulaN L), FormulaN.conj A B ∈ s.succedent) ∨
  (∃ (A B : FormulaN L), FormulaN.impl A B ∈ s.antecedent)

-- ===================================================================
-- Lemma 6.3.3 (required def): gIsConjImplNormalized
-- ===================================================================
/-- Lemma 6.3.3 (required def): A G proof is in conjunction/implication
normal form when every non-leaf node with a pending target selects one
actual target occurrence using conjunction-right or implication-left.
The indexed rule constructor fixes the selected formula and its exact
prefix/suffix contexts.  All subtrees satisfy the same condition. -/
@[blueprint "chap6__lemma_6_3_3"]
def gIsConjImplNormalized {L : Language} :
    {s : Sequent L} → GProofTreeExt s → Prop
  | _, .axiom_ _ _ => True
  | s, .onePremise _ sub =>
    ¬ sequentHasConjImplTarget s ∧
    gIsConjImplNormalized sub
  | s, .twoPremise rule sub1 sub2 =>
    (match rule with
     | .conjRight _ _ _ _ _ => True
     | .implLeft _ _ _ _ _ => True
     | _ => ¬ sequentHasConjImplTarget s) ∧
    gIsConjImplNormalized sub1 ∧
    gIsConjImplNormalized sub2

-- ===================================================================
-- Lemma 6.3.3 (required def): geqIsConjImplNormalized
-- ===================================================================
/-- Lemma 6.3.3 (required def): The conjunction/implication progress
invariant for G=.  A pending target at a non-leaf node must be selected
by an indexed conjunction-right or implication-left constructor.
Equality rules and unrelated logical rules may occur only after the
node has no pending target, and the invariant holds recursively. -/
@[blueprint "chap6__lemma_6_3_3"]
def geqIsConjImplNormalized {L : Language}
    {hL : L.hasEquality = true} :
    {s : Sequent L} → GEqProofTree hL s → Prop
  | _, .base g => gIsConjImplNormalized g
  | _, .axiom_ _ _ => True
  | s, .onePremise _ sub =>
    ¬ sequentHasConjImplTarget s ∧
    geqIsConjImplNormalized sub
  | s, .twoPremise rule sub1 sub2 =>
    (match rule with
     | .conjRight _ _ _ _ _ => True
     | .implLeft _ _ _ _ _ => True
     | _ => ¬ sequentHasConjImplTarget s) ∧
    geqIsConjImplNormalized sub1 ∧
    geqIsConjImplNormalized sub2
  | _, .eqRefl _ Γ Δ sub =>
    ¬ sequentHasConjImplTarget (Sequent.mk Γ Δ) ∧
    geqIsConjImplNormalized sub
  | _, .eqFuncCong _ _ _ Γ Δ sub =>
    ¬ sequentHasConjImplTarget (Sequent.mk Γ Δ) ∧
    geqIsConjImplNormalized sub
  | _, .eqPredCong _ _ _ Γ Δ sub =>
    ¬ sequentHasConjImplTarget (Sequent.mk Γ Δ) ∧
    geqIsConjImplNormalized sub
  | _, .eqGeneral _ _ _ Γ Δ sub =>
    ¬ sequentHasConjImplTarget (Sequent.mk Γ Δ) ∧
    geqIsConjImplNormalized sub

section
-- ATTACH-BLOCKER: variable
variable
    (L : Language) (hL : L.hasEquality = true) (n : Nat) (ih : ∀ (m : Nat), m < n → ∀ {s : Sequent L} (T :
      GEqProofTree hL s), geqDepth T = m → (∀ (s' : Sequent L), s' ∈ geqLeafSequents T →
      seqAllAtomicOrQuantified s') → ∃ (T' : GEqProofTree hL s), geqIsConjImplNormalized T' ∧ geqDepth T' =
      geqDepth T)
-- ATTACH-BLOCKER: unknown command Lean.Parser.Command.include
include ih

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqNormalize_target
    (s : Sequent L) (T : GEqProofTree hL s) (hleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents T →
      seqAllAtomicOrQuantified s') (htarget : sequentHasConjImplTarget s) (hdepth : geqDepth T = n)
    : ∃ (T' : GEqProofTree hL s), geqIsConjImplNormalized T' ∧ geqDepth T' = geqDepth T := by
  classical
  rcases s with ⟨Γ, succ⟩
  change (∃ A B : FormulaN L, FormulaN.conj A B ∈ succ) ∨
    (∃ A B : FormulaN L, FormulaN.impl A B ∈ Γ) at htarget
  rcases htarget with
    ⟨A, B, hAB⟩ | ⟨A, B, hAB⟩
  · obtain ⟨Δ, Λ, hsucc⟩ := perm_mem_split (FormulaN.conj A B) succ hAB
    subst succ
    obtain ⟨p1, p2, hpdepth, hp1leaf, hp2leaf⟩ := geqPermute_conjRight_withLeaves A B Γ Δ Λ T hleaf
    have hp1depth : geqDepth p1 < n := by omega
    have hp2depth : geqDepth p2 < n := by omega
    obtain ⟨q1, hq1norm, hq1depth⟩ := ih (geqDepth p1) hp1depth p1 rfl hp1leaf
    obtain ⟨q2, hq2norm, hq2depth⟩ := ih (geqDepth p2) hp2depth p2 rfl hp2leaf
    let p : GEqProofTree hL (Sequent.mk Γ (Δ ++ [FormulaN.conj A B] ++ Λ)) := .twoPremise
        (.conjRight Γ Δ Λ A B) q1 q2
    refine ⟨p, ?_, ?_⟩
    · exact ⟨trivial, hq1norm, hq2norm⟩
    · simp only [p, geqDepth]
      omega
  · obtain ⟨Γ₁, Γ₂, hΓ⟩ := perm_mem_split (FormulaN.impl A B) Γ hAB
    subst Γ
    obtain ⟨p1, p2, hpdepth, hp1leaf, hp2leaf⟩ := geqPermute_implLeft_withLeaves A B Γ₁ Γ₂ succ T hleaf
    obtain ⟨p1, hp1perm, hp1leaf⟩ := geqPermuteContexts p1 (Γ₁ ++ Γ₂) ([A] ++ succ)
        (List.Perm.refl _) (by exact List.perm_append_comm) hp1leaf
    have hp1depth : geqDepth p1 < n := by omega
    have hp2depth : geqDepth p2 < n := by omega
    obtain ⟨q1, hq1norm, hq1depth⟩ := ih (geqDepth p1) hp1depth p1 rfl hp1leaf
    obtain ⟨q2, hq2norm, hq2depth⟩ := ih (geqDepth p2) hp2depth p2 rfl hp2leaf
    let p : GEqProofTree hL (Sequent.mk (Γ₁ ++ [FormulaN.impl A B] ++ Γ₂) succ) := .twoPremise
        (.implLeft Γ₁ Γ₂ succ A B) q1 q2
    refine ⟨p, ?_, ?_⟩
    · exact ⟨trivial, hq1norm, hq2norm⟩
    · simp only [p, geqDepth]
      omega

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqNormalize_other
    (s : Sequent L) (T : GEqProofTree hL s) (hdepth : geqDepth T = n) (hleaf : ∀ (s' : Sequent L), s' ∈
      geqLeafSequents T → seqAllAtomicOrQuantified s') (normOne : ∀ {prem conc : Sequent L} (rule :
      GentzenStep1Ext prem conc) (sub : GEqProofTree hL prem), geqDepth sub < n → (∀ (s' : Sequent L), s' ∈
      geqLeafSequents sub → seqAllAtomicOrQuantified s') → ¬sequentHasConjImplTarget conc → ∃ (p :
      GEqProofTree hL conc), geqIsConjImplNormalized p ∧ geqDepth p = 1 + geqDepth sub) (normTwo : ∀ {prem1
      prem2 conc : Sequent L} (rule : GentzenStep2Ext prem1 prem2 conc) (sub1 : GEqProofTree hL prem1) (sub2 :
      GEqProofTree hL prem2), geqDepth sub1 < n → geqDepth sub2 < n → (∀ (s' : Sequent L), s' ∈
      geqLeafSequents sub1 → seqAllAtomicOrQuantified s') → (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub2 →
      seqAllAtomicOrQuantified s') → ¬sequentHasConjImplTarget conc → ∃ (p : GEqProofTree hL conc),
      geqIsConjImplNormalized p ∧ geqDepth p = 1 + max (geqDepth sub1) (geqDepth sub2)) (htarget :
      ¬sequentHasConjImplTarget s)
    : ∃ (T' : GEqProofTree hL s), geqIsConjImplNormalized T' ∧ geqDepth T' = geqDepth T := by
  classical
  cases T with
  | base g =>
    cases g with
    | axiom_ s hAx =>
      exact ⟨.base (.axiom_ s hAx), trivial, rfl⟩
    | onePremise rule sub =>
      simpa only [geqDepth, gProofTreeDepth] using normOne rule (.base sub) (by
          simp only [geqDepth, gProofTreeDepth] at hdepth ⊢
          omega) (by
          simpa [geqLeafSequents, gProofTreeLeafSequents] using hleaf) htarget
    | twoPremise rule sub1 sub2 =>
      simpa only [geqDepth, gProofTreeDepth] using normTwo rule (.base sub1) (.base sub2) (by
          simp only [geqDepth, gProofTreeDepth] at hdepth ⊢
          omega) (by
          simp only [geqDepth, gProofTreeDepth] at hdepth ⊢
          omega) (by
          intro s' hs'
          exact hleaf s' (by
            simp only [geqLeafSequents, gProofTreeLeafSequents, List.mem_append]
            exact Or.inl hs')) (by
          intro s' hs'
          exact hleaf s' (by
            simp only [geqLeafSequents, gProofTreeLeafSequents, List.mem_append]
            exact Or.inr hs')) htarget
  | axiom_ s hAx =>
    exact ⟨.axiom_ s hAx, trivial, rfl⟩
  | onePremise rule sub =>
    simpa only [geqDepth] using normOne rule sub (by
        simp only [geqDepth] at hdepth
        omega) (by
        simpa [geqLeafSequents] using hleaf) htarget
  | twoPremise rule sub1 sub2 =>
    simpa only [geqDepth] using normTwo rule sub1 sub2 (by
        simp only [geqDepth] at hdepth
        omega) (by
        simp only [geqDepth] at hdepth
        omega) (by
        intro s' hs'
        exact hleaf s' (by
          simp only [geqLeafSequents, List.mem_append]
          exact Or.inl hs')) (by
        intro s' hs'
        exact hleaf s' (by
          simp only [geqLeafSequents, List.mem_append]
          exact Or.inr hs')) htarget
  | eqRefl t Γ Δ sub =>
    have hsubdepth : geqDepth sub < n := by
      simp only [geqDepth] at hdepth
      omega
    obtain ⟨q, hqnorm, hqdepth⟩ := ih (geqDepth sub) hsubdepth sub rfl (by
        simpa [geqLeafSequents] using hleaf)
    refine ⟨.eqRefl t Γ Δ q, ⟨htarget, hqnorm⟩, ?_⟩
    simp only [geqDepth]
    omega
  | eqFuncCong f ss ts Γ Δ sub =>
    have hsubdepth : geqDepth sub < n := by
      simp only [geqDepth] at hdepth
      omega
    obtain ⟨q, hqnorm, hqdepth⟩ := ih (geqDepth sub) hsubdepth sub rfl (by
        simpa [geqLeafSequents] using hleaf)
    refine ⟨.eqFuncCong f ss ts Γ Δ q, ⟨htarget, hqnorm⟩, ?_⟩
    simp only [geqDepth]
    omega
  | eqPredCong P ss ts Γ Δ sub =>
    have hsubdepth : geqDepth sub < n := by
      simp only [geqDepth] at hdepth
      omega
    obtain ⟨q, hqnorm, hqdepth⟩ := ih (geqDepth sub) hsubdepth sub rfl (by
        simpa [geqLeafSequents] using hleaf)
    refine ⟨.eqPredCong P ss ts Γ Δ q, ⟨htarget, hqnorm⟩, ?_⟩
    simp only [geqDepth]
    omega
  | eqGeneral axioms hne haxioms Γ Δ sub =>
    have hsubdepth : geqDepth sub < n := by
      simp only [geqDepth] at hdepth
      omega
    obtain ⟨q, hqnorm, hqdepth⟩ := ih (geqDepth sub) hsubdepth sub rfl (by
        simpa [geqLeafSequents] using hleaf)
    refine ⟨.eqGeneral axioms hne haxioms Γ Δ q, ⟨htarget, hqnorm⟩, ?_⟩
    simp only [geqDepth]
    omega

end

/-- Helper for Lemma 6.3.3: normalize conjunction-right and
implication-left directly inside G=.  The output remains indexed by the
input sequent and can therefore retain reflexivity, function congruence,
predicate congruence, and general equality-rule nodes.  When the input
already has the atomic-or-quantified leaf property of Lemma 6.3.1, the
normalization preserves its depth. -/
@[blueprint "chap6__lemma_6_3_3" (main := true)]
theorem geqNormalize_conjImpl {L : Language}
    {hL : L.hasEquality = true} {s : Sequent L}
    (T : GEqProofTree hL s) :
    ∃ (T' : GEqProofTree hL s),
      geqIsConjImplNormalized T' ∧
      ((∀ s' ∈ geqLeafSequents T,
          seqAllAtomicOrQuantified s') →
        geqDepth T' = geqDepth T) 

end LCS.CutElim.LKe.Equivalence
end
