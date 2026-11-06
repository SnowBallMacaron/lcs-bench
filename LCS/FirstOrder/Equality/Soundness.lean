import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Equality.SystemGEq
import Attach
import LCS.FirstOrder.Equality.Soundness.ProofsStamp

section
namespace LCS.FirstOrder.Equality
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution (formulaSubstEvalDirectN)
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Completeness

-- ===================================================================
-- Lemma 5.6.2: Helpers for equality rule validity preservation
-- ===================================================================

/-- Helper: conjoinFormulae evaluated to true implies all constituent
formulas are true. Proved by induction on the list structure. -/
theorem conjoinFormulaeEval {L : Language}
    {M : Structure L} {s : Assignment M} {default : FormulaN L}
    {fs : List (FormulaN L)}
    (h : formulaEvalN M (conjoinFormulae default fs) s) :
    ∀ F ∈ fs, formulaEvalN M F s := by
-- BEGIN PROOF
  induction fs with
  | nil => intro F hF; simp at hF
  | cons A rest ih =>
    intro F hF
    match rest, ih with
    | [], _ =>
      simp only [conjoinFormulae] at h
      have : F = A := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hF
        exact hF
      rw [this]; exact h
    | B :: tail, ih' =>
      simp only [conjoinFormulae, formulaEvalN] at h
      rcases List.mem_cons.mp hF with rfl | hF'
      · exact h.1
      · exact ih' h.2 F hF' /- retained: used by LCS.CutElim.Interpolation.Equality.Support -/

/-- Helper: The equality reflexivity formula t = t is valid. -/
theorem eqReflValid {L : Language} (hL : L.hasEquality = true) (t : Term L)
    (M : Structure L) (s : Assignment M) :
    formulaEvalN M (FormulaN.eq_ hL t t) s := by
-- BEGIN PROOF
  simp [formulaEvalN] /- retained: used by LCS.CutElim.LKe.Equivalence.EqualityTranslation -/

/-- Helper: The function congruence formula is valid: if si = ti for
all i, then f(s1,...,sn) = f(t1,...,tn). -/
theorem eqFuncCongValid {L : Language} (hL : L.hasEquality = true)
    (f : L.funSymbols) (ss ts : Fin (L.funArity f) → Term L)
    (M : Structure L) (s : Assignment M) :
    formulaEvalN M (eqCongruenceImplFunc L hL f ss ts) s := by
-- BEGIN PROOF
  simp only [eqCongruenceImplFunc, formulaEvalN]
  intro hant
  have hpairs := conjoinFormulaeEval hant
  have heqs : ∀ i, termEval M s (ss i) = termEval M s (ts i) := by
    intro i
    have hi : FormulaN.eq_ hL (ss i) (ts i) ∈ eqPairsList hL ss ts := by
      simp only [eqPairsList, List.mem_map]
      exact ⟨i, List.mem_finRange i, rfl⟩
    exact hpairs _ hi
  show termEval M s (Term.func f ss) = termEval M s (Term.func f ts)
  simp only [termEval]
  congr 1
  funext i
  exact heqs i /- retained: used by LCS.CutElim.LKe.Equivalence.Validity -/

/-- Helper: The predicate congruence formula is valid: if si = ti for
all i and P(s1,...,sn), then P(t1,...,tn). -/
theorem eqPredCongValid {L : Language} (hL : L.hasEquality = true)
    (P : L.predSymbols) (ss ts : Fin (L.predArity P) → Term L)
    (M : Structure L) (s : Assignment M) :
    formulaEvalN M (eqCongruenceImplPred L hL P ss ts) s := by
-- BEGIN PROOF
  simp only [eqCongruenceImplPred, formulaEvalN]
  intro hant
  have hall := conjoinFormulaeEval hant
  have hPss : formulaEvalN M (FormulaN.predN P ss) s :=
    hall _ (List.mem_append_right _ (List.Mem.head _))
  have heqs : ∀ i, termEval M s (ss i) = termEval M s (ts i) := by
    intro i
    have hi : FormulaN.eq_ hL (ss i) (ts i) ∈ eqPairsList hL ss ts ++ [FormulaN.predN P ss] := by
      exact List.mem_append_left _ (by
        simp only [eqPairsList, List.mem_map]
        exact ⟨i, List.mem_finRange i, rfl⟩)
    exact hall _ hi
  have : (fun i => termEval M s (ts i)) = (fun i => termEval M s (ss i)) := by
    funext i; exact (heqs i).symm
  rw [this]; exact hPss /- retained: used by LCS.CutElim.LKe.Equivalence.Validity -/

/-- Helper: The equality predicate congruence formula is valid:
if s1 = t1, s2 = t2, and s1 = s2, then t1 = t2. This is the
textbook H6(iii) instance for the doteq predicate. -/
theorem eqEqCongValid {L : Language} (hL : L.hasEquality = true)
    (s1 s2 t1 t2 : Term L)
    (M : Structure L) (s : Assignment M) :
    formulaEvalN M (eqCongruenceImplEq hL s1 s2 t1 t2) s := by
-- BEGIN PROOF
  simp only [eqCongruenceImplEq, formulaEvalN]
  intro h
  obtain ⟨h1, h2, h3⟩ := h
  -- h1 : termEval M s s1 = termEval M s t1
  -- h2 : termEval M s s2 = termEval M s t2
  -- h3 : termEval M s s1 = termEval M s s2
  -- Goal: termEval M s t1 = termEval M s t2
  rw [← h1, h3, h2] /- retained: used by LCS.CutElim.LKe.Equivalence.Validity -/

/-- Helper: Every equality axiom instance is valid. -/
theorem eqAxiomInstanceValid {L : Language} (hL : L.hasEquality = true)
    (A : FormulaN L)
    (h : isEqAxiomInstance hL A) (M : Structure L) (s : Assignment M) :
    formulaEvalN M A s := by
-- BEGIN PROOF
  rcases h with ⟨t, rfl⟩ | ⟨f, ss, ts, rfl⟩ | ⟨P, ss, ts, rfl⟩ |
    ⟨s1, s2, t1, t2, rfl⟩
  · exact eqReflValid hL t M s
  · exact eqFuncCongValid hL f ss ts M s
  · exact eqPredCongValid hL P ss ts M s
  · exact eqEqCongValid hL s1 s2 t1 t2 M s /- retained: used by LCS.CutElim.LKe.Equivalence.Validity -/

-- ===================================================================
-- Lemma 5.6.2: eqRuleFalsificationIff
-- ===================================================================

/-- Lemma 5.6.2: For arbitrary contexts, each equality rule of Definition
5.6.2 preserves and reflects falsifiability in some structure: reflexivity,
function congruence, predicate congruence, equality congruence,
and a nonempty list of equality axioms, appended to the antecedent. -/
@[blueprint "chap5__lemma_5_6_2" (main := true)]
theorem eqRuleFalsificationIff {L : Language} (hL : L.hasEquality = true)
    (Γ Δ : List (FormulaN L)) :
    (∀ t : Term L,
      sequentFalsifiable (Sequent.mk (Γ ++ [FormulaN.eq_ hL t t]) Δ) ↔
        sequentFalsifiable (Sequent.mk Γ Δ)) ∧
    (∀ (f : L.funSymbols) (ss ts : Fin (L.funArity f) → Term L),
      sequentFalsifiable (Sequent.mk (Γ ++ [eqCongruenceImplFunc L hL f ss ts]) Δ) ↔
        sequentFalsifiable (Sequent.mk Γ Δ)) ∧
    (∀ (P : L.predSymbols)
      (ss ts : Fin (L.predArity P) → Term L),
      sequentFalsifiable (Sequent.mk (Γ ++ [eqCongruenceImplPred L hL P ss ts]) Δ) ↔
        sequentFalsifiable (Sequent.mk Γ Δ)) ∧
    (∀ s1 s2 t1 t2 : Term L,
      sequentFalsifiable (Sequent.mk (Γ ++ [eqCongruenceImplEq hL s1 s2 t1 t2]) Δ) ↔
        sequentFalsifiable (Sequent.mk Γ Δ)) ∧
    (∀ (axioms : List (FormulaN L)) (_hne : axioms ≠ [])
      (_haxioms : ∀ A ∈ axioms, isEqAxiomInstance hL A),
      sequentFalsifiable (Sequent.mk (Γ ++ axioms) Δ) ↔
        sequentFalsifiable (Sequent.mk Γ Δ)) 

-- ===================================================================
-- Lemma 5.6.3: soundnessGEq
-- ===================================================================

/-- Lemma 5.6.3: If a sequent is G_=-provable then it is valid. Soundness
of the System G_=. Every sequent provable in the Gentzen system G_= (with equality rules) is valid. -/
@[blueprint "chap5__lemma_5_6_3" (main := true)]
theorem soundnessGEq {L : Language} (hL : L.hasEquality = true) (seq : Sequent L)
    (h : sequentProvableEq hL seq) : sequentValid seq 

end LCS.FirstOrder.Equality
end
