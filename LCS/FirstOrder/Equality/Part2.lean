import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.Completeness
import LCS.FirstOrder.Equality.Part1
import Attach
import LCS.FirstOrder.Equality.Part2.ProofsStamp

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

/-- Lemma 5.6.1 (companion): If s_i ~ t_i for all i, then
f(s1,...,sn) ~ f(t1,...,tn), using H6(ii) and H2. Ensures
well-definedness of the function interpretation on equivalence
classes. -/
theorem eqCongruence_func {L : Language}
    {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    (hHS : IsHintikkaSetEq L hL H S)
    (f : L.funSymbols) (hf : f ∈ signedSetFunSyms S)
    (ss ts : Fin (L.funArity f) → Term L)
    (hss : ∀ i, ss i ∈ H) (hts : ∀ i, ts i ∈ H)
    (hcong : ∀ i, eqCongruence hL S (ss i) (ts i)) :
    eqCongruence hL S (Term.func f ss) (Term.func f ts) :=
-- BEGIN PROOF
by
  have h6ii := hHS.h6ii f hf ss ts hss hts
  have hb := hHS.base.h2 (TypeB.tImpl
    (conjoinFormulae (FormulaN.eq_ hL (Term.func f ss) (Term.func f ts))
      (eqPairsList hL ss ts))
    (FormulaN.eq_ hL (Term.func f ss) (Term.func f ts)))
  simp only [TypeB.toSigned, TypeB.comp1, TypeB.comp2] at hb
  unfold eqCongruence
  cases hb h6ii with
  | inr h => exact h
  | inl hF =>
    exfalso
    by_cases hn : L.funArity f = 0
    · have hpairs_nil : eqPairsList hL ss ts = [] := by
        simp [eqPairsList, List.finRange, hn]
      rw [hpairs_nil] at hF
      simp only [conjoinFormulae] at hF
      have hss_eq : ss = ts := funext (fun i => absurd (Fin.pos i) (by omega))
      rw [hss_eq] at hF
      have hT := hHS.h6i (Term.func f ts) (hHS.base.hTA.closedFunc f hf ts hts)
      exact hHS.base.h0 (FormulaN.eq_ hL (Term.func f ts) (Term.func f ts)) rfl ⟨hT, hF⟩
    · have hpos : 0 < L.funArity f := Nat.pos_of_ne_zero hn
      have hne : eqPairsList hL ss ts ≠ [] := by
        intro h
        have : (eqPairsList hL ss ts).length = 0 := by rw [h]; rfl
        simp [eqPairsList, List.length_map, List.length_finRange] at this
        omega
      exact falseConjoinContra hHS.base.h0 hHS.base.h2
        (FormulaN.eq_ hL (Term.func f ss) (Term.func f ts))
        (eqPairsList hL ss ts) hne hF
        (fun F hF' => by
          simp [eqPairsList, List.mem_map] at hF'
          obtain ⟨i, _, rfl⟩ := hF'
          exact hcong i)
        (fun F hF' => by
          simp [eqPairsList, List.mem_map] at hF'
          obtain ⟨i, _, rfl⟩ := hF'
          exact rfl) /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

-- ===================================================================
-- Lemma 5.6.1 (companion theorem): eqCongruence_pred
-- ===================================================================



/-- Lemma 5.6.1 (companion): Negative predicate membership is invariant
under pointwise equality congruence of argument tuples in H. This includes
nullary predicates, whose argument tuples are empty, and makes the printed
predicate interpretation independent of the chosen representatives. -/
theorem eqCongruence_falsePred {L : Language}
    {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    (hHS : IsHintikkaSetEq L hL H S)
    (P : L.predSymbols)
    (ss ts : Fin (L.predArity P) → Term L)
    (hss : ∀ i, ss i ∈ H) (hts : ∀ i, ts i ∈ H)
    (hcong : ∀ i, eqCongruence hL S (ss i) (ts i)) :
    (SignedFormula.falseF (FormulaN.predN P ss) ∈ S ↔
     SignedFormula.falseF (FormulaN.predN P ts) ∈ S) := by
  have tailFalse (A : FormulaN L) (fs : List (FormulaN L))
      (hTs : ∀ F ∈ fs, SignedFormula.trueF F ∈ S)
      (hAt : ∀ F ∈ fs, F.isAtomic = true)
      (hF : SignedFormula.falseF (conjoinFormulae A (fs ++ [A])) ∈ S) :
      SignedFormula.falseF A ∈ S := by
    induction fs with
    | nil => exact hF
    | cons B rest ih =>
      have hConj : conjoinFormulae A ((B :: rest) ++ [A]) =
          FormulaN.conj B (conjoinFormulae A (rest ++ [A])) := by
        cases rest <;> rfl
      rw [hConj] at hF
      have hb := hHS.base.h2 (TypeB.fConj B (conjoinFormulae A (rest ++ [A]))) hF
      rcases hb with hB | hRest
      · exact False.elim (hHS.base.h0 B (hAt B List.mem_cons_self)
          ⟨hTs B List.mem_cons_self, hB⟩)
      · exact ih (fun F h => hTs F (List.Mem.tail _ h))
          (fun F h => hAt F (List.Mem.tail _ h)) hRest
  have forward : ∀ (uu vv : Fin (L.predArity P) → Term L),
      (∀ i, eqCongruence hL S (uu i) (vv i)) →
      (∀ i, uu i ∈ H) → (∀ i, vv i ∈ H) →
      SignedFormula.falseF (FormulaN.predN P uu) ∈ S →
      SignedFormula.falseF (FormulaN.predN P vv) ∈ S := by
    intro uu vv hc huu hvv hFuu
    have hPS : P ∈ signedSetPredSyms S :=
      ⟨SignedFormula.falseF (FormulaN.predN P uu), hFuu, rfl⟩
    have hImpl := hHS.h6iii P hPS vv uu hvv huu
    have hb := hHS.base.h2 (TypeB.tImpl
      (conjoinFormulae (FormulaN.predN P vv)
        (eqPairsList hL vv uu ++ [FormulaN.predN P vv]))
      (FormulaN.predN P uu)) hImpl
    rcases hb with hF | hTuu
    · apply tailFalse (FormulaN.predN P vv) (eqPairsList hL vv uu) _ _ hF
      · intro F hF'
        simp only [eqPairsList, List.mem_map] at hF'
        obtain ⟨i, _, rfl⟩ := hF'
        exact eqCongruence_symm hHS (uu i) (vv i) (huu i) (hvv i) (hc i)
      · intro F hF'
        simp only [eqPairsList, List.mem_map] at hF'
        obtain ⟨i, _, rfl⟩ := hF'
        rfl
    · exact False.elim (hHS.base.h0 (.predN P uu) rfl ⟨hTuu, hFuu⟩)
  exact ⟨forward ss ts hcong hss hts,
    forward ts ss (fun i => eqCongruence_symm hHS (ss i) (ts i)
      (hss i) (hts i) (hcong i)) hts hss⟩ /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

-- ===================================================================
-- Lemma 5.6.1 (companion theorem): quotientTermEvalIdentity
-- ===================================================================



-- ===================================================================
-- Lemma 5.6.1: hintikka_set_eq_satisfiable
-- ===================================================================

/-- Lemma 5.6.1 (companion): Equality in S induces a setoid on H. -/
@[blueprint "chap5__lemma_5_6_1"]
noncomputable def eqSetoid {L : Language}
    (hL : L.hasEquality = true)
    (H : Set (Term L)) (S : Set (SignedFormula L))
    (hHS : IsHintikkaSetEq L hL H S) :
    Setoid { t : Term L // t ∈ H } :=
  ⟨fun s t => eqCongruence hL S s.val t.val,
   eqCongruence_equiv hHS⟩

-- Abbreviation for the quotient type.
@[blueprint "chap5__lemma_5_6_1"]
abbrev QType {L : Language}
    (hL : L.hasEquality = true)
    (H : Set (Term L)) (S : Set (SignedFormula L))
    (hHS : IsHintikkaSetEq L hL H S) :=
  @Quotient { t : Term L // t ∈ H } (eqSetoid hL H S hHS)

@[blueprint "chap5__lemma_5_6_1"]
noncomputable abbrev qmk {L : Language}
    {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    {hHS : IsHintikkaSetEq L hL H S}
    (a : { t : Term L // t ∈ H }) : QType hL H S hHS :=
  @Quotient.mk _ (eqSetoid hL H S hHS) a

-- For n-ary operations on the quotient, we choose representatives
-- using Quotient.inductionOn and prove independence.
-- interpFunc: given quotient args, pick reps, apply func, quotient
-- the result. Well-definedness follows from eqCongruence_func.

-- Helper: given a function on reps that respects the setoid
-- on each argument, lift to a function on quotients.
-- Uses Classical.choose for representative selection.
noncomputable def chooseRep {L : Language}
    {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    {hHS : IsHintikkaSetEq L hL H S}
    (q : QType hL H S hHS) : { t : Term L // t ∈ H } :=
  Classical.choose (@Quotient.inductionOn
    { t : Term L // t ∈ H } (eqSetoid hL H S hHS)
    (fun q' => ∃ (a : { t : Term L // t ∈ H }),
      q' = @Quotient.mk _ (eqSetoid hL H S hHS) a)
    q (fun a => ⟨a, rfl⟩)) /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/



noncomputable def finQuotLift {L : Language}
    {hL : L.hasEquality = true}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    {hHS : IsHintikkaSetEq L hL H S}
    {β : Sort _} {n : Nat}
    (g : (Fin n → { t : Term L // t ∈ H }) → β)
    (_hg : ∀ xs ys : Fin n → { t : Term L // t ∈ H },
      (∀ i, @Setoid.r _ (eqSetoid hL H S hHS) (xs i) (ys i)) → g xs = g ys)
    (args : Fin n → QType hL H S hHS) : β :=
  g (fun i => chooseRep (args i)) /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

-- The key property of finQuotLift: when all args are qmk of known values,
-- the result agrees with applying g directly.


/-- Lemma 5.6.1 (companion): The model with carrier H modulo equality in S.
Function and constant symbols of L_S act on representatives by term construction;
those outside L_S receive a fixed default interpretation. A predicate atom is
false exactly when its negative signed atom belongs to S; positive and unmentioned
atoms are true, including predicates of rank zero. -/
@[blueprint "chap5__lemma_5_6_1"]
noncomputable def quotientStructureEq {L : Language}
    (hL : L.hasEquality = true)
    (H : Set (Term L)) (S : Set (SignedFormula L))
    (hHS : IsHintikkaSetEq L hL H S) : Structure L := by
  classical
  let default : QType hL H S hHS := qmk
    ⟨hHS.base.hTA.nonempty.choose, hHS.base.hTA.nonempty.choose_spec⟩
  exact {
    carrier := QType hL H S hHS
    carrierNonempty := ⟨default⟩
    interpFunc := fun f args => if hf : f ∈ signedSetFunSyms S then
      finQuotLift
        (fun reps => qmk ⟨Term.func f (fun i => (reps i).val),
          hHS.base.hTA.closedFunc f hf _ (fun i => (reps i).property)⟩)
        (fun xs ys h => by
          apply Quotient.sound
          exact eqCongruence_func hHS f hf
            (fun i => (xs i).val) (fun i => (ys i).val)
            (fun i => (xs i).property) (fun i => (ys i).property) h)
        args
      else default
    interpConst := fun c => if hc : c ∈ signedSetConstSyms S then
      qmk ⟨Term.const c, hHS.base.hTA.closedConst c hc⟩ else default
    interpPred := fun P args =>
      finQuotLift
        (fun reps => SignedFormula.falseF (FormulaN.predN P (fun i => (reps i).val)) ∉ S)
        (fun xs ys h => propext (not_congr (eqCongruence_falsePred hHS P
          (fun i => (xs i).val) (fun i => (ys i).val)
          (fun i => (xs i).property) (fun i => (ys i).property) h))) args }

-- Helper: terms with all free vars in H are in H.


-- Identity assignment for the quotient structure.
@[blueprint "chap5__lemma_5_6_1"]
noncomputable def quotAssignment {L : Language}
    (hL : L.hasEquality = true)
    (H : Set (Term L)) (S : Set (SignedFormula L))
    (hHS : IsHintikkaSetEq L hL H S) :
    Assignment (quotientStructureEq hL H S hHS) :=
  open Classical in
  fun x =>
    if h : Term.var x ∈ H then
      qmk ⟨Term.var x, h⟩
    else
      qmk ⟨hHS.base.hTA.nonempty.choose, hHS.base.hTA.nonempty.choose_spec⟩







/-- Lemma 5.6.1: Every equality Hintikka set over the occurrence-language
term algebra H is satisfied by the identity assignment in quotientStructureEq,
whose carrier is H modulo the equality relation induced by S. -/
@[blueprint "chap5__lemma_5_6_1" (main := true)]
theorem hintikka_set_eq_satisfiable {L : Language}
    (hL : L.hasEquality = true)
    (H : Set (Term L)) (S : Set (SignedFormula L))
    (hHS : IsHintikkaSetEq L hL H S) :
    ∀ sf, sf ∈ S → SignedFormula.satisfiedBy
      (quotientStructureEq hL H S hHS) (quotAssignment hL H S hHS) sf 

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

