import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.Partitions
import Attach
import LCS.CutElim.Interpolation.ConstantSubstitution.ProofsStamp

section
namespace LCS.CutElim.Interpolation
open Classical
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen.Hintikka

/-- Constant substitution on LK proofs: for any constant c and a variable z
fresh in T, replace c by z in every node sequent and rule annotation.
The result is a proof of the substituted sequent. -/
@[blueprint "chap6__lemma_6_5_1"]
noncomputable def folkProofSubstConst {L : Language} {s : Sequent L}
    (T : LCS.CutElim.LK.FOLKProofTree s) (z : Nat) (c : L.constSymbols)
    (hNotOccurs : T.varNotOccurs z) :
    LCS.CutElim.LK.FOLKProofTree (sequentSubstConst s z c) := by
  exact prepare T z c hNotOccurs
where
  prepare {L : Language} {s : Sequent L}
      (T : LCS.CutElim.LK.FOLKProofTree s) (z : Nat) (c : L.constSymbols)
      (hNotOccurs : T.varNotOccurs z) :
      LCS.CutElim.LK.FOLKProofTree (sequentSubstConst s z c) := by
    have termComm (u t : Term L) (x : Nat) (hzx : z ≠ x) :
        termSubstConst (termSubst u t x) z c =
          termSubst (termSubstConst u z c) (termSubstConst t z c) x := by
      exact folkConst_termComm L z c u _ x hzx
    have formulaComm (A : FormulaN L) (t : Term L) (x : Nat)
        (hzx : z ≠ x) :
        formulaSubstConst (formulaSubstN A t x) z c =
          formulaSubstN (formulaSubstConst A z c)
            (termSubstConst t z c) x := by
      exact folkConst_formulaComm L z c termComm A t x hzx
    have termFreshAfterConst (t : Term L) (v : Nat) (hvz : v ≠ z)
        (h : v ∉ termFV t) :
        v ∉ termFV (termSubstConst t z c) := by
      exact folkConst_termFreshAfterConst L z c t _ hvz h
    have freeAfterConst (A : FormulaN L) (t : Term L) (x : Nat)
        (hfree : isFreeForN t x A) (hNoZ : z ∉ formulaBVN A) :
        isFreeForN (termSubstConst t z c) x
          (formulaSubstConst A z c) := by
      exact folkConst_freeAfterConst L z c termFreshAfterConst A t _ hfree hNoZ
    have formulaFreshAfterConst (A : FormulaN L) (v : Nat)
        (hvz : v ≠ z) (h : v ∉ formulaFVN A) :
        v ∉ formulaFVN (formulaSubstConst A z c) := by
      exact folkConst_formulaFreshAfterConst L z c termFreshAfterConst A v hvz h
    have sequentFreshAfterConst (q : Sequent L) (e : Nat)
        (he : ∀ F ∈ q.antecedent ++ q.succedent, e ∉ formulaFVN F)
        (hez : e ≠ z) :
        ∀ F ∈ (sequentSubstConst q z c).antecedent ++
            (sequentSubstConst q z c).succedent,
          e ∉ formulaFVN F := by
      exact folkConst_sequentFreshAfterConst L z c formulaFreshAfterConst q e he hez
    exact transform z c formulaComm freeAfterConst sequentFreshAfterConst T hNotOccurs

  transform {L : Language} (z : Nat) (c : L.constSymbols)
      (formulaComm : ∀ (A : FormulaN L) (t : Term L) (x : Nat) (hzx : z ≠ x), formulaSubstConst (formulaSubstN
        A t x) z c = formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x) (freeAfterConst : ∀ (A
        : FormulaN L) (t : Term L) (x : Nat) (hfree : isFreeForN t x A) (hNoZ : z ∉ formulaBVN A), isFreeForN
        (termSubstConst t z c) x (formulaSubstConst A z c)) (sequentFreshAfterConst : ∀ (q : Sequent L) (e :
        Nat) (he : ∀ F ∈ q.antecedent ++ q.succedent, e ∉ formulaFVN F) (hez : e ≠ z), ∀ F ∈
        (sequentSubstConst q z c).antecedent ++ (sequentSubstConst q z c).succedent, e ∉ formulaFVN F)
      {q : Sequent L}
      (U : LCS.CutElim.LK.FOLKProofTree q) (hNO : U.varNotOccurs z) :
      LCS.CutElim.LK.FOLKProofTree (sequentSubstConst q z c) :=
    match U with
    | .axiom_ q hax => by
      have hax' : isFOLKAxiom (sequentSubstConst q z c) := by
        rcases hax with ⟨A, hΓ, hΔ⟩
        exact
          ⟨formulaSubstConst A z c,
            by simp [sequentSubstConst, hΓ],
            by simp [sequentSubstConst, hΔ]⟩
      exact FOLKProofTree.axiom_ _ hax'
    | .onePremise rule t => by
      simp only [FOLKProofTree.varNotOccurs] at hNO
      rcases hNO with ⟨hRuleNO, hTreeNO⟩
      have transformedTree := transform z c formulaComm freeAfterConst sequentFreshAfterConst t hTreeNO
      exact folkConst_oneRule L z c formulaComm freeAfterConst sequentFreshAfterConst _ _ rule hRuleNO transformedTree
    | .twoPremise rule t₁ t₂ => by
      simp only [FOLKProofTree.varNotOccurs] at hNO
      rcases hNO with ⟨_, hTree₁NO, hTree₂NO⟩
      have transformedTree₁ := transform z c formulaComm freeAfterConst sequentFreshAfterConst t₁ hTree₁NO
      have transformedTree₂ := transform z c formulaComm freeAfterConst sequentFreshAfterConst t₂ hTree₂NO
      exact folkConst_twoRule L z c _ _ _ rule transformedTree₁ transformedTree₂
  termination_by structural U


-- Regression probes for the proof-wide premises above. The quantified
-- formula is closed, so its instantiating term disappears from both indexed
-- sequents and survives only as an `allLeft` rule annotation.
-- ATTACH-BLOCKER: private declaration
private def substSignatureProbeLanguage : Language where
  funSymbols := Empty
  funArity := fun e => e.elim
  constSymbols := Unit
  predSymbols := Unit
  predArity := fun _ => 1
  hasEquality := false

-- ATTACH-BLOCKER: private declaration
private def substSignatureProbeAtom : FormulaN substSignatureProbeLanguage :=
  .predN () (fun _ => .var 1)

-- ATTACH-BLOCKER: private declaration
private def substSignatureProbeInstance
    (t : Term substSignatureProbeLanguage) :
    FormulaN substSignatureProbeLanguage :=
  formulaSubstN substSignatureProbeAtom t 0

-- ATTACH-BLOCKER: private declaration
private def substSignatureProbePrem
    (t : Term substSignatureProbeLanguage) :
    Sequent substSignatureProbeLanguage :=
  Sequent.mk [substSignatureProbeInstance t] [substSignatureProbeInstance t]

-- ATTACH-BLOCKER: private declaration
private def substSignatureProbeConc
    (t : Term substSignatureProbeLanguage) :
    Sequent substSignatureProbeLanguage :=
  Sequent.mk [.all 0 substSignatureProbeAtom] [substSignatureProbeInstance t]

-- ATTACH-BLOCKER: private declaration
private def substSignatureProbeTree
    (t : Term substSignatureProbeLanguage) :
    FOLKProofTree (substSignatureProbeConc t) :=
  .onePremise
    (.allLeft t 0 substSignatureProbeAtom []
      [substSignatureProbeInstance t] (by trivial))
    (.axiom_ (substSignatureProbePrem t)
      ⟨substSignatureProbeInstance t, rfl, rfl⟩)

-- ATTACH-BLOCKER: private declaration
private theorem substSignatureProbeAtomNoVar7 :
    formulaVarNotOccurs substSignatureProbeAtom 7 := by
  constructor
  · change ¬ ∃ _ : Fin 1, 7 = 1
    rintro ⟨_, h⟩
    omega
  · change ¬ False
    exact id

-- ATTACH-BLOCKER: private declaration
private theorem substSignatureProbeAllNoVar7 :
    formulaVarNotOccurs (.all 0 substSignatureProbeAtom) 7 := by
  constructor
  · change ¬ ((∃ _ : Fin 1, 7 = 1) ∧ ¬ 7 = 0)
    rintro ⟨⟨_, h⟩, _⟩
    omega
  · change ¬ (False ∨ 7 = 0)
    intro h
    rcases h with h | h
    · exact h
    · omega

-- ATTACH-BLOCKER: private declaration
private theorem substSignatureProbeInstanceNoVar7 :
    formulaVarNotOccurs (substSignatureProbeInstance (.var 7)) 7 := by
  simpa [substSignatureProbeInstance, substSignatureProbeAtom,
    substSignatureProbeLanguage, formulaSubstN, termSubst] using
      substSignatureProbeAtomNoVar7

-- A constant hidden solely in a rule annotation is still found tree-wide.
-- ATTACH-BLOCKER: unsupported untagged example
example :
    ¬ sequentConstOccurs (substSignatureProbePrem (.const ())) () ∧
    ¬ sequentConstOccurs (substSignatureProbeConc (.const ())) () ∧
    (substSignatureProbeTree (.const ())).constOccurs () := by
  constructor
  · rintro ⟨A, hA, hConst⟩
    rcases List.mem_append.mp hA with hA | hA
    · have hEq : A = substSignatureProbeInstance (.const ()) := by
        simpa [substSignatureProbePrem] using hA
      subst A
      simp [substSignatureProbeInstance, substSignatureProbeAtom,
        substSignatureProbeLanguage, formulaSubstN, termSubst,
        formulaConstOccurs, termConstOccurs] at hConst
    · have hEq : A = substSignatureProbeInstance (.const ()) := by
        simpa [substSignatureProbePrem] using hA
      subst A
      simp [substSignatureProbeInstance, substSignatureProbeAtom,
        substSignatureProbeLanguage, formulaSubstN, termSubst,
        formulaConstOccurs, termConstOccurs] at hConst
  constructor
  · rintro ⟨A, hA, hConst⟩
    rcases List.mem_append.mp hA with hA | hA
    · have hEq : A = FormulaN.all 0 substSignatureProbeAtom := by
        simpa [substSignatureProbeConc] using hA
      subst A
      simp [substSignatureProbeAtom, substSignatureProbeLanguage,
        formulaConstOccurs, termConstOccurs] at hConst
    · have hEq : A = substSignatureProbeInstance (.const ()) := by
        simpa [substSignatureProbeConc] using hA
      subst A
      simp [substSignatureProbeInstance, substSignatureProbeAtom,
        substSignatureProbeLanguage, formulaSubstN, termSubst,
        formulaConstOccurs, termConstOccurs] at hConst
  · simp [substSignatureProbeTree, substSignatureProbePrem,
      substSignatureProbeConc, substSignatureProbeInstance,
      substSignatureProbeAtom, substSignatureProbeLanguage,
      FOLKProofTree.constOccurs, FOLKStep1.constOccurs,
      sequentConstOccurs, formulaConstOccurs, termConstOccurs,
      formulaSubstN, termSubst]

-- Likewise, a target variable hidden in the annotation defeats freshness.
-- ATTACH-BLOCKER: unsupported untagged example
example :
    sequentVarNotOccurs (substSignatureProbePrem (.var 7)) 7 ∧
    sequentVarNotOccurs (substSignatureProbeConc (.var 7)) 7 ∧
    ¬ (substSignatureProbeTree (.var 7)).varNotOccurs 7 := by
  constructor
  · intro A hA
    rcases List.mem_append.mp hA with hA | hA
    · have hEq : A = substSignatureProbeInstance (.var 7) := by
        simpa [substSignatureProbePrem] using hA
      subst A
      exact substSignatureProbeInstanceNoVar7
    · have hEq : A = substSignatureProbeInstance (.var 7) := by
        simpa [substSignatureProbePrem] using hA
      subst A
      exact substSignatureProbeInstanceNoVar7
  constructor
  · intro A hA
    rcases List.mem_append.mp hA with hA | hA
    · have hEq : A = FormulaN.all 0 substSignatureProbeAtom := by
        simpa [substSignatureProbeConc] using hA
      subst A
      exact substSignatureProbeAllNoVar7
    · have hEq : A = substSignatureProbeInstance (.var 7) := by
        simpa [substSignatureProbeConc] using hA
      subst A
      exact substSignatureProbeInstanceNoVar7
  · intro h
    change
      FOLKStep1.varNotOccurs
          (.allLeft (.var 7) 0 substSignatureProbeAtom []
            [substSignatureProbeInstance (.var 7)] (by trivial)) 7 ∧
        FOLKProofTree.varNotOccurs
          (.axiom_ (substSignatureProbePrem (.var 7))
            ⟨substSignatureProbeInstance (.var 7), rfl, rfl⟩) 7 at h
    have hTerm : 7 ∉ termFV
        (Term.var 7 : Term substSignatureProbeLanguage) :=
      h.1.2.2.1
    apply hTerm
    change 7 = 7
    rfl

-- ===================================================================
-- Substitution helper lemmas (preserved — these are pure formula/term lemmas)
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem termSubst_var_comm {L : Language}
    (s t : Term L) (x y z : Nat) (hxy : x ≠ y) (hzx : z ≠ x) :
    termSubst (termSubst s t x) (.var z) y =
    termSubst (termSubst s (.var z) y) (termSubst t (.var z) y) x := by
-- BEGIN PROOF
  induction s with
  | var v =>
    simp only [termSubst]
    by_cases hvx : v = x <;> by_cases hvy : v = y <;> simp_all [termSubst]
  | const c => simp [termSubst]
  | func f ts ih => simp only [termSubst]; congr 1; ext i; exact ih i

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem formulaSubst_var_comm {L : Language}
    (A : FormulaN L) (t : Term L) (x y z : Nat) (hxy : x ≠ y) (hzx : z ≠ x)
    (hNB : ¬ formulaBVN A y) :
    formulaSubstN (formulaSubstN A t x) (.var z) y =
    formulaSubstN (formulaSubstN A (.var z) y) (termSubst t (.var z) y) x := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    simp [formulaSubstN]; congr 1; ext i; exact termSubst_var_comm _ _ _ _ _ hxy hzx
  | eq_ _ t1 t2 => simp [formulaSubstN, termSubst_var_comm _ _ _ _ _ hxy hzx]
  | conj A B ihA ihB =>
    simp [formulaSubstN, ihA (fun h => hNB (Or.inl h)), ihB (fun h => hNB (Or.inr h))]
  | disj A B ihA ihB =>
    simp [formulaSubstN, ihA (fun h => hNB (Or.inl h)), ihB (fun h => hNB (Or.inr h))]
  | impl A B ihA ihB =>
    simp [formulaSubstN, ihA (fun h => hNB (Or.inl h)), ihB (fun h => hNB (Or.inr h))]
  | neg A ih => simp [formulaSubstN, ih hNB]
  | all w A ih =>
    have hA : ¬ formulaBVN A y := fun h => hNB (Or.inl h)
    have hyw : y ≠ w := fun h => hNB (Or.inr (h ▸ rfl))
    by_cases hxw : x = w
    · subst hxw; simp [formulaSubstN, hyw]
    · simp [formulaSubstN, hxw, hyw, ih hA]
  | ex w A ih =>
    have hA : ¬ formulaBVN A y := fun h => hNB (Or.inl h)
    have hyw : y ≠ w := fun h => hNB (Or.inr (h ▸ rfl))
    by_cases hxw : x = w
    · subst hxw; simp [formulaSubstN, hyw]
    · simp [formulaSubstN, hxw, hyw, ih hA]

-- Term free variables are preserved or mapped under variable substitution.
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem termFV_termSubst_var {L : Language}
    (s : Term L) (y z w : Nat) (hwz : w ≠ z)
    (h : w ∉ termFV s) :
    w ∉ termFV (termSubst s (.var z) y) := by
-- BEGIN PROOF
  induction s with
  | var v =>
    simp only [termSubst]; split
    · simp [termFV]; exact hwz
    · exact h
  | const c => exact h
  | func f ts ih =>
    simp only [termSubst, termFV] at h ⊢
    intro ⟨i, hi⟩
    exact h ⟨i, (ih i (fun hc => h ⟨i, hc⟩)).elim hi⟩

-- isFreeForN for a variable that doesn't appear bound in A.
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem isFreeFor_var_notBV {L : Language}
    (A : FormulaN L) (x z : Nat) (hNoBV : ¬ formulaBVN A z) :
    isFreeForN (.var z) x A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => trivial
  | eq_ _ _ => trivial
  | conj A B ihA ihB =>
    exact ⟨ihA (fun h => hNoBV (Or.inl h)), ihB (fun h => hNoBV (Or.inr h))⟩
  | disj A B ihA ihB =>
    exact ⟨ihA (fun h => hNoBV (Or.inl h)), ihB (fun h => hNoBV (Or.inr h))⟩
  | impl A B ihA ihB =>
    exact ⟨ihA (fun h => hNoBV (Or.inl h)), ihB (fun h => hNoBV (Or.inr h))⟩
  | neg A ih => exact ih hNoBV
  | all y A ih =>
    simp only [isFreeForN]
    by_cases hxy : x = y
    · exact Or.inl hxy
    · right
      have hzy : z ≠ y := fun h => hNoBV (Or.inr (h ▸ rfl))
      exact ⟨fun hmem => hzy hmem.symm, ih (fun h => hNoBV (Or.inl h))⟩
  | ex y A ih =>
    simp only [isFreeForN]
    by_cases hxy : x = y
    · exact Or.inl hxy
    · right
      have hzy : z ≠ y := fun h => hNoBV (Or.inr (h ▸ rfl))
      exact ⟨fun hmem => hzy hmem.symm, ih (fun h => hNoBV (Or.inl h))⟩

-- isFreeForN preservation under variable substitution.
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem isFreeFor_var_subst {L : Language}
    (A : FormulaN L) (t : Term L) (x y z : Nat) (hxy : x ≠ y) (hzx : z ≠ x)
    (hfree : isFreeForN t x A) (hNB : ¬ formulaBVN A y) (hNoZ : ¬ formulaBVN A z) :
    isFreeForN (termSubst t (.var z) y) x (formulaSubstN A (.var z) y) := by
-- BEGIN PROOF
  induction A with
  | predN P ts => trivial
  | eq_ _ t1 t2 => trivial
  | conj A B ihA ihB =>
    exact ⟨ihA hfree.1 (fun h => hNB (Or.inl h)) (fun h => hNoZ (Or.inl h)),
           ihB hfree.2 (fun h => hNB (Or.inr h)) (fun h => hNoZ (Or.inr h))⟩
  | disj A B ihA ihB =>
    exact ⟨ihA hfree.1 (fun h => hNB (Or.inl h)) (fun h => hNoZ (Or.inl h)),
           ihB hfree.2 (fun h => hNB (Or.inr h)) (fun h => hNoZ (Or.inr h))⟩
  | impl A B ihA ihB =>
    exact ⟨ihA hfree.1 (fun h => hNB (Or.inl h)) (fun h => hNoZ (Or.inl h)),
           ihB hfree.2 (fun h => hNB (Or.inr h)) (fun h => hNoZ (Or.inr h))⟩
  | neg A ih => exact ih hfree hNB hNoZ
  | all w A ih =>
    have hyw : y ≠ w := fun h => hNB (Or.inr (h ▸ rfl))
    have hzw : z ≠ w := fun h => hNoZ (Or.inr (h ▸ rfl))
    simp only [formulaSubstN, show (y != w) = true from by simp [hyw], ite_true, isFreeForN]
    simp only [isFreeForN] at hfree
    rcases hfree with hxw | ⟨hwtv, hff⟩
    · left; exact hxw
    · right; exact ⟨termFV_termSubst_var t y z w (Ne.symm hzw) hwtv,
                    ih hff (fun h => hNB (Or.inl h)) (fun h => hNoZ (Or.inl h))⟩
  | ex w A ih =>
    have hyw : y ≠ w := fun h => hNB (Or.inr (h ▸ rfl))
    have hzw : z ≠ w := fun h => hNoZ (Or.inr (h ▸ rfl))
    simp only [formulaSubstN, show (y != w) = true from by simp [hyw], ite_true, isFreeForN]
    simp only [isFreeForN] at hfree
    rcases hfree with hxw | ⟨hwtv, hff⟩
    · left; exact hxw
    · right; exact ⟨termFV_termSubst_var t y z w (Ne.symm hzw) hwtv,
                    ih hff (fun h => hNB (Or.inl h)) (fun h => hNoZ (Or.inl h))⟩

-- Term-level: constant substitution commutes with variable substitution.
-- retained: used by LCS.CutElim.Interpolation.InterpolantRepair, LCS.CutElim.Interpolation.RuleSubstitution
theorem termSubstConst_termSubst_comm {L : Language}
    (s t : Term L) (x : Nat) (z : Nat) (c : L.constSymbols) (hzx : z ≠ x) :
    termSubstConst (termSubst s t x) z c =
    termSubst (termSubstConst s z c) (termSubstConst t z c) x := by
-- BEGIN PROOF
  induction s with
  | var v =>
    simp only [termSubst]
    by_cases hvx : v = x <;> simp_all [termSubstConst, termSubst]
  | const c' =>
    simp only [termSubst, termSubstConst]
    by_cases hcc : c' = c
    · subst hcc; simp [termSubst, hzx]
    · simp [termSubst, termSubstConst, hcc]
  | func f ts ih => simp only [termSubst, termSubstConst]; congr 1; ext i; exact ih i

-- Constant substitution commutes with variable substitution in formulas.
-- retained: used by LCS.CutElim.Interpolation.InterpolantRepair, LCS.CutElim.Interpolation.RuleSubstitution
theorem formulaSubstConst_formulaSubst_comm {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) (z : Nat) (c : L.constSymbols) (hzx : z ≠ x) :
    formulaSubstConst (formulaSubstN A t x) z c =
    formulaSubstN (formulaSubstConst A z c) (termSubstConst t z c) x := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    simp [formulaSubstN, formulaSubstConst]; congr 1; ext i
    exact termSubstConst_termSubst_comm _ _ _ _ _ hzx
  | eq_ _ t1 t2 =>
    simp [formulaSubstN, formulaSubstConst,
      termSubstConst_termSubst_comm t1 t x z c hzx,
      termSubstConst_termSubst_comm t2 t x z c hzx]
  | conj A B ihA ihB => simp [formulaSubstN, formulaSubstConst, ihA, ihB]
  | disj A B ihA ihB => simp [formulaSubstN, formulaSubstConst, ihA, ihB]
  | impl A B ihA ihB => simp [formulaSubstN, formulaSubstConst, ihA, ihB]
  | neg A ih => simp [formulaSubstN, formulaSubstConst, ih]
  | all w A ih => simp [formulaSubstN, formulaSubstConst]; split <;> simp [formulaSubstConst, ih]
  | ex w A ih => simp [formulaSubstN, formulaSubstConst]; split <;> simp [formulaSubstConst, ih]

-- termFV is mapped under constant substitution: only gains z.
-- retained: used by LCS.CutElim.Interpolation.InterpolantRepair, LCS.CutElim.Interpolation.RuleSubstitution, LCS.CutElim.Interpolation.VariableSubstitution
theorem termFV_termSubstConst {L : Language}
    (s : Term L) (z w : Nat) (c : L.constSymbols) (hwz : w ≠ z)
    (h : w ∉ termFV s) :
    w ∉ termFV (termSubstConst s z c) := by
-- BEGIN PROOF
  induction s with
  | var v => exact h
  | const c' =>
    simp only [termSubstConst]; split
    · simp [termFV]; exact hwz
    · exact fun hm => h hm
  | func f ts ih =>
    simp only [termSubstConst, termFV] at h ⊢
    intro ⟨i, hi⟩; exact h ⟨i, (ih i (fun hc => h ⟨i, hc⟩)).elim hi⟩

-- isFreeForN is preserved under constant substitution.
-- retained: used by LCS.CutElim.Interpolation.InterpolantRepair, LCS.CutElim.Interpolation.RuleSubstitution
theorem isFreeFor_constSubst {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) (z : Nat) (c : L.constSymbols)
    (hfree : isFreeForN t x A) (hNoZ : ¬ formulaBVN A z) :
    isFreeForN (termSubstConst t z c) x (formulaSubstConst A z c) := by
-- BEGIN PROOF
  induction A with
  | predN P ts => trivial
  | eq_ _ t1 t2 => trivial
  | conj A B ihA ihB =>
    exact ⟨ihA hfree.1 (fun h => hNoZ (Or.inl h)),
           ihB hfree.2 (fun h => hNoZ (Or.inr h))⟩
  | disj A B ihA ihB =>
    exact ⟨ihA hfree.1 (fun h => hNoZ (Or.inl h)),
           ihB hfree.2 (fun h => hNoZ (Or.inr h))⟩
  | impl A B ihA ihB =>
    exact ⟨ihA hfree.1 (fun h => hNoZ (Or.inl h)),
           ihB hfree.2 (fun h => hNoZ (Or.inr h))⟩
  | neg A ih => exact ih hfree hNoZ
  | all w A ih =>
    simp only [formulaSubstConst, isFreeForN]
    simp only [isFreeForN] at hfree
    rcases hfree with hxw | ⟨hwtv, hff⟩
    · left; exact hxw
    · have hzw : z ≠ w := fun h => hNoZ (Or.inr (h ▸ rfl))
      right; exact ⟨termFV_termSubstConst t z w c (Ne.symm hzw) hwtv,
                    ih hff (fun h => hNoZ (Or.inl h))⟩
  | ex w A ih =>
    simp only [formulaSubstConst, isFreeForN]
    simp only [isFreeForN] at hfree
    rcases hfree with hxw | ⟨hwtv, hff⟩
    · left; exact hxw
    · have hzw : z ≠ w := fun h => hNoZ (Or.inr (h ▸ rfl))
      right; exact ⟨termFV_termSubstConst t z w c (Ne.symm hzw) hwtv,
                    ih hff (fun h => hNoZ (Or.inl h))⟩

-- formulaFVN under constant substitution
-- retained: used by LCS.CutElim.Interpolation.InterpolantRepair, LCS.CutElim.Interpolation.RuleSubstitution, LCS.CutElim.Interpolation.VariableSubstitution
theorem formulaFV_formulaSubstConst {L : Language}
    (A : FormulaN L) (z : Nat) (c : L.constSymbols) (v : Nat) (hvz : v ≠ z)
    (h : v ∉ formulaFVN A) :
    v ∉ formulaFVN (formulaSubstConst A z c) := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro ⟨i, hi⟩; exact h ⟨i, termFV_termSubstConst (ts i) z v c hvz (fun hm => h ⟨i, hm⟩) |>.elim hi⟩
  | eq_ _ t1 t2 =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro hm; rcases hm with h1 | h2
    · exact (termFV_termSubstConst t1 z v c hvz (fun hm => h (Or.inl hm))).elim h1
    · exact (termFV_termSubstConst t2 z v c hvz (fun hm => h (Or.inr hm))).elim h2
  | conj A B ihA ihB =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro hm; rcases hm with h1 | h2
    · exact ihA (fun hm => h (Or.inl hm)) h1
    · exact ihB (fun hm => h (Or.inr hm)) h2
  | disj A B ihA ihB =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro hm; rcases hm with h1 | h2
    · exact ihA (fun hm => h (Or.inl hm)) h1
    · exact ihB (fun hm => h (Or.inr hm)) h2
  | impl A B ihA ihB =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro hm; rcases hm with h1 | h2
    · exact ihA (fun hm => h (Or.inl hm)) h1
    · exact ihB (fun hm => h (Or.inr hm)) h2
  | neg A ih =>
    simp only [formulaSubstConst, formulaFVN]; exact ih h
  | all w A ih =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro ⟨hm, hne⟩; exact ih (fun hm' => h ⟨hm', hne⟩) hm
  | ex w A ih =>
    simp only [formulaSubstConst, formulaFVN] at h ⊢
    intro ⟨hm, hne⟩; exact ih (fun hm' => h ⟨hm', hne⟩) hm

-- formulaBVN under constant substitution is identity


-- BV(A[t/x]) = BV(A)
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem formulaBV_formulaSubst {L : Language} (A : FormulaN L) (t : Term L) (x : Nat) :
    formulaBVN (formulaSubstN A t x) = formulaBVN A := by
-- BEGIN PROOF
  induction A with
  | predN P ts => rfl
  | eq_ _ t1 t2 => rfl
  | conj A B ihA ihB => simp only [formulaSubstN, formulaBVN, ihA, ihB]
  | disj A B ihA ihB => simp only [formulaSubstN, formulaBVN, ihA, ihB]
  | impl A B ihA ihB => simp only [formulaSubstN, formulaBVN, ihA, ihB]
  | neg A ih => simp only [formulaSubstN, formulaBVN, ih]
  | all w A ih =>
    simp only [formulaSubstN, formulaBVN]
    split <;> simp only [formulaBVN, ih]
  | ex w A ih =>
    simp only [formulaSubstN, formulaBVN]
    split <;> simp only [formulaBVN, ih]

-- Helper: (.var x) is always free for x in any formula.
-- retained: used by LCS.CutElim.Interpolation.Equality.Axioms, LCS.CutElim.Interpolation.InterpolantRepair, LCS.Herbrand.HerbrandTheorem.Part2
theorem isFreeForN_var_self {L : Language} (A : FormulaN L) (x : Nat) :
    isFreeForN (.var x) x A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => trivial
  | eq_ _ _ => trivial
  | conj A B ihA ihB => exact ⟨ihA, ihB⟩
  | disj A B ihA ihB => exact ⟨ihA, ihB⟩
  | impl A B ihA ihB => exact ⟨ihA, ihB⟩
  | neg A ih => exact ih
  | all y A ih =>
    show x = y ∨ _
    by_cases h : x = y
    · exact .inl h
    · exact .inr ⟨fun heq => h (by
        simp only [termFV] at heq; exact heq.symm), ih⟩
  | ex y A ih =>
    show x = y ∨ _
    by_cases h : x = y
    · exact .inl h
    · exact .inr ⟨fun heq => h (by
        simp only [termFV] at heq; exact heq.symm), ih⟩

-- Helper: if v ∉ termFV t and v ≠ z, then v ∉ termFV (termSubst t (.var z) y)
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem termFV_termSubst_ne {L : Language}
    (t : Term L) (y z v : Nat) (hNotFree : v ∉ termFV t) (hNeZ : v ≠ z) :
    v ∉ termFV (termSubst t (.var z) y) := by
-- BEGIN PROOF
  induction t with
  | var w =>
    simp only [termSubst]; split
    · rename_i heq; exact hNeZ
    · exact hNotFree
  | const c => exact hNotFree
  | func f ts ih =>
    simp only [termSubst, termFV] at hNotFree ⊢
    intro ⟨i, hi⟩; exact ih i (fun hm => hNotFree ⟨i, hm⟩) hi

-- Helper: if v ∉ FV(F) and v ≠ z, then v ∉ FV(F[z/y])
-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem formulaFV_formulaSubst_ne {L : Language}
    (F : FormulaN L) (y z v : Nat) (hNotFree : v ∉ formulaFVN F) (hNeZ : v ≠ z) :
    v ∉ formulaFVN (formulaSubstN F (.var z) y) := by
-- BEGIN PROOF
  induction F with
  | predN P ts =>
    simp only [formulaSubstN, formulaFVN] at hNotFree ⊢
    intro ⟨i, hi⟩; exact hNotFree ⟨i, (termFV_termSubst_ne _ y z v (fun hm => hNotFree ⟨i, hm⟩) hNeZ).elim hi⟩
  | eq_ _ t1 t2 =>
    simp only [formulaSubstN, formulaFVN] at hNotFree ⊢
    intro hm; rcases hm with h1 | h2
    · exact (termFV_termSubst_ne t1 y z v (fun hm => hNotFree (Or.inl hm)) hNeZ).elim h1
    · exact (termFV_termSubst_ne t2 y z v (fun hm => hNotFree (Or.inr hm)) hNeZ).elim h2
  | conj A B ihA ihB =>
    simp only [formulaSubstN, formulaFVN] at hNotFree ⊢; intro hm; rcases hm with h1 | h2
    · exact ihA (fun hm => hNotFree (Or.inl hm)) h1
    · exact ihB (fun hm => hNotFree (Or.inr hm)) h2
  | disj A B ihA ihB =>
    simp only [formulaSubstN, formulaFVN] at hNotFree ⊢; intro hm; rcases hm with h1 | h2
    · exact ihA (fun hm => hNotFree (Or.inl hm)) h1
    · exact ihB (fun hm => hNotFree (Or.inr hm)) h2
  | impl A B ihA ihB =>
    simp only [formulaSubstN, formulaFVN] at hNotFree ⊢; intro hm; rcases hm with h1 | h2
    · exact ihA (fun hm => hNotFree (Or.inl hm)) h1
    · exact ihB (fun hm => hNotFree (Or.inr hm)) h2
  | neg A ih => simp only [formulaSubstN, formulaFVN]; exact ih hNotFree
  | all w A ih =>
    simp only [formulaSubstN, formulaFVN] at hNotFree ⊢; split
    · intro ⟨hm, hne⟩; exact ih (fun hm' => hNotFree ⟨hm', hne⟩) hm
    · exact hNotFree
  | ex w A ih =>
    simp only [formulaSubstN, formulaFVN] at hNotFree ⊢; split
    · intro ⟨hm, hne⟩; exact ih (fun hm' => hNotFree ⟨hm', hne⟩) hm
    · exact hNotFree

end LCS.CutElim.Interpolation
end

section
namespace LCS.CutElim.Interpolation
open Classical
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen.Hintikka
section
-- ATTACH-BLOCKER: variable
variable (L : Language) (z y : Nat)

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem folkVar_termSubstVarEqOfNotFree

    : ∀ (t : Term L), ¬y ∈ termFV t → termSubst t (Term.var z) y = t := by
  intro t h
  induction t with
  | var w =>
    simp only [termSubst]
    split
    · rename_i heq
      exact absurd (heq ▸ rfl : y ∈ termFV (Term.var y)) (heq ▸ h)
    · rfl
  | const _ => rfl
  | func f ts ih =>
    simp only [termSubst, Term.func.injEq, heq_eq_eq, true_and]
    funext i
    exact ih i (fun hmem => h ⟨i, hmem⟩)

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem folkVar_formulaSubstVarEqOfNotFree
    (termSubstVarEqOfNotFree : ∀ (t : Term L), ¬y ∈ termFV t → termSubst t (Term.var z) y = t)
    : ∀ (F : FormulaN L), ¬y ∈ formulaFVN F → formulaSubstN F (Term.var z) y = F := by
  intro F h
  induction F with
  | predN P ts =>
    simp only [formulaSubstN, FormulaN.predN.injEq, heq_eq_eq, true_and]
    funext i
    exact termSubstVarEqOfNotFree (ts i) (fun hmem => h ⟨i, hmem⟩)
  | eq_ _ t₁ t₂ =>
    simp only [formulaSubstN, FormulaN.eq_.injEq]
    exact ⟨termSubstVarEqOfNotFree t₁ (fun hm => h (Or.inl hm)),
        termSubstVarEqOfNotFree t₂ (fun hm => h (Or.inr hm))⟩
  | conj A B ihA ihB =>
    simp only [formulaSubstN, FormulaN.conj.injEq]
    exact ⟨ihA (fun hm => h (Or.inl hm)), ihB (fun hm => h (Or.inr hm))⟩
  | disj A B ihA ihB =>
    simp only [formulaSubstN, FormulaN.disj.injEq]
    exact ⟨ihA (fun hm => h (Or.inl hm)), ihB (fun hm => h (Or.inr hm))⟩
  | impl A B ihA ihB =>
    simp only [formulaSubstN, FormulaN.impl.injEq]
    exact ⟨ihA (fun hm => h (Or.inl hm)), ihB (fun hm => h (Or.inr hm))⟩
  | neg A ih =>
    simp only [formulaSubstN, FormulaN.neg.injEq]
    exact ih h
  | all w A ih =>
    simp only [formulaSubstN]
    split
    · simp only [FormulaN.all.injEq, true_and]
      exact ih (fun hm => h ⟨hm, bne_iff_ne.mp ‹y != w›⟩)
    · rfl
  | ex w A ih =>
    simp only [formulaSubstN]
    split
    · simp only [FormulaN.ex.injEq, true_and]
      exact ih (fun hm => h ⟨hm, bne_iff_ne.mp ‹y != w›⟩)
    · rfl

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem folkVar_renamedEigenFresh
    (formulaSubstVarEqOfNotFree : ∀ (F : FormulaN L), ¬y ∈ formulaFVN F → formulaSubstN F (Term.var z) y = F)
      (e : Nat) (F : FormulaN L) (he : ¬e ∈ formulaFVN F) (hz : ¬z ∈ formulaFVN F) (hez : e ≠ z)
    : ¬(if e = y then z else e) ∈ formulaFVN (formulaSubstN F (Term.var z) y) := by
  by_cases hey : e = y
  · subst e
    simp only [if_pos]
    rw [formulaSubstVarEqOfNotFree F he]
    exact hz
  · simp only [if_neg hey]
    exact formulaFV_formulaSubst_ne F y z e he hez

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem folkVar_sequentFreshAfterSubst
    (renamedEigenFresh : ∀ (e : Nat) (F : FormulaN L), ¬e ∈ formulaFVN F → ¬z ∈ formulaFVN F → e ≠ z → ¬(if e
      = y then z else e) ∈ formulaFVN (formulaSubstN F (Term.var z) y)) (q : Sequent L) (e : Nat) (he : ∀ (F :
      FormulaN L), F ∈ q.antecedent ++ q.succedent → ¬e ∈ formulaFVN F) (hz : sequentVarNotOccurs q z) (hez :
      e ≠ z)
    : ∀ (F : FormulaN L), F ∈ (sequentSubstVar q z y).antecedent ++ (sequentSubstVar q z y).succedent → ¬(if e
      = y then z else e) ∈ formulaFVN F := by
  intro F hF
  change F ∈ q.antecedent.map (fun A => formulaSubstN A (.var z) y) ++
      q.succedent.map (fun A => formulaSubstN A (.var z) y) at hF
  rcases List.mem_append.mp hF with hF | hF
  · rcases List.mem_map.mp hF with ⟨G, hG, rfl⟩
    have hmem : G ∈ q.antecedent ++ q.succedent := List.mem_append.mpr (Or.inl hG)
    exact renamedEigenFresh e G (he G hmem) (hz G hmem).1 hez
  · rcases List.mem_map.mp hF with ⟨G, hG, rfl⟩
    have hmem : G ∈ q.antecedent ++ q.succedent := List.mem_append.mpr (Or.inr hG)
    exact renamedEigenFresh e G (he G hmem) (hz G hmem).1 hez

-- ATTACH-BLOCKER: section variables: helper requires front context
def folkVar_allLeft
    (t₀ : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfree :
      isFreeForN t₀ x A) (transformedTree : FOLKProofTree (sequentSubstVar (Sequent.mk (formulaSubstN A t₀ x
      :: Γ) (Δ)) z y)) (hRuleNB : (FOLKStep1.allLeft t₀ x A Γ Δ hfree).notBoundIn y) (hRuleNO :
      (FOLKStep1.allLeft t₀ x A Γ Δ hfree).varNotOccurs z)
    : FOLKProofTree (sequentSubstVar (Sequent.mk (FormulaN.all x A :: Γ) (Δ)) z y) := by
  simp only [FOLKStep1.notBoundIn] at hRuleNB
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hyx : y ≠ x := hRuleNB.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hRuleNB.2.2.2
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (termSubst t₀ (.var z) y) x (formulaSubstN A (.var z) y) :=
    isFreeFor_var_subst A t₀ x y z hxy hzx hfree hNoY hNoZ
  have sub : FOLKProofTree (Sequent.mk (formulaSubstN (formulaSubstN A (.var z) y)
              (termSubst t₀ (.var z) y) x ::
            Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))) := by
    simpa [sequentSubstVar, formulaSubst_var_comm A t₀ x y z hxy hzx hNoY] using transformedTree
  simpa [sequentSubstVar, formulaSubstN, hyx] using FOLKProofTree.onePremise (FOLKStep1.allLeft
        (termSubst t₀ (.var z) y) x
        (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y)) hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
def folkVar_allRight
    (sequentFreshAfterSubst : ∀ (q : Sequent L) (e : Nat), (∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) → sequentVarNotOccurs q z → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstVar q z y).antecedent ++ (sequentSubstVar q z y).succedent → ¬(if e = y then z else e) ∈
      formulaFVN F) (e : Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L))
      (hfresh : ∀ (F : FormulaN L), F ∈ (Γ) ++ (Δ ++ [FormulaN.all x A]) → ¬e ∈ formulaFVN F) (hfree :
      isFreeForN (Term.var e) x A) (transformedTree : FOLKProofTree (sequentSubstVar (Sequent.mk (Γ) (Δ ++
      [formulaSubstN A (Term.var e) x])) z y)) (hRuleNB : (FOLKStep1.allRight e x A Γ Δ hfresh
      hfree).notBoundIn y) (hRuleNO : (FOLKStep1.allRight e x A Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKProofTree (sequentSubstVar (Sequent.mk (Γ) (Δ ++ [FormulaN.all x A])) z y) := by
  simp only [FOLKStep1.notBoundIn] at hRuleNB
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hyx : y ≠ x := hRuleNB.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hze : z ≠ e := hRuleNO.2.2.1
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hRuleNB.2.2.2
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  let e' := if e = y then z else e
  have hterm : termSubst (Term.var e : Term L) (.var z) y = .var e' := by
    by_cases hey : e = y <;> simp [e', termSubst, hey]
  have hfree' : isFreeForN (.var e') x (formulaSubstN A (.var z) y) := by
    by_cases hey : e = y
    · subst e
      have hNoZ' : z ∉ formulaBVN (formulaSubstN A (.var z) y) := by
        rw [formulaBV_formulaSubst]
        exact hNoZ
      simpa [e'] using isFreeFor_var_notBV (formulaSubstN A (.var z) y) x z hNoZ'
    · simpa [e', termSubst, hey] using isFreeFor_var_subst A (.var e) x y z hxy hzx hfree hNoY hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y) ++
              [FormulaN.all x (formulaSubstN A (.var z) y)])).antecedent ++
          (Sequent.mk (Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y) ++
              [FormulaN.all x (formulaSubstN A (.var z) y)])).succedent,
        e' ∉ formulaFVN F := by
    simpa [e', sequentSubstVar, formulaSubstN, hyx] using sequentFreshAfterSubst
        (Sequent.mk Γ (Δ ++ [FormulaN.all x A])) e hfresh
        hRuleNO.2.1 (Ne.symm hze)
  have sub : FOLKProofTree (Sequent.mk (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y) ++ [formulaSubstN (formulaSubstN A (.var z) y)
              (.var e') x])) := by
    simpa [e', sequentSubstVar, hterm, formulaSubst_var_comm A (.var e) x y z hxy hzx hNoY] using
        transformedTree
  simpa [sequentSubstVar, formulaSubstN, hyx] using FOLKProofTree.onePremise (FOLKStep1.allRight e' x
        (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y))
        hfresh' hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
def folkVar_exLeft
    (sequentFreshAfterSubst : ∀ (q : Sequent L) (e : Nat), (∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) → sequentVarNotOccurs q z → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstVar q z y).antecedent ++ (sequentSubstVar q z y).succedent → ¬(if e = y then z else e) ∈
      formulaFVN F) (e : Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L))
      (hfresh : ∀ (F : FormulaN L), F ∈ (FormulaN.ex x A :: Γ) ++ (Δ) → ¬e ∈ formulaFVN F) (hfree : isFreeForN
      (Term.var e) x A) (transformedTree : FOLKProofTree (sequentSubstVar (Sequent.mk (formulaSubstN A
      (Term.var e) x :: Γ) (Δ)) z y)) (hRuleNB : (FOLKStep1.exLeft e x A Γ Δ hfresh hfree).notBoundIn y)
      (hRuleNO : (FOLKStep1.exLeft e x A Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKProofTree (sequentSubstVar (Sequent.mk (FormulaN.ex x A :: Γ) (Δ)) z y) := by
  simp only [FOLKStep1.notBoundIn] at hRuleNB
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hyx : y ≠ x := hRuleNB.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hze : z ≠ e := hRuleNO.2.2.1
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hRuleNB.2.2.2
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  let e' := if e = y then z else e
  have hterm : termSubst (Term.var e : Term L) (.var z) y = .var e' := by
    by_cases hey : e = y <;> simp [e', termSubst, hey]
  have hfree' : isFreeForN (.var e') x (formulaSubstN A (.var z) y) := by
    by_cases hey : e = y
    · subst e
      have hNoZ' : z ∉ formulaBVN (formulaSubstN A (.var z) y) := by
        rw [formulaBV_formulaSubst]
        exact hNoZ
      simpa [e'] using isFreeFor_var_notBV (formulaSubstN A (.var z) y) x z hNoZ'
    · simpa [e', termSubst, hey] using isFreeFor_var_subst A (.var e) x y z hxy hzx hfree hNoY hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (FormulaN.ex x (formulaSubstN A (.var z) y) ::
              Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y))).antecedent ++
          (Sequent.mk (FormulaN.ex x (formulaSubstN A (.var z) y) ::
              Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y))).succedent,
        e' ∉ formulaFVN F := by
    simpa [e', sequentSubstVar, formulaSubstN, hyx] using sequentFreshAfterSubst
        (Sequent.mk (FormulaN.ex x A :: Γ) Δ) e hfresh
        hRuleNO.2.1 (Ne.symm hze)
  have sub : FOLKProofTree (Sequent.mk (formulaSubstN (formulaSubstN A (.var z) y) (.var e') x ::
            Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))) := by
    simpa [e', sequentSubstVar, hterm, formulaSubst_var_comm A (.var e) x y z hxy hzx hNoY] using
        transformedTree
  simpa [sequentSubstVar, formulaSubstN, hyx] using FOLKProofTree.onePremise (FOLKStep1.exLeft e' x
        (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y))
        hfresh' hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
def folkVar_exRight
    (t₀ : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfree :
      isFreeForN t₀ x A) (transformedTree : FOLKProofTree (sequentSubstVar (Sequent.mk (Γ) (Δ ++
      [formulaSubstN A t₀ x])) z y)) (hRuleNB : (FOLKStep1.exRight t₀ x A Γ Δ hfree).notBoundIn y) (hRuleNO :
      (FOLKStep1.exRight t₀ x A Γ Δ hfree).varNotOccurs z)
    : FOLKProofTree (sequentSubstVar (Sequent.mk (Γ) (Δ ++ [FormulaN.ex x A])) z y) := by
  simp only [FOLKStep1.notBoundIn] at hRuleNB
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hyx : y ≠ x := hRuleNB.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hRuleNB.2.2.2
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (termSubst t₀ (.var z) y) x (formulaSubstN A (.var z) y) :=
    isFreeFor_var_subst A t₀ x y z hxy hzx hfree hNoY hNoZ
  have sub : FOLKProofTree (Sequent.mk (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y) ++ [formulaSubstN (formulaSubstN A (.var z) y)
              (termSubst t₀ (.var z) y) x])) := by
    simpa [sequentSubstVar, formulaSubst_var_comm A t₀ x y z hxy hzx hNoY] using transformedTree
  simpa [sequentSubstVar, formulaSubstN, hyx] using FOLKProofTree.onePremise (FOLKStep1.exRight
        (termSubst t₀ (.var z) y) x
        (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y)) hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
def folkVar_oneRule
    (sequentFreshAfterSubst : ∀ (q : Sequent L) (e : Nat), (∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) → sequentVarNotOccurs q z → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstVar q z y).antecedent ++ (sequentSubstVar q z y).succedent → ¬(if e = y then z else e) ∈
      formulaFVN F) (s : Sequent L) (prem : Sequent L) (rule : FOLKStep1 prem s) (hRuleNB : rule.notBoundIn y)
      (hRuleNO : rule.varNotOccurs z) (transformedTree : FOLKProofTree (sequentSubstVar prem z y))
    : FOLKProofTree (sequentSubstVar s z y) := by
  cases rule with
  | weakenLeft A Γ Δ =>
    simpa [sequentSubstVar] using FOLKProofTree.onePremise (FOLKStep1.weakenLeft (formulaSubstN A (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | weakenRight A Γ Δ =>
    simpa [sequentSubstVar] using FOLKProofTree.onePremise (FOLKStep1.weakenRight (formulaSubstN A (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | contractLeft A Γ Δ =>
    simpa [sequentSubstVar] using FOLKProofTree.onePremise
        (FOLKStep1.contractLeft (formulaSubstN A (.var z) y) (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | contractRight A Γ Δ =>
    simpa [sequentSubstVar] using FOLKProofTree.onePremise
        (FOLKStep1.contractRight (formulaSubstN A (.var z) y) (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | exchangeLeft Γ A B Δ Λ =>
    simpa [sequentSubstVar] using FOLKProofTree.onePremise (FOLKStep1.exchangeLeft
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Δ.map (fun F => formulaSubstN F (.var z) y))
          (Λ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | exchangeRight Γ Δ A B Λ =>
    simpa [sequentSubstVar] using FOLKProofTree.onePremise (FOLKStep1.exchangeRight
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Λ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | andLeftL A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKProofTree.onePremise (FOLKStep1.andLeftL
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | andLeftR A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKProofTree.onePremise (FOLKStep1.andLeftR
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | orRightL A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKProofTree.onePremise (FOLKStep1.orRightL
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | orRightR A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKProofTree.onePremise (FOLKStep1.orRightR
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | implRight A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKProofTree.onePremise (FOLKStep1.implRight
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | negLeft A Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKProofTree.onePremise
        (FOLKStep1.negLeft (formulaSubstN A (.var z) y) (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | negRight A Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKProofTree.onePremise
        (FOLKStep1.negRight (formulaSubstN A (.var z) y) (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | allLeft t₀ x A Γ Δ hfree =>
    exact folkVar_allLeft L z y t₀ x A Γ Δ hfree transformedTree hRuleNB hRuleNO
  | allRight e x A Γ Δ hfresh hfree =>
    exact folkVar_allRight L z y sequentFreshAfterSubst e x A Γ Δ hfresh hfree transformedTree hRuleNB hRuleNO
  | exLeft e x A Γ Δ hfresh hfree =>
    exact folkVar_exLeft L z y sequentFreshAfterSubst e x A Γ Δ hfresh hfree transformedTree hRuleNB hRuleNO
  | exRight t₀ x A Γ Δ hfree =>
    exact folkVar_exRight L z y t₀ x A Γ Δ hfree transformedTree hRuleNB hRuleNO

-- ATTACH-BLOCKER: section variables: helper requires front context
def folkVar_twoRule
    (s : Sequent L) (prem1 : Sequent L) (prem2 : Sequent L) (rule : FOLKStep2 prem1 prem2 s) (transformedTree₁
      : FOLKProofTree (sequentSubstVar prem1 z y)) (transformedTree₂ : FOLKProofTree (sequentSubstVar prem2 z
      y))
    : FOLKProofTree (sequentSubstVar s z y) := by
  cases rule with
  | cut A Γ Δ Λ Θ =>
    simpa [sequentSubstVar] using FOLKProofTree.twoPremise (FOLKStep2.cut (formulaSubstN A (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))
          (Λ.map (fun F => formulaSubstN F (.var z) y))
          (Θ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree₁)
        (by simpa [sequentSubstVar] using transformedTree₂)
  | andRight A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKProofTree.twoPremise (FOLKStep2.andRight
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree₁)
        (by simpa [sequentSubstVar] using transformedTree₂)
  | orLeft A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKProofTree.twoPremise (FOLKStep2.orLeft
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree₁)
        (by simpa [sequentSubstVar] using transformedTree₂)
  | implLeft A B Γ Δ Λ Θ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKProofTree.twoPremise (FOLKStep2.implLeft
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))
          (Λ.map (fun F => formulaSubstN F (.var z) y))
          (Θ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree₁)
        (by simpa [sequentSubstVar] using transformedTree₂)

end
end LCS.CutElim.Interpolation
end

section
namespace LCS.CutElim.Interpolation
open Classical
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen.Hintikka

/-- Lemma 6.5.1 (part a — variable substitution): Given an LK-proof T of
Γ → Δ, for any variable y not occurring bound in T and any variable z not
occurring in T, the result T[z/y] of substituting z for all occurrences of
y in T is a proof tree of the substituted sequent. -/
@[blueprint "chap6__lemma_6_5_1"]
def folkProofSubstVar {L : Language} {s : Sequent L}
    (T : LCS.CutElim.LK.FOLKProofTree s) (z y : Nat)
    (hNotBound : T.notBoundIn y) (hNotOccurs : T.varNotOccurs z) :
    LCS.CutElim.LK.FOLKProofTree (sequentSubstVar s z y) := by
  exact transform T z y hNotBound hNotOccurs
where
  transform {L : Language} {s : Sequent L}
      (T : LCS.CutElim.LK.FOLKProofTree s) (z y : Nat)
      (hNotBound : T.notBoundIn y) (hNotOccurs : T.varNotOccurs z) :
      LCS.CutElim.LK.FOLKProofTree (sequentSubstVar s z y) := by
    have termSubstVarEqOfNotFree :
        ∀ t : Term L, y ∉ termFV t → termSubst t (.var z) y = t := by
      exact folkVar_termSubstVarEqOfNotFree L z y
    have formulaSubstVarEqOfNotFree :
        ∀ F : FormulaN L, y ∉ formulaFVN F →
          formulaSubstN F (.var z) y = F := by
      exact folkVar_formulaSubstVarEqOfNotFree L z y termSubstVarEqOfNotFree
    have renamedEigenFresh (e : Nat) (F : FormulaN L)
        (he : e ∉ formulaFVN F) (hz : z ∉ formulaFVN F) (hez : e ≠ z) :
        (if e = y then z else e) ∉
          formulaFVN (formulaSubstN F (.var z) y) := by
      exact folkVar_renamedEigenFresh L z y formulaSubstVarEqOfNotFree e F he hz hez
    have sequentFreshAfterSubst (q : Sequent L) (e : Nat)
        (he : ∀ F ∈ q.antecedent ++ q.succedent, e ∉ formulaFVN F)
        (hz : sequentVarNotOccurs q z) (hez : e ≠ z) :
        ∀ F ∈ (sequentSubstVar q z y).antecedent ++
            (sequentSubstVar q z y).succedent,
          (if e = y then z else e) ∉ formulaFVN F := by
      exact folkVar_sequentFreshAfterSubst L z y renamedEigenFresh q e he hz hez
    exact match T with
    | .axiom_ q hax => by
      have hax' : isFOLKAxiom (sequentSubstVar q z y) := by
        rcases hax with ⟨A, hΓ, hΔ⟩
        exact
          ⟨formulaSubstN A (.var z) y,
            by simp [sequentSubstVar, hΓ],
            by simp [sequentSubstVar, hΔ]⟩
      exact FOLKProofTree.axiom_ _ hax'
    | .onePremise rule t => by
      simp only [FOLKProofTree.notBoundIn] at hNotBound
      simp only [FOLKProofTree.varNotOccurs] at hNotOccurs
      rcases hNotBound with ⟨hRuleNB, hTreeNB⟩
      rcases hNotOccurs with ⟨hRuleNO, hTreeNO⟩
      have transformedTree :=
        transform t z y hTreeNB hTreeNO
      exact folkVar_oneRule L z y sequentFreshAfterSubst _ _ rule hRuleNB hRuleNO transformedTree
    | .twoPremise rule t₁ t₂ => by
      simp only [FOLKProofTree.notBoundIn] at hNotBound
      simp only [FOLKProofTree.varNotOccurs] at hNotOccurs
      rcases hNotBound with ⟨_, hTree₁NB, hTree₂NB⟩
      rcases hNotOccurs with ⟨_, hTree₁NO, hTree₂NO⟩
      have transformedTree₁ :=
        transform t₁ z y hTree₁NB hTree₁NO
      have transformedTree₂ :=
        transform t₂ z y hTree₂NB hTree₂NO
      exact folkVar_twoRule L z y _ _ _ rule transformedTree₁ transformedTree₂
  termination_by structural T

/-- A variable is not bound in an LK deduction tree when it is not bound
in any leaf sequent or rule annotation. -/
@[blueprint "chap6__lemma_6_5_1"]
def _root_.LCS.CutElim.LK.FOLKDeductionTree.notBoundIn {L : Language}
    {hL : L.withoutEquality} :
    {s : Sequent L} → FOLKDeductionTree hL s → Nat → Prop
  | s, .leaf _, y => sequentNotBoundIn s y
  | _, .onePremise rule t, y => rule.notBoundIn y ∧ t.notBoundIn y
  | _, .twoPremise rule t₁ t₂, y =>
      rule.notBoundIn y ∧ t₁.notBoundIn y ∧ t₂.notBoundIn y

/-- A variable does not occur in an LK deduction tree when it occurs in
neither its leaf sequents nor its rule annotations, including eigenvariables
and instantiating terms. -/
@[blueprint "chap6__lemma_6_5_1"]
def _root_.LCS.CutElim.LK.FOLKDeductionTree.varNotOccurs {L : Language}
    {hL : L.withoutEquality} :
    {s : Sequent L} → FOLKDeductionTree hL s → Nat → Prop
  | s, .leaf _, z => sequentVarNotOccurs s z
  | _, .onePremise rule t, z => rule.varNotOccurs z ∧ t.varNotOccurs z
  | _, .twoPremise rule t₁ t₂, z =>
      rule.varNotOccurs z ∧ t₁.varNotOccurs z ∧ t₂.varNotOccurs z

end LCS.CutElim.Interpolation
end

section
namespace LCS.CutElim.Interpolation
open Classical
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen.Hintikka
section
-- ATTACH-BLOCKER: variable
variable (L : Language) (hL : L.withoutEquality) (z y : Nat)

-- ATTACH-BLOCKER: section variables: helper requires front context
def dedVar_allLeft
    (t₀ : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfree :
      isFreeForN t₀ x A) (transformedTree : FOLKDeductionTree hL (sequentSubstVar (Sequent.mk (formulaSubstN A
      t₀ x :: Γ) (Δ)) z y)) (hRuleNB : (FOLKStep1.allLeft t₀ x A Γ Δ hfree).notBoundIn y) (hRuleNO :
      (FOLKStep1.allLeft t₀ x A Γ Δ hfree).varNotOccurs z)
    : FOLKDeductionTree hL (sequentSubstVar (Sequent.mk (FormulaN.all x A :: Γ) (Δ)) z y) := by
  simp only [FOLKStep1.notBoundIn] at hRuleNB
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hyx : y ≠ x := hRuleNB.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hRuleNB.2.2.2
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (termSubst t₀ (.var z) y) x (formulaSubstN A (.var z) y) :=
    isFreeFor_var_subst A t₀ x y z hxy hzx hfree hNoY hNoZ
  have sub : FOLKDeductionTree hL (Sequent.mk (formulaSubstN (formulaSubstN A (.var z) y)
              (termSubst t₀ (.var z) y) x ::
            Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))) := by
    simpa [sequentSubstVar, formulaSubst_var_comm A t₀ x y z hxy hzx hNoY] using transformedTree
  simpa [sequentSubstVar, formulaSubstN, hyx] using FOLKDeductionTree.onePremise (FOLKStep1.allLeft
        (termSubst t₀ (.var z) y) x
        (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y)) hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
def dedVar_allRight
    (sequentFreshAfterSubst : ∀ (q : Sequent L) (e : Nat), (∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) → sequentVarNotOccurs q z → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstVar q z y).antecedent ++ (sequentSubstVar q z y).succedent → ¬(if e = y then z else e) ∈
      formulaFVN F) (e : Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L))
      (hfresh : ∀ (F : FormulaN L), F ∈ (Γ) ++ (Δ ++ [FormulaN.all x A]) → ¬e ∈ formulaFVN F) (hfree :
      isFreeForN (Term.var e) x A) (transformedTree : FOLKDeductionTree hL (sequentSubstVar (Sequent.mk (Γ) (Δ
      ++ [formulaSubstN A (Term.var e) x])) z y)) (hRuleNB : (FOLKStep1.allRight e x A Γ Δ hfresh
      hfree).notBoundIn y) (hRuleNO : (FOLKStep1.allRight e x A Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKDeductionTree hL (sequentSubstVar (Sequent.mk (Γ) (Δ ++ [FormulaN.all x A])) z y) := by
  simp only [FOLKStep1.notBoundIn] at hRuleNB
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hyx : y ≠ x := hRuleNB.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hze : z ≠ e := hRuleNO.2.2.1
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hRuleNB.2.2.2
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  let e' := if e = y then z else e
  have hterm : termSubst (Term.var e : Term L) (.var z) y = .var e' := by
    by_cases hey : e = y <;> simp [e', termSubst, hey]
  have hfree' : isFreeForN (.var e') x (formulaSubstN A (.var z) y) := by
    by_cases hey : e = y
    · subst e
      have hNoZ' : z ∉ formulaBVN (formulaSubstN A (.var z) y) := by
        rw [formulaBV_formulaSubst]
        exact hNoZ
      simpa [e'] using isFreeFor_var_notBV (formulaSubstN A (.var z) y) x z hNoZ'
    · simpa [e', termSubst, hey] using isFreeFor_var_subst A (.var e) x y z hxy hzx hfree hNoY hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y) ++
              [FormulaN.all x (formulaSubstN A (.var z) y)])).antecedent ++
          (Sequent.mk (Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y) ++
              [FormulaN.all x (formulaSubstN A (.var z) y)])).succedent,
        e' ∉ formulaFVN F := by
    simpa [e', sequentSubstVar, formulaSubstN, hyx] using sequentFreshAfterSubst
        (Sequent.mk Γ (Δ ++ [FormulaN.all x A])) e hfresh
        hRuleNO.2.1 (Ne.symm hze)
  have sub : FOLKDeductionTree hL (Sequent.mk (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y) ++ [formulaSubstN (formulaSubstN A (.var z) y)
              (.var e') x])) := by
    simpa [e', sequentSubstVar, hterm, formulaSubst_var_comm A (.var e) x y z hxy hzx hNoY] using
        transformedTree
  simpa [sequentSubstVar, formulaSubstN, hyx] using FOLKDeductionTree.onePremise (FOLKStep1.allRight e' x
        (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y))
        hfresh' hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
def dedVar_exLeft
    (sequentFreshAfterSubst : ∀ (q : Sequent L) (e : Nat), (∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) → sequentVarNotOccurs q z → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstVar q z y).antecedent ++ (sequentSubstVar q z y).succedent → ¬(if e = y then z else e) ∈
      formulaFVN F) (e : Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L))
      (hfresh : ∀ (F : FormulaN L), F ∈ (FormulaN.ex x A :: Γ) ++ (Δ) → ¬e ∈ formulaFVN F) (hfree : isFreeForN
      (Term.var e) x A) (transformedTree : FOLKDeductionTree hL (sequentSubstVar (Sequent.mk (formulaSubstN A
      (Term.var e) x :: Γ) (Δ)) z y)) (hRuleNB : (FOLKStep1.exLeft e x A Γ Δ hfresh hfree).notBoundIn y)
      (hRuleNO : (FOLKStep1.exLeft e x A Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKDeductionTree hL (sequentSubstVar (Sequent.mk (FormulaN.ex x A :: Γ) (Δ)) z y) := by
  simp only [FOLKStep1.notBoundIn] at hRuleNB
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hyx : y ≠ x := hRuleNB.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hze : z ≠ e := hRuleNO.2.2.1
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hRuleNB.2.2.2
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  let e' := if e = y then z else e
  have hterm : termSubst (Term.var e : Term L) (.var z) y = .var e' := by
    by_cases hey : e = y <;> simp [e', termSubst, hey]
  have hfree' : isFreeForN (.var e') x (formulaSubstN A (.var z) y) := by
    by_cases hey : e = y
    · subst e
      have hNoZ' : z ∉ formulaBVN (formulaSubstN A (.var z) y) := by
        rw [formulaBV_formulaSubst]
        exact hNoZ
      simpa [e'] using isFreeFor_var_notBV (formulaSubstN A (.var z) y) x z hNoZ'
    · simpa [e', termSubst, hey] using isFreeFor_var_subst A (.var e) x y z hxy hzx hfree hNoY hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (FormulaN.ex x (formulaSubstN A (.var z) y) ::
              Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y))).antecedent ++
          (Sequent.mk (FormulaN.ex x (formulaSubstN A (.var z) y) ::
              Γ.map (fun G => formulaSubstN G (.var z) y))
            (Δ.map (fun G => formulaSubstN G (.var z) y))).succedent,
        e' ∉ formulaFVN F := by
    simpa [e', sequentSubstVar, formulaSubstN, hyx] using sequentFreshAfterSubst
        (Sequent.mk (FormulaN.ex x A :: Γ) Δ) e hfresh
        hRuleNO.2.1 (Ne.symm hze)
  have sub : FOLKDeductionTree hL (Sequent.mk (formulaSubstN (formulaSubstN A (.var z) y) (.var e') x ::
            Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))) := by
    simpa [e', sequentSubstVar, hterm, formulaSubst_var_comm A (.var e) x y z hxy hzx hNoY] using
        transformedTree
  simpa [sequentSubstVar, formulaSubstN, hyx] using FOLKDeductionTree.onePremise (FOLKStep1.exLeft e' x
        (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y))
        hfresh' hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
def dedVar_exRight
    (t₀ : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfree :
      isFreeForN t₀ x A) (transformedTree : FOLKDeductionTree hL (sequentSubstVar (Sequent.mk (Γ) (Δ ++
      [formulaSubstN A t₀ x])) z y)) (hRuleNB : (FOLKStep1.exRight t₀ x A Γ Δ hfree).notBoundIn y) (hRuleNO :
      (FOLKStep1.exRight t₀ x A Γ Δ hfree).varNotOccurs z)
    : FOLKDeductionTree hL (sequentSubstVar (Sequent.mk (Γ) (Δ ++ [FormulaN.ex x A])) z y) := by
  simp only [FOLKStep1.notBoundIn] at hRuleNB
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hyx : y ≠ x := hRuleNB.2.2.1
  have hxy : x ≠ y := Ne.symm hyx
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoY : y ∉ formulaBVN A := hRuleNB.2.2.2
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (termSubst t₀ (.var z) y) x (formulaSubstN A (.var z) y) :=
    isFreeFor_var_subst A t₀ x y z hxy hzx hfree hNoY hNoZ
  have sub : FOLKDeductionTree hL (Sequent.mk (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y) ++ [formulaSubstN (formulaSubstN A (.var z) y)
              (termSubst t₀ (.var z) y) x])) := by
    simpa [sequentSubstVar, formulaSubst_var_comm A t₀ x y z hxy hzx hNoY] using transformedTree
  simpa [sequentSubstVar, formulaSubstN, hyx] using FOLKDeductionTree.onePremise (FOLKStep1.exRight
        (termSubst t₀ (.var z) y) x
        (formulaSubstN A (.var z) y)
        (Γ.map (fun F => formulaSubstN F (.var z) y))
        (Δ.map (fun F => formulaSubstN F (.var z) y)) hfree')
      sub

-- ATTACH-BLOCKER: section variables: helper requires front context
def dedVar_oneRule
    (sequentFreshAfterSubst : ∀ (q : Sequent L) (e : Nat), (∀ (F : FormulaN L), F ∈ q.antecedent ++
      q.succedent → ¬e ∈ formulaFVN F) → sequentVarNotOccurs q z → e ≠ z → ∀ (F : FormulaN L), F ∈
      (sequentSubstVar q z y).antecedent ++ (sequentSubstVar q z y).succedent → ¬(if e = y then z else e) ∈
      formulaFVN F) (s : Sequent L) (prem : Sequent L) (rule : FOLKStep1 prem s) (hRuleNB : rule.notBoundIn y)
      (hRuleNO : rule.varNotOccurs z) (transformedTree : FOLKDeductionTree hL (sequentSubstVar prem z y))
    : FOLKDeductionTree hL (sequentSubstVar s z y) := by
  cases rule with
  | weakenLeft A Γ Δ =>
    simpa [sequentSubstVar] using FOLKDeductionTree.onePremise
        (FOLKStep1.weakenLeft (formulaSubstN A (.var z) y) (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | weakenRight A Γ Δ =>
    simpa [sequentSubstVar] using FOLKDeductionTree.onePremise
        (FOLKStep1.weakenRight (formulaSubstN A (.var z) y) (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | contractLeft A Γ Δ =>
    simpa [sequentSubstVar] using FOLKDeductionTree.onePremise
        (FOLKStep1.contractLeft (formulaSubstN A (.var z) y) (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | contractRight A Γ Δ =>
    simpa [sequentSubstVar] using FOLKDeductionTree.onePremise
        (FOLKStep1.contractRight (formulaSubstN A (.var z) y) (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | exchangeLeft Γ A B Δ Λ =>
    simpa [sequentSubstVar] using FOLKDeductionTree.onePremise (FOLKStep1.exchangeLeft
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Δ.map (fun F => formulaSubstN F (.var z) y))
          (Λ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | exchangeRight Γ Δ A B Λ =>
    simpa [sequentSubstVar] using FOLKDeductionTree.onePremise (FOLKStep1.exchangeRight
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Λ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | andLeftL A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKDeductionTree.onePremise (FOLKStep1.andLeftL
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | andLeftR A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKDeductionTree.onePremise (FOLKStep1.andLeftR
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | orRightL A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKDeductionTree.onePremise (FOLKStep1.orRightL
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | orRightR A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKDeductionTree.onePremise (FOLKStep1.orRightR
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | implRight A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKDeductionTree.onePremise (FOLKStep1.implRight
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | negLeft A Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKDeductionTree.onePremise
        (FOLKStep1.negLeft (formulaSubstN A (.var z) y) (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | negRight A Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKDeductionTree.onePremise
        (FOLKStep1.negRight (formulaSubstN A (.var z) y) (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree)
  | allLeft t₀ x A Γ Δ hfree =>
    exact dedVar_allLeft L hL z y t₀ x A Γ Δ hfree transformedTree hRuleNB hRuleNO
  | allRight e x A Γ Δ hfresh hfree =>
    exact dedVar_allRight L hL z y sequentFreshAfterSubst e x A Γ Δ hfresh hfree transformedTree hRuleNB hRuleNO
  | exLeft e x A Γ Δ hfresh hfree =>
    exact dedVar_exLeft L hL z y sequentFreshAfterSubst e x A Γ Δ hfresh hfree transformedTree hRuleNB hRuleNO
  | exRight t₀ x A Γ Δ hfree =>
    exact dedVar_exRight L hL z y t₀ x A Γ Δ hfree transformedTree hRuleNB hRuleNO

-- ATTACH-BLOCKER: section variables: helper requires front context
def dedVar_twoRule
    (s : Sequent L) (prem1 : Sequent L) (prem2 : Sequent L) (rule : FOLKStep2 prem1 prem2 s) (transformedTree₁
      : FOLKDeductionTree hL (sequentSubstVar prem1 z y)) (transformedTree₂ : FOLKDeductionTree hL
      (sequentSubstVar prem2 z y))
    : FOLKDeductionTree hL (sequentSubstVar s z y) := by
  cases rule with
  | cut A Γ Δ Λ Θ =>
    simpa [sequentSubstVar] using FOLKDeductionTree.twoPremise (FOLKStep2.cut (formulaSubstN A (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))
          (Λ.map (fun F => formulaSubstN F (.var z) y))
          (Θ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree₁)
        (by simpa [sequentSubstVar] using transformedTree₂)
  | andRight A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKDeductionTree.twoPremise (FOLKStep2.andRight
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree₁)
        (by simpa [sequentSubstVar] using transformedTree₂)
  | orLeft A B Γ Δ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKDeductionTree.twoPremise (FOLKStep2.orLeft
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree₁)
        (by simpa [sequentSubstVar] using transformedTree₂)
  | implLeft A B Γ Δ Λ Θ =>
    simpa [sequentSubstVar, formulaSubstN] using FOLKDeductionTree.twoPremise (FOLKStep2.implLeft
          (formulaSubstN A (.var z) y)
          (formulaSubstN B (.var z) y)
          (Γ.map (fun F => formulaSubstN F (.var z) y))
          (Δ.map (fun F => formulaSubstN F (.var z) y))
          (Λ.map (fun F => formulaSubstN F (.var z) y))
          (Θ.map (fun F => formulaSubstN F (.var z) y)))
        (by simpa [sequentSubstVar] using transformedTree₁)
        (by simpa [sequentSubstVar] using transformedTree₂)

end
end LCS.CutElim.Interpolation
end

