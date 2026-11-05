import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.Partitions
import LCS.CutElim.Interpolation.ConstantSubstitution
import LCS.CutElim.Interpolation.VariableSubstitution
import LCS.CutElim.Interpolation.RuleSubstitution
import LCS.CutElim.Interpolation.InterpolantRepair
import LCS.CutElim.Interpolation.QuantifierCases
import LCS.CutElim.Interpolation.KeyLemma.Cases
import Attach
import LCS.CutElim.Interpolation.KeyLemma.ProofsStamp

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
-- ATTACH-BLOCKER: variable
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem interpolation_key_lemma_wf_exists {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    {s : Sequent L} (t : FOLKBotProofTree botP hBotArity s)
    (hcf : t.isCutFree)
    (p : SequentPartition s) :
    ∃ C : FormulaN L, IsInterpolant botP hBotArity p C := by
  classical
  induction t with
  | axiom_ s hax =>
    exact interpolation_exists_axiom L botP hBotArity s hax p
  | onePremise rule t ih =>
    cases rule with
    | weakenLeft A Γ Δ =>
      exact interpolation_exists_weakenLeft L botP hBotArity A Γ Δ (ih hcf) p
    | weakenRight A Γ Δ =>
      exact interpolation_exists_weakenRight L botP hBotArity A Γ Δ (ih hcf) p
    | contractLeft A Γ Δ =>
      exact interpolation_exists_contractLeft L botP hBotArity A Γ Δ (ih hcf) p
    | contractRight A Γ Δ =>
      exact interpolation_exists_contractRight L botP hBotArity A Γ Δ (ih hcf) p
    | exchangeLeft Γ A B Δ Λ =>
      exact interpolation_exists_exchangeLeft L botP hBotArity Γ A B Δ Λ (ih hcf) p
    | exchangeRight Γ Δ A B Λ =>
      exact interpolation_exists_exchangeRight L botP hBotArity Γ Δ A B Λ (ih hcf) p
    | andLeftL A B Γ Δ =>
      exact interpolation_exists_andLeftL L botP hBotArity A B Γ Δ (ih hcf) p
    | andLeftR A B Γ Δ =>
      exact interpolation_exists_andLeftR L botP hBotArity A B Γ Δ (ih hcf) p
    | orRightL A B Γ Δ =>
      exact interpolation_exists_orRightL L botP hBotArity A B Γ Δ (ih hcf) p
    | orRightR A B Γ Δ =>
      exact interpolation_exists_orRightR L botP hBotArity A B Γ Δ (ih hcf) p
    | implRight A B Γ Δ =>
      exact interpolation_exists_implRight L botP hBotArity A B Γ Δ (ih hcf) p
    | negLeft A Γ Δ =>
      exact interpolation_exists_negLeft L botP hBotArity A Γ Δ (ih hcf) p
    | negRight A Γ Δ =>
      exact interpolation_exists_negRight L botP hBotArity A Γ Δ (ih hcf) p
    | allLeft t₀ x A Γ Δ hfree =>
      exact interpolation_exists_allLeft L botP hBotArity t₀ x A Γ Δ hfree (ih hcf) p
    | allRight y x A Γ Δ hfresh hfree =>
      exact interpolation_exists_allRight L botP hBotArity y x A Γ Δ hfresh hfree (ih hcf) p
    | exLeft y x A Γ Δ hfresh hfree =>
      exact interpolation_exists_exLeft L botP hBotArity y x A Γ Δ hfresh hfree (ih hcf) p
    | exRight t₀ x A Γ Δ hfree =>
      exact interpolation_exists_exRight L botP hBotArity t₀ x A Γ Δ hfree (ih hcf) p
  | twoPremise rule t₁ t₂ ih₁ ih₂ =>
    cases rule with
    | cut A Γ Δ Λ Θ =>
      exact hcf.1.elim
    | andRight A B Γ Δ =>
      exact interpolation_exists_andRight L botP hBotArity A B Γ Δ (ih₁ hcf.2.1) (ih₂ hcf.2.2) p
    | orLeft A B Γ Δ =>
      exact interpolation_exists_orLeft L botP hBotArity A B Γ Δ (ih₁ hcf.2.1) (ih₂ hcf.2.2) p
    | implLeft A B Γ Δ Λ Θ =>
      exact interpolation_exists_implLeft L botP hBotArity A B Γ Δ Λ Θ (ih₁ hcf.2.1) (ih₂ hcf.2.2) p
-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Lemma 6.5.2 (required helper): For any cut-free FOLKBot proof
tree `t` of sequent `s` and any partition `p` of `s`, constructs
an interpolant formula `C`. This is the inductive engine of the
key lemma, operating directly on the proof tree `t` rather than on
an opaque provability hypothesis. -/
noncomputable def interpolation_key_lemma_wf_witness_cutFree {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    {s : Sequent L} (t : FOLKBotProofTree botP hBotArity s)
    (hcf : t.isCutFree)
    (p : SequentPartition s) : FormulaN L :=
  Classical.choose (interpolation_key_lemma_wf_exists t hcf p)

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Spec for `interpolation_key_lemma_wf_witness_cutFree`: the constructed
formula satisfies `IsInterpolant`. -/
theorem interpolation_key_lemma_wf_witness_cutFree_spec {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    {s : Sequent L} (t : FOLKBotProofTree botP hBotArity s)
    (hcf : t.isCutFree)
    (p : SequentPartition s) :
    IsInterpolant botP hBotArity p
      (interpolation_key_lemma_wf_witness_cutFree t hcf p) :=
  Classical.choose_spec (interpolation_key_lemma_wf_exists t hcf p)

-- ===================================================================
-- Lemma 6.5.2: interpolation_key_lemma
-- ===================================================================

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Cut-free LK helper: extract a cut-free LK⊥ proof and use the
inductive interpolant construction. -/
noncomputable def interpolation_key_lemma_witness_cutFree {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    (s : Sequent L)
    (h : folkCutFreeProvable s)
    (p : SequentPartition s) : FormulaN L :=
  let tBot := (folkCutFreeProvable_to_lkBotCutFree botP hBotArity s h).choose
  let hcfBot := (folkCutFreeProvable_to_lkBotCutFree botP hBotArity s h).choose_spec
  interpolation_key_lemma_wf_witness_cutFree tBot hcfBot p

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Spec for `interpolation_key_lemma_witness_cutFree`: the constructed formula
satisfies `IsInterpolant`. -/
theorem interpolation_key_lemma_witness_cutFree_spec {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    (s : Sequent L)
    (h : folkCutFreeProvable s)
    (p : SequentPartition s) :
    IsInterpolant botP hBotArity p
      (@interpolation_key_lemma_witness_cutFree L botP hBotArity s h p) := by
-- BEGIN PROOF
  unfold interpolation_key_lemma_witness_cutFree
  exact interpolation_key_lemma_wf_witness_cutFree_spec
    (folkCutFreeProvable_to_lkBotCutFree botP hBotArity s h).choose
    (folkCutFreeProvable_to_lkBotCutFree botP hBotArity s h).choose_spec p

/-- Lemma 6.5.2: Every LK⊥-provable sequent over a language without
equality has an interpolant for each partition of its formula occurrences.
The interpolant has only common predicate symbols (apart from ⊥), constants,
and free variables. There is no common-function-symbol requirement.
No free/bound-variable convention is required of the original sequent. -/
@[attach_debt, blueprint "chap6__lemma_6_5_2" (main := true)]
theorem interpolation_key_lemma {L : Language} (hL : L.withoutEquality)
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (s : Sequent L) (hProv : lkBotProvable botP hBotArity s)
    (p : SequentPartition s) :
    ∃ C : FormulaN L, IsInterpolant botP hBotArity p C 

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- The LK-provability reading of Lemma 6.5.2. -/
theorem interpolation_key_lemma_lk {L : Language} (hL : L.withoutEquality)
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (s : Sequent L) (hProv : folkProvable s) (p : SequentPartition s) :
    ∃ C : FormulaN L, IsInterpolant botP hBotArity p C :=
  interpolation_key_lemma hL botP hBotArity s
    (folkProvable_to_lkBotProvable botP hBotArity s hProv) p

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Choose the interpolant supplied by Lemma 6.5.2. -/
noncomputable def interpolation_key_lemma_witness {L : Language}
    (hL : L.withoutEquality)
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (s : Sequent L) (hProv : lkBotProvable botP hBotArity s)
    (p : SequentPartition s) : FormulaN L :=
  Classical.choose (interpolation_key_lemma hL botP hBotArity s hProv p)

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- The chosen interpolant satisfies all clauses of Lemma 6.5.2. -/
theorem interpolation_key_lemma_witness_spec {L : Language}
    (hL : L.withoutEquality)
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0)
    (s : Sequent L) (hProv : lkBotProvable botP hBotArity s)
    (p : SequentPartition s) :
    IsInterpolant botP hBotArity p
      (interpolation_key_lemma_witness hL botP hBotArity s hProv p) :=
  Classical.choose_spec (interpolation_key_lemma hL botP hBotArity s hProv p)

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
-- ATTACH-BLOCKER: variable
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
namespace CraigFreshBot

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- The source language with one genuinely fresh nullary predicate adjoined.
Function and constant symbols, all of their arities, and equality are unchanged. -/
def FreshBotLanguage (L : Language) : Language where
  funSymbols := L.funSymbols
  funArity := L.funArity
  constSymbols := L.constSymbols
  predSymbols := Sum L.predSymbols Unit
  predArity
    | .inl P => L.predArity P
    | .inr _ => 0
  hasEquality := L.hasEquality

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- The newly adjoined predicate symbol. -/
def freshBot {L : Language} : (FreshBotLanguage L).predSymbols :=
  .inr ()

-- ATTACH-BLOCKER: section variables: helper requires front context
@[simp]
theorem freshOldPred_arity {L : Language} (P : L.predSymbols) :
    (FreshBotLanguage L).predArity (.inl P) = L.predArity P :=
  rfl

-- ATTACH-BLOCKER: section variables: helper requires front context
@[simp]
theorem freshBot_arity {L : Language} :
    (FreshBotLanguage L).predArity (freshBot (L := L)) = 0 :=
  rfl

-- ATTACH-BLOCKER: section variables: helper requires front context
@[simp]
theorem freshLanguage_withoutEquality {L : Language} :
    (FreshBotLanguage L).withoutEquality ↔ L.withoutEquality :=
  Iff.rfl

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Terms lift structurally because the extension changes no term-forming
symbols. -/
def freshLiftTerm {L : Language} : Term L → Term (FreshBotLanguage L)
  | .var x => .var x
  | .const c => .const c
  | .func f ts => .func f (fun i => freshLiftTerm (ts i))

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Formula lifting injects every old predicate through `Sum.inl`. -/
def freshLiftFormula {L : Language} :
    FormulaN L → FormulaN (FreshBotLanguage L)
  | .predN P ts => .predN (.inl P) (fun i => freshLiftTerm (ts i))
  | .eq_ hL t₁ t₂ => .eq_ hL (freshLiftTerm t₁) (freshLiftTerm t₂)
  | .neg A => .neg (freshLiftFormula A)
  | .conj A B => .conj (freshLiftFormula A) (freshLiftFormula B)
  | .disj A B => .disj (freshLiftFormula A) (freshLiftFormula B)
  | .impl A B => .impl (freshLiftFormula A) (freshLiftFormula B)
  | .all x A => .all x (freshLiftFormula A)
  | .ex x A => .ex x (freshLiftFormula A)

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Pointwise formula lifting for contexts. -/
def freshLiftList {L : Language}
    (fs : List (FormulaN L)) : List (FormulaN (FreshBotLanguage L)) :=
  fs.map freshLiftFormula

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Pointwise lifting of both sides of a sequent. -/
def freshLiftSequent {L : Language}
    (s : Sequent L) : Sequent (FreshBotLanguage L) :=
  { antecedent := freshLiftList s.antecedent
    succedent := freshLiftList s.succedent }

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Terms lower uniquely because the fresh extension has no new term-forming
symbols. -/
def freshLowerTerm {L : Language} : Term (FreshBotLanguage L) → Term L
  | .var x => .var x
  | .const c => .const c
  | .func f ts => .func f (fun i => freshLowerTerm (ts i))

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Lower a formula back to the source language, replacing each occurrence of
the fresh nullary predicate by `R`. -/
def freshLowerFormula {L : Language} (R : FormulaN L) :
    FormulaN (FreshBotLanguage L) → FormulaN L
  | .predN (.inl P) ts =>
      .predN P (fun i => freshLowerTerm (ts i))
  | .predN (.inr _) _ => R
  | .eq_ hL t₁ t₂ => .eq_ hL (freshLowerTerm t₁) (freshLowerTerm t₂)
  | .neg A => .neg (freshLowerFormula R A)
  | .conj A B => .conj (freshLowerFormula R A) (freshLowerFormula R B)
  | .disj A B => .disj (freshLowerFormula R A) (freshLowerFormula R B)
  | .impl A B => .impl (freshLowerFormula R A) (freshLowerFormula R B)
  | .all x A => .all x (freshLowerFormula R A)
  | .ex x A => .ex x (freshLowerFormula R A)

end CraigFreshBot
end LCS.CutElim.Interpolation
end

