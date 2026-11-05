import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.NNFHauptsatz.Renaming
import LCS.Herbrand.NNFHauptsatz.Soundness
import LCS.Herbrand.SharpenedHauptsatz
import LCS.Herbrand.SharpenedHauptsatz.Permutability
import LCS.Herbrand.SharpenedHauptsatz.Theorem
import LCS.Herbrand.PrenexForm
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination
import LCS.Herbrand.NNFHauptsatz.Theorem.VariableSupport
import LCS.Herbrand.NNFHauptsatz.Theorem.Paths
import LCS.Herbrand.NNFHauptsatz.Theorem.Purity
import LCS.Herbrand.NNFHauptsatz.Theorem.RuleOccurrences
import LCS.Herbrand.NNFHauptsatz.Theorem.ExchangeBodies
import LCS.Herbrand.NNFHauptsatz.Theorem.Midsequents
import Attach
import LCS.Herbrand.NNFHauptsatz.Theorem.Example.ProofsStamp

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Soundness
open LCS.Herbrand.SharpenedHauptsatz
open LCS.Herbrand.SharpenedHauptsatz.Permutability
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.Herbrand.PrenexForm
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS.CutElim.LK
namespace LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule
noncomputable section

-- ATTACH-BLOCKER: private declaration
private theorem nnfHauptExVec1_apply
    (t : Term nnfHauptExLang) (i : Fin 1) :
    nnfHauptExVec1 t i = t := by
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  rfl

-- ATTACH-BLOCKER: private declaration
private theorem nnfHauptEx_iUnion_fin_one
    (s : Set Nat) :
    (Set.iUnion fun _ : Fin 1 => s) = s := by
  funext x
  apply propext
  change (∃ _ : Fin 1, x ∈ s) ↔ x ∈ s
  constructor
  · rintro ⟨_, hx⟩
    exact hx
  · intro hx
    exact ⟨0, hx⟩

-- ATTACH-BLOCKER: private declaration
@[simp] private theorem nnfHauptEx_mem_empty_iff_false (x : Nat) :
    x ∈ (∅ : Set Nat) ↔ False := by
  rfl

-- ATTACH-BLOCKER: private declaration
@[simp] private theorem nnfHauptEx_mem_union_iff
    (x : Nat) (s t : Set Nat) :
    x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := by
  rfl

-- ATTACH-BLOCKER: private declaration
@[simp] private theorem nnfHauptEx_mem_diff_iff
    (x : Nat) (s t : Set Nat) :
    x ∈ s \ t ↔ x ∈ s ∧ ¬x ∈ t := by
  rfl

-- ATTACH-BLOCKER: private declaration
@[simp] private theorem nnfHauptEx_mem_singleton_iff
    (x y : Nat) :
    x ∈ Set.singleton y ↔ x = y := by
  rfl

-- ATTACH-BLOCKER: private declaration
private theorem nnfHauptEx_forallYRyRectified :
    isRectified nnfHauptEx_forallYRy := by
  simp [nnfHauptEx_forallYRy, nnfHauptEx_Ry,
    nnfHauptExLang, nnfHauptExVec1_apply, nnfHauptEx_iUnion_fin_one,
    isRectified, boundVarsFresh, distinctQuantifierBindings, formulaFVN,
    formulaBVN, termFV]

-- ATTACH-BLOCKER: private declaration
private theorem nnfHauptEx_QxOrForallYRyRectified :
    isRectified nnfHauptEx_QxOrForallYRy := by
  simp [nnfHauptEx_QxOrForallYRy, nnfHauptEx_forallYRy,
    nnfHauptEx_Ry, nnfHauptExLang, nnfHauptExVec1_apply,
    nnfHauptEx_iUnion_fin_one, isRectified, boundVarsFresh,
    distinctQuantifierBindings, formulaFVN, formulaBVN, termFV]
  change ∀ x : Nat,
    ((∃ j : Fin 1, x ∈ termFV (nnfHauptExVec1 (Term.var 0) j)) ∨
      (∃ j : Fin 1, x ∈ termFV (nnfHauptExVec1 (Term.var 1) j)) ∧ x ≠ 1) → x ≠ 1
  simp [nnfHauptExVec1_apply, termFV]

-- ATTACH-BLOCKER: private declaration
private theorem nnfHauptEx_QaOrForallYRyRectified :
    isRectified (.disj nnfHauptEx_Qa nnfHauptEx_forallYRy) := by
  simp [nnfHauptEx_forallYRy, nnfHauptEx_Ry,
    nnfHauptExLang, nnfHauptExVec1_apply, nnfHauptEx_iUnion_fin_one,
    isRectified, boundVarsFresh, distinctQuantifierBindings, formulaFVN,
    formulaBVN, termFV]
  change ∀ x : Nat,
    ((∃ j : Fin 1, x ∈ termFV (nnfHauptExVec1 (Term.const NNFHauptExConst.a) j)) ∨
      (∃ j : Fin 1, x ∈ termFV (nnfHauptExVec1 (Term.var 1) j)) ∧ x ≠ 1) → x ≠ 1
  simp [nnfHauptExVec1_apply, termFV]

-- ATTACH-BLOCKER: private declaration
private theorem nnfHauptEx_forallXBodyRectified :
    isRectified nnfHauptEx_forallXBody := by
  simp [nnfHauptEx_forallXBody, nnfHauptEx_QxOrForallYRy,
    nnfHauptEx_forallYRy, nnfHauptEx_Ry,
    nnfHauptExLang, nnfHauptExVec1_apply, nnfHauptEx_iUnion_fin_one,
    isRectified, boundVarsFresh, distinctQuantifierBindings, formulaFVN,
    formulaBVN, termFV]
  change ∀ x : Nat,
    ((∃ j : Fin 1, x ∈ termFV (nnfHauptExVec1 (Term.var 0) j)) ∨
      (∃ j : Fin 1, x ∈ termFV (nnfHauptExVec1 (Term.var 1) j)) ∧ x ≠ 1) → x ≠ 0 → x ≠ 1 ∧ x ≠ 0
  simp [nnfHauptExVec1_apply, termFV]

-- ATTACH-BLOCKER: private name in relocated declaration
theorem nnfHauptEx_antFormulaRectified :
    isRectified nnfHauptEx_antFormula := by
  simp [nnfHauptEx_antFormula, nnfHauptEx_forallXBody,
    nnfHauptEx_QxOrForallYRy, nnfHauptEx_forallYRy,
    nnfHauptEx_Ry, nnfHauptExLang, nnfHauptExVec1_apply,
    nnfHauptEx_iUnion_fin_one, isRectified, boundVarsFresh,
    distinctQuantifierBindings, formulaFVN, formulaBVN, termFV]
  change ∀ x : Nat,
    ((∃ j : Fin 1, x ∈ termFV (nnfHauptExVec1 (Term.const NNFHauptExConst.a) j)) ∨
      ((∃ j : Fin 1, x ∈ termFV (nnfHauptExVec1 (Term.var 0) j)) ∨
      (∃ j : Fin 1, x ∈ termFV (nnfHauptExVec1 (Term.var 1) j)) ∧ x ≠ 1) ∧ x ≠ 0) → x ≠ 1 ∧ x ≠ 0
  simp [nnfHauptExVec1_apply, termFV]

-- ATTACH-BLOCKER: private name in relocated declaration
theorem nnfHauptEx_afterFirstInstRectified :
    isRectified nnfHauptEx_afterFirstInst := by
  simp [nnfHauptEx_afterFirstInst, nnfHauptEx_forallYRy,
    nnfHauptEx_Ry, nnfHauptExLang, nnfHauptExVec1_apply,
    nnfHauptEx_iUnion_fin_one, isRectified, boundVarsFresh,
    distinctQuantifierBindings, formulaFVN, formulaBVN, termFV]
  change ∀ x : Nat,
    ((∃ j : Fin 1, x ∈ termFV (nnfHauptExVec1 (Term.const NNFHauptExConst.a) j)) ∨
      (∃ j : Fin 1, x ∈ termFV (nnfHauptExVec1 (Term.var 1) j)) ∧ x ≠ 1) → x ≠ 1
  simp [nnfHauptExVec1_apply, termFV]

-- ATTACH-BLOCKER: private declaration
private theorem nnfHauptExDeltaBaseRectified :
    AllRectified (LCS.Finset.empty, nnfHauptExDeltaBase) :=
  AllRectified.insert_right nnfHauptEx_PaRectified
    (AllRectified.insert_right nnfHauptEx_QaRectified
      AllRectified.empty)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem nnfHauptExDeltaRectified :
    AllRectified (LCS.Finset.empty, nnfHauptExDelta) :=
  AllRectified.insert_right nnfHauptEx_PaRectified
    (AllRectified.insert_right nnfHauptEx_QaRectified
      (AllRectified.insert_right nnfHauptEx_RfaAndRfbRectified
        AllRectified.empty))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem nnfHauptExInsertSelf
    (A : NNFHauptExFormula) (s : NNFHauptExFormulaSet) :
    LCS.Finset.insert A (LCS.Finset.insert A s) =
      LCS.Finset.insert A s := by
  apply LCS.Finset.ext
  intro x
  simp only [LCS.Finset.mem_insert]
  constructor
  · rintro (rfl | rfl | hx)
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr hx
  · rintro (rfl | hx)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr hx)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem nnfHauptExInsertComm
    (A B : NNFHauptExFormula) (s : NNFHauptExFormulaSet) :
    LCS.Finset.insert A (LCS.Finset.insert B s) =
      LCS.Finset.insert B (LCS.Finset.insert A s) := by
  apply LCS.Finset.ext
  intro x
  simp only [LCS.Finset.mem_insert]
  constructor
  · rintro (rfl | rfl | hx)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr hx)
  · rintro (rfl | rfl | hx)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr hx)

-- ATTACH-BLOCKER: private declaration
private theorem nnfHauptExVecSubstSame
    (x : Nat) (t : Term nnfHauptExLang) :
    (fun i => termSubst (nnfHauptExVec1 (Term.var x) i) t x) =
      nnfHauptExVec1 t := by
  funext i
  rcases i with ⟨i, hi⟩
  have hi0 : i = 0 := by omega
  subst i
  simp [nnfHauptExVec1, termSubst]

-- ATTACH-BLOCKER: private declaration
private theorem nnfHauptExVecSubstNe
    (x y : Nat) (hxy : x ≠ y) (t : Term nnfHauptExLang) :
    (fun i => termSubst (nnfHauptExVec1 (Term.var y) i) t x) =
      nnfHauptExVec1 (Term.var y) := by
  funext i
  rcases i with ⟨i, hi⟩
  have hi0 : i = 0 := by omega
  subst i
  simp [nnfHauptExVec1, termSubst, Ne.symm hxy]

-- ATTACH-BLOCKER: private name in relocated declaration
theorem nnfHauptExSubstRy (t : Term nnfHauptExLang) :
    formulaSubstN nnfHauptEx_Ry t 1 =
      FormulaN.predN NNFHauptExPred.R (nnfHauptExVec1 t) := by
  simp only [formulaSubstN, FormulaN.predN.injEq,
    heq_eq_eq, true_and]
  exact congrArg (FormulaN.predN (L := nnfHauptExLang) NNFHauptExPred.R)
    (nnfHauptExVecSubstSame 1 t)

-- ATTACH-BLOCKER: private name in relocated declaration
theorem nnfHauptExSubstQxOr :
    formulaSubstN nnfHauptEx_QxOrForallYRy
        (Term.const NNFHauptExConst.a) 0 =
      FormulaN.disj nnfHauptEx_Qa nnfHauptEx_forallYRy := by
  simp only [nnfHauptEx_Qa, nnfHauptEx_forallYRy,
    formulaSubstN, bne_iff_ne,
    if_pos (show 0 ≠ 1 by omega), FormulaN.disj.injEq,
    FormulaN.all.injEq, FormulaN.predN.injEq, heq_eq_eq,
    true_and]
  exact
    ⟨congrArg (FormulaN.predN (L := nnfHauptExLang) NNFHauptExPred.Q)
      (nnfHauptExVecSubstSame 0 (Term.const NNFHauptExConst.a)),
      congrArg (FormulaN.predN (L := nnfHauptExLang) NNFHauptExPred.R)
        (nnfHauptExVecSubstNe 0 1 (by omega)
          (Term.const NNFHauptExConst.a))⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Extend an explicit finite context list by one formula. -/
theorem nnfHauptExOfListCons (A : NNFHauptExFormula)
    (xs : List NNFHauptExFormula) :
    LCS.Finset.ofList (A :: xs) = LCS.Finset.insert A (LCS.Finset.ofList xs) := by
  apply LCS.Finset.ext
  intro F
  simp only [LCS.Finset.mem_ofList, LCS.Finset.mem_insert, List.mem_cons]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
def nnfHauptExWeakLeft
    (A : NNFHauptExFormula) (hNNF : A.isNNF) (hA : isRectified A)
    {Γ Δ : NNFHauptExFormulaSet}
    (sub : G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality) Γ Δ) :
    G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality) (LCS.Finset.insert A Γ) Δ := by
  have hn := G2nnfDeductionTreeCore.allNNF sub
  exact .onePremise (.weakLeft A Γ Δ) trivial rfl
    ⟨trivial, ⟨(by intro F h; rcases LCS.Finset.mem_insert.mp h with rfl | h; exact hNNF; exact hn.1 F h), hn.2⟩,
      (by intro seq h; simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h; subst seq; exact hn),
      AllRectified.insert_left hA sub.allRectified⟩ sub

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
def nnfHauptExWeakRight
    (A : NNFHauptExFormula) (hNNF : A.isNNF) (hA : isRectified A)
    {Γ Δ : NNFHauptExFormulaSet}
    (sub : G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality) Γ Δ) :
    G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality) Γ (LCS.Finset.insert A Δ) := by
  have hn := G2nnfDeductionTreeCore.allNNF sub
  exact .onePremise (.weakRight A Γ Δ) trivial rfl
    ⟨trivial, ⟨hn.1, (by intro F h; rcases LCS.Finset.mem_insert.mp h with rfl | h; exact hNNF; exact hn.2 F h)⟩,
      (by intro seq h; simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h; subst seq; exact hn),
      AllRectified.insert_right hA sub.allRectified⟩ sub

-- ATTACH-BLOCKER: termination suffix
/-- A bare atomic identity extended by the supplied context lists, in order.
Every added formula carries its NNF and rectification evidence. -/
def nnfHauptExAtomicAx
    (A : NNFHauptExFormula) (hAtom : A.isAtomic)
    (Γ Δ : List NNFHauptExFormula)
    (hNNF : ∀ F, F ∈ Γ ∨ F ∈ Δ → F.isNNF)
    (hRect : ∀ F, F ∈ Γ ∨ F ∈ Δ → isRectified F) :
    G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality)
      (LCS.Finset.insert A (LCS.Finset.ofList Γ))
      (LCS.Finset.insert A (LCS.Finset.ofList Δ)) := by
  match Γ, Δ with
  | [], [] =>
    have hA : A.isNNF := by
      cases A <;> simp_all [FormulaN.isAtomic, FormulaN.isNNF]
    have hn : AllNNF (LCS.Finset.insert A ∅, LCS.Finset.insert A ∅) := by
      constructor <;> intro F h <;>
        rcases LCS.Finset.mem_insert.mp h with rfl | h
      · exact hA
      · exact (LCS.Finset.not_mem_empty h).elim
      · exact hA
      · exact (LCS.Finset.not_mem_empty h).elim
    exact .axiom_ (.axiomPosId A hAtom ∅ ∅) ⟨rfl, rfl⟩ rfl
      ⟨trivial, hn, (by intro seq h; cases h),
        AllRectified.insert_left (AllRectified.isRectified_of_isAtomic A hAtom)
          (AllRectified.insert_right (AllRectified.isRectified_of_isAtomic A hAtom) AllRectified.empty)⟩
  | B :: Γ, Δ =>
    let sub := nnfHauptExAtomicAx A hAtom Γ Δ
      (fun F h => hNNF F (h.elim (fun h => Or.inl (List.mem_cons_of_mem B h)) Or.inr))
      (fun F h => hRect F (h.elim (fun h => Or.inl (List.mem_cons_of_mem B h)) Or.inr))
    exact (nnfHauptExWeakLeft B (hNNF B (Or.inl (List.Mem.head _)))
      (hRect B (Or.inl (List.Mem.head _))) sub).castTree (hL := by rfl)
      (by rw [nnfHauptExOfListCons]; exact nnfHauptExInsertComm B A _) rfl
  | [], B :: Δ =>
    let sub := nnfHauptExAtomicAx A hAtom [] Δ
      (fun F h => hNNF F (h.elim Or.inl (fun h => Or.inr (List.mem_cons_of_mem B h))))
      (fun F h => hRect F (h.elim Or.inl (fun h => Or.inr (List.mem_cons_of_mem B h))))
    exact (nnfHauptExWeakRight B (hNNF B (Or.inr (List.Mem.head _)))
      (hRect B (Or.inr (List.Mem.head _))) sub).castTree (hL := by rfl)
      rfl (by rw [nnfHauptExOfListCons]; exact nnfHauptExInsertComm B A _)
termination_by Γ.length + Δ.length

-- ATTACH-BLOCKER: private declaration
private def nnfHauptExIdentity
    (A : NNFHauptExFormula) (hAtom : A.isAtomic) :
    G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality)
      (LCS.Finset.insert A LCS.Finset.empty)
      (LCS.Finset.insert A LCS.Finset.empty) :=
  nnfHauptExAtomicAx A hAtom [] []
    (by intro F h; rcases h with h | h <;> cases h)
    (by intro F h; rcases h with h | h <;> cases h)

-- ATTACH-BLOCKER: private declaration
private def nnfHauptExAllYToR (t : Term nnfHauptExLang) :
    G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality)
      (LCS.Finset.insert nnfHauptEx_forallYRy LCS.Finset.empty)
      (LCS.Finset.insert (.predN NNFHauptExPred.R (nnfHauptExVec1 t)) LCS.Finset.empty) := by
  let Rt : NNFHauptExFormula := .predN NNFHauptExPred.R (nnfHauptExVec1 t)
  let rule := G2nnfRuleCore.allSubLeft nnfHauptEx_forallYRy
    nnfHauptEx_forallYOccurrence 1 nnfHauptEx_Ry t rfl LCS.Finset.empty (LCS.Finset.insert Rt LCS.Finset.empty)
  have sub : G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality)
      (rule.premises[0]'(by simp [rule, G2nnfRuleCore.premises])).1
      (rule.premises[0]'(by simp [rule, G2nnfRuleCore.premises])).2 := by
    simpa only [rule, G2nnfRuleCore.premises, List.getElem_cons_zero,
      nnfHauptEx_forallYOccurrence, MaxQuantifierOccurrence.replace, nnfHauptExSubstRy, Rt] using
      (nnfHauptExIdentity Rt rfl)
  have hSC : rule.SideConditions :=
    ⟨trivial, (by
      constructor <;> intro F h
      · change F ∈ LCS.Finset.insert nnfHauptEx_forallYRy LCS.Finset.empty at h
        rcases LCS.Finset.mem_insert.mp h with rfl | h
        · trivial
        · exact (LCS.Finset.not_mem_empty h).elim
      · change F ∈ LCS.Finset.insert Rt LCS.Finset.empty at h
        rcases LCS.Finset.mem_insert.mp h with rfl | h
        · trivial
        · exact (LCS.Finset.not_mem_empty h).elim),
      (by intro seq h; simp only [rule, G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
          subst seq; exact G2nnfDeductionTreeCore.allNNF sub),
      AllRectified.insert_left nnfHauptEx_forallYRyRectified
        (AllRectified.insert_right (AllRectified.isRectified_of_isAtomic Rt rfl) AllRectified.empty)⟩
  exact .onePremise rule trivial rfl hSC sub

-- ATTACH-BLOCKER: private declaration
private def nnfHauptExAllYToRfa :
    G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality)
      (LCS.Finset.insert nnfHauptEx_forallYRy LCS.Finset.empty)
      (LCS.Finset.insert nnfHauptEx_Rfa LCS.Finset.empty) :=
  nnfHauptExAllYToR nnfHauptEx_fa

-- ATTACH-BLOCKER: private declaration
private def nnfHauptExAllYToRfb :
    G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality)
      (LCS.Finset.insert nnfHauptEx_forallYRy LCS.Finset.empty)
      (LCS.Finset.insert nnfHauptEx_Rfb LCS.Finset.empty) :=
  nnfHauptExAllYToR nnfHauptEx_fb

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp] theorem nnfHauptExFormula_not_mem_empty (A : NNFHauptExFormula) :
    ¬ A ∈ (LCS.Finset.empty : NNFHauptExFormulaSet) := LCS.Finset.not_mem_empty

-- ===================================================================
-- Example 7.4.4: nnfHauptsatzExTree
-- ===================================================================

/-- Example 7.4.4: The concrete non-normal G2nnf proof tree displayed in
the textbook. Its two `forall y` instantiations occur above a conjunction-right
and disjunction-left inference, and the `forall x` instantiation occurs above
the root disjunction-left inference. Thus quantifier and propositional rules
are interleaved exactly as in the starting proof before normalization. -/
@[blueprint "chap7__example_7_4_4" (main := true)]
def nnfHauptsatzExTree :
    G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality)
      (LCS.Finset.insert nnfHauptEx_antFormula LCS.Finset.empty)
      (LCS.Finset.insert nnfHauptEx_Pa
        (LCS.Finset.insert nnfHauptEx_Qa
          (LCS.Finset.insert nnfHauptEx_RfaAndRfb LCS.Finset.empty))) :=
  by
    let t2Core :
        G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality)
          (LCS.Finset.insert nnfHauptEx_forallYRy LCS.Finset.empty)
          (LCS.Finset.insert nnfHauptEx_RfaAndRfb
            LCS.Finset.empty) :=
      .twoPremise (.conjRight nnfHauptEx_Rfa nnfHauptEx_Rfb (LCS.Finset.insert nnfHauptEx_forallYRy LCS.Finset.empty) LCS.Finset.empty) trivial rfl
        ⟨trivial, (by simp [AllNNF, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises, LCS.Finset.mem_insert, LCS.Finset.not_mem_empty, FormulaN.isNNF]), (by intro seq hs; simp [G2nnfRuleCore.premises] at hs; rcases hs with rfl | rfl <;> simp [AllNNF, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises, LCS.Finset.mem_insert, LCS.Finset.not_mem_empty, FormulaN.isNNF]),
          AllRectified.insert_right nnfHauptEx_RfaAndRfbRectified
            (AllRectified.insert_left nnfHauptEx_forallYRyRectified
              AllRectified.empty)⟩
        nnfHauptExAllYToRfa nnfHauptExAllYToRfb
    let t2 :
        G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality)
          (LCS.Finset.insert nnfHauptEx_forallYRy LCS.Finset.empty)
          (LCS.Finset.insert nnfHauptEx_Qa
            (LCS.Finset.insert nnfHauptEx_RfaAndRfb
              LCS.Finset.empty)) :=
      nnfHauptExWeakRight nnfHauptEx_Qa (by trivial) nnfHauptEx_QaRectified t2Core
    let qaRaw := nnfHauptExWeakRight nnfHauptEx_RfaAndRfb (by trivial)
      nnfHauptEx_RfaAndRfbRectified
      (nnfHauptExIdentity nnfHauptEx_Qa rfl)
    have hQaDelta :
        LCS.Finset.insert nnfHauptEx_RfaAndRfb
            (LCS.Finset.insert nnfHauptEx_Qa LCS.Finset.empty) =
          LCS.Finset.insert nnfHauptEx_Qa
            (LCS.Finset.insert nnfHauptEx_RfaAndRfb
              LCS.Finset.empty) :=
      nnfHauptExInsertComm _ _ _
    let qaBranch :
        G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality)
          (LCS.Finset.insert nnfHauptEx_Qa LCS.Finset.empty)
          (LCS.Finset.insert nnfHauptEx_Qa
            (LCS.Finset.insert nnfHauptEx_RfaAndRfb
              LCS.Finset.empty)) := by
      rw [← hQaDelta]
      exact qaRaw
    let qOrAllY :
        G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality)
          (LCS.Finset.insert
            (FormulaN.disj nnfHauptEx_Qa nnfHauptEx_forallYRy)
            LCS.Finset.empty)
          (LCS.Finset.insert nnfHauptEx_Qa
            (LCS.Finset.insert nnfHauptEx_RfaAndRfb
              LCS.Finset.empty)) :=
      .twoPremise (.disjLeft nnfHauptEx_Qa nnfHauptEx_forallYRy LCS.Finset.empty (LCS.Finset.insert nnfHauptEx_Qa
          (LCS.Finset.insert nnfHauptEx_RfaAndRfb
            LCS.Finset.empty))) trivial
        rfl
        ⟨trivial, (by simp [AllNNF, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises, LCS.Finset.mem_insert, LCS.Finset.not_mem_empty, FormulaN.isNNF]), (by intro seq hs; simp [G2nnfRuleCore.premises] at hs; rcases hs with rfl | rfl <;> simp [AllNNF, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises, LCS.Finset.mem_insert, LCS.Finset.not_mem_empty, FormulaN.isNNF]),
          AllRectified.insert_left nnfHauptEx_QaOrForallYRyRectified
            (AllRectified.insert_right nnfHauptEx_QaRectified
              (AllRectified.insert_right nnfHauptEx_RfaAndRfbRectified
                AllRectified.empty))⟩
        qaBranch t2
    let ruleX :=
      G2nnfRuleCore.allSubLeft nnfHauptEx_forallXBody
        nnfHauptEx_forallXOccurrence 0 nnfHauptEx_QxOrForallYRy
        (Term.const NNFHauptExConst.a) rfl LCS.Finset.empty (LCS.Finset.insert nnfHauptEx_Qa (LCS.Finset.insert nnfHauptEx_RfaAndRfb LCS.Finset.empty))
    have hSCX : ruleX.SideConditions := by
      refine ⟨?_, (by simp [ruleX, AllNNF, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises, LCS.Finset.mem_insert, LCS.Finset.not_mem_empty, FormulaN.isNNF, nnfHauptEx_forallXOccurrence, MaxQuantifierOccurrence.replace, nnfHauptExSubstQxOr]), (by simp [ruleX, AllNNF, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises, LCS.Finset.mem_insert, LCS.Finset.not_mem_empty, FormulaN.isNNF, nnfHauptEx_forallXOccurrence, MaxQuantifierOccurrence.replace, nnfHauptExSubstQxOr]),
        AllRectified.insert_left nnfHauptEx_forallXBodyRectified
          (AllRectified.insert_right nnfHauptEx_QaRectified
            (AllRectified.insert_right nnfHauptEx_RfaAndRfbRectified
              AllRectified.empty))⟩
      · refine ⟨trivial, Or.inr ⟨?_, trivial⟩⟩
        exact nofun
    have xSub :
        G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality)
          ((ruleX.premises)[0]'(
              by simp [ruleX, G2nnfRuleCore.premises])).1
          ((ruleX.premises)[0]'(
              by simp [ruleX, G2nnfRuleCore.premises])).2 := by
      simpa [ruleX, G2nnfRuleCore.premises, nnfHauptEx_forallXOccurrence,
        nnfHauptEx_forallXBody, MaxQuantifierOccurrence.replace,
        nnfHauptExSubstQxOr] using qOrAllY
    let allX :
        G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality)
          (LCS.Finset.insert nnfHauptEx_forallXBody
            LCS.Finset.empty)
          (LCS.Finset.insert nnfHauptEx_Qa
            (LCS.Finset.insert nnfHauptEx_RfaAndRfb
              LCS.Finset.empty)) :=
      .onePremise ruleX trivial
        rfl hSCX xSub
    let t1 := nnfHauptExWeakRight nnfHauptEx_Pa (by trivial)
      nnfHauptEx_PaRectified allX
    let paRaw := nnfHauptExWeakRight nnfHauptEx_RfaAndRfb (by trivial)
      nnfHauptEx_RfaAndRfbRectified
      (nnfHauptExWeakRight nnfHauptEx_Qa (by trivial) nnfHauptEx_QaRectified
        (nnfHauptExIdentity nnfHauptEx_Pa rfl))
    have hPaDelta :
        LCS.Finset.insert nnfHauptEx_RfaAndRfb
            (LCS.Finset.insert nnfHauptEx_Qa
              (LCS.Finset.insert nnfHauptEx_Pa
                LCS.Finset.empty)) =
          nnfHauptExDelta := by
      simp only [nnfHauptExDelta]
      calc
        LCS.Finset.insert nnfHauptEx_RfaAndRfb
            (LCS.Finset.insert nnfHauptEx_Qa
              (LCS.Finset.insert nnfHauptEx_Pa
                LCS.Finset.empty)) =
          LCS.Finset.insert nnfHauptEx_Qa
            (LCS.Finset.insert nnfHauptEx_RfaAndRfb
              (LCS.Finset.insert nnfHauptEx_Pa
                LCS.Finset.empty)) := nnfHauptExInsertComm _ _ _
        _ = LCS.Finset.insert nnfHauptEx_Qa
            (LCS.Finset.insert nnfHauptEx_Pa
              (LCS.Finset.insert nnfHauptEx_RfaAndRfb
                LCS.Finset.empty)) :=
          congrArg (LCS.Finset.insert nnfHauptEx_Qa)
            (nnfHauptExInsertComm _ _ _)
        _ = nnfHauptExDelta := nnfHauptExInsertComm _ _ _
    let paBranch :
        G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality)
          (LCS.Finset.insert nnfHauptEx_Pa LCS.Finset.empty)
          nnfHauptExDelta := by
      rw [← hPaDelta]
      exact paRaw
    exact .twoPremise (.disjLeft nnfHauptEx_Pa nnfHauptEx_forallXBody LCS.Finset.empty nnfHauptExDelta) trivial rfl
      ⟨trivial, (by simp [AllNNF, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises, LCS.Finset.mem_insert, LCS.Finset.not_mem_empty, FormulaN.isNNF]), (by intro seq hs; simp [G2nnfRuleCore.premises] at hs; rcases hs with rfl | rfl <;> simp [AllNNF, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises, LCS.Finset.mem_insert, LCS.Finset.not_mem_empty, FormulaN.isNNF]),
        AllRectified.insert_left nnfHauptEx_antFormulaRectified
          (AllRectified.insert_right nnfHauptEx_PaRectified
            (AllRectified.insert_right nnfHauptEx_QaRectified
              (AllRectified.insert_right nnfHauptEx_RfaAndRfbRectified
                AllRectified.empty)))⟩
      paBranch t1

-- ATTACH-BLOCKER: unsupported untagged abbrev
abbrev nnfHauptExMidGamma : NNFHauptExFormulaSet :=
  LCS.Finset.insert nnfHauptEx_midAnt1
    (LCS.Finset.insert nnfHauptEx_midAnt2 LCS.Finset.empty)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem nnfHauptExInsertOfMem
    (A : NNFHauptExFormula) (s : NNFHauptExFormulaSet)
    (hA : A ∈ s) :
    LCS.Finset.insert A s = s := by
  apply LCS.Finset.ext
  intro x
  rw [LCS.Finset.mem_insert]
  constructor
  · rintro (rfl | hx)
    · exact hA
    · exact hx
  · exact Or.inr

-- ATTACH-BLOCKER: unsupported untagged structure
structure NNFHauptExPropTree
    (Γ Δ : NNFHauptExFormulaSet) where
  tree : G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality) Γ Δ
  allProp : AllRulesPropOrWeakening (hL := by rfl) tree

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
def NNFHauptExPropTree.cast
    {Γ Δ Γ' Δ' : NNFHauptExFormulaSet}
    (p : NNFHauptExPropTree Γ Δ)
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') :
    NNFHauptExPropTree Γ' Δ' :=
  match hΓ, hΔ with
  | rfl, rfl => p

-- ATTACH-BLOCKER: private declaration
private theorem nnfHauptExAllPropCast
    {Γ Δ Γ' Δ' : NNFHauptExFormulaSet}
    (T : G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality) Γ Δ)
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') :
    AllRulesPropOrWeakening (hL := by rfl) (T.castTree (hL := by rfl) hΓ hΔ) ↔
      AllRulesPropOrWeakening (hL := by rfl) T := by
  cases hΓ
  cases hΔ
  rfl

-- ATTACH-BLOCKER: termination suffix
theorem nnfHauptExAtomicAx_allProp
    (A : NNFHauptExFormula) (hAtom : A.isAtomic)
    (Γ Δ : List NNFHauptExFormula)
    (hNNF : ∀ F, F ∈ Γ ∨ F ∈ Δ → F.isNNF)
    (hRect : ∀ F, F ∈ Γ ∨ F ∈ Δ → isRectified F) :
    AllRulesPropOrWeakening (hL := by rfl)
      (nnfHauptExAtomicAx A hAtom Γ Δ hNNF hRect) := by
  match Γ, Δ with
  | [], [] => simp only [nnfHauptExAtomicAx, AllRulesPropOrWeakening]
  | B :: Γ, Δ =>
    have ih := nnfHauptExAtomicAx_allProp A hAtom Γ Δ
      (fun F h => hNNF F (h.elim (fun h => Or.inl (List.mem_cons_of_mem B h)) Or.inr))
      (fun F h => hRect F (h.elim (fun h => Or.inl (List.mem_cons_of_mem B h)) Or.inr))
    rw [nnfHauptExAtomicAx]
    apply (nnfHauptExAllPropCast _ _ _).mpr
    exact ⟨Or.inr trivial, ih⟩
  | [], B :: Δ =>
    have ih := nnfHauptExAtomicAx_allProp A hAtom [] Δ
      (fun F h => hNNF F (h.elim Or.inl (fun h => Or.inr (List.mem_cons_of_mem B h))))
      (fun F h => hRect F (h.elim Or.inl (fun h => Or.inr (List.mem_cons_of_mem B h))))
    rw [nnfHauptExAtomicAx]
    apply (nnfHauptExAllPropCast _ _ _).mpr
    exact ⟨Or.inr trivial, ih⟩
termination_by Γ.length + Δ.length

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Certify the same bare identity and explicit context weakenings used by
`nnfHauptExAtomicAx`; the certificate introduces no separate derivation. -/
def nnfHauptExAtomicCert
    (A : NNFHauptExFormula) (hAtom : A.isAtomic)
    (Γ Δ : List NNFHauptExFormula)
    (hNNF : ∀ F, F ∈ Γ ∨ F ∈ Δ → F.isNNF)
    (hRect : ∀ F, F ∈ Γ ∨ F ∈ Δ → isRectified F) :
    NNFHauptExPropTree (LCS.Finset.insert A (LCS.Finset.ofList Γ))
      (LCS.Finset.insert A (LCS.Finset.ofList Δ)) :=
  ⟨nnfHauptExAtomicAx A hAtom Γ Δ hNNF hRect,
    nnfHauptExAtomicAx_allProp A hAtom Γ Δ hNNF hRect⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
def nnfHauptExPaCert
    (Γ : List NNFHauptExFormula)
    (hNNF : ∀ F, F ∈ Γ → F.isNNF)
    (hRect : ∀ F, F ∈ Γ → isRectified F) :
    NNFHauptExPropTree (LCS.Finset.insert nnfHauptEx_Pa (LCS.Finset.ofList Γ)) nnfHauptExDelta :=
  (nnfHauptExAtomicCert nnfHauptEx_Pa rfl Γ
    [nnfHauptEx_RfaAndRfb, nnfHauptEx_Qa, nnfHauptEx_Pa]
    (by intro F h; rcases h with h | h; exact hNNF F h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl <;> trivial)
    (by intro F h; rcases h with h | h; exact hRect F h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl
        exact nnfHauptEx_RfaAndRfbRectified
        exact nnfHauptEx_QaRectified
        exact nnfHauptEx_PaRectified)).cast rfl
      (nnfHauptExInsertOfMem nnfHauptEx_Pa nnfHauptExDelta
        (LCS.Finset.mem_insert.mpr (Or.inl rfl)))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
def nnfHauptExQaCert
    (Γ : List NNFHauptExFormula)
    (hNNF : ∀ F, F ∈ Γ → F.isNNF)
    (hRect : ∀ F, F ∈ Γ → isRectified F) :
    NNFHauptExPropTree (LCS.Finset.insert nnfHauptEx_Qa (LCS.Finset.ofList Γ)) nnfHauptExDelta :=
  (nnfHauptExAtomicCert nnfHauptEx_Qa rfl Γ
    [nnfHauptEx_RfaAndRfb, nnfHauptEx_Qa, nnfHauptEx_Pa]
    (by intro F h; rcases h with h | h; exact hNNF F h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl <;> trivial)
    (by intro F h; rcases h with h | h; exact hRect F h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl
        exact nnfHauptEx_RfaAndRfbRectified
        exact nnfHauptEx_QaRectified
        exact nnfHauptEx_PaRectified)).cast rfl
      (nnfHauptExInsertOfMem nnfHauptEx_Qa nnfHauptExDelta
        (LCS.Finset.mem_insert.mpr
          (Or.inr (LCS.Finset.mem_insert.mpr (Or.inl rfl)))))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
def nnfHauptExDisjCert
    (A B : NNFHauptExFormula) (Γ Δ : NNFHauptExFormulaSet)
    (hDisj : isRectified (.disj A B))
    (left : NNFHauptExPropTree (LCS.Finset.insert A Γ) Δ)
    (right : NNFHauptExPropTree (LCS.Finset.insert B Γ) Δ) :
    NNFHauptExPropTree (LCS.Finset.insert (FormulaN.disj A B) Γ) Δ := by
  have hl := G2nnfDeductionTreeCore.allNNF left.tree
  have hr := G2nnfDeductionTreeCore.allNNF right.tree
  refine ⟨.twoPremise (.disjLeft A B Γ Δ) trivial rfl
    ⟨trivial, ⟨?_, hl.2⟩, ?_,
      AllRectified.insert_left hDisj (AllRectified.of_insert_left left.tree.allRectified)⟩
    left.tree right.tree, ?_⟩
  · intro F h
    rcases LCS.Finset.mem_insert.mp h with rfl | h
    · exact ⟨hl.1 A (LCS.Finset.mem_insert.mpr (Or.inl rfl)),
        hr.1 B (LCS.Finset.mem_insert.mpr (Or.inl rfl))⟩
    · exact hl.1 F (LCS.Finset.mem_insert.mpr (Or.inr h))
  · intro seq h
    simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact hl
    · exact hr
  · simp only [AllRulesPropOrWeakening, G2nnfRuleCore.isPropositionalRule, true_or, true_and]
    exact ⟨left.allProp, right.allProp⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
def nnfHauptExConjCert :
    NNFHauptExPropTree
      (LCS.Finset.insert nnfHauptEx_Rfa
        (LCS.Finset.insert nnfHauptEx_Rfb LCS.Finset.empty))
      nnfHauptExDelta := by
  let Γ :=
    LCS.Finset.insert nnfHauptEx_Rfa
      (LCS.Finset.insert nnfHauptEx_Rfb LCS.Finset.empty)
  let left : NNFHauptExPropTree Γ
      (LCS.Finset.insert nnfHauptEx_Rfa nnfHauptExDeltaBase) :=
    nnfHauptExAtomicCert nnfHauptEx_Rfa rfl
      [nnfHauptEx_Rfb] [nnfHauptEx_Qa, nnfHauptEx_Pa]
      (by intro F h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl | rfl <;> trivial)
      (by intro F h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl | rfl <;> first | exact nnfHauptEx_RfbRectified | exact nnfHauptEx_QaRectified | exact nnfHauptEx_PaRectified)
  let rightRaw := nnfHauptExAtomicCert nnfHauptEx_Rfb rfl
    [nnfHauptEx_Rfa] [nnfHauptEx_Qa, nnfHauptEx_Pa]
      (by intro F h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl | rfl <;> trivial)
      (by intro F h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl | rfl <;> first | exact nnfHauptEx_RfaRectified | exact nnfHauptEx_QaRectified | exact nnfHauptEx_PaRectified)
  let right : NNFHauptExPropTree Γ
      (LCS.Finset.insert nnfHauptEx_Rfb nnfHauptExDeltaBase) :=
    rightRaw.cast
      (nnfHauptExInsertComm nnfHauptEx_Rfb nnfHauptEx_Rfa
        LCS.Finset.empty) rfl
  let raw : NNFHauptExPropTree Γ
      (LCS.Finset.insert nnfHauptEx_RfaAndRfb
        nnfHauptExDeltaBase) :=
    ⟨.twoPremise (.conjRight nnfHauptEx_Rfa nnfHauptEx_Rfb Γ nnfHauptExDeltaBase) trivial rfl
        ⟨trivial,
          (by simp [Γ, nnfHauptExDeltaBase, AllNNF, G2nnfRuleCore.conclusion, LCS.Finset.mem_insert, FormulaN.isNNF]),
          (by intro seq h; simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with rfl | rfl
              exact G2nnfDeductionTreeCore.allNNF left.tree
              exact G2nnfDeductionTreeCore.allNNF right.tree),
          AllRectified.insert_right nnfHauptEx_RfaAndRfbRectified
            (AllRectified.of_insert_right left.tree.allRectified)⟩
        left.tree right.tree,
      (by simp only [AllRulesPropOrWeakening, G2nnfRuleCore.isPropositionalRule, true_or, true_and]; exact ⟨left.allProp, right.allProp⟩)⟩
  have hDelta :
      LCS.Finset.insert nnfHauptEx_RfaAndRfb
          nnfHauptExDeltaBase =
        nnfHauptExDelta := by
    simp only [nnfHauptExDeltaBase, nnfHauptExDelta]
    calc
      LCS.Finset.insert nnfHauptEx_RfaAndRfb
          (LCS.Finset.insert nnfHauptEx_Pa
            (LCS.Finset.insert nnfHauptEx_Qa LCS.Finset.empty)) =
        LCS.Finset.insert nnfHauptEx_Pa
          (LCS.Finset.insert nnfHauptEx_RfaAndRfb
            (LCS.Finset.insert nnfHauptEx_Qa LCS.Finset.empty)) :=
        nnfHauptExInsertComm _ _ _
      _ = LCS.Finset.insert nnfHauptEx_Pa
          (LCS.Finset.insert nnfHauptEx_Qa
            (LCS.Finset.insert nnfHauptEx_RfaAndRfb
              LCS.Finset.empty)) :=
        congrArg (LCS.Finset.insert nnfHauptEx_Pa)
          (nnfHauptExInsertComm _ _ _)
  exact raw.cast rfl hDelta

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
def nnfHauptExUpperCert :
    NNFHauptExPropTree nnfHauptExMidGamma nnfHauptExDelta := by
  let rfbBranch : NNFHauptExPropTree
      (LCS.Finset.insert nnfHauptEx_Rfb
        (LCS.Finset.insert nnfHauptEx_Rfa LCS.Finset.empty))
      nnfHauptExDelta :=
    nnfHauptExConjCert.cast
      (nnfHauptExInsertComm nnfHauptEx_Rfa nnfHauptEx_Rfb
        LCS.Finset.empty) rfl
  let inner2 := nnfHauptExDisjCert nnfHauptEx_Qa nnfHauptEx_Rfb
    (LCS.Finset.insert nnfHauptEx_Rfa LCS.Finset.empty)
    nnfHauptExDelta
    (AllRectified.isRectified_of_isQuantifierFree _
      ⟨trivial, trivial⟩)
    (nnfHauptExQaCert [nnfHauptEx_Rfa]
      (by intro F h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst F; trivial)
      (by intro F h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst F; exact nnfHauptEx_RfaRectified))
    rfbBranch
  let mid2 := nnfHauptExDisjCert nnfHauptEx_Pa
    (FormulaN.disj nnfHauptEx_Qa nnfHauptEx_Rfb)
    (LCS.Finset.insert nnfHauptEx_Rfa LCS.Finset.empty)
    nnfHauptExDelta
    nnfHauptEx_midAnt2Rectified
    (nnfHauptExPaCert [nnfHauptEx_Rfa]
      (by intro F h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst F; trivial)
      (by intro F h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst F; exact nnfHauptEx_RfaRectified))
    inner2
  let rfaBranch : NNFHauptExPropTree
      (LCS.Finset.insert nnfHauptEx_Rfa
        (LCS.Finset.insert nnfHauptEx_midAnt2 LCS.Finset.empty))
      nnfHauptExDelta :=
    mid2.cast
      (nnfHauptExInsertComm nnfHauptEx_midAnt2 nnfHauptEx_Rfa
        LCS.Finset.empty) rfl
  let inner1 := nnfHauptExDisjCert nnfHauptEx_Qa nnfHauptEx_Rfa
    (LCS.Finset.insert nnfHauptEx_midAnt2 LCS.Finset.empty)
    nnfHauptExDelta
    (AllRectified.isRectified_of_isQuantifierFree _
      ⟨trivial, trivial⟩)
    (nnfHauptExQaCert [nnfHauptEx_midAnt2]
      (by intro F h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst F; trivial)
      (by intro F h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst F; exact nnfHauptEx_midAnt2Rectified))
    rfaBranch
  exact nnfHauptExDisjCert nnfHauptEx_Pa
    (FormulaN.disj nnfHauptEx_Qa nnfHauptEx_Rfa)
    (LCS.Finset.insert nnfHauptEx_midAnt2 LCS.Finset.empty)
    nnfHauptExDelta
    nnfHauptEx_midAnt1Rectified
    (nnfHauptExPaCert [nnfHauptEx_midAnt2]
      (by intro F h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst F; trivial)
      (by intro F h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst F; exact nnfHauptEx_midAnt2Rectified))
    inner1

-- ATTACH-BLOCKER: unsupported untagged structure
structure NNFHauptExMidConstruction
    (Γ Δ : NNFHauptExFormulaSet) where
  tree : G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality) Γ Δ
  node : G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality) nnfHauptExMidGamma nnfHauptExDelta
  path : G2nnfProofTree.RootToNodePath tree node
  above : AllRulesPropOrWeakening (hL := by rfl) node
  below : AllRulesQuantifierOnPath path

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
def NNFHauptExMidConstruction.castRoot
    {Γ Δ Γ' Δ' : NNFHauptExFormulaSet}
    (c : NNFHauptExMidConstruction Γ Δ)
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') :
    NNFHauptExMidConstruction Γ' Δ' :=
  match hΓ, hΔ with
  | rfl, rfl => c

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
def nnfHauptExUpperConstruction :
    NNFHauptExMidConstruction
      nnfHauptExMidGamma nnfHauptExDelta where
  tree := nnfHauptExUpperCert.tree
  node := nnfHauptExUpperCert.tree
  path := .root nnfHauptExUpperCert.tree
  above := nnfHauptExUpperCert.allProp
  below := trivial

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
def nnfHauptExPrependQuantifier
    (rule : G2nnfRuleCore nnfHauptExLang)
    (hAdmit : rule.BareAtomicAxiom)
    (hPrem : rule.premises.length = 1)
    (hSC : rule.SideConditions) (hQuant : rule.isQuantifierRule)
    (c : NNFHauptExMidConstruction
      (rule.premises[0]'(by omega)).1 (rule.premises[0]'(by omega)).2) :
    NNFHauptExMidConstruction rule.conclusion.1 rule.conclusion.2 where
  tree := .onePremise rule hAdmit hPrem hSC c.tree
  node := c.node
  path := .onePremise rule hAdmit hPrem hSC c.tree c.path
  above := c.above
  below := ⟨hQuant, c.below⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
def nnfHauptExNormalConstruction :
    NNFHauptExMidConstruction
      (LCS.Finset.insert nnfHauptEx_antFormula LCS.Finset.empty)
      nnfHauptExDelta := by
  let ruleFb :=
    G2nnfRuleCore.allSubLeft nnfHauptEx_afterFirstInst
      nnfHauptEx_afterFirstYOccurrence 1 nnfHauptEx_Ry nnfHauptEx_fb rfl (LCS.Finset.insert nnfHauptEx_midAnt1 LCS.Finset.empty) nnfHauptExDelta
  have hSCFb : ruleFb.SideConditions := by
    exact
      ⟨trivial, (by simp [ruleFb, AllNNF, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises, LCS.Finset.mem_insert, FormulaN.isNNF, nnfHauptExDelta, nnfHauptEx_afterFirstYOccurrence, nnfHauptEx_forallYOccurrence, nnfHauptEx_antXOccurrence, nnfHauptEx_forallXOccurrence, MaxQuantifierOccurrence.replace, nnfHauptExSubstRy, nnfHauptExSubstQxOr]), (by simp [ruleFb, AllNNF, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises, LCS.Finset.mem_insert, FormulaN.isNNF, nnfHauptExDelta, nnfHauptEx_afterFirstYOccurrence, nnfHauptEx_forallYOccurrence, nnfHauptEx_antXOccurrence, nnfHauptEx_forallXOccurrence, MaxQuantifierOccurrence.replace, nnfHauptExSubstRy, nnfHauptExSubstQxOr]),
        AllRectified.insert_left nnfHauptEx_afterFirstInstRectified
          (AllRectified.insert_left nnfHauptEx_midAnt1Rectified
            nnfHauptExDeltaRectified)⟩
  have hBaseΓ : nnfHauptExMidGamma =
      ((ruleFb.premises)[0]'(
          by simp [ruleFb, G2nnfRuleCore.premises])).1 := by
    simp [ruleFb, G2nnfRuleCore.premises,
      nnfHauptEx_afterFirstYOccurrence, nnfHauptEx_forallYOccurrence,
      nnfHauptEx_forallYRy, MaxQuantifierOccurrence.replace,
      nnfHauptExSubstRy, nnfHauptExInsertComm]
  let baseForFb := nnfHauptExUpperConstruction.castRoot hBaseΓ rfl
  let cFbRaw := nnfHauptExPrependQuantifier ruleFb trivial rfl hSCFb trivial baseForFb
  have hFbΓ :
      (ruleFb.conclusion).1 =
      LCS.Finset.insert nnfHauptEx_afterFirstInst
        (LCS.Finset.insert nnfHauptEx_midAnt1
          LCS.Finset.empty) := rfl
  let cFb := cFbRaw.castRoot hFbΓ rfl

  let ruleFa :=
    G2nnfRuleCore.allSubLeft nnfHauptEx_afterFirstInst
      nnfHauptEx_afterFirstYOccurrence 1 nnfHauptEx_Ry nnfHauptEx_fa rfl (LCS.Finset.insert nnfHauptEx_afterFirstInst LCS.Finset.empty) nnfHauptExDelta
  have hSCFa : ruleFa.SideConditions := by
    exact
      ⟨trivial, (by simp [ruleFa, AllNNF, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises, LCS.Finset.mem_insert, FormulaN.isNNF, nnfHauptExDelta, nnfHauptEx_afterFirstYOccurrence, nnfHauptEx_forallYOccurrence, nnfHauptEx_antXOccurrence, nnfHauptEx_forallXOccurrence, MaxQuantifierOccurrence.replace, nnfHauptExSubstRy, nnfHauptExSubstQxOr]), (by simp [ruleFa, AllNNF, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises, LCS.Finset.mem_insert, FormulaN.isNNF, nnfHauptExDelta, nnfHauptEx_afterFirstYOccurrence, nnfHauptEx_forallYOccurrence, nnfHauptEx_antXOccurrence, nnfHauptEx_forallXOccurrence, MaxQuantifierOccurrence.replace, nnfHauptExSubstRy, nnfHauptExSubstQxOr]),
        AllRectified.insert_left nnfHauptEx_afterFirstInstRectified
          (AllRectified.insert_left nnfHauptEx_afterFirstInstRectified
            nnfHauptExDeltaRectified)⟩
  have hFbToFa :
      LCS.Finset.insert nnfHauptEx_afterFirstInst
          (LCS.Finset.insert nnfHauptEx_midAnt1 LCS.Finset.empty) =
      ((ruleFa.premises)[0]'(
          by simp [ruleFa, G2nnfRuleCore.premises])).1 := by
    simp [ruleFa, G2nnfRuleCore.premises, nnfHauptEx_afterFirstInst,
      nnfHauptEx_afterFirstYOccurrence, nnfHauptEx_forallYOccurrence,
      nnfHauptEx_forallYRy, nnfHauptEx_midAnt1,
      MaxQuantifierOccurrence.replace, nnfHauptExSubstRy,
      nnfHauptExInsertComm]
  let cFbForFa := cFb.castRoot hFbToFa rfl
  let cFaRaw := nnfHauptExPrependQuantifier ruleFa trivial rfl hSCFa trivial cFbForFa
  have hFaΓ :
      (ruleFa.conclusion).1 =
      LCS.Finset.insert nnfHauptEx_afterFirstInst
        LCS.Finset.empty := by
    exact nnfHauptExInsertSelf nnfHauptEx_afterFirstInst
      LCS.Finset.empty
  let cFa := cFaRaw.castRoot hFaΓ rfl

  let ruleX :=
    G2nnfRuleCore.allSubLeft nnfHauptEx_antFormula
      nnfHauptEx_antXOccurrence 0 nnfHauptEx_QxOrForallYRy
      (Term.const NNFHauptExConst.a) rfl LCS.Finset.empty nnfHauptExDelta
  have hSCX : ruleX.SideConditions := by
    refine
      ⟨?_, (by simp [ruleX, AllNNF, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises, LCS.Finset.mem_insert, FormulaN.isNNF, nnfHauptExDelta, nnfHauptEx_afterFirstYOccurrence, nnfHauptEx_forallYOccurrence, nnfHauptEx_antXOccurrence, nnfHauptEx_forallXOccurrence, MaxQuantifierOccurrence.replace, nnfHauptExSubstRy, nnfHauptExSubstQxOr]), (by simp [ruleX, AllNNF, G2nnfRuleCore.conclusion, G2nnfRuleCore.premises, LCS.Finset.mem_insert, FormulaN.isNNF, nnfHauptExDelta, nnfHauptEx_afterFirstYOccurrence, nnfHauptEx_forallYOccurrence, nnfHauptEx_antXOccurrence, nnfHauptEx_forallXOccurrence, MaxQuantifierOccurrence.replace, nnfHauptExSubstRy, nnfHauptExSubstQxOr]),
        AllRectified.insert_left nnfHauptEx_antFormulaRectified
          nnfHauptExDeltaRectified⟩
    · refine ⟨trivial, Or.inr ⟨?_, trivial⟩⟩
      exact nofun
  have hFaToX :
      LCS.Finset.insert nnfHauptEx_afterFirstInst LCS.Finset.empty =
      ((ruleX.premises)[0]'(
          by simp [ruleX, G2nnfRuleCore.premises])).1 := by
    simp [ruleX, G2nnfRuleCore.premises, nnfHauptEx_forallXBody,
      nnfHauptEx_antXOccurrence, nnfHauptEx_forallXOccurrence,
      nnfHauptEx_afterFirstInst, MaxQuantifierOccurrence.replace,
      nnfHauptExSubstQxOr]
  let cFaForX := cFa.castRoot hFaToX rfl
  exact nnfHauptExPrependQuantifier ruleX trivial rfl hSCX trivial cFaForX


-- ===================================================================
-- Example 7.4.4 (companion def): nnfHauptsatzExNormalTree
-- ===================================================================

/-- Example 7.4.4 (companion def): The concrete normal-form G2nnf tree.
Its three quantifier inferences form the path from the root to the displayed
midsequent, while the complete subtree above that occurrence uses only
propositional rules and explicit weakenings above bare atomic identities.
The tree, occurrence path, and rule-classification
certificates are constructed together so they refer to the same indexed node. -/
@[blueprint "chap7__example_7_4_4" (main := true)]
def nnfHauptsatzExNormalTree :
    G2nnfProofTree (by rfl : nnfHauptExLang.withoutEquality)
      (LCS.Finset.insert nnfHauptEx_antFormula LCS.Finset.empty)
      (LCS.Finset.insert nnfHauptEx_Pa
        (LCS.Finset.insert nnfHauptEx_Qa
          (LCS.Finset.insert nnfHauptEx_RfaAndRfb LCS.Finset.empty))) :=
  nnfHauptExNormalConstruction.tree



end
end LCS.Herbrand.NNFHauptsatz.Theorem
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Soundness
open LCS.Herbrand.SharpenedHauptsatz
open LCS.Herbrand.SharpenedHauptsatz.Permutability
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.Herbrand.PrenexForm
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS.CutElim.LK
namespace LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule

/-- Lemma 7.4.2 (companion propositional part): Every quantifier rule R_1 of G2nnf can be permuted with a propositional rule R_2 in a pure-variable, cut-free proof. This covers Cases 1-4 from the textbook (conjunction-left with forall-left/exists-left, conjunction-right with forall-right/exists-right) as well as the G1nnf-inherited cases from Lemma 7.3.3. Each case constructs the permuted proof tree T' explicitly, with subcases based on whether the formula A belongs to the context Gamma or to the top sequent of the propositional rule. -/
theorem g2nnf_permutability_with_propositional
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Γ Δ)
    (R₁ R₂ : G2nnfRule L hL)
    (hPure : IsPureVariableProofG2nnf T)
    (hCF : T.isCutFree)
    (hQuant : R₁.isQuantifierRule)
    (hProp : R₂.isPropositionalRule) :
    CanPermuteWithG2nnf R₁ R₂ T := by
-- BEGIN PROOF
  -- REPAIR(T7-47): proof pending; construct Q for each eligible occurrence
  sorry

-- ===================================================================
-- Lemma 7.4.2 (weakening part): g2nnf_permutability_with_weakening
-- ===================================================================

/-- Lemma 7.4.2 (companion weakening part): Every quantifier rule R_1 of G2nnf can be permuted with a weakening rule R_2 in a pure-variable, cut-free proof. The proof constructs the permuted tree T' by applying the weakening rule first, then the quantifier rule, with adjustments to the context sets. -/
theorem g2nnf_permutability_with_weakening
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Γ Δ)
    (R₁ R₂ : G2nnfRule L hL)
    (hPure : IsPureVariableProofG2nnf T)
    (hCF : T.isCutFree)
    (hQuant : R₁.isQuantifierRule)
    (hWeak : R₂.isWeakening) :
    CanPermuteWithG2nnf R₁ R₂ T := by
-- BEGIN PROOF
  -- REPAIR(T7-47): proof pending; construct Q for each eligible occurrence
  sorry

-- ===================================================================
-- Lemma 7.4.2: g2nnf_permutability
-- ===================================================================

/-- Lemma 7.4.2: In every pure-variable, cut-free G2nnf proof, each
quantifier inference can be locally permuted with a propositional inference
or weakening. Every eligible occurrence pair has its own boundary-preserving
Q, including focused side-formula cases and weakening-only intermediate
paths. The only extra inferences in Q are weakenings; lower-schema copies
are permitted. -/
@[attach_debt, blueprint "chap7__lemma_7_4_2" (main := true)]
theorem g2nnf_permutability
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Γ Δ)
    (R₁ R₂ : G2nnfRule L hL)
    (hPure : IsPureVariableProofG2nnf T)
    (hCF : T.isCutFree)
    (hQuant : R₁.isQuantifierRule)
    (hR₂ : R₂.isPropositionalRule ∨ R₂.isWeakening) :
    CanPermuteWithG2nnf R₁ R₂ T 

-- ===================================================================
-- Theorem 7.4.1 (companion def): allSequentFormulaeAreNNF
-- ===================================================================

/-- Theorem 7.4.1 (companion def): Predicate asserting that every formula in both the antecedent and succedent of an `LCS.Finset`-based sequent is in NNF (FormulaN.isNNF holds for each formula). This is the hypothesis that all formulae in Gamma -> Delta are in negation normal form. -/
@[blueprint "chap7__theorem_7_4_1"]
def allSequentFormulaeAreNNF {L : Language}
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) : Prop :=
  (∀ A, Membership.mem seq.1 A → FormulaN.isNNF A) ∧
  (∀ A, Membership.mem seq.2 A → FormulaN.isNNF A)

-- ===================================================================
-- Theorem 7.4.1 (companion def): G1nnfProvableSet
-- ===================================================================

/-- Theorem 7.4.1 (companion def): Over a language without equality,
a set-based sequent is G1nnf-provable when it has an indexed proof tree,
`Nonempty (G1nnfProofTree hL Γ Δ)`. -/
@[blueprint "chap7__theorem_7_4_1"]
def G1nnfProvableSet {L : Language} [DecidableEq (FormulaN L)]
    (hL : L.withoutEquality)
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) : Prop :=
  Nonempty (G1nnfProofTree hL seq.1 seq.2)

/-- “Note that the system G1nnf is a subsystem of G2nnf.” (§7.4.1,
after Definition 7.4.3.) Under the section's conventions (rectified NNF formulae,
with no variable both free and bound in the sequent), every G1nnf-provable
set sequent is G2nnf-provable. -/
@[attach_debt, blueprint "chap7__definition_7_4_3"]
theorem g1nnf_subsystem_g2nnf {L : Language} [DecidableEq (FormulaN L)]
    (hL : L.withoutEquality)
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L))
    (hAllNNF : allSequentFormulaeAreNNF seq)
    (hRect : AllRectified seq)
    (hCross : finsetCrossNoFreeBound seq.1 seq.2) :
    G1nnfProvableSet hL seq → Nonempty (G2nnfProofTree hL seq.1 seq.2)


-- ===================================================================
-- Theorem 7.4.1 (companion def): StringEncoding
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 7.4.1 (companion def): For each root-to-leaf branch in the G2nnf proof tree, assigns the letter 'a' to each quantifier rule and 'b' to each propositional rule or weakening rule. Produces a list of strings (one per branch) encoding the inference sequence along each branch. This is the string encoding technique used in the proof of Theorem 7.4.1 to track the arrangement of quantifier vs propositional/weakening rules. -/
def StringEncoding {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)] :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → List (List Char)
  | _, _, .leaf _ _ h _ _ => h.elim
  | _, _, .extraAxiom _ _ h _ _ => h.elim
  | _, _, .axiom_ _ _ _ _ => [[]]
  | _, _, .onePremise rule _ _ _ sub =>
    let ch : Char :=
      if G2nnfRuleCore.isQuantifierRuleBool rule then 'a' else 'b'
    (StringEncoding (hL := hL) sub).map (fun branch => ch :: branch)
  | _, _, .twoPremise rule _ _ _ sub1 sub2 =>
    let ch : Char :=
      if G2nnfRuleCore.isQuantifierRuleBool rule then 'a' else 'b'
    (StringEncoding (hL := hL) sub1).map (fun branch => ch :: branch) ++
    (StringEncoding (hL := hL) sub2).map (fun branch => ch :: branch)







-- ===================================================================
-- Theorem 7.4.1 (helper): containsBA
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 7.4.1 (companion def): Predicate asserting that a single branch (string) contains the substring "ba". A branch contains "ba" if there exist consecutive characters 'b' followed by 'a'. -/
def containsBA : List Char → Prop
  | [] => False
  | [_] => False
  | c1 :: c2 :: rest =>
    (c1 = 'b' ∧ c2 = 'a') ∨ containsBA (c2 :: rest)

-- ===================================================================
-- Theorem 7.4.1 (companion def): allBranchesNormalForm
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 7.4.1 (companion def): Predicate asserting that all branches in a string encoding are in normal form: the string consists of zero or more 'a' characters followed by zero or more 'b' characters (all quantifier rules below all propositional/weakening rules). A branch is in normal form if it does not contain the substring "ba" (a propositional/weakening rule above a quantifier rule). -/
def allBranchesNormalForm (branches : List (List Char)) :
    Prop :=
  ∀ branch ∈ branches, ¬ containsBA branch

-- ===================================================================
-- Theorem 7.4.1 (helper): IsBAExchangeOf
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Theorem 7.4.1 (companion def): Predicate asserting that string s' is obtained from string s by replacing one occurrence of the substring "ba" with one of "ab", "abb", or "abbb". -/
def IsBAExchangeOf (s' s : List Char) : Prop :=
  ∃ (prefix_ suffix_ : List Char),
    s = prefix_ ++ ['b', 'a'] ++ suffix_ ∧
    (s' = prefix_ ++ ['a', 'b'] ++ suffix_ ∨
     s' = prefix_ ++ ['a', 'b', 'b'] ++ suffix_ ∨
     s' = prefix_ ++ ['a', 'b', 'b', 'b'] ++ suffix_)

-- ===================================================================
-- Theorem 7.4.1 (companion theorem): baExchangePattern
-- ===================================================================

/-- Theorem 7.4.1 (companion theorem): By Lemma 7.4.2, when a 'ba' substring appears in the string encoding (one propositional/weakening rule above one quantifier rule), a single permutation step replaces it with either 'ab', 'abb', or 'abbb' (quantifier rule below propositional/weakening, with possibly extra propositional/weakening rules from the permutation). This is the local exchange step that drives the normalization process. The resulting tree T' preserves the conclusion, the pure-variable property, and the cut-free property, and its string encoding reflects the ba-to-ab/abb/abbb replacement on at least one branch. Under the indexed `G2nnfProofTree hL Γ Δ` API, the conclusion sequent `(Γ, Δ)` is baked into the type; no `T'.conclusion = T.conclusion` or `T'.WellFormed` conjunct is needed. -/
theorem baExchangePattern {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Γ Δ)
    (hPure : IsPureVariableProofG2nnf T)
    (hCF : T.isCutFree)
    (hBA : ∃ branch ∈ StringEncoding (hL := hL) T,
      containsBA branch) :
    ∃ T' : G2nnfProofTree hL Γ Δ,
      IsPureVariableProofG2nnf T' ∧
      T'.isCutFree ∧
      (∃ (oldBranch : List Char)
         (newBranch : List Char),
        oldBranch ∈ StringEncoding (hL := hL) T ∧
        containsBA oldBranch ∧
        newBranch ∈ StringEncoding (hL := hL) T' ∧
        IsBAExchangeOf newBranch oldBranch) := by
-- BEGIN PROOF
  -- REPAIR(T7-20): proof pending; existing case/conversion proof debt
  sorry

-- ===================================================================
-- Theorem 7.4.1 (companion theorem): bMaReduction
-- ===================================================================

/-- Theorem 7.4.1 (companion theorem): Iterating the ba-to-ab exchange, a string b^m a (m propositional/weakening rules above one quantifier rule) is replaced by a b^k where m <= k <= 3*m. This bounds the number of new propositional/weakening rules introduced by one round of permutations. -/
theorem bMaReduction (m : Nat) :
    ∀ (s : List Char),
      s = List.replicate m 'b' ++ ['a'] →
      ∃ (k : Nat),
        m ≤ k ∧ k ≤ 3 * m ∧
        ∃ (s' : List Char),
          s' = ['a'] ++ List.replicate k 'b' := by
-- BEGIN PROOF
  -- REPAIR(T7-20): proof pending; existing string-lemma debt
  sorry

-- ===================================================================
-- Theorem 7.4.1 (companion theorem): bMaNReduction
-- ===================================================================

/-- Theorem 7.4.1 (companion theorem): Generalizing bMaReduction: b^m a^n (m propositional/weakening rules above n quantifier rules) is replaced by a^n b^mk for some k, placing all quantifier rules below all propositional/weakening rules. This shows that the normalization process terminates. -/
theorem bMaNReduction (m n : Nat) :
    ∀ (s : List Char),
      s = List.replicate m 'b' ++ List.replicate n 'a' →
      ∃ (k : Nat),
        1 ≤ k ∧ k ≤ 3 ^ n ∧
        ∃ (s' : List Char),
          s' = List.replicate n 'a' ++
               List.replicate (m * k) 'b' := by
-- BEGIN PROOF
  -- REPAIR(T7-20): proof pending; existing string-lemma debt
  sorry

-- ===================================================================
-- Theorem 7.4.1 (companion theorem): permutationTermination
-- ===================================================================

/-- Theorem 7.4.1 (companion theorem): The permutation process terminates: starting from any pure-variable cut-free G2nnf proof T, repeated application of Lemma 7.4.2 produces a proof T' where all branches have normal form a^n b^k (all quantifier rules below all propositional/weakening rules). This is established by the string encoding technique: each ba-to-ab exchange reduces the number of ba-substrings in the encoding, and the bound b^m*a^n -> a^n*b^mk ensures termination. Under the indexed `G2nnfProofTree hL Γ Δ` API, the conclusion sequent is baked into the type; no `T'.conclusion = T.conclusion` or `T'.WellFormed` conjunct is needed. -/
theorem permutationTermination {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Γ Δ)
    (hPure : IsPureVariableProofG2nnf T)
    (hCF : T.isCutFree) :
    ∃ T' : G2nnfProofTree hL Γ Δ,
      IsPureVariableProofG2nnf T' ∧
      T'.isCutFree ∧
      allBranchesNormalForm (StringEncoding (hL := hL) T') := by
-- BEGIN PROOF
  classical
  by_cases hNormal : allBranchesNormalForm (StringEncoding (hL := hL) T)
  · exact ⟨T, hPure, hCF, hNormal⟩
  · -- REPAIR(T7-20): proof pending; normalize the non-normal branch encoding
    sorry

-- ===================================================================
-- Theorem 7.4.1 (companion theorem): cutFreeG1nnfFromProvability
-- ===================================================================

/-- Theorem 7.4.1 (companion theorem): Over a language without equality,
a G1nnf-provable rectified sequent satisfying the §6.1 sequent-level
free/bound-variable convention has a cut-free G2nnf proof. The conclusion
is obtained by G1nnf cut elimination and the embedding into G2nnf.
The root remains indexed by the original sequent. -/
theorem cutFreeG1nnfFromProvability {L : Language}
    [DecidableEq (FormulaN L)]
    (hL : L.withoutEquality)
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L))
    (hRect : AllRectified seq)
    (hCross : finsetCrossNoFreeBound seq.1 seq.2)
    (hProv : G1nnfProvableSet hL seq) :
    ∃ T : G2nnfProofTree hL seq.1 seq.2, T.isCutFree := by
  -- REPAIR(T6-21c): truth open under E-CUTFB; proof pending
  -- REPAIR(T7-20): proof pending; existing case/conversion proof debt
  sorry

-- ===================================================================
-- Theorem 7.4.1 (companion def): premiseOfHighestQuantifier
-- ===================================================================



-- ===================================================================
-- Theorem 7.4.1 (companion def): removeWeakeningQuantifiedFormulae
-- ===================================================================



-- ===================================================================
-- Theorem 7.4.1: sharpenedHauptsatz_G2nnf
-- ===================================================================

/-- Theorem 7.4.1: Over a language without equality, a G1nnf-provable
rectified NNF sequent satisfying the §6.1 sequent-level free/bound-variable
convention has a cut-free, pure-variable G2nnf proof with a midsequent.
Every formula of the midsequent is quantifier-free; above it the rules are
propositional or weakening, and below it they are quantifier-for-subformulae
rules. Rectification remains a standing assumption of §7.4 and is enforced
at every proof node by the G2nnf side conditions. -/
@[attach_debt, blueprint "chap7__theorem_7_4_1" (main := true)]
theorem sharpenedHauptsatz_G2nnf {L : Language}
    [DecidableEq (FormulaN L)]
    (hL : L.withoutEquality)
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L))
    (hAllNNF : allSequentFormulaeAreNNF seq)
    (hRect : AllRectified seq)
    (hCross : finsetCrossNoFreeBound seq.1 seq.2)
    (hProv : G1nnfProvableSet hL seq) :
    ∃ (T : G2nnfProofTree hL seq.1 seq.2)
      (mid : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)),
      T.isCutFree ∧
      IsPureVariableProofG2nnf T ∧
      IsMidsequentG2nnf T mid 

-- ===================================================================
-- Example 7.4.4 (companion theorem): nnfHauptsatzExMidsequentIsQuantifierFree
-- ===================================================================



-- ===================================================================
-- Example 7.4.4 (companion theorem): nnfHauptsatzExIsMidsequent
-- ===================================================================

/-- Example 7.4.4 (companion theorem): Verifies that
nnfHauptsatzExMidsequent is the midsequent of the concrete normal-form proof
tree nnfHauptsatzExNormalTree, satisfying all three conditions of Theorem
7.4.1: every midsequent formula is quantifier-free, every rule above the
selected occurrence is propositional or a weakening, and every rule on the
path below it is a quantifier-for-subformulae rule of G2nnf. -/
@[blueprint "chap7__example_7_4_4" (main := true)]
theorem nnfHauptsatzExIsMidsequent :
    IsMidsequentG2nnf (hL := by rfl) nnfHauptsatzExNormalTree
      ( LCS.Finset.insert nnfHauptEx_midAnt1
          (LCS.Finset.insert nnfHauptEx_midAnt2
            LCS.Finset.empty),
        LCS.Finset.insert nnfHauptEx_Pa
          (LCS.Finset.insert nnfHauptEx_Qa
            (LCS.Finset.insert nnfHauptEx_RfaAndRfb
              LCS.Finset.empty)) )

end LCS.Herbrand.NNFHauptsatz.Theorem
end

