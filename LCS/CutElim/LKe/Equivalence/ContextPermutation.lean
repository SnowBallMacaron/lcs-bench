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

-- ===================================================================
-- Lemma 6.3.2 (required def): gProofTreeDepth
-- ===================================================================
/-- Lemma 6.3.2 (required def): The depth (height) of a G proof
tree: 0 for axiom leaves, 1 + max of subtree depths for rule
applications. -/
@[blueprint "chap6__lemma_6_3_2"]
def gProofTreeDepth {L : Language} :
    {s : Sequent L} → GProofTreeExt s → Nat
  | _, .axiom_ _ _ => 0
  | _, .onePremise _ t => 1 + gProofTreeDepth t
  | _, .twoPremise _ t1 t2 =>
    1 + max (gProofTreeDepth t1) (gProofTreeDepth t2)

-- ===================================================================
-- Lemma 6.3.2 (required def): geqDepth
-- ===================================================================
/-- Lemma 6.3.2 (required def): The depth (height) of a G= proof
tree: 0 for axiom leaves, 1 + max of subtree depths for rule
applications. -/
@[blueprint "chap6__lemma_6_3_2"]
def geqDepth {L : Language} {hL : L.hasEquality = true} :
    {s : Sequent L} → GEqProofTree hL s → Nat
  | _, .base g => gProofTreeDepth g
  | _, .axiom_ _ _ => 0
  | _, .onePremise _ sub => 1 + geqDepth sub
  | _, .twoPremise _ sub1 sub2 =>
    1 + max (geqDepth sub1) (geqDepth sub2)
  | _, .eqRefl _ _ _ sub => 1 + geqDepth sub
  | _, .eqFuncCong _ _ _ _ _ sub => 1 + geqDepth sub
  | _, .eqPredCong _ _ _ _ _ sub => 1 + geqDepth sub
  | _, .eqGeneral _ _ _ _ _ sub => 1 + geqDepth sub

-- ===================================================================
-- Lemma 6.3.2 (internal helper): depth-preserving context permutation
-- ===================================================================
-- ATTACH-BLOCKER: private declaration
/-- Removing equally marked occurrences from two permuted lists leaves
permuted remainders.  The occurrences are positional: this remains valid
when the marked value occurs more than once. -/
private theorem geqPerm_cancelMarked {α : Type} {P Q R S : List α} {X : α}
    (h : (P ++ [X] ++ Q).Perm (R ++ [X] ++ S)) :
    (P ++ Q).Perm (R ++ S) := by
  have moveFront :
      ∀ (U V : List α),
        (X :: (U ++ V)).Perm (U ++ [X] ++ V) := by
    intro U V
    have hmove :
        (([X] ++ U) ++ V).Perm ((U ++ [X]) ++ V) :=
      List.Perm.append_right V List.perm_append_comm
    simpa [List.append_assoc] using hmove
  exact List.Perm.cons_inv
    ((moveFront P Q).trans (h.trans (moveFront R S).symm))

-- ATTACH-BLOCKER: private declaration
/-- Inserting the same formula block at arbitrary splits preserves a
permutation of the surrounding contexts. -/
private theorem geqPerm_insertBlock {α : Type} {P Q R S : List α}
    (block : List α) (h : (P ++ Q).Perm (R ++ S)) :
    (P ++ block ++ Q).Perm (R ++ block ++ S) := by
  have moveFront :
      ∀ (U V : List α),
        (U ++ block ++ V).Perm (block ++ (U ++ V)) := by
    intro U V
    have hmove :
        ((U ++ block) ++ V).Perm ((block ++ U) ++ V) :=
      List.Perm.append_right V List.perm_append_comm
    simpa [List.append_assoc] using hmove
  exact (moveFront P Q).trans
    ((List.Perm.append_left block h).trans (moveFront R S).symm)

-- retained: used by LCS.CutElim.LKe.Equivalence.ContextPermutation
/-- Atomic-or-quantified sequents are invariant under independent
permutations of their antecedent and succedent. -/
theorem seqAllAtomicOrQuantified_perm {L : Language}
    {Γ Δ Γ' Δ' : List (FormulaN L)}
    (hΓ : Γ.Perm Γ') (hΔ : Δ.Perm Δ')
    (h : seqAllAtomicOrQuantified (Sequent.mk Γ Δ)) :
    seqAllAtomicOrQuantified (Sequent.mk Γ' Δ') := by
  constructor
  · intro F hF
    exact h.1 F (hΓ.mem_iff.mpr hF)
  · intro F hF
    exact h.2 F (hΔ.mem_iff.mpr hF)

-- retained: used by LCS.CutElim.LKe.Equivalence.ContextPermutation
theorem geqPermuteContexts_base
    (L : Language) (hL : L.hasEquality = true) (permAxiom : ∀ (s₀ : Sequent L), isAxiom s₀ → ∀ (Γ₀ Δ₀ : List
      (FormulaN L)), s₀.antecedent.Perm Γ₀ → s₀.succedent.Perm Δ₀ → seqAllAtomicOrQuantified s₀ → ∃ (p :
      GEqProofTree hL (Sequent.mk (Γ₀) (Δ₀))), geqDepth p = 0 ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p →
      seqAllAtomicOrQuantified s') (n : Nat) (s : Sequent L) (Γ' Δ' : List (FormulaN L)) (hΓ :
      s.antecedent.Perm Γ') (hΔ : s.succedent.Perm Δ') (permOne : ∀ {prem conc : Sequent L} (rule :
      GentzenStep1Ext prem conc) (sub : GEqProofTree hL prem), geqDepth sub < n → conc.antecedent.Perm Γ' →
      conc.succedent.Perm Δ' → (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub → seqAllAtomicOrQuantified s') →
      ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth sub ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s') (permTwo : ∀ {prem1 prem2 conc : Sequent L} (rule :
      GentzenStep2Ext prem1 prem2 conc) (sub1 : GEqProofTree hL prem1) (sub2 : GEqProofTree hL prem2),
      geqDepth sub1 < n → geqDepth sub2 < n → conc.antecedent.Perm Γ' → conc.succedent.Perm Δ' → (∀ (s' :
      Sequent L), s' ∈ geqLeafSequents sub1 → seqAllAtomicOrQuantified s') → (∀ (s' : Sequent L), s' ∈
      geqLeafSequents sub2 → seqAllAtomicOrQuantified s') → ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))),
      geqDepth p = 1 + max (geqDepth sub1) (geqDepth sub2) ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p →
      seqAllAtomicOrQuantified s') (g : GProofTreeExt s) (hdepth : geqDepth (GEqProofTree.base (hL := hL) g) =
      n) (hleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents (GEqProofTree.base (hL := hL) g) →
      seqAllAtomicOrQuantified s')
    : ∃ (T' : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth T' = geqDepth (GEqProofTree.base (hL := hL) g)
      ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents T' → seqAllAtomicOrQuantified s' := by
  cases g with
  | axiom_ _ hAx =>
    obtain ⟨p, hpd, hpl⟩ := permAxiom s hAx Γ' Δ' hΓ hΔ (hleaf s (by
          simp [geqLeafSequents, gProofTreeLeafSequents]))
    exact ⟨p, by
      simpa [geqDepth, gProofTreeDepth] using hpd, hpl⟩
  | onePremise rule sub =>
    obtain ⟨p, hpd, hpl⟩ := permOne rule (.base sub) (by
        simp only [geqDepth, gProofTreeDepth] at hdepth ⊢
        omega) hΓ hΔ (by
          intro s' hs'
          exact hleaf s' (by
            simpa [geqLeafSequents, gProofTreeLeafSequents] using hs'))
    exact ⟨p, by
      simpa [geqDepth, gProofTreeDepth] using hpd, hpl⟩
  | twoPremise rule sub1 sub2 =>
    obtain ⟨p, hpd, hpl⟩ := permTwo rule (.base sub1) (.base sub2) (by
        simp only [geqDepth, gProofTreeDepth] at hdepth ⊢
        omega) (by
        simp only [geqDepth, gProofTreeDepth] at hdepth ⊢
        omega) hΓ hΔ (by
          intro s' hs'
          exact hleaf s' (by
            simp only [geqLeafSequents, gProofTreeLeafSequents, List.mem_append]
            exact Or.inl hs')) (by
          intro s' hs'
          exact hleaf s' (by
            simp only [geqLeafSequents, gProofTreeLeafSequents, List.mem_append]
            exact Or.inr hs'))
    exact ⟨p, by
      simpa [geqDepth, gProofTreeDepth] using hpd, hpl⟩

section
-- ATTACH-BLOCKER: variable
variable
    (L : Language) (hL : L.hasEquality = true) (n : Nat) (ih : ∀ (m : Nat), m < n → ∀ {s : Sequent L} (T :
      GEqProofTree hL s), geqDepth T = m → ∀ (Γ' Δ' : List (FormulaN L)), s.antecedent.Perm Γ' →
      s.succedent.Perm Δ' → (∀ (s' : Sequent L), s' ∈ geqLeafSequents T → seqAllAtomicOrQuantified s') → ∃ (T'
      : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth T' = geqDepth T ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents T' → seqAllAtomicOrQuantified s')
-- ATTACH-BLOCKER: unknown command Lean.Parser.Command.include
include ih

-- ATTACH-BLOCKER: private declaration
private theorem geqPermuteContexts_conjLeft
    (Γ' Δ' Γr Δr Λr : List (FormulaN L)) (X Y : FormulaN L) (sub : GEqProofTree hL (Sequent.mk (Γr ++ [X, Y]
      ++ Δr) (Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') (hΓc : (Γr ++ [X.conj Y] ++ Δr).Perm Γ') (hΔc : (Λr).Perm Δ')
    : ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth sub ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  have hmem : FormulaN.conj X Y ∈ Γ' := hΓc.mem_iff.mp (by simp)
  obtain ⟨Γt, Δt, hsplit⟩ := perm_mem_split (FormulaN.conj X Y) Γ' hmem
  subst Γ'
  have hrest := geqPerm_cancelMarked hΓc
  have hprem := geqPerm_insertBlock ([X, Y] : List (FormulaN L)) hrest
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) hsubdepth sub rfl (Γt ++ [X, Y] ++ Δt) Δ' hprem hΔc hsubleaf
  refine ⟨.onePremise (.conjLeft Γt Δt Δ' X Y) q, ?_, ?_⟩
  · simp only [geqDepth]
    omega
  · simpa [geqLeafSequents] using hql

-- ATTACH-BLOCKER: private declaration
private theorem geqPermuteContexts_disjRight
    (Γ' Δ' Γr Δr Λr : List (FormulaN L)) (X Y : FormulaN L) (sub : GEqProofTree hL (Sequent.mk (Γr) (Δr ++ [X,
      Y] ++ Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') (hΓc : (Γr).Perm Γ') (hΔc : (Δr ++ [X.disj Y] ++ Λr).Perm Δ')
    : ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth sub ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  have hmem : FormulaN.disj X Y ∈ Δ' := hΔc.mem_iff.mp (by simp)
  obtain ⟨Δt, Λt, hsplit⟩ := perm_mem_split (FormulaN.disj X Y) Δ' hmem
  subst Δ'
  have hrest := geqPerm_cancelMarked hΔc
  have hprem := geqPerm_insertBlock ([X, Y] : List (FormulaN L)) hrest
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) hsubdepth sub rfl Γ' (Δt ++ [X, Y] ++ Λt) hΓc hprem hsubleaf
  refine ⟨.onePremise (.disjRight Γ' Δt Λt X Y) q, ?_, ?_⟩
  · simp only [geqDepth]
    omega
  · simpa [geqLeafSequents] using hql

-- ATTACH-BLOCKER: private declaration
private theorem geqPermuteContexts_implRight
    (Γ' Δ' Γr Δr Λr : List (FormulaN L)) (X Y : FormulaN L) (sub : GEqProofTree hL (Sequent.mk ([X] ++ Γr)
      ([Y] ++ Δr ++ Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents
      sub → seqAllAtomicOrQuantified s') (hΓc : (Γr).Perm Γ') (hΔc : (Δr ++ [X.impl Y] ++ Λr).Perm Δ')
    : ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth sub ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  have hmem : FormulaN.impl X Y ∈ Δ' := hΔc.mem_iff.mp (by simp)
  obtain ⟨Δt, Λt, hsplit⟩ := perm_mem_split (FormulaN.impl X Y) Δ' hmem
  subst Δ'
  have hrest := geqPerm_cancelMarked hΔc
  have hpremAnt : ([X] ++ Γr).Perm ([X] ++ Γ') := List.Perm.append_left [X] hΓc
  have hpremSuc : ([Y] ++ Δr ++ Λr).Perm ([Y] ++ Δt ++ Λt) := by
    simpa [List.append_assoc] using List.Perm.append_left [Y] hrest
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) hsubdepth sub rfl ([X] ++ Γ') ([Y] ++ Δt ++ Λt)
      hpremAnt hpremSuc hsubleaf
  refine ⟨.onePremise (.implRight Γ' Δt Λt X Y) q, ?_, ?_⟩
  · simp only [geqDepth]
    omega
  · simpa [geqLeafSequents] using hql

-- ATTACH-BLOCKER: private declaration
private theorem geqPermuteContexts_negLeft
    (Γ' Δ' Γr Δr Λr : List (FormulaN L)) (X : FormulaN L) (sub : GEqProofTree hL (Sequent.mk (Γr ++ Δr) ([X]
      ++ Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') (hΓc : (Γr ++ [X.neg] ++ Δr).Perm Γ') (hΔc : (Λr).Perm Δ')
    : ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth sub ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  have hmem : FormulaN.neg X ∈ Γ' := hΓc.mem_iff.mp (by simp)
  obtain ⟨Γt, Δt, hsplit⟩ := perm_mem_split (FormulaN.neg X) Γ' hmem
  subst Γ'
  have hpremAnt := geqPerm_cancelMarked hΓc
  have hpremSuc : ([X] ++ Λr).Perm ([X] ++ Δ') := List.Perm.append_left [X] hΔc
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) hsubdepth sub rfl (Γt ++ Δt) ([X] ++ Δ')
      hpremAnt hpremSuc hsubleaf
  refine ⟨.onePremise (.negLeft Γt Δt Δ' X) q, ?_, ?_⟩
  · simp only [geqDepth]
    omega
  · simpa [geqLeafSequents] using hql

-- ATTACH-BLOCKER: private declaration
private theorem geqPermuteContexts_negRight
    (Γ' Δ' Γr Δr Λr : List (FormulaN L)) (X : FormulaN L) (sub : GEqProofTree hL (Sequent.mk ([X] ++ Γr) (Δr
      ++ Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') (hΓc : (Γr).Perm Γ') (hΔc : (Δr ++ [X.neg] ++ Λr).Perm Δ')
    : ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth sub ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  have hmem : FormulaN.neg X ∈ Δ' := hΔc.mem_iff.mp (by simp)
  obtain ⟨Δt, Λt, hsplit⟩ := perm_mem_split (FormulaN.neg X) Δ' hmem
  subst Δ'
  have hpremAnt : ([X] ++ Γr).Perm ([X] ++ Γ') := List.Perm.append_left [X] hΓc
  have hpremSuc := geqPerm_cancelMarked hΔc
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) hsubdepth sub rfl ([X] ++ Γ') (Δt ++ Λt)
      hpremAnt hpremSuc hsubleaf
  refine ⟨.onePremise (.negRight Γ' Δt Λt X) q, ?_, ?_⟩
  · simp only [geqDepth]
    omega
  · simpa [geqLeafSequents] using hql

-- ATTACH-BLOCKER: private declaration
private theorem geqPermuteContexts_allLeft
    (Γ' Δ' : List (FormulaN L)) (ts : List (Term L)) (Γr Δr Λr : List (FormulaN L)) (x : Nat) (X : FormulaN L)
      (hne : ts ≠ []) (hfree : ∀ (t : Term L), t ∈ ts → isFreeForN t x X) (sub : GEqProofTree hL (Sequent.mk
      (Γr ++ List.map (fun (t : Term L) => formulaSubstN X t x) ts ++ [FormulaN.all x X] ++ Δr) (Λr)))
      (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') (hΓc : (Γr ++ [FormulaN.all x X] ++ Δr).Perm Γ') (hΔc : (Λr).Perm Δ')
    : ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth sub ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  have hmem : FormulaN.all x X ∈ Γ' := hΓc.mem_iff.mp (by simp)
  obtain ⟨Γt, Δt, hsplit⟩ := perm_mem_split (FormulaN.all x X) Γ' hmem
  subst Γ'
  have hrest := geqPerm_cancelMarked hΓc
  have hprem : (Γr ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++ [FormulaN.all x X] ++ Δr).Perm
        (Γt ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++ [FormulaN.all x X] ++ Δt) := by
    simpa [List.append_assoc] using (geqPerm_insertBlock
        (ts.map (fun t => Substitution.formulaSubstN X t x) ++ [FormulaN.all x X]) hrest)
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) hsubdepth sub rfl
      (Γt ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++ [FormulaN.all x X] ++ Δt)
      Δ' hprem hΔc hsubleaf
  refine ⟨.onePremise (.allLeft ts Γt Δt Δ' x X hne hfree) q, ?_, ?_⟩
  · simp only [geqDepth]
    omega
  · simpa [geqLeafSequents] using hql

-- ATTACH-BLOCKER: private declaration
private theorem geqPermuteContexts_allRight
    (permFresh : ∀ (y : Nat) {Γ Δ Γ' Δ' : List (FormulaN L)}, Γ.Perm Γ' → Δ.Perm Δ' → (∀ (F : FormulaN L), F ∈
      Γ ++ Δ → ¬y ∈ formulaFVN F) → ∀ (F : FormulaN L), F ∈ Γ' ++ Δ' → ¬y ∈ formulaFVN F) (Γ' Δ' : List
      (FormulaN L)) (y : Nat) (Γr Δr Λr : List (FormulaN L)) (x : Nat) (X : FormulaN L) (hfresh : ∀ (F :
      FormulaN L), F ∈ (Γr) ++ (Δr ++ [FormulaN.all x X] ++ Λr) → ¬y ∈ formulaFVN F) (hfree : isFreeForN
      (Term.var y) x X) (sub : GEqProofTree hL (Sequent.mk (Γr) (Δr ++ [formulaSubstN X (Term.var y) x] ++
      Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') (hΓc : (Γr).Perm Γ') (hΔc : (Δr ++ [FormulaN.all x X] ++ Λr).Perm Δ')
    : ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth sub ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  have hmem : FormulaN.all x X ∈ Δ' := hΔc.mem_iff.mp (by simp)
  obtain ⟨Δt, Λt, hsplit⟩ := perm_mem_split (FormulaN.all x X) Δ' hmem
  subst Δ'
  have hrest := geqPerm_cancelMarked hΔc
  have hprem := geqPerm_insertBlock ([Substitution.formulaSubstN X (Term.var y) x] : List (FormulaN L)) hrest
  have hfresh' : ∀ F ∈ Γ' ++ (Δt ++ [FormulaN.all x X] ++ Λt), y ∉ Variables.formulaFVN F :=
    permFresh y hΓc hΔc hfresh
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) hsubdepth sub rfl Γ'
      (Δt ++ [Substitution.formulaSubstN X (Term.var y) x] ++ Λt)
      hΓc hprem hsubleaf
  refine ⟨.onePremise (.allRight y Γ' Δt Λt x X hfresh' hfree) q, ?_, ?_⟩
  · simp only [geqDepth]
    omega
  · simpa [geqLeafSequents] using hql

-- ATTACH-BLOCKER: private declaration
private theorem geqPermuteContexts_exLeft
    (permFresh : ∀ (y : Nat) {Γ Δ Γ' Δ' : List (FormulaN L)}, Γ.Perm Γ' → Δ.Perm Δ' → (∀ (F : FormulaN L), F ∈
      Γ ++ Δ → ¬y ∈ formulaFVN F) → ∀ (F : FormulaN L), F ∈ Γ' ++ Δ' → ¬y ∈ formulaFVN F) (Γ' Δ' : List
      (FormulaN L)) (y : Nat) (Γr Δr Λr : List (FormulaN L)) (x : Nat) (X : FormulaN L) (hfresh : ∀ (F :
      FormulaN L), F ∈ (Γr ++ [FormulaN.ex x X] ++ Δr) ++ (Λr) → ¬y ∈ formulaFVN F) (hfree : isFreeForN
      (Term.var y) x X) (sub : GEqProofTree hL (Sequent.mk (Γr ++ [formulaSubstN X (Term.var y) x] ++ Δr)
      (Λr))) (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') (hΓc : (Γr ++ [FormulaN.ex x X] ++ Δr).Perm Γ') (hΔc : (Λr).Perm Δ')
    : ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth sub ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  have hmem : FormulaN.ex x X ∈ Γ' := hΓc.mem_iff.mp (by simp)
  obtain ⟨Γt, Δt, hsplit⟩ := perm_mem_split (FormulaN.ex x X) Γ' hmem
  subst Γ'
  have hrest := geqPerm_cancelMarked hΓc
  have hprem := geqPerm_insertBlock ([Substitution.formulaSubstN X (Term.var y) x] : List (FormulaN L)) hrest
  have hfresh' : ∀ F ∈ (Γt ++ [FormulaN.ex x X] ++ Δt) ++ Δ', y ∉ Variables.formulaFVN F :=
    permFresh y hΓc hΔc hfresh
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) hsubdepth sub rfl
      (Γt ++ [Substitution.formulaSubstN X (Term.var y) x] ++ Δt)
      Δ' hprem hΔc hsubleaf
  refine ⟨.onePremise (.exLeft y Γt Δt Δ' x X hfresh' hfree) q, ?_, ?_⟩
  · simp only [geqDepth]
    omega
  · simpa [geqLeafSequents] using hql

-- ATTACH-BLOCKER: private declaration
private theorem geqPermuteContexts_exRight
    (Γ' Δ' : List (FormulaN L)) (ts : List (Term L)) (Γr Δr Λr : List (FormulaN L)) (x : Nat) (X : FormulaN L)
      (hne : ts ≠ []) (hfree : ∀ (t : Term L), t ∈ ts → isFreeForN t x X) (sub : GEqProofTree hL (Sequent.mk
      (Γr) (Δr ++ List.map (fun (t : Term L) => formulaSubstN X t x) ts ++ [FormulaN.ex x X] ++ Λr)))
      (hsubdepth : geqDepth sub < n) (hsubleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') (hΓc : (Γr).Perm Γ') (hΔc : (Δr ++ [FormulaN.ex x X] ++ Λr).Perm Δ')
    : ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth sub ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  have hmem : FormulaN.ex x X ∈ Δ' := hΔc.mem_iff.mp (by simp)
  obtain ⟨Δt, Λt, hsplit⟩ := perm_mem_split (FormulaN.ex x X) Δ' hmem
  subst Δ'
  have hrest := geqPerm_cancelMarked hΔc
  have hprem : (Δr ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++ [FormulaN.ex x X] ++ Λr).Perm
        (Δt ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++ [FormulaN.ex x X] ++ Λt) := by
    simpa [List.append_assoc] using (geqPerm_insertBlock
        (ts.map (fun t => Substitution.formulaSubstN X t x) ++ [FormulaN.ex x X]) hrest)
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) hsubdepth sub rfl Γ'
      (Δt ++ ts.map (fun t => Substitution.formulaSubstN X t x) ++ [FormulaN.ex x X] ++ Λt)
      hΓc hprem hsubleaf
  refine ⟨.onePremise (.exRight ts Γ' Δt Λt x X hne hfree) q, ?_, ?_⟩
  · simp only [geqDepth]
    omega
  · simpa [geqLeafSequents] using hql

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqPermuteContexts_permOne
    (permFresh : ∀ (y : Nat) {Γ Δ Γ' Δ' : List (FormulaN L)}, Γ.Perm Γ' → Δ.Perm Δ' → (∀ (F : FormulaN L), F ∈
      Γ ++ Δ → ¬y ∈ formulaFVN F) → ∀ (F : FormulaN L), F ∈ Γ' ++ Δ' → ¬y ∈ formulaFVN F) (Γ' Δ' : List
      (FormulaN L))
    : ∀ {prem conc : Sequent L} (rule : GentzenStep1Ext prem conc) (sub : GEqProofTree hL prem), geqDepth sub
      < n → conc.antecedent.Perm Γ' → conc.succedent.Perm Δ' → (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub →
      seqAllAtomicOrQuantified s') → ∃ (p : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + geqDepth
      sub ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  intro prem conc rule sub hsubdepth hΓc hΔc hsubleaf
  cases rule with
  | conjLeft Γr Δr Λr X Y =>
    exact geqPermuteContexts_conjLeft L hL n ih Γ' Δ' _ _ _ X Y sub hsubdepth hsubleaf hΓc hΔc
  | disjRight Γr Δr Λr X Y =>
    exact geqPermuteContexts_disjRight L hL n ih Γ' Δ' _ _ _ X Y sub hsubdepth hsubleaf hΓc hΔc
  | implRight Γr Δr Λr X Y =>
    exact geqPermuteContexts_implRight L hL n ih Γ' Δ' Γr Δr Λr X Y sub hsubdepth hsubleaf hΓc hΔc
  | negLeft Γr Δr Λr X =>
    exact geqPermuteContexts_negLeft L hL n ih Γ' Δ' _ _ Λr X sub hsubdepth hsubleaf hΓc hΔc
  | negRight Γr Δr Λr X =>
    exact geqPermuteContexts_negRight L hL n ih Γ' Δ' Γr _ _ X sub hsubdepth hsubleaf hΓc hΔc
  | allLeft ts Γr Δr Λr x X hne hfree =>
    exact geqPermuteContexts_allLeft L hL n ih Γ' Δ' ts Γr Δr _ x X hne hfree sub hsubdepth hsubleaf hΓc hΔc
  | allRight y Γr Δr Λr x X hfresh hfree =>
    exact geqPermuteContexts_allRight L hL n ih permFresh Γ' Δ' y _ _ _ x X hfresh hfree sub hsubdepth hsubleaf hΓc hΔc
  | exLeft y Γr Δr Λr x X hfresh hfree =>
    exact geqPermuteContexts_exLeft L hL n ih permFresh Γ' Δ' y _ _ _ x X hfresh hfree sub hsubdepth hsubleaf hΓc hΔc
  | exRight ts Γr Δr Λr x X hne hfree =>
    exact geqPermuteContexts_exRight L hL n ih Γ' Δ' ts _ Δr Λr x X hne hfree sub hsubdepth hsubleaf hΓc hΔc

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqPermuteContexts_permTwo
    (Γ' Δ' : List (FormulaN L))
    : ∀ {prem1 prem2 conc : Sequent L} (rule : GentzenStep2Ext prem1 prem2 conc) (sub1 : GEqProofTree hL
      prem1) (sub2 : GEqProofTree hL prem2), geqDepth sub1 < n → geqDepth sub2 < n → conc.antecedent.Perm Γ' →
      conc.succedent.Perm Δ' → (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub1 → seqAllAtomicOrQuantified s') →
      (∀ (s' : Sequent L), s' ∈ geqLeafSequents sub2 → seqAllAtomicOrQuantified s') → ∃ (p : GEqProofTree hL
      (Sequent.mk (Γ') (Δ'))), geqDepth p = 1 + max (geqDepth sub1) (geqDepth sub2) ∧ ∀ (s' : Sequent L), s' ∈
      geqLeafSequents p → seqAllAtomicOrQuantified s' := by
  intro prem1 prem2 conc rule sub1 sub2 hsub1depth hsub2depth hΓc hΔc hsub1leaf hsub2leaf
  cases rule with
  | conjRight Γr Δr Λr X Y =>
    have hmem : FormulaN.conj X Y ∈ Δ' := hΔc.mem_iff.mp (by simp)
    obtain ⟨Δt, Λt, hsplit⟩ := perm_mem_split (FormulaN.conj X Y) Δ' hmem
    subst Δ'
    have hrest := geqPerm_cancelMarked hΔc
    have hprem1 := geqPerm_insertBlock ([X] : List (FormulaN L)) hrest
    have hprem2 := geqPerm_insertBlock ([Y] : List (FormulaN L)) hrest
    obtain ⟨q1, hq1d, hq1l⟩ := ih (geqDepth sub1) hsub1depth sub1 rfl Γ'
        (Δt ++ [X] ++ Λt) hΓc hprem1 hsub1leaf
    obtain ⟨q2, hq2d, hq2l⟩ := ih (geqDepth sub2) hsub2depth sub2 rfl Γ'
        (Δt ++ [Y] ++ Λt) hΓc hprem2 hsub2leaf
    refine ⟨.twoPremise (.conjRight Γ' Δt Λt X Y) q1 q2, ?_, ?_⟩
    · simp only [geqDepth]
      omega
    · intro s' hs'
      simp only [geqLeafSequents, List.mem_append] at hs'
      exact hs'.elim (hq1l s') (hq2l s')
  | disjLeft Γr Δr Λr X Y =>
    have hmem : FormulaN.disj X Y ∈ Γ' := hΓc.mem_iff.mp (by simp)
    obtain ⟨Γt, Δt, hsplit⟩ := perm_mem_split (FormulaN.disj X Y) Γ' hmem
    subst Γ'
    have hrest := geqPerm_cancelMarked hΓc
    have hprem1 := geqPerm_insertBlock ([X] : List (FormulaN L)) hrest
    have hprem2 := geqPerm_insertBlock ([Y] : List (FormulaN L)) hrest
    obtain ⟨q1, hq1d, hq1l⟩ := ih (geqDepth sub1) hsub1depth sub1 rfl
        (Γt ++ [X] ++ Δt) Δ' hprem1 hΔc hsub1leaf
    obtain ⟨q2, hq2d, hq2l⟩ := ih (geqDepth sub2) hsub2depth sub2 rfl
        (Γt ++ [Y] ++ Δt) Δ' hprem2 hΔc hsub2leaf
    refine ⟨.twoPremise (.disjLeft Γt Δt Δ' X Y) q1 q2, ?_, ?_⟩
    · simp only [geqDepth]
      omega
    · intro s' hs'
      simp only [geqLeafSequents, List.mem_append] at hs'
      exact hs'.elim (hq1l s') (hq2l s')
  | implLeft Γr Δr Λr X Y =>
    have hmem : FormulaN.impl X Y ∈ Γ' := hΓc.mem_iff.mp (by simp)
    obtain ⟨Γt, Δt, hsplit⟩ := perm_mem_split (FormulaN.impl X Y) Γ' hmem
    subst Γ'
    have hrest := geqPerm_cancelMarked hΓc
    have hprem1suc : ([X] ++ Λr).Perm ([X] ++ Δ') := List.Perm.append_left [X] hΔc
    have hprem2ant : ([Y] ++ Γr ++ Δr).Perm ([Y] ++ (Γt ++ Δt)) := by
      simpa [List.append_assoc] using (List.Perm.append_left [Y] hrest)
    obtain ⟨q1, hq1d, hq1l⟩ := ih (geqDepth sub1) hsub1depth sub1 rfl (Γt ++ Δt) ([X] ++ Δ')
        hrest hprem1suc hsub1leaf
    obtain ⟨q2, hq2d, hq2l⟩ := ih (geqDepth sub2) hsub2depth sub2 rfl ([Y] ++ Γt ++ Δt) Δ'
        hprem2ant hΔc hsub2leaf
    refine ⟨.twoPremise (.implLeft Γt Δt Δ' X Y) q1 q2, ?_, ?_⟩
    · simp only [geqDepth]
      omega
    · intro s' hs'
      simp only [geqLeafSequents, List.mem_append] at hs'
      exact hs'.elim (hq1l s') (hq2l s')

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqPermuteContexts_eqRefl
    (Γ' Δ' : List (FormulaN L)) (t : Term L) (Γr Δr : List (FormulaN L)) (sub : GEqProofTree hL (Sequent.mk
      (Γr ++ [FormulaN.eq_ hL t t]) (Δr))) (hΓ : (Γr).Perm Γ') (hΔ : (Δr).Perm Δ') (hdepth : geqDepth
      (GEqProofTree.eqRefl t Γr Δr sub) = n) (hleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents
      (GEqProofTree.eqRefl t Γr Δr sub) → seqAllAtomicOrQuantified s')
    : ∃ (T' : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth T' = geqDepth (GEqProofTree.eqRefl t Γr Δr
      sub) ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents T' → seqAllAtomicOrQuantified s' := by
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) (by
      simp only [geqDepth] at hdepth
      omega) sub rfl
      (Γ' ++ [FormulaN.eq_ hL t t]) Δ'
      (List.Perm.append_right [FormulaN.eq_ hL t t] hΓ) hΔ (by
        simpa [geqLeafSequents] using hleaf)
  let p : GEqProofTree hL (Sequent.mk Γ' Δ') := .eqRefl t Γ' Δ' q
  refine ⟨p, ?_, ?_⟩
  · change 1 + geqDepth q = 1 + geqDepth sub
    rw [hqd]
  · simpa [p, geqLeafSequents] using hql

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqPermuteContexts_eqFuncCong
    (Γ' Δ' : List (FormulaN L)) (f : L.funSymbols) (ss ts : Fin (L.funArity f) → Term L) (Γr Δr : List
      (FormulaN L)) (sub : GEqProofTree hL (Sequent.mk (Γr ++ [eqCongruenceImplFunc L hL f ss ts]) (Δr))) (hΓ
      : (Γr).Perm Γ') (hΔ : (Δr).Perm Δ') (hdepth : geqDepth (GEqProofTree.eqFuncCong f ss ts Γr Δr sub) = n)
      (hleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents (GEqProofTree.eqFuncCong f ss ts Γr Δr sub) →
      seqAllAtomicOrQuantified s')
    : ∃ (T' : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth T' = geqDepth (GEqProofTree.eqFuncCong f ss ts
      Γr Δr sub) ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents T' → seqAllAtomicOrQuantified s' := by
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) (by
      simp only [geqDepth] at hdepth
      omega) sub rfl
      (Γ' ++ [eqCongruenceImplFunc L hL f ss ts]) Δ'
      (List.Perm.append_right [eqCongruenceImplFunc L hL f ss ts] hΓ) hΔ (by
        simpa [geqLeafSequents] using hleaf)
  let p : GEqProofTree hL (Sequent.mk Γ' Δ') := .eqFuncCong f ss ts Γ' Δ' q
  refine ⟨p, ?_, ?_⟩
  · change 1 + geqDepth q = 1 + geqDepth sub
    rw [hqd]
  · simpa [p, geqLeafSequents] using hql

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqPermuteContexts_eqPredCong
    (Γ' Δ' : List (FormulaN L)) (P : L.predSymbols) (ss ts : Fin (L.predArity P) →
      Term L) (Γr Δr : List (FormulaN L)) (sub : GEqProofTree hL (Sequent.mk (Γr ++ [eqCongruenceImplPred L hL
      P ss ts]) (Δr))) (hΓ : (Γr).Perm Γ') (hΔ : (Δr).Perm Δ') (hdepth : geqDepth (GEqProofTree.eqPredCong P ss ts Γr Δr sub) = n) (hleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents (GEqProofTree.eqPredCong P
      ss ts Γr Δr sub) → seqAllAtomicOrQuantified s')
    : ∃ (T' : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth T' = geqDepth (GEqProofTree.eqPredCong P ss
      ts Γr Δr sub) ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents T' → seqAllAtomicOrQuantified s' := by
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) (by
      simp only [geqDepth] at hdepth
      omega) sub rfl
      (Γ' ++ [eqCongruenceImplPred L hL P ss ts]) Δ'
      (List.Perm.append_right [eqCongruenceImplPred L hL P ss ts] hΓ) hΔ (by
        simpa [geqLeafSequents] using hleaf)
  let p : GEqProofTree hL (Sequent.mk Γ' Δ') := .eqPredCong P ss ts Γ' Δ' q
  refine ⟨p, ?_, ?_⟩
  · change 1 + geqDepth q = 1 + geqDepth sub
    rw [hqd]
  · simpa [p, geqLeafSequents] using hql

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem geqPermuteContexts_eqGeneral
    (Γ' Δ' axioms : List (FormulaN L)) (hne : axioms ≠ []) (haxioms : ∀ (A : FormulaN L), A ∈ axioms →
      isEqAxiomInstance hL A) (Γr Δr : List (FormulaN L)) (sub : GEqProofTree hL (Sequent.mk (Γr ++ axioms)
      (Δr))) (hΓ : (Γr).Perm Γ') (hΔ : (Δr).Perm Δ') (hdepth : geqDepth (GEqProofTree.eqGeneral axioms hne
      haxioms Γr Δr sub) = n) (hleaf : ∀ (s' : Sequent L), s' ∈ geqLeafSequents (GEqProofTree.eqGeneral axioms
      hne haxioms Γr Δr sub) → seqAllAtomicOrQuantified s')
    : ∃ (T' : GEqProofTree hL (Sequent.mk (Γ') (Δ'))), geqDepth T' = geqDepth (GEqProofTree.eqGeneral axioms
      hne haxioms Γr Δr sub) ∧ ∀ (s' : Sequent L), s' ∈ geqLeafSequents T' → seqAllAtomicOrQuantified s' := by
  obtain ⟨q, hqd, hql⟩ := ih (geqDepth sub) (by
      simp only [geqDepth] at hdepth
      omega) sub rfl
      (Γ' ++ axioms) Δ'
      (List.Perm.append_right axioms hΓ) hΔ (by
        simpa [geqLeafSequents] using hleaf)
  let p : GEqProofTree hL (Sequent.mk Γ' Δ') := .eqGeneral axioms hne haxioms Γ' Δ' q
  refine ⟨p, ?_, ?_⟩
  · change 1 + geqDepth q = 1 + geqDepth sub
    rw [hqd]
  · simpa [p, geqLeafSequents] using hql

end

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

end LCS.CutElim.LKe.Equivalence
end
