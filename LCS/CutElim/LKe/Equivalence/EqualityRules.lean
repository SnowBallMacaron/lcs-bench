import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.CutElim.CompletenessBridge
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.LKe.Equivalence.AtomicCuts
import LCS.CutElim.LKe.Equivalence.StructuralMoves
import LCS.CutElim.LKe.Equivalence.Inversions

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
open LCS.FirstOrder.Equality

/-- Splice atomic consequences into a congruence axiom and its continuation.
The construction cuts on `C` and on the listed atoms; the specification below
makes their atomicity and the input cut conditions explicit. -/
def lkeAtomicCongruenceSplice {L : Language} (atoms : List (FormulaN L))
    (C : FormulaN L) (Γ Δ : List (FormulaN L))
    (proofs : (i : Fin atoms.length) → LKeProofTree (Sequent.mk Γ (Δ ++ [atoms[i]])))
    (ax : LKeProofTree (Sequent.mk atoms [C]))
    (continuation : LKeProofTree (Sequent.mk (C :: Γ) Δ)) :
    LKeProofTree (Sequent.mk Γ Δ) :=
  discharge atoms Γ Δ proofs (.twoPremise (.cut C atoms [] Γ Δ) ax continuation)
where
  /-- Remove a finite list of assumptions using their derivations and contraction. -/
  discharge {L : Language} (atoms Γ Δ : List (FormulaN L))
      (proofs : (i : Fin atoms.length) → LKeProofTree (Sequent.mk Γ (Δ ++ [atoms[i]])))
      (T : LKeProofTree (Sequent.mk (atoms ++ Γ) Δ)) :
      LKeProofTree (Sequent.mk Γ Δ) := by
    cases atoms with
    | nil => exact T
    | cons A rest =>
      let q := LKeProofTree.twoPremise (.cut A Γ Δ (rest ++ Γ) Δ) (proofs 0) T
      let r := ImplAntecedentProjection.blockLeft [] Γ rest Γ (Δ ++ Δ)
        (by simpa [List.append_assoc] using q)
      let u := lkeContractContexts.left rest Γ (Δ ++ Δ) (by simpa [List.append_assoc] using r)
      let v := lkeContractContexts.right [] Δ (rest ++ Γ) (by simpa using u.val)
      exact discharge rest Γ Δ (fun i => proofs i.succ) (by simpa using v.val)
  termination_by structural atoms

-- ===================================================================
-- Theorem 6.3.1 (required def): geqRefl_to_lkeAtomicCut
-- ===================================================================
/-- Theorem 6.3.1 case (i): Simulates the G= reflexivity rule in LKe
using the reflexivity axiom (→ t=t) and an atomic cut on t=t. Given
an LKe-proof of `t=t, Γ → Δ`, produces an LKe-proof of `Γ → Δ` via
atomic cut with the reflexivity axiom. -/
def geqRefl_to_lkeAtomicCut {L : Language} (hL : L.hasEquality = true)
    (t : Term L) (Γ Δ : List (FormulaN L))
    (premise : LKeProofTree
      (Sequent.mk ([FormulaN.eq_ hL t t] ++ Γ) Δ)) :
    LKeProofTree (Sequent.mk Γ Δ) :=
  -- Atomic cut on eq_ t t:
  --   left:  → t=t  (reflexivity axiom)
  --   right: t=t, Γ → Δ  (given premise)
  -- conclusion: Γ → Δ
  .cut (FormulaN.eq_ hL t t) [] [] Γ Δ
    (.eqAxiom hL (.refl t))
    premise

/-- The reflexivity simulation preserves the property that every cut is atomic. -/
theorem geqRefl_to_lkeAtomicCut_allCutsAtomic {L : Language}
    (hL : L.hasEquality = true) (t : Term L) (Γ Δ : List (FormulaN L))
    (premise : LKeProofTree
      (Sequent.mk ([FormulaN.eq_ hL t t] ++ Γ) Δ)) :
    lkeAllCutsAtomic (geqRefl_to_lkeAtomicCut hL t Γ Δ premise) ↔
      lkeAllCutsAtomic premise := by
  simp [geqRefl_to_lkeAtomicCut, LKeProofTree.cut, lkeAllCutsAtomic,
    lkeStep2CutAtomic, LKeCut.isAtomic, FormulaN.isAtomic]

-- ===================================================================
-- Theorem 6.3.1 (required def): geqFuncCong_to_lkeAtomicCuts
-- ===================================================================
/-- Theorem 6.3.1 case (ii): Simulates the G= function congruence rule
in LKe via atomic cuts using the function congruence axiom
`s_1=t_1, ..., s_n=t_n → fs = ft`. Given an LKe-proof of the premise
`Γ, (s_1=t_1 ∧ ... ∧ s_n=t_n) ⊃ (fs = ft) → Δ` (the shape of the G=
eqFuncCong premise), produces an LKe-proof of `Γ → Δ` via atomic cut
with the funcCong axiom and an unpacking chain. -/
def geqFuncCong_to_lkeAtomicCuts {L : Language} (hL : L.hasEquality = true)
    (f : L.funSymbols)
    (ss ts : Fin (L.funArity f) → Term L)
    (Γ Δ : List (FormulaN L))
    (premise : LKeProofTree
      (Sequent.mk (Γ ++ [eqCongruenceImplFunc L hL f ss ts]) Δ)) :
    LKeProofTree (Sequent.mk Γ Δ) := by
  let atoms := eqPairsList hL ss ts
  let C := FormulaN.eq_ hL (Term.func f ss) (Term.func f ts)
  let parts := lkeInvertImplLeft (conjoinFormulae C atoms) C Γ [] Δ
    (by simpa [eqCongruenceImplFunc, C, atoms] using premise)
  exact lkeAtomicCongruenceSplice atoms C Γ Δ
    (lkeProjectConjoinRight C atoms Γ Δ (by simpa using parts.1))
    (.eqAxiom hL (.funcCong f ss ts)) (by simpa using parts.2)

/-- Function-congruence simulation preserves atomic cuts in the input proof. -/
theorem geqFuncCong_to_lkeAtomicCuts_allCutsAtomic {L : Language} (hL : L.hasEquality = true)
    (f : L.funSymbols) (ss ts : Fin (L.funArity f) → Term L)
    (Γ Δ : List (FormulaN L))
    (premise : LKeProofTree (Sequent.mk (Γ ++ [eqCongruenceImplFunc L hL f ss ts]) Δ))
    (hPremise : lkeAllCutsAtomic premise) :
    lkeAllCutsAtomic (geqFuncCong_to_lkeAtomicCuts hL f ss ts Γ Δ premise) := by
  -- REPAIR(T6-73g): proof pending
  sorry

-- ===================================================================
-- Theorem 6.3.1 (required def): geqPredCong_to_lkeAtomicCuts
-- ===================================================================
/-- Theorem 6.3.1 case (iii): Simulates the G= predicate congruence rule
in LKe via atomic cuts using the predicate congruence axiom
`s_1=t_1, ..., s_n=t_n, P(s_1,...,s_n) → P(t_1,...,t_n)`. Given an
LKe-proof of the premise
`Γ, (s_1=t_1 ∧ ... ∧ s_n=t_n ∧ P(s_1,...,s_n)) ⊃ P(t_1,...,t_n) → Δ`
(the shape of the G= eqPredCong premise), produces an LKe-proof of
`Γ → Δ` via atomic cut with the predCong axiom. -/
def geqPredCong_to_lkeAtomicCuts {L : Language} (hL : L.hasEquality = true)
    (P : L.predSymbols)
    (ss ts : Fin (L.predArity P) → Term L)
    (Γ Δ : List (FormulaN L))
    (premise : LKeProofTree
      (Sequent.mk (Γ ++ [eqCongruenceImplPred L hL P ss ts]) Δ)) :
    LKeProofTree (Sequent.mk Γ Δ) := by
  let D := FormulaN.predN P ss
  let atoms := eqPairsList hL ss ts ++ [D]
  let C := FormulaN.predN P ts
  let parts := lkeInvertImplLeft (conjoinFormulae D atoms) C Γ [] Δ
    (by simpa [eqCongruenceImplPred, C, D, atoms] using premise)
  exact lkeAtomicCongruenceSplice atoms C Γ Δ
    (lkeProjectConjoinRight D atoms Γ Δ (by simpa using parts.1))
    (.eqAxiom hL (.predCong P ss ts)) (by simpa using parts.2)

/-- Predicate-congruence simulation preserves atomic cuts, including predicate-atomic cuts. -/
theorem geqPredCong_to_lkeAtomicCuts_allCutsAtomic {L : Language} (hL : L.hasEquality = true)
    (P : L.predSymbols) (ss ts : Fin (L.predArity P) → Term L)
    (Γ Δ : List (FormulaN L))
    (premise : LKeProofTree (Sequent.mk (Γ ++ [eqCongruenceImplPred L hL P ss ts]) Δ))
    (hPremise : lkeAllCutsAtomic premise) :
    lkeAllCutsAtomic (geqPredCong_to_lkeAtomicCuts hL P ss ts Γ Δ premise) := by
  -- REPAIR(T6-73g): proof pending
  sorry

-- ===================================================================
-- Theorem 6.3.1: geq_lke_equivalence helpers
-- ===================================================================
-- Helper: a cut-free FOLKProofTree has all cuts atomic (vacuously true
-- since cut-free means no cut rules, so the predicate holds trivially)
theorem cutFree_implies_allCutsAtomic {L : Language} {s : Sequent L}
    (t : FOLKProofTree s) (hcf : t.isCutFree) :
    folkAllCutsAtomic t := by
-- BEGIN PROOF
  induction t with
  | axiom_ s h => exact trivial
  | onePremise rule t ih =>
    simp only [FOLKProofTree.isCutFree] at hcf
    exact ih hcf
  | twoPremise rule t1 t2 ih1 ih2 =>
    simp only [FOLKProofTree.isCutFree] at hcf
    obtain ⟨hrule, ht1, ht2⟩ := hcf
    refine ⟨?_, ih1 ht1, ih2 ht2⟩
    cases rule <;> simp_all [folkAllCutsAtomic]

end LCS.CutElim.LKe.Equivalence
end
